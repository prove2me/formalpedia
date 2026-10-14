-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1639
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:59:55.305971+00:00
-- url     : https://prove2.me/submissions/7ae74038-9174-4936-adb1-d8088d50cf66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 294604316 ≤ n < 294784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 294605566 1250 294604316 294604327
    0xd14100302010f021203090a020f10021c170a06030b0c0f04060c0305041e03151107080c0c0d1b06050304050d0806011b0f05070504090c060f0203071e0b011505 70
    0x1030180f2400d264075103881c016968258126100e8070855001115144890b40082c14503408500e802441c00c183d03080e04070740221101c03a000c14000d50381e041034185c1c0c0c94000c0802c80c4800c52103009011000c0002d40346103294006113480c4522002800c2c15120482c2c85003100c4000c034030402814030560f50b0174403040f05002d08043c0303803040880b40d221050030705a062100c10031021801c5070360500c00013840e031364035281c08038161300e1444c091060022240400c50760301e20307118452004040100440c1c1209400050594452500f02c0c0f082d400c0c00c920f17454041d0b100340022800800c21001c0c890390104410313000c07448040d507655540107903158401111b0040440e04003844612249000b028425007090040c0350110b50705801c41819618040c0b402d0302954010f103c0034000b401c06c2020441d00c1c0190005450511100301991b660a060400da40a541d080c44039411041c0d081318820001e580380150019055040540c03c10386c0009a842c0d8030030140d8130302c85082c00104030081503001d91200310409640303051504 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 294606816 1250 294605566 294605569
    0xf05060715090c0b070512090a0e060a0e090601060306060206011401180b0a0e0307080703230f01060b0d050601180b0a020f06090106080609070b18030a0210050d14100302 75
    0xc09520203000358066a42d4464004210700e054514050100c510500d950b503040ca042580ca401404041c0d070395458401c03c0f0030103d80d11818643e0b001c8441c3c1041280071500c4000002d907404c0c10f00e0f08a822a81859000c22506240c00503c02d4126429034404001054440c0002c03070b01c481c0240101c41c0104401c0c083c0802c1c0d94810044480e411980b01410300895403070b60701d00825a8041404140041c1c8a2800f40c0e089140500450005042c03174001094000e01e566501440f00048100ca40d003010391900c0a104c00e043c2c184200360300780b25810020082e01c0d0321011944501d4101c0d4543c0201145044006076980d405040d5096184046121200380580b41a4a4002503440103158001b140603038940310a1020040083c41d0140302408004507004c0d040601c20b0b440c0c0003000704140103039403013098104001d01c5444c1c12202610203c40001191528240200b80360400401000f03411482841285504903805400f0b4102c51900b00c0040c04400305c0e05c10122045401995940c032489020081000103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 294608066 1250 294606816 294606833
    0x301020d2f0f160c030b06040e0f0d0305040507032916020601090b061303080d050c04140402030615070b040b0a06051c050c090a0e070902120a050402011407050102040e010f050607 79
    0x20008041d03c02620303039040d9036003001d140381c070341d0048400c00c510805005040ca054061401310000050090170310700070035101c0c16560740c0440410001d1656840106082c480240113041c055600a408074003c5000e407040c4855201c10440c15210081714100483ca03900c0005190303100c41d082da517000f0f01080e42020103000081110740662503203c00204001000a4000d0800700c0085000d924040c0d22071b401c0043c00300680e04000c0c54650740441c02c02040c00840482e15000078651400e940060300c9544a41c08241120810383ca000551417012620204100340c44105a2040344108004011901d8501c0d22100790340d4903002c0c5030380c020240131814030030000f0801080038641c007c5044880d000c00000204064500640d040c0220070348610303e41c0403101041089000a003d034003011841e002070344910680400d0050700c03240350f254a0308049019a881800302d25100e43c16034902a6035003800b03180460003548030344030b10f40780074015400000f004228032040c81304541000d440285400c80c00c0c0e913000c82 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 294609316 1250 294608066 294608077
    0x11505010215060a151e09050d03110a1e05011a130e03040506190207060f0804021003060e070c140f03040303110f01060e070201050f01030c060e040b0301020d2f0f 72
    0x4000c50078900005c1d000c0c1000c03043c0d0860242e0b60300d400d041045030240c81a0741500b2014200107125400c2c50402140e00c817001c030705007026054900420301010010b40e0130f08245180e6006044d0f0407049040d19901090454507511a40c441c600802c411616880a814210402d483c4d1544c0280480c28039403201165800a00740e151490341604d05d400e0326000000d0903900450354116403038035007298a070411501004030f0000350026050116800a0b05000101050781c010720081c0070342111f00038030003414001d4101102600f840c4025000609c1e0600300105269071002060329103403e20f20035850300c55800704500103243c08400140d40b925042d034030140c4400304800c24108042c460a00300324103c01d000e2103041c019002513070308543d2908200c01c0c02808e40d00007508140140c8103000c0104001044000c6130401c0f41d1480c00d00d00c026003641d400050003071201c00001901342d400020360007170700b0109034400c107011025030491240d20001c010528551038001c044944040e00d00304600040701020a0240c80c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 294610566 1250 294609316 294609319
    0x218040e1902032a01090905160e190303080a0b0603010e0f280204150e0f011101020405120a03140a0c0b100306020d14091501091109091801150501021506 68
    0x50400c01c0081d8600707065845041c0c55004160804e181d07142c50b41c2d001c40418000c0000c0300341403106043c98211402000d15101015050012106944016440b207508090b0301925003190b100718540c0d82d0402411140080340e98000861410104101c05d00d000e00540c2e058485080e10342c40740307a45800203a5a030050140103400d0903590b070302000341d000082e0500c5210703c1d180002c003d43c4991400c0000c07107040300c4203c02501802000c5d0111604c40d111781d01c1e4156035030401d1030700c11455503803860542c0c0248165004035800c1010a101e04002940c0020096081071103640c60f111030200340c0718a031800c0e015103041c07000084d810320019408243c0c1807810b03681104048100f10011540da5440d0713003c90340042000310340c1e0740c1c84030380b03000550307202174600b1340c0c08a02c450140c840002c2241d01c00003210014012241c000b6a1000c85e403103110280426038038906405403943d101410840705407184022106400780b169800d0561182c0303880f1b0a2445481180d2043e0000c1401f548580000e1558820062607103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 294611816 1250 294610566 294610573
    0x1e030405010902130902030106090b010503070804140a0f020f0a0b0f18040507030c020606060c1018081b07090204050a060f0c08031e0f0906061207180218040e190203 73
    0x8000751380e5103405900024140800003e00e1904c1c0d20500d401d4410302c4d03014210480c9480d44c3c071003c60360003d04880e409892480c0c01c0d40d83c0d96840c500103c0c41c00d145945107000e4030844520004002d2082c80c10490503008550b98031140181a081240045107070180901c680b07824030108031006109000b030a40d01d0b41c040701800e5810640c0001c40d0460b0000c5a1100020303844510b43c3c650a40c05220707036038101d40c0581c1c4040c501503d2864955580e032503070100350746003590b0398034100c0d04040f20007010740f05e1035105e20115a240c030340304070381d0860403083e00e0074584600540d0000105043c043c801c4404917900078000301d10280c030301503059609c040b420030010f050148000a000004100c1c000130343c8034002c107070060380000021150294089600900e0b1051041e4000240041c1000008180b64090340483d41d050034400c181d401c203803c0180b04c1d03000ca001140485004209111150058003040c001c859032514030111580401050307030a40310500340d181e04400e0082c40808045000a40b5150000c1e044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 294613066 1250 294611816 294611831
    0x2090c0f0403030f0c2f0102010c1b170d020307021006050a0603050402010e04110a1d03371a061c0201030c0e030303040c030506090a050c010c061b09080d02031e03040501 75
    0x4003050342044e4484d803100d0741c00019013800c1c118140c0b80d20762106c82c020f2008101100382550301078082280c01c4a0758a808603941c01040c200a4420308074000c0604007600142c07164a125615000f0b50803d6950300094081c514009803401154440c03442100c0008050411261801a0507801488043e0043e410001c7c911a00c086c541c5907809004034136124260401c0c0d40e400580c00040c8071280048082c1d850701001020381c03905640c006160b256002e90515201d14a100100e00004100410003d0503020006480750005010840040c15200034180804101d203a036240100040440b94100c00101441081520030255100342d0000c9040c0f08107007482d10a0b042c10100192564008680c21907d801c0c0022090013040028004560880e020600515041d4210356441d9191f2841e00182410040c181d1040e0051100320740003001000104404001032038146540202000e0783c9015641c142d22802000354006071000003142c001c1c1441710744400d0400407501150074254006081980c1350340d2036042d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 294614316 1250 294613066 294613073
    0x2060a090312050405150109090b04140715120501240807030608010603050a060b011110110d020c01091b0b0f0c03070615030c0e062206031e02090c0f0403030f0c 71
    0x15113025900850003041e100d1020490329400d4001600540d0445013401c1110380090020103d9503007196200160150042c0300b40351591600071640d0110032040c00a690100c0e03401d0f04611100320031120030348280030f07031780c1c0fa044209203440200c0b421340c1c40f03960509100b03002e062107040080d0b04011107140c08034070695103070003250a55107140c00a8815030000443d100c100841d510840860714020b0900d41040241c610305a9103e165801300142c120307403103050304001050001d0031500c601000c180115142d801c5031109e90f00a108001c0115250500340c0c680b80d90010240c51070b07030205c038070307807800640f0f4496942001c40d0340e0b401181c809011480300380020b200041a50040032030340c040300c020705403140d89903042c1000c003152151710140c4083c4c0d6507800e0000580f640152030420002c841c884507101c0341d1a40c00c1200038801940b000d001c401d00c2074180c0d0854990842c80341b4800f402100c0b070840740d40381c0c8031031303034034548a80c010702401c0030000c00c020000280a0040521416624180554600300320744 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 294615566 1250 294614316 294614321
    0xe030d03020c070f0f03080a0302070b011d1f050d05070801020c0c09071b0209060d060c080106120e06011e0b040608070318050c0103052701230702060a090312 70
    0x1065408260007046030301409804124200040c419201d101c0d003503c0c900a600c6008180710301002e0b1070143c0014005104034045d404550a09a1106480d100c0e0342e960b075100a01074490301031110b840b40c1440080fa100d0041009015241d1003400e0009c02030390b14007010003409a00c03054048070280640c0c0f0002440c15001e10150644c440b482c1d015110f211030a800300603a8080091024040c441c24402d040c64203402c0c40202c1c805031794141c903410a0b649a14000801c0000e91210003004141842400d00303a840e48012290304840190f02c072100d10386000048207054400840b81340a040c0c2c80b04004100620f40480d880189140780e0103c11541c42e04c40c1d2810043e940705402120100c0e41e05400e101d035480d4184a05010088050b44800d5510041ea540d9500e0b0a00810070504268413080429401a000280c40c004611b440041c1c8400c2240450454041c0039103034550442c0402e141c00c140506041140268422401035015142c40d40d19444503800404021000386d04004240b00c208002c040d00f071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 294616816 1250 294615566 294615583
    0xd0b0612010f090b0a060e01080703120909180308070c050303040b1509040b01080c0909030a0c0c080307030306050a0504050601020607080c07020a0e040b010b0c03180f1801090e0d120203070e03 85
    0x1c1518080b280780c80881002680d0983e40301e41f076154400b0004001000002c58884152640903a1070080d100d80000708807080011600000c103014a40241400040c441120020084d0302c0707616071032080d07500d40300b040c2c8892110702d0004d89260401c00001e0002070b04400f40c00e900c1500c404078182c1016800011405907941150b00301c0d03c4003001305c01030000102c20030441484660803940f0013594608844030326124000c450b070140910030030505100410441050250190460030f044a482700160304005010b042140702d514003a50b401903003c29542002e0050f40e00c5100103800415140e116200c080782d9405004003444100710342031000034010f81e50709030071000810605c8003140e52424113081c00c0c1115901a4804040b0744401c00c4404030070580803060ba070b2015003211401502000300303070100d80a0645800150b51020703040c0c4218000c40008140641600c582c1c42d81005003000400707500d69a03001000450011540c44482540d050089400071130b400721041c5000810b11200002007403038003020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 294618066 1250 294616816 294616823
    0x307030b10031a040809041a1e1f0507080315040c031416020c0f0a030605130c1401080103061e0c02010509010b09010b030a150b0301061d0d0b0612010f09 68
    0x41000400c28080b40c103e10394a9110040340308062418242d50319000c81c8a82c040850185440d003c0000d00c98a400307107000070007940680a01c82c490111000701100d01840100705214050b072503410083c4408c041ca5120340b1203c1c41d03d072185019a2525a0b40903a08010304007548000b03246404400c81d15107010f8890305c030ba51a02c01051207420301d0040d1000c884000d140c4441c10461a445500c038650000b458a8002c0d41554552068000440414003180807600301030441030800040c801800b168801da060002d000e00c0140c1d003500c1c0c07205150755442858501c05030010303003014018004130701154401500c030820040410100b9055a0b03e4400765241100c500000d030f5560030800c00480800e0103100503450045800110380d605001e448245400003604103e089c0359108400d02c0301200c4605203030007518aa03900c032620396030b64200081500502030034000141104401c2c80d00d040c10301d05542d0080c150300c409800c20070382e40d500c00c1c0014070f40c001700c21f20129900c440504c0e43c0c014481c072900340031500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 294619316 1250 294618066 294618091
    0xf040b0a050a0f1b0b060301020d020310060e0303130603050703020705011814010204030803010e0403020f07030b070909060e061909060902090f030606151806030f070212040f0b090307030b 83
    0xc030034102030944a260f4501c001480a000c842d4003811203a00d400000c0c445c0e00404402c1c0d9500e0ba80086402405910816500c15200005200000c58410002412124607950312000098550145034581c040c2c0305001c0c2d0701e240040f006101140c020340007945c3c004003d2034014100f10300b039101c09080d910550200c00380d14210559175400d0003c1030401c814880c141340000c0d8905455581d41c0e541e0727403205124142c0181da0003004981003601c2881a107405040b0042103608094880c1003d8200f00020303a040b6020465070303240003c1c41e0b40c40d4060744084541d40d444100e103903910b14082c001d10084c5641c001c03a02d000f1001011658410b103104e001d000d4494500300517201c102e0303403061200303070110000c5061081c0d00807020000c00b07955003000c42899041c21107034241c950100d14521110a0721040000d070340460040304000001021071103451080c031050742240e4822022010500c0707144280d0180d00741102589a05020000c901e02c0203121012015045810705507580e111041d0002c3e09031000d00c00c060303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 294620566 1250 294619316 294619327
    0x170a080a0f0801050a0513050c0405180f090109031b0312180c0e090c0d260d050a270c08060c0c070b0405090a0506030a140d0207060c0f080f040b0a05 66
    0x20ba01100389800f4213001da07200c440141c10080002c0c4044101302003800038640700e40010b4100b403002402e460081c030b00030300003100c4850081170f4054000ea085130120880320290002030542c0e00140a4400c085405440303894400080007146d0b00e1081207410705030b05010600c20f944c1109040c5110301101104244035041c0c04600f0342c40d068060b00000e5026201c0142c0242c18808452000f10305545a074804a1744048034085c44d1500c0020781d10304014440b41d20304030b01b004d1118040110002c1008c1044120704001550b138200080c002c84883c0428180d0414030004a90041500e444001c03080c43d000d850500c0c00700d03680c6d0380c0f010b1505004842c1140c04140114030340280030010400803025205c10702c0840d0a050a1a000c5641a0301c0200034454582d20360000c81c201c0d460601c01a01e510b5000f0700c2c0c4000030764462a04d195101ca00417418001846480710002c1c4042c80b54464207000c503403190280704280c50644032000b40360421011414000001c010000b11080c005000b401000c0031910390a4441 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 294621816 1250 294620566 294620597
    0x10020f0a14121510020f070509130b16110613120207090e070302030106210201050702040b131407050403020f190e0403020d081602150a02040b120a0b03010e07170a080a 74
    0x5101c0804c190b41c000b0850342050030001c42c1c0e4600340c0710b095410454681d0744491650b415095080041d000d4821901400200174031384030003210b0401070b41c5036402d19115030340034187d98460440c5c2252210003029840000280d01311900c00b644506407040307030b000d00c1c0c4076540740c81110401790011307801d070744011410021400d0a0207480000e00e4030780c4045421228400680801c5042034800a0411100080c0c01c0c0866840c0d41c0102003043c0060651840742c0c01c0c482028000703005030312402408103142400140c000e80f090044409480e0702400b400009501d14080c80160a01e02540000b000850b060100352503500c0306e1520b200e1030091740204160140d50078007401000b405800c21008442c400303007c3ca14142c0000b80122521b0000c03052104a90351500b0703080003401143c0000c8108130000801c41b04170400c400d07c150240301e00070010010a0b20500815088031025044d03030700e007500034920402c924030407000c001031514100002e948a5044a5443c0c0c031180e44800342d801c010030718400001c0b103203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 294623066 1250 294621816 294621829
    0x150a0201060e130507030b0402041b030506010e1c020103050a060b07030c060c0c0209040b041a090322050d1709060a08090c09090717190503030910020f0a141215 71
    0x111004580110b212922134803685e448800500010f065110384401040454947d079102d551342850060140b1185088044002e005e483c0c01c2d01d00743c2c0095488410b07412030385007004002091005400a445615010f680150041c1800030031043c078440d50f49400107209035415008100051007580c45440b05400c07860001c00b01c4802e60040c00070442c0c1c1d00c01e0b03035005880314030483d50081d4005104590583d290302c1c00d042110300340d00d146c008800c4d0400602c929400c0000c05000e80d5803201c50b12404104007126107220b00a0782d80b098552000c82d0400d00d0002c0b480054800301b42b14402c0c4041032921031118003141250f401540d03a90000342c241410400d042c0e44c244400316603404121418500f90600408040e9200424080d06004601c044603009001d44200500d0803014910044020040c0309030030b15a490390412079403804540207815184007182414401c817200702c008010140d0400c26843c40886841040d100c601032604020008084000401c8404030310400d02501e20040c03c2c0422005e03ca070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 294624316 1250 294623066 294623071
    0x4030b010f080f10091e080301050a0e0c0306042f0910020303060306070f11070b2a19060204090e0c01020d050f0403020f0a1203050901140f030a0b150a0201060e 71
    0x406421a0f905014105070100c0d448500d040503160101c3c030459107052003808800f940e0381044032410382c1200842080840c202650480fa401c58808000a544100b0303480c081c18100c40901c1c1d10901040055418a0a940301580c103e40708640b800311183c0c10b5603459084d1003035001ca49140380313002c43d01402c031f0719010f0b941c9954810144042c0d81107003011f802080d0345401c0681b41005210305011410f160a10800c400c07584694400d0440354003a03a10303c140e00060784a208103005000300d103103003042c40d40c05504410314041d4151004000741c4040d040c0301501042201011a4501d07000c001c00a810b050500030446035411210291101e01c1e82c91002a103840e85107072540b010300c50107000b8800c0344407400064408403901a00c000300b0780b460000008843c140603400c8040b884021000c0442455441400342180500a0f22090a101c0d04981100d0701c0380200203842c095000c0c2080040c8480c00c06030412856410007501c080c180300400864a40c09400078080000184c0d5500000c1209010401c000354 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 294625566 1250 294624316 294624329
    0x1e07031a01081e03031306020f04030f060b0114070311151e01050f010909020304290a0614150a02070f060f03050a150303050c0f010c0c02012325020604030b010f 71
    0x40c81c3d040e19410700f0f074413400b004205c0701644007488604801d004440e01120058070b400091155607035108c4c5000071030640d1411065401390701c1c015407200c0c41d5001c2d1000b2486446840d541a00b804400d41d07044500c01d401c40142943e50003402d101d121000c540204d120702985001c0181400311014200143d00210141d002e00d01c10060780a010086980010100c8152112010056641da43d10308010120407440281062411401856008040c0d501c040c118010380140d00c05110255950a165455203c0fa9400503800b0010140e01e0800c02c07194001821b46444500590701060354442070b91351149200d5004901003030980403202c00381a458410640c1c0410020720403c0030a00d0341c0300203d8052143c0c007004040c032000203045043d030842048001482d44450b8000d0008a00c0c5010041ca21030030203104a01085040116807114800c5800b10100314190001d0a4240307000c16034031001503094218207c5181c184082120051b07207030640200b01441c00383c0c1958120794034003003003841c90040651001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 294626816 1250 294625566 294625603
    0xf12020c0a031a0915070309050a0b07030e07060512060112091b06031d1e030d050a1a030a030f0806060904050c120c040303090e0a0209040905060702011d1e07031a0108 74
    0x280d0001703141c110035800a03980c1c5030020300480395140a52504c581700354003400d40000c100401c0302241e81034104400b215a4801520740007a50740c4d1082e18580183d1000c811128041c400050b4039500ca14150f40344069044d1000c640c400382c68680170140c0c0d542003182491401000824042a9007502410b541d2036408075103040302c010010f80154651141c803200c0604038217402100e20b000d000c200203480890030b600d4420811810100e44e04001045000c6201c0000c0c9042c0d506180307517280214242c0c040c0f030380540b610341c001003e4100c112083c0100800b034aa05c00c200b4418103229850340e200d07031881065600c840e23541c3c500020245403102c91004101c89aa01401c0205000095210007490b04682124141c2011303a2140901d003406402030480c10760b0401e2405080c0014004001441801105107030004c2080b02c188902912960030034030342d181100c0d48215141400d4030910300000c4200440c4005540500e610b0340d03128101d0214441c0e03081074241ca4500140900c0900b40804100700c0f051032000f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 294628066 1250 294626816 294626833
    0x90302063402092d0c190309061503030806040905070b160b1315050a06031401050a060905060d02010507050313080604151a040b28170a0f12020c0a031a09 68
    0x41420244a40f0200c2c800c6120f5008a201c20111105807180c00c1500000602c01b51114000280280210003003921814101035042c0c00c400d103540030b98020740e501170b42c40024a03502c803020b00c00545100c400449403440341d001d0004082d1400400751019400710803845c9034032001d60901e078241c140050803114a641140f1080c0e80000c00f400c03141880718500b00300200f8a55140b041900040c242584050000315404881d01c11002d0194030452007410300160421680d9107421490040321001c03105240c0060040488402640c0904090603120b440380048a19140c0401d80460a0660703640c0010005e6025006100c1000010f005214a0014949080102c0000f01c8403980c0b040d0051990359000315642c1c00d20003041d071908580c404070f003c1c3c00304817501c200704451082000340c0c90504c0f903000c501d03100a448045401c004a68000c0c83c542000700c103d24281151100011a12010207000961003800e405022a484208440d0000d501404108000c03082e1640a0280020700400b84001604403148 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 294629316 1250 294628066 294628111
    0x70c05090c0a080403110a0b011e030206091c06020721030b0307050f01020a0606031b1403070e060607170d0c0507020306010e071116050a0b070309030206340209 71
    0x580720b0300d8a05250a074a240c4650900350303001018280d91000714000c1800f96018424014103160403030340040c000a504002c0700c560901142130502000754017480401c04404146403400d1004480d82c00001510204a49555034070100d0341b028904681c103100417001210041e00078480a4502d120509081c485d40e903050000030740b0340303d1601516106d8030008115018992003044041011030380401d040110640340c4c00e00c0c07030f0b410040c3c41282c4d07070060500201040368541825001d80c807040150042402d90700b05005410700381001802d69410100070301020001c81c0443c1508403900255403407483e62034103043c0d0502c2c151504941f0820a100d010002180103880008250741195441c0c1c50b015499192454101c400d003002c0c0d5010300444c828003402c00d0b0780d41056042001203903012616a07a0669642c940025503004843d0301501040c00d11204101505202004003490b01c0d003003240310034404110105c216141c43d581074000002491001c00380450404450a540082c0c0341d04108000e0048901c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 294630566 1250 294629316 294629341
    0x181a01051801051009080f011b02070e040b0604110a0e0a05150a0815031b030705012619020403150e061b09040b030a08070605010e1014010c050111070c0509 69
    0x1190900454503a0302500700d8602c07401c540c00140141400361445030825900c2c05000c9c02140c030140301d4904507820400c6010740000351480c100e41c10084611b40c6591203850f074980340a00102501d41068440c0c454411001e03203000140710716802e58540c002850b0310801886010342003a00b102e40950720b000c1c43c485003449150180d88032101d0078540000c05a444140c60201c5120700b5002540502c5200d51840801d0b880080c8403500c90410750849000981c1c030b0004582d0003ca401ea050036180074801e030480400700106055500200c54022141d00c101c00705d41441c12641b0652060380d07030841c940c00c20010107000d80228500c60251000511042c1030001841090311040b07a82c1107100d19000481c81c045460760341141c3d0180100500b40d61364020142400c004503402400d0840340350f86810000b18410032400b0141e4007916240c2d00d480f2400e03041ca00303403181f803032000021541444000c451010002d00d0074000c1618000303542c04120703100c4960746454001400f49401040c420380142c0c0404c4101a62724 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 294631816 1250 294630566 294630569
    0x1060801020424121d061308091c050a12020c040b1f1701060215070219080c010207060f0b1305010302060901031e020d0c08060301051504050a181a01051801 69
    0x3003d8502000707411000c04d40d910b50041c4e556200740760410160280c0c0f40c00f000c070304840400014054420075964010300c9500b107440480e004000300028803200c0c07068200090040c1d1078444540c42201c0c541040d031200c45c60602462011a820700c25100d0300c0818507410303c98815106000e9a050002410003000103042120300b104222140b80c81c8820044010300c240b028000340d2480f1241c0080d1542c682c10004c0d100c482c40c074010048090900e022440c0944002481403c440507070324801240000d9940d030f260503a101000c01c40701c964086c0031240204030a8461149031461070b082c009110005102400000c80440c201140b40034542001000035803550f008503100c0041c2481d001814039820460481c240ca240c00d00744c1c2100b0b10100d82134489100030344c4501d107556001d40b901d403d40e5480d03804250270303213404560501d242c10015040041a0425400c40c98124203101c0c800b00e001c25050702003000358080d050040d18104885442e2641e21451240c0703003405040240c0e10f104d054000482c0381079015074103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 294633066 1250 294631816 294631859
    0x20301090b090412110106030c0305030703090b03040b042310140601020d0e0402090402120a0501030303051501050a030c02030c0a1b090c020a080702060f1206030c04020a020a0b1003080c0d02010608010204 90
    0x51704800c1e50640000c1d0700140255501c1340c210242c25442c0e08040d07941c0d4209581c1100421304081c0702051960b59803098900c196032011020070603945581e00e40107401790a2050004201c0c444a03000c01d000e0b414000d049010342028000107c003401030981b2865001c0140442d4159001009000c12090f031000315501803200c2030b00c0159a9044000c0881c00900c18462000b0904040c130b010b10040c000f41e0f07000309040764043e983c1489a9114840825510828141e0507402b10f0b0302000580f412501135000b40c440c2d1a00c50040da403e09100111090800c80b1420046078490040100c042c500b801294507600a8003038040c08111448c200d860181d41d481c02d00e003000e01045c002060940c11075940b0800c488005480094481d11540340e00e500042c221400e441a038840d000b007030030101da0740c101031080d01d40e03ca803030361700500001c030040d00c0d90003102202804070304103846800d0001c80892860002040c4090006004140c55400d900000b0b0850f4100d80101c0910b9004000400100401c400d004201440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 294634316 1250 294633066 294633077
    0x12011215180b0c0f0c0615060412020d14030c0f0f06011d13051c020c0409030e06070f08070317070e0a0504020a180807140105090a171203040501020301090b090412 72
    0x4400a41072034a005011001316030200014003014400e60209080f80602c105e207528544045140e810040305006034041e40d0221600a6200405440c11a10b000c10740c9005d40c42c541c8030801410714407411a07000413890f032120790200207282030390542049629030280304200035204a5060081d030750b5045d014580d0495000c2450001301d0382a914400c10303c0304283c0e1003030450fa0008d203024120316242103a51075800140c0128110300c901070402d40201c100701a030660340d94a60500440401c150307078202d03150544840c00141307820000508843c004000301c5000361030b03110314001c0f0140705182045000746a40c04102d007002a4080c41d0711040381c9503042e11002c40300507072108050325045915008ad50403000700d82d00c246c0400038081c100850004191940000104804102c000040d1106c1c4a41c41856400000150007040748445600e41c0b000010303000030566607100c03031015004d0030070340041e14155800d942c004010001641c4038890604c0e040415115140f02d850241c40c2c8a046060b220b001000784030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 294635566 1250 294634316 294634321
    0x609100209030312192c0a030f0f110321100b0d02070614070908070603020a051c090507030c0f17030702131e02120c031015030212011215180b 63
    0x110340d018208a80e82c1010000c008000040e0400c0d920020b02c445190f010f1001e1b40c4456002c800e011400d01d4105030951180d0880e60f0f030300c4000721007601e8401c80402c100301ca0300b89200c610036414401800080810f14000008a045144540c110310b0090100e80c00415036000c00c1125180d540c0988280d24400540103844a106017020809000c2c0d00c034622403001c6e1480d00b00300c240b60f0030100c02030596081900302e820b40c0340c44040590480c410441c0040100e0000e0194052541d4103000e820356404507014017281d150303103613510315140800c83d8000f02d5005a0410050111140700784d410002000448048241e40401280e65902d030300c09c2900c041d0080c068002c0900400000b600b00c51000005482200e4008810f0020b4900035081000080242d0315610302040a840050080c0ca018181d0b500c40c00c60304078544000c501c00c080ba83c40d981810305130280070030880041012200c038000c01101054a0000071186400b26010512441e110215480d1422416801e503441c0d140340e010742d51143d403c070140e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 294636816 1250 294635566 294635581
    0x90a03060b0f1002010e0f03031e1b0a1d1c030503100f0602101b050a0c0c150306060e01020109110f041404030915020705010203030a020306061b0609100209030312 72
    0x310b24a100c0355040b4844110380108250b055211070030406510341550001394080101c40e0f101d00c1309a401c100b0380f4000079801e460501d00d40c0030340d0b42c202402c00f0803001300e04003c0d03690600503000f5800e084045002c1d92040d07a80456405a100d802050440d4612220384544104c0501c11036048400b50030800044002032490200014440141060803131910b41d0b286e44a10003582d8131121000150094100341c29000c0083c1e41d80841c980001160315054103050413070384c00310382080c4200301c2600c3e051031003540021103100c01a00282d50b40d019940202c0c1c3c45051103000f801c0c00c080d00c1c2419045a01d400320301404501e80d407914071001401100c1e94514503040b500000c0140c110f205d071501c00300207a83c00740310406410220722011180f40d816215400240700d00c0507a1030300218071415025030010070028410186c180d00442d44080c0080403141014070100718082810040d4100c07019560100050220312602004405c9041019000c254540200340d800319459000c0c03441c041666443c0d0398040b40c0e04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 294638066 1250 294636816 294636829
    0x412050c0406081b0303090d060b18090606010314060906040c0e0402130905010b04080a030c021f0906020705150702091b120403030c110307030e01050d0c080604060803090a03060b 79
    0x22688001d005100342038540c050292500c0c203030700400d40d0783c5200f005000100e050103c140c1e40030410041000503d0180ba441d02d030040c040ca5246e10317901c422038200c20b011020508142d1030040340050001c00c114a00000007408035400c103240d9034100c1040c01d00f00f03d21035071065000d03588911700307950200d9075400055064520880341c1c0d07a40c6511030300209000b00c40c04540c4003500100c521040c0103100c1ca9070b80d220070322150301c698082e4030410b030414500c002c00f081c05046409182271010780510149000d101301c054080381102c1004002540d0b00c00100042e503410041280540b108031040201050005800a51881104d800034090303403c080000300d175a90800890483c05410f00b10250b959220482484114a000c030741c201e02191414910f5086207101d80f81140c40300c0b035510000c5192203555142035a482030444895410408100310391410022640902114801d543e00c0300c440c14140403082005840c020340010440354014840c5140d140e40e21290001160381042c40040d2500113070020820 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 294639316 1250 294638066 294638083
    0x5040807090207050c0a050a0605070f020907020309010f02060601210e010207030f03050c03060a0b18061603030e0f30040e0601020d030501230607060e0601050108011a041205 77
    0x480d01446200040100c041d03001030191500c40e4054907000b9081c0010020002c0342c50080e50703000486400140241401900200f01503802220308502284040d8001013131048112140360068001050315129942c2282ea0042000110b0014004500e08000000c0c401444001141c10404648a84040200c0c45520900400017010000c0d50382d042e05003130144c00c01e000d401d01e2200007031801000500c58100d10041d240101c4004003203102c0c841c40c240d2307400c83d01d800c485c0c000d0031001c44010340c0594554602c401803910310030850900b103181806080c040e01321104c440407850590000914402c0345080030404140c1c0d4072680810420001e81903034a99041185a8001d0068010000b40800d0f1025165038161048200340d0844018018418045080c3d4000303100d00f0b4081c0c15120441140d095030352641201c140406000c4e64108049506d03200245c519856003000706400c842c00500c955680581c1c401d02600c50000140386890941d1a15410b600c00c1d48100c40d501e14401e1290703002c0103024000c610 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 294640566 1250 294639316 294639329
    0x40f09151a0708040504050106050301050117010501020703060207031719150b07140f030d02070c0504020a0906030c050702090a090201020f0a05060609100e0f070f020106300b010602030c1b0f0d030504 88
    0xc2a589c4500d40a00580d10a001d103d000c6015081e4030680c41d0351a1507800e06030795041e0301170500c092030750303a0709406508403800071000c0c0140d8801c11918070320081000303481415812028000c1d465500c056104440050f01240b20495600740306101b114204030880d9005980515041d4902c83c1007a000c41c00c0c06805466055140400980e4a000210076000f60080b1405244408100ca0351801004100e1148042d9000841c510131001c01030940241e00070b8000300707141d007001813428076181e000400400c000c0f40d0004240d40c1e00d00d440030a6581c100105480c03640d130b050003044000819216581c0e00d02006256500c103000660000d14620201450b6900900074090501e41604181303205503400c0f80c084031440d001985c1d13680c2c01c4c1030701403050107001c08442c0407507008e5901c0c14944410703007156005102c0c6580300c00380d071000900014841280c07a80c02804294080d51300c403008010500c0c01c0c5910802c00301d090305030340d5400d41e40076a2440c550100b50203049a820114010701e1409840d54013982d400725 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 294641816 1250 294640566 294640571
    0x20405030f0607080601030603032c0307060201020403060608030301060903120c1205030735060f060a09090f0213090b031c0c140102030f0c0a02070902040f09151a0708040504 77
    0x31030070001c000a4550042c0110340720281240c1e142d000450846170340f0722010b00060b6546017038104041c104802c0400c41ea94480041c0d40358011407020034608001a806100103030741c005800c0040c0800b5208171000740c8400da014515552601f0002000c05050380006048600314426040460303014041507014103500c400c903404003040440004d0004e400454100002c40c80800a4603405103a244030f00818101d895203607440c01010000c550b401440040400b44c020100030300c074401075503650b07020b000602c00130358400640c6411701ca040d105443c507403d1080b008134014041440c01184502500050302c030880700010310201000d0005e41703042445002154808840001444d49a50120b8281c52090040f000080b900d0401c81d202801c078441220000910b03040c078004070b0000380b8120001c00c2c0449c2c82d441159070258407000600b0480e84694440110300415000410003c1c845014030590851815001c402c814075280c4031420443c02080303a00c05a000c00150b5000b04004041510701800010703204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 294643066 1250 294641816 294641833
    0x118030507150c050a0e030a0c290f0702040c021501080c041404200d05030307030b0906010c051b010c060501090605040b2e1202220503070b09120102040503 69
    0x14120354003400080c0c4000038900c07405002d1800301e0064440c2003082d0341d2483e141c110014001c44020b141c40900c2e030381c98003030901144082503801e241e0308041c16007a0310480c2621a80b01c806010000400d841150b40c5c002413120303244000b45a02039442d00780c0c065601061407074091004905003074041d46a9020569160000304503c07200040f041e07104801501c080040086000c124164002d044800415042c4600448541c0d402560306421b00f02c074000d09201e803d444541c0c0c6480c155003044a05000180c0d40e0030f17500d03542e40741103016160814820308100480c00301e80d40b6142c1d10342c0f44500e001c06404071410fa14040a0340316030010410260405010815940c42d801124042c015521a01d071203181000201c41c1a45804040422040c080048410451034181007400042c2d41034880d980a00140c1d95501c4040500e90000708800c1d103e4521841e103a50085400c08803410b52a0400b41c0030f135118200a2001102da02c04464910200322a412103d00600e41e244d400b9101d82d80000c0e40500400c0305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 294644316 1250 294643066 294643073
    0x803031003060f0b060f130b070308090606061c1a040608010e2107031211070f0203100c05220306090b1e060a030201080a0b120c090a0c051b0118 64
    0x9440e080c0c80c49210140100340e044204a429183c000301d00030760146080282c000c500341800010b00503200203d2081038025610b00300c01409400c803800070340c08110141c041010b41c213800d20000c0c1d4040c0e002c48440307040c01c0307422904980c2000030010100c0d005035a034500400000e0700060201e03181074000d00a00c000754640504030701034104402100d40741c3c400c444240d5120321541d03052002119501d6161f5041204d02d4904403030350b400000207000915030b1103803003120540c00500242106405000141e400001600c1418580303c81402c54010392860b01e408102c140360320100312194500d4482008003d00503121601010210913400205414902441e031010001101030280c800c1081c072182106100000303038010000701e0104c84050740038200070b406100540c014900b490700104600f500044520300500815003079181c2c410f0101c060390203500d004d00d207071800e014000e0303100721000b100b032208002c98080504240500040000340c0201e410060307008060941c04148988003114121400381e0071803c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 294645566 1250 294644316 294644341
    0x70903020307170f0c2823100e010806271006080112030c060f021215040c0309231614040b030c1e0301021c4110080303 53
    0x100e00000c240151079101381c810034040b60b90800c801018080e01c2e80604018018041455440120402441200c4d000314074902200d29030542050f403241048003d40721101044a1004048a48003c00070b06250280c000c0c2d0344810916080003090f94041c9880509807110002c101181c94103940e244890020004030545030100c82084540b1521515a1a41c0b5a00070740e0410f101c000300a0701062600c500e903000510690701c210a54281c40b1300050901040c203c00c040319a000f900c4c030718822201c488000320b044c80e03d07100349520303500e80c0d0400308039101c1c82e95110f140c07407600100242c984407862031603003100913000d02410f0300b018104c0d51100105034031f400c004a040c3c0158141e041c002c0b40b418000d000d003401c0c000354010a411000748107403003200300840d283d40703240c0e00300b040705425540a000024400e034029586940d8031002c4803010802c82c044a01e11800d080101b2111900114504804012699003010308804c03451301c0b908186c0642d40350001c10144289551011440f403000000700300d000b000749c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 294646816 1250 294645566 294645599
    0x10903390509060303120403080703060b0c1b040902221b03090b0a0905100509010605040c0306170105071b020f1507051203090309040b040f330b0d05070903020307 72
    0x450b400c0000d61100c1090555074001c0310040301e440310b03080300440d0110f4024100d071540720150f490301044003074641d650000d194019180d20070065021100744c1214000554038041000c4064908104c00f071410b8000074280042c0c21602d410308103046501c0d83d500c032200c0e04007a0b0410b442d00714131900c10054400013802002d2033481a91010080804601005018004c0401043c1c00800070701205400c0c02d41a8000c21000d04003001c0d9640c0e4100006051300e880c000c2a500400580340080c044e45801c00c80c480e20313111540c054200380d15240400000541022019182e0040d80a408942406520100d5040d010003202c40b6800000d01e00a60700c02540c501c001d150440c8200c00b545c03038484e0304905040c03840c042a00c0c802c03000e800600110200781019880042c00e01c0004102040d010a004062030444145103c524401d8107040080d0780e135032151900310102d004840c1d4030496658503040b444240b81c002c2c440c400c80c2d85900d070000b141c0480e201c1d200703940280d0380040c241c0d10381c00d80e20002540006a007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 294648066 1250 294646816 294646819
    0x6070507060f0e0f0405190c050d060801020906040b07080f03040c0320011407050a0c08010b120c0609060702040905120c0d080c0a0c0c080604110f030c0109033905 72
    0x1100001c1032110f2060010982403003004e4407004460b0007510400c4090704004010344d501040200e03152203e600140611f2450052984440f6560400d542c03140040e1000c681044015a00400c241213698807807804613000c90701d1002c0056200c190700e103030008141c0310740c4541d000c20300004000d01c81444100c403c28000c991241c0b400e00800e90103030200c1c1c400e810900c10a2400304901034907480da02c910701d40050a44511401c29030b500701c0340b581c0da440c0ea0202c064000000ea070f95503250542150810808102d94044820000e001c1c0f980c88600055103031280d849418042c00c008996142107445640044a0136035100381a04c15440640f561940160000700300c900040c85841c06140c00d01703018003085405980381a251300c0c80e2011602c81900d0892500900f11119043d401c0c3c001103281d010b0007074901030340c03140840203828001d0500700501d481e50043c11501c241c00039428080c4581c3c221198404603a0702c12007000c2d528484106011915803007001c2e80c58800035080d844241508074500b0401038400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 294649316 1250 294648066 294648077
    0x101406040b18130510170114041b0e15040213080a0b0a1109030a083010380904020a08090610030b0f04050c120f0c09070c03110102090607050706 64
    0x103d030072032003542c100ba41d000354a041e1810050182c4d00d4401800c8074917840072000410758100c80c111705040d120382268140d44501c00503c504801c1b4824200306c030010281003012413031a051030707400080c09544080f04a4840c40e4002103a100d5031120000304802094610b043d40c40e04840c0d8200200c0e030010407980002954600210749480701090300c1a02c1100c032020340100f00c540d0b2950340d400d5096100c1070b040380c0c0c00201c00040760f803a264012442654040b9418400403070307041c242c6940e680c6079030750742100031502c001d24581c000003034800340d500f0400864042d11070385620b0740c56100c569521540100c10b81250000404203c0c140c1c004c2c10141c060820701c801c0741c01a0340e401080304035141007400010402940d4401159500070250040b83e042405078064980e40040354000a522a04c50640c0f000907030005080100106c00c02e00ac44038400304103940500551401c00d4000b051101103020060a02c400c0c080084c1c030300381096055134a4801f0140074076581c0d505a05100360b1364881407158070f00248 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 294650566 1250 294649316 294649339
    0x1c050901020f1603030c0606051011191a1b160302100507020604080d060801020a0e0301050609041101030f0e060108070806071b0209060d051203090c0603101406040b18 74
    0x5001d050f00303604000603074800303411603034211844030010005451454441102007119904d400201e420382c0c002c1d80f1a014201e6017403280310305106800411400c000155030111b8045900f8807200c0c04400074842031648c11707564440f42003081032401000c1e004140170101e088034800d8162540c2103400c5009408442e07803d0b07840740b00f0a0948800f210036000682080c004240003d003210068003507074031209800300312a40c40b44102402ca8001d00644400644031042149240c107080c80780c146c010005450082d1580340c03e071101c1e1407400c04c036144941050399403d480c550a4017070b0390103140044142c409486195a45983c80ba9031101c5a00801e034031800341c10b01040c2d02034003440341d88001c4450342e5100307000b104081e000c00080400c01030038030b030b04003880181e4400094004d00050540324080d407442906e0781000c0715107618201240c0b00c41030007001c2c10024001e410304404403110884000e4003140749850600740100748c4501495100071b0304600089030120580e80d01d01c0381d140c44a403090f180c3c0600b41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 294651816 1250 294650566 294650593
    0x50105042a0807140604030b090a02090a0b01140a090305070308090a06020616030c1e17061e0906030a0807031101140c180301110d05012c01090c021c05090102 70
    0x80c41d00d88501100c0750f00545080003280f003003645558104c0001024641002d50304c2c6c880d814406000c40e910901d035080041c2c1c01003146403540c0000c3e04810302071002c0140800c440300190411a11018400320f04102080201c1c0c03151150500c940619440ba00741c8200d50b80d0b902e0061022340004910602c00c00d054000810981d10000700d142c480d8241c4a03403504030703414140d800d0f001032403218805020000e110310406c0341d000e03190b810010510010350326540c0542034039002c00200d4001030031003841041c1c0024a12200d02d02a075601c400d42c2d00c1100c0400c410784a08000a2070580e040d1801040c01c100401c04405144e0024224070241c0e2156000341304c8003420710100403519800303c40802c051380061002035a10040382e0a1404028406070000030400c003a0302031a4250380200c181c0c94819503c980050240051400407604840112641419809059901c1c000c42100500031504034aaaa040d8404894820071a000c8071040c9070002c414402c0082031300038401d0340214949409440f852072040d100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 294653066 1250 294651816 294651893
    0x309120c02090c0d06030c0b030a0623060c01090215120907051f11060a0c0e1c121202030703060305060f0105060d0b01110d05030f01060e090103080a030905010504 72
    0x381d07401070020351240d9654080070040d07080740c42d000914654441c03001c40029445002d0201400790300004545134035102030a08103864090700005c05000c00000d01014880c049848050240c03011100c20f0748a1030b112504034010500180043d5101e42000280010140c0d54002441603140792003013011259030307405d00c1d1692103a6170322a06800c080001108141001182d001e2102884c841c5069140783d144140d00e145000c00c1543c0c1c2c000c1e1190b030b40000c80e071f42a81204410102803000e8444214401d02d41202618890445401a044102c400a000406480340d00c2403040724400c00340454076420814002002001140011a02132068401289106003c448175504030b0310000c0c40c681c070b000c40038803003103010f04085c3e0300d143d0612010346a100321004060152003e0001c060b51556207a24211485a0200d50b0680c0400184906103001c0d4001c1d8841042c03403415030b030b04020782c0f660342c42c055141100188400d210280803075281000f848100f120382c66003c0034441e1b02e80d4050880b8203040226890 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 294654316 1250 294653066 294653087
    0x1207080a080306060d0c020304090e16060e030304030c0e241f0306080a0609031e0215070516050105010905071119050a0203030d0e2413060615030912 66
    0x1240d44000380580000d41d20000071940510060903160801c82c1200c40c0006603120500a50090b0b00040303400e0011000511800c2c10b4110a980100301105601100d101c11007440d00460003044018080341d4441d0f2020802c5074001c5911160591031241d40300c1561440d100141c4001e0a005444096094031001c0480f0b03204200100609403001c00400b2500c1c901c0710021070051005050311120005407400342071050500290080c1404a20207a2038900101071609c09503801644240c6002003510007503002800014400c6492107036540d548800b18103888500410b46255511000d40c981c4c00708005041d000340f4102c40c0c807800203228644030300100340e0b210903a19a1480d1140e000c6c40000c0bc10060100c0d10743c48079402002503901c800d00d0790b004281180e200c0c4140c1381c40c8035286ca000003400d000410000c240c80d0010310710100c100003101b031000031000001d0440c034a03241f0498210010310201da404840280703c0d02a400c02034400002002c0c0181184c1542a41c000c14214000741120380030710038005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 294655566 1250 294654316 294654329
    0xd0204080d05072f13150f0b0304080705150106030b0a091109060304061814060105010807090303080712020d15050d02030c0603040f020d0b1504150603020a05090303040b091207 78
    0x20403031881c1c01c1340d03c0c92030400c1e1100e0a540e0349089a52000d1901ca40f5031034100d40d20344036008074400684507208542006560303c58010743c07102d20340030400b82c1c0e142e00c00e80381c120764821030b00c80c1e9036062814218a00002460580d40206049000150b60b0760140c0c80b10b550f2600c15200c13000380e1665608a50212a40043d4140c01030400300030b140303d6031400c48011a8010300c1070348002541c00e00039085803030b90100c0c030b242215081000014491404004c00c49540105000d103003404452406c010020044c0e031180c4001014440b60101040a66001e40303042c000c2c3d40c90090086444042c2d44007100050004407443c464600a13204011440d81092400c1c00c0145401400030442103012200b84102c560005100b524448a050900ba0042c5e643e8400c50781000c1c099445000c0f40d0400303181c1e221207903d26046841c030803407921f0b100c10800da000242850032036000f4140142c40e0110b20105440510924001a0385030000080104041443e0800313010300403800e4511903035030345850f01d44d02d69a00e000c0c000c65 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 294656816 1250 294655566 294655583
    0xd0c151e08091e0708010204061713050c04022d130e01030c060f02030f19030e1f0b030309060c03040e0105100c0f0206042402010c0c020a0302090a020408030d0204080d0507 76
    0x288103c6201d0051041032a940001c8074003540d580c82ca42c600726042a00240002a03001c604041003c0303401c80411b4001d030500c5800603000701503a484a50300c0c00c02c411201d00681e0089203203890302c0702045441495170104a82c11070520741f00000e4107c41e900c44d401820001c10000f00c0452500c0100b0700c0a41030380d5000b40741c501041e003810340c01d0f82c15801d0a4429021407004104041d81944c1c034030041d1080c0088020400401c0c0b41d10310015041d2500150408000d601000341080e203401c0900052481d652051000141c0c1c5120300082410743c42890410783d0402400540d0300200100000140702700e0312148480311043c0d807903600308018412011041000103100d0750000021600950070705c042548000c20140c6056901c0603d003206004c1c61303c07501308480100503007109190b02030103800c03106055487c04100850b9a0790014060030300c240030181c00791000c8800200500350640c100d07800f40c64442c046a0729449050305180c00396225006456441c05005003d4581d140030340181c59035550b100600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 294658066 1250 294656816 294656833
    0x9010f061b0c0f0f05040c032306060417070305010b01090b04060302031003020a0b03070e0f10080a0213230114090603040c05040c02010b040b090906060d0c151e0809 73
    0x1141c070500c03000003660182484900000e507112040302c4100101500d071150030810b480c1c901044100c034420001041403506000e10450f03010010200c2c5568074241c96503150f215103030800803404030b004542219003100402001c81c4001000040c046003141d00c9003000740407001300503004544817440da1040c004110b506020900c80340e40650041c541c0038a03030228043d41603a980e000030f0064034641d400303141c00110000c1804141039010031000d5043c00e06031514600c004010011443c07036107407803194108004940001c00c9540c0301c1501100c9500031204200064103488446070042d80307144021241154024001d40c888950165504850b41c02c0e0070000c0740d041000d10400d10407594001003007201c8440c44401c01140a64851040c146030000c140c0c00061800148824402154024001140314150315400c000c2428800a0101d511400580c0e400140310760500d0109034113000740d0058503821042d003200c2001603a003c040307480c0d82246a030021003501300d00c4505072000102600d41c000b498014044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 294659316 1250 294658066 294658097
    0x70c0c05060901170403021207140f0606061804020403020409060c020706140d0c022401050420031609180c0f0302270310050f04060e0f06070804020d1a0609010f06 72
    0xa031130764000d000380103486080d0140180c51441e03038032518044501908420089000e00802c01c54001c540d00340314010506401c10000240140c098000103a0f510341c0380c00801000381d2030b10b4041d500103640c040d000748148412490910090500100d4045c0184a901c00014045e403089030720503102e01d8150200352500301e601030014040c00040000e80154410030299030301040300ca070003400340c1c1540400c454410707506001c2080251050700c80c3c6943c00312008411003228560100c00c481d0000c2d0003c0c44170f0305c0a00e00c190183e5036804541d00c40c0d00889180080c6440541c1d541d00a9840c104c0d030b079541d415490514940c143d00300c4c082c07808a04c0da0b54001c00c080541c41c0300d0000c80c5121801000702214492142c2440f01000d0310b030219459841c41d0440010702007080002d008103604501c402010748000b03d1542c40b02552404010281d07410081c113900810300755200d08090605443e0080d1658100302008081010034510a940d87d5000740300d0340340001410b4410000d8442035070282e565a2802c1d0044a5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 294660566 1250 294659316 294659357
    0x20309332206050703020403020907030f0510030203070b03060d02060715140f04020d021f0e0a24050307090504020c06040b0a020301080307200901030c060305091b010f0c0506070c0c05060901 84
    0x1400070045c1542088007001581d0303440030851013039526580c08201040c01110880070b80d4409003110080c05003482c0d0500040c3c2c0d0104010040d01c0d80c00d00700759140d035500f10005c0c48804140b00080d4100e14001260010300071a0040ba00703540210b03040a01040900020003076608404803080f0048615400200d4014600031102e00a280c2c001400501140714000d80c0306244510f02240b000402d4400f10410054104800100003d041e4281201c150704480048000e841d050741100c10100a0000000f4008038000c0c51424040c3c83c0c042d0045403a030141c0b0040c103595000503501174a407980441300040003480d242c021603040c1c0704001c0c00385081c600940d81c0c500226864001e40d141da41c0d001c9202c202180c40c0c103400d0700e00850103070308240344441c40c0c0b4101800300c81d4098000c4d4101d4020804420441d010142141c44200f401e1908010907000010200c81c40004000c0040181c0100800c0c0440c46601c800c45440450103182e004007069520340c10005c0b18452003071b43c50b0100d4a0151101d010303007002d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 294661816 1250 294660566 294660571
    0x30c09051b0d0614060307050910050708040e010e100b09190509040506010510030c1407241b11071e0b0a0c2d0602030933220605 57
    0x1201e10303100c0100700e081264a681080b508100c000c1d0781c0740010400c0d4411001010070078030054411500d107090001008103107224100403a0301418020a40c0040188204222124160040d50580d100c82e00c85030803184003a0284180500c0040c0e03000411000e02544208008803880c0380c90741480d140c1000f05100d92815121106890180c03d01d81c0014a81c640740707001442039204030301500c050760412003003110380e1000c11082010140f0340591004000d4001444e030071600d41d0300c0c45031900d40c0068074203075460f080d110710200c0e00c40054001c007918146140c2c1191100c0007041071a24007030001704004494410082240b2107503a404110104041070a19000385120f0103640100184c5644039444110103074070012aa02c0050b0720b9400071014881c1c440705511910700c03d0105203851489884400c0390507021180081c1030143d0000109528040410841d80c01502228a420011802e641e1012003011040901690460f600b40003880d940401c0d1145500b80e0070303203c0d030406c204d41e40d5101e560003030000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 294663066 1250 294661816 294661831
    0x50a0c14012106030602211b03061e06070302061503011a0405040606050a0303020c0f1519051908010314010506090c09060f0711030f010e0a11031204060207030b0c04030c0905 77
    0x48030008130220b421400106421403d0030140044001030342035070b455248008240c0300129040414040742100980206c07500140100c44216003082d02e911301034061825000b045a01c40e000141c80720416070003040e814404c0707803060456141508603000b41360a03a03416600300c041c1100000c0c201c860610f007960040380c009008003400105e0b2901c6d5408281c40040da07800036409139100380d90310310781c9103001d030f590003007001c801d40301c1b035102c8403a01403106c155000c1c0f90305030f25060300c9117201381009610840035601d0101c070718100c4c2c0c40590724046002d01190000c0c0410b48100e091194a900e403240140207081c0250000307003140f0b1469540031080d170490b0308640c802580c884810800301c003840410901501c0382d07a004480c2d071243d10105104051034417484201440319a41008082c1200b03090100c1d0030304641e42c00c1200200c03034400010000341446034025649012480104000c075086900150303801c250f910981700c5090035140c0d80c1148189001c0e40c40300400241104006010b8030751290000c0da0030910 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 294664316 1250 294663066 294663071
    0x150b01090603110705030a05030a0b2e110610090f020c060c0d06090501090e0f0706052d0c030a090f05030303070f020309090718060311030402040207021c050a0c140121 74
    0x490317907800d819607012090350000900040140050070000d80304403001e00c503080b96034609040304901c1c07494522550151844c0108a03072188103680900600000082c805001c06885041c41d14403c6854500c3e01c41c01025000e6252000100d800c091900c02c03151030380000d000425103591400c050a10300c0c0d01219034102d406840b400c0000328081503006a5010f8900204007181c9410000001490b10300c403020184000d600c5001e040105a03040307011aa480084901003940c418111107804107922031244e50300100d0320002236485014103000c4060050b01c0d00703d558180c091660f034400d503022550240a0558103030410404150400d00800700d05109800c280180c90034220303500005240307964100c1d0b4400c0802d5113602c030030601001801c41d0750040e0004c1c2c1001c0100d400c0c002d200c401d440c00002e000a000c4d650005034882599101100c80ca021819811400d4800185103002c075264002c000d82210324540700750021480741d9000141451a62041c0e40700a01e0410007004404481e42401d00b021350a90f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 294665566 1250 294664316 294664327
    0x1b03090c04050c0f0310060e030604200609031c030b060f04050d02041b0819111b150712150501080f0402040633030c020703120203040e13150b0109060311 68
    0x5802c5001d50b11801e40d070311112040311310b01000a491408d8441c510381c401e4109004220010301f40340c015456590400f2148050b000e40c03000410035074840d000107254184500841c080059004d16144c50618926540502424200100f07115450041601c08003900c041444240241d082c082d1100341400c0c001071003c00d1100b064814889900d0304a1a80c0d00080e0304401000030f03013206840543c12003038071441d041212460801062209010701103000e0340c40200c070b0421200c5040f040210b500309400501480020b82402c26002d8104141c0c4070702d910200703040805010b2042d40b101d20701c200f11801a100d0384203e07a00d500100e00c114100420072039119a4409006c0740d4940c641003000d0000540c5105d05502d01c03004da1000124582c00000c4c0420035040c0382d007000100740c2c00b1606a08403503010300d03948900d541c0f05071f0982c05c44c01103800c0154841841c004100810310700e00203200a19002d1b041d0b040d201c1d810a400390301602d4040b00c00601041c9200001c11405210b075100b800c400407001103d60424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 294666816 1250 294665566 294665587
    0x712050d02040b07020f0a080d0507080f040e01150201060e13050109050f030c0606040504080a0503040c0509100612150b070303090807030206010806150d0311010e070303081b03090c04050c 83
    0xba0840c0d005114901c2c004901c6908509100040240d03112003142c01c820107515001410f643c60996108130800c00c2008141c00c401c0050300c05c151800c0c03ca4004100e5216526081020381840007403089465140900d00b032150b04c0d90040c8940420380d224241503031000c4c0d0780c0c103200a04c00001d80a04075920366a50181c900410b00500030140f8804001000c0c2d5a41d00352050024602030300a03004074032562500301400000389162084861036421400d00507165512800c04400d0030f8407a5100940100d030800c20050000c007585105d01c00d864250b00c2e040c892064003803004007240d186034403804029138000028030510410700046d10126100380360114040b9901c0d5900000c503002003800300e0140e81300c4401404055400d11071540d020b00903140c0204522414000a96041881100901800ba03040da5500d8000c0017900400c10070b04000041b10f81c040c0da82e00c0c0040568000b11103140d004950711401c004036a5580c001c407401890128001c06491148100f0800103080140c031007605c0c40020050001d10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 294668066 1250 294666816 294666821
    0x9112a010504080a0905040515010e120a030203040f091a0609030309030106032123130e13030801080307080403061a130204060905010302070201050a0815041508010e030f0712050d 79
    0xb03944070761111a10303002c1115000c0e020402c5038006c41e11440c244000c2020726084036010a18104e000d10701240c80380442070100b000004614418541401010049401c0c1a0000002d20440d9070320f164103e071060752a010801110707414121420302d40242e10a945c03035854640c01400d918000201070301c4ca011a03c10001e0300710f40107540120f0340b481001d022015903260200003400341e00c040381021480340e0490050340c10780c1403185641003200e400104196503100005c3e02240041e00f254420300d030880c180b00e07415450810400d0341c1200043c00e80000461070160110903a40034540c060f1405080a06550791840a803100620114122040342c40e0f424150b9116002d152003401a0b8600595aa08041d0001c06204140c0c2000c0d05240c0100700c0540181da000041392000582807900c0d109986075040352151517844d03408010780c8241445001d03090b085180712001c0844038031000822100b6111159207489000340b90f60740300e091506021403004110940e0014100c9800c0d4501a468a01c0b0401450704 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 294669316 1250 294668066 294668071
    0x7110106090c03091416090509010b06070318061b03141303080c0106050603010f0b1b2401170d18030f060204090c03140a0b060d06030b0f0109112a0105 67
    0x39444507149400e201020300d84503202243c1c100504032050500701c802100360710606c585001f01e0780e1000000c1c1c80076000e51007150200c9000704110390310407c07400c0043c150b8503440e041129001c500306c000504103001c0c1e4102082c49040000080c2510441e4406036100307540a6070059500104000c1804500d1180c0c01d58000355100303007034091711400070f040110300310346045c0c1102e40207841c1040188070806080100303404030740007103561a64605074035064480c0d44403d002c80035141c0c404c80c4420045441f524416000d03802034040620803c0c1e0362060700103402c48620b420120240c0003c2403000f00385125060101c0b0003030300d0348000000380c0da413691501581800b00d0b500f500e40d42d40c0480c0334030640050340214185500c183ca8103200c6003101104113524810302a03c01d0088658a6030b4204868864400352901480c15290402055031781c2e040c0784c081702508445044040c0210000850303407001c1d6109500300550801c0340c4605201c80043c01001c000c42d605c10820316000e4a680a24130170009020309d51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 294670566 1250 294669316 294669341
    0x40b0d020f1c021f02100612080a0e0414010512060f0a0b011403090303010e0a05070906080a060b0c01020408060603160608060109030213060e06030d080a09031b0308011a0c060711010609 82
    0x45074911074002c0c101010021846500707810f00c4070411160300c484800050f66a00910703010362b61125910142d56241c840c60b01290018205803d60941c290b02c01d50503412900c0030348030a0015228108025200d4504864aa0347c1f000c0540200e600c000140d800b0348488441810101d803502d031128440245a001114070010300c1d4000001840065522924650408a4403406100d513040144d0060b242008a0182e2410809500002000c095840c0c214074000d00070402010395132500185614003039030080c00b500d10544a04800b0034181d0074005000c14010780c68100c00e6030100e0030450102ca129102500840c10418620b4000c4096070b6104c0d10484c508151000001e42e0519007000c0c41d01392200140618840d40281da00803079811740004102c2c0d84004029800240c5135100d103815503c01c1003c11141038048003010800d400c0640003e42c03141a2151200d00b01e4551882c0172094843d4400d62501078025000720f4041801c080c01141d58004602c0e880f000030402ca030b11103412404440d00c850514 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 294671816 1250 294670566 294670609
    0x61302180c09030d09030201020a0204050c041a0403051605011b020d0b090f0d052a1002130608100b0403150e010f0903110610150e0a03060902040b0d020f1c02 70
    0x1080607283c200205000e102903820401c200314075540001c3e4603049450006401107803900000380307444103000102c601400f110140c0c40d0300040f814000400316009400304454501c64075030a00c2c00d51102018520031280d05942d80b0184640e0050020710310004100308030f804c80c0c000410f910019800248941c45641000020502c41e99803007141032501c640d030004c18003407100401035410b031039400390011681d0345a000f01c01100c07021f8031590207151450103000261080d20124981400385800e1542d00116a16507807050070701d85542d50200302403401031084007040e0b8010803080000800700803448100010361800025034401c030b400c2075070a5030030608282c00c2c03071695940d11303100f095003110400c00e2040251000788070b14078000d190144119540d01480411002c3c0c40303c400c10b03c0c3d108aa00010340c1402606e2001619942e00c4c0500c06403104190032841a41044201429410308494051a0503001810321041c100e10700d09002d85001040380d11403290340a446c01101503101d140c600340c601c104032901d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 294673066 1250 294671816 294671827
    0x5210c030d26160c03090b2b0204080304440f0c0a120203120406030c030b041803050f13030b04060510030c0536180f061302180c 57
    0x1066008070300500b40e002c5003001081804110492401012001e20300307400c02c08583c82c0c040c00c00342c0d191820703548104862580007880000e50000300440d203a1002c03040f20780f5020301c040360780400160700803800340742c54540c42404108540c0c6a00a07816040100a800300f41c2c484214800001060105124a83c41c0c1c02450802403c80b035030402a0102400c500710203003070364081c040c00080142501c0d02c01d240104070051402001c0d960113000446100944411860366161390307000240245c0b42103414070002c0b074680701301c1e81458203242c080c0411041182c07007040c0703400049039404e80d065004607428041100050140410003a50518410003541c01204510311038074042c5000b01c25940018600801840b0040042001a030031004201c280da02c210762a040500d2030301509103411140382c86450032002410b0400c912569038444081c028a59010501028881001c0c203595a040304140e01c0200c0e40054006405020f24283c3c42202c10f10061503044007202c0852132240d20842915040441ca82c0004c0c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 294674316 1250 294673066 294673097
    0xb0a020903010c1d0406031109250c06060e09030a0f030e39150a020102090a09091208100e06030c10390b060d0204061202040f020405210c030d 63
    0x20a04c40448042c08501d06540d01c410561480403d02805614002c020440b491124606029000c6d40803021726170030b001c01940246103a4048805490442c54060302090074444011481d04c2030200100071854411081404c031907513100e901c040802c15a690440c0c000510080c070200c9080e000c111201000c1e0055040800d03d9043d1107081980300007403d0381d1720103458841151080861040c6460207072105201e43c0d00382d0283c032540b11100e500c0380320604041040b0107654001c410142c00f030540c0b41500710440b0019685011f060360a13505d640a8505c4c1045600311090b0030070751200e8003074190f07154445204040340c2c1c555800c060f0703440840d0360503031140003584c48503200400d003024144425403030843c010704030000404420006402401d08030000b5031680c6a000f01d1840055025000f0404c1645d581840c0ca00c00d01c1526040780726904103100c0041e07000150003034400746c90008050032100680010209102181350380400132a0080c036440480a5500f8480c00403800c00944410350074404505 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 294675566 1250 294674316 294674357
    0xa02130903120c09050d0c1802030a0e0c0105030a0e030c03040603020a0219020a1202060702030706030e010b010e1c0f0501050907090f09030c1e0b19140903070b0a020903010c 77
    0x1100c5642c64503080020b040d0b036900c074811604544090b40c0300e10050400d403c0c14088403150740c1051640c80741d105289183c8800950045200e142002c4080110a4100c0c0c82c45486100140c00310340081d0090002c18102c4449078482035030118a08100c914014040d1010750940d00541c3c4a00c003c81d601107144a545034041c44255101844100c1012111019500240c2000f990b40101441c00c189001c1d0f031011512035400320703145180c00404640401c2da8405005000d42043d40c100c04165090a41e6401554042c00e1700f45001700f4000e200e007000d02c030a2000500303900f0b44aa01900e03c8013200400e000032031020301c64103024039048405802c040d400c1032801429503640c41604540e01e403a0084044c04294000c90b1540d5041d449400c55403848c060b001500390720b0201c4403020723140f4080003060101e03100804803a0300e40458410004e011803030600405954801c0c0440303200140b500200b0004001034a0102c40503440348206078010309081d091004a8219020a0030b480081619208504410107800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 294676816 1250 294675566 294675587
    0x70321030501051c0803180a0507050109120209010b0307180f0614030103051005090708150a0b03060106020a15021e0307030f11040308130522060806040b0c07050a02130903 76
    0x603074a240805180444480212001c15406001c42c4400700201d88002c0520320071f481c5c2c500c249000c840c80e0745d440b8240f503a100c040318400e940c04a90140300024032440e908541032109078004000200e280e00c2c0c41d0b481d03000c40d84014800d50030450141000441540070740c015401814641c10030343c500301e00381311000d4100040a80700100e50002480100000307a0b000440b442e071803041c10000b0038680c5649500515000090308406441c1c0683c509151841c46800300541c86804c072140d081c888a840e00040c152074810038082c110040e048101d440004c18107816400030b040052002c01450286e005100c5480c00c00000751030078555600100380510b003941401190910440c80c807042089042c038024208841c49240302c01808444003040d808503140142da195801008007401c00c0b03000c0c114a00d8105114402d83ca84051401d01d0002d002c00c040c10009140f51099074800381d0f071052a00c1e001e00d5151240c0041600701c2d03203445030580078401070b11074042c4444818048400414400a585000381c40d22040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 294678066 1250 294676816 294676819
    0x30a090c1707082a010905100e040f02040617070504050415090b030c030d0c020307030b0f01030c080a030903020607330b0306090c04050702100509031306210c0207032103050105 78
    0x81300c0304060400810010510702201046214405115940165054507845e4049036102c10140700110405420052054101408840c00c101100d00c2180c03c030102c0c001c5014081c0020035042c81d100c202c2c1c900d260341c82c0d0412070f6414024240395442c400101980ea481015580000881d00108403048141c0100440302008a001e820000100c2c03011a99890703524a280c010002c0380e00c1034600390f4a050292801070f64001c0c105604501d041e4400103900c51080c4030880d21510401d0001408500103d44a00c5e200d0303041d62000056441c0d038080003030a8004410544003020000b208030b151107a1852400010001c01042103250030140c0b10705001c64640b841f42ca8000d80048041004161010641c40c2c807250084400084a84451200301e1911940b80700480c071003464001408040c110020280c849200c0c81d881c68092581c5610b02211900390100c5030752502500c0004007a0241060340186801140310f00c100c9842c3c075901d4480d80c0441c032000d1007044010211303400d0300c00407642c11301030070707014200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 294679316 1250 294678066 294678073
    0x18030e0105030f062106150102061303080606130b0c0c150c030405040e030c1203041506150c1e060905060705120a090309050901091b020606060906030a090c170708 72
    0x10410303c061080d8000900540c400d0042000d03c2d416010040380c140046880c1204641051034001c404070071400782c51105034058072602c1d0028005004004890200c903078984d6a41c80a91a110309114041c0c128001049400c5440c40c808109415000c0107400381503002c0c801045000115401c0c094800c0241c0850f1074110710802480b1103135480001250107c510a580005585030115040703411400b8101c090401c501070420101003010841c1e01941c0107070f008008900202c40860740329000c0f14103910034184100611074007070342d110b4002c0081e105c0e65070046e0b8254806c655002c03034048020248803401c580c2c0c190380c0c00002c42804003c009080d401580760a00510f07010000d81a80d000002c01491512010341394141c200c1010310508000c2c0041002805615843d43c5500d21500034000410504894003004400c07400041e10002c0c14034010038002e410f851a06011500380a01541300802605c04c0d40d4a0b04c2c0041d0000e00518041402000ba1040c28005003200250342800c200d82540304aa0729032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 294680566 1250 294679316 294679321
    0x81b0c0d0e060906210c0901171305070602010f1d0a020d08120a05250e0103020706020c0708070e0f040b06040504050c0910080c0a0f0603020f040918030e010503 71
    0x640010014685403141c24500140d103059070004a052003100e0503540c000c4004240c1072004680d00b1500c0c1000203107480030240c155101e100301d500b02d008210049000036507149500b40800148050560032403a118142a03440c01c903174031a1440d1032100c0c0c1c410740c0141c0d583d8154100e03601c1f8501c502c0a28100343d0880c2c0e00c14100f001c40d02d542d84e202c88000684204880c0c1d108004000c800c008803251801c0c86c02c1711030038920344513540b00000e00c2c003100c4840070864414070340b09440ca842c401d00c012901d0603494000252105200440c020b411111045400e00d0742000740c0c42d010041004010001c0c02044001e100341c42c01c11038a054401d0015040c090750001480038000080c0300c070207220f07901030350503640050b180c2d4440c1802c40c50b244003441e103180c11400101c00c0c0000340301803000d4003040d50844030403526001c03440c0b0180005c44009109111a90320707a58014000c245c0700b0340040102150f1450403608007900d54058100b183c7c070110b000302c844500980858109600b04500c035605002c00d0070602d0452 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 294681816 1250 294680566 294680587
    0x906141e010b300403030c1d010801031106070501051006090602030f0901030c26040507290a14031f0e01180c020304090e03120a02070507270c081b 65
    0xa01448030f00074094541c148450202210b0350310f10002c00d804514070120a400c0c1420b000c1c0050514102c11800619003c803e880d108054a5044a09a1042c1e4800711141e1071500c82243d40784100341c031664015420440c13030700443c6c000d02400340110304c90010045c5032860010003070300c03054103644030300c0a54009014440300800c1c410151207444401b828080ba6079808030004848000050303030a0220307000b80705100c81c0346c162503c10091140344284111055591a414400100c00c0c3d040d14036082c030707180b01d41c6100141d8200070103445614418184900e80410840641c205a0811265015214002c004403035000f0a2140150003c1c003031001c0c41b202650526000703101d030f0010f006c10405110b40760600841c4640c401c1040b5002024211010403550000110301c42c0c0b81d034006181c080740b205030400402d00c0c1d180034ac170031a0120b507406002090400e2a0650049040c0741e600c0640041100c4100d1821800285000300304d0107031443da0310071040749801421030303404000641100102c41024002c69142 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 294683066 1250 294681816 294681839
    0x51801060c0f0f1707022e031805120d0513020105030c0c1218030106050646030c0215010e0c09040219020705130912080601030906141e01 61
    0x40e142c02500d41480040e1a09110020b00b102c24030040030030011081380e503100000b150252140a03c221140040c02c4130940c503c2e00700501c1ca82c8043c0c500c8140303c00c0004041d01980c0503100c400c150003808140000b0584409061680c002c1d0202c006010000710070740c0c3c24400f4401c0c154014052803000c1e4058010350002800c42c00020100356042c10001640c00740c52404203d56600e02e54040a001d0f501c245581c2c40703060f031024403410a4041d40c00c1103004901468180d00f0380d103881070100c03021044442244900030f41416681c2c40d40f040d4610511644202115044040520030304540300414584000346000340b414034103884621000803448018881001d40401264010219680c82078440c400040060004e10889405d4103510038003030150052250003081e05021503a084400d10b00380c035813a0503900306507a880c150080808400c03034100240207000e0540590000e00c103140000310f0400564805040b10500c044500c10100071008014101c801801610161915170545030f10551522006000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 294684316 1250 294683066 294683087
    0x9270305042105120406030f110315060d02040603141e0705250506180604050a061a0603041b0602030a0e09070203090a0605031501051810050903070605030105180106 73
    0x10a0b801e1195107090281640e9442c62941040655124070000305188083d40d105205503808282411400600c59075a84034150840301d036a0720f4540f4640d144400c0300301c5107904806c159402242808440548801c0b44040c1c000350403541ca0018000c2d1000140b8150864014160103099000380d4074038030304480c6500c40540046443c100306840700c140d107282103540303125a00c00d0784110100e00d0100c0c0034044001020790040c1c0002d1056207500010307009580d10760300300702d030081d026034000f1140c1c3d00010103540c4034850440c64004140011982040000c10650040d0717820359019407200a06410503142c801480020421400110700e00000c0c00d4010706034003040e0419038400d0902c0400030308114002e004a0f0000030300145000c1249483c0c1c08040e105803c103940b002180c1e1840c0759034a40c41d50050301100c3c052404001420900350a010070880c55400742c1303551074100701081c000190681c408210f64405800c2589032152698101414440d0181962806050b0f41340034500410a07290000d842c0703607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 294685566 1250 294684316 294684329
    0x607050a030c08040b0d0213080f030307080712020301030809030d090513090609050102070c0801060e010b04092a0e09060a050d080a0201020702131d0105070e040c11070927030504 79
    0x500e000460602c0c5a513405a80c1c01359016070030014620703c1d0211103074010501ea0560420310440641c45070200741e680c00f0213400c1c003c450b50081010990842c000c811041c2d01401600d010341800d1b01c42000401039030400c1e84110380c0800f0101d402110740c9014803002c2122101c51400507691031074a40052492a5030171040c146c503650310070558050040e5034000c005415004002950303a01440e2914040c07084d00c034414401c003546040400702d4000038081d0624100c501d0b001480341001d0412000710014010300010b00101c50403410003191392034555405502140094591a052103000410312400d150000c00c1e40e417191420034000c1c00b07195255542d0141e400c0d001444107450b01210349040c0e009104040010b580001c02e10b0b54840704060713a802c0206d0440007425410034040c80c141c4114244d41003541c41e100406c50030019038030541419484000300030000d01d40840344110342d20041c2c0c01e004054010019568071240c00c2c8002c1c210040e08400da1940150072031410340d020f40c070f00071b00c0780c0181e00550 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 294686816 1250 294685566 294685577
    0x40501020d0f1b02060c01020a09030c090b01120c020a0c030b16050301080d0305100f0803041701050f07081003060207050d021c0806090703020409022a0106080c191503050a0b0607050a03 82
    0x40f041d0740310700050320350f1303920080003c6640381c05a00c8058500d401500c01251012425800880c001c0c41703078040d040703c0740c0c010703140d800760101c0d4018880e0141820030110000c40c8034901607032011404444407840110700501e1000c1883c01c10070748010784049000384100034010104010480c211000811803450303003440c500000c990700c03440c1010b0035038680d41d446070150140740342e4089403a0300080f0003801214217124030030b000c0c004030300c0800d802c4e1242114141025000702d000104a240104401c41e84031900050500d001a00e03580d0b11000c90b0000c24040e42c2640c800049103041c50340400c902d202140104811091743e800440c0000c0403440c0003802e0602400018001c80c251074040d8060740c01810700000155140d4a1b8841c2c0e582074a50724001c030781d800d555420136100c4400d1062140d5025910390760b0280c00440c0c4040706014403040880ea850845c2e181e012000a0484040b45010301c0c41c0400e5640442c10f07041004c0a001501c407110b1a461055004002d15030000304005416458980e050070326 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 294688066 1250 294686816 294686867
    0x120809012021070f030c0e060706050703020c030a020a0b010807080601060315050d1b0501050f0a03090f02030a0f030210022514030301060e12030705120d1b05040501020d0f 76
    0x61140030700318188500c440b9a140018008859007201c80c041d40c600103503404101c00740c40301c0c00072540044401041ca810800800ca017402103886a004554420a1402d0152074403e000c000180b80d139002c00e0501c03006030040d41490040040710704403e8010b295000061442e281032096070342e1a214103200e15001c0c0b568032210441c0e0244013409035402014014a032002c00300e46800c0c0f8505141000302041d8500e04500c0d0003103220760003030b000d07207100c00304003401c15080411990003500205001d200a5031010f000919180060740d0801a221280d44038044802480c581464003919109800d1102ea118500500c20003034000c2e00703889003800c040415000050000c0e52420403044440101300410080e000010011a040350002034140d000c1d081502c0188048040c00c04450301ca000700e510042050300001c05001c1c5404802c406011389540d1400c0c0001c0c4040c2c00000800a038605090f02404603c0204041101c2e40c1c050001180309482030404070455202c00100078400070820710040c55054450a9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 294689316 1250 294688066 294688087
    0x1140c07050c27070306030503030a0504110a1a0a210209101d010c02011107150e01050c030301090b06040906090f0c030209091603020f0310050f060a121e091208090120 74
    0x1180e0001c42c1c004050326035070b08114594bc809441c2c203c80030354407010012012881c6080c0900c0f0081120940b0203010318403581440140c0c02e40d0300ca8424401008542d8181354000c046c5020a5002c90010705da0041c1d40b202d5801c1405810300d0000041400c1c40004900c0062035400d00002010401d024030340b240c004400e038030043e1214080b403c408185031045c01c80c0817401c0703100c0140300040040c2a449100b41c460383c0b40011512031040341e007200c0d22604240b00400000016420501d58031000800540c1040c2d00c524485040394450361202e0105c2c1e403254441d4400802c00d10640140704403a28040d0b280510300d0010038441c52000d414543d1113015844040e00d02c500c694141c3d9250503000780601c1d501d00b0406640042290707103000c0c40344646c2c0341d0b14140704946001c4081300c144207503684030b0030003048541c1c801c04010070074010040d1440200c0c484108a02d0020711460b40e10174407400200020340c0084100401c17106006054900a0780b41484103602c14552400011650900340710035666209210f8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 294690566 1250 294689316 294689321
    0xa09060605011b1b180902010912170901050c160501032703140f27030106240c060c050721050f090301060306051e1b0702100201140c07050c270703 65
    0x41c001e01c02c0c451760f0380d10344405c5030716a0041081c80c1c1c000da9030006184e444550174058941420070091254603204030320044404414040c04600f001414054200000700c00c41d603041100307044612024041100e800e0000c1e46c1c040c49206404000500c151140a409210903084c02c2a584000741c1407050450300c600300314040200312a41121403a01254803801c00140809254040e5181040c000e991100d0388026810144280012281800a0b0000f02d81200c03c000100c450642040000c0140c55200c16001c42c40360b0142d900003030b00d103a980c1c907542e0442e424408240406400948460f80c0c90310007485903158010180c4a40e809130f10010343c0e40d00041b400007030040c9040c4d84000c005070300784401c00c0a82000b640111900c6007080c8135200742c03562002c0005445458101c00540310540c03d000b1030b009030400c089400d520243c2030000051518185402244c55603080318141c4600a000032071100700036091024518003841a80c3c1003101f03880c01c52000c891424043c0d49003003180310a400103010340340b080c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 294691816 1250 294690566 294690569
    0x80109110402031b0c0328270302062704290d060f020c06090307021c0201020322050f01090b0403030e0307170d08090a0b010303110c03060a09060605011b1b 69
    0x2220010f41d68100592195229005948501c408921074041031510f5170074019000c0c540a840c0d52a08d03605450b40f80c00501c0c21413401c2503a880c0c03580c0710708080016140c02004011941c1c00d0401140b03400c101c0307071103010000340c184110350180741000e100700041a07151320303155420b4400c1160075a100104502140c0c900e62115800340c80c141c2000b90349541c07a411903009104500d43c200548440307a945803070290703a0384a594402500022000418000d88160030120030045d403051054a242950303008101c0c0c00d1175003003101c868014081000c200850301d44205070140c0241c083c2850b40e2560301c0d04034131034524011840050140148c03c822201c4690b003d100c0c03440540180b48110142601610a86130380340408602d00c0080382a840209900100014003024a5540450706038001d07030071968101e50000104102c1d0b140da00c201c0c1c0044041d95011b015583c841d02c9084000101c170440ca0900c4820b03640683c0c0b15a050101246400c0201141c0038803c03801d013500014400c40000184d46100c00c115050f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 294693066 1250 294691816 294691861
    0x30a0c03051b01140105010912151e0c021c0306060203030105090a0905070303020d03150e040f05010e01060b090406090203010e1302061201060c20010e19081203090708010911040203 80
    0x4e2141c0c424500c80e40c2421130f4161042a683d0355285504c9501c03034038541031160700207170240d20504a8080300000c04e4000425100070040006110b800441c42c10064404900e0090090b030041c6200c00400c0209601a0355100e00d21b14050094a14004c0d01a4492006001340b9001e00902400108040510742084400aa00c0411101d02c69580d0600030344400703003442c1e400000b82c10001841d250192080c4060155840d01c80c203101c1545803a0b5a10260740702d200c104807215501d490038109840d200307200d420001c00c6240b0303406542c1c040d80401c0004403109900034041041c4140010310845440000d2142d21241111800310307189114000190f882c003920b44428200c2c901c03c1c0001c203202e64001c52600c0300c50f1180c521000d101032184218020305059514460006201050350b81b018540a81e07207201c54030100208021403903d9001e118180f2030341da0604100d40d4400070900c031107078400300000c0c4020329000d002000840199500c200100c9082200d40f841981c01101189103c104210500b904540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 294694316 1250 294693066 294693071
    0x10219020f0a0803040b0c010c02011a0607110a0605092106070c0303090c0f09180201053403020f060a05040506060103240f081908160507170c040e030a0c03051b01 72
    0x590310449006c55000304800e51036542048040d070401401405415106111008100c03c1d2586000a101c81a003151000b9103002103600e00d0300020741c072a80c21640c0580341c55500d06a07540c0707840c0c0c18440070f00c90a15006414884400681c3c00000000c11050303003111051424500d200e020382130450181000480140a184e640800002e000d0b20584160084810590341446911139903104041425680b0380c0c00303030116108006503080900156600da06084200884a003610384050000b800c0a441200480c090b85c48054001d402e49002c00c00c0c554003d81951060140d46030550740d40f9180d00020340080d05051700e85ca8001d9609840418000c8a00b40e24181d00d194159507050318500b40503d480340c10407a00410401e8480c0c840d009201c459400d420180f02480e04641d00c600c3c0d0b101d2510000f044e10741d0300413280c02003480c04004180082da15001c1000388007050904041000300c074800044040743d98130401c0054509171300f0200380d00441d909428043d40b1381200e10261002400880075000e00380d407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 294695566 1250 294694316 294694319
    0x9070f080d05210f0601080105060c0c19120605070314070c06110403020301050f070801090b0333150a050a030b06125203080304031403090c040b010219020f0a080304 73
    0x1210511301c2c89131800f642d44030003d0742d8800500005105900701c8000582107100704e01e0181c00c00070f0300038020021214805140503966178100340c03885100441120f81c00d8845051052a0764180244a1240042c00d0029040d081c07110000d440ca08241d04c1c010300d074a403030380b806400807070185068400440d000b800074822440c1102a90400000803207000c0e002c01c3d402000030a01003044c0c86008514940600140390314054058401c0803443e140c6610404d520080c000c8000e5240b00301c0c441c0c4d004054840081503920038140c100014861540c00032401a4240d000070008140c1340403900d50404801e42e502e160000c2211001e5040090280c0200300c0d6104125a82c0c00943c402c01c0d0f51811788030030309004954003400c0070382e0b400f40c00b07403200d0f4180d40014048000c0c80410128070045420031301c40d0611031185001540c218209410403541c0015a4014a43c0b11049007442e026580e8961001d01c0a09103400f280ca40440d000340d000384010303000b084032200310b101030307124078044501802c22042203130b4946 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 294696816 1250 294695566 294695581
    0xa0921080a0507051b0a0b0d020409060816061d04090f0804170705040c02060412022a030f12040b0d3308030f070803061c0302010509070f080d0521 65
    0x6900c41801180c1074810410301d40382c1d80c1403030a40c03c064117500800b015410791801c3c1e80400943c000080807032800380c0c20880051401d40e0780c86030000403e00c14001d000c600d10720740d58140500425500c031000380804d6000f070b04c00710400d01c0c002210590301280c001924054900300f0001b1104220401001110300060201d48800c401c08031021400ca06c60403200c3d250740324402c0c001500c1c50644d030100541d01c000046400243e0345031440c580101984101e030651201d04200c07210400405500c101d071403040741c0303204401c1d040a00008041c2d038101ea0051000c5039804140317001c24807852081d08400d0308045810f6031700d0100760f00aa80122030310003603104240e2a800100d4420640308550b51175101c0f000000048000e804416179507494000300140e42040601e4480c0360859100030902e503801090640c541e403076008a400c403a41700074002c7d4000942450140c100501d4040c541e044544da00380300c03d0081000312000282d50340800c119127000c9450f10711800b8000101c050031200c00e140c034041d00c410800b04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 294698066 1250 294696816 294696827
    0x10050a1a030a05070c1a0a0e121918180e0607090302040c05130311030c01020609100f0905060f070305010b251b080102090315071d0a08100204050f01050a0921080a 72
    0x52020403000c005100a023140c80350388201103244454216002d0102c01d4040340003010141306016a400c1c0126100d05140c1940c00a8210340c101c03c1030386000c200e4021702d441980c4940d01d90440418028442420095400b030100304051200a1107151030b4120030003414402d80c15101407140c600e81801c403070764a81c540075052803a9800a00c1c001d1007403a0502400f58170002c1c0310741c00b48150001030450740440a080710080c007040400c40030860f80768240340b000200f0810000d4402e60308000d07054000c0c2800c1800170103490060b44075111800080c05035818100105100303004c81003881d500b00740c54115901d003921034a51600324200700203d50740c4000a0001c0e041d002070102e418200e05507118a450070380f030308006075001c1c0d5140c40014080b028101c3c1100388500911042d040003850a84200d6441e403440346000d10b00030300203401c1c0381c000c18100141c2c1003400c41c00342c115400342029030604803450380040502d4601c1c41160b02d03207a60410b1050272440710001c0041d00542212809aa4442d0b5081c007408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 294699316 1250 294698066 294698071
    0xc01060902030613050403140310120b10060f14180d08120702010c090302120f06100e060603010602150a0204030203160311040605091302030f01020310050a1a030a05070c1a 76
    0x14001500801140c0c801c0c4e0b10900c0d201d6903160b2510807a010b860080840305820080c66240c240380c02500210b8200c10080d80021001e00c00d2600244626181c2c286880c0c026013940000c0600440d002400801ca82100e141b034400807841241c00e4039031200b04402c09040783e030100c081e50402ca07100c06550500c0118402401c941184181c003003419100c4000c200c1c2240c8144400c0c00008403240c40c01e00c014a40302201e102900c00400481d48402e6001c1c03903a03814a0000d60303105003130094408013009a611002e00503584400f00319511811589407100194031003090b2800350203620561000a00b072031540c1d50668001c0d6801074100c40504d800c0328114180301d071380350206551402d5007121200051034540580d80a660000d00700d05055180c000070489043e00342030007242c2c1400b8106034a078402c002440a58400c904290248250501e02000c2c0400716246400c85032109140000d00803149508030204d0750401c84203480010166254142120213003401d482c0148a00100d110a12041c1014240c507030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 294700566 1250 294699316 294699319
    0xe06011a03071d06091009180902030307080a2006191e0b150c06100b03130219080604060b19050a0b070204111b010b01030e1c03020c010609020306 65
    0x1811840200800080d80000c071a048002020182c0700c0c00c01d850110320b034903500480a0600390400e0310340000282501c1c9030000120015500000c1081007a01c40c140c51104040b403d10300300010b20729500404e0f200e2280200140a030310000404001e0b01c3e124034000ca128000c0d0040804280784079082464035601d09640c650640c4c1100b074031300c00d0349500350b01c2010100e00020a041e62048c0303146e101040600b0840076603d5010103070a010b103401c00700801c024204060070300080c0185d440c1c4503c41203036840280d0049055220305108000450400942c480200381e0121400740e0868564a00198400342a03080b1200341d016210510080040d03940140c6111503048a20710301d419840100e8540600061184a44c05040440c0800008040e000140a11800517101107400d02e29010407030020ba01c03030b1401419200e1014140c03030a0035001e00c01c001c400c9000b441c045c0702c02881000c0302c03940c0b139080d50150b80d404810102183d489034043d604582d0000000d00c024850907a84840e04002500201d9085 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 294701816 1250 294700566 294700589
    0x2061305121005183706060503010c03050402060412061e0c0f0f050d050603100912020c06090f060c0a12030b030601090c140f160c17010501030309090207150e0601 72
    0x200340b25070a14001d107984e4079820040024983d03d1140129541c54804220291044404800e81a140c441075181c4414043c00e00494070a01d41001e05085451110079501003500d008140300c01650707410b00f141e0032100b1130a0081103045003070506200400780d500465000303039400c00032007603004a6600142c0c1c108609807102400c244007079400b641c08285040b0303400c00281e010048000f14040350350100d6080718000c0c0490720480c0c1c140340b52608889880405840c1003200e840b8038007240f6030400040840705e100703540c071600b40007026000c9040300300d010300369a118010101d1026101d04040014101e45178001d440c0c44841040c10304050b0062142d501c40074000d004000002c1030705051800707401e11003074041e82c441002440410a507040c40c1c01c800321b070510758501004060341000320140030100700c07801020052000c4e480d003a040e07054a0701180814415074140801040071a80003d0344800b11075107d6000f50b41d500079442c042c100040200e0500c05a00e1402081c40c5000d00c0c0010010f06030f980103010b1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 294703066 1250 294701816 294701821
    0x405130510060e22080706090c06052803180b011a16290a0213050d020a0b0d0603080d0c170f0613020f18150403050a02061305121005 59
    0xa40050750568007400343d40d40d00000214029850b88001042c501034030390300d402d4a03041d5039a6184042e500c11507081d1103594503143c00c0000c0c80103c0034498018203d03400d00500d40090031545d5640c00081c000030314000d140340109196018001c1d00a61242c103610400c08000301c01d20325050300400c00a0055840140291408884c0d02d0b00d1003040b50040c14004c4038500d5222020b907284007400101c100098500011200e80300c0c81c0c1c0064241440c094000f03070304096124080e52100c1243c0c01c0c419481140300c1c2c22008681d20168403405409000e50302c0f6041429078940f11010a00051300980d80020008200054002104541540801d86000752a90395450758400140d01040000c000e444079001d4141c00350101d06545040b68403141040001100503040400c5141103d20503084900303d800f02c1003859200000764a072051017510b608032007503200c40c20306040d40c5a09070741d0a2813200080c00b80c0c50000e454900c4d6241d0007014001040c00420140405400d0024160ae40001c030f4000300c0c1c1203040c10003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 294704316 1250 294703066 294703093
    0x10804060b0d0f14070b04030b180a0b010305060c0304080a0e060f040e0906071128060e0607090806010815060307050603130b010f0b030f060a0e0106020c28030f060b04051305 77
    0x1285c04c00c40307117400c00325810305081d5190b0038051034014005000c01c031601c8030087c0030780710140400160742e4000d00140340d0640c954100307030781000c0c0c0040144218040030000c000c0020010000d640340c1010300e2a1040000c1d200740c002c80e000c4d12070441c00e4400c1c04004140000c83d4a0750031101480f80b00b907101540d0307003511442c200b9235451a030100c0129031608103840b0f0580840d005074045207002c2850700702c102051100d0f1681d0040340d030501030491994100808100c82a5049000540180300550082c07950b5031410318210b1b140e60824000c2e50b9079290f06400301e04266001c00421010f410002c14030f0382c0e0390a0a42201c4008450faa01c12509030012800005201100154135002c80d61140c2081d0314650700d065a501c152140240081c2c0d22030840540418000a603c8245010b450170381c00408800d1860410000c2070921001420781142c44070704018060444841004103c0364880003e05001c0c01c14034000020f8401c01c441290071500c3c1200700705154842c00244144c942c010416034081104020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 294705566 1250 294704316 294704323
    0xd02090a36080706060f0306060e0601020c011209020102160f05011e080112020d0515070e241c0c0504090b0f031e0307020a0905101d0402010804060b0d0f14 69
    0x1200c0711a886010501c00815024401400b01c54400c02000502c0c1e40c44181c4002c503058580c0050715900d60318a03040c00001440d900c1c2682080090000381004800703500002d0005000c210302500844d10741803c03c0459008102c40c40c9800c2c0341124607040c6588500c2c0c00c404a0410348110b600065105c811603080d540310103079240b18408140d40c0c1c246560b00741039041085220013202240c0144e07507481c02c02e011070760910800240c114402e0003407400c0d0600c2d100043c50103500c1119288111813030081e2901c402c59a0750948100030b0201503a0381c036010340c9240042c0091940c0d10341c1d5500760410701155000b5602200038025600515401c000c500e070040240b0900d0807217400c116030154000140b0307044000c2100b5500303104000c1041201c1c0381c16034560100703610f000c8030340c08080e55135103500900001c3d80440013804040c0042c00714045030307040440503140440d0000f4001905105c820f801080a001a541010051800180c13491016104a141503100f4082c905800c2d60504100307401c9108003003010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 294706816 1250 294705566 294705641
    0x90608071d01110f150a06180f0e070e070212030108030d2004060903060608011b03150e090c040c030c0207060e0a08070605071203050c0a0e0d02090a 66
    0x555a01c504180148601100a420400c0180c144155210300801c104020000040700500400c00f60008000441c1d958940101c0546030000240c1080400d00c00011036031005022003801c04c90101d03030748000c031207a400184181e680c80d203410b020300c0401007011700040b00f69074054252f07582225a20000c4500007000f0340000c1c0202c51031a042002508480c07000b40c0c1102203508000800c07940569a0b405c214442e650140e8414008140c10303103010014400390348a10f50040071501c009010005c42008801c1030024078490130300a055444a1615095990148650251100300e03400b0705c940c109010b1480e03a0703903100c44400748140d0034850201c4050b44070303014401610110b44c00400185061031001c0e5500361150148513000440c620002440040403c100401002c540d20f40550300d100d5400c141c04840c4124003a0300c04d140c104014080c070b6510550441e249941c107458402480c05002000800300c080d812340203075005800e40140081c200040d800002c0c503041106c2c80c2410041644c1c607100c04c01d14103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 294708066 1250 294706816 294706831
    0x3190920040506010e120c040204090b0901150e09070c0b01032d020f0d05031e03040c12023d0201020c070519060f050d05040804030c0e101707030203011a01090608 72
    0x5c1c3d40e07501055060800b00e1590034140035003a42d80b00441e2102040403030b00181d0000d404203455904845150400401d110f014101c0d5103540f040140b032200d0060094a04841014042d0303d14030005400320384165408040d01d0381c480c280c4c03005540d4a042ca000400c560359072031032000c1d4140d60075100380c0c850919942500c0c1d6010381050004807014007000002c00140c9000e54030b60104000500701814400080314400301200500b03034884c00e107070921010b182030b290030003a000c0312003001400140c0d0302c2c01d614090b0314003d440d403c00d010900c0070710b4921010203e850464011014040c0b600035070b806401820710190713020211500183e980b0100b0000e29440c9241c500ea4401d100b10500c0b10602c01da040c0b030300160390b90801500d003d081001d00c0048030030440307080c0c0fa0440701081c2442003103040c0511174000d1001d10120391142c1010211011085050b03c682600180700012040e41034805211001c0211340040003040411200c005004181013600904d5000445050300400c0b151700030361180380075280703 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 294709316 1250 294708066 294708077
    0x81b01020c1b0105160b0601020f06100303090503060f01151707020c1504050a09050403110a1202011d19020f040f050a0605030a050d05070201030b06041502060105010203031b0319092004050601 85
    0x106d4443c200100c0c00941081c0c110300500c50070307241019041045601504940c0c00c548122803a5041c02401d0b41d0550b08082e2094000105000c4c02c3c1555051650644040040c10800c1d07001060007910700d0a464038204a40c1442c0800300100640c002c50203041d021070580310004000e4002c000c03204117100e5801080c4d07000e440e02d8030610581440380d1000354080e109003001c681074200d1305203452a0003103069085460700d0750441a03158503030382070203050812140175049895560109904640f240785404031a084000d40500000c19941c0301c01642080d81c1c0060010021100d28000d104082d1a0490300d0071100d41c00c220001990342000a901c515542c0c002d80035020042110740700b251070398030030034040c1d0405407210314103c03082d95460b00401c010465441c0384241e01176100c0f4040d06101050b84030314195001841000700050081d440410b00c00e14001d83d00da500c0d030301c0c01d81d440b20111000c40c450b41c009242c604503902304002000441d402c0d603007071250301c048a122542080191642150014000352 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 294710566 1250 294709316 294709357
    0x6091018050a0e070b03071103030103020f10020106210c0f060813060f050c0306010f0305070503060d0309081905070e0106120c1106040b01090c0903020d081b01020c1b0105 76
    0x485651000b6001402500c01298816000d0035240c44d00040d80c21142e9809000010300ca90143c20641951884180002450a540c03440d00001c100c2183c1d41d1059000b20055040804424801e510500140c110442e5024030215030203010010f6007180b02d001caa02c0d403085d100c04241280ca003030a070340445960340c3c1c1d8401d8a9440005070200288400001c5510540b50315500421810303501425128529507000c0d15101d142050006112144006079001030500d80401e0101703a9901200301d0768807450556030303140409040c0c9022071704d42d84240c0c01502c060086001ca0200307100704444811816000c0c108540c07059072594503e0003410800e02c1814040380000c5100501e000032904020410311050801800c40c6051604031400d210046038101c41c3c010a0f4401801900914825040c80c170003a40740600d0002e04580c08221150290013024005280115006ca450f03001200c080d4091a440e000940d12811141c401030780d01c6075a580c004500c178080d2440e020065104800340c541c1448004101c0758601d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 294711816 1250 294710566 294710609
    0xe01020a1511070503070807031b030e060a0203040329070207080d0c030e0315240108060904020d08070303060e060111031209100908040e071b0b09031c0203060910 72
    0x140b02110041d02080414000880800c0d001d0000c0c00880380100754550359540d503403070010b145521100045a0204002c040758000c00d512280d44000714009550b07159581c0c107200713402e03455805682e00007460b4050341a40050b01d01c030421086041091201020105500c8401059844849a0003918490340c0b0014201045910a80ca04060140a402c0c40c503821001200400d09242901540080350614a41403018000040c241c0310340d40540081c00343c01807409480020f160700b034040e085500c20800134020506541c1e500141c40d8025500081c3c00e680d8100d2841c000e005809144282c180e1800c3e0800098080e5004e280d00c807402200180c091407410381c1a0340c2c0b0005005010701030017014881c3d0751210064110074800d00542074000c803503072a1075919064248000300e40c000e01007010006031406074200542d441041010944d44080d03c07141d07035500c10000c1c514500a201e0340807c3c8130034100148808446907402140188400c4e00c094041d6503070342150b004d42d0700342446a00c0c0309035000c40149008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 294713066 1250 294711816 294711821
    0x110103020301060225030803180709061206110408010c170702061009020a0e03030a030e012f030a180f020103050906040203100c0908030d0c08180c0103020715090b070e01020a15 78
    0xc0035501085c0e0b1051710317511680160f81040355450008031003103002c0c1001e49030401090b00100203512050000500303045d8401801201041b0003826603841d06c81400c510768441058901600405d8000c12208241680080804403410b010824100c82132020459080c8041340f014418040080c842c03904518040c07899000354001c00b5104200900c100d60796400c2d65060004010a001c246e5005c982151082c4490742111343c11842d240e20128180306520790fa03200351000540c2c40c0a0725900d1030701c0740d0f42d414042c806000c00030305127a54402c030070445004001c102400550f059000382e804006035034070100c81ca692150142c83c0a541a44400100c509212041d0028024180d003440c144410f20f9643d0350719482c0da0059031801c040e45480b0210700034a107904c50711256002040e11440c6e100c481001c17420645500c3d5102802c0d0400d0740000704a0280403c141c02061a6900b0610422240009040102c0e07c860243c866000080c0a2200e212141d0300c001084014540c201420a46030196810107000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 294714316 1250 294713066 294713113
    0x203030702100201140702030d14060904120c0f0318060f020a0209061512040501150b0403080f0708071101020c01180e0709050a080f011503030203090f0f06161101030203010602 78
    0x4540d00c42001c9110414485d0480340a00b04030340056481d140c003003a203142640c1c10320b035284604030725030410007032903546040489410a030045d0019801c00c8081a04680c0e904e07a0b5500500203081c1078480d0000c140d81b100c1c000380e0943e50900485941c54545208441b00a0b20005110040c0e014030381c205c01501e005806207402100003000103030f1307407500d010283c00759801c40c90021048076015010131050000a000d076500d44011251101000ca0034410013075068082c501020309001c00c080303004824000c03d04222510316411005040e02c4c1d80e114a040320a52013040409801802015124205540a80100c031444003404211710841d40c108001000c82050040c9030a08211402e900005c49880d4010944050b114800181c013235025040b0b04142519040501a03c400468480810110340d001c03054400c1d10074103c60006040d01981c0000707401840030981a68400e40001e4901c000c0303003090b005414054860b080c9603004802201c0154200e000034443c48025810100100441c500303409010785 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 294715566 1250 294714316 294714349
    0x15050a020405040f0b0f030f1207031211070204060806100308090301020f0a110c011b1122140c25081c0506091b0f0c01180302030301210203030702 65
    0x1070a00b5a680700280559103202a400209076550b40100c140782000b2010034080071044c0c1c0280880c140411070903584417181010703d1404080461080b0030148150300c1e03041e110f4200034050240ca050b460b240c000c0390f0310091080b8032580c507241700029400404152184100ca40505911407245541c6034642d840c0d01a50b0340c10b526550030406a05e0319074101d00580908090795440d50f1f41f4801c5030103103603d80041070401c1c0d418421403051094a400b644902c0f02c0c030140e0b0080b070801640b03400c6404518a1503c201d400c600040519601d800c0c0c00941e2ba000503020300e6200e071025056203402040304080d10a065107403104002c091000480c180750583c3e03956629208140e42841c0c1140026092000007001c00040689501c920074401d007171901002e2144c0100d00c1c008800d000c1403001306491094030030f42d20f103010304060210b100c2c60304e24420361161440c035211a4003c401d0b2030040c54029100c1e0302c00d004103400128030040840985521a40e10768501e940079000b1450305005408021000602d0310059 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 294716816 1250 294715566 294715571
    0x30c04150e0f16020a0b040f060e070602010c0e0603060a0918060207081201270b01050d15050109081c180b1810020c03190c0305070b030703110715050a 67
    0x540c07000e0112200b440ba9a030500030000e40c1c105034001d041e20200210801c0304640c40903820b4400b00346080601900554400c80921902c070b03503480e02c04003502019041060034020320f203001618507019045204009400d69441c240d1150007410450300e4001070301d1442e0402131800003403000c00401ea00c03000c00100d442110b40300024407a6200d1050f60f00524040383d440030b000c1070076200600c0300001c01340940b1047c070700d200100c580c0209004103040c035004048401038803491000c206900407012943e4007400342c130092014002030000d40103a2121403240360b0009024441c0000d40030804a81d41040c040a507070f078222924840c480869001d9801800321240305001c8074001400030291000300000107900c00101e0880702c004d402c120728108041d0303071482550400780c5d051a03107641c007050304030203203240c0072191240e89100d0070718101c2e481507500010114400c012010a0406020780654807950b15070f40c080c0305241071210440c6090040444c002c0041c0c01c1d0012080d04507589030800c980c00380145900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 294718066 1250 294716816 294716819
    0x109111c1b0b0c010606020c041103060f06041203050c061b0a0f12091524030201050304060902030d110d0504030b19140a020406030b04020910110705090f070f0e030c0415 75
    0xb9101c2540051110310103a9511001003200a03010300c0b041441c180100e030100806100c10201d2020303888001c0c140f0744512000e0404000c41d688000989000d4a030303003407402100c00c04c50b1401410741c0d4030403100e6441e00e106040015202d5a00c00c0c0c61800c901180004050410f412100140e507845a60000d00d0f080c001100c841c2c80d5002c0f040d1140701d00245c0521212414002d42105c280e0881d2a01e00080622861280f5624503141400d42600300301d1358286065940c07136565003807400041c6952903000390305005520042a4080d0b02c040c04d01841100142680d21401c2681c800342d0f0302d4400d900c0000c0250340040002260b40c0c092148520040c40b40030008a20100809400800c1e50400c85a00c02095800b24050284942c184541090248280d0b01186450866000a2414101c0d1240c020802124541e00c0e00c842005024030b0380140b002a020000c03605006401450a503412202070300010b14080340f00c1f1110f44102c0d03003c18181c401078094100204041c00340409042c0a901101070205102030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 294719316 1250 294718066 294718079
    0x1118030f0102091804050c100f030b040b0a1401091d0108060708041a0405030c1c030e191e080c060a050a0911120a0b010807090b01091d040c0e090109111c1b 69
    0x41c8c2012001c190381d4002c9144284000941100c1c2e00f20032007070003145040c0d042c0d61540c81c1d2040140c00c0e601e4064500d000b803030451004032840111794100d100104143c03040711024140c0040700605030307201502510220740d55010100d0f841901101e0142000c0354400c244000300340b81d421082d4103d800340080d80d10380f9041c002000d2a100c9001103c044d42008502d2841141d9494030607030f441404140301a086200b14403002002c45503d00030040c0200c00d17a200c1c0641800c664044400c0000d0b804402d46480c1c145074000d2507106e000c101d600c01d0301c0604000000d0868801c5125411100758008080307603840202d6001e01406003015611400c0d98811300742e00f175000c90100c8210a008110400040c0301040c00c01d01c0c00025a00980401d0f0f040c4051140140044491a8020b07040d410003100d0101e0039680724240560360140b1035100c2940e1003802c030140204200190051001d60b8010304800d0800200c003c24020b5000300c0c0c40c0d10441d440010b004910000c2c03c860350101480d0052008808490346400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 294720566 1250 294719316 294719329
    0x1209080702030f0c030613021809191104140108032b021605070503060906180c04050a09020f0609060f0313021215102301031118030f0102091804050c 66
    0x10010007554001500d5074054170702004a1a8030400c1c40140a000e540703144e0200b41c128807004400c40c0018540f20000712802d601300024548610082a00c04030080c441c10501001071450045500882c03c1010200c141004040f201d8101d48110005614003c440340c0071f20b020000c41801402000c18a14154543e038039540048c0c500031102e002c9294054245103805031611045a00290083d000902002031074040401c4003a4450550340b6888001d9280b01c87c0039003010590700b109a0310034500400d20074490103560080d602c02d4800c0d02c4203211803a0240810103a40075405035185d104008201c22a50241e003500910380207400180e041d03002000355400528440c1025007000002d0303000030800b10000080d01803003600318445001d4034404906012001c1c030a0b40741c2c1240800d1101800b40510f149034031950140940349002e200040e01c0e000030100c034014100c18100e06d00e11906c0341c2d185c1d40c2c0c4440410320072100e514000070186d0304400300c0030294101c510b000510a4605001d962450107882c0c85a8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 294721816 1250 294720566 294720583
    0x30f0e0310060b0c06010812041703070b0a1e0908030a020906120f0412080103030212070807120e0103060f08060f10080a03050706050a090309050402130f03050f070503030a120908070203 82
    0x7078103083c4e25100c0b02c0311071a103007150580c03007640a50f0162800003001d0586100325010340e0b002203c0b0f0503101c201003292620714400c4001c01028507458408020706c0741c903298804902d0702901c0d4201416103172480f6901e820740c2c4004001034401e480410100d041256103900815652001500d0242004040340440445800488640c01c0a14542e010441002a1148420751188180c02c02000030b50441d2402903031031000102d02004040001a40028001c00000781c03044c40707134010305085201024400c014441d481a00c0c040340424100100030071030327816125505c8103403404580100582c0d50b401d9000004614050030014070f80c950f198000c030f108e44041c031201516a0203a00c55507a150300f1481c040040719401820005543d141c121a1000a50300c05040d4007120707821940907868104408400d01d018019902000161911000000800c200807540064491103202640da045a41da014036889102d0304000e800000d441049109107003100e0b41c4203542481c043e020513400e180392580403070701d81400d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 294723066 1250 294721816 294721829
    0x102070314091f0e120c180408090d0212010c09050109053f0703030306050f0a060806040e03220e2206020a0e04020418060f06120b0f0a06080103050c030a030f0e031006 74
    0x1800c411b0850801d100c919001c0f040c1c0c81b04030425460700d519401c181d80a8240714a201d205404201c00641d96071a200c0f000d000c00340402003088142550b0003501c0640680316150214015490008030780c504a034000c1a00100c4100c0e00c0070b00b08800b50007040c0000c404488690950082590700410f41d02008208003071031198800141c03072070411040040703402c8a4110a8415000f8901c1403008581c041191074000c03009440c0826100345146050f404c600030b000c2910500c444091100750722040060299085902c04070b244d02041e1280c441c00c00c00d0701e01003541d1003a0203c0400100380055903d500407c4161560f150098002c05450002000c1e0f9000364840008000e6005616080600e188940e00c0200b0551201c0f48034a460080c02604c00c04105100c03a510b1651800701c1001c98441900d0890526001007400526545a00000c0d010800a00003130b10786204100e8400d04900380021143c180c141c01d622541c045003001c2100b01c40c2c10081d5415903400d40a80e0b03402d00340042c080d0007510040c190 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 294724316 1250 294723066 294723073
    0xe01121116240902010504060318061509050609090c010c0302101a0f0f09190609050a05090607090806010e0c0903010905033c03070504080f0102070314091f0e12 71
    0x1c41c8020710055075504600e21180c2d85400c000c140141c1c0c001c030842c0d04a07111402c2c08501c51031851040040201c4d0150f000d80228107111036000b50341c0c4601520800d07520581001c1109844030014488c0066040780c0c103000b1381d40801d11048030f560241200510152092040722080302c0b24082c03007015100260b94114000f00c820200c05c150745070900150710b2903607007910f00454411404c070002d0581c200140603050030800f040d241041e20040f50700044007800700000b0510881c14410300510007004101c45840307040c001c990108550b14442c0c0c001d0021515060000c1885900b0f0000e01086800c0260030703c500e01000b0000031200c3d0310280142d540c5507021340080c64903125001c6d58502591a06001d04045560203990242c2110b2503c20718045d14156440c0191680c1d1000c00c140c0d281c2c80742d500b042440c1e00c1401c40521040d40705400410100d80300e40d40711004141c4c2024501110300581441c168400b08203000b1114501054000c40c1100c80185040400000311501083c030404042d130070038542c0e81 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 294725566 1250 294724316 294724343
    0x120109030c1e20030a0606080a060b0303070507051c0615080d021203180708060a0b100905030c01030b03012309060f0709030809010c0c080c09070e01121116 69
    0x82205459881c0c580a01002240118030b41e60303c0950030b020b00c0074403002d54001001030304661000c0056481d50703580842c0400030b050b103500103595641d44040c412210a070404660700340750706010090314401a48140102070303450420040000e074030380c0b4001e110b000c441007a403044042049400740e0007284140b243e10a4030b45080410f641d081042a20b4001306540c0b15200310788122581204495018010b2194000c010304e003003c0c000e003444565030080c407003031050100b402004c10090f48920000740c01168802c4507043c402d541540d92103030910400342d142d0001c1c0ca41404075402030300b140031581002000028a540036022004100c10100c8050030210350300b000300847d081d42001600d80113082c003000d9440c0b500d0030210083c40e000309404010b0102070701140d960f2059000d81c12a40d0007540c4124120310494039101880d544420098000348a0010074000c100484d000f582011b0b03070701906a49100f881a01d0b01c10100c00b42404480010000344108010020440b481484100391445042200c4206 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 294726816 1250 294725566 294725573
    0x2040b0c011407090e180319030b030114060904050a080d020c15011a0705010e0607030b040c090501140c030f0a0c0b0c031e13020a03030206010f1a04060e120109030c 73
    0x181c10000b21030700704403810380a0000e0303a03400c400d0345401c03500300e40710020703155488503121801038003402040c24140c8004100414038240342043c0c4040c1c60b4807581d0030402c4900140400d42607c050f419440c044440e214041005411718040442d8070174002c40885818840a946142d051380c0166181c1100c80d50202d04a4010682804050b00360304030000c0611203541041a414000d440c0c0c201407410064001a1200402c002900824200d54008003a11481c0c0ba0092021300038000c40b50312107118070314100c40d003541c06004000b450f09580c010794a2458100400012150940c841c000050b41840288036000da0710010300c0081074484417a680b0307440300e48404d261100c00c2c503a000e002200c10540c24001c01c80c3c41114000940e1103a02071802c400c0d602d4891882607003003c0700600c008ad4004020403804000c3c0758000030141d04a030681c140ba200310640c3e58500c81005a4402940c0b0600e140c1008104201441b0304000000444014002c0ca24108040b28030303402c5070101001200440c0551510700c090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 294728066 1250 294726816 294726821
    0x10f0b1605120a031103040c0b13081b010f11060109020d02070803040f0203070b04122006030901060e09160512012703080609160c030207050301090507080c0301020c03120402060d02040b0c01 84
    0x945d80f480d59490941c05c0564510035070380000d01440342d2003130340851b1140c040b000413103107180109220300a440e006e040318020403801c2c0020300c66076404502c00c000b030301c1001c501c076401001d03405003031380c01419090b400d10a10748040e52001c0c0d10483e02580074800b28012403443c00085028500c51103d440303c0c03100c10710501d418500ea640c000100703120148410409034107005001c0c0d0100380c0c00f6000e201c03804c00c05004420000c25003551160003120120800c1010303481517000d401600c0e1051040000d954454141650700ca104c400712017608002a0001c02041c00c10030324010b05618510b001103048504905030003c0c4a90300c8054060448080c84d1600038150024079890b0030240c01d4405501030f20340741000d8004441a441a14104400c0c6000c0c0018144240820b402401c4014000e00100c1d041e4140300381e8032030a074080c2c504103000340c900d04046444c1c14400c82d050801e00f030024504108120010201c039400007001a07070001c00401103032040541603c0104007401702a00c801c1d885403e140c403440e08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 294729316 1250 294728066 294728081
    0xd030f0c0207030302030a08090a12020a0311010501060c080d060512030a0806060a08010e130605130b01080d08010b0c161706070e0a05120c0910061403010f0b1605120a03 75
    0x554010b41c20900c0841d0380402120030112850070400c1c4d131030b00c40c21040c903c0e2007656500500100082c401d40d0410a40c0421640541030080d038502039500300301c210701c0d400c0307500030f10030b5101080d000c21504000410300d030b01900a514620f480010501d9542000c6000d00f080000c500c480c03030f040081c1c0d40301c020f50070480e041c2d0040029103005043c04854100074014440600501d0741148228000590248031a42c4d04502e0540c0b19405001ca0b00302458503901c0c00050540440f5140380c103200219038410000341c92650342c2d41c10303a00c8200b940d18284424040c2d40c060081e882040c01207541d1204082c0100c51001d00401c0030010240459188030462810504060500410041802080d000c688e5540c000c4409a6404441c4121264802e8466619140f0401d107251781000c038042c10410802078000b0200100ca8040d284c0d08002102e6880c0001c0c00c0c80240610700100d071071014241302d0114941c02130100c04101c190120101840c0d500c0d103510b070519001c42d241100000042d10620258940a03515 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 294730566 1250 294729316 294729341
    0x70f1206050a0b0f090a0b0414030303060607030c1a010e010f0806041703060301020d0f0504060c02060c16080903250501050406020a061a09040b040605130308040219080d030f 77
    0x806030070400062420300700b611403007103034240104801000710800001c03070f0f0300300400a0404024654030103412920760840c0c410881050908507003440241000720850b881000002c011620b41074403035030300340c881307035a640c2d01600e08280040b2004445411010624040c0c2800c0c0014581d0358540f812030842a0002c0e08000015000b40080c00001030145540310300804e080c4031490b4480e40c030000440e00a000361110070300c0c1340381007141040d1003000c25032190340903a0250f2428004601c42c1242a0303580d007002c1c0d8003c90b103808200100c04604504000c1051081e21901501c0c0c80d0550303a0300081c1c50080d800031407842022851b45014907034406a240500184801c2c01d01a0400d4607000c030280d2207090b41c900c041c19540c0c540d44800429a00000da64042610080102e079403800c060804504549048800301e642600c0c100c041511044080e4050b903c40d58035070b590640c00d55942d4240402080d01e1055004145162540882d800c001840043c1030036440da540024000d04016841080c1c810214444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 294731816 1250 294730566 294730571
    0x418140a0903020c21031b060a020a08040602070c0b07110a080705060409020f0403052a0103091e050109140a03090f0b0f1608030109060617010b041502010e06070f12 73
    0x4a00007500860210140c40044451091210100385e2440d02c40f020500d41180a010006140000321042e0492450100c100c0c0304070350603a51644540030032449420380000200b0320300400100020b010340c00400f2603511400240210300e0741e0b0019000c554009900455102c1010502c1030356034208204184000c00b40c03c0020321700f251506010810342c1c4542d000708102a60005025024081c803441203400866104040b03400c0302c0c0c01600c0300390700c41d0b09100c10b150440e1602e414107015980300740100c540907074002004d2052440b102903c1c02040786030680840d0655240c24848011490501116044000c407001514283d00b10345030042001c0e400b80c00c0a1681c1000900034490f1200010507118040000c460080c3e645161020107a20b0740781ca2030000b0724030364000001140e42546c0360070100c03c42d602c0703441c0c2100e46100da12107030740c90850900400200b0b54041c00100940040070b9140311458085000010b0130721084440c0758204981140c0c50804513200904d5083c0150340030480200710803240e46c04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 294733066 1250 294731816 294731831
    0x2309040908041d06131805030708030405150412030c1b080301260c0405100b071b0b0c1b13140411010c030206070e01050f160606090614060c030418140a 67
    0x245030500d90b40340f4901085d6685102403401b0060300b00b240c01d1640000032640c480c91a403400c0d4400d0780c0212021982c2d8029620300c0e50a01c00310080c124001c3d50b006048020490030140220002c002b2241c411040044891000c204411026080d00189028913050b80c1d80b0341c14142c040075501240710343c1850a4a1211060901210110352a088500d00b00c0c2c0c00324064640e40c050540d6a5199000054140f00c0000d4420420402c1940b0010994a4800d5080e003103943d0103100c0414015603400c09c01c95002040c0f2600410072414841c5c1850b00c0041164440f9908c80945d50300b29607207000d0031000c0407058028402440345028042010850918055011880780d54009403106800341a0740d0510001050f1040540e01420583c0c0981c02c0440c00d9540b90640b11007480e4000e0394001d000d0710b03007514110000c140c10b0300318051a41503d6503500034a8000f084e403000e00a0039800035400e149940001d101c04950f408017a000e335020f0381e0101d01c000c10ba070442c0c03507405100d0342c0000c0c040005042c030300b511 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 294734316 1250 294733066 294733069
    0x303140f090418050d05040501090e0421140708130f1512021c0b0907030e03040501050310050603010e0f15150903010e0118050610062309040908041d06 67
    0x441e90303902025a00070641c031081c07040c070380507018200c14020324034000c031030b0710180f4654414050002c441c403d90303e80c00501c8ea1003042c9024000240d070050030300c0d2643e104080034100e00c02a2200a00c01e1407a082c05c42d500003407800b5246030032116003126900c20000700c0c10202101e068014000e44070029001c1c0c01705d46041f1040c0c00c00c0000140b0071080c000c400030344034001c02301ca0741076460495582201d5451030254403046c1c0001c00c5800700840c41041c444001c1502c40744244581044521355034015844e03c0d0403c03005540c10b400c001c01110107551100800f007038a448500243d03000740544c582a0a150a2180203410002001045800f010307c8000b8051440c0d95203c4102e9600c800000040e0380e43c4072001d02080c00340c02d080c0d40b4080d996003011440c03000101200e40700006603018a0960365640c5030028101c01c44821885984001840107501c000148032801044001d04401808186840b18200c042015103900c0030050302c441101041c204050350f407400c018201c140c03443c2442c540d940741a40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 294735566 1250 294734316 294734347
    0x1a01020d0c050114180f0c060414030a02041d070801020906070f03050d05180c03030903060609091c0221030708041103010902090408030a060e010810020703051b07030314 75
    0x40c005400c10000e62910000d0107002e60050507182110b003049256440d18014070914000d190005c662988a11105811800c0c00402e0190700c0391402402c081c505441c00c200c00542d03c603000621640750084140b80801a0341d40e108a00d007031100c00d441c11030484508101c1034282012a80078900c1079004000303a03e43d81e51114202c800150788804103100c2c0c000c0c541402c407100e02880d0b450030304062400d018000080b410741c0350100320885200c202c1c0d0030248441d060644a0251109030398241e031024010800600d01200d0b050350144005040709c000007883c03105040c07580a69480748000d600030300664030f000e12450781c842845100105213941b035410b240e1402014404000d001030441c4c190351200c802d04e690b081d00140003150b0020302c40300c1c990a1a00344116a070384155100200c00b842c20380000741c5d2000310002141207402038005808900102c0c11124003030351192504500f049402c1040c0000f0a50300100b031082c01b03012200900c0201e00714513003d050007a44007200101c00000b4054801d0750610710 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 294736816 1250 294735566 294735583
    0x4020d0e1b151306050a031803020a0209010906120618050d170105040c020c0411041a04180603020102030a05090d0f080901080c0924040906032906010807080403091a0403061a0102 79
    0x80c035105c5d55030182c09900f20000c00d90400c04611301e0349504444010325500150721500640212a00714141c0d91305c050050841e0302c0e920602000702c045001c004080b07882540301c0c8031452685c4110203840b4940c0c2e80e8407418254250348040103e03403800b201c280c0507030380d03046d00a024000a0310200b0082585400113555181c800507010b20039070b198440307210105904002d990045c100300359056806500b0310b804840d550042e0181c083c605040515a9103d075071b10b80a2030f0101c070f8041e0059803070041240c1d412a0254420090160003100c00915040010481c1e810364804601509195440e092010001060340c1ca000c3d1451903611400c0c040e0708400e5a800300d90444100c402070714120300c0b00983c09a8844c80c01194420902d041c5046800001d200108414078030303a280d69220383c5208034882ca446002c018003a10751a00054109000801050103522003681160013800d00c0e02078190780f8019542041c4800c4911304000401240c10070402c040c5008107091001403a1210030300c50381020000350360300c521 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 294738066 1250 294736816 294736829
    0x1503131a0a050604181e0b191808030103120311120405101a010e04090b0106090602101b1b0b0106121d0606040c09152003090d0204020d0e1b1513 64
    0x820840369072030056100d0303d502c0c047e40034109030131916000e0800c000307401d00d1903e0324145a0a00e0b00081d06025030440c41386200d86e00c0355465080d42d085413120400d849141c00c0c14005d050356000c80c94003030240b5001500038020280c2102c6000e107030510b0054201030700004040170060070304100c1004166420301440c00d1500070b06c1c00420540f0000c2c0058064000388402610300404000046802d036132040c504002d0381c403507808480813407822681030001c4a14100c40340307420174259400801100d00c5814480007281d000b1600c10001020b5441d800a0f0100030f03400100841d01a402915000006008105881d4004c000e5a0b2001c2701c40c584660b11400001c00191140d9901d40060709c0e2540078019840180544412001d072151200324003800243c1780c100e1b04034100e44080300b141018100041103c002500c0541000d050f101c9a9013404003a4100e4254107141c0e5481e0721844071f070070794100b244c504410174600342500e0b145024010b02880c1c0941c071041154400e010018290103035410610a8100e846 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 294739316 1250 294738066 294738083
    0x10917070605030a0f051305070b030f0109020d0209030102030a060e0901060501171008070602031c020301060c170f070f0212030903060c03130c030b070806010e1503131a0a05060418 80
    0x94440d443c4e4024841140311000307103031400042c810611151001c14011901c18400c82d44e01548840300c4174014001152011403c40b000d0307005120000e0180c0140007121355028025040616400020782079800c111400c80c0700642c0c8840c10401d181141d100c2580142001c4000c00000f410440000c044a40d107170217220440c0c80b210042400810340840d69401826001d05540c0203540b5800025200d6011580fa0005d450003c4009a426441031084a040342d555841d140a0700380b103a0b0f140156803441d1400e40300401c5080c030004030f500c2801f20040051600c926a8a1480422031040015021250402012903070051000315500d440008042d50040314011080707449690304281c0c48500f4491080003480c0c142041000000c014202030854007400303060b1202c609550b190401120481c44031001d10341e0180018550382e2140e01c0540046400851803100090310012a484200140e07030b012001c8100804040100b08411409100c0c1d01c3d04031408a0301801003199148405900c5a109600a0280030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 294740566 1250 294739316 294739321
    0x109020c25150206011707050901140d0503040f170c09070c0f0f0303090203060f0405060105010f02071205070302030f010203042f0405070203090109060905030a1707050f010b01091707060503 84
    0x40038030810100500b8288496000300c11003150080d101e140030302c6002d00c81601c078090401c14610218804060741c3d0007400500b21070780b801a00b0012600c001150a4101c940c256010002c901c061005101401d41d8034680d4450314a0003443e2005299045007548440e044454440c035160780300d00da03840c0c0002403850a583c0e50700160500d107034040004000142410414400502050b4040c0c2290121600840507941e0030360310503004200c0d050045500900030340010006000643c001d03000360f81455903601c1110501a216080780007801c543c210103491641c0420030030000c514080281003078a2110200070742c103500b0165610801d0140020740070350b0380300402c0d10b941050302c0c0b803001c040425a0010024003241c2044500030751268414500c2c82d000032120400410380600a440200440300e0182c010400055a0703140c0c1c1c10000381c00c15038150b10300030030081400171641c100403201d500040200001182102c170000500303803d40c0c682c0411003140c1003100d0003995210100d190340840f034140c20301c5aa02d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 294741816 1250 294740566 294740623
    0x2151b070c0b030906010f0504020a0f03020a0207050918060916150e0306070c110d08091c080304060204081005010b0d09031407060504051002070c17030f18090109020c 74
    0x50b038000407541580402040b10131000018540c0c100c40b0201e6124070796503254400e001c00d0b48030b103801d030b8408544107007406090144250300400d6691458419900d400341c8620001c0c42c1e07290150f0380c000c120003158841e00c0b23150b40d0074490550012110802800c85400309950304503082c00e6441030051044825100708601c80c000c031030301420703004018180d50700b03454502805000750240300815102100171524001107414443e25106503542c00c038002c10b042140080410150b280310780d200d07208852280a00000040c8040e0146001e244031f0701002d1307111400d1102051070103a0064514007120309000042148541d06000c403003044040040104082c2414101501d1442000e030140880c404006034101c2442160360000d40154492402c1c0c4494150200d081d9046e03004401029051100b50300c0108661980c8105010980c41ca0400fa00d0603c40100142d101c00e8000ea020f0038101c0315000200d0060303103420b0740c42502600310188118100500d40c10340c10f6070b803911509030ba0190b8407254030003500e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 294743066 1250 294741816 294741833
    0x11505040b0412050f01050907030206070609080a05070b070801030c090905010b090910050f0106080c07050a02150d05180303010b0d02090a060302090112091214070605070801050102151b07 83
    0x50650a0500741c0d5842e079545040b407030b030300d003100044d542402005850000658103015440c01240700704000d00580d800c5400304019980900c10844140380e4981c41140041c0d00c4030080d2201c02e4840d2034640c1c80d1030309800d00003c00e29000300a402000707a64401840021400724100303080da15500d0300000d805481d458000e00418100b0503030780c1e001200c102007184400f000140c03039080103070000050207175440e04a469100e50f50700f8044e03c8085000c0c41c000034804074840002d080c0300b90051040b42e548011a0300801c039083c01c404414048400700244562441500740182d41d00b00b4589410030390b480b8590240d1503101e02040c0214040da000000b8108440768036034040d41c1c088080104803440e955030310f160150080d0301540e4024040713800230b0030948070413000340f02d411070094001100100404003a00216400903288200d4048410248152070100f0014803a80d440780c51f0903100e503c20b55047c0000a031500c07a2294086107203040c800d0801c4540020303c90b05043d0381e001008071075140c2c01546000c060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 294744316 1250 294743066 294743069
    0x121103070209070e0f190504060f0f06052203080706050c0702030a02060901021f0212010503030a0e0415031a0414030705030d09020d05150a05060f0f0f0a090903050705010506010302040e01150504 86
    0x9104400300d02000311300c0c03180c00b400b86c21103000700e074208005541d400109040b200c040c4500207051480d40800c01005001e2001491a034411100b20141229018115407200d0541c0c0c10136101404086102001c01c00c0d14425190806801d10b061400c11600d94006981c41ca001036000b40641c4020402110f103034000c01901c3d02d03144281c2480c10b080541600400700a40206060001c00b6159200004040c2008011519070984c10303511600d2511515003440041c00c440c8000000c0749040076000000b050f420312202da03250070481180a090700305400c1c04800d19904078034640460f00300700420b0b00043d000104503072440d00002c10100d98030b8004d00000d41c0d01d411080300030b05070380141e000b200c0c84001404071140c070589001400708056101d040030f100008041c00000303608041c40450b03040291615103914400104001d048109454813100f80009484034040e08901143d40840c400041240c00c0c000c69038440c10038601141090f28103c0780780207100040c4680f49400340c000444822030ba00ca45c2c02c0700d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 294745566 1250 294744316 294744319
    0x3070e15041a0d050f0d230f0d110a0306060e010c1104090b0f07021203130b060a0b0a050a12020309030304020603040609050610140405250e030703121103070209070e0f 74
    0x80c1101090700381940c41c1c0002c000c0242d014000c00741200d40c04c03030283d4100e1f140b02c250800c52800c03040102c5d1000d00141d11001d030608a182d01401903004844882c000d81d607440e2490080c05859054a170b1001e4161482c0780c20076014070400d0041c101c100e903030250308640420f41040c95140032402210116000f040c6085018118200b40d400f00100c83c40550f003800d0140e17545d41e088034100031050700c4114441c0029200c1903c42d40176624000041244c0c010f8440e006000185103002070b6540300d18071034041e0f010b03a00d01d201040c4003041070b240054016221000159035a00e055195141800141b500d9100c0100f00070320450002c80454180820791340726000e4a580302d402c032401341c1840403903002e201d8582e2040100c000b581e802e0351401c074105402014080c154141c40010580d60101c900d403807201c1402d10040c1000801c001000f607660b01008140c006500840c6130005036120908020a200c0c0d40707481d0901641d01c100b101100613100c2d007990316480303d0140351401c1004241000101040c44408445 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 294746816 1250 294745566 294745579
    0xa15030b040c031e0305030a0b01020114010f0f060306030203100e031308030d05011707050103051e0f091c21090210021c020d0207030b04020607050d0306030203070e15041a 76
    0x41000700e804400002d076405500606855413858032010b1900b2205400100020f0b410710100c1d40713614850b00b042c4540101400049008a145246189603603c00da00c6060b410104120421a08041c40c0054001d00b40c68907090069170b00b140c0200b0f65500c0c0c0c042c42802c1c860350ba44c0d415014420b00384203481b50040d01c110300481080e075507010745960341c021084914405282200014445909486c003008070502500907141540c94400113500600c4020f24001c4200b040540e65000723642c0d4042051b10440248024541a0904502040c5800c920703442c51070400214110b0070100a40103000c0003403180d05625004a207070310110303e05c009044140ea0003900170300d4182516100c1c91b00840c64482d4448a049400c1d0000d45400d070072613035050764185000158000c40d5003030012800040e01554850700103000b161410019580e15890b0450041101c000a541e44006004504d02405214000c10a10780c40d06502c1c20701681009a2603140303000f06200319520201d40b00e02180c83c1d4801c1103000784c0203012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 294748066 1250 294746816 294746821
    0x106020a0201020c0f010e0f010e181e060a03080a030b1201020304061a0d020111030c0f07080c0409030819060503190303150b04050d1a010b19020607080a15030b 71
    0x103940d41444180032800340c011407480d4540c40c00c140d52044e0020005075904111511210140309003400b051100c54100907003645442801e803a03950b010407130082c902049180d507240400440d0400988110805407500880d024002c0c1543ca140c243c1040d00d0300920710b541d84c5d41c030010b01607000b812080c1078036400158200d030031008488190b010311700c1180204018041d8104030510042841d29410314160b22481c2040c14401551050100032000819101200d140c1842e150419141203210030300c505260b4082d0b101407100410621030070b81108020b5405110010300b559003d045000024910760440e012030f407920302104655000440101400b60942c2c903070601291401c00f1070480394400b1b5000c6070409203404101e0003151804c6c81190f040c50b100324209030403c2d0410483c1ca62040c01520710f402800840011900c0c007a9496000b80101250503603a50510b10303208400d076107282268400c1d90002000c221900e500481d030713694805200d01c40002e0900a0b070500c144d4080640d040035004180c45d408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 294749316 1250 294748066 294748079
    0x2090a15060c0515010b0a030207030507020a081c02011e09050a020d1b050d05070306020f121306111206090a020d02132d090203100e0a15081603080a051201 69
    0x10b101d88410b0041c01552002c0c0910040d0640ca40b00030b11031200e54031010428464054429809084440d120346043e51600303035142c00055510340160031965a0741c0040c181e4001000c0780034211491049140001d2054240103104040b250300c5818110f00c00c0e9481e1305000301000024051240b40590044c013030080708002e0b080c144540088080071551040f0390500c0401c0d00d241610035200d14562010082070600d08580d6000081d4200d84281c030b10469003030000a8010540d40402c6100b181c4c0254141015807040c10100243d5a2a01c00f07110700001c01c021020007007503844481a402841512040344980303450070710070020f00ca201848500103101207045c40f8414054003040d01116860002c4142032444041650409031105600f40103e9a5483c41001100e1780c035000b8591105440c16035904503070317484400c0d0760710035400c0b40c6080803107a60300c1c04080c0d840d42040040015004440003049000e4440040496296407400302400c11000030908001e468442c0c8200e03040d40740c60050300640e5507510314 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 294750566 1250 294749316 294749327
    0x1050403080105100e150f070f0819140a08190c02060405210a0309080d0204060503251d0a030f03080906010603020f18130c0e090c0c060402090a1506 66
    0xc051003429140f0a00f008240300d500b018003000ca000f440c280300c0030070000d03046c0060303401041c061711201c10601040000c0364030724003400300c014000c662041d035400c00f0304c0d40038600700c04440020050200300d4030315507044a204410703104d61103200e0410b4901502c55a890700c031039280b61083c0300280c43c04c150300c1c030400550102e5000e0013188207c04440004480040e0701c0011400b14500c0600420140300c42a003041c07103908030141d031900134035803035141140d03040e42c001c01d03030340150009400b02d040042070241c84090752018040050b080090075100380300c0700500400d00034009000580d582080c504034165940c80700d0380032004550014024490030070625000d00090300894043c90a4001d0130000036000e802802160042d501002da46071074040030040b080e04039007003040d400c0d810200c420b002035054813040c4100c08007000b840c0c807003a090780166404c000000c1801404101c159605111003022040002042500b041d41107540407410b603a40f2240384014035010075280e50f010f2a8041c000b44090300701 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 294751816 1250 294750566 294750569
    0x30f06020c01060b39060423070603061503090206030105060904020c0709050103030f09080715030212070e042406110a0b042d0b01090f0605150d0b1008040b0c0903010504030801 78
    0x211500c080d22000c8001d08172403da86180144682002c0b00280000e662958514000107200f030000082000540c8450f190042070f80210001ca40d485009111540d002e11050150480c149001d0055103415400b2500d80c0c0010301c192400741d1804654500030760780d250103541c002c1511901f120003d641c2d40240c100501002c0c0f0081d0040ba001d0144200030038803c00d0800d05507080c81d0000c0c00d00310318019104849104a06e40c4c44101a400c2c403161744140980c0301c0b840d0141c0200d594000d003992038941044115401c080100d08a1903200e070385003001650b048405000c49840341014080b201c10b50b042941048a0a480280709803c2e020400c4100958000a000320403200320503c503c1100707103030845592882448001e40720031071f82c80c01000b50750300680050320080d41c40f10b408960b147d510008500354a40c0f9181030700304000c01240100a0740e130648211504003600b26404207441c0682c8501500c550720240005d06082041c10001d000d0440c204211410110040d0003000240b402d801d0040600e0b100707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 294753066 1250 294751816 294751867
    0x140a0e180f03031e1e0414060a20040f0909063e0903060a050405010b031506150a0f03020a0c121205010501020705102f0303010306050c0301030f06020c01060b 70
    0x4d52503105803105524042446050458169010060144281040322500500c22550580f16800412a40c0014480c40e80504034015001c01c0c40e2080a40c0c1e0300600c0321100e907010b844441400b0801c42d458030000a04d0455070182000038010f5540c1c241500a041d0040019400e461001c0050007003091141c6041c103110140c00d004c142d4542d600750390004a1092141455140d030210000c140700e0342042c5c0c4103d4102c0d124100000d00c00070301d48042400d0460142414014400302c400300589410079901d105841c4103080741c90b03454035008034000340625140c0800070040690120328808182c1c080c601c01b258007500440030f001c1d03110002c2030080c0800e4000c0310070b02030036042130000146940005000002e691006000c07800c0705000940880b000b41003800911054080869101000740001d181c583c4005000405195203605508000d402d035000034041580c40d02003000100f020800c15500300c45126803005003d0394541c03031100c0140c0075140c1500111458a00004c00c580d003c2440c521418a0f00e44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 294754316 1250 294753066 294753091
    0x2030312180a0b0a02090a03020310140f0106020618160b030103050c010306080d140708070506100609080304050915090910150315020702010203160501020a09140a0e180f0303 77
    0x84400c0300d60b8980c10069030042079041410080755400d01c40d030f006040c9413000074124890942d0b490700020301e00508002a07860099507940c104142540107108180d0100001d42c51000c15490100d009660b980010404c050f1a020301d0f0095046ca00c051220ba1450321100246860b103d46600e240c8010358420f10080760b843c4a0520446c100b54000d00442d07040720003080103000c140c0350281c42554003424984001c14122000c0100d07e0001c0c2501021f03090050283c0014159890320610450a03006246c0142e018804104420410b400c030004c201d6050340c2d4241c92a020f19250406a40c240803444c10609034441c110400308202c0301c40020b401224a107550105000030b1a0760a252440c8818502016003460741109882d03403407800513001421014810710440f403034030f03541000d0480700c0c1c02d46c04d004494036500003c40011040d4814001009010b00440281d25111380e0030014a84601d6842548211002c2d0700c0010b0780e801c02c4400c00e20b5844020015202145450100c282e00e0b58803c5808034007595 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 294755566 1250 294754316 294754351
    0x30c080a140f10090e0d030b240a1b11130b01050d0b010e0306150f010908030904050405010b06042903041a09100e0d090503120a0c0c0302030312 64
    0x41041c01500da0401c108005a40d00d522801a00200c0890042840400381450600040c20701001d03c50742015880390000744ca0781c0c42c00c5920007815141103241c814802d11441c0540025070814180100c002c144112043d59514981d2800b60390350015400d4220040918001d54405c5c0105105601000c220403621074941d100c5004c561401c64a0201110340015024440c9010a0000f544007151500e41410451401c1c010300300081e18000c4210ac0c1c000d02c1b001c081c2180d0003d4141108179a0001c542420403070100c0d810080d0032640c0303004248900384030300c3e10384001c1414068290b21001c01e8100c0070304402d64480d124443c1c41c02c40f104400c0c0080e0694206800100d484042c0c6040d0b81c007540d8421282e07100031070030882510752304502030b00f40411401640c40308081c001d118070a042100b00c2c0040a408090001031300074000d408141e0119001e60441010580c001c07203040112200309015052490501d02203040c01864000f030394000941510000900c501303a480b0301d4100d584601e200c500400d001d038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 294756816 1250 294755566 294755581
    0x240c0d080108070506030a0e0d0c03020c0102030f0702060d1119020f060f0615040807150e010801030308130309030203030304050c0a080a020109090f02090a060915030225020d12030c08 81
    0x111401d10504000f600030b200181320510b072a00065410084070840480d01e5030404079524140301d070500d030311004a5044000b4034105901800b4842c4021003d001460614111480740c1c5118421900b0003440381d0400150300402102c503900501224002d40040d580b52010000d0158a941100b100200580305010007410344d20030000e03000d80701d2282044421f0700c0380c031024103006280540c004030324441d01051001140312001001482c0091281c10f6040c46c6400c81018064844520344401c1410441e2840051010076001087c6541103040c105903a140490a8101101d40b50419000254540000000c1c80b090020018803880c1110080303d02d00d8210750358070080383d40c130b02000b00e009022032441e50080100840f03503880001c0c0443c800401502e000b1140c80010055481500308001140700701106000d41241c100c00c0703004178006400c08501c2e20700d54240f8014203401d04110030314802141001402192256945007540035441015a800303040700000203000b4040c4580240c00140e006070000d00c11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 294758066 1250 294756816 294756827
    0xa0207060f150927080705030d0c0c030818060c1605070f15050406140d0902090a0609110a0e090a020717030f22200d0501060f05041506030b240c0d 65
    0x2c1350391003411070182003420f540e142e03640c1d0000c103001d49a038001800b803120750005c0da0007144c84201c80c940d90709540410718540a0a066406440041d0b080c000e5410403010000009440ba000b80421000300c1d280c071540c2030162044039500c9030040c134500442d500003030715003802c080107010b60b94081c203604e0010a80401c1212540214445d04001034866945c1d00040c0320084020302d550b0b4080140803800c5090394010510803501621450b59856488404009605c014441c074555087c6100c03000d8640359201800030709858031100b00510540914000c50109103855046a046c0c1d54085d0300030303070106e140d41d84103016504203d50801c030029172100018001c582c0e140018543d00244180307a92043c480351501002c4140d1400c40c1030114004e4401741c020740e6941407151075490b02c075034004912941886210710003507400c1c0c4d01490003075042912a0070246c0ca404071b07400030350302a8135000409014250000b08542c41262943c2820780344034102c01e0070f142080d8014442c19240c07600b215942c084400c030032602c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 294759316 1250 294758066 294758111
    0x1b0a080f07091d030a0c0f020d0809010207080714090c090306040c1701110708090f091306060b0c0304060807030f0c050403030318051207050f060109140106050c060a0207060f1509 79
    0x321500f00b08008038600d40100c6d0090030203070240384454506410350f40800d1003413040783c1c025034881b00040b0741c0301440c0da4104640707405000040080c103826441c041c1f410410241c902ea10740d12403459503002418030702400c02615104031000341198640d061070b041c202c0d040809400b907413202d41c0b000510600a540e0500810b04104151007100d450101c4a8940001903082828410303440b4404ca290302c6a99610036900701c0c024440107040e00005450352410b10b00300e03080c1e64042c0a03201001c1c8603070f0b5a80403020043d5030465101c1d0401d01a1399950003c100d00034004001c00c0c0c4800740ca0a090720010a41c0704015100f6a403082d20708010035103054907000c01c181401d11004110754800f9204801245c10782019105152280040310881c0c4001c004103401c0200c00d03040741d4130b207941d941030308482d100036000070600600c0700e030428500c1e2a50300b0810b1904d40078000e00213551075400080010030448a070303024590041040104004445045041d8030342d10025115400c100d0341800c600d2101c00110000c1d291 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 294760566 1250 294759316 294759371
    0x61005030309210d05030612060906151203160b01061b11010c0609052107052109030102030403110705030d21021c14070807021b0a080f0709 62
    0x10b003040800010400c0c100b80c100c003090043d0394815050284280304211540c4e24403901e407070340c0b500c03442c008040c4003904424100010303180d4441403e00a81e41b502107181c035001141c03031507462084a52030b000700d246441c100e1104900e600c070001e0003c0c4445a070f151044801c81c42110042e229903600d01702101c1500749201805250b0114040c610002a0078118039401440181000c0c00c825105171518012036030500402c0d035003600b058810145809c40c1116501e07240f4506100c46007010403d84401d6901e413a5403004540c900f00800b08680c10110300d03402d032440360314014001c0d550b9140ca0700e00141001c0700d140c1c1c03035001e82c03280b40804141ca190206002c1a01e004603582e440c00c2c1001c121440100d211280d81c0d9910565080240f00c0f00000100d80310074505035108000b107440c100c075943e1005244401007243c8100b107030344001c1c00749465010030341910400c2444009692070b0314002c001100031501d544000464030031600c1d900b01146000c0f07405403c440c0428010000000215860a40002d01402d4003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 294761816 1250 294760566 294760573
    0x2503020715170702120426060103152a0e0102010e07180b0a090e0601030506060a0f09050402040b0603090106060e030d02250803030703050114040608070b070204020c010504030801030506100503 85
    0x185961160302c59001d900c45414030442e00305018120201c255035126030405071801c822241c00c6000b84040714000f0305a940311000030800ca601d50346981259103032804007a90b0701500c42000a10500d8141c6ea82910340c0d80d0703d8020b0410000b00500600307800c000701a00ba0240d400d041e00c80080d19004a416411034198000540842050310000c2008004d0450402e502c400800e1007c9891041485103d210201003c001d00d569411130500f940f41182c001e00d1a445581c2d00d90301031107a844d804400508039004c00c05c001c01c0d075866034400240a07110f58100b058119170007200304401c01005400c4082191000d4681d83c401c0d000d02810b064803081e4240048016038040a01040000e1018039000d103200949100048003a440e1a415415a4800e8400380c0002e40c8a000501251600c10702441c415402210704005161038900c0194840115114012990070b01160300415900d4a030101c491204c80c94008200030b00e45480c1c080c04450b806e010680d010301c203050000d403401303280741184426210010001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 294763066 1250 294761816 294761837
    0xa0203070905191a010509010207031b0f0b0310030209060f09150a08030310050d050a080a031a0103151e03050304090c0f0206040f111203030f390705032503020715 72
    0x41d170b2964007071f004042c110300c0b541c500040451051481d101d00507801c0303205810002d140802d65007400d101074000c100405020018040a1015a60107908590b41902c80030b00c40c0ea9100e00250003980401441d0740c0010710001081541181c0c0c602800e068001202c000b4416a02d800030950b580c0400c844501d0043c541d0002401070745084100e21b08060311030422034010025941e111280c1d5008215000e011a0712108600788494541450b180504801c1c40d08200c0c1d42c00e00042074802800302d21a00341540c0c0c1038241444411200c084c04000b854000c003c40c1e07900ca9841414000030b12611846000144003a000400308910210741c8500807500005115910070864440340c0b90480c0b00011650300014041480c603110303100740086d42c030490040c2c02441031458013900c18110a00071081d03000d528004000c1a0030301401400591071032660181d1550b4640449250840c958408c08441060503c0d000f80040040107061034400c2c6218400c0c2c3c00d03144075941c2e96410552406002c0d2541c0c0110300300b07000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 294764316 1250 294763066 294763069
    0x10f0c0b131416090605090903070b190608070806010e0105030a03050a030b0a15120c1b140105040803010f09020f0301091806051009110a080c07050a0203070905191a 73
    0x41c404882030103048441d07028035040710303194036107810051503200f2010300901c1001403103440e200f000000c10341524191010715002c03203440e46900c01c445006251401d214007007a41803a40305205901411042c808102c02900c0300604c9648181c10700c221440b51080d80c001186504c40c40c44054122240030b070040c22900d00980d0305880c0b130340000c008a4201a0740c0c01c1c0300340e156a034262040c80107003501a110b11180e80e03041c800501501890b8441c0030818200468030900c507038041091003104848403035a1115803000c1c50b000750102400e120302c1c9299801c2100784130501140c0e500460407a04094048000c80e41c5c0c81c02c5040580c0161484442c00320b00c01d0004100044032601f00c01000c0c0c6844108402d4104c913580c0700d408a0302c0584400b1403134580640244000101841142062200340b0210390410311b02c00401007804000400000074050b001c10725808200041100c1c060b13880d03008068804041e1241181402060100c2c0d0744019142e01d4210074022072407502c17070081c00940c6180450784405a510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 294765566 1250 294764316 294764341
    0x4030b1b190302130f05040c020d0906030e03070204020c0106061107030f02040f0b13020a030c0201050108060c0a09080105090615060309070306050615161b061707030f0207030e010f0c0b 82
    0x1c00505400f008110202241c854010014060001c00101d006051500703100403150340280717103030a40d4841103078260804d8000e15400b04551503440e0105d07445007a0f0b01240d08501440000039001030006c550180030740019004081a500c4940d140340403400404411544ca1155220180910030782c1d08070740c40542400d41010006130703034a5002098110150b0040b46d60b11041c0141c42c0c10301d82d40440c0407410740780d05001d0030071040b60510083c4600d50625400949680b00031780501c51581001480c400b400d40184d0a1000901000d40200407501c0c1402110781c54807000c49840142140207030401400d80341060a4a0003100b004000380300311411941c60070021f010190046921440c8114034040002d401802080e60712480b14461640e00d41ca032412000180001802804010604001748109544103000c400300801c50389111959407901c101c10fa00808041c2c1c020340840740000340074001c0c95080820240c50900c00c0c0ea4903160320f40c50071021182c954401c1c02c010015200c02011036612060507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 294766816 1250 294765566 294765607
    0xa0506060423040c05070b220507060f09171e030c101a04020c0d0503100906081c0e0303182701091416200303070504030b1b 55
    0x103000c4601c0c090b1103030a14a4060031038503620b1800c002c003800c18030ba182001d01070035440c4041420310030b0811800b0390303c0800031040100134180d4941c402c43c00c415500c00704644512000d41040a48441c2901d500c0d00602e4200f13686a02c802003546100001220040c25000b0800282c0c090050039050414480442c0d880722240203102481c03005016204030410244403c4608527804000001c0c091141c080301c41d8100ea584100c00d10851050001d5010311502003900c000150840c6070040d44da03a12241005005441500124a0f440c035022002c114403600082c1c450036103400d0100b140e101c00400d070080720340e0036421402a401d90030620545103401c2400e4500c01c0c1d009001031000000401000860a0216200584194503c6510010410791940d0f20803884d40d850110ba018149240810400f210301410300109020001640c64409110350410250015a011401603035920700740901c004086800c14041514604488408650b404029800e00b4146800952055041011030300c2c02c2c0190440c203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 294768066 1250 294766816 294766819
    0x307030c14040602070f050f030307032003070605330d02040f1104051305060d02060306130515040b030109020f06070804090903021c030b0112050c0c030f18030d080a0506 75
    0x8040c1d48800c00c00c03080050409020558002c20200740340071a04200c4541c03a500032801111400c004140e16200030084a0030300b5050300300118682c2c0c22041c01180c1c3c000d01350614455000110b021410800590805401444003c0c030307903070b8658082151840c100107000c80c5649140c000f41c0c416a81e07801d00c4540c611515000900001d40d0035180703440d00040d210400750030f00780190002018040c030315240d000101400301c1003e0410081ca4441d01140d810460b24602a00c80c1001000042c03055603908035a90303400d40202c0c401e2045042010f0240c0d40011418201441a4245900d2030384604052003821440c940080c80004903954139000d00c1642c3c1e11880b41601c4981b42000042242d2450740034420045100c0d41c010041c00888000c0b20400c1d14a58080030101030a01c0d0b45825030340c6c1d00200d0314120f04c20182000030151900490114075204141c1c071102c03d4000414032055004040000d48101c0000b044e01e10400f19140e4101901c0c4d8000b00c0710b60003c100c4540200d08592815800349a00100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 294769316 1250 294768066 294768077
    0x25030b0409020405040c080601060c0c09021c0906050a0b0315010306050402010c050d09030b0a0b1014131403010b2205040309050a0e07030c0f0207050d020402040b040b0d060510050307030c 83
    0x1050b40120381910000c079420b4428029040301042808000c010b4140184094a80304021405680d0f076001000c1551281e070400c81d030007055840d0340290b2008910f48024030360008104041080c40c180026200499134042003902c0d000c101c80072401c02146104800c807800c441c03030341c03260b0869a500c0010900a04164104110103d080c1c3c00502c041182e01c02240c107588030610404d141d4070708482084401402c4080560421400c0c1c4065141c40c858249025120300340450f400444611818080c00340804146440006450010f294080c2c1c0480c1110140b068009010726203560301400940300d004648050200d4a1484c0c031900d0780c40c158885900184285071050703c80395110005070513400d541c0c0122448010120a00400703075003510034106040c1a50030030408500810310080d480309020701c078290241d0808452841190b0f034680c1220080c0c601240255200da45072034030035410750040d40c0c541002510b000c0b80401c040c0341802030150800684e55943d031a6a88201084019202502481c8103000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 294770566 1250 294769316 294769331
    0x50105040e04060e01050f0412051e03040521040302040e0102070b040311031309020a030b011106060d05010b060d02040657140d050306060403110d1a0a0525030b04 72
    0xa0090340d0245401d504413071f0385402d02d410b0004e080190000103100303001040000350b2545a0000d9003501030044400419100c7c3e84500b0a642408200a03010a50540c104d0320010340402001c058801d59000769400c00c00c610005000703a00700d20a6074400750500304040300040c00a84035840c08c401c0c503510720080e00d080080d65503008074800301d00d401c01901690041440e88c4859414070038500340e000e007440c0008450b0b50044007a80c540380054a030324017902e009100c480c2409001d41140846c408098030090307a030610b070410b880094010340500350000f84214050300c6410740350340c0030000d5011101c011520180c640644910f5079040341d003040181004020a56101c3c0848251511025016001034004510003c1c2d4071418800788100d81070030b01205009204080c0c8038001904c2c2600d51103c0e103140328403c2440061006400e40b0310040c12200d1701440b100340c1040e140065800340c200880140029221260706035064080344102d69181485000c1d40f01d149d902c203401440c00d0400107440002d40c0c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 294771816 1250 294770566 294770591
    0x30105013606060302040302130c140310121101020733120237120506030118051005150d020108100f08030c0c031203040605061c03030e0d09050105040e0406 69
    0x2d41c10b55011a000c2507000c03400b00190308059902d20705251542004102e00050f6a10140c80d01d1240300d0b403100684000b01c0010219420f07807a80c0405420030707035060260240140fa002c00d11035440d02d10103006020f010800170700e60000030705541c4180481c8004800b21410241041007402c08100781c00708108100a2030400380c0c5440c4010162410104e01d4520243c100c0100b0705c81a900000100c0c3e86c00011526800015500c00b8000441505105010429480b1080080e0160045051085040014010180400000181000030803415030010f01c000c0c0c0c1c074010340034040301c041900950418801400400190b10802803e50b00203c4072070500c100a80300d52411070003d18035040160503078000a85243740e840108090414480708800600580c0310b4180c0004140c0000391005081540300d0340031820380e640d1800f90700913240d00d085c0c201001d07580608005000d0050403490100500800c041d4100f82845040740c00191003041c0c4880d0716103480c0038607001e00598000c000395a0700741d4410399658903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 294773066 1250 294771816 294771821
    0x311011b031b20040c08150402030415021b0d031e091a010602030d0e0606010905101103070818030c010f12090f0f02090a1b0c080c06090d020c0301050136 68
    0x1c8801151250000f04101d4180800c0351581580d00c804e0005107010050318074006c02525000003c1610f000d601ea45a6141082d088440c1030341c540f040138004141d010001e028910083c8460034098201d582d60f0b0b210810a17000c5030039400c0880c44003a03541c114020302d11081d410142d000d622403102d0700403815a0401414954a0a070071240043c0c20006400d11564024040d5240c2045058083c06260405e040042c0c010691480792a02a2030f402a4141e20240140c00a420760300320502500c0d550701ca6440d000c0c9095000c44400125020ba00031117500600b000900703400302c40f1040c1c4660040c0070300081d09460700140241c0012203a0389a5444030005400c40c0040840244120f03405c045109442c070400090000c0280000c000502e0260040c1800d40d041110051200030781c100300c843c40529003000100e0340305604246115106140900410000010f5140a2420242d09a411100c442002c16081e24000c2c402c200100b044460309007000021410315001d45400c40c00070f8040141c42c070041405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 294774316 1250 294773066 294773093
    0xf02030706020f011a060405100210020a05211326040306050103060b06030709052713050705040c09140f030a0506160507120e060f0d02040311011b031b 67
    0x58100007501c0103800707001d0040e00c8840c0ba0f8045c2116072014400082299401541700d454850b10604501242c2107000384024a81140384040c02d55564825080c09089607000d43c0d06440750700c06641081850303402c10b164a5000d01d00301c50a10685c0c001d50f131070f10019250031911030900610080c60b81412420b901d0000c0004520403003010034290301d1401d1250440741d881050038050b0300308108021555500458550079030f2802c82e94000c2c0740301d400303188004403001c25685100d0403141006004100555000030740700c00d40b2520450b00038545420602c81502d0003844800045408404140441c1c1e90b1524948410035000e032140c10900300c2040028076103d442d45050b51541c000074140481401020000c40902aa03810402d1412015603540fa81c1075188140350010007050100303548161369807404031201c0b0303120030b005181c5508020012030000e40c0700d407000b01e400001142010f2910b500441982c82074031207040c5c500030707076031150340b4140d5405030302800c0c0341030b08000844810000b8205a2981b81d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 294775566 1250 294774316 294774329
    0x40909030804050f070602060a0f02040e010b0904113a2a020705090718181509140117030f0304140d110309010c030311210c0a090308070f020307 64
    0x4210b4101820010f0030310030102c0c1c0d100f0954203c602e080c412683c000600c80d4101500007800601ca00c2e03003142c0940203010b140c0000e601340c1c0d102000080c0c01219a0091300f02410104e50812005a1083c20001da5210f845c045506074002801c59010964a0540203d042940c10202003c0707003400668400c120f40b00e9403829114002626000f000903420303160392007608515070004004140c2448000748605a008050400304456001d84580041c030815641c1c008025424125083e18070515031030015040010b85140c2070048900009001c410300e0042808000d442464039201b6400e243c41110240e06008401c00340388800c100700600d4080e00001944a580502c1c00380104951410400b4107100030700c0d13482c00c2080120590301144000120803209007280034200090b070341d00c05140076400f0300400c0000b808102d8020880100c1c50446030009814a0b40d40c411081185d500d40303164031058050394016100262100e0b400b440069904001401c1550041c4200c044040e46c903030000e8a012403542192 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 294776816 1250 294775566 294775577
    0xa0203030a090e0a02120406091a090706030e0c0f060a0203070807060501090501091b0f1101110406080907290c0d03060504050903120c072f010f050c0a03031104090903 74
    0x4000060442d05981d802813288002946070012080f0f4558017480c020300064481a80c65602c0c40c01c0104810303030488080e603c2059680d03185802d5280a8445a4500c92140840d0401c101c01410300c00200c1c200200d5030004040c10301e4005943c090140642000883c0010342c4401c01c00ca4021403080302c090007040e40b11b101d0205156041904500c00d5900692116049600b0841141800d4144d100d0000a815261030f013404034000c5030300102c50100e103040754840d039035103413540b124448281c000040058070714a81b40c680c402d841d94880203588007598030a411047c0341c0c0f986c00b03090100d1180301c8040c68224088115050a0450100c02d0078030f40e00d010418042696120104800e0400f80141c80e4015144d030059402c0500c03514030303e07642c1c2030000d0200500100005100041100f5031074410404e9000040d00c2d04000ca006181500600440c030300039000c2074858080e05a028840d4046884e0400494054003100e420b03075905801810140c9490244041c05110204d40d1540c2440b441b40d040340246c1d1070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 294778066 1250 294776816 294776819
    0xe0a08030a0215070806130f0e01020d110408030307080907031e020f2211070615180c09170a060509030a0318050d0f05040e040f05010c0206060f0f01020a0203030a09 73
    0x6850400303120750f030a10700c2e0f440c1002c1204e03458001c480154005410356a0b01542c43c0c00d014100f00070a01082d4510307016103030505004420300154007400d450400d40740700700200600400e50651074004d601c5501000d40c002c10015660a00c2411350603080705898048503482516a540e6001d02c1c0c0a19042800440506852070309602d05400d52000008090f04e02c5003c14584a030740c90761003501191034110090b02c1d0400d0307144441d0181c00325202e070b54011004001051203108030b600020304e14407849000c1a40d48a01ea900c1030340501c582c81207001d842d1a541c061520f4000240d01c000b240e16210003141c09011100c1000ca41c090050034480d036004c0000c2c580d80c1c02c01b448040e080b902c0030304000c080442401100c000180c00041c083e941d000b07441c188140e19580ca030208079201e00c11500310013484400d2100b40310403c8603600810700c1c46403041c1d00a001080100c1e20803a40c82604648440c1d000107081308d82034840c01e281c00c14a500c1203061054417000030b6140c0200385144c1c092540c0c880020b1035140c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 294779316 1250 294778066 294778087
    0xc030c0507150206240f03070509040605040210080609040f08070c030302011d03040305060f06060c0316020f0414070e0117010b091507111c0b150103051b070b070e0a0803 75
    0x3844d54005c21200c1408000d40310400880c00780d140100c01e89000f40c40b102100290313990100201c0004040003803400c8141c1c41c00e458a0b0000c0c040035541280035404800c03542050500a650f09849003501034951140c6588507195061200c40400b0300b40e610302c104102c404007191030144140701643c040c2e000400c103016030038842a0007440440d401e0415400134002400051000300749581c1001c0308400c05901500e400d400503c0c144200903001c0310601c00000c1100038409070070b8441c01d043d03000f11417100001d0780240501050322407034102080002a0f010000d02c42c18094034126901941c11314100c3c058000c000d00c41700c00c03c034081c0c00003085104041400f1a6500e021904900d00b030f00700c041600e0803d0410f40c0e036110050941440a881180203180710130104030400e02042020740c1128081007030b408c20001425000216040d25800241803100240d140740b241c0c04000a1494106203a40c60400c0e50788640e100e064000d400c51081121000f9000490394914680402501030140a035965034005507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 294780566 1250 294779316 294779323
    0x9030909150614070c15110714010806010302091c0618060b100507080307032a050d060510090504020702040608010905060702011406010906051605010617011116030c030c05071502 79
    0x3d4548200c1010442200068105500e58080b03d143c9005410f02101046013900da060100c0416030302807013410703c0050100b2104030320340d90883c02030700c6845454603903d00450036442101501ea8101011405071071980700e41800204e80c035402036100083d1491f4413016402c030381c0c034182c0c001d46200762220704510641c80c202d01030074880045400c1032450141b50707556001c0b050000a100906166403551511140d080361f0304003582d2015041c4030424406401c030f0300504582c1001105d00009494540003050358100544c4101c54452180c584c01030340c514100c1004042c0d40041c400300d8000381c50307000004440d5400d000c0c0f6040310b0700c1000900f0301d9140c131400090031036114046068030742607203005120159801c049a0030560707120f440e103281e0741c011402c040c0003072101d0040e004100e50f1900900003100004107080c07070610707042e0000a1000452906540501d4007903092050f00c601c24500900e000603020f0300618030303081d01c43e0504480d484a10345030681411520750008414031158255403120b5641403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 294781816 1250 294780566 294780587
    0x50f010f21022a0607081905180610030201140a09030203011b020d0305060f01121d0d0e09150405100f080109020a05100206060111011d010204030615120204090309091506 75
    0xe0300c0420700444841807483e50781d003005c0c2c8108213100c0e0038000700f0388098864a2a2070000101d410900c0035040c04100034410b032020154400041c000e080126102c045280041300441c2d40580d94120034041d03a0050349071552000c0d20002c24000c0e000c0d00040162428000d55000350f8101c080e201c8139911884019003081000c0c81000d040504c2c0c401041159914515840010784080c6032804c9071a0410180800500300c2104a24124a01103012600040001745100003240e00341d5404060544a1060000d0b500003602d41c4044541c26003014411030800e54480780d80302c0a00b410382d03c4400d0350750b4120040b80096030000019a5111000001541080700c1114014502a203140140e40700042c0d0081d00d402001e8140c1d4108021003100b5412284250050559070b080611076400140f10f0000d200e0003075100c1d21045880a052000161050f80b61645100890380b0340d04000384514601d0342040024001c200085060140c080d0001c18400d059200b4100840b1710a8001240d003824040d01a1a01068 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 294783066 1250 294781816 294781867
    0x4020a050a0317030417070506070e04060609050402030402031e01090605060a0b0901030e1014100b04080303040303151a0306120c03030703110a021c0c05040501050f010f2102 77
    0x1645080000460306000b025000500305080d84d1291628a0000c900444440c0681c03c11440455880107125000c501036014800c20748806160724480014401a2822480340001040c040e031400c00490030550015940540b0003415915009004451040225244074000207140e540f5541402040030a00c07500303401a00403503480101c1e928002c1d00034003610840001504054807150100011041003001d5181502055428810001001c100f03190b0014121000c2c0c00780f015444002030780b400c0075401c6501780e450301405986144c2d500d0704c09a000e4603003440d100d5030309071010320001400d1603809820420708444100c0e0581c3d82c06c0010400004c03e0500b008480d854200004801030342d40d0000c100e170711f6142d0505040c0c1c01340c0811a061801d00040480c00781d0000304e812580d1488545010740d0320140341c03041d88416104d64683c4c0c140030844a09001d440d40001d80002000031641c020f1020307000400c964074207400040c0c0c0703448020500d048000c0300c030b481141c0c010803040e904105544400464140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 294784172 1106 294783066 294783079
    0x30201120e061602010b0d02090c130f09020405010314010e190209030d0e1c0b06041a042a02031309020703110307050312130b0c03150a090504020a05 66
    0x207240c012400651810860350745078581320a5174901f85801134090000c1ea07803000759032036036136200a110506021900000048415a160300c08028100f107050160300c0390703d40302c001342c240e403d41d42d0b00240c8a45100c006014540b15825078680c81110009041d22a000d5610000700900c00c00700d54a8040c080c0d40c4104103440e80140e0700105540060f1404c00c0314005450070420b44c644141c8004102c208814003041c403620341030304010203410445454012000007140040c08540780d007402c92040360098071001455050707124504820801d0b90015601d005940e00141307107010380034000d042c0030355800f182e908240b500c104440490b003121030080341d43c2c42c0c039070b42092592900300303101c041d03031010380080051380210f8980061504150b11400703110b0349132120100c465040d00b00800b50414443c50b03410001c01603489651000080c280c41800003080d05040c01401440302044d00700c41d01504 = true := by decide +kernel

theorem cover : BRFrame.Cov 294604316 294784172 := by
  have h0 := BRFrame.cov_init 294604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 294604316 ≤ n) (h2 : n < 294784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
