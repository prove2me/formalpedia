-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4885
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:03:05.701961+00:00
-- url     : https://prove2.me/submissions/b5eea745-f756-47d5-b8ac-9489f3659f82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 878417266 ≤ n < 878597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 878418516 1250 878417266 878417317
    0x1020327010912051e030304080403020d1e12031b05030a3305100f0c02040506280905010e090703080304020301061214010b120705040b0f100f030f0207020a0b 70
    0x44400302e103104030010020b403541141402900c21030301c02a501175500800c2004002a020025201100c0c3d0544244550794400c2c54000a0744054602940180c0d07000060002800015400c20507000c5c21034030b0400c4402d040e1060964103990040c0c901c00442d0080000c40c41c071002030390002a1204801c2c044800b5070321500c02d441920712031850580740c0620300210500c028544504004180051810500c104401682c005807102c000100082d00c203942d43c0c00020200d4032140c410098415804a10010f075640407100044451440c1c00f413071484a02d02400070030803001c2800018001c0c84280f0013090540e2441c1d846902a90000700201e8065403100400120004080c03003000c40240304102c4c82e5000402c03181c00e242180c2c0900c4131580b0403a201d0400303038031064001c1092011b0354803d03100441c00e250503001086c4a0000074000c1900082c0524045040561003040c0c52041c5a096405001c00c07a00044104140d0040c03d4002c1d40c480c4110004120f0349116000816050348266051a1098030704034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 878419766 1250 878418516 878418539
    0x6031003260f0a11010204141306080f10050609091f110f0406020c09010303210612120f02030c060c03270309040605040203010803071106071b060e010203270109 71
    0x300c001e002c240c00451034a0b002074001c2440862402e24100850405280c00c00e0603031035260b80b001c40ca0007103c4095940c0c005d14107981098001e060648116003544085080c07007640c40b0340c8842c1901c0c000707207400c02294035880c0c0b20b42c0c00d50090304080003c1c82e48181441d01c01c01055071800d1050a010750314400005003180340c0014144002a03001c5140d03e0702d1400030064100000031707900b00c3c4900d02c0c4800500000b90003411440d940300551100056580c80c08035004003c12180d0401d0f04c004107840320b2081000701010080009180550301c4400210034141c003070340d40e030140070b02042040d000040001c10b24011140910b41c84a804100b1400c140d42d00c00c102e10a80038410389402c000d400c00034080c0520300303290054000910040d40c0852556240250140d202d000c0c00c0c00040c031103400c2e129a0382113540d4910694a0341030308070300301c204c40603c44001c054a201031413040704046079001080c501e2560022043c0e444a0404c500c02e00d101000d888510145801d054011a0500c044403030080f5051000c079 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 878421016 1250 878419766 878419777
    0x30f12200c12160311060403080f0304210e190302090f0702010c0e0102070b0c07030b011e051c03210e0705090a060312082203020c09060603100326 65
    0x101905030020490140003011004a440025550040300c045107008003c10040040741d40120060020b4200300000540d00d1140d6400500842404112100301da01c0c00001107000d20300c07c101000041240c2500388451510301038a02d00440e0060f00000d00904189135001c0240d411000d038a1041d0381c4079400607450f000c0503103002030990104010000c9058092081007141380c040d042c4104403400c0c0000003903403162180075512400a004c40d01042c400c90400c40480034640c468400ba8840d0b0b100c0864511030054420f14032260550118002818180602d1010052182d001070740380e45e12442d00e0685035203081d254400111000c21400700058a40ca01c1540650004040a01403461912080009581000e4078a2504070328001c01000003890381160540c0905541c1002413032540c4076444495800c040c9a12a1080902c039a184410964041107042e4070400881d454050f5840b060f0038000035010071070305c20b070008514030801e10114125440e08982d0618524030f04943c1c0d144180540c0341034118 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 878422266 1250 878421016 878421077
    0x504060608090c12030a0c060605042f03010e160c06020a0f030e0606010207150309411b040b03070e180f19110301050c0a110601030f12 60
    0xa00e0034401200c109001110a910080301d04011341d03464584000d0b00c074802c0c05100814000d0b1006a2020080260000002054028401c010400c00e0a181c048260050300e800351501d0b80075004800429118010743c0e068644640c0d07954040c0e0303034001d03401610841001254003032080c400503003000102c20b03000600b07071076007540c2d14494030559500000d02968854200c148203034005004021a03640e001954004580c080340058000040d13048080e0001c000114014042900318412500000c099605681e1011980d8103c00813a0382c0520b012003004802800c014129081a516a903807140480700510542c040280000754084404000a18004a035403121401c0d0007e1800c20903183c07074400e200342d560101600a007082c00c00407034801c0d4844003003c4456064005d84070150003840896410b0708044e400150080000b400c14003c4000142c04c901c0980c3c000a1320f0000310280c104002c96034078100e03540b1801040d01c688255030751680000c000201c0008008450f07080f0640d0300100c1030b0481110a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 878423516 1250 878422266 878422277
    0x906070302182215030807080a180f060f0e030d08070315030b1b070b06100e0301020a110708070303050f03180d0e010e0609310e0106090c0228060605040606 69
    0x340480d1205940b581c0041c01c04004400c501003000c204206c017282c41c20703980240390030303583c46040c5030a66041101c0040451402c0d4203810201d07120308451880020785689850755841440080c100300d968486454031341c1e42541100c07505c07001403400741082c00e400541c80c0c20003082d03405026640d410141d0850784181c40c5a0f00304400c0c09182070742405040d803191800649945054925158041007200140c1998001c040044a00310440d200d10108042c424004009564401000d00d00404071a80700e00c90301000d00a400000456050001d603c4040f0707a4035803520340c14402261008805038200410080c044820b0201c1c11421b0780d8103002d107540c5c48065441d05200200174400041920384d074901c0c004d000d11020485030000340d640d45699106d480710301d0549522010701c1c0008100300c29914101f00b0000f42818851048540103420440c25540740c5075042250b020001002c9030744003051454815010360540c03400720744140740b4070070704d040c0c501a000100301e140d5607501103401c40e8802c0d0701c40c50005c1d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 878424766 1250 878423516 878423569
    0x41a0421211b08010617070309020d0f0302010509031e031f1d07051c02071103010608010c080901090b191103070903110a0f060e01110f0a0c0e090607030218 69
    0x854402d05151031201c40c070309800d596042150250083c600181d081740c040c1c004000103440b0512a400c0886041da014002d10340c18442890005043c085c107400c12005035003060002481c5450010640c3c0c101e055510f01500e85641e64070b68001103500140418040020f80c2140c01447d00748003030b00300000c110300311401604030031034040c01e038104030060070030f00400600704005400340e244614070b030381211001c2c0c0d00181c0d070b41200d2812001200004030709581550800b40001406003041d809101941010b480d0b040660340c881454a080300c540310b1004040c60701c004045003840d4100c0d000c59a0181c01101c0001d1081c8040e2821811a00110759050000700c0b5402c0502c00c01020036000000034005417036582280d800c00740c0d04040307260a401034200700041480c09106aa1041020301d1001c1814000d403442a09008100c64070341100c443d00781c80f014030034100020340458014605108005400180c2840d4a0300d030717000c0b006548200484441002c1c44454100c8956503001c0c41d10500180300f81c40f2400c035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 878426016 1250 878424766 878424791
    0xe0d0c0312080601020c040c05070c0b0c070501020327030f12130b070209190603020d060c1103031308030c040b0c060601030f020f030c070501020c070e041a042121 72
    0x1aa003410301c4108160b02003032100c180d80000b83c0d007920140803140440c901c050321908071540c0c0913080c8040c003080b0702c01d0400546017010324002c04451441100359020b1684407401a6500d120b0707032040e0041400c00c003501007400702901b01d600380c0d50100201580c54255802420034078000385207078042100326000503000781036000590754000a1003107000b201d06100342500042c21104005100700c035602d00a064401c2500025030020000d107600406956165606e8101a4014040402074101154442014405009000040e00c0c403403001c105466564582c1e07070751141d000ea000a00180100202840003190000ca01c03406001c1400070400101060701e003410004059a04801e00900c903d481003100c0c07a80c0b19910000c59501602840c4940d0743c1e0f00880c40c00b11300a2041112030b500c84e0041143c040b640078240011039010300c1c02412501041c107481040b22042400c20760700180a94684100003450b40801030900d65004e1160500c101d00c040300310903d0030b031295800300c10741120343d96030a40d800c0c0c07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 878427266 1250 878426016 878426033
    0x120a0b0907140712022e110f0301150c0804030302011e020c070605031807061205061005040e0717070207030606142206050d0b01031a070518010e0d0c03 67
    0xd16407900150070b603610151110540b26420010341250032414400107018001c0140c01205c00601c110810b0f4000d41562050025505102c42070026040294241d068890003050ba0010200040d015196034608070741c03412480c846541040a000841600ba0702084400016000642c000e400104044da8944100d0603c824007000404c0c840b8414484a85074000005540098420701c0c100966031780c50b05d0b01d0b00a2041e4803031520100f43d20506002050743c940c021007007402013040f01818040c58445604010004420b07a400000123802131000704401802c2c12030f03058109105044c80348800000160482c0354507001c84000380940d11000d020010400d452042100402c0703203503941040e1801030400940c04901803841a5508a441c1e8070340000d856007a880000100300c020b03c8007502000d1031070703c029a12001d1100350b504200144070b4080c01c000903410103101c3d40c13982c1d40b01c81c6410082104100d8100130b8400301410001010007240b443c0c0c590070003400c41c86000e21048040c580c5103103007032800c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 878428516 1250 878427266 878427271
    0xf0b0f090a061d0612012903030d091112070302010e09060f090c0a260f041b060905010f030504032c03060901050411010c031b0611031302032a090903120a0b09 70
    0x21710742c0c941a034140002e00e4103292002d410040c00300300e401007100d6070000703071840c0940f80000c2c00c1146400c0c0b26200300100614643d010103801e450010b40c1d10b003141e040310340f103454912000e4082491059000f0580c9070502da6540c3c0300000070022181c41c10910085001940c2c1150070219100c0001500b0580c0c5801c0f810004852102400c400b91441d9102000e07405282c02401c2d136010351210341d010030200846840451724103202404020407560380e0f000e000380000903030b03c503240c0401d41914105004a12a01801d842589c050311640a00c1401154525644107030040201102e082c440c10380c0082e6405110307043c0503400110000c6143d0a282c10000f24860490316000d0500c600c44182c10300280d08a001401d280c0451032200340c81b014541040e001a1420751456003080300c00004004503218403145454a05001340e0486246500354040c8441203115610baa19040b90000040d804624002511943c0300c28903001b601e0800e0b2000c4124401254151008021141c80b112240c419050030801d0300c5e03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 878429766 1250 878428516 878428549
    0xc010c020c0307050a0b0706090203010e15161106060f010e1005070b01080c090109050603030403020d0b0a0608030301050d0f0804050d0311010f18110103060312030f0f0b0f090a061d06 81
    0x117a40c030301c0c00a10140314442c02200400081c5c03604242802d65400303605c11182111114191490300c4154008486011002c84018500724071340c1a22118043c40354200641140400000304801e0b00c2d0710040280d0441d07402c0c0707098104050081421200e40b559500045598202d4481c5500c0c0e65140c5011112280140c000703400c1607020021510035070f40c41215260468001540000e90342c0c513004007280c154070540d00042d402100c143c2c107030401c0058100b4110710404000b1030401ca070a4841212940781d100a07c41e0360340c0a4900d9a01101181d0314039812009144078060b01031510340c0d5a40031512102209009901103210000100d010050a01941082c4031841801300916003c0410040f010101a1000740007003004060303410181c1d00a50108000c2c640009a60f1900f010a103002001f400e10024890101c0c2e04101500b9400b913051300030a0a8004000c10320031261420500380002001d00501e0440303540e07119240000c400849500b000d07000a5050b4036100c5a281c01802d0010000c125005070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 878431016 1250 878429766 878429779
    0x150504050a0e21040b03010e18072607032312040f03061a030106080313170c30100c0206060d020603070c080f04062d140c010c020c030705 61
    0x210084070049020300a40d2030f03912003181d440382808050341c054003ea410400c49040008000b0070b000041c11007092140e200544401244c620b081c80154035a140c5100e8110044207418600c2d0b031200d8141152040035400508840c03401d55240c80310001300d184082c1e0042541055641d080241400748440400c64258078203181c0742520b404007840d00c100301440003522541e506e040b200030b000c02d510080304007220000e00070300685d074544441c20780380da000b0500707a03500101448000030903030b1032002250349214260340a00300510001051118454441840c003c811194042c2021200c140e0040040b0782c07504100208007014410409004440281c041c1200350740c400d0003000b00942d0740d11440404254180c540c6522502c0d042030549102c580d95100070b0078030340301055444036007880e00040c000312480c035a0f886149000b030003c95031001c19100900c0c8a0300c070003c044000c40700e0141c000c4e1f40b5a180940115403810b942c9442450840382c40101d68030060b000158915424a400c1180d203002d0b140860b0714 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 878432266 1250 878431016 878431031
    0x30e031c140705010213050109080d020c0d06270b0f010e0402150c01090b1e07081f0510030203041103010e03071106090414010905090d0c0f15150504050a 68
    0x18840480001001041081481c420145007600d035039007900c2200e0f9000c002951144042d06d022544802507000c2c2c00c0c0000ca89620009080c0400103814140c18034039005003040c41059000c4c40305001c00c40c0c2003035800a45130100300c220000031803803901c0144800050600c411005180c1720045600c00740001c120344203102c0050051101d135880035500254102c488496034045410742040c0d030702440101d819103501c0d1003100c40c01d0120b090001382c400d03c5c9071050300c0007035180511041d11044050381c400000500c91000608aa034006c140d68001c011800d0301c0300d07041580c800001e24164444051140000c6e0048184400c01600400c482001c080441c020b000c20007080342e01e99940e0103070007c05030044c1a203942c0c1e40c903981c0790740040f03600000000d00b0a02c000707a90248031714464071081c810126214600340c0025203100d0046003441d04018142d0380d4401540742c1d0385031600c2040c2c03003150641c0e4400e00000011085840e42c40b900300c12002c00d54040750483e180c02c003040101e8100074043c402681c1400c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 878433516 1250 878432266 878432293
    0x120c030212010e071106010b0a120e031204081201150e09010602061902130b040314010b0f040902060909070807020d08010302090412050408030c01020702150c0d0509030309090a0504030e03 83
    0x1810305440f4851201062a40c0f0048100da00c242036100c040414010708001254504460008101d01915900c5504070038001c0625201240d84990b03c0e42ea6980043c8011031440001000d4641c000340280c800e54284043c1c00c2d0f600007880070a03030041303c800103085103020030340c6e80102e642d04406c101154106410342c54410701070f40b680b00c024481e82c1c80c49020700c000b007003516081d03040d984000d0044002d03e4031582c4030522101c0b284d201c3c0c00285c4d8400529103aa40b00c0990500510503001c0d0701800b075184040c1c0000600020307040c0180300301d034411014083d02c0e03015103580010910800603951944602c1c06d000d040a070904058003000c41c2044050401031015071584034506400c030790301030294500b441e240708040b20b8502658100b001540030005105030100d02c1500504260b900864074a06908624180301c403003440b400005001c0c9402c00610301c060240503201500803040701400344c1b86003100c1c4d640061580d8004441c201280c030f641e00140b01c14150706c4900024056401c0e001042d08180741403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 878434766 1250 878433516 878433547
    0x304030c11040f050f0619061d040912090f06020f060c090d2a0902090f0103090c27061203050417210d1a1503060d050d120c0302 57
    0x94090309141d0301e00080d550365207480d4000c0c042421914420000e5040c445a90a00b5080582d12a4481e8001060f440d0805001842d03540464145440c2c441d0031002c03a48480005c81b0140803940d80c025a9100d016000c500d00640c02c801c010b4550340c03903c119a0074225664000310054100b1811503020300c120b60207000307002490355000852030340160349602032100080d507204181070000300003092082c50b0340d20001500078440007051a081e000808a52284161422030007010911075100c000480c1121441d406540302980890184044c5000b0380e442d003071001e030340c00c48a00c1c454008403281203503044a24a01d1141c00081c107250849a584415030b17481c0100140281d00513042080c1c81d42d00303031850310300c0100301b04035100c0c0c220344000d09c070003100b800105c209030005900c060f10582440181c070380541410842000c41c1c0300c0204014510340c000302142c0c001da0001405550450740c2d1220201c04a1400c002c1002414250b5480b03d0340d003816900290141d0b00c0841c6404d00345801030164041300e14101c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 878436016 1250 878434766 878434787
    0x20702031605060d05360106053c04020a050913050103020105120c09030a0804140910150e1807090e13030f03020d060602340608100305010c23030403 66
    0xb01c800708280d25496541c1507440001546450402201e00e885801001c001d4400341c180429031b40200841960b40050003c0d03034102c2106000b02c034111403051285840c20582c3e0400c0c0c00c502c41094510000d054001c90203e9000b0307800200424030224005413580313451070103407440c080c008100340aa035155500103030003401411010840c068515000030300011444041d1042e0000c001c3c00c513404120307142480f100c154030a00447c0720400442107107008030300b4500c0080740500e14240c10540f040d86010303800c088008a002d2a80300300803c84808003202d0392902c4000b0701011a485100c00071307080801002c0c24020003a40040340305c031041d07001c01c4040c0e640c412200340b086405081003030301144000e02c100c0080c403c4801206030355141c4013010980560001e001480c8c0803c07506913030100c0300c882a4000c00072092040f0810140c1c1c122406002c200c3c45034070b41e5600000384004100344a5241c1c0d5905017910800780c0b51400003007030ba2002e0035848483d000ac1c004820b80e000d20391803850400ba1801001c46c04513 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 878437266 1250 878436016 878436037
    0x2010e060c0a140403030306030c08011a1002070b0c0303101a090904060f140a060605090a031106090303030c0c12040602060a0903111207060509060f041218060302070203160506 78
    0x4070320010018003444105400401c3c0c0314990b50344035140e190181c01000ba80c0020f41d58105200b001144901c0148a4044c0c8801c030b24010b02004075000d003c22080040081d1004114041c45800182c40304915000d0181010040090340e140c1c944a408003000c0800780d440311003108040a03c550003d40342904488420138241d81002942e5034030704003140130b80300c0841c1c07c2a06d40d00d41080080600105c0400b540500700c544814448107a6600c0d080701c4500500c83c1c0940d0109010500300001a84008114111000038000b1801e1a80c080b00181c19070300125001e4000000c0041d40740080d1a09008003090307e28141811030406050010080d0b80c4c040c0184000a000e54a01200341414015190310461005040c11100e003d4070425002c54150050f0804454040c1400302191000201060051113030081a5001649565544407402405c1c4d07403880c150140400351020f403a404c606103c201015098546026070303210503a105151626a034008220080a02110107000320340d520310450301c01e0f030710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 878438516 1250 878437266 878437291
    0xb0706140f0c040b0c0c0d2915041e05131106130312020a12020106050f0a1a031308120921030c0708090604030b101e06050c0a0c2402010e06 62
    0x8000034001d1511b45103c000907840868070b6009020045070484044254903c41503880b40e4003a00c3c0600018120181c400b03544101d20442c081c5d10a007002c1d80244842d0340c0000010503820000140e600c1200c1c0e00b9144013a4000e1707105020014401d611403101102042034440ca890904010744a515102d0309000061400d84000c03166041144200964010103801681e486000d03c0700c100040c2c002e00b2a841910f006000d5103000e40820f281007420130003243c001510200802028103195011b5600040000c94001c0f910306150002c5070075140a13040d03002222422920354142111a180b51400c1011800a2524901c0004034103090200940360000d10011200351a0075851520010b680241d01980c5d8001c400884e0010902c84e90105180c0100103400701049119102c0d4400604d8100100c00c14012030a5a2410861507100d03030300501c1110400b5096030036111041d03550301c040000d2a8000b007120310322510018000310445004000441d40c0c5e00081000228000c0110b07191031000784002020030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 878439766 1250 878438516 878438527
    0xf0306010e0d0b070906032d02031e04230309030a060b01050c060f01060e100c0b04111f0318051c02030c070f03050712020d0209100b0706140f0c040b 66
    0x101d0306103405841c15070150f43c0b99094130b029500208038031454443c04000038100b46805604c0404d5444c041d000c1c4086e028420b43e00003c40141001035403001d400081d413000604451142102c0c0050030303a01851041441c03400d03100100d002d000741405000340e05403491b0001c000c510810b50b0009556485a0390060003c43d052a00c080169170b540500541d80510340551070821160700c5031101a14141c0e0401d48603c0400380700803040c404903984010b0f8540c0031a103420038038400301e48417201940e4024451169508920704403c040f4401c80c03100102ca0000d880c000381c180a040f40c00d40601c401070345403a110710040f0b40064031020340c2c0e801c0d90101d0200c4400314890342501d1030310038801c60b040f110380c2d9400c0300c1200340c2d50f040d1082c00b24490710040e1454024900046694000210b036090801c1c4c004210840c0503031187c08100200c200604018415161003500242c0c600c13501010f000498003461000680c0013810304a20703c040c400418503900c200d040c00400c214141c0c94001e682c240ca0071503503d0703034a41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 878441016 1250 878439766 878439769
    0x301050d1b0801020c010e150402090a02131a0903010c031e020d020c0303100608060105040e0609061813020109050901030f0f05010f050f010303020f01060602061302030a0f06090212030f0306010e 86
    0x80341c4940042076154000502041809015080040c9075a1210100c501c0c01030000b602d000c9010054074003d500001c0e540100e1003000307268002e407402c90200c1c40040c10082da1501401180002c00c00a000c1180f4003040005103440c0270b10826000606a040901c54450300b0b0f4850920100c41d00045030749241c5c04144024400c180c1d42c140e416030040541200d41da41020800103844000511580300041d800c0d0300021810b5124900351070440d170b520307059850702e074480700100440342e1f0000b01303400d8220154800e1313010046070520030940074482c00d2442c0205214280001007020fa40c50b0004e50141c0300103401040015020450070400e01d42101d0344404501c414039000f03014100701c0104507045424402441414a02c40c80100e048074072907000c8840d40108003260ba801e9580f244509405a040180003401904100020781c20043c801400e130303903a60f0400e0703541070700e4003081c00c03000c0c0c0751140d40c2c40c10041107040142d00040b0742c3c10410700543c1054603418448440d40301c0240b0b03060401ca0b02c84201c1c0d403113 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 878442266 1250 878441016 878441063
    0x120b0a1502160303140d0f06090209240304030f1b0303020c21040308091906020721050616020109061508160e060613030b130b28050c0f0703050405090c0301050d 71
    0x101f02c503a00c001c0c028199600c070001e01940240d01f0142c4240103101d27075940661460b0070041d685c9000031a000e0b0843e501c58900342c0352124008640030500107800161500d140000189050080c070030b1b05d005803a58945070080303280004144800514007120b04c1d841d03d04040d0041500c0880c0d51203000b40b6691705444022446c14003042e40051880548640c0101d00c040d00826900c003501d10f4000e0810040d0f140036105070352a4071940f40078001ea000840400d107005001c902c05507002c542c030300000c1000b0341541c1e20b01c011112024440070725070003019400d0180300c0c01842001607041880c1d02401c002400e022417035007000c9004c0d207541d11a15000420504400d10301c00e041004640220b0307185168901350324140b00c4105031400488004503000001141042116015101c54107034042d120303407001126910a00078000500800c0580b003040c040d03602c03000238100c0142102442944c1e040d44a0345820140088000b024101c550004014401441583c07211096109040c0e0003a01e000904e92001510800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 878443516 1250 878442266 878442281
    0x3020625050d03020702040f090210030504060e030406021617030d05041b0905040b1b120402030a1b1502030405060d0b1801060c050f03040e040201120b0a1502160303140d 75
    0x454062072000c0c0d01d00c1c030f40607400307810114002c3d83c0a004d080100986002110f801c2c0c81e000707500804005d016001a0700c0b961150754880d114800008116450000d803500e5600658030050044c0c1c44004001601d0303030460803c400030085010303940b01490258082c1601c03030040070001d0100319920300c0040d080c40181600300030000b1031070711060321942c0c03101103403005002e0440e0306450380740c44032022503001c000070030350a11009098025141030402d8000624160a4041c00c2640c0c0b40c4600311004001c940d40316100159400d8410105002c80d03d80f544030703651028424204030940d007090104100548405013181d14821b4030b0540014040c8a0100282202c0e1807996004004a07211001140d0983c00c48400304c842c0740904100c840c41610080126624811805103000c4945000085070065000351641144100c0c90301d40070801003803980110f08000705030f91010020048903400281d00c5901032018982089540403044030780360868501426048940b89007100300f1200080c000a0440030303a00816 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 878444766 1250 878443516 878443523
    0xf0c040510030605120c0f01180314010b13090203060f070c0510020901020f0a11040e07030f080703080703140711121603031803080402040c051b010f0605060403020625 74
    0x70072441107981c006005000703a001e114041d10b42815000109500040d0641501c080113241e61110310300c2100442d0004042800c40c071961340e5000004c000910703000c155030052000c0c00000180245101c0c2080300aa018030b4007489114984041403015840c0842c025502c01c680140d14200e90311004c03802c44070601b00f130714058503900665910410b8048150000c09031054260700710b4216424407449192038005e11500184280c1201c8958102c03820a900441c0c0341c081508269507110750b903a101d0280e80740345201c08560b481c600113205000c05800003901504003850307140c03c0007181901081d40042d244080c240c0130031310035480303c0c100c02040c0030000c4000b40900c0c0c84001c0d44980c04070a000581e2200351500700d022900300f504007c002e00c603841a80000d00c1c0c2550f07840070291650f03000e1000a191900180e070801c03108204c80c503e03041d002c4d007208005804002c000903e41513100011022501ca5410240c86003408000400246c0d60f0142030b0b07009052403181c228210f4a80404105018200c180000e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 878446016 1250 878444766 878444779
    0x2d0f061706060d020d0f05010b130c05090f0d08130603050a020a0c1b091103061e03100225080309010501062c031606090602060f07140a02010f0204090b130b090f0c0405 74
    0x6c040000641002c0d15013023080d0346035103442010000d070106541c9200c030719000141d000c1c009405140b0709806030039807420025292402d404a280c41c1d0190940c00303902901c00490800204020150303041c495030342d0000e81c00d0400c40c04c0002516004261007107106025008203401c05a0100e03010f05e1034482c80c0103108075941040b01100201c041880b64004a070340d10f120780c962282c00d5141c04c000717401a00e03540c5002005840b04614081c40d160080d0440e10041d085c0e040707580c0c4e1881c00b038000d104002e44514081c0410540340e01d802c03110305080d039105802401c10008910b544004034170401182101c546404c1001d502c6500c1240d010138906130f0701031400485044007800010311a41c000582d00f05560013642a1600c0e1b6540c1c0c5e00000081c2802d44a100010b04c4501184041200c01c1020b4680e2540500c0003050004181e050002070380c000da003124001ea540c0c0c0081d000c0529000322460741700d0b01d800e68280b00c40344205c2c001401008008115441c503810303040016004950000460303000e000010a403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 878447266 1250 878446016 878446043
    0xa021206010e130c0c230607080406020f0d1d0a0c050d050a081b070f1a0a033b010506150c071a040e010605070c092d0f061706060d020d 60
    0x1400104510401c2d120906d0400a442c82010700080180c0d045c0a03010080400361070700c11003212861307001041a560250300340005111740304070600a00300d5103000745003c600c0c0c0c0300002120422000014011215920402c0818000340030300400b823040b10f00445101c00d607120581000ca0510b00171082c0180080400644041c84c42c04880040c1c20341d0190301c0403a01826100c00340301c3c64102c214040c411020400169001440e0800c100030014003d8526002c0745000903904a83d80c00c994410012030416070540f000d1100e5000345041200020b00c000003030286c0e040a002140c84800394114a4191590018050b180d402c4100b05000080c0040b050344900105a0740c1c2400c03070340c0c1103409400d540c066164000900c40b44903009603241e05801052030040c2c9480c2049010042031843c10021010f0b8014400307a0b001c8903038520b43e000300201c0d11404120520740100382e06c00c0300c03c0c0342c200c0031006240000d640c001041c0000c40e02d92007101542e580301c210506000040b4140036440c0c00400e440035041c031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 878448516 1250 878447266 878447291
    0xf030f0b060a0b030a0902121516170408070c030b0f06030d091d1026010b15040e0408121617130201320307080a021206010e13 56
    0x54024854050010000151148000c010558070740e4814224800d20610124203090a01c0e4000749803548000c05281540a00000560600c4140c00b40c061080e4080010007840c4241060003080c141c0407880e04030212814080d44451101000c1c0c0060000400480d4a108000300719402d0b0014581100d240c0d012840c02c0da61080c91110b0850300b15000740960a03821120a014545031010390b42803000c00807032203c4413481001c58040003084a8986a0710200000d032442a1101507200b5101c140711101c440d15440d040301d4251401205107900901421000e0b08011a180302503c1c15a141110b0f10121034032035082071500d9006982d100d0380213a01c03c00512550240c8043c2d218414042c50312000001d03068180e20760f101c4041102c00d1240070b8145244c100066100341c0c079203003103804d03c40c0101c07a500458441d09100300803000104a800c46c000018800702640102c445c5c0c2e13100c20105403e40c0b600d141c00720128243c00c00a480c81e41441810032000040765500725002280c50449002004900061b04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 878449766 1250 878448516 878448533
    0xb0306180108070602070b070215031f09020d050f06011b0507090614030607020a030909110d09081e07080403061a04111e070c030b271e010c14130f03 66
    0x8130b6074015214994001030092048000c0d41c44083d0020000f14400d0000c250b94429980028168001d0b2003002d075203d9110604445d0100c050f001038a001a2206015180c5008646000d0603c1c1462582c49040000d02e80e1701c520080f100d000c07101d07015421740c4032525006241540b5900b041c04514103003940071491140013019503020075011421200310f03845450080c3d846203c016800760004450107001c1c0544009508444140e12005040034a003c180740701b81d8040303c1c0801000c941990001803c03000c90f001c81c0243d4001c140b40b4600c402d1500d44541c3e80d00302c0c00d1140b03110090480b500da49500c240107400003040030b00c100001c2c0c0188450500c0800680840e803100f05011101c0c8858240c91204140c03000545282540c441c50840409086d40c032030031501e05005220b00c015888010754918514409629040f003201e4903001819018142210103200c40400041c12027643e240c01c8241901a03480300062900d1800034421a54810b01104a07142c05102e981040314000030a810001c00c008a05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 878451016 1250 878449766 878449769
    0x1511090103141003030e01020a05030d0f05160c02131d0d03050c040f1809080f1206101e1803241b050319140a0c0503010f0b030618010807 61
    0x9980c204085a64442401201d41094980000701e00f0302881c2480040d000d0203646110990500444040c5000e0f6a05c640c55640081c08108520762076209560324804503000f955041001c3c04132421040c4081c0d00c1c014407201500c200a0711401c00107541e104048180d5120140140303801c0b1444407a4090700b00030556074041e40d03103030f130b00021b14020002c0d420321801c0d01500c003500d460300440c5c040107140c440000304800c2c41c07000e011469030b6962120fa002a2550009000c01141500403035140c02000005000f91003008020500480441414007850390384031602c60321009900c9418001021350780400c4130040c00d00ea0048121010020303010091100303d0400f4980102c511040340c071001041d00e0043c09443c510304640800c0140c0300c81586c5a940030358003440d401240d00b50f04c08111081c00400340107891503c1d0f00d0805068885e400d100300c00405009040c00129282001451549801c5514110081a101c2c002c480180440450051340e18020300e1607201d0610096054031703584407040991680442e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 878452266 1250 878451016 878451019
    0x1031b051504030212030405100c05120a1416080309012c0304210f0b040308070306080601091d031207090e0c0405010f05070516090e0f0a0f151109 65
    0x106400080501c0e01c8011801c412844100c180d040c03e24590078001d1305002050001d0150006100c089001d407100003981c0c003c941d81e80e80b504420100d038102103003000d0741c2003208016a03801b04048005036030440e05030850340943c0b600c480d0b59210548500100010b204000504011000050220744001500004000ca402c11464440d201c1103020810b55418482c83d1500260424001004450b901d50400c400c88009010035081d8450030f640c5020720b09c40380b480200d42080203c0c00b4041410f034403001d42a40305406060800c540e07400d04004e25076610b07051240d0705680b0380b0b40c3c0000554150308905450b0b00140304045985036011818061141d2a040300c0910005140000009a075040003503210302030410310019910b420308002c01140d0408a0060940501000300005000a401080344080c40301c1140c409244e094140784403002035031a1150300c004c495011085001c1c0001010600e030003115070014a030050a0f0592410750f0b6036207102c035841103505250002440503484c0050090248110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 878453516 1250 878452266 878452313
    0x1614010b010c120818070608010609171b06160812060907050403030f110a0302100c110606040209011106090c01140423030102130b091005070503030a051e0103 70
    0xc41400440300070050410141440c044801612840c81c05440c0d6180c110340c0d03100c00c982d4054505101d0340d04d00b0302c9a0b4400d80008403140010801075910510030350241990420800542c00d080d8501c0c1e59a8140000482804500380c160345456500c03d012151400610764001080c0030150900c041da40d0090706170b10525880e00e20008080e031405c046424030640003522500c0c1058196102181c170503004101180c1804607242d00d40c42925010800c204966200ba8000c1c441e030a1543c0a40068915001200c02449804060075400100104441d42e103e10140c60050b181e0416100403240440101c00b010014041d400520084060100d03224030488002c1c0ca803002c4c07481558042c54145d10583c41040000d56200c0090016290001041003004000800141c10014211285101120326070b00c040c0321008000351200d840e00340200701990701d111604066080414503110152a44001000402c03080e641740002000c01e0300c1d400420405a000004003419903840e80391512009204c1305003900c0655 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 878454766 1250 878453516 878453531
    0x3160305071a0103030c1202070b070f1a0108030406030f06090608060106031103060607060e01140a06031104050c0405090405102d0506010504090f0207051912020c090c0c03161401 79
    0x4254074041c43c101d96141e41c0d00c0240c48013a4030b403aa0001c4006040354214002c0e454005088a01900035124480c06a0034008402c94645081d00c8070384070114210802030442e9004205810011003560200c0d00075060121300e12a02d000900c0081039242c0004a40031706d0150003042e011000140b0070f050351020384042020206524010141d40821154503502c08010000c06000030859004440185180d00010413012000e40140640310740c2154a149015a0340c42c08005010a44180500303c0c64269000c000d14101400d00005610070742c05150301450406000c1004c12108016504029801c3c0400b00032604401000d030140505403401030010800000e0f0301e544d4400c4510502c0d00500d016120985014075051040b00a03005215000b840c69900307011050109070b00784806841456002c2c0700e14941100b9142c24451041d038038100c50219400003821b0442e54450b9415a0342148110381c105894090304030410740b40d07114400e51402100c120b10510820040742521528021200c034000b03003d0740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 878456016 1250 878454766 878454803
    0x60e070809060709050321070c150207061b06050c0f070b060405061c031202070c0f052b0b1021021309020f04020906041208031f06050306120316030507 67
    0x12415801106ea1581003181029824081c0241d269801c5402554a500300307251b5840c0c0003540543c0d0340c00b001c03110080260304841c4650600100c40584628104059030001e0f610b00140e021800c04801843c1c603a403074001c01d10800b0310106403544459110921582d450b96450a001c0a0304251181809641080d01041e003c3c80e00400a4000f000c4100b10340902180ca51421248024a031484030100d6500f00b06203404640a2005007014003048010b0003001d501d004207100c1c5100e52110300703200d1407500c12113a101144100c80302c0c509494001c24407070820b44030603c0e45100c0f40c0c41540200714074080311800c00030501241980c120310a000300c40340e2105000044694042e10f4a0101c001d6014190041c04405403400d80c2c040d005501000e0002c0b403c0c00c0d01e40301000c101098a21050781c80e005c002c410850000c052071010034511400c58032019150740745c01c0026009000103020f16218604440301042040000c100740c6000201600c9050095807544c24090700700d9022034020342c1c4120020040b036104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 878457266 1250 878456016 878456027
    0x5100804020127080118020a0e0c1b1221010501230706110301060504090515060901030507022d120c0304060f0e09010e0a18170c01060e0708090607 65
    0x2580d0180c580e0400e8002000c1c07580c0c0e00703420034406050f480028140102e0301c2d20091140c032010500ca003c113228001524010005a00110b42c1f010030400301500030880d0702002c035800c3c0c808041d040c0684281c4500c0100109060022229107511100c00202d1480040c3da10710002d89034451241180759520b90b280d50046030004459940600e0340c220054009007100003c800600740f07103002e4078000403002e14030705071294103a00a92046002503030114003440b64458910a003a00304407000e040200144080d008122a80280000281410340e250002880240244401d08000034105208611010080e04d1907004000e4040261521700c04c0300410305c0442512000c65801c4142d5800942c01d103841c0a80c01c43d40c07071516410030f07000c20882d285000400d49424103001d029082600d141062840d101031403500b140d40f80008524141410350306080491b50000150503110102102240d40b90351188459024001030381c042c01d00c5000c44000c00482039480100c0b02d00030b041c2401078550b19182d00c00100d41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 878458516 1250 878457266 878457271
    0x60b030105041e030e060408030a08010b0c0c0105090f04090b07120b0913020d05010c0815040504030c113001050105191e0b0a02010b01030f061208030402010e0d0309051008 76
    0x2540340b501c4402c0442d8800040b0720a0001e1192404442d90909030006c180e0b140c0056100034001ea00c003180d4481c809030000000740c007508070300380082d003894009647d041e81c0d2919900d515042c40b40c00a03989050340c65070a0750702a400c40250003030240c10107034541101030440c01c40c0d540001807001d0360010700c104000c1c0102c210b4640b00038207082c41074650012485078103900d050b0490344140d0444d00e80300015030038007925040c4080c45c3c680080030b1604982c4501e440024500b0140304901d003004000c0040d4204c50f00708015600f000c00a209800c0d40d1000c50398000b9000c0304407900ba181600192600740b1403071607242c50312034010002d1000b40d070b854050004000361f6042c0c9441b80010b40c4024480d0802d140720000909107102086050035030b03a01585031855025142c5800140d4640301c5140565030540501d04006040c0b0204000b19440c250300604503922143c8024100d01c000001f08056a00c2020f410312600340c010055070404501d4613003d441700300c083c0b0406000b000c840103204141c50140d0389092 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 878459766 1250 878458516 878458523
    0xc121701051302070212150a14072a0606030218060607110a0509010e0f010e01050d020609041407120c0201020703141e1605010b0925090308070f060b03010504 70
    0x24164282000c11800502c0c0c000ea441010f0350901800000d6690640744200c81c0d4075040142c44010341404191000c10780042c001d10302103040044540ca00144044030380d9004d51540780c801c5041c1c903000a06022107084e0041418031030281d01499007841320950290301128401c03038203200460411400305110000c211030321a03204009000d400007040c100e40c1030075144140203080d0001d03035440d440046c2404000781c21254801c00e504081100c010407181245014141c60700e17160f0b0140d890180040da52519010700240210400314540e03200d51295004034443e5103805031406c03c86d1412070001040849990007040e103140c00c00d4603c4a4803070040c8200d458654156413048100c0040d840003a603640e0005541c444048407811840504028802c0074241c0708001000550b402212800c003103080d15000c403001c0e841480c200d0180070703003c00741114001c1d0815001030410b110148001c030544002c480c59001500d0b402001801c401007004131080b0000c1e00313100304401c0054118150a1600721001214002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 878461016 1250 878459766 878459807
    0x30305100f080d200d050f04050a090504110904050606010c170a0c260412051006091b020f19031101090501020d1404034404030e060a02030f03060f100c12 68
    0x64041c3c0d125000a0587d248082010752609680b80081241605a5031000c0e0402e42c8d24000d120402206501d06032040c1c10445401c55581415200c503511580003a189505108003007505d50200860146142c01d41254205e01c40e440b1020b692002e40038410541d0126803140040b40c410a12040d44a0380082c07060003040c00314105404c00320030700e40c4a580420f05541c07510403030b0582c1c0300084150041602030880c40350049010190348001107100c410b030f00020403e540114540d1402c40500160410444081400845025032a400c1c1900e00341d0140c800e030007265003003140b10001d020b0150010410410752503010410010005c030a489083c0d0705440c002c000860481c0d101100b13003502d000c00b004901c00040c00144003440c000340040c0e1403140414841d44c082d00d900420040c036400c4968031004600607640e4910744240e048000303459115500849256080100100d4100c3d1100401d152906c032000d808500d42403003041018140b0700501d6000c48501c202210040304140c400e1001d01c0700c2c41d8a84c12340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 878462266 1250 878461016 878461033
    0x1b050c121f200a1d0a050d0f02040b101202030a0605190612050601020a15060801060315050105030303271e1501081b1c0249030305100f080d20 63
    0x108030444444c480540e44151210710105082e83d9000b202e041d00c9116a030f440003149810b1040c013090300d007500784c544c0c072842018050302c0d041d1f50000380b004850242d031100169a9941d04100328000c02c081c5d04500c1d0811101e00c0c16008510145005c0c40988034281c0f038110201c1b050048150982c0c20449a0600681080c41e1410029404180300004044883d8021551a8403140800e00311a404d40c01600c1031041d2140e950b0005203e4820240584800e8001d1840c52070a40100030380410b420340c0110b01190400c43d005203c18041c0450545440b11043c220066842030004030750700c040718540303201c003961f0020000800b15400034007841241d08900e0400040320204c1c0400a21000b50281c081d0001ca242401d0070040e607403c01e040b680c1340100c40b41d68024042403040c40000e0308407170009c1d04805085201a49460076102c01c40c000c2c90f5030500d0081410766030070304011583e900d80e5110300c610180c0328601080214000c12801c008030026914200c100c00d5841811503041000d103e8544a44c100b18038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 878463516 1250 878462266 878462297
    0x6040f060c0302071e0612020408190501110d0207050c0406030510020c03160c15090303080c0d1409030c0d050304232505011b050c121f200a 62
    0x1460203541d030007030050320100c96440302c000b103000a18624904084001202c2030241e180c0100580513054207001c411400c20342480c021580d1002891244041380c00020300f0720003045025007180c6d881540d40081070b038448130461700603000782d001410201d9450140d095400224149407107150b08503a0032038020180325215a401d0402035014010860090008001d000040716104404500103442040c0c41e5482030300c1e0103940b03103400144403884c44c1001401c02080011a5001c00c6d09034120f05a42c4500b650395400110b181d00030080c021394800300203c02030404ca894a4088090f000e40c004079010b942c1e041c4d00100341114140300c11100241040d407800403b12107c049070301003001001d80c00d01220340c0c2000c485002003006400d0144c6602e00310722590184081d5038031088c07040e010301141d1400c841f039400e00e03942e40741c07500030340d0940e45c1c086d001407500707100c0c210020000c1020b8440c0c00c903100c2120641e44c103407940140188104030681c4003620301c0703941d03e00040746046910804d10743c1c9e22150003139013410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 878464766 1250 878463516 878463527
    0x270601030507291815180127150f020f0624132f160501090209042409020105180a05040e0f0c010203070c0e15090106120506060f1c0f0e03030a0b06040f06 68
    0x500d19038840380100c184000b00381080341040505462700c40760801c16840003000700110090105801190000c0581c0c09401100041260b0004002d080ea10741c46010b0103103038440040b0402c0300c1907110701030090003403208285a00807200c90b4a0544c246c000680480f112000441000c03002602949041024502010310b2600010b0120f102e0310000c07072581c0840d000691000390030b9070142d032005004040803011100c401000d41e07415441082c1032000071882d4001030040e000d81c2c205e43c00c520402c81d40031881503480c00400c0f00034080060040042003880040e0340e95aa0720b0b03088804051040781241d03e030720b43c00081517403505a0300220a80180d410b2886440c15440068200e103030040c48140d1100082d81c80d18046400b81c000380c1d582c080c00d070601001c40c005503080944a1070050f0401c100c40404045424110350194050f42c03c0c6801401c111403c190003080344650f0116078510304008103080c07040200046008004218050128880307400800c01d02e0700c1948110600020500c40802501c1d0152 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 878466016 1250 878464766 878464787
    0x11040807030f0f0b0c0d0501060e061207180b071506030809060f0f0a27180c09080102040b2101050d0609050a05062706010305072918151801 62
    0x1000c040107580075a60f684848408160380c0240c5004011070f8581b489204c40c81040c0c010046031401e44482c0382c42c1000b003151440f41321850240718891000162000e0300a145005031529030b420800d903415601e001010f56504201000c13980c044060102c030f0400f403460700a03071044d00c0d00b00c415586400c5080f000c00038564041002e01f0400318040c0308000c01d01c1c0560020b407011001607240e483c90b014402c8209608211035a0301401642c00b80030061010450700700d094110b103080000d0000f06000c172400103807410465039010080d590b00004020441c14841006000d480180c1e90040400e805c0e40c174140c032400701003401850303003104158070344902040480d00300464141c010803e44250390b45a4031000c0c18864119591003071147c4641600c0d0388034142d42c04401c0310603a003001801c4194115514640c84620922903d14412182060500500310210307100848446ca20601540c1c0e0000c00084442201c126006a01c2840d038058101391030001c0d00110b6801c0c507140c488882d02c2d941014015a11100003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 878467266 1250 878466016 878466023
    0x30301080f013e040e040b13031d031617010c0927180506060a08160e1b0a02060609070f05071704050d0303020c010b010c0b04031b12030209030111040807030f 70
    0x3c00c1e826280d800000740100050651041c614116283c14100003010039409420721000d00d528101c01404698400906907212141c801c0c07022605112070006071805620a00140762001c0740e00000410103000c10f6541c0102c1b195030000e2040c078211940989181c000ca1050108401c0903502d02614010481700400440003441030000b940d40c19500204081c10411804075600c0e4802d0003845058900b03005c0f61001044030000500b03806000c040b041d41c400200d84240300c8090028000f14503035001005400002c48040040c0c0e07622882c0e2800000c2d5258010b48507107000d0260b00002c5041c99114590700c01d221140303500c900e85810101d60300e680e0b140140c1000c9400c080003e020100362035a6800e12140f03401c1c000d41d80940c4075000329080702e00319011041034a05000e80824490300007402e407140554440e03014104403180003600200911941c0310721034014124101c81d04460a40c6405034040c000f14a4180c000b0030541c400401e0b65900c0b80300398003640b0916800365070300b04002001d281822050b81e12 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 878468516 1250 878467266 878467361
    0x5060901061101060b0309010c02070923060f040513030e010810030b060d08040f030b1302030c010813020a03061d0d1209050309040f02070b3403020c0f030301080f01 73
    0x1d45d60155085074006649001560b51a170b20003c0e8166810012803001d0700383c0940c10401011051903101409034110742800800080070b000a003143d44d1480404015200070b4020300071460240c0340c40c07070700a204240490201d15032a2485a5039481882c000d0b12454401e1b07094040181503846e201c400a10050403107900a03404423030103000840800281004020303604251561300c4c1146400c0f002e5800060500003420002d140c4040075960016410041d88402e007007548594960306007050700b12140f100d020350000e01030780000003000f2792940b0010260840c00200008402044103042d00e82c0342042d0110300040d4000d011450400480c3d002410040c030410444e4500010000402e0a55004816018403140d0100d91102840300c0d640c11140d0101d24080d5020700e02985283c0d602508a420a8444000c0009030707005003524020703030455121880100071105082a20354480707070750b54401d00489095010340e504248040c01c05018050010100602c10405102c0691500c500c070f1032401c625500011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 878469766 1250 878468516 878468519
    0x806060d1503030918020f0711010207120b0a1419050606070b0406060f060c0b1f031b03110d2301060f0e0106090b0903210904060b0c100506090106110106 68
    0x2030925510703004511980358980c0c00b510381680c0c540b900d034290a41c10a00c600404c031200d11100e0720f008980d0310070381c050302d4007082d1035805004030310703010b0316070005141c1000307080c800020302201410b118490f003103280050000c401009030144008000f0355406c2d4030440800445c0302d503516180c101c25400b22025080380c2c01c2c000d040d200c113040c40c102540d041d64800c1d0f855a0a02c503400c0400c0d10f40d0082c02841c100903c51414a0ba0752081c1690300520781c0f2504a45609c1060340c0650040071003000b180c0010320710038a01400c005c142044a05480212284540d28205812a04250460949403500400a00940400a4500f0b1b904051a41c0820f180755030394800400c03800ca00300b0140016008210038170b84258186a00a0450314464204040d8000e00313100006641c0d40c0010a04000a81c003031516a1000c0d40303202ca83c00b03600941c0001e1358407a040402c00b1031401c0b400c002505422521100f15089404a01640e000b118010703210b0325001f02c2c01c0c500512203e401071142d40c5100c0040d500000704075 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 878471016 1250 878469766 878469791
    0x1514040e01231005030d080705030601050702060d0f060603050114010302182d010305010e0703180b0108010f0b0604060801030b070203040e04080910110607110f1005040b010e04030806060d 83
    0x901d4000901d001102c1c01c1c4240840e840d900040c49014100507002454032070010400035101c03060040c006402c200c80000013507070a034850700075240c00701d41c040c203000d1301c4410a101c190082c001290030170300003a02e03245001034450b22074082c450403610304c50300301c142c09041680114041e40c04030060300f044000c1300400e0011501e070711500085c454080340081402c00c0b6001c00d0351113412046120305040604080050200042004009400001c40e0034001600c3c0c01400c1ca240024120720001752101e01900000940b03000e040d00001401450030804202c03490001e4100101c6004502611000444c60070043c00020118005d107900b0041c50b00443c1d0500c4d91743d200c050310700c1c0011074040340c98900110f0810300d5030a00c02800000003201d801c0140c00d0491800b078a540e82c1130010b010b1002c000714283d0106880300d040c031030b8466120a54054443c28214103413401c02070902a00c0480c0c0c2c1e402c0a5000050303034855500942c0c05154913035650a901d03200c3c3c0d0304200964002c00b01ca80c003000da8809048202 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 878472266 1250 878471016 878471051
    0x2010c020a090c110a080d0509100c21090503030105040b13050103050c0906040e150a110d0b0a0b0724390905060702060a09080f010902041514040e01 66
    0x14004220042002c0c0e03d40a0000c200900070b0440c42d04a40c0042d54420005400304142e81d58691500f80010700e80c3ea43c1c940d601d00d0701c680c82c5071104501d45001140040554443c0092000500000e40e8034005280020380c141200d1010801805941040c001846585419001116030314002451094401b82004860301118403e03841111941e101304c4000c102c40c00c040e0001daa105008481c20005108200e4400d41c8944401d400d05495501b01400501c521000b41c1c00801584041d214290302c1d5803600203007070002c204c43d850040c4654001c020000d10700000204680f55194044440110300381c21359192818a502601c9000d090b5131206201055810840c2d8800078084c0c0300303c0780901114600445015000c00b5400d140d042000046e028085a2a005c1c210303010380341e05580569490070101c104a6501480ea00000c100340503041f0218140703101508403940450080b50200504001c0034001800d00e00d0038410003400d03640c24202043d0601d070540c040a2000304000c004586600300c4000c0c80c24 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 878473516 1250 878472266 878472269
    0x50604060809060109020747010f0b030c0f03191103040209010b0c03070f020f1002161508160c08131e0e163b10120902010c020a 57
    0xe58400420445110810030f4500420440d80d0841c546440c1c0d840d0360320442c0c1c5070741c2c41d02c00380b690078103484a444003100c82c43c600c05800142c010801300c13a50720b252a5072348400c1c410340c40b800b00504c80114034550b01c4c40c2240e000d40500c41c0d0b81480c24903140f48200031600000c0c481d1f560403070f4040340702503040c2290050100101e5081c42c1143c1c3d0f4901841000051a8103801060520030113010707010014a0010440d004960000c50384c516190f090300c000b0b040c56000c0c0003019044800c1101100a032600040c0403c1507000d4081130005140e25510f80008900724109610300080180020500341d42019005550100321440d00c00c0d82094a501c0c0d1600551104000ca107050000301c1081001441c00030102c0c44448081401d41c0c40c8529200c02400034040c040d0401c4038045440c80e001803650f02945000010ba29018490141c503240f031184040100c0d585e1700300540c2844440480041381c070f030160905035080100d444005043c009814050014001048220f06010034114054003580d1411185030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 878474766 1250 878473516 878473529
    0x50f010614120c2409130b0310090c0506091906020304060e0603011214100f1a01020118031d121b0d031707090b03090d02240f060406050604 62
    0x1030050900188080030710b0349420302c0b040d50843c4044040c0e0360360301d4020400140d18000c2032a44410700c00c0d007056840c0b00d0f0449035903200305400701c1c0d00940c503a00c1d08403005030401101510744600c41c403040f1030141c46403120024102c0d1481c1c0e006010a20b80304020f410240c1d0007503c90400305107840e40f51509400c2c0e035041800981c2c8040340030803005d50302103204444030409503411819035260052401d01c08201c008002c000d08402003025070b480f14204440d121000d4503a80c103128403540c03541040020840d00c11100b0115802881100017940140520000c0f10b548024901c0c00c410b181e00d085401c641050a40e2403010803140303004005640d0350741c0e1010b110320400007411461aa541403003184501c180100c034042c0d41034203402808250030408800f07480203407400c00001960381000440310400940c10805034144007000788002840700255010359082070fa021600d000c00010f0f1036410f54006045024110b100728000511a40944254980c118901420208419444000040c42ea800503003144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 878476016 1250 878474766 878474789
    0x140304110a12030504170a120302070b0609060303070210120c0e100e03031b0a021e10020106050325030c080a060b01080714211905010b030c04060c050f0106 69
    0x10310841c9041460900182201950300c2040e1109507009461405144100c101c040f0000b10540071900c0180b054200a0794801003512041e401008098002c4d081941e068461004101c0000c5145c1000c41c0320034000c410090003582000903e40c20000010324882e181401c01541500004802070240a1008c03418a80d4a0b1491901368032018080c2e48000c241c0c0503001c00c408620414404e850110850320050300342c809010300309c00098900c4d032800341a5100250000c10800a62550104440b1581c800c980c003241c843c0700d019003100d4102c1c244d0f60f142c010154140c1140d101407100c11021010401c22a11012001c0c941c00c0d52a181d002c1400741582c8540001c2c0c010301e40002c10440c041c0303c0e1080000003428800d01c0360800360b800070010702154500044002001542c1c203504941c0d42401c00080740700000d40107452030041003207800ca181c100340c105489400c040010510078080000d07030f480b81c2d218500c628100742c136044040b104151054000d40d168015000c0c076402455081c010040901130241d00c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 878477266 1250 878476016 878476043
    0x30b0a0e1905071115061513081b1309080a0509040b100503060112050f070f1107030623010b03040210051c020a1e0906050c031612020d05041a0a140304 67
    0x18a0505480b83d0340100080d00e4817082004a40d1020f40011300400c110429680364420f880e442c400500244d00840410302c106801c00504030407402e4003100404003038075084003117010081d2050a85d0005200281901400c0c03004c0703003040d0302c80c501400c0c8198006001280205003080428800c004410080c8001035000081060786d507044000000d2205c3c180b0002c0159250450b9542d4281c007010f070988040054800e074012072309226045846d442d03011102038030031450340e916008008161400180d000c1c0f0b0b412000450a203059101d07041d0489e00d68403080e81c0b65076141c1d403c00c078500c0e03c802c0c040d100b8040140f10311400705078620980d0117223101c400801a0750304c104200290a00c450b410001e02c2d030500d102d00c1da048469110402c06c0446229047c401d0721549000111340c21805810740504102000002110a200584811080c844136507000d980000b052004215402d100d035000d10100301c0c949070a405520a2008028480e0f03c0091500060118099501c0f5855900c02d480a1380d001c00741089c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 878478516 1250 878477266 878477297
    0x90b0a0b071112030a0c030c060204091401030b1810090602072f0f130506120d120f05040c06051303060e0606041d1011040f0303090905010501030b0a0e190507 70
    0x38003d07078100030b440096041041e014002443c00d05032000c0142005400312000c030030042a0f806a6018186164040c0520301e24908100c111600900c000c0d08c4225440c0045038100300111216010312602c00098070300b000c0f00f4200240502900341c000c8852543c200704200200b5040b10054408136843c100500b41c84081594544001d1910744120b40328000703107100300f03442e95182140d158080e041c40801040c581c0e6540001481035200702e2140405015414040341042c1d4060302c408c0c2ca0180a180801100a100e0041000c8600c1200e0040c1b505500034010701010707010300060088008040380c1c1c0c0048649a40e5000e083d280275203038000d0300303902143c148085403915016880300180c40c820655951070f900740d24543e0307400d90f4240a249140c1d481440250b148144170844001d81000e20304d228881d07640340740003040c1804900c40c56048034507000c00447d5962007401964034588004090310802c0307040240a1049000107015150b280e41e0403401c3c8020181c05018a9201d2801900d40c1d1940994040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 878479766 1250 878478516 878478529
    0x2032a191a0a02010b06190804060b090a020a091a030c0c0c03100903170408091e040e03070209070e060703081306060306020a020c180c090d0b040f1218090b0a0b0711 73
    0x101820706c00d0f60188260124016180c07014a1025440d14145905445c4ca080c0b40c0c00621100a145401a405004024546015030020480c07105150b954408a660b28038900c00c440269141000511a042000c1030b02c00303101c54060541d8012000544c1c51108000c40082d1030050401800700c245a140c0c41008107058001c1820031030001d5048d0304a41c01d10305607803010602c5c41260000f511481da001c5284600039605841e88080c410702030320800490b00c4507030000341d0b02c0c0c1001c40124850800c80b00003803e050b114412031800540301810341d03401d002090f0750a0b103021070010b16480e00606010401c0340820340600076900218010300d001665800100070080c00c14100d00030003030041d0312010007040490003000c0c9841d44001a440c1007920b03100fa400010742042500080585104025414042030100361418a0610f902c10040c00d0b0901c400a00140c03440e8254440300580010103070703802c01203a1466000f04980e032600400f407082ea9601d50051441c1e940101034295003008418509a85605100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 878481016 1250 878479766 878479781
    0x90c0e090a020a170706270b07050c241b0a06060321120c03060e04050313150e09040c1d101a032409010603020702032a191a0a0201 58
    0x40c2c1c1d204c00a4264041300ca0341d508072440b5070380422500f0414140d0020346040b180c241d518a0442a401559443c9a14081c64000c100c1c02e0b140c07402010000000e901d0054144c6042c01000d54480000000030104044990451304070036031400c2c0d01203440245100d003441000300117071040344005100d034103508010306001410300d0711441240813080b00340c030082c3c0c020b681503104c0301c0400c5000c40e2032000c0103000c502904143c0c2c040c4510040b0441808200800071020745401c0d0140d0550480081c1d40b800d1804261200008620205244111076103c81c00d211011031340c031902070100c6240041e651010081c007000900415904a0009800d000c2e0702440307104600000c11003041c1c294044050080d4070300c820720001d0b08100320000281c1200500c4a25503402c40501d210040290f5443e60f5181d10240c0654040b2408034031901400164034070030081c0703246001c1140e001c9403a001c004010007091005280182c1005418003000000000c0c0240316110f00d1400906485109512034462040c06803d68001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 878482266 1250 878481016 878481029
    0x102070803090a110f0604120507151e05030c12040302011407020309030106050a050922080a050d0f060b041206020c0d020c0909070617070512150f0604120303090c0e090a020a 77
    0x1703e1002d40655130390002034406550b043c0000000309500b07803800c20301e807584581c4214240c60030480510941e94201800c6042000e0b050b03102103020308005402c48140c4422501c0042c2c1c2c020074402d8010b050301410346031303501c1031090000044d100c8242d0702d44102403204031040e00041e8400a01425641400c0c040c510081100750303118030302d0a0601000540d44c00005100003a40c03030700610a0040f40100b2928004071507000711000750340780040c0c0c50003030455101c102000c15450412800c2c1c009a60b0902c140c50845074041c070002d00f0300342040219090502c00741000c3c1c0b0040d409001c0c01744003c005000c542c10640d00e50b001020701e01c00b48814000ca00c0382c020040100f6070030046040180e0340d00a2400e4440c00c842030740390112540c4542041c0da4900452030f60740c40440740300d41049514851030446030503441040f10303582d60301401c0004104192056000703026051419220060010f40a5048809164481c521001c02180c850030100702a6204449403c0c0c25441040c0140c25400d29242c00e4024005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 878483516 1250 878482266 878482279
    0xf020d06140121150207050a0f0804173405040e010f0c020d0f0c0305042c061c0b1003021002010204090506010e0f0108060a0b270102030910110102070803090a11 71
    0x195504c407801e0002075480c41d00d0300c96800090403000c011050260041c1c45070300114111001102e41054640c940060161548654098183d60000f500008803d021040d008801450082c1c0413042d034030300c9a49001080030852031001000c141a5110f0180f00c140d000703864000111103150940b040c0540300c3c1c0e070349a0700c155080801c0d0402c0384c9902c036803000c01010b12424881e81400e03840c0350448552099612080350758003081d400c2140c50010000c00c0441c0c0ba6004643e03000d0b502e641d02007050380040307460710340c1c04940d1503d010030006114455a56021103001c0c0088101e541c0d94003c1038411881c0111580142d60004041c02a41464418280c00c020203181a4a00342450408074244000c0485000e06103c90310001840c85d5903400c15240107880910382564460314200c0c8039030500e5031001c2064161080160258020f544004155624020020614044152080d00a85002c0e9044c1c4035400301355020004403003c6440500114019521003004101c16015418a003440a0428441c14892503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 878484766 1250 878483516 878483579
    0x906062a08040e061c05010b0405090f100e0f010e030309070f0e0601031a030106081f0c05190203040302041a0111010c0806011b0f0f021504050105070f020d061401 72
    0x54081c0251415240c40910381980c80c2c035401d0020380c1818540524850709108084c0c0d800820806403c5074211003c299070610080e1180f015094031740c001080c1c2554158880750900b45022103d4020442c1120881c2c02d44800f5040c103148282582c004060284c550340c000018408501d074100b120704020426661920002c1e81000805000e0081c003400c914100740d1141d108041058554801542000780180208080e40d640c0118a8a594540f500700e603408141d042c825460100e10f004006a1710f0440d034409203401001550702d00b040d8540c403810710840c40248008001600c5510034001085480c6a40300703513407200c000004003040c50070f040e4001d6603418503e9183c21960040c1516070002c009080038107072201d010201c90b413801c803004006402c081e10030f1407036003c1c451149850508030740291050009140b0a01c0d8201c0c4070712442c4540350004e81c0812200c408950710680391000c1500c010410440100b0585401e000e0b075903011a90328049840030010009114075a400800d02440d510041702e070300303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 878486016 1250 878484766 878484773
    0xc120503010b0d0e011d07051c050a0b040804030b0708100618050609043e120103080f1903050919020108010306181211061b0904150906062a 62
    0x902805500f505615156481c80000540030341040e11105101e0f20440034190700901038541d100540d100e0640100b004111805151340c985611481c1690028010700900a580c0e65518040780018030a0f9403203401800007000080003036950071700500d190740da817003000d00b1706414410050300c00350f10200030b0100404034200c40d03c2c1c203000c0304c00c11541c085851035100c505002c0070501070a4104a19900c51454206451180401203008210030b5079100c601c2c040c14800303000c00d40e1140f09001151685070450001040003440800c010440700d401d0b500c055080407000031131015030302c441e18902008641c43d20704004409a04002c105003101ca00e48520180b00d01540018040300c03010300002d0101901c0711800c0700204074450a0356040ca5102c1001c00c3c0d00711280c0070003094000400c0b44c0030030b1030040c1d502107440070076510460180c03101000c2c4000e180002c032004000c01450f84204940c0b0480480313100040000d4141f04107001084503032035001005a12503d5103554101c3c00c02e4105a070100000981d020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 878487266 1250 878486016 878486039
    0xf150503061504020d02130305010c030506240706020301080a030e0619050904020708040e0f090304050f0111010605191a310306020a0309050610080607030b01110d0c12050301 77
    0x30404884120007014030040118019108801551070792034000a80e1f03607100a003c01c1c00c01c00326400764008021042c00b001084050fa42e041e19216880703804544c1200030b03075141c000301a9004c50b541840c0d514004c0980c1d901410fa0300240d00c2214550821a901c209140e0403d1080c6080308045407900e1a00e1160707005000c611440400d400200300c0d01060414840d1160b90484404035049408030341c4aa580b026600951002162120840341e402000b08503001c80000c01e9500340c0b04020a800590403030f003001103c85000c1c1d151407820540d01c5920000702078482280300e5406007003d0403c2d2503410304102850744806010000c6414030356003000038400804220080201d4401440035920740071120140c81d081e00c020540020b004907200240c95000b02d03030164401e691040c0300f0425943c2582e5170020302400191107100f04d402c07580003400061400c91083d030010008200504100c0400b02c2c88007034451400c00e0001d2080702081a081d914424004803d540708540c40c01807074181d2075036050144c000f05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 878488516 1250 878487266 878487271
    0x302030301170a170c0f01090b0601031e0f1b05130e06010c05031303150b01120b060c031824090904080909100e070905220b12010f15050306 62
    0x1500b045180804000c1c201031001d00c1400d90050050140d40c0c0030070311014040d502c600c40d0b40c2140c2c49544104c141c01c1c80c06010361800320b0307044100750610340d848200640140421840300484144111802c0e11000480d20500c03a00707070b107207031000110b02c000c00b9200c48019544070860307014004240080280c403034035010090140c1d41c40c14408155511041e006903002c031034544009101c0c2c040458240c25289608401b44100da018000342066030a802c2100f008503000c5e061014001040c909651110f4003c0f50441d600c0441c010b030101f0f02e0010504462425900041c070600320b070410f910203000b0203151101d09966080850300f00121a00c0841c803203440740f403040b144018003454a00c400141071151800958015420260402c50300d46011224a15a10031034040c214400e0a00030100340c60510410420040d40c0c4045d01d031900d020003501980c401281c400181d100810b031140c03113881a6444900314480b501c0e0200b400890815040100041910844a0182400d10005508109584e40001c2194 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 878489766 1250 878488516 878488529
    0xf06210206030a1d060411100f02031204140d03150b1912090c0e07030f0b060a05071106070b0405010e060402130c1404080a061103040804030206030a020418091e0302030301 76
    0x1c00036040c0421a16a0840004c01c44580c052281000148410603901c16480001104d005000d6803060000707441007040c844101005030b00500ca45401581c1c80754005401501030740c2d110a5058010b0310151801e006110701c60300194654000704428003441d04904080d0800c080c0c87c0e800e1180b503c4003d841e9400856014040064200e0440b40345885a80090813480d0441c034541002c80d191041d80d5902003050f82c021001a00c0c0417206103100c13000d841464410403001f440300b807a11007080d10407079441d0440e080a50721120520b6100f1000d17078030035000b0b1480d24030860400100c2c0c6840d0800d01c0c00c40c2e003a00201c610300d070008010400103950300415400c00205500000625201c514402c072200d0103040c43c0e40140b004001000b003500c030360018049210521440d000c0c80101c83c010703000c42c0140404e07180281003040c2032009100600d0301034003131644006a00700050074181c1e951401e8a480c5d6506803004245540d41c904131003031002d10022040c1c0403c2413840d9984441850380e00030b6484c40140700d1038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 878491016 1250 878489766 878489771
    0xd02030f0706090b0c0a170106020714011101020c06190504170313201e13020705120301180c08060a150509031005010821120a090203010f06210206030a 67
    0x1c820420903a002822154029000f4440c41c43d0140003141a580442e00c4200412603401c85440c001c400040c4042c107840040c0d01805801e480d20b0242089094175064642c1401540e00c1501040cad002403014050400c0c0810044c0702e50704000e264603107442d1300000000400d508000801c804a202824503017136000314407010342d503280d07624913499201c2d182c03040e8001c0081c5240802180105442d521602009904491000c0c180d0340220342d008da006d50b090103030703504016490519a00560340354081c00c0d0301741c011416507420950a4210158a620903084551058542d0342003000403144d611078656585000c0c1426422410201c001584801940c49000c612000e0070988400142c0b16000395112120050100e440c41c500c00901140075040c00d00600486100d44201e500400d5003404224031042c40088d5200c0c41e22580403203400a020300209240c030081d40314003d00005807170900c0740d1840c0e107620b40d900007402401c0044c159024081440a1101803440c28020300c0540c0e10103084036003080212100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 878492266 1250 878491016 878491027
    0xc1803081c0b030a0308040b0c1206040c02070503060c0406170603030922020a0e0f01020c0907121d03070b011505040b03100e0903040306060e0f040b07020c030102041401020f0d02030f 81
    0x545002d0030b07403912401e80500031034813240100764200c4901030056200d0404840d07195220f0858003001c0c000c000d08908140c10100108103a802c0c00d61029a44031400d00c159540f480e21040840d2a09205450030801454000390420030301d80d0001081c4040d681005040c07406003071120003e036507801a42c5096125625018111800009807507452070300c82c00300002591503d400ca0303000751081d85e503100c6140c09105561407410640d8808211641801d00c000c2140146458070300049804031140142508042c0e52100c07045000852620b04190941d03002d00116030390516441d0034040c00c0c0c01070340940a00040fa0a02d40c490b01c0c0c20200b610156044912020b440755260b0062900c0141e0035885080520303405414000c802c8004001041034a00807901803211036640c95200000388401c8442018440318800800d0019010941854219400344115020b111503500041d007280d2150340b00c0f4100c3c01a014406a4030350301400450301d809002e00140c10110b003040c102035242c0c4100303c0b201180020002c0ca = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 878493516 1250 878492266 878492317
    0xa0b090f04140109051f06050a05030601030813050402030a02073003150e2703030c0405040c03200306010e060702030a0303020a0912114b12010c180308 67
    0x2050113600d822500b00d40300c50180d0742015540701010500400c3d40f5041c01c0c008105030900018203400c450b0054014981c1e81c1c40c50320780c00400e03000301c100a03c07a91144480021345503280d001550007102c00800040c0e4940709450405c0c01c0400c80c070602540f149400c080d00350f200e42c00c49150440e00c04542000310724460344030000c0192031683e802c11a1421444014801001107003003181002c40018400c16950b15100444560340307000440d04255080400c0000b8003481c08c0c550803010100c40c1d2420046240449902c513984610085080c013945250b0110810410f580c1c08034401c80a09070941b08940b50950b03a03000b00382c8540514a010f82856000102900070b10b118440250003001008a01c8035880154549000f4510422840314441c1c2c0308004031503440521210204811012200800406110f0007035081815900d10481140d140d071544070700e4005d4681d1030141501180c00e500000781c4100c00e00c40a041e0640300c0c08400f0031041411001c0c400a00200c0c1203416407036000010041c100aa0407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 878494766 1250 878493516 878493521
    0x80114010c060e0c0306011a0a05130b0a1205220602031f06051e0a1b03021009080403140d171504110a030f0b01020a0f02060f030702060a0b090f041401 67
    0xc0d0000c0a0503e8606082c0003000003203040004810110140c4500740d0341c0e03c8004000305d582c2d00c03000415030303010442446160700134001480d8412002d81101c3d1080c0c0e44a000c0d88081e0070541e42c03540410380051050f54108114803915521580891980740c5203401c200303810072005400c1c600100042d034000003240700c020b030503011445002440034001e080c080c0c5412000300395411203c0420990010a00070900c008498070648920811598031a06250034012001080f00d01b4054150158014001c00301850700c02030044226250268088aa407249035281c944402a100408140c5a4026010120351140e0040201d0100646100400d610fa00d8443c0b07024241254240d40035881403420070040250035205000d805156111b0301c0400c0307401180c000440c10303595035140d050b0040e00291404000280000c0c0e04203003103400a0030b400c1c20812005017400d480c2e402510340d02e01581c000c0c010422072101038080c5410004054500251504060b0391240d0000009070008040c1540c00321005c0e02e1325401d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 878496016 1250 878494766 878494787
    0x1091101080712053d1508070c150c0509091f270515040e0a05030a03020d06030f0501060e0a02040503030922060e091e0303060103050403020709050103080409140708011401 76
    0x401ea28003106851000e881851540d80204121500e61994001106940213248003a21b12540d10343d10344039540c100e8101c84500390010300311110001c0e07862012107542c0074840d152108c803082d214181d80704410030801010341c034010300c9000c040d000c440030400b840701d41c24034640403540c41e46403c00382c0103803030680c9400c001e81d0000e544070050714210030002009040440c0d01c0c200081078408003c000c041c6c8544507203403d4010303009851680104003141c40e41c4d109500600654013008d4000a01948075503038680f44d0426a64260b820303a445000178000744650b503074000e8000e003c1c179004510346407500c80426201d00a204896110b802c0d03000c68000e26500040c810f1060000c01201006542e0302c65629145251050720141c445106800242c64050780001c40d01e2400c02d44c5000071400c41d900c01004402070580184202c0440c00390060001e0015480d00545000c0d61080c1e111a03121420065284107c405031798504840c804980284000182c10000181c15145d24601440d07103105401c1c0181d80400d1305c5d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 878497266 1250 878496016 878496061
    0x120306170a1211150109060e0601020a231203040c050d052a04021b0607031e09170a1e0509060711040e030f040e2d07030f06080109110108071205 64
    0x808107503000d0603104d0701015060341e6850500b0080179459101900718403200f15101030250b801204010080b949074904403040e40501c02030300058030100d104081c20002c0c4990300005040010090200b0800110a8240503150a4a0b0008204d01544490b81da904405d501e0348d1001c81103803602d040346000c0506141001e00c0241080d503072498260310f04552207541003012040340c081c0c000800e0101c2e00c203000381045503680168410b402c003403041020340101100c42e41110034804000b40118600c0e000320142180b40b026840f0342c1d07120640008501821243c101248041240c01c21203074015540e00419181180d82104210362002c1c0b5034004180202100000315509120100750000c0c03404040e40200180c41e2182e8141200b03844101e032606402e00000340040c0140064400c0c5440c000b21110340070303070100c0303d03180c003041400d03c40c050390085400c542c02140c039a0f515886902d003401408680000460001e00e0000042d1030b0801c402060190100603146142e40c5803000b060740c0705090088c071800e8664 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 878498516 1250 878497266 878497273
    0x2030a03030c18170d0f120506040603021005031617070f091721031302100c020402130501171501030f060e0f010e0f0618061903120306170a1211 64
    0x80300c0350300c1c88124a8061180d803140c424a0200d10000c0c2c460312040e40a81d0700c1f0303110702d081d480c4030316800700250500030001d540082e0f0342c4000002598641181d00241d51058440e03036582e0070300f1426500c1001c01e580b521018041c080102102484041d039044d82d10500350710700b005255000700d00c2110811026801400010f80303651214400c12030205d401908004502c40340740c00c410303980e1403400c41c40c00212143c400f0300d8007944890016003407424840b04c20080f0742c038120008801d140e0000341240c00c1883e80000103565072005000650300440106080607141c1d5804100c0d00c2c03c92005901c0558001c0c42e02d04041d2146c0250344020f4040d0044c0000e8001803108a4140c580102d9242c03e00784244a1006180600d1002c43e1150080c180b80c40e018560107850540c16031410045000303541c401410b2907400042141d02c1003605001d40c6004800340d03105452010400c05580c00c010191801034015040000c480b080444800d04009804c40f01070360302c110081c84c0303504051004e8401d854061039003581d600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 878499766 1250 878498516 878498519
    0xd050c09091608061302101b060c272907080d0b120c0f0a0e0a050403030506010f08131b06030f0c0302070b151302121e0402030a03030c18 61
    0x1078003090b121206074001000c2100d65903104a0181ea666042e190b9013881d1110b000382d0b0003d42008203240d1008103c504103103440c20301c890458080590f41e607400b502c0300d5a48040b410340702ea910260780c01001d00700400c014600c07044000d01005401c403c0c4545451403000c400c414140000c68842c0d01d03401e5403504440c64940d071090510406076031082c03590081952900a1200c900d240c400b9000d2a58a4110020720016000c0400d114070044100007041d0321442e00c05001648091b1406a42c0c0302d802c0403400450141028540a410340c0c0c0b01520480c148946004c0d01c095041e8804842d941c400507031200841045039600b0705030342d01c0e0309440f2940001414031001050799600340c0c001d00c01004424004000000309010101c04900a131900104450f0303118012540f01806d10f5080ca03482e5000a081d410010320108043c0103da00101c0262880d4240404001600c4491000e900c00c25000c0c00034482c8074030700380e400079881d00b01001009041c035949802c0401d40340d1180d41d030f9400e29400400d8840106 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 878501016 1250 878499766 878499781
    0x1050406260c0612010e01050a0b030103080a140a02031c0b131a0301090b0f010e1605030402012109020a050f150c0115030f12021204090209010c021806031501030f020d050c09 77
    0x50006d01540540b015400c0002401c1d040c540031000444100851150660b400c691b40c280d016845600d41804008400d104c48142d0175a1400502c10a0400d400850b40c1c0c06030504d450030002a010702e82a10507188c202d0b201c00d07030344079540805020b607501e00001812140b00041e002c2c0c8034030800c500f55019860401b040b4100901100318500921204c8001052aa6545200300300080100c42d20724a068221003131140c114040c2c0050b5800c02d205040500c000170045200c00010760034440740180703e546031240f800950402d04595805040c0c2030790920300c45031003c00854040000700081c1a43c4440c006800c00090100f940402084103c0312544060a90341c0d0904c04407821081400341c8201c034201c01c448a0207400065000034007052420602c0c05e10703260403040d10081d0403050b001418050020303081801641c40d0301d08190020105030141e00705082c9601410300d4840f0ba4601040491444001440481c480243c00d2907035641c103c0c0c02c0606802d8910301103007054511050603400000311030a10440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 878502266 1250 878501016 878501047
    0x602040303111c0806120609030319020c06010e130602070606062601060e01090e0c0a0e031218040603150e10091e0804051c03020601050406260c06 65
    0x4607402940c90a85100e00b00403500e40b10b20f40e035060082c070826920800384140d4004c0e40d90b16031104008000784202c0c4918415103091820031510110030f50400000c0084020400c04011401d0304030303c03001c5003004609092195078210601844019a6271400010343ca0b002c1000703000b000d1071b800380096407200114908000544141c0c010180420311103020001c17181003541c6404044006e0b032418002c50b13441c0c510181d500c5802e840b05141000040240410100d1044810314001c01030700b042503581d03403900b040003880c0c080c0154407140f19400c1050004188081141910300203500707004032460300443c080c0001d008041aa10003041c1d0000300002ea0311000c4940c0c060f45036001074800362600303000703854011005c40d041418000d180c2c5010b11102c07005207202c405020340300c1d88a411150f1915464500041079942001212010500c44503104020543d0510100c1d004142c20758040c41001c0c2450002c0031030340c02d1414010106401d000702c07454401c00821030341d5158000038103920380c3c3da011807491260 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 878503516 1250 878502266 878502269
    0x150b10170109020c0316110307030c0311090103120e1f02101a0d06090f0c030506100b0a050910120f02070b060a0308090112110a1e030902010f0311070609060204 71
    0xc00120400002900714614021101d10060f010060340c5007401c40040d503003003201c0309041540c4040c2541740020f6907407010480f4002950062034005c0c489865842c2c902d5002d0550036800380660346803401040002d075010980328680f100380c02c00c07071544402031001c00c4040403101d2078001c07403104420070151455004540a010704010750030034808581d5030100c07440325a030007100144c0c00c0b0780070b1000c41c001726a4581c0200883c2e8400c1c50b000c0500d4800381c550700d26500080d0001d48258000109000e081c80c06507120b080100b1102e5482802c19680d42c00150082c0101d2190a00030020741a030b407014544581c00881f1000e480041c06c0001582e240b40540c000d421900c421100340101d10049101450980825403c8951010445103402c0e500c40044441070740000b0f01458807511003201240100e200009440e45020503515510341000c8a40342800d030480502c1060141403501c4221809070344e10403002550400d2a007070105016150307501e0310f200d80c4207403c00a00392601c1c0220b40420003005400400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 878504766 1250 878503516 878503547
    0xc062d1207080f150102031804090501020f1b0705030a02010e040e0f030415051c09020a0e0415050106030513170c07080715081311060c030c0106030606080c03030304150b10 76
    0xf081c03941da003801485030f4046030107403c1c050b9005210040401030107030701000308550040c00100781001c1c5582e8460a981165010340b241c18004940320101002c074040c0504a02605e0004041051400000c80d407552049003000e41003100ca00e4140e4459111500400c0044000004450401900b51110b0740c4a41050003a0104078580c0c1ba65500c00318031170b400390360000a060300c0030b03c24540d0100410004101c108801c03600010b084a00042c03100d185030070a4400c0f4041d0300890703204035000250384100c4038140c2088003450f103014184020b03002c00200c03054009900c0111100722074035402140149002b02200e00c83c46224014003c01c2c88240420a401140c11884811035066041c5d4000c3c1c0341e805049905403640007600021002003100d0240c03080110078060520381c42d03d60420341081c190360000b800c01d5140d030744400301002001290311604005201c0e400103098900f02180000ba200c4c80090300103002008209011140c1b81240d60000303640b140700504902541e110703030341e015007514400704019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 878506016 1250 878504766 878504791
    0x3100611070f050f2103030106180b0703080703020c1609110301061b0206040911030603060a052211090f0a270f1703090703050c062d120708 62
    0x1240d862000288080c2038401050b2001d0790b8900b402c0610070b41040b0049010740c081c2c1003c016003510301001c4108651035080c0c401a60392981000005000d0f0400b001c00c0910b08000e82104000500001c0b054480c115410718000101d0307240c100b01180030740180103662206001e8641c420100c0c0d58076040f45001c035256034000744010b030050300200c0d07543c0c0070911410011a01008030349030006126045211014030041409041c80d07200c100d440200c6a05e0418140d2482d4004280001c1e85020000e2aa01440e020000d01c1a841c0c0a054140140344284003c80e20640312210042040310f039a80409821138094900240e03440d00741411000100c0680da00b0b88850301e05105910300000b862809150007198001d0030710301010a542e04070207141e6200096442810101d401d50448601500075802805000003d003003017810350074001e052002c0c10014600c185c0007040948642d008481840da140c0c02c06541c000300241840c0d00f031420903c40c00f032204171642c104404001056402561850240300140c2c1c81 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 878507266 1250 878506016 878506037
    0x3020c03010b0d030507050a0501020d02030103022409060c0106090504030233060d031101050405010605030111041d07110316031106070206010e0705130f030b100e01090203060411031006 82
    0x50600300c0b89840003080d007000d42540c422022138081c4004101c0244184100c030a2518691981422038100c40039204145400000410c01c0d840c000840744010b0001d00c5010601012001c203e0038148605035045004000c085000844501c007944140010805000c040c40740b464280390003515800d60130603400603081d11403c0e20a01904001d64020480c070620a520000d440700000c21040608040c42242081200d500d01009070310203015050003140320b10000b2071030504081c101401e4542e01400d25280010034401000003c030030902a008001030b110b0101119180d42d182103c035413204000941142c4400100014000350b1215a030401c940641c0da04102d0308041401503803500010303a801c000591041c0c0050000150b00301d031964021b180d43c00c00629003145106034405d48a06984000024840c4980410501c014800c09542c441003081020213403c1c2099170003044103c0c18007031560000d60210000e14607843d103500141140511045441d201e203454500503000e0340d42e0f4010f040018841040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 878508516 1250 878507266 878507269
    0x20310061107030b010501182c01061d040207020a0e130b0f016c050a031107031403070302010b060906040306050430081006170a0b060406090303020c 66
    0x600307105882e8045100e104c10392030003004440c1105a5004440c0c5210318510000d0009071081c400000002d6028040d03c0a28025507054031405050744000280000012941c1d81d05c00c0401c0e0040048004076401070b101c4000c0d0000c03601504080c3c104480035800501030082403240d69800c40c08031845095984c10b9595000002005010217100e40c1c02c8107080100e11024501c600c0c01500031940c4400c500c01403c1c0c1c00c01480041c26424584214100d51102020a003a8201192000132802100c8000068100543d540d0b503170b242c2080c000901080741008070100400f2083c0324000003580c001d50b505290001c09501240c8907840f00b14202c01542c070309100140c140c2402819240c44100040c071203410702e403941e02c0e0100605802801205c40e00c0401c4101c14480103102c05488041c04c00c10400c5004100840b0007801720000034145255005550320f00f0050244d0144099080110360350368603180d502c809554a02074984096059488040820007040b4681d00900e8107080342d0103a0b00715028002041c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 878509766 1250 878508516 878508523
    0x204060c0f02031c11011a03120a1404090605090703091e03030902060708070215070b0103030f020c030a051623010e030f010203011d0601030c0207090c11010203100611 74
    0x11889020030409190325000c1072211020545140c00075080d6070714850b240002c006000072840c12040030940150381484104424400d9001001d8403500d014080305d0701c140040c0d43c1c1d100e41101862000000104c8003a400c0c8643c14104c250481c400146803525101d80c0200e001d055580070300c41c081d240e08400101d01a10074000d170211a50420107801d910b800c1d00c2c02c5c15521450551090b001e05881d840300d000141c0b11340e0020840c59000790941d0b44c403208c441c41000007695050448204071801484044040b4652051550450ba450300703000232405698423040e42440c100d0700d0301c075a00d80160010481407107400b0803026282006205004400b6271a50b01900010800b4003009414901c074101102c1154082c90154013070304c0c4010225804805005001400c3e40e00903000394400403582101c4100c5082110081078005409003003e128416482c2c000954500b003901c50044502c2c0c403031107501c100038001c0c25291001e86101009558138508101c004010050070f00ca0000090018103040d0500170010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 878511016 1250 878509766 878509769
    0x903021c0917370803010f080601051f0c020a0b03040f05010506010306030c0e0601020c0901030c03110d030e010e011b0c08071d0a05071e020d1e090314070914190204 73
    0x1040f00704a001c0802c2c41c2d00c49401c00740e6800115200b0859907400400c002001843c0282142d07002100564104a250307810580c044c0e0049000d0206003003020140020215150064a0145002c101d900e0f8075000045405009a020403012100001804280820311102c04003480c01a0000e015a45410004400b01c6400784000350280703c0c0c42e60280314580c0b0407900140c00100510403640300c41028400202992003e038400ca60114145000300108500141483c00c12a400c0f60b000d0302c50616510090040703d0f1a02a82e030411015105840042e0301030010303039154083c283c0d005030380d070441d503d85104841064000c8083c0c510400f03000107130a00314101e001000750b68120000c80c0c1901c030340d0410b5000d040003420a60600060310a60600b002c07480b0503880c80060203030300400d8139a040d2031001c0e00800190041b0703c03117401c00305601c0c1c034030640000241c0100c0c1d80c400c0c0000c2c640d0300c0d24000f035814840c040d00110305d01f5050001c1d0207400013100d0419170040c00c19640642c0c10383c2c070200c0d030102203115a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 878512266 1250 878511016 878511043
    0x209010801150e060d06051c1103030301180f0617070503061302151318020403151415030c0613031202150f07020a050604080a110a080d0903021c0917 66
    0x40c00b064030f01e203081180140c0311881a0100200c0c049441d5400180050034035004080c958030309103007040500c1005041400c12460a6010390f03d95410040c002071004000520014100e032100b09000b00407032607a216034014a40402003e200141500e038190301c031000c9100340d43c8288200c1000c21070004c60301e01c102040b558010300211042c0e0510041080d1a081320b00e41c080ca4071459003000480d130003500101c17016901118001a521425807801544500314883c1854800d86081414484020f41c6120750780c01c8040c1072042030340310304001c00207840c08014500582e04128046002e0041641c02517004e400d680c45080d82202d0150214012682c40100843d0071a642d6107080108042100320f110868001d0864415101050841e84460345010b00680e8115841080020501c00d4154400da0b085d40400c0360700701410103c003103034842400b075000b4040c080e401e0580e40c0000d101058001c118082070640d41440550041c3c401d544041c20120359803082914840206154511200c00450a800c44124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 878513516 1250 878512266 878512277
    0x3080a060509150f032419020702180a02040b1b0c1f080c040806072109150f02090a0806061503041a060a0803040f051203030c1602180406020901080115 67
    0x882c1d00400070310130745030b01206405000b4035015041030054a03104421002c6952003040f841c2c01d02c00040002082d041000712503651051250b440181e0300e004513010140301101030b01c4a40c0e202d400c0030000034852540041003e00c80010b4110440d00b01400d03022b814000301e026280f0342162001404511601030114121080d40100c02c510f847e80a1484950000508486907044c551210035052800c4404d6a9410218146814041d24200b2103043c0400610042d141030049243c0f5030780e180f00003100d8040f000e0289072680000c1204030081e5059811162004244892072039641088507211041510414020b1440901d40000c01440e04110b9024650000c0c034416461782145291017000c2c400f900044d40400004000107142d40b081020300050018200b038003c1c42403808081121006000b0110020394000f441006440c3c4c40700001e50b81c903040702e4046015501400d2002074800c005100004050400040911045c88041d40c0a000313001c40c00e8880c0340469886104424954980281c010000346 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 878514766 1250 878513516 878513551
    0x19030609050702150408030901020d0c03200c0d0806060c160303030f14010902071b150215040503120903090315010617010515090d02040c0c031806090302041805070303080a060509 79
    0x3501ca2004682c49010301c230006040c40d044803515001d8607898003020300080d0300d58100184449200c01001d1032030410300c091030700d00900c01c12030036119198111500c01380084140000d0080e2501d0341283d110410400a440504900da024050b030307a07400740025000030b49040840f100806040c811080120702c28a5107401d40da181c200307400c0c060740c00003000710b03030104105031800c07100b00036214418050030100c005100000400a0300a14016482860b2850070350444d00f40004103c0100c1224040e8480f142108050380e24030548524600c50740c44031a80622849211002c9112078202d4113041c1c503800e542c0d0b85180a0b03851002006140f0a029842d40040c0c004002c0440000203c024030141c00d0181c40d80c1e01c6440542c001030203c3e0141b2030b02e800072a041080c40340425620211812040e08400b400c20491420500010300c00103a50000a000c0c2da9156060898060203040ca001074070362140448403290727220315004005131001d883e440f032000d0402d54045402e203861801940f041010284001804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 878516016 1250 878514766 878514773
    0x80c1b0d0b0403180e1b0909040633050f04090507061209050f060a0b090f070c2d03090501050f0d020f13081609060e0a050c190306090507021504 64
    0x10304000e84110140301e007100d48135080c86881c9514100405602c41c0055561402841c1c80060020b4040c1003075200b1000c002200c4140c0c0c1c0d00d000c0c0c42c1c010341c02c150005032080d07140441060079803038500c0e03d151003480e186802c1120281502e011059900545d0780d506180c1103101448203840706160300070201e070050349040c4070700b51045020181414002070086001c3d0500d848950070300c1101e403640c1106400c20b50400500c6240ea0250041001c030a64241400b884c120b6900742c0c01000141c510000c0010b40007a64051141c905088007001c148603800b0b01040390150a9201c4d1501204c2040b404960700c200700281c0341d03026a0949450540030b80b6807a02d402c1000640030000d501c51030b105c1416170740c2404604c0c15000d04c400d54601400d504e000030300020902c3c4020f44130030012548030003e0242008401e000400c0355004440c0c01c815482e0020490f80c03202c0403140c0c160300032212090003219045840307840080d81500240125005103030108403549800108031388841640110380c4403121540c012170b000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 878517266 1250 878516016 878516033
    0x42405011b03120f060b0d0b10110a08030c1b0606010806040501060905040b03030d0519060812040902090d20120105010b0703050a090902120a0c030b01121512080c1b0d 74
    0x11044d251000a0f401e803222030141854001d54080740016503a80c10404003030500040c1008400a00d0a10b030054903010006690394240c0c40d44010901000800402d0002c0407c1041c0c44070303080c901c800c44111100c200403050b582d01c0122500b500081c142d50100c1c10600301880b81c05d051b903269035900c800d158103120621000d4000c100049030948400c1060441500f01485050301038060340400b1107001189070312070310542c0c134503400c003a085420400000030042d07141c4044404079421030f1740150715a50300340005164103620341e0014000c810740ba01c21250144800f148138040b0401101c1665415100094040c01c071502400340c00550b41041040d0030103c2d005a000d000040301c41d14244d00100d4035402c50a003640c1040307150388454840030741405488032090040614a031180d01d801c0080380c0302d07040000c102200607080c0c0c1500315650010320b241c40d40b20308181d101411040308400d958454915000d8050742c4000030b440101c1c0280c00c401108950900890181ea80000b03082d40e03580041900d07400349 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 878518516 1250 878517266 878517281
    0xc0d0305091504030501020a080f10051f0c0f0309090c1107030f0f080406020c01030b041503030806040e120310060f0c1b0905040c170a03120506042405011b0312 71
    0x8010b2418400007000690900003000500c4503030381da203001402c3c0744401e19a40403001d401c8070104008041c0500260310364003541003101444031446014082c8101c002e6071110380344000689885596803c110616402602483c100c80040030b082040e803155000403502d440c118840707070845070440c4400700042024441c07203501c03042c0100c406a004241c2a03480200c540d01c540d0109001d608080c410760541c0da0188110a15031405030750601100328800040918480c050000506000e10070300481e2050303c1d40d501c003440d6289120210385403518035004010303642d00300315451b1145241c0101e001c6651807252410240d0510030f0784601c081c0494039610340c00307800c048420840a0070722004c03002131201e280b4003c881c042e90194144490350b90800040000c00305102c07544020b20b6200f0340c01200040d6100100c1107a4000d00c98000403551140c0c40024051f1400c1200421000001c0d201610050a0320405408645090300c828010f120a9507540500d00f0801c00060b020440031603154048500b160000d01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 878519766 1250 878518516 878518549
    0x30b06030f041a01090b151810031b0201050406050117031204030327020a08210d0603080301170601050301180602130e0c0a17040c0302060a12060905090c0d030509 72
    0xf0000c0300704800c011100d0f1002d900c4440700c1901c6002c554018142000d000800400101c9024603101805c0000011a00e5500300c0b03901820f130f04442c0c0e1600c1446544030312078a1000300d45501d4841c6000200a020b400155010346240e45403000000710095403140c06052440c03000c001d0b608040703290b5803042d001c0e00300520560038513880301a039400100c01c941d2003000f4290741070f429103600501401440000705441e00449030650261742803920380d4000c1040303880c404048099807650386480c0c2c0310440103441c9951008002920100000c1001104141865031440d050800c0f52440c0e80e031182014282c2c1c0c040e224812403492880151004102103030014441c8a012902c00180e16a0f58441c1c1d0202c03e4044541a41070b81300820701d40441540801040d0300c032403500d80f040f40142081e4440084d8852180b0000f4400c02000500900141c003844403160f5051100c0c204104155440c40b4400c05010708071020350a1740900454104246051a09900c00a80558900741006440c10a200f229410b115546 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 878521016 1250 878519766 878519783
    0x80f0706090e0408071a010801050a0506090c090102010e010606030c140a0509041107021005091201090b070507231005060316090209060c102a050307030506060f0c0106050f01030b06030f04 83
    0x1170041140400b1646082c29140010900c9602d040d40ba03d0840d100a4040310106003841c0500c60360359034401c0e0f866007001102072241d0350760f0b42010040c0d0040c41079018000c1d0302c0d420310b00005107584d016070041c01d5640b01512041d460000c115111000707803041c0c411203400f050051080b0080d6040c542c0c04096003080342d00415240c5031860300042c410b188402004800900c0002d050394980c101050f81c2e02d058101d100c003d2000701403e9480c0f0381c400c01d0080c510070800c0000702d0b10700144840602c0503409400d0104407410341c401e500c900c840d00c801034000040900d03030606001c20034a0800040e0700e800880810010754045092945c0503008e94081c2c1d480b554010b0781401a01c0624201f481042642105080002090030050108110031280340c6031006603041c910f0b112030700458002040f203034070030b402e85000101d0340da41800040c00b82c019407410ac10185030128180603240c10550119041e588110381d2001c0c4558080c004601741d0351004005070b04404103001281403c030070017510a80091090307559 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 878522266 1250 878521016 878521027
    0x2030d0917030f01140a030206030a090302071a041a0c0d030c031e0b0310200a0315030b0a0b04020c0c060304020f1801060e1f0e030f070906080f0706090e0408 70
    0x100d00e560810f80e42404a40310b064010000c401000ca0140018081030b220b80f40c0d0780340b55400040c018040107090358500c0391200c11480c100761007801140045e10045e42c01403d421140c1101c015290081c0c020703008035100c08868241c3c1480c04c40296412144960000c0600028140307040f8007401e842d20080c01456210302a100a41c40701450148014064100010701d19030101d081501c4c01909070502c1040901d482405170909040480c202018404811311958400c4016400c500074550000040c14801c0078020101c01c0040d2801180d0180c4444d0105110416451080004900c030340309131032890768003c01200d4494203104c800740d0703442800149500c0710202c001010801d41640c445403402c2c183c80f5403005005d00c542007005406180710907502000010081c00701c142c114400c001d8010305100e0b11248413985580c0400009844000c603400f03a9034207560350803c806c050202405040c556000d03000e12001107081c0010803404503809587c5070200c462800500c15090350000d001540d00f079508000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 878523516 1250 878522266 878522303
    0x191202010c150b0f040507050717040803040e060405100e130c05030102041203090f050906151b0610290a090b070b010e0606070203150606090307080d0f050a02030d09 73
    0x142070302260880c0b000442d061480104100e441d680130900184618134003c14021010380c4041901c43c200c0d404003101da0790354903c4100005500030f550040c5014440014003241285400d06050f0290b0403e480902c1540c5a009041010965502480111101d0180006c90121110320301c580220300507021885480e485601003801da0303020350086104511011010004c159020102c0ca0041030f00c044c807141180d0608000460103400a0b2000c0d10418000c000b5020302c034908011941080c5441c452a10f458512411291b1642000c540b0f1140c0c0104520001a01c0d1055104103c4501460900c5840002020b0b18030145500801480c42c10403499410100300d4228800007800c02d075000c1c07203040055615040851030400e000521050041c20140300010058a0008402c1007181200c03c07a04031641d51324000c110756004a02e52a580740c4104580090458000318000c19080400da5680400844060341560148150851000103074030070085000c00469950048450a10804e05464295400003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 878524766 1250 878523516 878523533
    0x70308040303021509070b090612070e030721150b03070e040b06120d0c0816080309010b010e130b1c0506100602070f03020910030605040c14191202010c 67
    0x1002111400400a03060041c19010000b515001400349460941c0385800480d50782c40b01064800c00e4141c0720042188001036456409a844404200341c003e402ea02c0d02c032000400030005107007018000c1c0111308000c5407510300b80c0550104040c000d031014007190b446d80c0d120f801c20650301c17100c814425030701d682d5103030550340c00c0c08001d00401180450103858101814072030107001e000703082c041c412048000b2265400d0804580b10540f00c0c218100807140b1005400c0250132441003015151414444001000811098202550003004010000c006451401e801540d22540100e205c680c8a540d8900d00302d20740300306401250500c030340502a080142c800b03240381125120701e81c00c100d4081d04894104003502c010543e085000303003020710041106524081c0c10030440562800080d0140804800003003034000c03412422001142c0c030103030411030f070b1030136052080000131207000744451790280d911300489a10308519031032199214070070616440741c50a80400110403035404201d06014403044844041480031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 878526016 1250 878524766 878524769
    0x3030d0905031803210c150702160515090d060f020a0e010216030c17010207050f010e10200a0e10030b1011060a09021c110406090b010c030f0e0307 65
    0x5800850700e40d403c0100b06003504000403000d42c0a40c1c4031443c0f12041c1101c4a03e42580c0d00b810300b034026130320710250582504107501581340c140c0559100d800d0000c115400a60b0312000ca05010030612aa40c0343c10402c410544110020310500c1401c0c012008145003c510b2400c02074130450002640140c0c801c90001681c1251948802040a400248803075513018007101e140c521004a000e034441c0d04566955820948501070003840c17002844c040340144030254100d0704829040004c56000700c0007002c0083c06001c100c07122500c10700403040d000c40a034a09010b51500320301c0c1407400e941100c00c0b03a070203015070fa000032106030104000e400704507005440fa022109500d0007150382c08a8a505400280041900070403119003c001c0039201c0355608000205005402070152980030800b1001f40c00040d0501c00000e480790b005a074140304d920b00700078429424090f040400c0d84d040c004e4598556007401200c0401492a000c5017200074010002445a41e0000d000001c034141094001c404001207440d10515 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 878527266 1250 878526016 878526023
    0xb0403080f160f290f13150213150c0f02010c02061306020f0d1d030f06090f0607031802370819020120010207080a021020090f03030d09 60
    0x402c03d8030341c20701294189045055510941c00e4854030044460005404001040d0311001415940485c000701d000c080940140c2c0c1e00310300d002d032440d200c2c0300d0014000c1d80a018070740c8925481180004003001302c8110002481025102c040e0161141d481d03442e0f01c04d040350407c81c108490700c01d5007070050780c400303000d4030218520f8240d00031600d00b0302070043e1030118002070003e800c1c0d100c070b01c2001e0400d900c02c2c02e406400a00319840c00006007140c010910340040c5145078003040c0542da080221002002420011030700d0301c40300703c3da42600e40c58020303002c981200d070042076500411002d80015080c501950041d02c0411181c1c41c16800103042211130003004217008044200780c0c41020042c0920820015895400c00d400e40040c8441580c006805070121003482490704401e01c51034040e200d020343c11340f0342546c0c100141c40d0740d82c0d5003818000c0d12000b5185400510078030f070000154500030300c584540c020a41d61401c062801454200300854101c0c8140080c0d03051004000050b108603590017200c01c442d10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 878528516 1250 878527266 878527283
    0x90c0f040e011e0e011215020c0f03031b09010915020a350f09100516140f06040507170a021005040515090306010e1f0b1308070b0403080f16 62
    0x1c801401d041d45090f1a031051114110500040c0400350b000360705662071551040a4000e1102c0b10300c800c030040e0041d85084a2203000d0504c3c0c4e406108008001103109285403c0c00d440500e00c07a0342c141c5441d02466083c240004c3c00c82c0000d10003001015045031000d522401101c249005984e204003412902c05004846100c07c40002e002441540d400d0883c500380c003080341c500b0001d80500340004d501403030f610300348680c0031074900d80d030306901074402c5850854000c9a043c2102200c0e041481c0342c4007500e2441c8403c0d1160644441c10990003142c058055a8000c025080161034000c0d180c00b0311104c40881c0d04c050195a50f0140180e650010300310024103951030b000d0720b451412041011700113064880d04600c51007001480c0140d41c0c0422054151f690101c02c00b0000c4c0c91340600540424440c01c03901c1003054180b80082500318110000c0d00e00000c1c0f40148492441d00da0300d2458403024a0321510307038038001c04e01c0144001410200a1300440185910345414042041c608505401001106998090307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 878529766 1250 878528516 878528549
    0x3021201022a1903050c120c1207020a0b1908180a02120f010219030605220504140118060507090e04140a0c0b0a0905040e1f2d0c030902090c0f040e01 66
    0x520074841441c11f1049180c6580c1040075104000d07454400482c141c008078000081c100c0215610000010081c04c0b00c404900e40b129034190300910300c5c00781e000d000c40100e0702c1d000c000340c01c900000d1003850000741c4520141c29860501c1d420322452081006490456028514402841000c01d1016051015514044401d05a40490007404403031403030700081d0103540b0305030400b140260080e02c040044283e50000164980d910308120f415485101c4e510000c5500f4540c061021058242c9518209801142e00304065292080c0c16580482030388518078a817445c410000c0c01003031241140301d100d17030780c90320540b0b500e80403580d100c8586908030b410a0720350801c00300c1c4960701d03240d21a030080d02504007654104850070ad81201c1030b0740c0b0115003030102c1c00d106440409440c0f190b400d401c990650700102d13510707101c080d034418294022200c248480640341ca00d042c0c031207900c8078444d00a180a8a8010749500c90548442044400942c410500038443d442c080000003011452050844d000701514070354501c040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 878531016 1250 878529766 878529787
    0x409020a021509120304030810090f0504021908150c0c01050f1b03010b040902090f1f1b02010e0d0501060f0315140601051c0b09010f03021201022a190305 68
    0x59030083c22003100c2d588604a5611014120402c17250031a406090038013171075440c0e94501c040012584c024138461070520340c0368100f40d550b07600040d008920072620403040e5128014409840345151044c92004c1d40b0a212143e151040d0f03041c0c00380c111480d211a289403000d5100094255442a070340044c46411000421401000010452104500070003466207154034000c80c00b8828040c6009244100780d0000d00450140d0b00c245000c07401e0100508110804c4004000c21511603900f00da018012803c00d41c0c40904140c1d5008507100030aa058665181c4070614109204501c0e0504204035010340d80c501010840c2100c5c840300304021b40c8288070039162006511084401d50741c5820403031290030030b01018890140e8010040e1201103a82c0a4070070465003058103120301518444a0350390304101228004504000b007000044141c81c000d441e4075128648a0704628202c1c8114801001c00084104404003003c082c940829590064041201c83c0191001034403890482503041c104c2c0030513000035204040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 878532266 1250 878531016 878531053
    0x5070602060702010209010f030e0a0209041b060c0c1203110312180d080424050907050a08070f1802070204020d0b010e1203340f021309081804020409020a02 69
    0x4401c2c0762000f07500301135400001919441c0300384003400600d603d810282206c08000c10401c0c020300c0d00117000103031302d00f4141408085989891011442c00741e41d10340205005005010a110055001c85050ba6181c81c0104540f500d01054500300e081005403107045424010405c0030b40394904088841100504040c50b0510402000d03404c2510a03802075400c4800c41900b016441c1d5110b074200701103059070311194940051030300e6417180c00c03050725142c18140305d03502c04001843d0099031010740e00445841c0d1500c155503555009403092060203408400c1c107000e113140341d42d8000c11840b2041009802d0a40c070341d000400741c2c0c003c18603444440380d0780e07402114550381c0042c5100b14403070103442e460344109091100d07913241d101d040311203c00014890703611140c0f00d106540c5d0501031207044440e401108460b1900021111034100181e200c6c140072840d0030350304460707880ba10365030640c4195561b2510f0010000d03840d0004241002c15805a0b003400700042c14003081c00240400106076018101c45080902c02482 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 878533516 1250 878532266 878532271
    0xf030309160e0f04030e0a03140d050720060d1b03050105040c050a0c050c040c050a03060f06200f060c07020307090203060f060d0b060409090302011d120c0304030b040507060206 78
    0x1a1440312007402c100e51010480c078a90418001c0401c884280d98905098684007a0108101c5c0c001500b48000070511940e40b0509203014080406c0c1c510542031408202c2c3c140c050042c0c0170f403862142c80e022489102090200c03000002005c0c0ae09401d000c1016000720480317010700c2243d03031300e00080e0b01e0349030304140d0620800c3d014050403a0200001558500d000f0030f00c0c0125020541813142d1451220280300c020000c420240700004c10512058891550040094008000d090003190030000046203101c0c1c03981e50358094500b42d61311150010580b52000c041c44280300e035031307100d40d009000a41450072400d1101c10b2046902e889202e5680c009032061501d09020741e407180d003080d44180284100d55603903040a0072800300484140e501d03299219401401094213660207a4014000070700015082065004140f106020390020048698210100e8001c3c807110841664140c1003d119589000e0780d102c050b00b1034080f28422241003a49031754550540c0c00c81503038203032034a0740f00e80c90420041b80d040104a030b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 878534766 1250 878533516 878533543
    0x30601020d1e2601090b12010902220e2b0e100503060612190c0c02030d140933040f0b0a0e03030d0b090c0a1d0406080f030309 56
    0x52800000e0042d260b0300c090711580d04402c0200361200c01e4640f50b06404983c00000a0f280800c41d1943e540c0d070604000e0440d06d0701c807402454020300c450180340040c03043d9603c468000d009502c07044c81d030b0743c3c0d031b045164003010011030050b96441454960b02030800c0031a001780e40c40284a40014001d41d9a23115240c1054a04410015180603503011600c3c0e00098140d095003508160303480361140707000603409010300900568600710040030011084070101d4201c2c00c03140c2c101c034100210080c1a2045501411074080039405034000256410400e120381c800027110305c40040841d0070602c4040004000303161030207c80ca02c0c1c4040c4004e444030340c54054000784c040c00b56003102c3ca1925180880407c0e4050385440399400301c0700042801400365000303114450b9034078401401e0b83d6403040c0d440f00c0000101080641035000c1c04100c00042c10400e212400c6030340780780141c0c82d510281803850701c0c50b0382c1c80102702c101030350000d8468000003074412040007022003420108000d19202c0c80e000d001c080c60010180142d0303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 878536016 1250 878534766 878534777
    0x70c0b09011e0b03010b0319020a0b070b131509031e020610090e01023702190204090f05031908060901050604060302070c03021c060b0306040b161211030601020d 71
    0x4070080c2c0d0302c000a6010300a0b2504040390070390752100041d00401e99001600d406020741c0c042082450b410100d540807503442190030050064940341c0f4402107001e0001f00500500180003c10b85066076842c050006500c070700e1855003080c208c0c0c4000d03403c1e1400c804080300410b05001020391401009800b050181c800e51004001d18500b0044902c9148420f2060340c0f0b1055132501d101c60f03540b100f901240c8030501300840c01c0300d04100c946075038511070301340158040d140000400a4a0400d03c0810b0f1800d0891821801e411404084c2e001c01005002c1d0300400c952100e1441a03410000b0000e0000d0090700401030004000e040c4101d42c05810000004d000b544500042c02c010700490795503600303032400e07140d05180050f25405145008505224250006544100300d440c00380c1d00d01f2241905003e8a5100d0f010901000322081c081c15a250401d890050100156a000410f0000407480d00e1540e19400e1034040401c0c1030843c0003d080310103105681c504c1a0000003045401e5270100104030f0f20003007030b1414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 878537266 1250 878536016 878536031
    0x8030a090210111b030705240406050706140105060a03020f0706050103030503070809010504030519180801021306081012030c06020d0c08090a1a0c04090f0203010602160b0927070c0b0901 82
    0xc1c1c850440b4052248141c81d0360503080d60151940c46440d8070320302314030f40c115502d0ba00c4220140060f000204100d07001800d0001c850101c64015403242d04071038020b032140d414220702c1f41055003e50409402d1141791081403102901141c1e443c06418020b40c02911b9503582da00b0300c2c940c010040035006240d10140c0c2e042100380701c0026408021100140c80b0743c8880b0308410f006000032121040e241e8612140c1070702ea4840450103031b00650050100c3d851b2516518143d69544800b5030303044000700c03801d12104402060400003100c5440001c549a0303c6860000d920440e0b42d5607110403a080482c0042c516036991003c014120b4110b00c000c1d401400180c0242010005907542580c1c014421044900c1407800c04041100503140d001510054020207034103200110172001050003d40003441002c005202c0c0d100250110003046071440c060fa2429200d41e8606103003407081c0300841802c88584080b8944000814440302c6400b52880d020f6540c9a4411425a001e410210f45010b000b600155003070740742ca0710 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 878538516 1250 878537266 878537269
    0x13050916050f0f0405030a0b0f10120807020301021e03040c051f030f06080d08272a06070807050714030709051f15030606050f03010308030a090210111b 67
    0x50b118039003890003900c0d43da840d8500300040a07018960020b074051096050310000c01800200302c508c100703c0d441d25000e06580710002180864024800e41f01902c040c854900302160400009040745400a40054135140721003154203840002004c1c103a4003c003000c024042080345800c020380c010101182e0004c410240302c0c0080407400792580144041c142e03508030080f2900c04030f401880c0200700e00d40645036400c48654019041032000c86108212032210010240c03100b01c0719103001e05902d4a18010320455082d1195580451080c0101007440d0034000341038116991070000401425120380031a40c0c80c4c1c40c103880c00c946040015045101e901ca81040e50403540e840c005414402c48040744404a6140ca440721481d003d00c014800003001040000d101007210300e10450041005d552a0f5010002e0a03640c0408682d640103036901000000c008000400c013044954026540000081e000061080001e40c0000c03000300000c0d4507100410700c89020342d40840b40c2401000c01c6c000c0b501500413103e011010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 878539766 1250 878538516 878538527
    0x608010308040b07050c06030a0c0e090f1611060709090e150a0c030b280b1c0f15060f02150105030a020d2405060901090921030f0213050916 62
    0x50a6102d0f40d021525070140002001903005411003e0121596030900f9500c180152a6003003641d00416643c140c0c1103214101025110300c1151050010400f5454541941c651654805180341c201301c4402041450136000703100640c01801c0944603907006510708503404041d02d49200d900c004c1ca0308034203016456440c240071540c0e400b0341300c0107002500f0303100e445c0143d00900c40c0b40852500301d640184202c000000340b00c0440084407041040b010100c1d620b0346031350707200c0c0310b802804100100c400e40050780c40d4070305404c0a8105c0c0d1403900003090540200104c414040d00f180d029000251517223882d500c440760144814020f2985001c1e650b560b1303604090104e0354800c0c00c548000c2c003c80c0021441740a0000d40c0d52510b0003021401a141014008540010042c1c83c1c00e48416100e50351200000694482d070b40300700345903e5030042941c07560b03040d2080000341c2030394103c0c90042815112079031400c50803094401480c41404044660841c1411321003070040d1860020b10200302c25003050029900135400c81d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 878541016 1250 878539766 878539769
    0x9060f020d08012601020d1d0f0a02061305090a06061b021c08040f0e0f01060305060108040b0c0f0c0102190201020403051f0f050f07140324061e040609060801030804 73
    0x40110344020440e01403a0341c2c3d80e000310440d440c17544042484103c7c5c560719044641144420048070700c05000c140c5445407500c48200500041d584600d4608005007481030283c41401c4214800c03030f0300b180e0b4801c00300e03100350002c540c0c5011156450106002c0d55400c44e5008100a60071440c2c501c0d07003032950b4045441710525840e580d1002034520485410010076504440103045a4011000c0240d640d603072040107018203503050580f00c038015002050040c030902c5080e04c2004160b50b102c28584440d22402010360019101c041c0c6100304000c608005540b01c002401c005c0c4210b130005a807441003401d01d800e5084488603141c210b90040204001181c2d00040c00340100e2560413032148581b41451854000346008061541000d0400082051503141d0700c0c1c0080c031540c0161200b80034080c044002c0d00c0c2c5444222030a004200c4040c1401e43c1c03145c1924496040c0f4031000d00790700c0c689050407580c0d00c1e80e016802049008044001802d1020070350006401c4018445418102d12039415590b0f841c9050045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 878542266 1250 878541016 878541029
    0xa0e060c09010309050f0d02070e13150e0f120408011d030318010b130b0123030115030212090a05070801090506010e09010f060e1512060a020f07050d09060f020d0801 73
    0xa50444d8018450700740b20085007203400000312185044032090203915007000e4812400581800d00009071940030b0050704000d410f900c00d0940340305c184e04403110401060760444c0b00380b09110756801d49203076010800c20015017131a041401916113181c170104d2800d503251007028584010443c202801c0041d0000240c0b50400700e918a41d5891801d40c090302c03401819507072030b080d900540341c0000703a0420440754080180c0610130b9030740d40001103c0c0e0360718008205643c10f05107000b20f01080100001003e122580c1c44424652a0140c9444414608000700a070103032900304107500a8a9120104502000090020840b10700203100c004025211300b074031000144a001c90030554000003810098003984454a204d5204800300b00098940303070030f0b5505080440c0d20000700a1180311b03007465480d0004030841310403c0500101075a503904080040039401400111440440a21510001410034450740f24000074640c1c408030824a00a001814403000c417225005540002c1c0c80d1021440e400032186040d81c60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 878543516 1250 878542266 878542271
    0x1020f070f1719090501020f0a030809030f04140a064407090f052202090118030303020903010c0912170d0e010f0b0f0a090b04020910080a0e060c090103 67
    0x482d0404052262000b203880d88075010020b014044003040b0030742c0010a50b0265070380300c03540b612000160307520790407034034019201c5c0c1c421846040081e01c0703500915400092103007541d041c8001c0300a110110342050300315411a00f00c2030389400d410304088e41e0b804d0003041546000c03d03440c1c4c1501200480481c00c0940444943c14007500300082c84481a2076088100f141000c2400d40e00c1c00501c0240441c00a000d039018030800350b4000540c52510a801c070100344020036400c0080328140038110001d5000c105958140118881e4181c5410900c881c044005d5000341c40142c0d81d4240d02c0c08041c02c44000b003001c0c0e424046032500901030700d20b1a502d90440d199010030340f040a080b05030b82c0d040b170a000d080c01d0000321504114444454160641141c030894000c13071414880b0b4000780b400c020180c074007641d4041e0021441c80003042061002d030041141d50b80c024100618192090001c82c010704070105181d000b1800500a0000d128824030440200c0c00032a8050003031800d120390070404c00d214035200a0304058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 878544766 1250 878543516 878543543
    0x50a0227012f06010803131412010e030a0305071b0f02010309050f0a0213062d0503010501121103012705031b06010302011409060417010e0106062001020f07 69
    0x90181484194030780881540980105496404002010703410b08204103d0142100010f0028000400c0d0f40e80401900c0c21020028144902030104007540c014041d03103d44401c100d80c5d50290281715008a40c1040c01c041d40d0345039021031004d015510013900740710401c000503800488400d20603140c50500c80d4010880303030381e43c50a4001200500112071014200f0f0003018030b0708144200000304010a94800d07070710310320700d1030541111400b00c802902c11410b9200801074401520315214403800350700f0203896248010507403500040703400c4540903001180288402a1fa201c184050031440c9c3c5290075080703009102c45481da0303030300c46030780f1084103a03010040f40d92207603402c00c200050066540002020700291500808042020780c0c0703480a1100340d002c00c00ca241c5c040d5212690390104c9158100c0a040c5515051070212035060748a84410000101e5582d00f40517076104800303001da0402090a60303144400130440103400c1f462059081003003c03071688104009405400c148003518000d40c1c00030003402c03004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 878546016 1250 878544766 878544769
    0x114010804081b010506010908010b0d02010305070c240501210602210f1b0c07050904151b0210060608010b03061f030213050a030302031b07091e050a0227 68
    0x2400381e0640c008500c1006600e0343d40205055219512407039007660340e0113a069070340030b006d0300320b9807013112580e00048100710035800755000760040d0350040d01900e0f02e01d51192580d00c810413000d805081d00002d9030650b1320800624071a41c002c07140900480c2882040c007000e8aa02c41000164000c00105019008150044a0b28405400c004403050390400300079113180c4114900b5401c00200c822400750740d1008804d040f81d42500060b25840d42000c00100b0841341000c08200c980c1000420488007101c0000c000000c001c400d0091134040440035090004541d040749002e420460b00e42c940100c0207141030010890b0a6100d1207460450f810716080c695241c0310900420414944c521002d00c0151400001d115101d5240d401081c1c001d51a0782440200c41e00c0d4020009558058800500164424020509050450603500d907079400500102c5000503681d10300e07002a0f03030b0303440d104011940d60b140014078011164000c0a034000100b0008501e81074061803c000e6400300b0200c0030840c40e90150007040107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 878547266 1250 878546016 878546033
    0x30f0908030a05031006051908091e1c020f100b0406090c17060913110111071d0124050c0106080304031104151406070219080105010303080f0114010804 67
    0x5030400d10240c90369000310800280803a4800e07140820b084041400005034584504103403142504040b00441c00003103860310031551000090b101c00118080c4840d0342c2e40350b20040c05284840500395025003458100c803480010f04e081801000800c0d904500520b080071100807951030305046440000050301c03000440890700a00a80d0030600383c45141500c90b8580d41d401580e00c044102c080d52a45004e603444000340268900243c500780078000c000d070342c1000041c41008420070b003c44103250044228002003407640c07030a5140c1c0c1c01100840701ca240581c03440100c68100300d01400700c040c0c070165820101120540804000d581d0782c01001800f10702e20401c00021340091000b04240401caa4860742c17039040288044600c036241500c00c51500303411030600340d03514800c80300303d8101580700d4411020560510615503c400c1d000c90344807401d00c1e02008c1842c80c80c03820380b01030401100009160340c1103103070140004030050002c59060304e400004110070080103020300040802840c02e01003039225890691803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 878548516 1250 878547266 878547269
    0xa030c0504080f06010e01060c0309060309030e1504170f1203062103031510081909020d0605042310020f0408010e0a0209060d1a040f050a0f060c1704030f09 69
    0x2881d0043c240150722040e8000380040c140c034000240001107036600c0714203031100080518010081101c8560401905000340d204624a5000b400c000340e009a001c400903002d80c015203240555107002140c24020319080504150388603150340e000b007807000c140b43c0c0304c5070391003490403035a11050100100051058881580c5010200300151414418100c07051070140c50303810446d0001c010307200106058400e0300d05000004808119a2510049070701c410420108084500ca503c4488988905c0d00c18010303142c40301c0415200707000c1c2800140d80d04091800700400e070f00c1040100c02400c204540c2e4941c06801240f10140c0d201a20401030781c2d07541180800405000c4c40d849000a9464450403640101c004035100000c41c3c030846500c6801e40d43c44040000c15030080300d000d81742d11003c1003980b55209002015907085801040261006180c0fa5940d0340342000f581021510b251f09481c0d984200b011a0055090742c4c1002d0400d00725000c2035459489010310001c00107810011800801041503014105440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 878549766 1250 878548516 878548529
    0x310b060702042a08010303020d2a03140a0c020a080c09010b031f080f010609050112080f040305070f090c0f1202090a0b0415020f030c03040b0c01020d0204030b010302030c030f030a030c0504 83
    0xc038103d00d15809440008244029405802100000034219109840b02004e40e01100d00150243c44451607100d0307510054a0102e092021560842c1c141c130030014080c000342c403a90358400d42c0351980c40c4180034a14000d80d01100140d4400d900c2000c0c1580c1d54200c1905642d0080c0c500d54407035494801c0501407084000748012207425542c80803d4161020880390300c44c500c2c16009006443c2d0b03500d10349048236800d22440d44810400b14158002641c81d20090a520305034510a81c1842c1c3c4035111a8140601540448940205010100f0400d0348034056800b0b00d920f503003010460610b8000c1c0203008a244000e40701a640d50004261307409035240400b54001d0181015495211501c0f204180000c0307079550300d0301015202d405040100c400700042100c0082c031160000c2d604051500c031000301c4503000158a030f0300c00d54082c401106200003510280c4020750041071b250105514500502d401e09200399602070081e0401e4840b0006d19000000b240e28a01462400261104900c2c8080780d07a40141d40006 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 878551016 1250 878549766 878549831
    0x1f15030f1116080403151415091501031d030309070b03040302030406112d0f0f0d200a053304080a030608060f160f14090609310b06070204 61
    0x640c0b24006c0b6512400e02c0514401d83e10300203071a0115100b00800c50b001c0c1d120792181c6003c000030254802c0a0030050840f8040c10041030b54640c48908144d07071300035046a000c2c6607001200704115404100070f06801000a92070f00ca145042980b4020345034412401410140100d07010300000b412000c010610848010100c00c0c8141030100008480c0b558031002d070b604203446905140d14201c44081001e5001c00341c214028a80d0403400e940513114040d041d6400d02195039940e0910704094801d114494980c1d100740c000d00340300000c01c0110031682055600d010760401c0d1070700d040080c00e030341d2402e061b4006030041c006da41c840024050480190001c0c0d0803962050054009214240c9200c5a0301b0b80680110b800c1c01038411002c035400c5070804000c0c1e00000004441091100340c0c0c130100c60041c4102203000d0140c0f807a040c140c03030215504030444400900c21412905490701e05074520b00410126424440003801100c4458002440f18010480060b20a603551000c83d03444c003040c0c0e420060052440e6020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 878552266 1250 878551016 878551043
    0x1050f12090a02153f04110f03070b04050909010b0d0305070203060a02031303030921350708040c05091e090105090304051e1f0f0c08121f15030f1116080403 69
    0x911f840110b800f1820701811003131a40404524000c0b4100040d18001c142c1641030a141c5003c000082c00f000d0101c1029550321992b540d2543c03180c01c003080f2002d002c0e460f00c2d541d8451603c145860680000d01031156280305100b404205241c2224504125415181c08500412035040080c0c4864210303a00150054203844080d0043e030b000400d0b40d01a441c44001c2410202881c1b203040f504c1d024402d46030303150300700b0000010b05e00c60082109540240c02501026005c0d900c61020802001040c0c03030420780c601c50f8100d00550422005030a41d44040d00500030f1040d030a01c5000c5035500e011b0703030007458850343c440c4001d84400360001c50703038a644002c01081c0d07011480e8401e0020b816a80c040c000000060207180d22100d0843c041d030b04403011150712101c99803407c1603022004042d0b85002e41640d106003114011202d15008662900c00035120b0340c0600304055114503005800c070350680d40c0405482e8100700001c031403662128180d6111501e04805030312461400d15040c9918420b60b00000c110b440c40c1184d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 878553516 1250 878552266 878552273
    0x40c17010f0c0f12050720030903100228020c13021c0608070b0307080a0c020a02030a0303020d060e040c03060e07080d031a0d0f0201050f12090a02153f04 68
    0x540360a07643d107036250400c04155681c407000c1510300464040340400d013203200c0700c0b202d40c4844e4a110400003a410540b410528070714000307820480700c808000001d980100f00e2030110b20814500e03c1c408c018901049150404842000c4d442d81c101051191140480c0301c2200082070f825011103280305c3d45224050381f464001c0709904002c0070391b80031300516807150b54030104a0020000c21a40901802d85070824aa9201885040904130300d010040841c0160861400140c0f0100541d82c03041d803281d100541c17100c0c0e8020b03030082203034411f40c0191301e040c0c03c003014070000c2003100b40300905483d00140302040c030402c254100e47c030300001fa40c0814003d00c541603a08140d20b43c954040480000183c100b001c400e504181040051181104094a81810740d104440158001c030020322298820000035401c0c80701040070b141c2e01c18001c130b40c260101e410410040c0d0441c500f00c0144035044d11111042030034440b64410704041200101c451446415103d019503c01000c95043c5240c000342842c3c00780c0140c6054a03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 878554766 1250 878553516 878553527
    0x406080a0b07050301060507080f0913050a0c1b300207180204030305090d0204110c01090b07110316080d0c120b010302090d1506030f0f050c0603040c17010f0c 70
    0x500c2a91600c6082021075290b502c00e0084a0417035519503a428240032464440810030342c02619403600c8003008101c220600d803681d0100c8050f450200400095900c1c1a410010544581e0303c030b4030081001c101010000c400c2202024101c05070403444a1110031034005107142500704035500720340c0c4c501408506115540d400940e01d02500c0d490303500400400060b04d0038405034000c85c0070060103d00140889032403030034042c00c004000c44c00200040b480d0344440d10401e4042e0301060103481d069440d84600c0c8140080390000e2601301c2c0d400d00e07042400d046800581c80c0c5074012403e00c412204058126070b03090101207010783c3c0c900d000030f40c03040010b22a901d20141110210f61642c0b6540707824011442d155600a2090b00d00c44c00025240244240d040d9851003898517030312012030304450340c914010001ca034030740948071000c0f03214582c440300000c102d050662604203821141c1e88148010030800000a5401041c402241c40c00c6030a9044901c5045900740034003241d00c0c20803542031410242020196001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 878556016 1250 878554766 878554783
    0x9061b061503070506032e060e190308071407030b0c180a23030a0f050706120209030a0f0f0f121106090705060a0c05010e06010609090b01022a040608 66
    0x119a03040c1141c418141522065180724850317000c04103200080490304121416400d41ea9082c07450300c040c041203280e608890380c198000701d00090141c0c00303280d02c90924010018505008441e400e08462441c2d9a08005204058000304007207072800c03548035514020841c040140d80c0c410340408851400e1200c0600c0fa400c0402003c020b00340e90182c00303840c0d00b40980c1e9513041d181c0251003480c4e914425074881d404818031141c0d944e01407050042ca003001c05c0740c880010b43c2c0c291090024000041c9842402040480f01a181e0348581d4810000790380266000115100c4041e40001200340003101030074040c59404c3c1c46207000e4104219580302004100022809008032803154135030100c0140900c501983e43c00048406980c04d5209038003d102a00e81200541070000051600c520384d119039640302402c0d59005849144103600c0000103106654010f41c1c00b1003e0280c2d10340c1000001541c200003541e41d4011050a0b13282150000c4124080140b205190904030001d08140243c60f6502640c80e03440c01c02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 878557266 1250 878556016 878556031
    0x20f0a150506060307080c0c21040602060105060a09030b1b03100501030518062a0403060501050a3c080f071502010203070206040b1306290609030d0509061b06 70
    0x41c8400144030307241c48000c2e0317805803101d80d4a800ba2951101c0b45485a5440702d050799160784034603680c801c031003145c8030081130180c9407590101e80c486252440c068900201a00218132414050052070030840c0c0c414408811650400f47c803a525444042040c1e85c9030906900c50a204080002040040d0000d111a00100c0ba02aa4200140c0e69083c8600e2a400c6200050751980d800040c0416072045941000e00c0070500c494150640c100042c00e030340c1c0c0056009600450354240c55200400c0780b480c00c41e01e142c0041a805000c1c3ca048109402013821240c603881050017a480d10b41c44960601c010003e020002d800f0700011503000c1c0420710700050f070710309882c4641a4003082d080d44039500d0510600a070b038002c1d00382c0c2c3c005091903199951031601d0074400a10f404003001c040131410011401078004d00c0d0440341c00358030110600026000001480380c014980c1c038082c1e14100b000030b407503407400258000d0445080c5460380d2240c0c61000058020310407003041d00e10322030610039543c00d81c0002141d03d9024041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 878558516 1250 878557266 878557271
    0x7150608240705040b13090e0a14030306010c1218080307060605060c060c0d110313030f11060613060e0901240f05010806040e010c050a020111091c03020f0a15 70
    0x1ca46490210840c200ca8030000a00306100c10400191444060b144402d603020813101c10f80d86070b050071400c642c2044140c14140d40070f03402010900004c0c0400050724202c580207580b452070000006041d018440368010085030500c09207d010a10904a07120724144d419031004409586100c2c40d039403500302c0304041e2685032800d40300190074038202d02200d0001c01100045e00d540d80da85840303e00e040e0001c803001c2d03c000391075541c8044034690740801903114a03031200c20b00c5c1c004400b5080042101d00f01040e80e50600258807010910041c0000f0b459a014030116213412030341420100c604042d0001c0d600407180040081c0170f1124a09040d0400440380e003402d1400c066402820f00400c5882d04948a050300700d90a082e0140040d522800c134050f40700c4070191010540098005210f0f08464103a040c0c0e60002d04040354640d00d40e0b42c203000d45410f41010b80070003818a985007000a5004403400410290040c0300070310b0f8810107009005014954a550054818404850801640026426203103140030751 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 878559766 1250 878558516 878558563
    0x160201110a0b0103140f0f0a08030c040f080a06050c07050a11031005160f0215011a190801030b10030515070c050607020d02071d07080603070f08011b02120f07150608 73
    0x40c0050b2695544401f07000605182969442d0503c8551000d400740c40d030400100b00100780c0000700f00070007005003031410041c440400039060034403c07100040c1555032034803010000d807008120009103035100b40c1d4106c0e040d10380403203954002928003001000019901130404041014540480340318500300c160300e46981c25100c2480700c1c01ca80314910301101d4040318680034018080541400d0007a50f9820a640707800e840c21080040350010580b01411045c0026a070380b0050041010306000c490704494a00c10502c20b19096999181e250000540c5d09118040042c000607081e80c0b01e80c11281c030454120003983c0b002c1c1403e0785c00a44584655002c1d402500c00d1400010f16459481070406601e5442021f080042c1c84d08042216065800340c291685407103200404142d0b4042144088001c003404000000d1011700d0441001162900c0d06040382990001c1144103110640003048404108078425141d654480707514007480400102c000f800f076622300c1d210010030307014000039900c0c9007140038080d1144200c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 878561016 1250 878559766 878559793
    0x3041a0417190602092d01120e0307080903030904020a0815100509010302130807090c09080708071703070b0f0a1a01050406050906160b06090c160201110a0b010314 72
    0xd0b140003100900649106400c00049003444e806481615802031440c882c00903002c0300c00d50410041d10f425901e0001411400f600d540c0c1001c0010140d5901c4441400207901400c4141c0d100d01546101038401000000e95010380e5a0510450303045d0308005108544550000300000c0c0230010481d82c400c40c01c408003a00b0384aa00e0607265246011510b560b0301d902e840240f0004401a4101010210000402c1e21000c60220001e100a8015010301e00c3c0018280c03084d110700038000602540325101c103403c400380034003500c41701007013040070340e42d80385001000d55001c0d840462440c0701e65180030f482200c1c81001d07c0240b46208140c18064428190f041c0260081110403120002c40c003001d641c080340342008200981c502070800340c112500d008010320b05140103e01841e01042441408441c200d4258082204170f141c80c6501503003098404413401d007400f440180503901b10007800030180c1030104241e210b0018150400c1500701c031650005590f03240d940c0d28600301010006c0b25035440210300482c440ea0300391 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 878562266 1250 878561016 878561023
    0x6090c070b13113307020a0e04150c08251707021e06161b0609020409051f0c030c020601090c11030f040603060e04020904120203041a0417 61
    0x1900040c0300c0c14540c54411406507940000d402c1111074414158054000b035881030201c440003550f1000082090040307500d0340c005162050304a441001302848440003580301d100d030400070b564a981700d03411310b610365003000b005000a51100404240c2071041035510b07643e1100e0070074041c10000c8002c100ca032450058a5040178098490500050740c0400a80c41d160420207003240c0116060051350800210b4031109080519000d41c1c600ca190700100034010410442204d03a00f09581c18540640c450060881c0124034942c5642c002c0c0040b92107010360410b550f5641d201c1c0c00401e6020b0708441c0810740c4061000380b205c2c0010701c6039103810702d410140400103019000e0b040410302a0740c09002d45a003000c8801c0000d007243c1c4174076000c00c028180c0064040307008100030075400c01c1140307480b42c8031850040300406641e420341100d5901101c88007408016190400500d422580c00410102d00900399030049246006d65400603054031440c5004440e540d4081000b8429101e0180b0b01d404552240d500c0542d9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 878563516 1250 878562266 878562277
    0x170a0209010e0c030f060619031b0207030302100e15040b0415330f0e040c14010c030c0f06020a030209040506060a0c020907020109080f0c0d1e110c09040b06090c 71
    0x50081d081001590f0145c042040c03d0340f00034002c1400307050080c030504414054490624050119588452400050b285102172440120f9a0b02c000c090385419a50004d45518450300c11044594032601d1510014405000d5411820750321810381d0a03e01d00303802d0525496005650581d2040903050640f024403842d0f02412141130301065a000703820f0112030455980c01550b0604c140a40c007840d00104100c0c21064924004000990f1501c6550505007030850810803a5030144030000600a0203241d05c2e60400000c507142909824100c0443c641820901c50034800c151000344440d10002c0c01080058141e4003411030480e05590070441a0f996070140b142a1003601c003040c0c08265070350000030051500d12802d9034805a03910021500300c08a640303008450704800503505842102040c05030042d002040303528003d4102c1d00e88003844030444481c4a901800ba00c641404205040c4401c0c841c05c542001004c949542c041c02c007008515003820110b84181058804074412042c0c0c2000c200000c45920613a00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 878564766 1250 878563516 878563531
    0xe0913020a06180e040f0201080a020307080c09061b061801021206040209060f07060f05090115060302030a0b130f050f0417071104020d060305060c041d0c04170a0209010e 75
    0xc81d1103040c8901541ca003c070314801202e05800c2c9040205020480f14003140c015440f461134032a0200c02d80c1b0002d04010f5000340900f8442d80b0502c100f05810b60b0001c1c0d03282d040844810240c1d9500d52950224907144140012151840c0d032440046409041c0003c60500ca501034001c00f03000c105003411418240d10580d16410346071010f08020031900d103007650042a100f00002c110f00d1130841c140b4040807894010500c10741d41165150850404514180030380765000b0781300402008080140071103040300004c81d0140c030040580c04800503200c040c440e8452510410000c0c0b41c1d2020f0400703030580d44041c00d80f0380007541c0c0789420300b400301d1050101307480da080c05960300c07044072050008035001c0480590000b040c01d85420387c09441691a0352200d100070041c199a01c03402044860860405500d40503000e0044036045000304403c2000342c0845005ca00400c4000c418222192611400d070415806103401c40c024110201c200004643c0000035803c840074426524150070341e98482150b2100c040031100803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 878566016 1250 878564766 878564779
    0x206180a05060c180307080109033c0e032509050c0a03180c03080c01320604061a04090b030309010c030e180a2009101103090607030e091302 62
    0x110050032010107004802d00d201d50040070b02001e84c00080c5040b00316440412140d555643d03680c1859880411010117085d4404680000001c454000c56008be0160f600d6440150982640204c0c40c810202c1030f001c600300408541e41c090718510312544080181c581c604160b00009000506101140a40c5d07200b02c0c24060001d00b0100d00b10400d5000e000030821000700c05044684450001b91034500201c05103000b000e0054403200000a540c1c2110040b2402d002500c8806000d202c450828502103041040c03403000384103080d02d86102281c068245130704126007e5541c00c41140c0c44421120103030044424403041030000850640074940c4911500c501c0e1400105800b8a80b4042030103800c0d048070940d80940398420315280c03401e00724024082540c075000c08684a0b49141151100d10110301070700c8140e07100f41850440200700240c0180300041d880710600802c6026160038102c14001e40d00b03000d070050050b40d40d4a400d45401000c48080a10075442100040c0110b0741a00044501528059000d410b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 878567266 1250 878566016 878566021
    0x50109050d051204171e07090b030c10020a050618030703050f0909041211070f140a0e0a06030209090f100f0207050f010506150310090f1b0206180a0506 67
    0xc0c05490041e29000362854850500e038208104840720040c00108014014112440c40c0c0c04113141c1403944550300582101c2c2820024801c1c00804103140341165030070980000c2900100340441e052018889040b030f408a840d8584400300c50300441c404c03e28a200300180e6031b060351004070701c080c40c00b040383e449641c40c3d1090004100203030040c002040350340340b104030460030810b0003000110024021541280c421424115409160b5000200d0b100050b000d0700140a00c2800c1200e4074001d452180300740d6208800412140c1056140e0078101d0001e091541030507002072400c111240098840d920049000d0086400015012503010840d00103614081c0041e1894048000040c00035180c841d0303c80044903420412400003031010000c410380007c0704c90000c81d0501c2c1841c1004000103001c00740d8460820100308100b003100410b400740040e00d0200c580060400c44641d04880180144050460fa4409840c0c4100a5940010f481881b8400c11483d00300c1c0e80040c2c0d280d6940312103e003040100140d024401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 878568516 1250 878567266 878567269
    0x11d070906080403030f051005090a0e06060609010504030c0f050306060402040b0d090c0f03060e060106020102030c0706020a02030d020d0902032112221b0b072d1b14040605010905 79
    0x60f80040c005e1402240c14070051500030304a800685200e2000e42d180c400c10040c81c24190032556000ca0540c504202c0030100702007007601d0710310050165102c0d60001446081d16030152040e030f0091600540d403040b03641c0d1034204000700304410b03004040c0b00307210f20000204640345c54000c41d8141c41d514122642030544032605080508a1404110b03040d00b00b100005c2030075034003105002d008600401e80455881851071881c1e040240680181086900401c1004203a684020494240c0340d400f050043c0c0e0b0b00310b00c1000b00d0031801072610ba400a42d0000548011020690b00103602650086054500418000c800c03c461a46583c2002c0701c110000e1203511507003042100c485a0060300b02c014070200c4e0541c1d14200c100c00d10308020450712020b000e11041c881b132040c1404440070b000301d5810245031180a40f245500c0a420701c00001644156541035104c60b00c02d801e6000c402548012030103600d81d00e4202041d40500305024284074007101c1184540ca500d03150140700c084600c1030b1a003603803007400d110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 878569766 1250 878568516 878568527
    0x30108071a0f0d060305030c030904150e0106050703031416030b031b150405040e0106080f03040f0902030c0c07061d04060312050306060c03220e070905131d0303011d070906 76
    0x42070f000095602c400000104038240000c02d1050701c0b003405147c1d1203d0344400c20084801550b502e134510380d10088240701e04002d4182042c10740d107603405c0c11a01c0f40d500d45400c801502d080500781000e40c81100500607040600303540003030032900c181c60074041e400300718007031555654030f01030700c007071501c410f50060318040c28002c103201d15040f03d0421032840c194485020600f518402440f002040e9920135080185401c148080400740303014002442c45c0a01d04060940b806256000e00700c42c49074004041410300440f1811120020304220940d4100d550303501001c1d00c40302215180d034000081c410b403080c001f0329061044909a81d4003e9452108000707802c4e00300c1d40350700000d2015800c840c0811060034602d4040010b08400d86134030352940f0290001d556140d46038240380c1d20020029544009200c0e81d59042241e00d0150340094814101000405000c0e102030714061102e45100110740a940c41d400b0300c003000450590742e800385a00048401a0f410380c80340401100c6200c00142c0c240c8003401502e1040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 878571016 1250 878569766 878569777
    0xf060115020c091f0509010e1f051305010810062d05090c04080d030506032e06030b150a0b0301030305030a27120f0e060702040204031205030108071a0f 67
    0x1441103512000006011988004050b40e50b1080b03c1d802c0602040300740e25130781002d409404c05503080c00c03040d4504200340095a41c040c001441e0460030150407881003803140217080040c9401401ca80d0316401c516420700c0185020f016880ea540103e00c600c4804101e10f001c2c1100711070045400036215022074400c100049100340030b011010845c0c01c000680c1d40e40300c2140f14011484601c410b07036503501e803a02c00c92915000c2039502060505002c00c1040641e404200707117906400c10903140c2e4050314821403400f82e00c020030b010300d0350031340c07a0000c0030082c000043c440c00d100700403100c000e004c960206001c000c690a074621414010050400c01400040d02c200c1c082c5400090070306021680980481030224681c22418500000c14408402e4a00b4844480b8540c811a807050600c03101050014000500100703030700106502034075001902404640700c6604032030040d9040945400840e05135500103110742c1c000c0c4900c098038840c0d8640824541c6101c00454800180140f4103443c01c1c2c01500410a50b4108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 878572266 1250 878571016 878571059
    0x9050607140715080a1401050d020406050405090309013c020106080706050a02150f18120a180e10090b0d150203011802040b070609052803030501080f0601 68
    0x220070803080c501d402044200007600c1040c401111103102500000c2c40c06400404c82d0700b60904240d0030140180100010a06542d010380d1203900030319403400400c02800096100c19003280c548010490180f40100280018510903a543c59408009203615000c4284502046e09982400010000360480c86620b036000025140004113800e540e4501c681d0510b0030f19400200461000982c22559980c1841185185c40070802c41d2491800c020050b000c041c0300007072003001000d0b4020700f00e10001c601040a4402c90b80590300c40ea036111203408c40200300341010804034254020602d07010030b0240d29065028494211303051841b503502e2403c040c04020384007685580d80c00205d81c000c0100402c1020304090108043e8410140e901d5252510b6030b0b403000701c0d10301c64403030f0644180310070310240c1a0102221a1685c01800207c0c07190014184039040460707040c4030420f01e501403103d8900040448000e402d0003402610b003000285c5c2d071519a191128210585c08019411000061218848004003121003050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 878573516 1250 878572266 878572283
    0x5060109030503070c0e1f050402031b040b090108010803160b13062c0d02100504020604080d21060501020c010f02121c06050609032a0a121209050109050607 69
    0x5582c1c444a00b03641c050354007a078505d00104018080004180195138018251000c0d202c12940056001c072406006409070902c0fa076000004104459208107903102e001c443d810049075115600c0d10407242c0c035804060814003240c10f2070000560008044140d41d455440c1c01841064983c0d03a5445662040d03001300382c10701d0071035036461000200781141300c2c900230441840d80418440c40f820606807035184040201c44a40c0d402145d40c454041d6000c50148042c0000702030100e540d80b101c1c8000307001030240360861246885480841d5101541c803010120341030300b403000c10300f12141581603a441956018003c40d0301580c080c1300c080c503144d486181002e02d03100b11481969000054000400002e0340402e0b400414220390f0495180c8070103085c451003000348003c0f40c03014039060b11070f80840e0300c0b101c809c01200c900dd1400c540b502040e00035008540d0034104018011130303d041d1240c0803070328240ca0440c1700381c841d00141e058826041e80100514820348005843e104a21483d04007003051a030f1114004450051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 878574766 1250 878573516 878573519
    0x6021309020a020c0111160e0c1b0619050606120901090606081e42010b0703030b0f0114090604090911030d140307050c011b05040510080c09010305060109 68
    0x181140301501c82d0242c40c0d4050055041000b000500180f044020ba403c1a00b0410542d90049030700140802103804038081c0e41c0d02540c54083d030b840540650048101c1c915a080d02240d006000454074610070742c4441c04110240c040500c90800306e49040701c07002d401000070040b072408aa0456034142c1d000040c03000103d00e503100c9540c0c040940c2d047d81d0004189920980790804400c0e03030680c8004010f48080c0c01000341c82407840510f0380144890500000305202c6c1d00a500300c450340084100e80a001c04804100b16507500c0f11450241e5008034010703000a454150084194a8a00c03181e6030b00220581da00000001c202d070032201954050901035a10981c10440012a88040c1c0641140c031400381c4507492410701c000052500f0f04800119400800800c4141700c494100032505482e0800c110b89407554403454000c14950040140302c009446406500360080d242d03550280080c425104155040041c22080003400d4070590801c0e1201011300c103050201070000e502c0303035000940c4010145400180a07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 878576016 1250 878574766 878574779
    0xe2401020c131d0303100b0f0712050f0c07150203070c090f020c01090f03020c1915111617010618180209040302010507031406130507120c0e040b030601030f060213 72
    0xc141550f4000729541000c01000242c1e074191140100a145000c8a00d241c20a00030400351544559040202202c1c40061404000c620640070358102d134411142040d610741c0c411050360340e00d103581e2041002340c2050013602d20304ea510110540d0040d69100c3d4441c40c40c2800c081c1d90308060840c1000440d00b069007444184e00e4030700240142d04129026080e017140700503042c14024200200c61000c140540113840880e42c9600400d2a50030441d5150b944034507990309408401c41c0d04284404022240d840b0780c0703079070494031004d6000180c100d4542d5104001c2c8452081c90f800d0030380d034551051400c8507403030005901181c01c094000c07001c4052280c80404e00c04030580d00040048105460580041c0c0d503a10400c402c00d9011b110710305070800084100c501d40d14202d0000f400c190040c0c8502c0e13400a40341d0010442190280c240046441d80742a000c0c0a44e9010703d20040c105001200018821403d0108041c070600380818420f061369040052a140340c03205407a803001035400702000d2000c0c40c0f40000000b42c2c1c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 878577266 1250 878576016 878576051
    0x1202010e071710150e090c040204061106011514030c070c0807090e010b0609190905011203091406072406030609061406060d0c030e070e2401020c13 65
    0x151919442044408403407038401460f03c4003240c65159050714081c0c000390081101c003520022110b04405102659544030301741e0381012189108035401600100e8082071507078102002c038908040c18001c5844980c1daa2041440d0305a00c0c1201c90045021814081000c846240055500524844d10b0f14500b06680c0c0e41c40c070a1012660140f82c0d10f4004070f0040c000c0c5005801280070709070382040280807c441d480005811845a040403500c544010000c62201e12045000e11001b0143c20303408118a40e035071810096514048503007140051481840415070301c203084d920106040010701000e04140a0f66a01c18072009104c00008680c1010601140005010b00500018600c6610081402c94403403512800341c0c0e4083c49403000c1e0182440800003141c54007820740e1a551100400458a4074044106800030242401600f10070b010b4a08081145a00120114040d411203000301040c02c680b03002c01c14880c2c6409403900d00681204010b030307a0300d01d00040e030806041d0309010002200c21400004414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 878578516 1250 878577266 878577269
    0xb070c14100524011d0111010606080a0e060906060f1305010b040611190323042c0f0402060307120915050610200109140a0b100506071202010e07 64
    0x34025118001c001e8484005000100246450030032000fa160340302c80040c058a405a40c1001d003146520030804550b886000d5881700030540b600208809902c071135008000c403404031683c09000f0f0414500050031200068a01d2142510a01074402038554800f08109800340100c0280d200741140c017032080d02d000c0d03071040350300070725a000380f06070390703918140700a885046200e001c2c488981102640c14606c091030681c28000b542c1c18902003c0c442c0c030744054aa00349034005046c1140d281e000c01c002c1031b81c00c4040d01e2107d5410b1506694242c880b4000e507241014030301100c03a9818081c4000214005003050405107402092504024441d900c0d40d000d20000c444c041e030b505540386000d2400420900b001c500c40e840c3c11220a40d51800003080d0b00340d020302050007006150f044501c241502580070b40081d03200d58016a48050316801c400940b060296032441880e005440400342400400d00c00c0c550410007204940028008074103201440d115248540701150001d4295500c40380a0070140600b40030323510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 878579766 1250 878578516 878578543
    0x90901090e0c18060a06110303070e12011509060b0306031c1214040311060702030714070b0f0d050a0b130c02010b03160f0e13080f070209010312110a0b070c14 70
    0x1034980304d02000031143d00d5602c5003050041504052003101c1d008000c42c1e0b413050082c14041c01031000c00b0003207105120464840e51a6501e071210f05144030103010f190074101d90556005100e4943c40e103c207100c2c144010740344a86d0561104144c40110141c0c070032443c0c403450003420087d09508462400c1030a8801c0d581c4d0800040c0340e0002080205500203045540d002d104400900191a11310806940c0784103101014011080700410088455400c120200c003a05a0080072074032665596041c001d11703040281c02545940c14130f000a416503d2078819502111301c010000c08d840014108500024444002c50b00c0440d5258110124280c604010001c1c0170031040412002051818000e452039800e2604201202d40c2c44c134051100169480f0440055940c0040c09959161403c1036140d209100c1c51900035007091016000200340708019100400803841178072130701400c03100944940d071036480555004096600345c00100e10103502c190b69541d40903100d0b551704d410001914441d2490107240c00a00b2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 878581016 1250 878579766 878579809
    0xf110a06110618060c340c090b01020303070e0609121b0414161806031407261b0304060509010c050a05040b09060702181b090901090e0c 60
    0x403050380c4420400e80b54001d00f046815030500880111142c0c40d4800076005254081d00841c02d00b8030408200d044980340c80c90260f026050710754210200c5c0d032540180c4000d69210900e090b0004a4030040d01500f02d414505a024624590310008151080842000140c0d0815000c0c0034011140d1900d82ca88400d510841d801056418101c1d01c45004120ba0781441900450900c40b240c19908405c1c21499000004a4030088180f58600001c49645071412180281e51221200008000350581e000181a8000708048032171660341c020180c0e580c10309100c0c0e12507010200c40704822403d40760180a0340103940030ba00000b100740c28a5100a0036002540c040e43e64035074a00c28401030610074030510814a00d2810480d081c01d400540141c168059440344556076040040c00400c207517a04405c80703414950040007103207807000b000840045010212544013514069038110a10300994034182ca140380b40007012041240c0c2800d14500181006180c10b1000b440340300c04070f0740503544250700201e0224401000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 878582266 1250 878581016 878581037
    0x9030b0a05061e030c04020313240c080106020a020f03071508060307080c091303020a02121005100f09020f070f0f1208040b04020d0201210c0806100207030f110a06 72
    0x20082003083ca41208902e1810540004885071008101c4d650031540859005841c4d03039581c049040c2c601040c4000400e182c0100280c008600c3c141512036082e060454070401007400ca140f800c0e41e4221081c06034030096030210001320014500020009102480030f030650385400d80c0c610306107600003001c0c512100810b13034020070001d031400d041145600a18043c0e000302102c1e0100d0307002c1100244080d0404482034805140d05c000e01d8002c2000744a0180e000c1c0c000300c64810a54082900d07603800701c8200d170701241001c0110f0140080741c1400816169484400c041c49840e001a000080d1700520a40c04103040074003846010600c49440204000e00504009094082503e4000c826107200202c42d02803003044014407020500c6003c0d541c3d070099041e119000c0781915400180c455020ba1240031f815880f00c08580081c4440a800024202610341c4456005407100f40800c010700d6103a881110040e0300807181040401c41c960400c00b00903028030000036111a0480c04071f080c180d8070360032620225986a42 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 878583516 1250 878582266 878582269
    0xe070207091503030807120b06190e03010504081b070e1509090a08030c090409151506090b1912020f0730050315040e1501050a060f030c09030b0a0506 66
    0x600d84401a9400080690b5095a030701400704407019000c802000f6120f4403401c54040ca0303600014003444010006501c40d5030701c45d0300f01c0b041a8560b80751800201c4106022501e070a050250a010b240d001c0d600a04281c0164000d0092041c1c20032441c4440c49140d4002611144501c25180144040d81e88940d20140b2101408401100070b420400568442d400c140d000c69904d00540c3d410042d114010760341c42540c2c1000402802880c5c0024118912301065500c210384598004914541400d00d142c0350340755507403c16070348500148946001d05508200c4101840410305004087d0344913420081c04540c074090b1694201d800c03070706005601c4100000c41a0134001682091500841000881c01d01c980342c100803440907180140d41c20080c0500400880e543c1c0381400c4944a5015000d04100031101c001920755070b40d00d00c501c1501018024440000c962800c16507004802e40d03070709445004d10b0550a00048000f824104030b00403c100c900000400010042d401003402041c940001040c00d0400a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 878584766 1250 878583516 878583521
    0x411061b0c0117100b071a0717011215020a03111615050405030d0b0102073f05060106140d1b030c0905220b04050705070b160c110a0e07020709 63
    0x11041400c3d02d110004011050840001c010301752003c10103040e40740c1e64940b41c10714020011482022805401d14100901c95606c0b120000c11510703d00381e084078a0341c1e41d2107000000350940c200a0000f035401c000548058034940c008080c00d02c801c2c030300016017104440c05540187c02545400f80c4008a00043e1024029034030312120081209a00030001820640c2d40c481d41c0c0e00c1100440c4410350384500200c201b9078000d20a12004010b0740c07202c4544000e80000054501164190f0749442400c914408000105044100645160b00400401041e428214151001d4800303071034450940200700076021b50014980101318038082811030042100605500140a588030210702204104103454100400e40d0780c48001c1800c00044d016500860038100708501c003600200042030b07002410b003000d1104490f4408001e2201c0d41c0181000a040d0700c071071000c9a00200c01c1240400020a40e901400100c1c0141c3da2103035607500d0061030030884907524548100071620407103111002d82c000c403a00708140b40590 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 878586016 1250 878584766 878584787
    0x1a090d080108070b04031202010608100c02070806131e06020d0911090603120a090f060203031b0405090105060a1209030f020f06160804030504030f0b010f17060411061b0c01 76
    0x320241c0442401c10b0700004c1c4a006a00c40501a000818900c0000c98001c0d4044400307060100103031040340c54107a1040c0041d140ca0303c1150014461030000080c10348010540c1381c090100c09060740003901c407035201c0c0b5542410481000c1c162086154401c80010064401010001c600120104283d900360034800f0a10020b40c20300e0b0b000b20f858104001060350301180301507041c084402c0c02c42d1200440d440460304aa45034016a50056003070802148041c1c001026512400c510898988040e0300740d219000c29000740d215042d004081c10300180420b142ca0f601030800030500386801c414403000007030300c0030586049030000d502081040d4582060940e0500c4000c00300851480107210604241d242509032559050b6600c0400000340040b500301841541110300031504414071840c8000141002a2021803e01c91054010140b9100141c041c071000380d04260103512202030850303540c031525548482c0d0041c08030142c4c000320800040c02503008070151303c040858850300600248802500142c4540882c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 878587266 1250 878586016 878586029
    0x5031635190203061302180d0c080d050403050705102a060b0f030c090601050f07050105070905012a0206040506210a0b0d1502040306140703110c100203041a090d0801 73
    0x40007000403503145d02486040d54004480016503130300a242030628600052a44e80c0c1d444100c511009040c044d80324082d031b081d642c01c50305032049100d501c02c0c26101c52145110041281e04640e00070801440c10041c682d5030040c0908002c0e0205040c3c1c480c07250591904205050701512144103402409014441c1e492514000e964011912012000180d0345a0461b0102031045000718001681a41703c0c6c030507610b42d407248490300d546a100c0d604d0700c130380a040125017905c000b5288080c0000d6039031160003901210440031a00740d421540c0e00880c1059042045000e0341c0121f8108000112a110180148404120b102e4510018084203034500c00302d25004d010210760a06104906800369070306a010321038141e01034a018507407000b2002c403001a020303540c0040e11039890440482e0b030201c032108085102d84500e176800c2008000114400245001d00040a4039903800005000c9154246030700864005000d00740402d41074440f0350a41c44d1500007151143d0182d005401d09815043d00103c00502620b030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 878588516 1250 878587266 878587271
    0x20c01021204051c120804060c0513180b061809010b1206123307030c201023100303051e0903060103030504060f0503163519 55
    0xda14519814007035402010f120300541041c2d1310b048000310403001c940c5940060100e400f45203015002d03001e584126400d944150415600590107846001214980c2d044044d0f000441401d282d0301c0d580035407420f444c50410340d559005588107607072640003a004582c0e1000201c002c0300504014041c01c442c060307010025803c81031184005240c41032042d554030090a890041c000c0748a5211a4508480340e4070b48140d80202829031440307000d800701c455240c0307200800c4a0704140c445000843c00c0310800068000001d40c03203540355078049980b19144001c285100d0855609207103590300b0b801103c440810300000350000c00490301c0319104215806501c2004c140c0d04070204e5185032000b0b0898865488c100560201c1802541003009050b015200000e00c0030301100d40c29a103903d800341c03050303020380240303000304801c1042d81c00080e104600301cdc0d201c4c640c0d0070034105c611804d20b0000e0728017101011001d58528104403150a0101c6d42c1169019442041b08004203c0d080030304070b20508a0100300746048003030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 878589766 1250 878588516 878588533
    0x9120f0201170934030201050a02070e0c090901150210050601200c01080c0a0503060f1201150e10051f05040e100501032324060c030903101820150a020c0102 69
    0x40607213903035800c885d028203000c3e42d280c245010490400c1560380120754105a02024003034100c000c100901400e103c1a140d26803103036255546124540320200200380140c5c44048410358054058100c1a040113040c10a02e101181c5940c05608410010410030300f00e0b444031170014015030380b00900036001406541010b14120142c100107001c9d1100418a90280c02c00d00009142526901032040000d00501c0c001c20150a80c494940d25001240c42500c0d1400a180003040c5903900f418402d400b1100000c1600e51040407810401100704038403000e401c1848130034070001400341c15140540784503620382c2c010303521844d05120001d011181415040034250740740e000c030340300740d40c40c2e207426560000103550801010100e60100058031207080352070580c202c0030100707084030801d0000000e4100c0000031030035107900d402411110422140c410024082c00c0c1083c1542901150061829007603140000b8401301c10246071a022603901241c17003d040480c039500085d03501c43d41ea41071140c1803401c1000d101400e600b1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 878591016 1250 878589766 878589853
    0x44110050d0809190b0702012a060b0f060403120f02030322060b1507020f100f0f02031204150c0305011401030f15060c05060709120f02011709 63
    0x80005401c010300070180040d203102d4513600c07420790300100d48182d8554410a40c860103400f070707543c00c43c4904034080b605035819031441c1d101c1c8242c240c003c2403466800e5090a012900d444002c0e210f5603501b203070007045121121005440301d0004201035800364129121200000708000d003044070188500c0d0031504284244a492065401107420100384911401036110b42400d00c82c0c000c141c82040310f6400800780040c528010064030180011500807100c03a030280441c0c0060086400b645990540061a40011803400500880399440038081c6071040f01d00b0900b240e030085000040584040e51401d00c03418040c000c020160040ca42c0400780c9103414001940340005c52203180005d4018203051540303d8003090300c002241ea20084070040c214046548850f5280740150022070060800d0303a0600408002400044c06040410300701d070340e1021000d11004080d01d0715050013090388404c03410403078102400d22440403032540700c0b401a0868409002c900c0d030019004035002b2000c5520f014080c0d4521300d4882c44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 878592266 1250 878591016 878591029
    0x403110a0b0714130905060102010c0c080313030504080118060e2109060d1103010f060f08011a04080f0f0f0c011e020309060c030702040b0103110904411005 69
    0xc03155007070880c8903080300c0400f28842e01644c0c8140c2d114510018000441001c6508402d0040c5000e80080200b6500450708072030501003100040d1503140c080001c941081c40000d07051403258000e08c0c01a05281d2900e0070182900d079881101504011400400400e2001920681024281e40402090342c00701684001520b0340054411120040d0302088174a0386071941022145404e122120400060804454180054200380031b071000405003140301091603400b440351805c21a203a6100d0b000c1ca42c1c80c000b00c42e2010045181d14541c800301c14000010321900c204074440860035600301a010b440010003450346080c1020f0a050702e140e200042220a5982044520200d08490000e222103100d806030240d24621a070021650007100001f80b11200003000300244c01d0040c0b08503000c1c0203a84010004400395114170030038128400007081100f80c4c5d8a450703400710501443c880140304000201402480340901c0c032050b2181600041012400c15411030228541d1000309000c2001c0c000d410040031940 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 878593516 1250 878592266 878592271
    0x60512070e0103110c0a0b0c070503040b070201090306020a02150a0c0909020309010221010801111e09030a05061003020307050901120f0c1203030c0f020c150f12010e0403110a0b 78
    0x1d108071001c4048003a44a50490960700604001495803802058030040c2d80d4030303442100b40c910302803403000b140c61003001c0d40844076a00d8007d13000314200350400500c00619031040300e01304c1c1440f020941c0080000d0040c0003038181c110050f0040c00c40078800203800111000000c1868a200b868890002c01e01c54001040405981100300c0050b01d90392480d0b651030080c8207007030750507080c54080c00007500b140000c640d07018140c074200002880b00858004c0510b003540964212180030309580c4202300942806000070b00b00c00e5000404840c0c503007070300e82c641c01c1c101072042d650042a484024400d02c158141001180010310081e580c540c0103600d401e0105503c116614801420802c4011301c0700c0a06c0901c40b00b4001402a80752480c2002c005468080c00922032002c0d0b4602061880141003001c50010402140c88030010349a100b01620401140510758401203014100b0b1105103e0030102e00d822600c0207000e8043c011a048030740c00c0c103090241008101c15480c03030b11030b88040030643c001001441a81d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 878594766 1250 878593516 878593531
    0x2103050d0b012102091206040308060d0201031424220b21010902040b030607080a050a02040f0b040807050303180d031b2a060c080c01061e030c060512 66
    0x85951980004840819500d09500c1c00002100708243d200c0034942d00074252030030110340c0c02c111400e81449a540f644012100500800e1840e800180241400c100c0c1d01d01c800e00c149800a1400d1895030410040202641d204400d40c24544051200b05007c1c55016801070b0210b03082c142c0c2c06110305160b0100000170f80100c0100751110342c0c4600507150b000302e101514141800740701601070035049460003050800d07010b91040b414240066014200030548030f0003a49281e0f036030b07595651240720b10405401d020304210a001d908000010707070200300c1050381700981108000c0035615840e0500c0280740841a0300b00501c83d420401c05081c0d498030404010446c807500b564218424442030905455150548030125148400c0040c29410410700689504515150f4801360350032222403251030a0a10b0b41c1d008502c041021782c009c0b100460a610043c0071000c0b038000020401d161201034240700904003002544821806d02e00274020040c000070118094500307031602905003501c0c80821001084080c0250 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 878596016 1250 878594766 878594771
    0x801060513090c0e0a080303040606090b180601111603020a170a030c0f0209040f02031b0607032d020a030e0d08040302010f02150c0c1009050d0f0e100305012103050d 73
    0x503040c60259400301003804e4000d244200319a82c400000d078680c3d000329800c1300c101d440c1460210b20446140300b500d85544001e052030340944c0680103094100351000d048a03040c4071420300070140a20b820030000722100d0300c3c02d5006090324610b1060100101c1a80c12009030020002c14140440c94005602017008c3e0300f51030260152107080c01c2c80d804084003a000a50003800300c1007040140048180c43c520054400d17000c0b1072000c1c0701c0105400d07840c5000c025196004108111000102e48034203200e845029000700c2020500f040980840c40b040840326200340942c001c602c01d6418035130420307080700e00040207540052a44019680301c075110710581c08020706105401c40c00085451003000061020300138000e5102c020b04012000c8040d5400055925409200b1000ca003a0342c00310758090320300307002d0344000101150000d800d8240c0f41c10081440103010070860031580d135101d549091031100c032880c1303036100005c1c194145914a03091004032040b051610b6580000703540000e41c040120340803001d02c0b0400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 878597122 1106 878596016 878596031
    0x1b16150309020906011214040b10080c030d030203090309040c03020d0b0301150b070830130c0b180a030b07030606091809030e0619080106051309 64
    0x94112400001064441d402200b011862141c08040403034481a000d001084403c1f00311403d9403406418820302410144002402001c2c2003d800580129000e00002c00e65400d0010129000c0550001c00202c5820052080c0c3ea00200f00410a110034076210034005c02039080400c408009501e00300e1040001d1405200743d0403d9641c5020075194940f401144c062560000e44007912200d200700860f14080804140382c450f400c6040403490b0f580044066a0310380f041005061503103c03082c403030041e00400c2c9840303051011030301d46804880c1d8031440e50340d000941910a60360740d50440d122003804000c00140e107080c40d2007032803561b908000c0c25541d1403080b5130111692140300707803030b000c1403c0d004060300c420b03005001e010b0301a0401e14040702c0310401040f5150b20060f004002803901c06101d40110764804000c600400ca94036146007003100803411000314100030b1188526523982c5201 = true := by decide +kernel

theorem cover : BRFrame.Cov 878417266 878597122 := by
  have h0 := BRFrame.cov_init 878417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 878417266 ≤ n) (h2 : n < 878597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
