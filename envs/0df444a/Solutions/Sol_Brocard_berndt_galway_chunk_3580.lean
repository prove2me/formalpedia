-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3580
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:04:21.922191+00:00
-- url     : https://prove2.me/submissions/9bdbafe2-9420-4c99-b643-8d1bc8874b45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 643705035 ≤ n < 643884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 643706285 1250 643705035 643705037
    0xb0d050a0506240d0905033103110904030203040b12060901050405060906010c08040f0e1501020c15090609090a140c03070912060204080f03071208150103090204090c1401 75
    0x1c0191215020803600c00d1030603001e10700c0c0c1c415606a480c105821a0043c146a094984001980d5503407031320b031582168420060701503213080d40c416030001d030b00342a14000c0d80075401c2010014098195600c1402005540380c859114070200000202014820070450700a421071a4555454103071104034001c0c044c0090310450311665400d80007140505080c413595100d14070060005440c2d442c1c17000159040d44915000703682d01c0508002c04039070300002c1c41c401c20041c40c2088480410346403414600c102d00013845030f194115001030158082e161b55100301d140c500301880701c2d410380d501e070b0400008006115416043c3c0d000840722040280100e500d83c0204030800034051403400316030b2986034840c240e10048860714081031400c4c4042c405110250070040015214420040c50183c0300c86101e843c010040e014082d0340c0d400004e5a90410032038010030503039070806043c03003c014100036058020301400c00070307028100b581d60040a0103640d1150007030342d000390300a50741c04d00c885d85030100c00c54404018107460f4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 643707535 1250 643706285 643706291
    0xe19030311280915051206010210110d11040e190603060603060f0c0c020a090e0f0312070210061a0315090a050a1a030c101112190e1f02070b0d050a 65
    0x150707007040c640060007082c0284c1d074240c903014140c42c1441c6e02c070001804090440c450070b1481034000d145c6225003242c400c0380b8040140c448071a030010740241c1d84542d0140307005520a0008000400044910980041500c500c0c03064a00c0e41d0244840280310306d034000341013141480e6000041c415203500c1040e1501f5642c409108141040c0400e48008042d82c40003500920184d00c100400e601c10f62183c2c20764600340083d40c0b50b461242c54441c1c0785410040c44203800120b1001400801901001280150351090341e041c420a80740c070002414030303180c449607a450220004006014000300075000078680c00014038a6184c0c3c140340e50461700070481201d000c40319902d04485c4420302c9600c03c02d617541581c8020010034081e0448400e2006110801e03143d4014011501001c101665041c810401c01c0c4034810b04071034850040311404c41d4031503c1c11240700184070414085401c240c481d40211450551603290591454550b8007049242c085a5480101e5181c0045180c5d83c50014035084107001d628004018 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 643708785 1250 643707535 643707539
    0x305061210060f3f0f050141061206040303050610020102070206070f06061a090102060c0a0c030c02012105011a09011205090102091302030405010e190303112809 71
    0x10642601c00000d202d090107034040c4d1000e44108a01090100041418001c0c00380580c090ba1003610f04003049008940c00d0f5140c550350746014024058040c10300003c281180084500102da030100400000c11480c19410f0890020343d25403611409612111507500890b10586000d040040040606440c00c0d07110300303640a40e07100700c203205000b580c104a400408140c40c00000e0794442b980c4c0800000c0456681d520b500d800280580700c1051300400058404046540340b9807a00024100710b40102081305a050034454038a49690000c0e807100d0755503042c10401100281400103030f031100b000c280060024031042034000c658495903040705040319444c60b04079034401095550444217014001c012800940c1c0d1500c80c144628403500a980c0110620700014078042c810001706850700038844200c001241c0010074002000000d203c0c10b040c0716055400f602c601d8216140501061381c10f504050105a2550780f060140103002040740d84c51400d484200f821603410801c5130310b254040c9690a00400c1d8050b04c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 643710035 1250 643708785 643708799
    0x80708060604182c071e0302060d0b030607031d152e060c030809120a11101b090e0609160509031203090d031103070305061210060f 58
    0x214000c250003020a8101810400d0a00541036003481c1980059204d0020b6040400c80921619003c910034080c03882d18031a20340240d280071038507440098602c51003440c1c0003489441ca00400c00b501d50444080d6a2160440c1d21103001d024102c1c05160300d0b000780401d00140e9905540410b00c02409040c154041028003540035868507448600c15204034100b500003000b4131000c40d041002001d407003000c60601500c02c001d601080d141a040138020034450f11a203402c2c180c01401c0395a22800c0c1d0001000204c06854041150f802810701c002c0501c1241c5400d07808102041c0116034421103080c004214504550345418002d50f05004c1c4200461200c0c1070102e0304000d03120005100d100080c01507100c03511000030061420f1000c41080e0200542840080040c0c2e030140120381401c0004840e40b03841b41004e540d828240241040c18005040c0b410110a14098964081c1ca510000d10700380000c05540d86804a0341c109580e08800c004c0f4003420356203110300001c561050703068441242c4500d070015240c4035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 643711285 1250 643710035 643710047
    0x130c0f0f09050f01031101050408030d0f110a0c170d0e060a05070810050f040f05070c0507060c0203150901020714061501030506061c0e0a061406090601120908071709010807 76
    0x103003400c110f641100060021038403e860003180f414040c50810315055840346194190b40028507001600c5480360310344030700d582c0540111040082c0301041d841c6032103107112015204103010f44008003030b0004ac0441402500818060b02c02d200b5081000f80704030b840d081100c50301e41c2c40482d00c0209103443c04010483c0d1511900c03540f445076200c0c04140090b582800c041188548005c6110307a84681c80e081d40e0240a120780c01514000d8440c0d0b210201c40d82c401d07161141c2024525001001045001040039002d1307640003031001c82c12881010707041825198101d29502a201b0794030054210020600c41141c55000021072503c00c210307250ba80704546400c1030044007590030581e50780742d1042080c405050a52504042007414084003080060903c6400a03500d0900315001001d4032000d07540c1e04400d036240611a80c03a0385c4a081160f1111300c4c1c2c603200c0c0010345580c440309101402c86695500600c20405040212800c0e41d030000c0f2600124030400225031203c0c0d02503450140001e10040106800d90b000304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 643712535 1250 643711285 643711291
    0x7030e1002101e0609091203020f0d0e2b0801091e0509030909090a0b060603060d1e0b0106120501080c0619180b19110c01030209030c130509151e130c0f0f0905 70
    0x20b101c0e1078000c0d0404002c1c090041c050030442c042c016a01140750754012a034000034200e5140501600c2030302d07201e40c060301d943b1050b030017483c00c5810001c0c00c29403180c0108240c00b452122102c00626602c0d80040180342d40203901c40580c00813415014800e02903030004403100030900c030342280d0540c0c0e501c03c000d02076180019281c4a401c00181039900000034001c648030441d15030351090032044c2e000c654540b02c03100c0e2000e07030201011841d0707004c0c0d420b94401180215400f51440c200204041645200802d002c0e100d04000c040301c18036149100100d0354803c01c075039403512007088041d0240c65152000e204071580b145c001c18001410500c1443d85541c003a200440e56001c034007001c1d00fa40768401c4015000b9620072100c07640d03d4001c0008055640c1d03070718000c030034100700803502c0007980d881c0c00d10510f0b2408002a0441584800c54410441040c9e90065828001e500494440090351281b0703440c02c2ca114040840145249005040416088107580c0c80f02c0072240351244400c1c0440d502d0740d106080720425 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 643713785 1250 643712535 643712557
    0x50a0f05030a0f06020d0c0f12050105030d0c05102d0b030705041e0908030a06120c090207141f0501090c05031512030d0207030e1002101e060909120302 67
    0x2d00342c0801c119064200400b030007040c01601e80300c2c08252020031030704403850500c041a0b07c0040201c5096100c250742084a41154003003105505100000350381705101500e1804100d4015800070400c1028840c8002c0c0c058400001e012a540f000501202400c0040e0b00f11010090160000080c2c03000740030301529640041c0147c0031182c140300510000c0c04500282800806183c2144000d408803489060b400380e0203000c000b03449051500c8654140c54080d880000703482e00c50075020000c286121001001c0318505d20300103035548002e29010072248007281c1c0741c0c4418007511b0b985c2c012600c54500e4000c0c041c0c165480421150380c88283ca0f60172103010b5050140001c1e414400905011010f0081c00d08149004000300701c0e5440d910071640c556442540904080340d00440c0010806d40c20002820174900200c1e4201d080642e5010020754400b002801d85812035180e0192410600001c210540c401000d20014403000f5200d04184000d40324203401141c50034943c02041106034400d101743d5500b0002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 643715035 1250 643713785 643713793
    0x9060606030106120f021c05060f19060302070609140a06050711190f0203011518050c0702061e0307050703140f0f0a090e1e150a05040e030d0f0204050a0f0503 70
    0x1400180d00300820f0000040d921051b03081245c94802c0c10480103212109000b02ea01080928140c014001c120306c04480913401244410800210a840d65615505940e0980740041e284ca609050074030140040700d0024222250440205428480c04100c1c81c0b00c1600a01d008d02c070341c2d280c0c0c44e0203c45001080b0607411080d003044003008c004003ca40c4021500c6805400313486800d2569800280c2180e2021061401840300c004080020390400c80c9ca51050000c40f0600700000e103040003e440091180c210002e11400b80022603440561a595200d002d15007080881920303071801220142c000d510420040d4003091551400310039020200d81111078a240b5401d5040c10300e40d074850f0ba03101a400c8803030320609100310520301149054069034104c1c4940941904d500001802c0c1000c203002980103000507500d003800840160050b254842075904031201950002041086c05200034107500272555202c0e0743c903040140302c021202c415009001601c0080356100314142d5650301504200304c41d88103080d01500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 643716285 1250 643715035 643715057
    0xa020909061e011b17040602100605010c060b032b090801050c0d092402070308071b080c0f030c070f0501110d05180d03030614060f190e1809060606030106 68
    0x12207107520307201403480c22031204c1c0320704041e9441e94800d00d141c00e122541c800d00840c00300621541007000d601c070011242010040c560801000800d10050401c0c040e0006494152541c81030b00c1c02c020802d1005128082d000c20543c610346029058081503100030001050504003198420042c801c042c020041e0445c141e02d00000312076428041c001d91802500d80a0680451042c20842d00603500da0b201842c201c01640c5e4015864040e05021007d01380404000c6400c891070410840880303810032040d00150324a4880200490603443d06c10b030200002c41318040820f400e0210322000034100d042d103e25090400072191a080111850a444d032601c0351a40c0c054005040102d000c3c4c002040d180000c0340386c108200d5035882c045050895265800c038006680ca07001000030f0071a8020f114030125084450905c1c0c0564010000514014000c0c100c540240c0303e070201d180e00340a41107880c01624007610100a02c41003552100250404403440f450038054a00020b010b450031000b10b0781039450b2a00c1d0405151 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 643717535 1250 643716285 643716287
    0x1050f09180a05070b070203100b0108130206090a0603020408010c020c090c030604111908071d3f012a080702070e0c0915071110090308030a020909061e01 68
    0x418518060514080c004060001c900188842c4e40681200300d030460b0344001520516140582a41500034031034944003210001c0da034003512658200d00c0040d0700b465500d0003800020420300c00c5400950340500c4001001600b02d030103801500841e080b03070300208070002110b0410390b190a00384d1011640488028005841e65685030080c50700030b0406400096083d8030690070410340d51242e035a00c84851440042e4003040d59001501550202d51440e29100004403080300403500d03540000030a00c5402000c1e007801308201035280381e842a1000c50556003000c450110010f00c18a11090408507a500b0010b2a05580e03600e0030754070002c5c040d801010090b072444840c040350038100c06001001103014504000030100903480c03c082c010701d00100303815611a08082080608046840342d814010b106000300d50100700048072a4002c80b10603200c01c128074031903203011070f406800e58100400c850404001d02c01c90358420b030f003e4910954141e4640c900c5031150700402041941d0409201d11402190030040b840b5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 643718785 1250 643717535 643717561
    0x40305191e080d05150a180f06060f1d060706020306030a02040903031a01092d03050d050a260408092d0a0501090303120b060c011a010801050f09 64
    0x24066056041100034840281d244007020070002d0341c90400104003151203001c90320501e9001581110b1410302c075540355020451b0400c540c418500d04021201c81d2079400c1405070031244628000190030803266407a41409002c0000c10050000001d8a1501c40c0300d0023401c0c040c40c0ca0036010024a2241484051307554540a548010602c907014002c140e074540c0107840b40d000b044005c900c01c1d1008507060381e04500c0059581110040d0318100040660104000214032080d20560003581103107070400b9244902012000c5055440200710b0320884202d049280d3b44913000d00303000e104a82e5a01d504401405400c480708100f00a88ac001051110100700000e81c0400203003e1841c1c041c4c101d100d2078050001852a0810f0f9800d8001700381c00c00300c82c020281c54514081d80140c002424030144050075a14001c00a440399010202e90a135280e0050001d550307070500341d07005501404000d020170803081c0619404441c2e00240c2902140000001003624903007400b920b280d504003c0c0c803c1207151303100201c00c0c00c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 643720035 1250 643718785 643718833
    0x709080c21151504020f09190f17010b04050412080702010f0e0307050105071b062a02010b090702030c0a1b0f03030c0519031d0414070f020f0102040305 67
    0x840020140810007034009008202100c0100c1503441d200e45020310f4460741d14404038541a220794410001211100085c40540d40440350664403004196403c54400e0781c0072001d07803c02002e6180090f40018110000924a48015141402841a00c0b4154180700985900f076400800c0324105001c2040e12074800d1100303543c07003219032001140c21419100900c08868444c45017030302541000800d4410b01c07000340a015008110307442d096400d01e42d0103096a2010242007401411561201c01c1c0001044070303101c10450000c08540d1891204601c428040d00070090410b420703020301d0400e00080c00c098008070940780d10601480150444842603603410811205a52030a110088244004030399254901011406180703c1d0b00d403554031549605086d8a0b108000314140c0300368604010050019910040c083c0d40c219070000840000000580020050442c008034240320030224800c0000709a4860701e1030700c0308401034094400005150b4569805c1c2d01c680c0c0006407142d80009412000550710083c103083c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 643721285 1250 643720035 643720069
    0xf0b04270c02070305071e290307050405040c0f020706030f020705030708120a0b220e0d08060a06170c07080c030304030305100801020901080a0510030f0c0602060709080c 75
    0x903011220144115011529001c0069211071030074402c1107420040100603104111f004050702d80035000d407000c0401c044c01810180300a00c200502c0b805080448102621000c0e9902c40c0c4a1418086c0204960000c1c442c6e20303c130f142071008582d8118000c2d84000016085603015041c154103203034094024158038280f101c1c14560800c202c1001c82d805001800d90b80e442010700e079568182d164944a12180c000c2d0102510501d405a0600140c1d03071403240007040c100000d100a004101245c210000300b46c803c0a5000c54014a200b201c0d069502005441c8109011540c03100e0103522200120354101c0310610401d110381c200317008582e076800d505010305000e07840360079410320f00301516441c00d08541059900300d0100b61a001445080340003c0b220b2805001940021410924901e000030f24501e40502115961661500851001d00c521350019000c1c1d90401c101a100380d00383e20307183d030700c664491003410010301030700d000700d011039104148003812a1400c5000300b80194410040054140c11198603036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 643722535 1250 643721285 643721339
    0x5070207050d0606090b010207061d0f09090724171b0f030105030633150a050d0c0206070915090906060804060b0a050a121b03080309070f0b04 63
    0x1c1c5030380d64003100140e1610490011440d140b500d920a801d1303541c0700c040769041d03400003007090042030341c050644020b03500340c1a80c820846c00c141f008034944805004003036400160031020807020400000d00c020844487d40c180041d408005100b00300601d41c140d00c41c4e00024440d656290b4003051125020350010708508242c001001c090b02e80360750030307800007014924400000c40100490701e401e101440c0e105200c107030760340e4508028803400c1442440c051a03c0101098402e800041030312803041d0229684070526482d55650f80e9500d01600741d822180d40f40021504050441c02070510101e01c03140204450b403075003000181407085040c01812a41015402c020f9103807800100c102450040f80014a941d0320346001505043c2003681c140c4540388281c9009100c281000c0116031603224414080b5100200c0c100d1018842d450314483caa611900045008800d00c400401803041201c001c6005505c80c0d4200e504d1941d5030034508509203000d204200241c4004c1c0070822a820250080142441d1111200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 643723785 1250 643722535 643722539
    0x1180915080a0f0519170a020c030f03070209014514090c030f1b0a0b0c070e10080c060a02010912091d0c0307032304061401060503040209060405070207 67
    0x180c2c60444040360641d109000720300c0e801c00784403061000400307241c050b6005500c8404070b501d9070f908010403422600c03088240010900c189504c244001420341c0700003010795132081c640c001842d541e508928401ea10580c49100002040389104c40c1c0c8204001000000b0943c02041d00f000d030309204015180010400342054612506c7c030003900c504031940341450703015445030905030044d900c0c02549a150034020707408042c40c0515140e0000340f180030280c0000c20b590951580a0226040784200da00c0038200b400c1c045607410850078081102000d680c50800f034098141c1e59805c07001c0086c3c0032440b4400080d04018445403090070030358020841d43c186400040f0364030601c0c8d600c016401103c0002d000008141007400e011810b891400e00c045c0c242c0c0000160080e040500700403143c0d21000d0040001c0c51313614600502600e100356050000c3c0c00203020240030b540f52600b840c01c041c10307003280e104204008050010031540d004805481c040c030b40107050749007169244002d20009200c09040c40b01076105001d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 643725035 1250 643723785 643723799
    0x912071208130602030118180f0b07020f06011d091f050a0204080f0619022502010c05030a02010507140a27090603060e0606010305070c0605150a06020102070201090501180915 77
    0x80d80288103007000c1c84604000710b87d66804540340700394040c03030b032041964004000c9007000c0741031414503402001c10505615058426481c000c01c1340341e030a026001c0d8800000e1004203410707071522545041040180c1c1aa101d01c040ba403605202022a01c0750000d010075040418003e50205500c407000b400018a000d840e58146072401203450f0710013020354010001c0113202340c2c02c00d86540c5512400b4500394207100d4550051180e607400b00090480000412400c01c0a40e03100740300b06941150840242c0795510704a00009018110807a07003a00400c019042e21000d00601e0070850700342c1000782d030326001c807520715520074001c168500302052503210701602c01084605440c4074201c000d504c140d000142131507410020360305000700209030074141850602044105a0000034041c1c1305503000c03000184a03556480039441088401c48450b42060486d6408120290154010b141d250f0007621000700c1617a84000456400da070220445d80742401d076074420003c031a443c1e001000342704510340b01703656a07a880d142c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 643726285 1250 643725035 643725037
    0x620030118092001021b0a03030c0f0f0b10060503010b090409052a01080c04031109091c05070302012409020f041a12010806010e060d02031f050912071208130602 71
    0x143d80102d00080c3d0346610255038040007a602103049120240d1001c10004000488407c2c080c0700140620092030220320800101c030600700e00455101e404491100c1850614244200c2c045078161a144011540881e00342c0c060300c181d90481d50907050440c507001d900c00c11300c00a8108a28100c40381d10030589510b1240000e0104002c00031540302c00c1100304504034000403c400b074003402541c1c00040411041c4003040022603109540301c01502c21501c56101c0c0c90f040340ca00f90030980a03100c8010f000c1448060300d50b12030000c1c10000d001e68002c1c4403543c0341a50403540d2201041104047c0074950300200003251460300035007100b0010b401518141592016900910104003060b10702e8900c0c00940c3c25501c07011202190f0160000e40000e103242d6052044031122144080c003071903c00c030108814482159020010f00c1c034400300203a8048152952017132480040c001c140d4842d507003405030100c520800c0142c601940d0702ea580000700d5030707a01aa000b9007030341d42640c0541a0f070303540c190000e844004200940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 643727535 1250 643726285 643726313
    0x712030c020a080313290a20060411012c010207080303010810060b0412230d022a060702131b02070608010e130210050412030c062003011809 62
    0x10013842c2d40359020070034818401c115401280c0380319040401e4030000a41e901411840280e92441544d640950700300541d11a00344c20052641c0d0039604800c075200e00d130007080c01030003944101403540301903490301c006581480c1e83c080c0e0769a10304e081e1071201c035000d60403814004403a2418015181c442d5150b035403550855000760041026644543d000040d40000ca10640c03005080001c20304d8102820034901501140340302c203001e040040c0c40d02603218000151486401f15941c5e0710101c0301300c0c803540748010b915101c40485072016400740c1400c260202812640c5007901c0b0078001c184034504900340d0300300072108807010400d58079140e607050540f03005540035170301ca40800d009400401d0310918015004048250580000e0207028a25003807100c100c901300700f20410268110780508030034a0310700302101e4501491780100d031107081610840040c540c1103481c1155090045900b4404c907444c0c490050716400b200c5142c0e46002d10704000400a900c02c020b411542c0c101120000300d0034510544644104002c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 643728785 1250 643727535 643727549
    0x310302064f110f10020d0c021305150a080102040b0a0809030d05090a12020d080103020d060e03040f030204140403020316051609020415080105010228140307050d02060402030712030c020a 82
    0x102c040d480861501e0784451005a4088505450030343c001a002912501c00302c0090007442011000303041190754000d500401a950300ca01000707d842c20755070040c1e401b40000f1445001c3e20b440000498628418003c0300c0c10346a08072443e600c0c048044030220f0b030303190008180e2061400280142c0e0202c04940c0211801040c1060003482d42c403e080c20b04c0d0754001c251000c007805543c41002d1a03040f02d030b040700d03015046a030126643c094404460800300c025000044c0311450318080024041454540c10340075406030380c0203403000c00203038001c41c40c8039440715410350700038000d40d001344001000d00c071408940c1007110b80700380705542080001d0715501e94009510b03000f12440030b4000c1800d00040d044000c1c0c1080c500400e1818001f2545000d00113911401c3c0483d528450507548041c000410b40107002c084021030b804407441c1d2000749102d1780d50f86c484d000a8001c86a6024081040101d1840080d81c140202e07001000f4009840c60203d14140420400c40704500380320380c400c240409030b610110707401c0040c000c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 643730035 1250 643728785 643728803
    0xa030c1511010507080f0a0e07060801060e0405060f060708300a09030f11070f08010b1906080a1d01020c060103020108010b13030803310302064f 64
    0x1111601825000c1c0d550240d14280e80352804100403d80d00000c050341019090701009410744400c5800320150855241020041c8a072803000101c10341d00080c00d6049401c150340b28038076048410104829541c00352003103540b0074891492203440e4036040000700001880b89504514040003040e020640004098100c105074031103003054130040c08113100080d07000c000d0603403c0064900c142d0300a02100544071b0701c0810003100110102190000300310030000342072070542d0610019901e007c0b0034041d0614141080c05444c0940303e0885e0400f907018807a040c0d40f0f040d101c040351b80c0d0710710809100401c3c0c030851145610803005210740000d0000e20080c8030404408002d04029030450002504540c0103901c00710041d0010043c4a81c45640c1441d001c09590340031028564076140c0d4490400c4025001c100782c0c43c2d0000d8404003c0c05d02c44092105660648030b9000c0c0c03a001e9031000010100c2c0c090000c00590035040f1000107030072064002a04003011010303501101211010705840d054000e010050440341800c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 643731285 1250 643730035 643730069
    0xc0c090c071514041b091e0c0207053303010e0a0b01020f100209040608061f0503060606040501030b011701180f15050d140604060501150c05060c07020a030c 69
    0x3004030750811040c02e010800388010408107000b07945100700148080d09440c1000d1031288260140b00c0c03500300410b541e11080c0b100a80007401d07140f00462402030422814608030484041d80d0021070020210380004050010001c080710906410000340c80042c0e40c1d00b4812101c0d203a505e8060f00145011300b00040d2540d000d4600490340c0700840728000d0665041d07603c011000410074000103884414000550f001580703548111000c44c0240070242c02450f030a0066104004445000b000d514421500d0284030211050703403142070549031101a900981c104404220a00c0954041e42004050907018034104403100c0e1403070140d600609081e0006d50028080d41c601400d002d20b24011034a442e515428100125010340820f410907291910955004a00188003a003c0c03044001032501104000303400c1d07030300030305c1d091800e50005d200900070b60740601d10304000d0310481445031100c810302540c0034000f0040e641322946003003102e070000030007241d0003501b0700c82c0400080d0b0000c4440004142c0758095120004d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 643732535 1250 643731285 643731293
    0x906110304110d17090a0e040305091003060503060105062802100b01140301030236070912050706083c0105120309061b010c0906020d1d060c0c090c07 66
    0x54440d8070b0a510891503c0c0900020461403400003600c401d280b65500e959026075404540102000e5006200c8403190074104000d041d04407006100040c3c0c01c880c0710f4015052444180c0c100c6110740116501544104014441418801c00a15196035105100e440e4040e0f80380c0100481061004400016009440441503c100700d000301c0c44144402d00f4003154099135220503014ac0d02051001078422215803581002e400c140d85c00b83d41902c1415481c0392030006032491a42c002c0101076500c00001000c5220000d001c21810b10807172011780e484000b0b40340e240c0c50050200c0b10548090006144403185021900301400a0600300c0b103001c0701d0040c1d1040c81020060301500d200416400307503014014040100000e204080103d42c601c20007290382d192550381000700e202c050a8505144d600662a003114000c0c2d458105403104c040340e416900322414402e02180c03c4030446c8043c40c65000382c14210013455030916008014054004003c811554403142c0c0a0020b03070108010b4800c1c41e00a00001303840b10501c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 643733785 1250 643732535 643732553
    0x240604020c0a14010c0306050d060f061e0e070f120c020c03150f0c0307020a120e1806040507050a0c060b1203070812090a0b01030210170910051e0106120906110304 72
    0xa40d40343d040400c1f8061401c800329240e401a00c0c00107000d20b566246000000013280c5c424401340c110107100c40001c6950629281c10310603640514070000007a20002410700b4803d0344002007000183d40e6000101c0341001480c03020382000e00811040d405003c2d01d0128035142040000d84a82030301f213400c0c0c1e00b030030000501c507041040a0a21601060100100303c800c64001954240190380280c9419000c1c01c8100100c580c54150140346510946c1011111072040e05042d15501401c0211801c01050b11909002d13a0244281c1d00030b5000329a075400a8400300d101e5502819041ca406400c903400b207180c4625650035940301440031a0b4000000c6a2120380c0c640304848554004d8100008010700e542c19107410300e481405200c02441040c00d604c2801005110f029420158000e003108414142010440300c3c0e120180d0900601450f441c0200003080340300c41044114100e160001d101070715900f8a1001c41b104d0f0400c1c56018000c944914145001501c0d86c46100d00f0280d802000a442e8101881d150540c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 643735035 1250 643733785 643733801
    0x16030f140a29010906050303040b0309150a09050105070234030506180706020607170a021b24130b130f0507051008042004141303030608240604020c0a1401 68
    0x501c0e191400900c1b90303407030010441d81a2102010525100d60340d46a0b064904503c580391904501003881c10b10a07040c100f5003240a4251050000b80425594404126918107807c501c2c0c0d620810b05c5405009604010b54024114901560000c14032503240d4542601c6c1900c180d40030309150703140320780c0c2c41040171050141401404661014081d1800d1407003006000e03810a1800c40c207140e104001103030525034203a0403114a5180e0030200c0b1080c606111070603484603041b41c0c200450318405a603990a00c2e43d801d104600c158035070380881c2e0842085403540c030220400140001001c42401e80340c100030600d60703640040010310610052400c18142400d202d4000c400c01d8031841401005d4060000003041011020001080030301c104c8052040c1c02c00041c003828403011201c0a121b02c220500034041000810084540c0c001c0d1000c2c40300ba80e80d041c15560f03d03d08950f18070408264441d90401c06030200854941040c001017025091100b400307901810180928812151490aa00c1d0680040400e00a00c55 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 643736285 1250 643735035 643735049
    0x40b0f0c12060f0d0c031203020a02030720090a050115030903050306010315050d050c0a0812030406020d0609020d091203061d1306061716030f140a2901 67
    0x15050505008490950285184603071511200c1000500a91124100c00c81186001800c0380552042810111041a40750009030740e1b22803010241c01c00302d03000c1d00032134804400560082d8941045900c69500d455117000f041c1c050204d40c0c0f031301100e41d42e40320310030070340035040e41d28001466500d045080510503020890003020b040c2000409008207801c01e05981e400030080c06c003c1025200e105001200c503540390001a845400c0e60b06031400d01000258950b200e800a0f51030b0000552500d42542e917a41c0c3d4039005281c1008204005800a0407507009004100b4218602050300758a908501d400d80c0c001e5a12241d40956810f211010700a03080010000d0001608003040b4081c14084c2c02c6060010300c01d10310306200000b00c0030442100c0c03a00d0700c0c076500681110081108039250085101c41c840800341103200c03889651920800413214501300021603901030840306806d816503464800164101e07c9941c0d00c1e000c3c0001400c0856060920010b084401c40c00c0340c2d002c0c0c0c12000d451806140180c0000ba = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 643737535 1250 643736285 643736311
    0x10c02010504030b0601020a020405090f010510051f0201020903011b173c0f0108251503140f0109060f0b0d0203180106080c013b1c0b040b 61
    0x100940d0308802200c1c10740307400025443c1641d58840040c0d1074a003030480020f420a242c103040002d004008903100300c0f40c0c54024020b00c900d46134200750764001291401025481102070300381c1146000641c0e1003d425032a2400054141502035000a084a841030102000c4040d40451102815401510311300d00400c8040b5410301030402d9400b10352400c902000700f41c0003944801d008280380051f286100c50b1300d10100c444940a2805c0e440c1c13401550707000e12400203a4803c03c40141c42d03640085218500c0415007010510901d0310301400c0090241c561000c034428942d66070361405001a030614030510a852581002d0030b6549000302c281c044640f10745c410b416038001c4640074091016a14210741000008540140e200d0321282c0d01d220300c28103225010a919841d1101c00100310202140d0700350402d0b0242c0381d1042c0c5812401c0645070074042100c0c0d08800207034203110500004080c2410204150300a00000041c4013205018031a041000ca01610b298030408100400c00c0080503480b0f40c0010132500d0700e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 643738785 1250 643737535 643737557
    0x6120506010315030210030b060d0c09150804030f0c0b070305070906030b130f1103090105010311040e0d08070203250203070815130f020406030b15031c2001050c0a08010501 76
    0x1070800940002441240c3d0705006686c141d00c81d401000c07031402c00070880c03070340e481400030745800401e0f03403003603070800305501c0000003481d20b4100c2e001844585140d1a400d000340d9455508455241400100c001400081c000e50b90200e40d80c8290a4070800340c17910005210700b00401c01410b038854a0744410101400c00c40c80103a19141c07102d61031081400d100010645e1040b488080c0003070000b50146441d2007001204101e207028054001c28101c1c1d0080e864840244400424081992485113080c0d403d1340c810381c0c801c03620601c00c0700c034180d0000780c5105490400c80d24074240d8000c82c07501845040000d80b0f00242030290302c0c090051100070010000140000c003000c1e052071801c080002d01c01c003036501805008009201d503010552840c203500400801c01c09890b0718000e6900c0030b0507511503407140510f40c01c0e04090700b000501c4c100100b403020380d281305a44d11548104c40c0c64403000d00341c1401c100700c0c0303000304a001030074014603000d0200c60380d040b510341c48071890007890010141d2129040007190749507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 643740035 1250 643738785 643738811
    0x1b01020a110c0315060402090d0b0f0a05010308251203061409010e01051002030403050d05031807140609030313080717010219050c01021e0405030d0305010513020a18061205060103 79
    0xd0740080802c1d061081034281d1711030000078028024940384a4000c0f003498284130802c40800c2001780b050590480c2e041325a12449001c5044800c02d006c010401c0e0380401c850b2820080b642c59081240f4043c1c24280c05105045da5225111032a912100300400e44a950034015011103104451000310700341e400000a41c50031501c545811410310865001d01a6078076041c18141c800c2c0300f00c0340a0361704030089400320700c42640003c0c100c0e401180d520001c246030302001441207202103480412910301c05c0300c004015000303004010007540801c2c0401c4e8544010400300700d2881c1c00c55100002413415502410402e4501320104500e20003182801080f644100802d42e6190540c2d0904615500c0c20710345180c0f20540d40490702c2c02449103400c408100c0140d1425107030510303603407001842612015015101c4c4c0e03200d81e400507000d40b002805600c1c2d0040b003103541c00045c0c0200c0d60241c0003118943c0340c0031a9140700c0c044150a1480d00d40c00c4400007503214002a0301c1c5507040d011b6541c0040007840c0c2040304015400d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 643741285 1250 643740035 643740043
    0x1e0d12022502180c030a11160201120204090f05180304121104020c03031005010306050103020a121109091e010608061309030509150714030a2001021b01020a110c03 72
    0x1074600d54400c9014001802c1d9202c42420b94080744032550482124109038284514981013201e070b4406860a100d44039032004410010ba5001c0218010400543c042039401500d04d90510f41c10341c00e14560134030000460307004030302540d4522a500720001900e0308092041c2c10341d0041510069072140d004120410400c41c1c40704038642c400d5007207040329180b5528031000501a200c3d51244521a102c007000303101c1c80304805880c180c1101c0d0309032002c01280e81d594006400341e01942d61004040364490305640c5402c4056000007180c0b11115103010f203040303c2100012150783c1c040e81d203c054011f40364107980c2c10381c5490701410702400080c100f0050514081c00000c00c1d88940c10140ca60b02038560512800b010302500541d0031240c00141402260b00c1402d000d42c400d50090301066840d0b42c1440c038822940c034008012698444c000f6610194480010164800140f0300701030080c0096500708454242407650034071104140e901d0071700150795072016940040000320010b03440002a00305040300c200681d0001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 643742535 1250 643741285 643741327
    0x9210409020a0309063e0a18051005120a090b070c051e0a0203060c0c061308040b2817180106030f0c0305070905130b091e0d1202 57
    0x84030250b9a081c1002007100900403064004100321b0a01004501002020146040c60007540401d10350560420000ca90300f56001024240700c4281001200319840c4144142e0048174010540d032421140d0311004214502c02c071000410009001182c07490b58a14084205600003131040d81c00c1c00341c40080d8a80310341009024210b44203002c1c7d10300d03c1030104102400344002200903181061141c1c05040302c0d0503250401180120303c00e0140c000010781d91049030003500c2c94a5100c600800031039035980460b43d01c09041c44000e0b5400c5801b80000a880d9109100920a06542114a01c5c000f190103e02e460400c00d011000e2050182000c01421441032626403103a000074011100802c0c45200805180104943d07040a0441c030000203c110902441c90240302c00c8034450011078035810354401c92602212416640744c520401c141600d4004900c0080784140c11030414025a00384079001482c2019040b00e0580f1040c580d0002c03909040d0759508281c1010b5001a003c40c15440c01011403100c4a41000350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 643743785 1250 643742535 643742549
    0x1e09020304060b031507020d1b021c08043b04020402030a0f02040312020f06071403251d010306060909051308070507091a0d060b0301110d05092104 65
    0x40001000c1c050782d038010b83c1c0c80803005000c0d1803242c1e040180c1030345000c404441c44070140c881e19504040640c03046c0302c4010703010f607524a09120b11086608100c1c4200c1418680c4c04d00101c080703500008a448100148024613141e8003c405c2c52070094901c0c1000c046040b407444503200c40c0c41003030300b407281d001e81203d034070035812100142d580d03981801e890010030024a0741c040030b81c404240402044120145840c242c1d4068086541c90f440e403030707080b66a90703031b00f120300e135000a211001c0945d4901852014640180c00781008203007180c1002d000d42a48402909414005400c0b00c40300040341da070658104e59008420f1130144069401c05401820100461051541d481d40e20000184211900750f400354200b0f91003114550740d007050b13040c01992500c10b801a441d00d01e280484c0007504c600c1845541c0526803001c6e01c4e5140c000456152031004000c2c460b8580d400d5501c48bd072110890b00c0c3c40c0024251200300703001c00611401c209a0b5185088682e01000840848000d01c14001c0c08180040e6404c03a0300c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 643745035 1250 643743785 643743787
    0xe04110d091e05010f06080601031e0305071a0a050a060b1605010b090f0f090c0f060c0703140307050f030405010507150b09043e0d030e09011e1e0902 66
    0x451500c1c1035104940d4182d5098820603010400c200803040d0000c1104460340c00381404a941c0380c0c034182d91180c4081c400200808490006640c948070341c034400b0381b4202d000742001400c0400725100c084e031002c54101c0f800f10032070004e01008183d1085220301074103d49000410405076041104100003440392040c040507042070340000f042000340941007580c0440303000e0f01e00b025904200d80c12042c18001501c4080012007d40000344e25024005011000d00324000c000c40780c4c014244c81441526407200240050034024520b002c0b0100d031284010313010845c4040011a6101802d007003050402a06240d4545650000c000421050780e002d015183d406802c8611419a01c0055405800130314040e8071498000510004220602ca8014880b800280040444880c801c1048045c0d680b04450f8190f540d1041d0380021003510341e0308005d1280340e18503100342840c1141aa4040c00034030001d500368044005941461521400d58003002c1401c402003003032071603400e9076014070310130042c1040190003a501101d0b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 643746285 1250 643745035 643745051
    0x41202010f0215011728021c0209010b07020301020d0e330a1d0a0606050405070206060d150e0102030406020c0c060708040b03060f13061e14060d0b0604060c02010e04110d 75
    0x907040c4100c009030441340c690208190800303d40c0321078421400105a10075400b0105184050148180302100c08d6801089444640e0038040070a00d1500000000c1c0d805650a01070344002154510601801c1101311008240e0840030f04294081508e120413503100b092500786503140100000b404513600b021010314003080004030103400d44036022404a92042c6031141c80012024404141d010000ba0340b8181c50030f0005a44007901030b6a100b605803007880c1c004240c600b044020502c84c002c85070000002400101c1c15a0b4260700d12400d90304151404d42e0255400a600900590100a100a0000e0541e080c078101401138031404114001c40c803031403804800020014401c2d545600d01082802c038000c045000c00803155013807000800b200d00840c628000d540307000301c0700c160803400400200d42ca8805844074072034180c401d024603500100d8054040585554803242141e942e00c01078000b4091540c0c602001013854000141480c400c5e200f80f80c090b510745902c6103424402e030402c488524115000206a4030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 643747535 1250 643746285 643746329
    0x20a150201090c0b0304060606030501080a12030f09080409062103080603190f0b010503030f1803010906020c0a120f0804060509150703021b030a05030f0c0f041202010f021501 77
    0xb4140200401e56802584081811000800614012400341c9020040380b5191402035007140d000b8011511300e907005603606000141d448040c0914148a031078082030529410358001c0076112000c4003102c001c50b02042c103001040c0c0600c1860001c0035107030f40701e00c154413181242d1030708464080405004c015424000509548040140210b580503480903201030070400e04043c003030780c1c0f00303501d04495026500000040301d02c0c00000f52081d1700c041401e0146090780d41e0003100800440703580f03269095501c2d600c0d910003050140c40500a2188440080d146001c0e030f51828400340300c580744d040c40510040d1002004916440200c41e50700036404003000405442d01c800d40391814400c482181160540c0f0800c0108580d450707005400000d200c200d2060142240d842110380328052403c0c1c0e036001032000d00000d480308050311651900071041c00c88640c0707801e00800c40c50361141e0158000421580b042c03e0380d5011542d005070440315000340c030302c0580f0a00c1d056030310045001c2418840d42101011607601d52200c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 643748785 1250 643747535 643747541
    0xe0307150204140d0f17030601020d090b0d020a0306050d06020909011d011802090312041d040b040308060604150302040608010608060f040e0c06030a06060e1002121e0c07050a0b07020a150201 84
    0xc1740d0408100d448a15034561140240c0d4401c82d0340d140103024040c8015200c3d8020035041d01a1500071940303509000413000660001d420040c40c2d001051345070301c000903d41d280d01d180605d040e405490090b030b480380d8545c1070007622034040e8026070b01905078500c07400d502c1c45000c034118191454016010602c5500440c9400079010f00d00420b0b91500071107480810820040c001002110a409440c16071180e60341034011000320200d40107081d1080340f10000740002c0c031861321140d011000500040c2400d48030a010381d40241d42e01e239000086030380003e05100e40790301300d04d00c90f00400480ca0040b2540c078040c0040741c030340f112403440c0d50700458580d801031030190010701162813007800240c20180c48c4d2502d03441c20005011540310344030101e0b081c1034481c20765082c0700301c8400d40e900044c0c00620007042e07107640c845819407041c20604a214400c0c4804c0c115816140e006205100c07410b00200206804c5c0400c100d917100107603000050b440020454200142c071140303071440403150000e201a402d02070300c0300306a001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 643750035 1250 643748785 643748813
    0x70504290f1605060109090b040b07090807030305180901080a06050a0b13090b011d0f0408160503090405010f0f0605071b060804110420030403120e0307150204140d 72
    0xc1c4a0011410740b204603208158981403030300600c2207501590381c40c0908421901a5030f8060802080c1e0310002d0082198500b54039004402c0340341a028559440f100141031003420b030001c50014400040c611a56150040b01008018003116a05015490a0700007580d4aa4104004141d2522000004d0990f201a0310104c01000054180c54078000d20f818440c000b4428200200d80d01460a0000b1960320300458101454144043c104a03890700d070010310104000d0010f0085030080710404c0380300c0c95203019108889646110300001e5880343c50640802081e075105810081500310b1a890800003c02041c503040101c52103424034580d5465241480361003814000c109110540810700005070490740480000c0c495030040a0443c00041040100000e698101660f035001e21181140030503041da6410007190000d1003401c0c800d4480c1e41e101a2242950401c028042c8680c20101d0141c0602003035854648000e540c0c00300851400d4207041d0061101c1a084845a0084001003403d03800c020610009101c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 643751285 1250 643750035 643750057
    0x10f0807030b0604080a060f150e131b080d020610090b011b12080c1207110313030615050a0b0a0305060307080f03180301050f0103060b010c1a0a0507050429 69
    0x10703684e0317203070040c040d030711004840104c4805c1d10300b5002c08401c1065104603481c040070b13601100d400b02c0c50085244482000903120000300d01c1100301d40c00000701601001c407141c520440c1400c0d01c091a1203181c0d818403000c090b542040d034119804100d580c68030426080140c0b80c0700c0500103500010500100e42c00807068080c604d0424015800c5820f12900300c501008211281c1d680c2001595047c803002500d0269028180d01d400700000072900d03440c00790b841002e800314940c044900b000c901c122a4a01689154019540c00741c4e00e84041080000c846c0020000d000103440803d040792034400e81c0043c0740319800d03e1408043e528030105001390750030b004410080c1a820100c92a070b01c2910501034a031343c0310900c00c2c400824803446a40c454201030199030311600340205403200c0c036031031030310b800e00a410504407560402850b851018001941030b03c2c4080c40c0d49801c003801d0000d14051182d03030101e51000d8402810f00006001c10401402d00904000c2e40400c000d0407907840700034100d42c0e40c1007400b400503001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 643752535 1250 643751285 643751287
    0x40c090515030901150b04061428081602030d110403050a12030501060c0b0601200304080a1205040e22083108190218090a0303050a0b010f0807030b06 66
    0x4a01d0701ea58000b46000f004a00300801520301040759022900b8910b12408083c11028401008101c0c020b00700c01d0752040040950034540384041641c0f92180e403082e00c45000814003504814040e42d0300000007544170504000394000e20744540c0700695240150044403044c281c540411000c10403501003502d004562000031525207000c03e241940500e00c0780889800003034501400040d02c41c1c4242400c6d182a90400c1c0500000c0d19103400440c4c0308203c070031005c6010490445240d448c0e42e0200000c10040404201601001541c3d2401c4031716210861900800c1010a02c005d1001c0d0301d020f502c19030001e000401d04d2040c1c2c0341c0b14408044a050717424000d0a40c00012542e00c003000303c1c1e01d031180040402c007802d48040b100d00d40c0140350111654010214154030120781c1d03c148020940d2142d04140c00245080780c28074070f103a07e41d166484101e41014070f070b8209400c5401016054003900d9040a0400c406209900c40200024184040328a081042220030000701c2da80600980c011b01e41c100c0c01400f02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 643753785 1250 643752535 643752559
    0x90f050606221a031c1106011d090c100c0213060b0f030711010507111614010f091502012304170306010309021207060f02010e060402010c03021009200607030e040c0905 74
    0x42405c501e041c030307040f001052151840400e4904086101c0341a00c00b03092603000c0d0207690040c2200d05580040440c403240c403e50520590036a9080f40481e40c07840e4a0b500d8038400138003841404040b018102c1d40b00444d505101c2e0601994605d101070f14408241c0c482e0040d107994400804039600740030044482c64135460041407290a0303602c001000d1040b400301d001c90385c1424020543c10400511845200c0f4881d05041c21102e4641c40380a01c085d0f001c480345040302c600d0381c4a60150b440b003040340c00b1501c0580c1d521800310303444050106908540e0365111440400502d4107446410003800840c2c10140b6054000001408076802940800c2c8515000b40807541000842d258144c2d40b0f00c594016440820305000b20b43c1c00c001c1c414012211444620303809040141c4803035005503428119000d084055001b500c1100000d49268800c08003054000c50b820120341e020402c1440340c0d1034842200e9402902e0820030200402d4106e0054007040c1000e4800140710350640d0001c0722070345290340005a218030354000c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 643755035 1250 643753785 643753813
    0xf0305030403020f0105130614071b080606060c07050603070309120903031107030f170f03090705180609040f05010e0a03030207060b0904020108070305040312090f050606221a03 78
    0x1034400d0b24802c4c0c6404c030381ca40840006407400e000701044041701020111040c0b01c0e46124103885095820003000307032420102642e682c08001880c1021500c02d4581007a02000241001c2200c03c1e00007a003941d0726850b101d001e920460b250302403409807a000340c40000c04501d00f90310036808100980d03002210006200483c2ca4010118000da1109800081060070700c4415104c000c80c0b06c030116075114141c03030b0300c894440e40c8400b40c0807603005224032403600c1805058800360001005502c5550260b016100b807608100802612a01109907186ca0307010850800c041d87c0c80d8280e002c0c0e08182c1001c02c000c22a280c924280d400f411000041080c5c0e4003070760072003908140d050b40180c800117100300c40074000050484140301154000701e8005c1d0005100340081107680b4000d902054101e4042e1805141900084d140c40064807806401110002d00851a5806200c01841042e80044089403c0c901c06402180301f14421400610444412981e03809800441c002030422100340c4940902078400350090090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 643756285 1250 643755035 643755037
    0x90a2301090b0f0909040204140403020f0d0306180f0b0303220b070209070807052512110c01050903010e060a0207050706030b03190f02090c0309120c070506090a0f030503 75
    0x28090116403210804910300c060390042d41d00c0300d40c002d03110b5410002d4040c200400003a000c1c2003a80c00c140c1c0c0c0c039a4240d041e080303101010300c1039000390001c1410042c01010546000304042c802c1c010546010410700c195117180c05408900c41d00300402082030381008030404014001001c55940c5884001510401485a00800300d070904410340200d85e015a20441e00131203100b080c1009602084040008030124060958a0381020041c504a8140071464802d08110304084009070546000c80e03800c2010040a00200c4082d1100e07442c02541c0c11040e0030703c0e196240c503416000c6061250104142010381c90941c4070340c409490310303001c4401504007285100001c1d8008041500c60b8080e12001203141030103800380800e9070b0300c090024207408a1031404888008001c02089441c1c0c020000c559015a842c104244d00030500400490350340d09040380011701d01a044c40d00b41101c4801030066054148010030034808841050301c0d22665058100b0006032115056003102c55002100031001c0180030b4000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 643757535 1250 643756285 643756349
    0x10c08010801150b0403031412090102091309050607050f130e04020a0b0a0e091905090c01021b090408030405010605030a050f070605071e02012010060e01030314090a 73
    0x20002c00450312070f4100e02c00c0c502c0890280681c41c0000f0441000000e116000042d014084580e00c18100045081d01c000031036001c0d11f142913507a401142d410401d18155030400041c00ca03035802080004980c0d640c1303a0325110000c0c2914240072002c5003c030444e500260444591007034007589583d1154544010b8041e03110262020f80c040e00350104080742c000054400c0300d07141056510390b1240035100104100700802c0c020688441101004c110304440e0201c1c0c003481c1d0181103200086c148a0f0317101000285420b28030000c0000740800c0010b210f405032158842e1030f0b0003507000400c0558917541c5082c1940501035540c0660303054030810700d8480c01d011000c2080156170352401c0642d01000e6407000f08880c14020f040024200c4081c030340400d2421084c0010110500b88181000c403100c031082c10b210702d180309840700f000e0a6500304501c000b18004903441038001808550400350b040c3d5043d5180240785d0040040309141d0f251000840a45564507080c0140044c84080030304034040200e030241d005080e41070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 643758785 1250 643757535 643757549
    0xf01030f141801090b0a02070305040302060409090b1b0403142407030606050a0f111c050c01050a0204081906060f030f05150601021902040b0414010807120b060d030e03010c0801 78
    0xc60b9241071001d0060203103031422a0021080c80311601d4015540000b035000103070840511100300070010050301d03203030042c03c024038600b070002543e12054140491800f03002400041c01d58048502071a4410141c020780d016203402c120740c80d00c03120542400da80342c400c14110000803003d441d40b5030010200040b2050307200d1045540c040c01140d41d43c6000f640e548c01511541e80211b40d5041d00f40f803d403441140300340110750f01d9204035140d42a4500f80c8120101c00c041e8a54001b4200080c3e82d96000801d0080c2c0307401440d400011842e2520300182141c90b0014410b607070784104192203201e018805150030a801800085141402c410354030710304051421310700c0c031044545014145008242d0100c03000307042c2c8900b1042e0043d1001c0c1a504696054501e240b002c03c0764400c0d0340c0c081403411030700c5070707c0b412120001d142403400e95541014041d038903100c0c0c290b1122011441c08030052000651500f00145c0081b41919446000d0303c60b468161080003001c5021500340d03103005034250340e1541c050701030740c101d6a003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 643760035 1250 643758785 643758811
    0x604090911100806030a12030915020a030e0a021503100e090c0a061d04110d11040303030b2211040513050406061514160804060306080c120c0f01030f14 67
    0x1c80c080d60340481c100c4d2502c1d4181c00c07541d00324000c150017891144011540e482c00081c00400d41e9500150754a0303441c803d2001303907408100603105582612448101c0c030294001803020f031340d0550010b0302e110340c004d0307405414070400b002099252a0b2103101c800a8a80c91203520700619082042640d9180c000444031310a1034102000280c050251810403020baa07900040c082540601050001a0000701c028006500041003c111400c0b050302c01c4114001d0485242503a40349503090060649114583e0240704500b603600c41150b8804031103800c400c00310802030214003810074240c0c90070640102d51003180c010045c5044c40c84048050b0344282e201d2446140c041040c2c1d9100d4800e200340303020424840303000c1100c0040d00e509109140c1c0240500440400c502d03400942c003660344003515009a072205011075200c850600c2400021701c14401901c1781a540c48158400504a195403030b092103d0b014012142c9103071128035a4441d401c0a1080014100d061049861100b1252644041228070329240a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 643761285 1250 643760035 643760059
    0x3090201080a0203010e1f080d0e090117030a0f090306090f05060a050714161703070e010e0f01080a150b12090d1715030a0818010327020604090911 65
    0xd610b100791382c1070350f4940340a0159070340d800158a50004120012039500e046480001522104c00c02400010408a0741c0d0002608400d00c28442109011381101c0012440d2a030314180840c0c00006645005040385840504003250390001c1e1407903030280d080501821305000b01034041c070841d0400744001e64401d80844005540b0f5184203001c0301c0007555900c000881c0c400618003613411907400791a002a2000b0110100030383c5030380c1c1d80e90881e0301c6401d007104107002008004030140c006044201c104800c1c00c1090fa407035060300014000001c200b41583c148003034070300890031410b40c9600850f0300c4c980511040b102680c4505d00c1c203059070011b070413800301528104000b90080201081c542054603858640c10f0350131302d1b90f002450812030010100204640140e8104045030740c10440c0130030140c00381d580d680d969441030710030000d100100d80c039050600d420b0400d242110820f410400800041c00c0482403000020f52000500d47e2103180e00080034941000040d40c2800326520040320204c8003145c40030b549807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 643762535 1250 643761285 643761301
    0x507170c0a030b03150411032b080a140c130518010b1605030a0c030807050702030a110f03100c0801061d01120b0306040c0f06210207170403030309020108 68
    0x800480d031028920100344000301007207000380c02811a440d001415520500030369400210f03101400c0324203a405032042c01809003282414000c100c212601d501c920303028004241d4084003442030004042c02040f043c540058000400307a44000310210010820080b6030a00360140b030983d410180040b458030454820000e005d103000300341140544200701044120340e10b40103c2d00301a400000c5c030003425110300c141010010b14188024000014070381c4820003080954100200101c400401400c00d020082100c0d07400b5a13070018024114980c400280307100c6640300710105010b42c45081c143c036014072490440300c99410181d08000c103c0400d9580b410b02c9a81d0f10703103007103904010030104442c0c02c016543d252840c03940f09900d6403c80010204000c5101421000031034600901150b054500c0302c19001c1c00e2100d5a1401102c400401e03462620b0b00c2421005085090041400304503420135a5000139110208000700145404000c0b440080d181c94540c0e90030007070054194040200d00203900d00c0c00042a078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 643763785 1250 643762535 643762577
    0xb010603021213031e230c0303040212010b0a080102070b09070b180a0f0e090f01051620010903090f12080f03070e0910171507051b010f0507 62
    0x40c40c1c0044003001c2c281c030f49600b1010580c80240c415002c026041d40000310650a295008900d20a10740d6421035600d015011310201001032400485540c004002d000442030000095a403c280c044640001c0c0071100c060702801000b5417000d55800c4008034000094502065000e4075140340940481e240c84c0c0c4d50140031640301d072002d01400e00c5015042c460740e0400b004040f1144c080c1030015088007051500e400c94480d926220364840c64840c2c1c420b008200f480c086c2400006e0f50303046a00002d0040e030911342c42d9150006080407c0f0350401c0010b105001200c0c1c9441440b92044038800c008220303104081c10003c0c6074640701d000355902c0d0340d00b070b8500042800710f81030f984200c650441d000ca401c0c030180c01c04000850303101420010802c42100391000103603a0b03a541c590b000c0c02001000c0401580b410f0000c42003414044070340d0680390090503002410200c40382d20340b6406171840c034000d6615000001180c400c0c00084002d4100c0b5881c0c0450340c04c500b155030380101d000b841c05032100e40c1d503ca4403000181e12 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 643765035 1250 643763785 643763797
    0x1020d0b12060106120b090c040503100b0108150102010204090e010615090623091005091008010f06140f1204030806120d030b04060812042108180d060c0c0b01060302 73
    0xa60340c80b800042004d203203c2d410f00d00e4880441200400c1504981c000039102e90b5040c0c540e0880d0500020342045145000c1180c404a1001041c09100d5000a40000381010340001c0207829100707107012038a85540e200394100c0c1c001e00394241c003c10182041850484c020400342c050354912040e8004c801019034000c0300250220b0b0a5540c80b04940c0703511114410541802d4060900244c0302804860354541c0c50040c100d501444c19031f5041d4480041804005c180c1041c943c1c00310074420300e400188104128004141d080c0d8080b8148003081c1c0c1151101761000b8031841454040741d40c4041000c44140e0002000e40307010704d00903940c40d8625203810f01003086141c841303a001426a88443c91201c200d074000d4100c032044180083c80050965900c582c040d0524a0000310385190344000502449001801100801b03a141c07a0000d641007003100b030342c0e0001a0300c01c00f04245040550f440340c034822a07071900c41041380107074841c000b48891a5004d00103810240ca10b00115a540344071030022900c18468425100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 643766285 1250 643765035 643765069
    0xf071a010311031c03020d0b120a0303050c0702011e090b19091d240a031a011d0403030f091a0f060405070c1704090c180801020301120320070801020d0b 67
    0x285413840c0c0d0605500950000c1502107526444410003016942c41403c0c1c840031040800150501407814038009007240c000512480b00740c0e4003400954003503648140050a00c80360f4058a103401c45030440d099a400965502c0101e06e00e0000400854020040c40b40c0303c01d8801a07291116044e0302d07030404040c00100c89181c0603403070062900285007021000501d003210018122000702c201d5040307000c1080c00d41290819124030301a0101203142010440c8400d00404020000300120030540030b03803001c1000007070005020940c80c0c0c501400b0002c03181d4454050103500c214403491007c004000c3e031035181d0084a2034015100340d10b00052076414075010b0244036010580ea90070518002c0d0740c4008000b2050210300401040a001c0468100080e128950004919444030780b11841844504140ba90440d004681a41d0061004000c1d02102102c10380e5055858240b071240030041c4004413540300700481450005101e500d00008040304194001c001a041024003440751204000c01e004005980c5d4000e42 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 643767535 1250 643766285 643766323
    0x60c030e0f0f0d030903020613050a05091e191d0d03050c19021c020f100204030507230405240301050103050607030c091a030f01080607020d03020f071a01031103 71
    0x48a00e046052069018070174102440b4040d180e40100300b113074220f007038109101191a94244882e18103070300f12000074082165007400a240000006a001b071010981501481c00100864400b07000c9000e9000040543c0d1810043d000c61070030034120448038140410120b014040048100030b21034002c16108401d4120020300d40002500803500e541c50085038503045018124144411114031007282e41c1240035640103003002c44900d98038604040769044000f140b40d2040008200081020900e072044410071040034000082e9140c000e186034081c0694a9413041c80d000406c000c12240c01e14412400501018880b0400302940034142246d03420702015200b5440710b000207402620940200c07250780d050349480800c0c1350b92054040c400300c0031150b4900d0307025030120400001081048049004007407400081c401403c003903c001e519103a8030301a110805400040c202c100b5184442141c000581c016540181400c84000c10a44220280070494180d81051407840b05440e00184130400200503038414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 643768785 1250 643767535 643767559
    0x90e090f07050613090207060501050a080a0317070e10030c1206030b190207080703020622230723040f0203090316060f0203012706080d050f040807060c030e0f 70
    0x900d4112004c0d0807900034220030003085010042c0007034096913102d0000840d095041004202508880740c0104000740e1110560402180c0d110301550300c5070340b00205400242e00c500100b22450880e02c880c80c4e82180041903003003210f81c1c7c940e00111516159654002004c01c031503a0400c1924020320002d0b00c84900100071804007940c5112140b00814102401403030110135683e0510582c00c421410380140c2c2080c400c1255101201e4100c900c05d43c21b0344404000000143d03181c01004c62100106110303014103c20700b54070341701c0c00c00608003d0032828103081402289030f545070f1000c8880300061801203003041172810100c0841e0007078070302480c1c51074081d604103802404490403207030b500e000543d1519290851841074500030720055020346024407900c4940c40d541101c0c00d02d0310b0720060080b0203c03454000208028800822045005141407420b05d584480024280c0ca841c05140c000c08580c1c080c20f100000c1541d00110b40d510001d00c01d44078061103440078420003501c0384602410301d80004443c004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 643770035 1250 643768785 643768789
    0x70c0305030c041a0304062d0b01033e180d15090303020a170c03130206070204060b1e0c0303040303020d0e0a0b01080c0906060d020a140703090e090f0705 68
    0x141d41c2c4880184421030a00d503660a213261030740c03840070403a0007600c0c000041c0800c2c4660b81c0105800c9030340346481c5000381360190368140d100d00a107181640d03c80d59a4028200d090303200340c100b851509102d00382c14402c5804c0309140d011660310402c40c0b44444003c0051090309128200582c0c0301130b00c82d80c01c00c0c0c00c003120240900c2015021420211140c811030310481503100c1f1284141c0f0310032402550010303102c007240400541511400005c80340c20486d19000c10074000c00c054210780d4002c44455011035848494404142203000301d8800a5015050034ac01249281451001d041d16200c95801141c2c0701d500032181427902c0c400c086503002160001c00c0041c0110f03004c0c1d0010031000c84800c00000b0000290b140305814040c03001030443e20940404010040000104031020040b01d0440700100300d07061800001c0c62902c00d950500c0c0745c090300400d0f01544640141c481d40c0d40d958240c1602d0742e603000b00c1d24004005c11907902982821110840c04141e200301d0008005003001c0803040249071507414a82 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 643771285 1250 643770035 643770037
    0x2010e0a0f030e0a0306090c06110f070501180b0315030c0a0f0b0a05040b0c01061514120a14011503181104050a0e010606090503010b091b0c0c04020a020a0c0608070c0305 75
    0x1c80d50313030000e4200e4000030002d80c0b64494180502d00aa650f0184642021030003001c10101e240c1c03a41030b95200c540040c59a50340490210200c8800b402d001d248610481c8200482c101c40364080800042c010040040002c1ca190204e20b0414007202919124050b0340100583d00c89640598015003510100502881c0c1e24140101094845410240d081990f030b400b00314003a900a848290f00c81e5101c000400030f120150460000d50551403d010310742c00c0107182d506d0058054030180d9517654144a0214031f60360310030350050341925a5900c0545596071183d04100c05150010720b0f01d00080c0c80c050b5212140c502d411841c4607026448503520719414551020000540006084e00c2000307540ca4425500b520000d11401e0010701035925002050381c03400381018215510122a6801482c0001c20010012a00c0803400c600c10039070b034995921a4800340b0801d107440155110b09420901c00100d400d103454000901c00036680c41490010030b440d0310307020100d0f100c4505447e03140101c1e24001340e140009020f90 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 643772535 1250 643771285 643771307
    0x4090902031504030e0906010f0e0f040b0901032954060919170d0c0504090b1002120c0c0a1706090105010f030602030c1e040602010e0a0f03 62
    0x60440780e405030040c00c1601040b20581d011404214241102c4001d030a11007004e6038405401d0801603c004000701e805007030042c0b0702201501c01c0302c034114054065aa280c2c04085000c0d0f0192203245103603140d10346045c040c080c020b0400300a0000c0700704145a2005900c07000d202e502c0b030702c0300d041c20320300d00351903c5840d0034810046040c1e200c0020b86d0110100411b072642c5032036100039855601003488442d83d2909010016042490a0700801c41c2c580210390245a030550056001c1c0c8282c03032080c0e10010070155401403999038580340e820051148122030f884400341c410764921050402848003840100f06502201c0302d48e20015070003251071402000e84200182c105040c0381e2080eaa0543c4100c00000c480216a0700020402c0b031200228400900c0f0812041e507001a018000300699410402810001000c1c4e2100406064000000404800e41d001c00e0301e4643c2640c00314030a04040c2e2903c1180e0350382290281900542c60a45907040e0a0700c00522800303c02c1d000043c0492130003c544007162011015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 643773785 1250 643772535 643772539
    0xa0516030309170901030e0a0b181204090f0606020105092d070815011a04092003181018060216170909100b19030b03030412120c050304090902 63
    0xd01102010415902014040320000c070f440a96a00b004000942241c0c032250480a10350700014031080003801400c0c9198005d0b0452030a07030080c004070340311689000d040310a9042a840c01181c00500c50f4010342082c205c001c10000d042c07050503240c840c102c0c00c0b0307803007141d581c0d901d6440300360054074660044c013003006c030394130b6405881400040c42c02503a40340c03400d203502621440d030158075200040c031807030039090b0f01400e15040000500c00c9560300c4c05c1e41900490040d0999035949243c0e04020210a4400d601c0f6a010520ba140d00ca15014104d110a40444485115140202c41c5030703200c0310ba15880b4510401c1505890718803c1045604c41074025007020400c9944041d01e03c85001c0800d0462145e4103020b408092480e5442c140003003803111440300031b030610158800c03d60081c00809800c03401d5907141041010b03d440c2da80c0304400b04a0107441d03c090560381600000070049100031120100c1072003c0d01510403c036200c002400102c45081d100c20002c0e1440e0014041070000090320f810400c6c0c62800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 643775035 1250 643773785 643773791
    0x608071e050a0c05010f0c12060504180809010302041d04031101050106051803010b060310140a06200109020a060203130f08030406080912120a0b0d030503060d0f0c0803090111030a05160303 83
    0x1041b6034101c0700c900704054007080c8540f0788a100c41c481405104003500c0203139800e2085030511034001541d5201c0c00303002002c0090128807000f01b0b92203541990010842d41d042d820969494441074285404190340c04c1d000945984002460001c05002c2c4038100d03541562050300e44103007049952130300c4541002995040d501c4181841c1d00c0e6031410050742c004e0701d0354003200454030314152001e0205200802454000c8000190811102d508800000c80e43d1040c120004e0410300c0e109640303401403401c120000d621084004010070081d500201401e0510b01d00d2031082c2d484d13a100c5850081d185440e104000880d80104410f220040c410036095401000480c1183c55448216100c2c4000f80c2201071200e03c0e0364160410003c1c02d441c00e0054005041041d40c0c80d03c032041650b1001080d41c0f000804090140300000c0102d0300300428001c0050038117030000d08403904c207900c1c0c10340b25840c1d0b80103190a60000c0c02146404140380c03400302c204d4a4002c0680c0f41e092400d240c030018801099a6240d054041c103039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 643776285 1250 643775035 643775051
    0x309020306064510081513110616031116120f0812070c17090d02060a050c06130c050a0f061b14010e06100320190608071e050a0c0501 59
    0x1507040f0340140100d10400b2041d010600785580c1510703010004024501e0740d56041c0c00e11000702464030b00702c48002d030841c01d140d05440d40040400c00c10702c6901904518000244000c00c1459800302c40107140e82c1d01c0e20140e500310440c5a0100311290740d41e02400443c1c4810006071800504000501c4204920890807103050600900160303e4846040700d052021680d081205c404101070400707168420300000302c1c0300b81000031f0040032401076038480c1c0340280240c000203812440c441c06003040c0c944141311710003102d00610705241982c005002c0705000320390300c08000c0d00114641c03a02d409414144c0300c060003010a041d14114040783c0e403032909109248280301c031440710b1000c50f0003504442c0045030090000725900c512800790078239000d0020980000540c1441e0309100050300380d0b044668810360b503d4420200008035000608801c26880e48046812080c800050710701c0e000f002151042103503480c0d4000303001034116020442d086141d070450010348100311000041c0d00075412a034040c0d000b80d0001038259 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 643777535 1250 643776285 643776409
    0x1050622060507020312040620030f0703091703070203030720130507080114010906120b0415031202010c121a1215090106030804050108070519030902030606 69
    0x200caaa04041c000400c0050340000f5030804000c00e041d4401048640c0d8a0140b81c00c20040090047d10407030841031540c0e040c554080d400402c2030b034900712903442800d0380d1200f942c90058000b1035a071140256101b200003100845040210944422640203006903142200a036115804000c8616102e50004400c91210006480b0034894801c82000c0140005550420000203002080160b000c907140c101e5080d9103100e82d076032280320802120520f04051800c480c680c1c10042c060078400c01c50b0781d006481e0140798401801c0c048090011039024a050040200600104030700f660712140d141c00100b2900b03207036012001c019a0106003c42500034440526101c904009410311132101644000d0b98001d0121013900350300003d145070415008002001410b2940d0345c5c00d80c09001307511a150511640d400005c001f075000d8411280b041146002d04000408152000740040150000a9000c6d2040c403000900d41d01b001061401e4032001c441019138050840c0c2104942c0f4803650703840da4031000e0140e42d007139080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 643778785 1250 643777535 643777597
    0x10305030405060c070806011215060602070515160602271e06190216050319031b0519060617150604090c0e01150528140d050a11070308010506 63
    0x17810700303155041804107243c14850481c14ac004041d212852410038104829a000140f0408440080d034080a400030b20044d503104a00490010a00703060440c120141041020350041c101000c42a242c42000c212922440c404a41078540058011f01c404c84181040003403070804910240700248480c1c0350900c4c2010840703a61100c000100c01513840741440d4031860041241e02d101800e0294002c1c40481d101c04a41e40e8400d28410000e000d20400c090301d49103020240c03401940170f6401008803081d41c140091400c2d110340c4441016602076242800210f480c201c045644400c81d0603050045c640b0645c01c5000c6040b803800a030080d54019510210140002c0003600b66a0044c12501c0512000390300d0400e401d00a00e02c040066030400c50b04200c2100043c541c0090070b03802100c40b403045100c80c0c801c20230645030580512803070a413144020400c40c141c0398281d0017503481100f9080040c031600160041c03005140c01a4070004000c9603003400180418144035001c1c0082c0700441c07104058456002d28000c2c14 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 643780035 1250 643778785 643778789
    0xb0301050f060d1e0609020f0d1a06040e2203020d030510210b070806031b0102120d0c030c111002030a0f05070f1404030f020d0303151814010305030405060c07080601 73
    0x3a5040140c9803e007213004074491200240300c0d0181c298688100d50300c484419105a1200a82203540c8100c03106a40080d04130706911514040d0055603615100c41000b02c0501045821500007a14001510201680460409105a0306800030841003002c000f00341c0c01303081c005103030514040501600080181e0440103560072640d90401c2103c0048803400d2080e4203160007800542400381507024041c031074900003031f0341400c6051008000d0706c4000c5400100d0415001003007400d83c1850214a503070b28442503600500072206a500d00300441d21f4031300000c0c1c81803042d1ba640c1202d0740c1c001162102c0d6005994004590111064000003007400c0184451021108103691074400540d28007080c5542c0b50700208031900d490101803075241001e00d10790701d185032000d17261310082c0200b014001500425019400036891040e10011580300c05c0e0b100d0a05080c010700b0900112012800c00d041c0c0320304140503100301d42c180c07900580034518181c2450140140c690151903480d00f244181c11001412203018864240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 643781285 1250 643780035 643780061
    0x40203070513050d0c03121101020d0203160206072a08070b0105010207120503090d030c0606090506151e0a02071503140f150909010f092603010b0301050f060d 70
    0x34640c030601e0044500b0004940009014800d02d0000401044001403600308a0307038444212030344a0081034080f207070011820402105036001040c060300d659507a8014611580104520314200914900221707030745e0100b4ac038803001045400506000c1040182c40440c0f0403a5601c4800c00c6410007541e481c860b03a80000b4099030340086800040c0101c2d82e060126100920015443c0c2c00a007199440312070303e0b07100740c8000c148100da003100e98104240c040c1813400c5415811031010403410356229031ba000a04804c4901511512210000d40810002d400540c3c40380709980c890065500000009141960f02407580001540b00d04140026404046542c1110910040d83c010992900b0040340c0c840540d0040d080e01d034880c445e2001c10500502820030518914012140d0b000c0f1070b12004680c500500c030b01400526400d0400d500f190911407050400c00510341001152802034804c006400658042801000b036848000c100402291410480c074a012040c002c0405141420784c0c402d58040f95801d0001c09 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 643782535 1250 643781285 643781287
    0xa090f030c08060106020604050c010503040c0909061a150304020906030715020f010b0a0e0a0b01050c0d050304020306060a0e010e04051218190503070b071103060c0c01051e01030f110402030705 85
    0x200100c4403e10040b80100b20030300080000e4103144c0e541d107481d82481c058540c1000000300004041c400c00c1c105080003040344a000704001155405c0c01c402512031825800c0c850184902c0c0c0100b03d0030920f1032240f0f1143c0150700941075427100e03400c000c1d4a000184c801641403085620200b0031481200d114203071507203e038005100552160b80c130035081d110500c2c0354074840c02502d03004000c1c80c01c20024140d40001400c00c0015155420720060b1014002c44294071800e11455034004400c6030410004d60060b80220100c46156440a041109008040c010040e41401020040085030140c1031200d804c00d10480c10350380c6e81d1b001c04820214a410101e02079041c0d1441c2c0e4181782440c2040c0b10034903050940707590184500c50401e000700741e0703d00b13951003030303108000c000039410040c441c849004001d80b84000701038441a00300f421138204d007030b00080e041e000254601008194281180c607103400b0013784940740c61300141e00e540c5410051101e8440b054920858802d90700d4416a1988001c0d44503c0e802d0b01c0d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 643783785 1250 643782535 643782539
    0x415090b030303160f03150b130f05030a08070327180c02030316030209040c0f080a0c0c020f030c121c05030108120f1207120f09030c080a090f030c 65
    0x4080d10480c4214900030b03002001132146640c00d21090362100a550704003024074686126013100205005000c01c07201e1072076458041240c400000043c14901d02c450a0040700549418008059041030310038158075600608042c00002d080308003400041c6c1c0a414400c0f191600705801c000002c0329100146008941c00005000088090203a07519070f00c41c0e95000c0084c0859000c01a55030300c40582509820354207d200d03450b107548250120703910030740050070502c201d10b09100003500d541036200c000d50115600c200010075102c4d40340306c2d1458080300741c0c0d41c00c00041d04940038402024411030055416002380309505161361116000040712042c1c010041c000c0c00ca68551217901200541445000c2040410042102000c00103404940d04010601c4580c5ca1910140c0c01c8620300c28043e0000c42c08400e0400c000030150088040e070482c41c1c03201c00500c121150030024a0890703848c110020701182074100b18070045a00c4002802c4510594204948225101c0707000c24034510741541b080369111840d8400b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 643785035 1250 643783785 643783799
    0x1f02030a0c08060a060e0a0b040902030703270215040503010203040c03110a0303140a0c05060f070e0d030f120e030408010207120306050a03140c370f090b0303090415 73
    0xd4910030007500e2411400310305040d400a159a0218800e01c0d08101541403000355035620b504140c001000d00302d04c0b003030390b03a0703950045d150194004031904c10101e4034010044000e031040ca0300c0c000b5800d00c4c000d146507090b40c00382e0810a1315001e10a101c21030300000d11010410740c0b000d1000b54080c9000f80710720b07020f082c55468600142802a45401c0c020ba401030b49c1040040d4010ba51401c07c0c00d00b0120050301c3c1c400d00d0000302d90031303040c004000d012031044009100d0301800c42c1c0c0850740914032a59865120408030820b0000500707500c6030090000c2d1501c1e107010b6400d88108000d4882d070f10300c1400490754511700c03a402031841e00b0541124017165400210b25080100d010a40080e035000c1b03041c10b00c400c0e440c10001039080d11f43ca01c00070f4240a4041070400c0352150a2003140441c000040002c2070b10621030343da2814007803c1c016042136900b40c54000c0c5801c01c05200300b040440d0404400400002e0410b03548078042d001000300d1a0305032005000f211290b9907070340546a2038401c00d0700350031000c51401032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 643786285 1250 643785035 643785041
    0x60804020a0504060518250c0b0c1c0207210203090405130b041b050d0309082e0c02030c060a05100e070507060504030e030d0801080c0f030c121f02030a 67
    0x403042c0e00c250300e8510200000c3e142d0444400700d00851248440b00e5680e407041c44d020300100c0d4214007014204900c2e0819007643c00800c40c1c2100c43c000c02e0400002d940712001d000080c40b491148002c1c0380445103011110780d54a400030080d0512500b8008014407a55101c011109031001040740541c00c0030690208904003882081e60040c9a1805c41280b04240d45071030401030000740020b098a80900b07004208030b00d591100c24000d110190038115040c1e401d05000702507940a01411109008030b20004000219480e03e000300424020100c41d154000081000d008280c0c0300703850b6042d40130510181c003001c0814401c0911a00b03401d2404129480c2481460041d58055040250784500328414001e00030f1b406010b507104240d0010001442d0303220340c1010b03201320300040512640361042d42004410558801440ca049648101c101c84140f840081001100d80460040381c1d090786c80242040824500385045056044c40c0c0015a001800c03400c1d01400d60540c0902c10f50034040d00001840794002c0300344 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 643787535 1250 643786285 643786289
    0xa020726190203030a0c0207030c03021507051209130b0907080613050c1306080f04080d0621110301090809130209030d0c0512030103030509090603031909031205070b010b1c0204060804020a 83
    0x21014003a81425a2b40e0100e04031850300000e40281812610303125016a1002280d00842c0c00070100c5000c2e07801c4000c0d00c0781c43e0303011800d91070280440c42418840304546029099168900804000503556851411100c1c80c50040456500141d12050780007600707450710540d4003c2c1800c408a030741d00d01c0f0742007907041d00c011603074810001c202c82c180411000e40c440c20749803a041030f4000480f07a92090a03035410340180034180c000700a946a4104803044500c10904c805d42030a20540080c11b810f1101c0003058201c80c00e00e800940b45c0c40c1e00f00003a8000345400c00d501660051101c1006050951038404245000380346840400890070503010710060100c20081b0540014041c140b0519540c15543d004005000d107040d1b0038060102003001c288556414010f481e0484031490043c115a4a80d2030014a0300c2101d00c81030328083c5044000d02d00359031007102100e01035604940202c030140d01c0c04511444990141c03e40e03803800c03000b00484034440142d50006000402c0184c0d00d0300045d00f40703401003100c085025 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 643788785 1250 643787535 643787537
    0xf0f0605040602120706021e1e09010504050906120609031b070f050d0f02100903020a08030307020627030318010c0801180c03020d150303080a020726190203030a0c 72
    0x1403200700b08050340010350000101042d145075464101510b080030203030080710508501117220060610928403030401400d81041c4158140c443c00c6112075004000c0e00c40c00000e00d0000c0c00c100b10501140c1424801250000006400b21000000e201c0e01d0605042065402d44a41d800005400303160403819035110302100110380c0501010b40c94121b04120100703041c03041e1030161040a81a0080c0901c0d00000908190064005c0b502c080088030002c08489503404201d226034050003012072185400400e492245040e070b0020039807520b1744040800d0060580c15840807854000c20181c081c040c050010350300402030000346448140380d8000c9a401c1d200b8480611f020002e900340100140240032841c02203025281c0d8000901181c3c480d0100c0c060301c21904010f0f220350a0902e2902c01074011031012045030302a43e100481c0761104d0604030145e12400c44003500c200c074040489544098000345404075140d01c0c200702d5140ca1a1b210302500d40b1802c00150b40c0251300007208200107041c850050f4084000f0b6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 643790035 1250 643788785 643788787
    0x7021c08070e010210050108033414120a02031902150f0c09030115090b010c0c0e1012060c0908070501050318070b12241003091502040f0f0605 63
    0x940400419103400107200c4010010101e0165070709034000d015140d5403508014040c403241d038403514543c0d500d610202d503400061407c107071203000e4200c049034101d032030381c4003c00404503804c00b5440e101c02000030104a980140112140400700c1507284000346080b0500381c002e96200c001404e001446d0f1140b2201301d01c1903401c0540c404000d1802c0580c140d5000803020003030a02c2c0c0c1c880d80c40c40300c030601988909a4040d0b20700000c4001001c800c0b04040f04a07454060240b00c8554048011541c1c0d0050003002080e141d01c96105000d070408600c0980e52102240c1592107409035500c40e04c4c202443c05010a480c9180e5421858910316440162100a40036080040113040d01d4200028110b1100030a8841a404000341d172041980041c0704060044c1461440c140d00c031480400414075401e42540c1400d00340d04407603030030588001c040b07010f00b40b80c2078002d01c141c1c150006106c4c15000341181640864202d15494460001c01c4200c5c40680080d002214085a810303040c45440c195400e03c540040080c404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 643791285 1250 643790035 643790083
    0x3050a0608030703033c05251d0603040b1503071406030a0902030a030f08070905011202070303140108010c0201241707030605040624150309140d080702 67
    0x1800400c54503400c1d1305242c0050784c030f207280400d034482a00800c41600c0745000c6400a101e00c2c0c03d0310141490b09050004204410f407540c4481c1d500044d2031f11081b8010044000480c0d04071805000703001406000f81c8a900c1000d8800c1c0005a0700341d01c00c42c1e041fa601405242131100f030884c046800c0c41d41c92420360003010064240000104070740110480315214440c000700140b106182600118000daa02400300e4003c0c20380c520300a000e100780c06048000080814000900c281d110301c070b034541152810303100d140b280c210500c9d0301c5020350f0010000390300f4551107c40d1108a0050200c00ca0700801d0304400000d4100050840203083d0351400b402079500c00c240b005600c84903402155218211280002e40004001c05201180c1c101455035001803c0b00c0e1130a020402800321640143c14001c10947c0c1000c13840820641b403000c0680107011b080940c490b1003a004000500136805070b04018010b03145013003030196000301d0a01c1c280b50380d603020740044c0d02e500601c080181c04004a12540d039a804260031210 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 643792535 1250 643791285 643791299
    0x31509030e0f1518040504050c03100501030b01054c0306231c08120f072a0816020f060c0309090c250213020c03030c0a0201060806090d03050a06 64
    0x50400b081030354480303000070b81e8200c114a081c1d1103107050f213001e0410311003441d00741800d07501c4412040e0742a0003401151000b01501c0780512460341030781e500059210480e4280410310070003010311480090762a01903021603070204040c00644055103c6071005c401e00b8820020b10a03284000e45140070207140c02c0030010f100030703028016010070244514881c60101c01281c400162031855902c061480c03112240c100c08244000c0350000c006180241014a80c603840e602d010003a050000c894000005810700f80400c4030f40042a402101c60b1116801021800d19540742c00d0a55440341c0310032900c6c3c00301000c1c00d500f1810010502945c0210848480c0d0600d0030040301142c6910807900c24620803c1d2220011b4080d050b10360a03590520402c0300e0380e0340c0e901c0c2140342c3d10381148110702d000d0b0303c1509800c60700c0c1c624009038000c40d20b02000490146081d512004001300e05900216058401c1d95240c041c0402c00480c10070541d480756075000300401c1200900603001c1c1c1203d4010b050145c45600b000f0060144d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 643793785 1250 643792535 643792549
    0xd141302210307021201203a0c031b050714030a14030702031606020306040b0402160609410a120e04110a020a0b0a020405010c120306031509030e0f 65
    0xb40390103580c0317000c4c8400c01c1e0034618010f01001c61039014054403c200e03e40c420081f0800b510140300083c00a0407105ca01e6141140600f040800118413201c00310b41800540035144c00c900c00b03604450a000c5243c60741d40500903c40001a540e041c0050000f150300700900c404c24622420422044000d0b500e044610b1500411483d006003d1200c160400800305204920810880e10446181203101c1034210311890804003951098a00500c030300c0c208880103903a89403a20131909080050004071480303610507035901026210032501a110010b95402c04000c09540c4010681c003100b903030080c200701201080b079500200245040140c85e942c450b04010f00002d01403a440d1015081d01d05101c0b40074200303d400a0090080f0721300800890401081c0c1180c4650000380c5060a00e108000e094242d0b51201081c0f030407802a031240d20f002500c2c9440c4c0c42c0101d400d003030248180d0601854041a007076140e49901c0800c24800100568055403260750700c0c00e05074801f4294070000000c50305010480c172108000356030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 643795035 1250 643793785 643793797
    0x150721020303040b090f0307060906050603010b0609100c02182409013302010203090705011107090902120f0a020a0b030f010e0a060e0a090204060b03040b04080d1413022103 76
    0x40038400c1000c2802030300301b00a01c0ca074003050362084940da6081460103101420814104660145c1400301180c11450103014900c0307407410140c09903060030a00360400c0504d8a1500c45041030114441c6d0500c0961522111002e5001c0c5460a9985c00e0416125801385484201c00000d180d04840d202e0b0080c036916446c1c0e42c0e0444010580e00040301d05225001310081701c01040201865886600da201c0480c1c040d005540300301000400c1c1c40c1c217103607100015100036150703c005002d103821200c420f100c0001154880401e960002c0e18081d100448143c2c028549004040040c0407a441450180210310b050844172002d000302044903800e6041c1051101404030040c001d0143c0e520011000445084042d800300700140354000004803207041c04c0000d05c0c02800c110005a000d64145a00400e807801d0700d9040740e015950059040b111941c440d29000d400f81c10801c8010045900d61003004c0d040d020040700e41d030052161040c50452040c0c103104004184408180c0b66a140c00d41120500414078048144c2d10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 643796285 1250 643795035 643795043
    0x61d0705040311060a03140906100510020a08130302090c180409030507032a1506080a120507230d08180a2604080304060e010206010b030a0e010b15072102030304 71
    0x40c1700c0d643e00c4000d80c042c2045070069442e4000303000821504020000d045405840c2c0c0c0d01600911302d8584052141440000f0010f9000d03030f0003840c1c585e0000341d0b000000d20300f0140340f03001c1e03001098683c0d000a401980540f43d00d440180c0c0410101c140780a4207600383c440103c100d90400501d00d80d41d0b0081c2190158076006014051301c034020082c204c02d10b1030325540d000307102911129003110300d03e05004155151444903d445103480c0003c12580c800054902050350407410350081c010002d00d0403a025800340808a07600060201a00000050003003080344d2540c010016200d0600503000041404000034800610900150071401074080049124024283c01a8500c140106a601e02112184007100c0c1c400c1010400517000135010404000340007641ca16680742e14204c032003003004980d681030078000d00860341c8040011541c20069507101c00f04021080c0c0001c10030612640020740030014204010042d400005448402c01c0305040d403644050203072044c103035064010740034029500d0000405c010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 643797535 1250 643796285 643796287
    0x6090103120215070306031407060903140c1905031b13020904021201080c0a09020304150f0e01150f080610060305100807120209070e0f0609040f061d070504031106 72
    0x4070720a00c50400b842c040200102d803d81420800200140110700c41036444850300800794010703810102c0c0740c20440314240c1c1d403102042d003582c6840801d4100c56203010a248a168514031581d26119510745500d10040c816030040340c5080705240c140900c0c502c10300e50404125414031215510340f80f11098298000f04016110035824000c90020b10a440300890400951800000c40400000780ea40c690441038409140700b42d40e0700c4900c0d09900051703070001e081c21000b1501d000403a00c140c3c8150f002c03102c946808220740410a40907400c59600003540c2d41d072442c2030301040c00050a0710025000400e040b41c002c091a150404804480071040d009606c10180c90303a000c0740d4010036640e50400900005426a040f1598800e294038687c0c0c01c50340124052040c010001720203d0240d0900d049444d0046e250071004d035110000c0003110f5000c0380d40301d1351203507075444044102c0c4030920400b00640681c0480c04030004600c6261000180014028810048100810300000d5102e16140140e801c09860346 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 643798785 1250 643797535 643797563
    0x20c100503090c09041112030304050a02041829060111060c0d090c0e0a0f06080c091801020c010504171309090f0b041b1418100b0c071503020306090103 67
    0x205040059078002d440e1320105090038401484400d510358030112801300c1c0e000120640340040207880e030004582c040c10035000703c1ca4040c0035081c03075040300b00d20300385c0304254407030294050fa50303c1d070302d4441901004c01d40d0286401d014420f600c0c002c2031a41007030003401c1802902e03045100703942c0c0d1000000c003507008a00c0c012500c41903217801c682000309144e900501e102c0c11591100b280f0703c3c00c10303001c9800f03030001402d21200ca01e0700b0b000c0c0d10600c0107980014014000e000d02d00b90034024060350242c0101003891100310313461400c0c0030a2014000c0b51b02d05000200d07250615060800c2e04044c01500c54019842c100014410a190b420708a02110680c0c040070600c41c4440c00c142c81344080c0418094405d0181e4020081000600300d01c40c10200351840f0b071240d2298440508000014032500780780e40040f0b50112200240340200c0c01941d001c40078054003800a43c590490122580201c29102c8140d8000b40040c080354550700211841e059083c6030450851800c200050201a410b2002824a02c41801a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 643800035 1250 643798785 643798801
    0x1903030e030a02100215070c020607060b13050a1401050306070e01080703020708031504050a050603060a02070807050d02030405030708060708060d0f0b04080c010b0303041d180703150c020c100503 86
    0x6100b400c540c00a2880ca0500f009080c0651151a43c444000003000190f0018a0080c0519002c04c41c40c1e401038220741c10500e5641d00c52004184c401d003a99405440c6c0c0912030702000083c01071030310501400d600801e002c0c004c219114007500741038001d00d20940061041002d000c4c0d0045014440e02000d103020200ca44940c40705400910400784060030a00000080103151030701202104042c00707094600308101d030342d000010404c0702c4094030120780c50303007111001c5001d0300d03240c0d00604076a81c0219600780c54416147e0f1740e2813611081d54098400b40c0c00c0418100306501d01448000300400861001d02864507000380d009044860040913188202c40d10000b44040c880280001030225034428440d00301400c1ca4144041c2c903411207604100c1c55800c280700800076040c08070a44007100c9041c0006489030441d13000582c4c00000c000d081402265400580d50801c0408001d10b0f070085004910409078040301241c010107582255500900b0356000c07800b6807000e62144500384100b0289480c10326181c0d04c83e202 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 643801285 1250 643800035 643800043
    0x1030c0609052704080f0c150901090506060103151214010c08070e21030c0606030d0203041202040221180c18190b030111190f0504030816021c111903030e03 69
    0x50107442c5080040f87e8a03411072000030b0140c080c3c0c1d200141d600071954407048458240d9a03004401045508144081041540a83c0004074104150340c0e80ac100c441e107a20901ca0080c41d056425203001c0d008010805103c02c00384109914100c00e86088180c500d80010060500180c070f2200d035001d8405000d540d00c110840901e034803512030007c0140e996030300401d9001503454605403441407090280000c50303c005400001100c0441d510b007040060744000329000c200007034201c00240f10541480e10880c024002c0c140101c2c6204030200c41050314084058034a45140c6810804428014042080c845681600d5045c084c2d03400400910258041540443c0b11405000c03042c248581542c2808507020550640601a290081040300300c4110080d1200088407210219039035000840c40030070081c0301150f4118001c0c00c3c40c0c101c20138402c0c031554a035804180b91401c180e40101c0302c81b119006250030413201c04c180c070031620421034007004d031081500c04440511000d0700c001428880a400001c8075a103041c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 643802535 1250 643801285 643801297
    0x50f0f0708090a060221040609061101090804030302060709090b060f0c0a021f030f150302100302040305030a09081b01121d0d020303010e010b180d0807020901030c060905270408 78
    0xf4000704400c95035880040e58031840c0a81c40c1c52144c5928003040c001d1080c21090b01c0031900c4650354560f542e4502081a1005407614150702029502c0d030103088003103815803004200541c400d50007031009142c54240285406004c4d0070a0318646d0500107504025038440068591142c40048002d60b01c60740c0b140060716040078100025041610003404100325403ca21a0700e901c0b07940358605002e5414103944003001c58040c151401500c800500e8107002508042d2403103030310310506003030040c03409442c2d44035546036801c59041ca20001c1c0110301c2c20b000005040c0070245030f000300c0a2044032102440e90000e0981d100c2003100050055555850402020500d5110005410320700240c8400d5042c03d0350094503944240140c814200416000048076800d034002c58010b614040d5003d80400888000c02c020b640311942e081d55034000902c04400980c0e50380342c2d014029072080ca900c030a0a89000c801070003c000a0788010700c6040110301d001d4000400d0301551100110582e03034051590b569150012440c0540303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 643803785 1250 643802535 643802539
    0x60519210b2d040b0102010b030a0f05071d04021005071505060d0c08010203040b0702070311150f0313120921060603050d0306050405010b0f0a080603100218040b01050f0f070809 78
    0x20880b9065540c2c110348440340c1c000c009440a20038060442c0040e400d8541141c03143c1d070180e002e200b800c1d022a081c10440d40b403072441001076403011aa20202009150380030a0b01c0300110340104140320451920848064045c0c07041c0c2052409c00f18180c0b5a180c403985040c402060540c1c5520028440780d0303801c2d031045ca0321580003480119464594001c03078000c0d041181d040302c03002c8000010643c200d00010740d0808895002040312000341d6542c0c00d028403094400c0610440070700621009400d030070302c4c0006e180f00d00004801c1c032072519682d08004000c1901a5240310a00030b40a1017882140c0080d6480b01d641e1000d00f180d01c03c0e0444501d4100010702c0c041d40003802c075000d080722403030b0a240d240d00804100d420458090100d640c80d02c00c0e203049442142c5054550490070000e0702e0302280210307080c2d980800020180c81690408a0a070401da83c40401924400022006100100d14003403180c404580000e2a1090074180b07041801c44c404e226464460340d4404011641008110140c1c2c1212210000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 643805035 1250 643803785 643803829
    0x1009240e0313030b180a110d0b1303030c140703051305030a0c03050105070518132013080a03091205010f090b0402030c030d05030a0b06070c060519210b 67
    0xb640c500000844818041181c010451001084030035182400608448171144068000c154403642c07003034200003808840c2500482d4015118000c21901c0c1c5095204503282481c2060241c1c8074a0700400b01c5211103407180900200c10b00841c0c0030000002a00d0b0b02c04d605040c80c2d0f035540c4800801d1030b09114031ba40016030510428035a0710411a490381240e048070703c100020300c12a180c1c071205a4035401420f141c42180512104446a203141105501d00303081038480c00091074440ca40b040e00704a582009008201103c000340721140c0341840c0f40d01c04010f2210700058480000566001405218148500c850703100100d0040401e004003075200b02c0148400c101d0401070220303a4540002505812a42070780300c0d0050b100da82005080c041468094050140c0c1e8032895642d030100300100a045104140303411500c1840041e001a15008000d0003030702c81512166112003000b5210b40c500c00d10f51811004200515070b0705014106150440d500700c0d41d4500012940200b140c002c0352007805003184000440b48 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 643806285 1250 643805035 643805047
    0xb070302100c1e050a0c0b040f060e010b0315090303010b0a120e0703060c020a020d021c0f080904050907030c031101140a09080d0302120a0b0d020d0506091009240e03 73
    0x30f00300c0349041100c400c0112042c0b990114080c2903a15004181c810004074a414000ea4001981e032481c030f50b0300a02c01c90207010000e0b0651174600c00c0720f6000c016100319a540344816045883d04211043d00c40e074104071140743c030349004e4405503186c1c0018031519030296004138110702c02d14010400c0030701e00f00107640b0400c907001e403d640f002e60b41c107480e100075160309181a00d4501200e1003c580d60815a0b00588141410350082d401d0002401060042040003269544c01c00c0c0010140e17814010018080c800c2c0300e490707980c00c5042104485c005403500300503a202c800b04000060307d445d07040003183c2d081070381c0401e421140307001a00c07142c1c1495044c1e90601c6000400c0c0580c69080318000e402e4900400448844808901c07064080307104007480c0c10460b030845000550404440d0300b041d03200c1417003d0311000385c00026a010034040c1801150803501e54229108000740c149040042d5220350481c480c06008a120981b0b40031403c5608100b40e8441203407100e03075a900c1007074540000007040f0042045030307991b90b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 643807535 1250 643806285 643806287
    0xe04030c17070b070512060d03021014010305061003170309120a030203100b27040f1103160e0a031101020f0601090b0f1005030f1306230711070b070302100c 69
    0x381c400301040f50b01c003240380701203041240700c0c900381e548601592449001c03c0c1c40e01e00400280b2000e0720000c0301103100f049581202201140112404c07402800103e6030b1950441c0f4025080c5203000308040e040384200d07401000070507003400e2a90a0a0416040a07a60380c441e400b0450a0681a9040d0b5035024400920010b803140e140d4021403103030380013507860040c0715150a40107041e03200d07181c0900308540014aa50004403560001c029103c0d03002800091000125040801601c1a10442c074034844804801c1180328a8030321890520010186028500701070030400080824000e070202414000c3c0b444895600d0341d00800800310329041e0318003201c0466035a032116501400003101c0460050120501d082014201009d040d010706580b5103401e42156103000c101e440d4090000c005049c045002c0a1407000b01d60188500c044000d030640c1451a4442d81c003402000c1450041d011323500304030700850501c800c510042404820f5a09001b02c4940d00c02150a041b480c0042c16940c0d228041e00e0090312140309 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 643808785 1250 643807535 643807537
    0x20a1e1505030412030504021018081b01020d090513050402031905060702011a06070303020f040902040e101418090f1903081006120b010c08030a1e0c090e04030c17 72
    0x240d00c00c081e5a081321040010440582d44155002034102e0030030760009036540e001382820191206051580212544e40d596224901505031003107420074441d038290039165580c1440425003030903080c140003503040e241c4004940c020740302100340059580e0ba007010604560b1700b842622110000302e00140407005031414010b40b1920b041d00c9141c05076280406510407100124022020004002c200a00707082c544c0c5c50580181d03000c6400400c1440c4c0400000c210703d15a88042c1007d8012199000c1807407400d00b000c5d100c400c0b8990004502c440d00041d01d0901c40e65002148a00c007070442c0fa0640c01c0352126410749103800b4100e4498440c030b009010820280e04c0b821076003049010301913950507141e5184c032141e148011119006050015040a56401110559800040c0e82c0366040c5049032071300710261680360b41d540098940c0e6410740e40302c0c6020906121004459011040c4820b020400012107010281114543d48107600340685030038001014180510030000b0303a81d40115503031030605180c0202000d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 643810035 1250 643808785 643808791
    0xb181c02040915180302060606090a03080c0307060507050337020d1a091006030e03130e07090f080a17040503031207030e0105040f0f060615020a030e0d020a1e150503 73
    0x41074505130290745034100d5407000640040d01a0080c200d603856107800d110099000d060703000c2c0c010b10120800400104042d004040410306040650f072184594074041c02034400c09840d42e003c2100c02c1c4140440fa0500303480459880c490318210115010140742da4001d4030001d0380280c1c8076a440030070342001c040c407a0341055400e14101d0410200c40001c208c1049120542a101006a1725002009108640c00b03980b00780030a501903001c0303a05001c400c851180643c09140c00c0717240012120b005000c403c6410004050192124400310f11000d81041c0090343ea0f8000c1003c080c1c0100d102e44e04a500c0000d4800803203018080140580350b45050f03030795803500d041c4016143c0b80002884c24101d89041101032151a0007a94032200c0035a028003151507c400b440302d00e1f40182c40e441ea2302c8100282c0500000c4a8145000054029281101c801e0070b0141080c0090f00306e80d4014039520f548000141e0f00e5196120035510031410b4802c21144120240580b982a9000b1011000c00600d00c1d541c0590441b024501c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 643811285 1250 643810035 643810073
    0x5040501111b01060905010303050f030a1b030f0c09321002011407180308031504090605180307081209120a0201021305030f070501050306011701030b0a060b181c020409 74
    0x400217560b080180b045420034400580000d40610819112040c0c9074000c58208852040c08250030010703014016080c41002031100c00320b581d07030032204031a103014041c41440080360708058005c507281000301c120b0294a142e41d080803a40e01e000a680721140c0d03c0e4a0b149804018190044040a0003000703802440c4070480b5803102000078000540c0e05105001d0300042c2040c00290400d50b6185658031030703a9801c05050b8002510380c8411510003a00c07184194070100e80035010208240c1042102d09425055913001c501d16600100b1990b00461200d03070456240c6e8000340c0c2969441d545403c20141000b40d5000764401c030760130024004121300da054010740044d015001911025542c0c50f800c150b0354a03403000e40001c00b50841102040a90b0003107002d154480c0060400880800c10030341000c002e5102604215111620102071085079505482800d01900c00e02810505c3d000840d6045041c0910503460740303126448803000d0700070040d072914601352015405041803003a40e126141400e514800054890 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 643812535 1250 643811285 643811291
    0x307050c10050a0c0809041e0612020a0e0402030c0618010906110d080a020c1e010c26130602031915050d0b0a0204050a08160602060103120305040501111b01 69
    0x2031401c20600c100c100c03a20b032100c510b0012092000d40e842d02ea00801524464428002c0308000d403224000c5035007011031745035040f41c4255800016401c0703c003140c0242c05080841c0030341e08016100e8000b41816518103c3d0f0303d903d540d4503880042e2a001500c92174680192000c03910303400d00414500c240e1020a407d80b2842c0380140c0b41e88040b1003204068003042d105900080d40540f4180c003c554031078000407246400f42c42c11050708203140c6021400c40c08204850054a82c1010b954005e100c0d02d40500c08925144144502d942c0025480341194241000c81060920109401d1017201d40d800c006c00b41e1041c01907450f8078140c0342a00b4841c1c0709101024545051611001044003006000000c0d038a0003862051080c10700c1c1c8840d582c4c1c0000408080025900708404950b503034440b8651002043e1500081c148400010328030480786185600c07113429544404018400074406d038510707030300001071454001410b070741c0c1d4242140503081701c41e8080510480024108003000b6248801e02805507000000c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 643813785 1250 643812535 643812553
    0x50d060b070b04120e03030c070e010f1a0d18060905060a09080f1c0f0b0a0b0c1009050c04110c0d0813030309020112060e040c060f0e060a0207080f030705 68
    0x103040644100d240042c5400644000900082c40410841290700010303d0b002640d80720b6100402e00c0c51303020984828059005000c10007184644c00100c80c0501040c402680d085450807138031005040b07104d071401080c03900219102d00311036010380c82801c85808c24030601007504c103182070020042040203000c2d2050b01540000406240d058010344039101d034003885251819003c248008545d40003400c4c2210450803051103811044014018400c0d08420320500254441c00718041018100440d0700c0344024810905c03002d00f503441c0c08a42035100400d0014007184a03031141c94a64282620959603c1e442480d107141025419040006031032510307030301011110711682e01601521019000c07502100b02a80201c0c440001074483c4e040b000e0300d1407040c1043c800d14415024000147c5005030018045003007842d0420041c4014501e118008110500f081d1032165801800201104440c04c0d440340100701c0020078542c0f99108201c1007004000900c01e440140112209007500c170361101c2416201c510511702d003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 643815035 1250 643813785 643813799
    0x60708071a0c07021c030e12030d02040e01080f0d120c0302040506070c06020d110712021906110c1005070201030b190305010510060f02030406030e0106120305070201080a0507051602040615050d06 86
    0x4c01d0b41c1c146e8068450541e0101240200304007034140d9001d89540b40001c0c031503050905480d0014102034a040b44c003ca8103581402802840c0002070b04c22148158131010603900403c0d040f05481c0000001d591012414140200e01540a441076a011540000000030460144948582200c01360740031582a03856103480b4580880d29900e01e050b0301c8407203410282d0200b01d0a4411010b110045101525118002003110820300c1100e242c1c1d030100c80880d02412002c001c021061102103080c2d40211840c20b141d120100c0002e200d07028441000741410340d240300350f0303a06a890888444000440c44e0807000910b40b0b910700319002c5d20702500c044003200300c0300d080811580c1c0503614524100645600450410740341150460107000c8884210a20b9566486e0104901000d0b078074501115000781c542565038000c91000600258000300401001441c020502072180ea020302201c0c1d442300d5000c00300034000c902e0300009000740a690f00039500a036659500c0c01c0390319000000b07441c0030801301c201000b282c0d68840d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 643816285 1250 643815035 643815079
    0x60317031b1801050912010c08011403031206220515040509061302012001063507120c0b0a0e12190b070e091f080c060708071a0c0702 59
    0x303102d15a0800c10707960041c00d07510840250440e01001892151280c03800c1d080d040c02c5595041095000074840c1d0300500000281d1000c640314a50107030002d40c030701000003450280704003018001034843e01030b5040d0103030303011a0100c85010704a088a020042c03802c0180e0205810f0392281d00e0107005900b484005954460003013203d40c42540079035101c0500c1100c1e64011121007442c0750508490544402c08a0341202092040070b01400d4030003c0c022807000f0812558083c400078031569016043e01c0c000041d1412008a11801240c15000c084068541c01d8545810707100060303000403111000200300c2035821076000003084030080c07041e00d520018102000a0603101e59502003403c2e0b006081401b010300190140715080da104100d460152160803541000820001099070451316060792007047d04920f40d54500c10b00000c10082008244600007107010030054040c001c806018104045189401c2c81580d40d8882c100786005940d96001c1c4c580150080c0c01074001950990246084c0306601e0791140c00b00c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 643817535 1250 643816285 643816297
    0xc0f010b0f0414010605090109030503030403091a07050706050a09030b090105060406150504050d06110c01050603190c1a0408060a020d0614011b0c08150411010906080f0604060317031b 81
    0x1560f80c03410b07802c0080580d50b076400403001e2410030407004400004900240301840c06240f2903a44c0c0f0512034030f80920448405601e005040303a000040008600290700081c2d407804540c11820306649601009800b500c48500b039602c0030705203401c45001c10940d5201948050310811040703400300051a00c43c000c0603050400d0301101c0740480d10420080c0306514000003034081140c404c241c04219481492420212608001078030b100caa034451060040510b800e000c40e400c800e148519861003520303e911940017105461207580c0d034420030701480d01e6030216000102d802410005044410b40c0c20085861002940030b0300c0404051881e03c040030540d08041d0b00d410700ca160059481a002004a01c4000072840201c0c404071248150b500c4000f82401c2e09011450156280c0b080c04111480d01c1c3c1044143c00750031600300c5041098001c0d0900c000c40c0c101034090340083c01040404120f540b0040410001c00464001401c00302428061104040c50702000314820010a1801d00640900b020203101c240914 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 643818785 1250 643817535 643817561
    0x608040512031e1f03030e04140712020912120a1416080c01150f051203041a07140a06060303030c030e03040504180602070b01030c080c01080f0702030c0f010b0f04 72
    0x1080c6503031803000510f1260410901410342c2c0d0702408032044450b030042d865000301c02148102c51240810300d0584140c54600f070302240f40c504513150082c0000e24100c48070f54480342482d4049609155a252101401c040180060407143c1c421209080c4e29031541121214070300084040078644144905c200c1591b00c022080300d44e80b8040e02040d078a042048d04083d54411181d0b5807800402c12070190760244a00a00c041150780302a103041c2410f01c02c2c2401e480c41d00d00c505500810042224810349440030302c2c1500c1c02c04519458607410b2400c516468400c0e0340e0804644504450581405220780c000c0080b08d2084e2020840001d41c4a810b90603a424441030f0301054105100400035410980c100120003902c0610014081c102980ca0700b04a800c079180c1503840084060042c001c010320002c181c005440090000c01c00c10701100c0000f015820020034a0300748604000100740c06500070415100c5110541d000e41d1020483e091015000b0142480f44601ca24100b201490725410107110f5051200c0407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 643820035 1250 643818785 643818811
    0x10c08040b0402220204050f010302071e0213020f03070e0103050708010504050714070609030306061409040b01200a0203010c09300c03030905040b06030c0910110106060804051203 79
    0x200d03114100c00341c10007441030781c03c600c040c2d02c500f41032111504000c1088841c0140140c0b0342d414402809509401e4030f20301c605141c410070440d8081000404803405020f1310075103c0e40b000b4003510101d079203401c0156603841e6490010401e95504051000038602c03905455a45050201c80840110f060725026100707000810702a40040c001814140c00181e8804620300304800c3d08040940a00e01075030019105680156540c800c10080660500a090040407289820b010149101046005510904895520840e42d4105074003071a4024050b0458102262500110040002c3c41e40350300d400ca501c40880c4a5460b113290076004500410188d0180d981052044c134907150444561029800320f400011500821209490b001984100c080c0f0007a6100b5501eaa03056458807041c801586c0c1c4080c0c6c0c0902c1284103104000803c4408000d5500740c001c100c0d5011042ca001a074207482181180c004030081c0e50030031001043c80d40d08602e1041c061880390b0704035014581c2801f5409020b0000399440301034020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 643821285 1250 643820035 643820041
    0xd090902070206040f0e342f030405090a0605060a05090a0e0106030902090c0309030702011b020604031a151c170c0c0a05040c230405210c0d0305031605090604170d02010c08 76
    0x202ca8001c403c3d50801451040d000d40c031010010a201440e180040230055200240521490800400c05904444140000e0017a203040c41b001034964094014800c0070400c0105280c41c155480842045c0200020300040807d541c5800004028081904003a40640c40c03c0c4046a50030302c100e01123070b01c1001c96030701860030055582d004650032800b0302015200b038190200ca403005a591007004000540c800c4201e4a28106202403910320844001c0070120902c4c0c007400004405c1c1c5841c140300b95909040807800800f414941341c401102901d442e40d034801810003040000203240002001c20003040212152200035076500300b00710580729040b4100000a031854100c0190b020b8000700c6092007500f1152850810342c03a5004100c0d40d4200003002d522051989000c48007501061210403180001601d0b10443c10f2130984001e0001d00c40a480400c80d200e0aa84020444c0d02c1413003640d10a5a004082c03650b903946d036590749034030910003d100a0180c01403880320b801250051041c1c0f065400e280e114052683c0e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 643822535 1250 643821285 643821287
    0x1050a03090c0302040501121a040206040b07031e1d030601140f010c06050709030b150d1e050a1109060d1109040f050a050706020f0d090902070206040f0e34 69
    0x148032002140c0b1030003003850100042c0c0e00d5000350350103807900002c1520700c50030714108090109041800d030110784005070284000f5864032412501940c3c1d4075034000744d46d00c2f4640303004c0710381451045240f4550189804880b041551040600d116075003071042c190410000403040503150ba1086c13150741d5585680c003410314a1030510000c0105024414101480704803617a45508060301d500301e41250000e41120410b1003000880360051340c012150300c0b40e42e10154020740c041a014100c0d000e020301040b030748800010354043d0914215042c940d0100907079462024514000700141180100d26115031803c1d00019024100030348142261a00003640540b002e91000600240040240040e600300c42c000c0034203400305000304000d03a4a1407156004000c200c1c41d1a0300203040130991203070400b071780d08054401040c141d4440c1e0300300305036404500c0041c2c0d14005440020858450b55014007041d00c01000300080e001e07201203540740f0451030120210480c3c1c141d88525120600e10300c842c2041c181c0c03804808001c2e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 643823785 1250 643822535 643822541
    0x8031318020c0a0c091112061905150304060605030f190c09020301150e040b010e0f06041509060e0406030b010b2b1a030316120201061d04021e01050a03 67
    0x10004680d00186404001c945080c14030200d07640a40e518075a8050400060643c0d1080c2a007035000b248219051042c4d0300c10480d020f150240c0070512500d01401c00345030180d250f50440000f458018116a1100a040441103158104a43c1907034400e280000000d01414081005d10b084240c000150205145406406502c20480312040c0c0e80a000700c440820050503510095000c1c10000d401c014903122121802000c8000f4650054000c03420204002c0859030000e4403521034903811900034503505120700120302c1c28020703039100703210b1012a03038410440d140d0400f190f6402d80b241561071100758684070045c082030321030030b22000701101c41c0040100515000c84015010080a100504042d40360480c0140503200103015074940e520b640d140300441d0007201e0301d190800b20401390040c506200b03c3d41c2c11410541d0700140060103d1282034800c0c80550b10039403150015100f0407a4181046085079450b0160700c2046501324024041d140802440d041200622644924165186441e042c94104204d0103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 643825035 1250 643823785 643823819
    0x32901120f0504060b030606010e0603060f06161a010602060106050f030c07051005060f041e020c030d0614131a0f0406120503030f1308071e02190501020106080313 72
    0x340d9569001c8520509001d401028002c9015500205080c01070801b01802c0001c09030469040c00320080e1800f015407509029a644a4403c9580700e2454100c180407c1d16031050a41070030344610982c900c01c042005140c2e00a0349032a68400b001d00c075a07295082640d4500003809150081402400000d030408007074801181d00c07000305640d00e800c0059036964a0f14100f01c101c007512000e074880c010070075503051100c400d4400080c1100c05120202603160799103c0d55000307c841060250300084c4100d40100104102d8000e5420030004000c0c00743e50b03030249090350400805040c4202c0e0005454505ca100c180a6909540b08040500760b01d07101440402000d00300d19180103070031940f42c1c1c2c400140071003416580d00381c060065020303680d80d2610090143c1d6861380203080d402c01180c4da02014011803c0401500e04450b484500c111a154510420040740703848020005d5100745208a580c862266501140e011a41c00717800a0240d15100c4031070580300e02550360010888804042c0c1006040c81c04410487c2c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 643826285 1250 643825035 643825067
    0x207060c08011a0a0903050d110f01200315090c0901030606030b10110f0d08250c060c0c06111b0705011d12031b0c030102031608060f040c020a03032901 67
    0x502c5c1a900e6039003504040c02104603c1c0881c40344419400d000c08244400c0030644010002080761412020b03403080c888800e079204150104008c070000e00d20700d041c0003584107400741c000d04040e11454101c0c2203002a9025100d4680001c1c10604001406030190041d40c01c5440e0042c68040c05000205048503c050040070b085d142c0e21400c0600d01b541c42c4144024041d0009965800c00580341000c89103540000d15140b1051100802800e0b80000b0340c083c140b1059150311140200d00c2043c400c2c4100c48034450b0007405000c69180400c1700c00c0303415110300201014940090034510408112a0306a1a4883c078030031305020410650030b41100035000344c0d8441600100815451390601907000040c0b9542111041400448007503540c0b180400080181c201c0d441d1080b002586540742c031f06084510060680607500c14801c520010540a035a11000035082c8075000d0300c03c020b0118040c1c03000391346503507254040e03011a01c0c04048500304030b091b003040000080c0d804501c07601c11540c0c0300110f4402e00041e4220b8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 643827535 1250 643826285 643826297
    0x52e050d0605130b0702030706061409190b150306090f01030b070c0f0602070605060a0b19051612020105011d01030c05010e01120507081e0f0117011404060207060c08011a0a 76
    0x80005020101c41501170240c650003983c589040d49000000c48400341c010911a402d10002820301c3e039100811541c0c08001c102c584542d0340900b00840e00a0030b292058160710562003040c0d42ca983c1031110207540300c0e07041120303203040c1500c0742181488098001c2c000079210b01c01510000701c9060062400c1013056120f0480c080039003403a034841104a1300302c4038044503801d8454061012614000f01d500d0003410444880600e0100307074140240c192803660001c0c4082c4400403500c00d2a40b85100840c111164014240e102583c000d014024001e141c01d008590710800b03140415018585600d4006042e00d92264010381c0c40f500306001550b22250710280241000040c800b405030507890b42c0969400b51b41952640c022509250403001241103100c603034450383d100301004001c1d52114480c0710a045a02d03110540304140714446d0154050f1415114241d4081400820300080022507070040c4141809640e00b0080c0e150380c002c04442058080c401c18144c2242c0e00341d07a81c203249414004080c0d200c200e051603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 643828785 1250 643827535 643827571
    0xc11120d050f210609071103030103110f19050a06020c01080a0b0607050d03290f09091204060c0c090506010206010303050c03120405030912010506010c0b0415052e050d0605 76
    0x25040e15059510f4007040301c000400e228190800c2c16955800c031580d4200425444108503100743d5030b000501c0007501013020200e0030030007074a503424418212078018081519000100684400304801d82c4201800b422500e100024024400315400780c280805a55884403600e40710705500c043d001c4e80c10580c0d4441420040c1c1d00000c1d40070007191003100e00c182c80108940e41e81880503507606030009049002c01c00d41034014100d9030794964004a08540c11a031905107030310340482da02c0c900013001c50800d03550080000c003c40d0303c0382c01c142c1c94080180308205130b12000340c86011905c25140140d90460150384024014400240200d01401c000b05126046a04103460418041080c9e8411703101902d45401c0004d18442138280343d4a181d1003240000002e000368180700000802c8101341d500c014145015031400700b8100b00d0480b030781041081e1050414881e50170b0010042d01c411003031107004400e07500c2aa42c0030701000440c190702011580001c241c6056211103480b010007030000288070380c84000b095144 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 643830035 1250 643828785 643828807
    0x302030615130905010e0118020304050a05060907050f10020c09040809030a03081e0610050c1615020708070e1308161401060807050907030e07080d0c11120d050f 71
    0x782198003040500c004059180c240f011044030f0041c3c1042420081c800d006100614040000726500c00000900590b43d070384500300030342002c20103200100b42c0d02480c424040c0d5040d00040440a595045991284000c030040420800c0c10400b501000960043e0001d0151840e294100070761240c021008149800c0300c09001030700342680d444085000ca401201403040059808400d580381c03078100071403101c440c00e00c100041d9aa803001d000900801a0000784038241705400c0c428410031035654401a052191180c00b0f021255520803400300042c8241280020003083c005821001c5521440f5902e9031500c0c0c404200c1d480c013502e0202074032250000c0002d010030315000103181d0111805103220401d040c0101c5d03d0b59003501c40c107a000748155440032405000e6a920540b0841d00142141000101048240303d49418080c0d82d501200d00d50040160503007010ba009007e58800b98400c28108001d504620b0800440724102041ea03031050340240c2906c88071302d00840092020f5800411080d00b4401c883c05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 643831285 1250 643830035 643830037
    0xe100306060806180a050604060203060109050916140403031b0807201009062a14010c030b010924030b040e0312090703020616030318050303040c08030306100302030615 74
    0xb000c1c0c100c0b940190100b01c507603074a07545111000520719000d00420241500c4440c1d40740e00180014000c1ca50000200d24a80c0c0a10741c12401000090005c50300d6144c81c5080300d100e40b60b40c442c8040031914224074108410540e070101c6050303e5040d210300c921417010f103880449007204102c046500103010880040170078000240712082042d480108042880043d0500c10b0703060b030b51034181041c0081d07841c3c00d003c0303160851883c002e0440003540000d0090405c1076a05411080d90002030041d6181e0380f1003034442c10301904410340d20440d0740c60a00c51401c042004484c6560740384076991299024130b1040c80c2140d80c46807018219403051078040303580481c1c003001808980a1282425140c0d100044900030907140e40601907004c40c900300585140307880d507008640a0301c940c204a07151100256182010103000364800e2120305501c503145600303400c41c3d2815581e00d031b00c20f90701500c1c25885c180b13000a0071071001040302d2003408050101e140c2c056000405401039040504a540d004800043c001e48000e0858 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 643832535 1250 643831285 643831289
    0xb150d1b140906160b0f0f0903070209060105030405011b0908070f0623042102090a1b110c0d0f1b030c0614160503030a0f14010e10030606 61
    0xa08000340050003203400300505042124240c00303010010907200c00500501040c2c1e468104180c4500790780346100c14501040c1480050010100083c0c2001c1c451000e00700020648101201200040e040d215200c4c1107503030b8000d0840c02035100c0d4100000519a503c540c01454200d4030030800400c0780068011a103d204100b6080d40c80040c0910204010800c010040359009041030401000030030300b0400c00404036401c50500384c107400301e020f40780c82c0ca0380381c05400c480003001c0c00210f04e03414030011a20500e003102d4a0744140e02c04c404600115151002603c620392413022181e80030041c88100e101c1c10f552002d1549a2024180074040d034400b07194850a480c043d100388034118400e09003c00345400300310103a68800c007980401920105100082500c804c0e80269451402c103451402020404407403284281c286440c09880e450402c1e0f020030a000001e5401502480018058105418003a504803900d60012002c001440801008240c40c2030f109581c06c04a100c00c105401502d0f510750f40e080d2400342d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 643833785 1250 643832535 643832557
    0x19051204080a20070b070c03050709020406030c0e01081b04030b0a0b030d11100218190303111209060c0f060903070b1303230c070b090925030b15 64
    0xb1101c510301d5005002c242602c1600c003607450010359030140c1640e60301080c0100740c0b01480002e000380134051000c4040f002141c1c401c088079081506c5a991030080d41062050101280c180803d0141050059000180704a8103a482543ca0340c0d0b241103140c045000e12860101c0c0140400010020401e49900740780701c1d040009001c200007a1810a0518012101c00300781c04004060307007418825000400e421a0540c0d210402603202c20361002c0885800d84d070340c011f4540c4044841c00c0c14198a54074500e007022240a5100c00c00c640121007101a112400713540c4c2e000c03112000304111311180c80e00c01e005d070a45103110403c495241c0200c090440c6020415241c58409600c017289800070804031200b030a42c4070262500780a0440e4031990054580d40322002c94042d01f0b103811042d518580351b51811b403100411140704a80e1001d03550901079030315500182203e40a001c000c0c2c001003001541407120107030040354a00303140080280c04001c6004202c646511503002110140940031070140e038000e01900541 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 643835035 1250 643833785 643833787
    0x3030615081807030b010e190501080a020a090209060d3612090b090402160b0c0406020c03280501020d092f0604091a03010f020a0219081905120408 65
    0x4400c11a10b44440720040480880d8480001480003400440c00ca60440303000d00b110300001e0311446d054544a40388100c201050b01d2600e400094103610002d0803041950007901c02819aa403500c06c00c0b0b0036440340d88005600601c080002c64016039043d4042c015821121440c0c4115440440c940060a0308d61f015124092808240300b2041c0802c101035071007405880c1c240300c501c80d4034280c0d82d160b4902a40219601c100c0d8081240c4517484840f1005d0b0070710310740c0500b44120901c0c103c1642500e030b800c40c2c05002c0040c811a4001120750400182c88249010007059201902104aa220300c02498115080355595000d0100d03d610101d94028410300c2d0348911b00d00e0308a003520a141100075510384144001c501c072211134010b0a5294a000c5500f99000c01038085100800060301c908841d80d40604207426618001a00304242495800f60a0f50500c035401d0301c44005150ba110883e18100d0340014002d54004c00c8880c2811000d03000d10041070007641089800c01142180041203180c08036019140580 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 643836285 1250 643835035 643835041
    0x140c1005090d02280201050306060c0109061e11040b07050f0f030a12050f040b0a02072012070f150903050d110706030911060901020a20090105010305041a040303061508 74
    0x80c040c440244c205902c0400c16080705004140200d40040c4148042d040c08000130119038180c48420480d07c107030404e90000e00002d8aa860001d000344040c1660040888005800c118501d000d40100300341000700c0b00a0754201b03810010301c5103040d4840b02d4111100d03c50210aa141d0035018030000c100302800748047c0d0f40342c60101002402c10140b07016005009450a8200b082030801405020f810540080d2001465030b0f4010070903000384035207907019200c042d0110114090561004007035004140035920149680789070700505036150071074083c3c00c0c0044c02005043c003003000e2000c0480c13400b000d149807440b46d6030382c0c9890701c0d401e042040c078107500050802a0390744152501040b014000700080d103800c000c0c840301511410b42c8a9124000070344242c0c4006a8a4102e0303100304495902c8a8020f2000f5140408035000d490000c54412080c6015044030f0300000382c0385d80030707100c1c1a02c0f03181c03c000c0c109010818032581d4280c0140c0207004409066403000003082840d105403240d80d461040340c8460120b41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 643837535 1250 643836285 643836287
    0x213170607080709150e010203090d0627020603070c05070510020a060b031f0e01020f041701050a1112040f05160f080f030a05030c090613050f010e01140c1005090d 72
    0x88402810f000030300200140c00c0191042c0d95207554505c20b40341c07400c80003a482c00d000407815880f07400c40103a072041e5600001c40602504e40d1120616007800c2d00000c075000400184079240d09007c0c4c0000e0340c4000d05000180d82d007801402140380c42449407064855154840300010124000e4801050040c0e1140c0e0894082110902c560780b8586011001040400c1050290624000103160704a403a5915100c0412120034250160b4100f80700401600d81c803551188009110f280a4070740318940b40d8201008104200b100c0c0c4606100c1c007240c4680740e840c000b0b07103800116688a021b842101e40301c840c0361200012410038044410a42111300b00000d07614a05010f2101004060300207a103260000c51403c1034000000040723940c0909035060a9841c1d68410b11004c516004400503503030018000181e296590221500703000640d00104c61070030070048450011a2420388050656000c11039464009007840b070880017501e440d0681c00c04031440c103031b92030520344103403030055a800d602e80d40403940701a440c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 643838785 1250 643837535 643837547
    0x7050d0b0a0b01036b030709031e14060a0b0a120605100f0801020d110c07180f02130303080f0f06041805010e07030c09020a0507060213170607 63
    0x4034007460306014442c624140c030184505204030302c12460030101d140b408840100d940c0c81c174541c8007081d941d60651882c0d005900400a0b003080c41003100200440203001c0d00140f0050740d0141c8410307524161554110b5507103c4070461000010308114000c5001c4038005140c0c1201511074448120103480d450a06540035030a40d00b03035120b403e124403ca420184841d5003003d00580030f0076003000e000301d0941c54400c4440e660840d140c001c0c0307104444000c80803a820605400818410400304010005455000441030031401540e03803030344039a00028010801d00846501c7c04000f01303540b40001a20b09030002d030410803a400880b8010529080000c1041850742019034180e00140b0f65100d00f800d0b1600441840f80000028000d512980c2e590382684130342c03030010820703081c100da01400800001c0205580c540d41d40059100031a80c15440f104041440b80c42c60090703030f00c84811610341900f00600c5a54a0019400c29007101d45000c00482c00000c00c44480341003400d007504417201a1025040020000f080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 643840035 1250 643838785 643838801
    0xe0a0e180c060a02101d0303040c0807050409120c0203030f0d0501090f1401030308040f140102120604020f0f0d090b0112060b0f010e060d1b0f090909050706050c07050d0b0a 76
    0x11410b018010400c01035004a0b540307185042180001401c4202d803049030140c888007104d803001034800802013000300607000b44110191000e80d4102c42d80c09d41d13210308000641d4124040180f000b001035181c0c208543c0503501c8800b0301880141aa428402ca04140e05880e801104104948070344a2004000c4c0501c940305000741c4485054061140002849008510306010311000b010003504600180900c8020602a084154400030048502100d500e0b800e000c0c0d00079a00d4050b01c004c008020801903d40303803007102c82010a980080b41845080c0d1503240c401d40000b51b601e41c9103a250344030310001440e0300d100d050290055070380101208150f030030482d040390a94080d05004038080101c01c080c980c0c000d070610103455812a1115030701c0c2a8041d0300000303062002071a2421401e003508048c109600070021428410380c607034a000c1280d80d0b50702c0d4042611441d28020304039800c110b030203000d1603120714010f01d81c080c048800c445240781d03201c022448040f4040c905949544155042c0000840c06015180d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 643841285 1250 643840035 643840039
    0x30b0906040c031e05160914042418050a0312020c060c090f040507110d05040e1602150103060501050a05061206091e0c130e010b07030e0a0e180c 64
    0x6803400781e0710340010491900018000f03102e81001d08070144d1080c50070810aa90007003c0e21500221171051400d02d91040c010142402d041256500f200300001284510480c2c111040c4840c0c40d00341d80d5039958042e40c03c0024062140c544c00c20144511448014500b454405e400410b0720020504001300210343c400c034103004442c0100003490719003000140030754001d0360070886a640c41e2070000020b8401a1034600050304036081804020030181c202001c600301040b60010b50b40c10b00c0c40d880d001c907840e110f1402080904408100440c000080c0f40d8440c1561b82003600442d003004094101d0001160000da0044416a132210018401414044464801410180c580b01e00b068505040e00610001c000d00325405142c6442c002104201c40c80b002c50a5121904108003003420100107003449503005040c128202c03105242e0000d45611050103880c104d81c56001c20b00d04201c0c0a035422102c0f03040c1c0e402055030140d0349840102c1c68030443c0282038040e000030340d1911441d040c001402c5050000c00300002e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 643842535 1250 643841285 643841293
    0x211b031816060509010513030b0a06030b150618010903051b1f0507120e04141e07021506131409010b040509070b0f0706360210050307091e030b09 64
    0x41400c0d0020f096030000c0000342400c41e00c600015428400020312680050f01d80414079040c40b800002950104040c2c0f402600c0fa44099982c2249101d00130403d61802d5801403010401d450240080f0f1450407100001458080101c650b01d0310742516001228207038041044132035542c20201d00c3c103002c0070040c4540101c2c44000e59030a111000d040d0b4000c144c0d001e001c070805240e040c103400303100e08240300398848014010440c441d03000c29016030740c903011611300d001c4c2c00030702d1910746050446502040c440ca03020350003064000802d200316015100050322441d00b080115030240d00048560180003000304002403074903100c0c07801c881d160b400d58240c40c40180c0241d1a1000b84842140080b54440c1a034104100c1a80c1d0b44054444085184c803c101c0080d140030310341003c1d215800020301c46031060340c04948805012220260500d100c201a0120095200c02c80d01c03450f25602c0c0c004c0d405168402040e06004245c0c96590700c000c1092850b0700c105129109400c1024010001c460340801d4100340323094010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 643843785 1250 643842535 643842539
    0x20331020a0311031c020c04110c120a02031603030c0215010b03070f020c0315010512070e0a0504030c12020708010f051003031b061a040606020102211b031816 70
    0xc41c0d1680c0150102401d10420101c41c6100382d01e00304001c41d0f8802d204820a1450b00c0c040308000e4503900c010b80c5642c1700d5802d1100004010110400741e60403525200003401d006081105440c1259125070307900c0b030550005102a07030040401070801d03200c0c0ca000740c6010500f100c00c1d4030000d003007141d06261042c00d2218500103101500080007a260303c40c10b40e00342035144041240c400e030f15044a0302000c5a2510030403400e107074003069014401e4101c940948001440d00c00341404241c03602400d0080e02e03007a80e883c400140d44010203401c4550040e000781094000c890054951600c02c0c8410025800568025403042012420034400d5a00d90748032290108280c2c1801d18030083c0011007480040c0400c00703080c080007090382d030055a01016541c403460070011403104441d2074204401e031100352032080c0d1030114005402070060084840c00000c0d05004540540b0000d01d568440201401c8140380c2510520088440c0915100942c0240142c1c0f14141a400b094001c55160550016130001081d55042d02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 643845035 1250 643843785 643843789
    0x105040506030f1b1c08091c2d020603070201050106020f01020a0c1203020c19020a050a05130f0e0a03030b04061401080f07050f030114130203070c080c0f0102033102 73
    0x100081300e4600003003412074806400140841c1104111001540308160590100028a0b00400701e018064801290381860403004815000b135a19014044544041d800060001501c0e1a05c1300d69841c01040384a0000e26004280035130812100000980c0d0f49034010300189030104401100205c0c410003c1d4540208440300601c00b00384414010182002c031703c4040200d034025015202841c0d40403007140d020642a907071030451502c0c00b400590090552a9010401d030510301455001d03074001525041024400c1b032120401072040c0c89000e031000382d44002d42038000d001800a210074500079900412200c1119081104440075948500e4150140780403081071640c20180e8180d12540840d0090540d81c0c0d0b200c0d09550b9131050607641140d036200000003003085000d500c0109083c031407e03681c1c7c00d0302103000e407000010ac0c84152080720108076183d0721007000440c188024448803406400381d804261754048502d0981c0c00075120400ba03580d4020300010300c0321054141c290409030440700d458840c00d0b01c1d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 643846285 1250 643845035 643845043
    0x20d08150d060509011b02061603150e04140d02030d1406030712031e0f030c091412190317240906040e0604060f0e060c040b0717120105040506030f 65
    0x801c00c0c1c3e03c980003c0d03c082e10a600c2226103c40401240e03503505000310009413a140101d41d401d1906c81d00c0c0070008615813103031181c900c42c05515864010f1041c2000c81c04404040010411128804001030b11000080140031400c2460515001107031204035105501043da10102c0202c440c40c100c0310100802c9950006501046809080ca40c088800050404903040740d1b1003000c0e51001d01d081c91001c00d038680d01448012044066580800c5450040d0b00202c0e0003107a50b10621058080e0841404100d1600a0500da004030082c81219100340782f03172100035108212102c00f170300071401c00280e403410a031798048076591056680002218020844042915500b0b18281d520f01401c0c0c00c0300043c81075115540100102c0007560102d0f1500d1a252a000014090b01c881c11280c0d1410500c151684a20014269019002e20141c036401c1c103003840070b550196001039a096442d400c4501d006402c29010800070200c00031408030800f01981000c1c00c1c0415503402070122400f07548200102d0340d04a43c086 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 643847535 1250 643846285 643846309
    0x1d16050d031404060504050f0105090f0603090f1e0d0906020a1104090204021926041401060506070501090b070815041e0f0b040b01020309030303181c020d0815 70
    0x44011164400c40d0504942211280003410306404000802141040e00310000d8001c5400c12110550401024401101c00d405605021504100544c040301c8840c40c0060103940d114902c42c003110b04910400b1549442c180307030385050700501861b048c104026070000b441002d540600d241061a607907031400c40002c0d0346d1056041c02030002c200600f00c1c14000e50300c0f07800070018160014425502c1e020469504070030780c00c4c00d148100c0420601c0307e03456601301d481c6a40715030f001141c0804a8480d52151908414030031041c0c40d03003805550307650700412036540d020040c03c1054054000060406494603107003000150280c9032006014001e0200314040203054145400081c00b500c010620046100040140c1020001100c0c403c1d13050104810f0203881c0b56018100348401103e003403004c1010301c4010b980341d00c22a15069050341040000844003010102200715550340b003070464540f031046109440390f03014000c0102c1c0041c1c0004443d020345070f500c110b81c03a42048000342440c204558410000b00d000380c0380c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 643848785 1250 643847535 643847539
    0xd0c0c0b070809040204031203061403031e0d050f0f010b040506250b07050d27030810080313060210050c1e07020409080a0212090a0e0619091d1605 65
    0x103034101c1009000002c0d200e12000190055442d16100c1c034044032080c4070341000c84006407821a00040501c003071140007804035000b0380074501d00050003018a14242c4544499814210b040251a80201c19481754504c143c4034005081c00505052030890098071b01a4071201c001d05041c40705118940d28141110303070302020041c85484100520ba600400100503030030140c04030110340200321510f038226000b0300300d0312000756007005070808050702e2080c60b0107071080e00c42c03807180d40b4603090000a006140e55a00300e421140c025440c1540c4203006031556100175000001b03807031a46010004107404100c8000484807629081c000e5103000c00c401d002d14020650729000c2100702510b080710200c4274008450302c15070050310600c06100c160610548540c0507200f10801803244042e03842044a4084c241c3d1403401004111144240c43c00c045180d200704042c0c1403e51205400400c42e118854484811000308196800440c09108a00d10811030700c10340084902e01c2c2d003040620001070071800c140e00e0295202 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 643850035 1250 643848785 643848787
    0x9010b07050a06050f16360f1410080708161b060b090f040312150b0d0605091005090408281205060402040e190b041404050d0c0c0b 58
    0x140c01d2080c40d021403858050241031400c010721002c01400300b9424403800c082450034002d1449100101d50f1910018003250100036254140b9013900c002d51020300c4103590240001e011079468001c0a400c1040301da000d9240321030442c2c0e80342030354200f481202010f4900d50412151a161668000c2c0203488000c00ba56400c181d03a000c0c00042c20702410304020b184515441140b000d01143ca4003800070b104038001c01c6d00c2650031100260400c01000d003907510940d8507a854128061942e00404044e00406402c000b040d41310040108041c900d00e8081c00c0c03104d000d681c011810030701c0c007420300c140c006002c1c25074184a0021308081c00b241d2950341c0c00540180d4032590082d984d0580202104403807950003a00e00310184030442c03601255500160300c1c00c5441303420100304030580328401004101e00c00c03441b919904e04840700014042c646000b00000b0300c441043e501040321442000024200d0300c000000038040130601c0705000038003004010314801030425041581d503c0a0f941c4500314841500e00c2400800700b8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 643851285 1250 643850035 643850047
    0xe1f0c0203030c0706080f0f070c03030c03020f0307080a0507050a270b030106020a0b07050702011202180402030a0914060408030402091f03060e0d170106030b1210060302130b09010b 80
    0x60420031a07500f4a240020307035841d59221080200030110544981e00b1034401c00c2c010602c541d8004e8542402891305c0d48406a001c2125a0160050150040c40c036041c035500740000c054802140c0e0044d8810251a5901c44c564981030703a440c0308880c000341c504010000e0600c4110005600460301248001840d4a2781d003d40f8910341403502000c4190704029038049010000145140e00010307140c03202032044403600241d5440070412034403401050f030042d0001c0c807503c02c2c004c100120350b40146900703524070740000d04004111010500f80e92040d101440a150b640742440e06000c110040ca0307070581703003e0780030f000b903428140c9400c3c043c6d000261001e071265a4080c00309125840e00c3d1040078031070650800c01403800d0fa0f00c0c00c04038028445400d89400c00e001d0700d41c0d0194420701c10031842c00d04141080e4003411f0343e42400d4086000b00305101c487c1c0d030070520201a002c0202c10412141501c4569a6408560326045205200312003495180b41036415041c195100360341d9481144c183e06594150340c0b0a030700c2e02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 643852535 1250 643851285 643851289
    0x2190803040b07080409090b390309030c070b0a0f0914100c0611090918070b1e040803041a0f041206090618140f030d050a02040506030907060e1f0c02 66
    0x4405d5521030140346140003012010007a07122001c900c41d03020047e5240d10080c00d80024a0144403011003201001103040420108248000145801803c400112410712482e0034940b41740c1150f0343c101c00c0701c42c000411541e00040e03001c2d022941c200100d1900c64a040d01c0e00907070607041c43d81c0d07054480c0314142d5032006060a174400c4218003040ca40010040c8500a5081c40d11800e03540000f0a05000b030f541030780000c1c1141244085804038548410041a190f031070404001403940080b5032030756241c3c10b03585055502e04200405400035000703074400b03103030b40e5807800010307c0610300f544101051031002402034078255418042907504580844800750f00b85445403810310020190007000a01c0d6034a00310b20300243c00441804c20350b1041c460100e9103082001116200d50f0341c012155049199442086040c50f01601c1d50055900034440c4103001d400c4c1034031440041c0b0940c00807076039101e00d0b5102d00410000b5541c028010060317a54151500080d84901d4480e2080c030311612232494061080903850f541c115 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 643853785 1250 643852535 643852537
    0x5100f1b030216030f170c0318040b12030301140a05031011040906170c0102060c0d0b030a0206030103051501050f0d0f11040c0e01030e01020c0616090801060605030402190803040b0708 81
    0x5907810003c42c0d6241ca49901e403664214084d0391003550200342c11b000c4541490500c10444201c100507000075428007a80880000304c44000d10381603900b054540320140142c0c1c540d240b60b000304103442c0c000b0755160b41c14001c110350108403034500c56219101c807940400c000c0e1804694620054501d25000c1040c2030101c5180e451880b899101468092038030313100086000103100d4030799200c0030000560310711715110780049035124029904000c90260070003003006000740c60360060180c400050141c40c0c0842036a000101c080c1c1090340283c13001c3e0040c00b9260350313402940b50a81d0140000721080311303038442c0ca000414184a28580c1c000d11510480c000e0a00b80280d910724482203000041041c4065110914018482c28a81e41c0c1140824144080d81c0320b207800600a8410b5000d2038001400180d07140c5008014561140e07240c01e01f4006070080110305050280680d00c054011611166600e003082c0c410301c0b68203408110082062490f0b284184200f00d00841120100e840052001c0d4541d8014113021040b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 643855035 1250 643853785 643853803
    0x12060d120804241a0103451112210d02070507090c021b031b120d09060e0607031202030c0c0a05060612070b070209191505100f1b0302 59
    0x400e07036000c454070440340c0c1c90300b00b108030507135181102c000d0750307450b80040d02581c0c1c05101d13003007404900c0035513030380840110300c0c062a0500c0d0b40700c50700103804002d10402e108120b007070405460308561505440312038102007003640441d9121100505034204c0b407a442822505031680340d91080300000400100b00a519019101066080310a0351140c5507503603d0b041c003d00c540c51503031004d8040d0000701000c09070700400a091100307001d009014031000d020304a852000d65103645590288100602c12901c0100300011190f4104540300c10366424141500070f0805a030f0079010718802d031020401540020b90002c110700d1303811341c01d40c0090f880791034004091006002d081700e10398a604c60f01d10b5000620800107002c5000c0ca07801d6034104404040410078039214103c3e4090700842c4241001504014203005000aa05c203104030b4035264106640350810054403510a02c030b080d0814982d2003409103241c0094000b160080350f0805482c06190a20080c00f5000b4004c00c3c80d00401581111009042c000d0084a103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 643856285 1250 643855035 643855073
    0x3010c0c051c0c051c0e0d03051905040308040902040f12050c09102c060102070b27130f050606030108070611010e06010803071e0b0406050402040e0d0512060d120804 73
    0x2e03003c45a904441d245440e08483c140058151b021a2840c0e0820317120805403150980d1300da910b89000290007102008400781c140c02009400c000000202da5150081e0028010003032016a0f07451401c0380c01c0d2006070407a0441d002c2802d90000d800006a000a0300314070038030007990031a9169550441d0702940e8012030740a060160b83c2e030b8450810f00100761401e0001c108401c84550340e07507180d44004a82e5002d05000300d801c410820083da01074555074103034040b00c1c802200c401f18213028a081c0070607101c1c801c0c4c40783d203650aa00d40c2c103928a8500039001d0aa40311074140d45c01801c540c504601c40b40d58403060b10480c414008003843c4480809420340100300001421422200d00c1c0d69075000c441e5a0b5481100207a5102e59807000d519150003074465080c02d0150020072140681c0c655403144001030074084d01c22030303010b55103c03140340c00302c0000d20690985c40300684500380c59140c08021202d10b41c00082101d8070a60800d8400070010710381d01000381010619183c5003000b036403940707895000610b0410000c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 643857535 1250 643856285 643856293
    0x30c1305092113080f0618070302040612020414041e020f04050412090b070c090b031e0607120b06072a030c090c050c0d0f090e0c03010503010c0c051c0c05 68
    0x4801400c0c8000074940000300c0d00741007070f605a484602c070b82c40701140c03000c1e0f502c2c0350800b502181c80c03050082c0c0040803641c0c810050b26952a501da00260071034a040d804010840740b4032805030254030f0107100703144c41000b007440d2040b1640f5040c1e84132104480403148408109910700050300c07e64035980010030130000003810802180c1010b00704480400c99000c00034000072aa1322000c102400030009580030158800b11545802e424642c0d9180030f0321a1041c00c5801d0b03c10301400c0c41c401880c140b01410b40c464058003400c02030034110310003021f1a84203c400315205003003c0700400142c8030071084900e619080000080312009103284581101c03160b030280015241e061314040140b00000c05070130200c2e0081a800c003d040500002681c071030040d61030200c3e00d0380103444404801c1d80241007800303601605150a0740c12645850f50750401020603600c00080100200050003d8242441107841011513810b01075500c030410754403103540700c41c94406142d10a202a016400c00c034080c21020707445a038018217170b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 643858785 1250 643857535 643857583
    0x21040b0318010e03130302040c111f11120406020304110603040b07200c0d15060f15110a080d14090d080f06011704080c1f0506030c130509 61
    0x1c1401c80526078040c140719442c1054014180200004503102c0e04011003080c07510a14603020030000f02084c0b2030702030910242210100a11401b408003c4000041d502644001001c80717801340d04035002001d0000d003030f003c01c00035103140301a4107010755842544014056641c0e583d515182c0d80320f0071690070190700900c0100a00003045418400e452143d8820380d42d102044036505840b42c21800a241160007035000701d0804a803508000c1d000782502c500411200960260700411a02116001d510906d03080d07039184400c0c0f08030300071035104811840c1a03260910100e0079605d590750302c42209440c010700c1242c000812110403141d0760002e10f200040040b1100080c50b100715415241c03064869000000f40e50a0001100018201030450007110181d4909221442c1c2c0d0b141184031480240007034400142c10b001a140b040310070130040c20039034602d142180c9504c2c0b642c844241558000740c080c1d48607400140e000542515200001d0405500303140c0080703403548400070049d090003015a290324103034106440c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 643860035 1250 643858785 643858801
    0x160204020c0f15010b04030803060d02060a1d04090c050d03170f0a0f090b1303020f0d11070801050603120a030f060e100603060e0414150702012a0221040b03 69
    0x2c14800e0908801c15240d400c9203020805401d080c090051380b030b510909200c03c1c008621410091a80864050540c0c140c1c90159000100584c0240507207100042c0c1c0070124401d503012100030710524200c180c40c2032056003090ba55030400f001c070500500f402200c0714038506007418400c1d000ca1040030145407442c5298281104058542042100c50400c1242000c0542d071103040342d80704908159801803c284400c0e180d050001d00750908680c0143c1c114418507510102c41942030144540c1c640c0191a4030203104910b403070b403d003040780c1640030f45442d0345030904000c3ca5490204000d01027118440801d07070303100303520081070300200a00074140c04854a0b02c40086111190584041e000b60000b010400310940d03107900c110251600c2c3d00070150642402804100082d0608054884001a00040e10f45000c0f0300300b46011100d008854640050b03445140c250105007080d03007038441d10303126140c0745030f00704c1d030319803800b07556188007410480d00c0c0101c000b00031181d000b00b8002d64000e071082c078154990342d08001407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 643861285 1250 643860035 643860043
    0x3120307030b04061509091806140601110708060115051209010902010201110f07020d0f1e030315060804021504090e011d07031502090f1005030a060608130602160204020c 75
    0x21118003c514202010582d000f59105a5410301699600c06503079074109a00704000d085540113060122800000c1c403070014605000d400c102010900012440d86080c500040c0095900c035032061041d0000c0805111a0f08040360132411365942c4c900c0d90070182c180340d400315103600c100c0407104140b403a502c050200c1c55a06400800015000764001e01c10f1040c020584036440c03055019400c0380c0d6208006e80b84c01410309500d41c00065000b4a0301118200650f00d803040c1002d40040d5991070401c100d0031b00d03010580c15225415071031014420100303881c0c1c20203d01918120010740060b1041215444141c055234007081110090305012200740584406850568003805141e0307400d1441102a07560903108010010b0090101c5e5009025411003a5011040c072000f9030220f102290454103034040082d0036107034500410711300789480d5a5a5640d03c0c00202c4c903030032071760303e90000c1d01041840011302100d022015200c0010716042600140e84140743c202ca010000006240250030900114007c1c1900c24049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 643862535 1250 643861285 643861301
    0x161211100c0512160e040606210204030f0f03090b12041113060f080708030a140a02070e0f090d140d24030804061707021507034a070905060312030703 66
    0x911741000002c15581040140c034a18000c500000e00300450581c0c440000c100710340d07114202020010b182c9922512510220b1a84040c1940d0010517004644200741c2d0003000c0000605c4402041403c24010f00304035090594060805024940707510b03204200e44c1d0b40c00c00e0b00790880441c080c040002e01c1d03862920341c004400038801c904950042c0f04c8005151800801221a069280c1da1040c01013482400f0300c6145030403581045e0214851031201103821451081c4c0c03180074000e0000850110718107480075925107144a50080c0070045017a0b40d1441d0400782c076055805c2203100394004110880603603594445500054a01c40d01c1c01c10b0403900200740300082e0010401c0d1030300c03a81d41c2030f0007040014089080e44000d880600050780850401d03811110410382c101d40148040c074010030001d444140342150340d40305e10303180405c086110f8280c3c0c000200042e05130503104100c60500e01d4501c1c024084585901d014440d20980e41d4031a40010303003076541802040c03200c04411842a842e8107188a00400810342c40e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 643863785 1250 643862535 643862537
    0xa080705040c0903050601050d0f0c06020313120b180f0307110901050a081c030b21010f0621050a080a0809070e1611030f161211100c051216 62
    0x81c40b02c10440e8419843e80f01900c0e040341c02400240d10388824005241202d071029214101c2d503d011800150341c1c1d5440c4001407145a00658071051170008042e82546a0f610a2020045401c0f0900015101c0d0108a03407120080704684d40c0c007125144594240080356124003202d01000903200100201742c0fa0407801d00000751103403413181c2c1e00c0c1c40a0142e514080d0042440030341c4440105159480008614080740015280100301c6c0302d2100c0114081e54140a402c074550162000d1111800c4024402d650241010380301c10b124152a02a071070702545078011405003466034428401c414404104500120141d00411050f0b582d200c81030002c0880c5410303680355026009403040000d80f0151064841e019883d541c1c0f2111601d400c0540a0b00c0c1c403442003070744003e10700007480b0844a4501c4c0001400e20b030705990441517030991543c6861040c280522150006000c0c12203083d0800f410f0006100541da00a00710002d0003054012040e00c1c035004038500c003c1c1c6403249100b00942d0a201d06283e098001c81 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 643865035 1250 643863785 643863791
    0x1a0c04150504030c0b13031212060b1209011503020f060f04030803010305070f0b0901081503060127020703050919050a0b0a020d020c010e100c08030109020a1e0c020405060f0a08070504 81
    0x51740410b040501c01c00944c01100310110741d0600c041407034840401c0004040d41051032107110028a21310940d105544a03420401000c942d407001c41c0c42c440780e002e5020001000070003289103d07008010414800b070002038001d041410100302d01e80c0b00c841c102c0b10510a8030b041d50381c5913903a030329141003180d20902040710301c0d014508001545112030041c0c0025154504009420030106030011218090001c0030b013444114070700342c0c4201c1500c1c18882a030203002c0024004802044070f00542090400040c44806440d204000000209621005441d545803044803440e120504000492440004c6c40c0c001c04c0e4000600000007031490000401840d801034560281c455a110404040c0c1c0c8440e0031201c01c50100d810a031301c144091510010b1419002030034203290102c003185807600380d0641c20980140000c07980c002a0100c0c1c064201070104c0309450b500c0301040114405142c01800c51040180090145484002294450740d5003441712900b0f1501414243c0c14a0703461350055591005071140da4001c601e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 643866285 1250 643865035 643865039
    0xc09033c0303070e01031a2806020610060c0c0e132d0b090114090307030e0604080703080315180615090306130602070506040b060306131a0c04150504030c 68
    0x15020003601e10a0f0301d552901c2090412030401540076103820703020b2a0080300180d681200710b640740c0503080000c169000e806224070035010354020b1061215048030056500540070082c000e00f621910328186e40d81c034030f816401d03150145801d828807241c91304290440d2841604118411040c1001b20a1450040d8600f50803041c42c0d981c10290f80c0024104441c4015079111408013207540c3c2e0603440c0e04420601d000240c8078003407240c0035580744003d4407040c4850704009071150615601c1210855055812a101841e0070300e08191180d8515007032100030b100340b60100010346545003182c02c1180c202000b4040301074a85424804090228089034682d10480460003510103c081030b0f0144e03446072300e001c0c00925050b1602c04e0504401400c25000702e510940800c0040000f174820303c05540034522842c010851414000708150030008000c2040c0340c0c0608220012011444003039039000c1c80b20f01142c0303140441d1140321498006104030703000f014450100a62503203805501c40010000c4900418511403840c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 643867535 1250 643866285 643866403
    0xe07121b060203031602070b0d0609060506040b03160e09190507020d020d05030a2007120c08031f08010608161a1c0f05130303230c0903 60
    0x103258001d000c010b81c010700002d1801580c10890000080c02c07401107910440e504d115450b1942d1000780180c40613a11820700300101042802000701800003142e186040500308551400c040c00010110300c5030040d1212a1010240503a88454491101400700102440c0030048603010440c0701080c0d81c041854100040e80c0d803480414042c40301031043d4060b1024460124003101e0640015008241540e6101c203c2007130300f940280007080a11200080c1a1549468108586176020100d604c6e02401050b2903030a000030420303c103c0c3c0d4011604984002c2d800c8201c150200326600c550040e02c91580380c601e000c1116480011402218100f10f000e0f1aa02c036118100030401007201c0210000a581c144203010403043c90701662403203003500c0c1c800010300a0104540000f41d032401d031520001044c0c02000d407014541d041c09210306450286081000083c80108911007041000380b403045645d001280c40340030b90b601880200040030660b8500c40b540240e0309242d11030076070320005240103102e030401001c0c600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 643868785 1250 643867535 643867583
    0x80d0c230c0103020f0f04030c08060f01061b050a05010f1a0303072607050118030f0512060609030f01050103050d08090a152703120e07270e0712 64
    0x20344034000d0000c050203000158042e401109031446050010300254001c07015103405440218000c00715511403070700d444095420228051f045c40000154440103014240d049080001110645071811104104a0401c20b00f0480602c600802c95424018016244000b5030001080001958100c04001c44900105640e0784942d0000030032007864440700103d80929500d80360100c0451007207461a00e11955541030858400708601200790078102994000d050744080501925601414498a40344060301c6030001d81c1c80040440380b08605c0040c0300320751070710180148042103030208002e001c0d6503181d10345541c403100502c80000024465200254842c1d10001c0c1101d4050f81103205821202d040311803500240c03e000507100524855200e40c9003040d40301011107042c0038069a2100c6100300103441c60400ea65204078015501e81c0150400d002004000e00310300d40d8514004000c01c403d07690810910b024004030249401d640c0240d031400250300d80040c2d41580e1040c410440780c694005540201012 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 643870035 1250 643868785 643868843
    0x60f0a06051c0f05010b030f060106090504060303050d0c02070b0408030c101e0b0a0b1815090a180608120c15100308090a080f07180219120204080d0c 66
    0x2e6080541540c2c40400d84181c8054802409440086596034440012a02c0c0064220380001280d100034010081c0c80d52040169015200445040c484140b40d5100240385020320003002c901c45a5814061603000d008022142c02440344650303554031690380350100340c0c072a04810414000c034000c0340340c500c2d181002071151000c503030001c0c00c254a030240d18849500080c9040180c081d0081c800500c08101801c40c44081c1c0300292010781040211581c18040c00310140500024034541c0005103c190b01a03a125030b0000151000700040c0c20582001c00c0d80c10000d011698440c0c41030b4000d454011a00220910050818103035401c210340720324a0b00348a90754054002c840300ca07524040b411040c0300261403000201080710008221207541c0b40c44140050034041e030401c0d44116035000b84410014900c40c1100c10300f6442d40480118101003c4003031400307404c40d0a603454030400c1042000c503010303d4001c0d41600c000e0100c0c0c208a51b510f40c683c9101400354140720b841613800c1d0b200344190803000d01102c085968 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 643871285 1250 643870035 643870069
    0x20a02011b0c170709020d09050d090612110d141b0301030503030f07031e24150813120c03030506030a15020901200d091d0105190503060f0a0605 64
    0x41d070b50b0316200d0310740800d4180c0c00740740905014484000402d0311840c0040c00d25030b2121103000a100f851481c1003403801c1d0a0280c9a070500c002e0380401c000305d40c2c21403490070401c03991407004103503282d901c800c0c000c0074440c00612840d00d918140030b2000e44880d51403164490004203461b01485072001807074000c2030109210060903940300f00009143e584695442e29040320303440c1008034184000c03160000d04000e81d00c03241428030f6503d600401d01165620320802d000810300d82045046030800c50f41842406459040c04180704401010407240f11b0410320001c06540c2140d246c10001da02c03800005d0003854070700c2e8240c001900f080e02141040c07401003003202c000796114a0400503e44000c030a01d0283d00b15040c064140090040c600c0e851140d2001b000c0304d904141c0014040d21a50898042c00c2030505802c028400144513601055540103001d107241999400c48642e5070f4008440703c2050603c025401484e00342c014607050100400c600c0b0034040c020644400c06001e40c82d12141804900740e40803403481 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 643872535 1250 643871285 643871303
    0x31b0f03030b041103180606010302090a090504080903100218061c2403030305061302040e13230a03091a0403031d040c2a020d031815020a02011b 64
    0x980024041d502c04050120003800210b0b104251500806054000721000c4071007001807910108449000e00103158803d00034281141014030300700c00308103490958020150400c1d03590300410244007410080c1ca48502e0010f040b61003c80708440031b04080c0d041b004010042d241c04021000c502c0c134041041c1d441c0c071071408035110030701445106600b0240c410700440e091511948100048401540d6030008003a5002e40c230f01082d42d050940038000609045500041003602c140300c02d0095000b034401d085d400c4a151b40f602c5100180504000b4280641b03100e140d98034000e000e515020040340403031207820040c041d880340c0b104555502000c100380d00c041d40d008800d84000700000c0c0002402440082904090140d460072102c00c8400410700320780000419401140352481d1001589688218112486807180c00c40c03802e0740c0c02680429950510104014140441c4402d03402090144074802e44c010081419620042e40340c1c140080e494180140d03040c1c5c00030380ba1980c40801c540140004c280c003513920008034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 643873785 1250 643872535 643872563
    0x50a090f0e0a050709090c02072102060304120216260604030f1101021e120c0c03040e0403020f012f0f070210021501030602041409090a111c050109031b 67
    0x1d03c2c00820000601c403100758040b51601d880c2c411042c0528040d0000c18013241400c0c1c051090044d0708405a603a424049091001a01c2d083c00382d981165211448200540781c5803010703424101c81116410514403d0540050124a50301c450b03426103c1505000b21510002c0c8400c9032a0300c01200c0c043c0100e142c0511201c61140300b07030160f0340c5d00c0301c1d0a4001410801d04c494454020701480321540118040400e0841e0b0741c070310303160302c641c0c010311b20b00707481c07441c1403102001c0396100e00440c0f003240a03000120001500741130082c001450840c03600c10082240070005025102e40003003c145c0e100300c08411400c00c0003030154142c00c4504d8a1400c0d5681400e22035036608200d00c4400d180002d000f1802207608852005d00c008d40c00c0d5020714460000582c80310700344545408140094075102e0310881400c4144a6105400314900001c150480d8502041a00031404600c0030300011010a0007440d103c480d0b00103004040d88159004da1180d52040d4903400040504d140041441c00c004e02069462141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 643875035 1250 643873785 643873801
    0xa21020d0e0c0906150d0905060702010510080c01080a0e15091b01021c02032208120a0c0308150621011509060c03090b27090c0d020310080a03050a090f0e 68
    0x241c8001c17900311001791030b26401501800c03e6819034101280d0a170701ca00d052010041d02801010f503c000803481900030309152440c0160744910f41d80d40c05051286800104070008140d0b000002e194000008640341c03c81c2e244403034a1001400c5030052050300444daa6002d00da601c03405107030801c040590007025400b00703800c2064030b2903d003002c100c015403004100318070240389070840540c82070981602000e541c91401d9015401c010350f100c10540602002c01c80c00201c0c0390401d014684090709458002c15070341c0d0f5201c511106605003558941d00000114418a00091805042440400a6040700d0059a80b034445040100d0a0101600414945070302400a01d04c92400c4c402c20704d0281c41c0c80080107680320100e240035400700315030300c0a6109940440740c80782d00c181401c0a020400355281042d0f803401180a8403140a06410103210b0b43c2c002020039000f068103103242c0d014101a10640e669220070f80b5000d0301580c010041c0102040748400001140700603044080111016000c004103d039a40b540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 643876285 1250 643875035 643875049
    0x17010f0b18090102090a0e180d1202030405011e06060e030c0312070c09060308040323060703180210050403020a0e010e0c030a09120221040f0b0a21020d0e0c0906 71
    0x111282a541d800d03c4821780d1035960294400090001001442c6181000103001c01da9484551340c005d0a94015a0224811940401d1131070480e20724440c01601d0b612180f0745207024100740700ca901c808001903484070300351f0790059008004071005904d441840a000d01c09250301c90003019a425819080403456510b03205080d8000c0505511601d4144405a100c50b201d90444003d60003d582d14940424140300b009240d0191004443c4000314005d041d0b110300490300d42e690f4000300114101078651198445600d0512007146c4042d41c010800441c11600c07900043c06504603100991040f130520b44006240e513120f5850318160b40c910100700406a5484c0f0741c5032403551000d00300000095952814502040d00b9641c1c0e103071091201da0140c903800010300185802c600d003003a09120b05000c200804c0269482c0c10610f40200c60160324001e440d85240441501c103010329801054a04400c251000c2400c40540e0080c00000f00c0c40e1420080005042c0c00d2130ba407015280e80090b04001c0c1e84020031860314001c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 643877535 1250 643876285 643876291
    0x6040509060607060905061611071503060b030c030714030c0a0806060d180b180303181203010b0d061a1e04090f0603060c11030706020a02070f17010f0b18 68
    0xd86407503e003010360b965800450b44641c4054034650080002d0040c4460090300c030b82d015140f18030303258052960510701c40303440380b10600c40c4200003c05040064044c2e406a00880000d102e0106802c0d200d103072011100c00703658422500100010010003444060031810b20542e8010941d03013441909203030784482c098070000380103415a42d115609200340007001c500d034000c030040b1001154106108284601d001c0e81c0388000038040440d503521002071008001d07070000c252070f4440c0c0c0e001c0303c403010400c0945ca1103040c00c200c0101e400c00361400100110384000c1072401410b0342d0a107060108002540c1e0301c210b04001030400381c24402d0180170800d040c840c0010454103101c03512805180c078a09a078459400c000c4540c1070f440c1d488140d8403070600f0418001203100705289404a400c011401104103680d0540700d00c0f079410020150fa9010901c0358101d0f100300034810162528a0398102116201c078110034a0118031001c014a943c02c1c1000d13b11400708900540e00c51103006823826149014500508050301001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 643878785 1250 643877535 643877539
    0x303081501050909010b07110a180506040617061b04050109030221060a09050f1524130905010c1d010c05011404110901060302070507031217040318060e0604050906 72
    0x6000003551581ca404240e4006c4c0185450a6503070b08040c503000c407290a800700b0003881405181d1040119a0709246003280095448100060a544510000e0000c1c0030540100404000300181021040c030000ba2660082c1d07040e040b10150f803071001c18490310300d00c00c0d4003a49001940c91502003005083c90b088210780b030844241d14070003d41482d080e01c0c1c40d205040350301d085069100c1817180e0078400709110010744071b1040c40180c0240460000806002000600907003d2041c191720720f440c4440a078041158800c00c0100807000c2914813541d1031002c1c04590005807295441c0c81040503c15014281ca445e2034188038540d00544041c0500640b107201400c5016070303a40d501c0d0b5080d20550300b40d500683d84540c0c40380798520300070200c10081c40910399058010f002450b10400045000c9000098444112a030202d85001483c01e545011590940f1001038180d0f40d1a448092108164200d03495580c0c0050702042c01001b1550b03545c0841d023016960003140d0304820104814005c03420040030b00360380300c200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 643880035 1250 643878785 643878787
    0x61b09040219230c030313051f0c0305010806070c0b0901020f0301092a1e05040506030901060e1e010e18070b0a020106050405010e070e040b1207080606040501030308150105 76
    0xa4403040340d0b8411050314100b002440001c014607031800d4001040c01048040d4102c98206140441da050b62403001a007920b040380c901a00a00070030408200802c00300c1001c0d141c151002c0510580140949000d00f80303440032a0511001044030940040c0035442018180d4884230050b503036807203c06480c1c5014100242c0c654007040504000c03406080254020603c490340080c440c4118030206091501001c030b000c05554012401980c0103601201c0350342c43d40d4101d401351503070524960f0141c0d02d5120741d80c070850b003080c8088200b11031004194808000c49a900d0861810340d940c5400980740840e0b401011981402003d00500015815200c15a40400d003600425094a140c505040c45c05500f6880a008003200040000c0c8103070703084c041c0342c00800341a9400e009650601e610001a210010b0a8100704091800321294545e100c1d0405110411b025090f0030000f2230300b20300390740c81d04280e01440601d845950003140300c0381403d12800341240e0705a5200075280c0c0b211610403080301c584285123810030034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 643881285 1250 643880035 643880047
    0x10e03010f090308040506010806091b0109030b13020a0504110a1808030403080d060812070b04020a090f0605011b02010503072007180f09020609010c02210a03020f061b090402 77
    0x70a21030906000e0180e10342e1138a0389000d2814919001058004800d00c0d0007034410701c88091030015402d01c40d9141128003810640700003004940c196900e42c0301820380000ba0701031001b80244200f801d18414001da03900c80aa50703c03841400240c9084034654112400100040a800c5102d0407040f900c140d242c95002c18690354828416246421541055405550008211420003220b1040340000c01c1210003424a000340d085031400c250250444c040c0c003c208400c0020215921203004502030305070040d0400420b00581c022400230205401164041000419580504291300301490401e942c140e40c0e961943c4e0f5034503400c0307443c111100d504440b008540403080b0a2105c0600c003400241c00003520011004401c03034110000e5400b032100e03413030750b151a20850340c4c00350700c500080b0b601174882824049051800d5101013903109101c40c0440440750708814052180d01c20110780c19078428002c0e404c030341d00d03011092901a02c41900355059031400c4600e4490407028900100a4461981d00920050a0203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 643882535 1250 643881285 643881311
    0xc0605090d0f110111060106050a0311090d0c1706011811041a09010e01170a0203070908010908070507170c0d15020a0206041509030905090408040f1e0b09030a02010e0301 75
    0x1802e444000c40e000c3c014030703010341c4981d68412034081c03205030b44000410107540741c00806045485203240280800d91030b1001d14000c00050411030b0900da1003d000340d81d4008840c18900e01c520944d00a400c0880d00c680313090300722040300088045c10380e01108802c09840303407580100380040001c00c104030003002c0c007403100181c0800805501e42e01c0c03119200e86250754018080c001410700852900b9141400305a90320f201c3e1074051800004c1e88006041e10040e40d940712498241c1e440140c0b0747c051801582006003000030040b082e006006058840c00454030030607110714086416064a0300380c0c0c00280d00a5860f1070140c5420311218485034015411555818442c02c070b010309aa00c89080d44001d68400028401003190845a0751581c14402200304400f04d402d66004024000718420584100c0d03000c4003260a0001c460200c0700140f21034190030702d94a42e46c403811150740c0c441d02140c1c035016480400004000341c102e01210f184202c000d0282290180e65801940ca6512100125030559030310350186042c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 643883785 1250 643882535 643882553
    0x50a0b04080405100504030f020d0201031b02011b03023609010806090d030527030424120902060f0a181409100e0408030a150608061c0c0605090d 64
    0xa580254000c41d0b50341d003080148641210006003c0702080010081080812500c12500c080d107541210030a03583e9004e0700040f809400400c028548903824403100e81001c5805510128000402c8010340b071a540003400141c0403405a260888440f0740e80d01c80e049812500130361151f400e01e55040508a0701d0b11a2000318001030001d0b00310440c6640705005218604804000d040181c0d4280d1809110a26000031082001994101100010707820b90f000407010140920a85003d0014443c2140385170819000d120103040f01c0c0d181000200b810700c4009070b40c0340d03a2401a08400c0b50060318081c501030940c2c94034089944548007620401007400b4065404610b80c01d141c1004020404012070115520385c10401d21010103048216200284042000094000051540d1050b003100816890f0b82cad40d00011005000e44004415508040c402c0c04a081908840910f00421085e1503282e41d4888420741625a655244805401c4020f52042000f02a1048004201040014144c10035070001c079901c0c0801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 643884892 1107 643883785 643883791
    0xc03121e13020a05060a200105041443090f29060a050c0102070b18031804020903030409050f04110d0c05010c061b020706110c1309050a0b 61
    0x2910350082c84030112456460300c09407880c41130380c02580c8c002d01040790112003115002404950741d01c00014012036030408181808503041c00c120750340340401d040c1e510340b00f982c1152600740306840d610106000020084120b011031000c0b5030066030402d90703085149150740c00010003c4074030100c0601c030b440c4151200a071200fa0741c60418260894151246400e03800740c030b41c00041c08904014950329094460740c1c8100c001e0705025840b103401b0b44c4030300c9139001e0451082c82e00c2407030401c1440c1550040040304c000604a170700e86a9159810419100211030500400d00c401c0d080000303000c0c0034881034011240440300c641d085a050751b20789845c1d801c180115810490940307918020000035a100714108108180502082c6010749c500070b40d0f44031030340550400032301140b070b08a40d1107070009405040c15100600c0f0318203002c10400c0000080042e4481902c42d48604403540012440c02c0300d070580 = true := by decide +kernel

theorem cover : BRFrame.Cov 643705035 643884892 := by
  have h0 := BRFrame.cov_init 643705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 643705035 ≤ n) (h2 : n < 643884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
