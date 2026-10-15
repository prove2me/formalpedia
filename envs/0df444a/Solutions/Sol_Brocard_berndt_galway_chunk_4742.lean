-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4742
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:35:14.722003+00:00
-- url     : https://prove2.me/submissions/96bc6269-862f-4ca9-b8f2-329c36b72966

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 852697841 ≤ n < 852877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 852699091 1250 852697841 852697847
    0x141041a071e020a112706040204090e0a060e0325080405100806031605010203030f3414090607030f03020d110c1b030303011401021204031401050109020a090324050c030f07 76
    0x2201d2000e44410f0034446c541014000542819a080840100b0150400303071500011011218609001e498070741c841c1007660304221081c0280055070340440080c600b452621141c02041c22142007030b01e0040c06201a101082140440c2034078064007010300f290411800c80100540010720949000d4442d1103a0100112491a006c004a0644006901640c215202c00d006044584005000000750035664481e0120159413500b00303d10b5180301c00051003c4070341c0c20740007a10242941c0d03801d4060040c10064620b441e1160022502104da151411000384000f1180c101c00a016443d000a0103030b062800210781c0c0c2003404050f0801c3c055010075105550401049107880f64051454141c06400501c01002191810080e41e803c003101801551420542000355001c254040d030000c4a0a81e49615080312101c1c09110702c42c050a0302030701c1145012440c0780c02130700b101c146200c0241480c4200c045a03040c84441002c040790043c54401c00d0286051901841c0340d150004c44406025841400000345105c0c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 852700341 1250 852699091 852699109
    0x924050102030405010c0212030a080a06080c0a060c06270c0503060f04080304210c030215040302120903070f0e062407030c02030141041a071e020a11 66
    0x8050700114a4603207001d00558000d405082c040e40e00141d000941310150800784000c114820390f564a42c2c40c1490550070a03011100c2c1078100e00010f038801d1250200d01d88602d4503ca040d20124100206002081d18105016091880400001d01c1908242007030001540c5078420249206036100d104440e203134002c2c559502000c0f19040241c407900004540810a10402103030418054130f801030342c6005112102007010070482404000840300080601071503418048152103049044001c0102c2c1003a84000f581c550f07141504c9031102d98002142c40d41550100701c040c0c020134a07000b001c40006d80d2203180125400701100c149024a001050319800b40c00449002000f40901801c240c0c200400c1d500d0440f900308015034226051f65860600d41d01c00142440e0403564080c1c8200385081d035840720b00c2050902001200d200300c03540c1140c0203000000e00b4080c14501c0344901182d2108503075944400c00c880018050122014940326040c6180d406940414901802070140781d00d408402010800c1c091481 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 852701591 1250 852700341 852700349
    0x3070605040f1d040f1e0b160e0d0209060409020307080a120503010815070302160b010f090b0f0d081b300d05041104150512010203010509151302040924 67
    0x203090a0000300042e2461051603401405495035003084c1b0080a02c0e4545100800d809841c906803503130030801845c2454241071110222490003001e0f454551020403410340611800a204001403000580240c0303483c0c0c06034a22035001002c460b26030390703a010300c40d40f10341000070300359a8040a11040500715010701e08070f90407031349081700a200d5640c802d410b044c07200300d0140c804010140c0801c031441e85444060400021903003c0c401d000b0095141020307400301c4c06815817044d0b0095040419041c610ba803601c01c1401c481c1025107400c0344400b00c80c0361100c4648a042c001c40c844103254011354082d11000100e03810350182a081a0341c01c40c0401051030140708914100c44024042040b5504402295803c06031300103120b1480d0050f005006000113040d035541e00000045240c0805007000f1031718100002944072141e0758021450355051602003000d103038004244030f08084901c696100c0603220508140300c280311070182151030742c1c2c0b100611409031042c128034038030050412400e0403a1340701c0100c801c4121 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 852702841 1250 852701591 852701639
    0x5010c18090207050319020102180915060c0f120406030c0804150e0f120d0f0605031e0a022106071d10050d0f091e0503070f050c03070605040f 63
    0x340c584440c040107036000c00012295404180142c0035403407640800600e84108940000d40c50381908000d84500d040482601c0f4801c10084060000c100008084451102410742d8016590090355400c14034001801c1c0c4240500c1c820040300541403030340500035105030740c03c6a80c00d110b0788070319080843d9101001d8901822a041d090079281160803682d10542d0700198010503200c200341c10803411801c103400030b10320720004800044d11b00c0c408045403042d40c206040c025030070814181400301080d42c2c1c0420f940646400104030741804c001110800c285140107500a021200c0402841801c0703819944481003074841e44101c0011807041030058074000d030000d00d1040d50200f2110724034200403aa40000080c94140002042451090003042c021250b5030b0040003000b20701c14207a494a00000711003000d441c652400b125850310700064020046540254000340820198115400c016080c8018007c15a40c10321688600094a40c3c20801810468001070001551a0b55401044903040e40500001d040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 852704091 1250 852702841 852702887
    0x5010b0a09050f150f012d0323010b07030807271502011a040c05040306062607060804080a051c050604050a0207030e120f1905010b010e03150a021905030405010c 71
    0x99442000b4032207c501c04d80f605c201165090b08a5032081c0c80181d00a00002900c44440201366410703601d144982c07046901e41c0303c05c00d43c50047c04180502030008000c0c10000303890045a200351143c40c8480d0403803908444040e45c910f04600140000d8440c2c80342d2099105a010310125460041c810000c0381c400d403442e04004100c02004201c000c3c0101055101130101c02e002c0803000c51114440c06010b4507020410558550f003000d80d04541901401904881d54030210050202d180d01185140d003295006034001d8582c118424142c4803401003038101204d42800b02c00354141080340b50042409104151420082030300c0b80500c2c50140d20a4040c040e001c5036080380710f0f50950500392424054030703d6510907107038040084c0d044030341481041ea070035914903c28001000180070081c030425411041c00d08000881d80c40c000301080c0c0f20b1280248400350141c60304001000d21b50385404441c00566400e1007000340c16007040015190b90010344040e103a03586011410503a01e4026030103105492014038030a03203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 852705341 1250 852704091 852704119
    0xa0603090b04061d0f0a0606170d030506030c0d080904051f21060e060f1608190b06031f0905070527030a080a0f031407030905010b0a09050f15 63
    0x1024158094141840314071300080701490020900450680c418998060100c2d071060303080c9482a506140c0003036a10889a60400003078580003d8850b841e1031527414041100c0d51344a0000c0c0c100303200101070360b0300182020302d03403c00c10100a00500c014a4203c0701000a510f82d0030100150460544194040310b240d000140058501d08000205500d021418040b481200307aa551007500c202c0b03402011240d0248086c0f15601041c403601c2c940c00000400c03e00a25149104014000500900b0b038005054409001c80900c91203a0440b0b04601c001602183c0d90b17061803441c1005415004030300200e01000882c02003840c0e540c80c040c0c076008190981e02d0506140406407801101401c1845a0312468485c0c01d40e0300c05501c05021f520320702070080e100c0c00d0f203440b034001e000b511020031081e20a003010318111070f240b12301d0030098460340c1001c1c0302d1038001101e003034a1501070b00400b42150296404401a20005092001a0011481000d007420352001c65110030340d507905400c10094140e6401251190942 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 852706591 1250 852705341 852705353
    0x1061205060a05040e10020706060806071706040b031903020c010201060f0b0304110105070606030c4103100501090605030c12030d09020612042003070f09020f04080304060e0a0603090b04 82
    0xe2200a01c05d0550b2020303000303036200c00126400407108442494546d103080140034818003a41d031b8000000c1c1007089107942080d01d1041c2083c00105058480c03651581018110f0710100900580d10b10140540c445c44511403c000c1c0d911260282c00c0b80c0107608105020541c0502551454219210440101d041d610340e6070304c0003410008050005c3c1007000c1400388901007001170203200000e502032550b5030f1400d402c040000e0701156816058041d0010541c0601c02d241603890a05015502004070320035149048000083c10100c1da0905040d00c94107106c00460551007650004d000c44008504464030301181005018410524024285040e04140700140d0722001c1600f001644034401001d43d8030f008000382c44402e01d084192000d07036241e481c041250340c280200400c0104070725001c400410005207844100d440407030450007614040381d00811514070b206d041d9010f03140601803035002c4d20388030380c3c9900c8002c1c200c04007c210103114032a0040000740c154068800c0400302a000003000e0099a5940c84003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 852707841 1250 852706591 852706601
    0x10170c090c1615020904061710091b170705011115040515040303051e0c0a14250b1b07060c170106030f0b030328230301061205060a0504 60
    0xa450302030040790312140010050150301d0110f04201d400162580052414042100c45a410801818185480300034101c40001070310134008050080103d400441882c2444480000c104c002c3d03640c5100f01008111111030151000000402c3e10441d03809503610401111204001d90340040c03950404041c507082901103a078001d9110380a4000c4407241c22500b00307030b40cc1d00001198103500103a911010b010415920640080d401142c0000704041030808030304c040b10f54443e9079900d000384020b81c80100d403499506400c0d9254100020f0700035459010040c600000980034580c111032182c140d0000541c3e032401440c0c44001e004008007218100380041d60303618024813084c0322300c1f070910245070f1105844482e50500d550103059a55008281412b000c195101600c420b0390503a840703500248105081090341d00301c00c810809900107080d4003249403500a4036a601c044102c040c401d40d190b0840103801e504900114100d410980e50500780d0312290072003008a500940d07001c0c1d4440d0241d40c00b00b2544c0f44c980c100b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 852709091 1250 852707841 852707857
    0x609100207080604080901020f15070507020d020d0f2d02010c03112d120703081003200f010e090a051801020c241026030310170c090c 59
    0x101d60015480b5810345241090840382103a22500002e1040c000b544e06203d600405030070792009000000314203080868a180c010110710810101142020655540000310880350742c000d0010050000c003400e0265002402220545640400345400ca101e01641360b044d0020003402500c480325000c3c0e96004403203280c205501541000341e503e4460702c882001340a20300751391004005100ba504200c00760000002d10b001170186480c0c0001c0d01c1401c04071080c904441d81d0950526108400d41c2d2001d4800c5502101500701402840b40c0c00c83c159422018001603c0c91043c080301c130064103840140c011249031880f0b01d092900082420003199985410342c0003250080c1c0141800e503013031280c0103422030032030308194400c0360142e201140440b0031403c1700e0008820100d000b4441e1109151054080e919110544112902d110700c01d200c6841a2400c0c80721207400003080000d5075a40d050411502844064a00900820141c001800c210340c0d600080e24081c4650046d10042d186ea9940001d0802c43d0400c00d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 852710341 1250 852709091 852709093
    0x40c080f0a0c030f1d1c0203040510090b0708040f0b0403050d030c02030c0a0c0f0801150303050903030702040f1401050a060c08210709060f1d0616020a120501110906091002 76
    0x960320240c072024080e00107020340c3e03040c5c00d0441c0341d01411102c0c6000e1389480001c209007081c440080302d2a1317000c01103d0a0b11406e48010381041c110352400c4a807000325a006140e040307808200881040708070300040c005c0f075843c0f04198100d0b580b0303101c00c506c0c41d1189220041040d80704880000e200c1d4065001614603003800c2c0140c07424416400c60b114101701d80c9000889540d8140c0383d00f0f025055800707000c1c10180403000020000000701640b2051048280e000190501402040d8820141d608104440c0102c0d07001c0c100b4000301c0c1c1000308880251581042500301446604004103050401c2220300c0100d4490b965007200250786501e0f500604c2e400f02500f40300708030f5140958042e405a24848031302031a56542c91010051402400038020041140604100510035610b2581300c40d9240043c44082c0d03003201c02e90b50b10315400500300411640700c50000e4002c00f054800240c8403805291035010640144024806002040b681c51014071070705c01c041d6030240084c0b205c420342e400c0c0480c0d80b07400e04140340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 852711591 1250 852710341 852710351
    0x70b1210030b0c070203010e0a050a17130b0702040b0d02150f04080d1119020603040b150d0c09150b04031205120411041a030715210b040c080f0a0c03 66
    0x500d4600c9451000c50f91081c84107800540e2104500302403203600c0404040e0809011003e14070f40e10030362181040c403000b034680400d40349240381c108a410111900b9884208079885040e5803502403003e80c1d04044400d0780b21741d140c620004c000b41004601d810606900502e00d0340c0400c04e0b00342c001000c0c7c01590043c446d41a0510020803240010000043c0b0000c0548989002ea900b201125250440d0400541014142e8081050050311480143c0f50055880110031105590308400d403c5220700f006a820743c040c0c084000d100520500d801030406172000250140a41d41c180c00b030060034000c5030311a00d0392500c0c04200030004140c0c28450701e908082e2074a0131a14085900d00e4034410389000b079a00380d441103003e0301484000e151a108901509030031084240415071f4400c0001e858103201c0c481e40354043c402002d28200544902d100b0a02e2003c0c8081201700c1007003040d0108010260b0043c40d60089143c103203c4c688182c09030059601c42d20002e1704210899554552000c0a400f0785107460f414142c0318 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 852712841 1250 852711591 852711593
    0x50606090a060509011d130c141c0b04051b09150406081218010305040b0703090302010e0f01140703060f060c05070f0b030a0b120304090b0d02030610080f070b121003 73
    0xc51390340200344c040303004140c8013802c402601c40301c200684802c8440b4200107a44e0000303001c00243d0000c0383c010440c003e080e0401d0300041000100412a2400c2d80c4c41c84982000400042d04413441c00f480c0150116091200c082d0300305001d50701da980d07441d03078450a47d900061185a00c002980b1021401400100351290340f04596890404015000064003030003141401018203040c9440d5400c540920303080c0281d06003615140206400502060101600c400503e000d16000350000d6070480c0c0303400c049800226200c119540204010405840c0482d00032001c11a198440d00400c000c0c2c4200e10070208003640f07030002c01d441c4d142da80c840466440c060568009505003211010301e0003000b403948516660316081d0400340488241c140c20b184240020034500000034000010f07142500e1400e040001c50044400010340c841d051000e000354076110f17000c20445032481881500d02202e6500c812506007100d21680580c451160740a521b071821001c2c4540b04000d0100001550800d00c0340007500342d004d40b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 852714091 1250 852712841 852712849
    0x9040207051e010b090f01140f0a090c03060905040c0e150a030c210b0117010f050907060801150804110409021201201c02071505090615010c050606090a0605 69
    0x3804021a0342c40c410a80c0510401c90a00956941007001c48941680d46090b44d0804178114060045c1400248809403a444030749801c03840103072481c001007901c45070720750381c001c00b030040c18150340b80c1000a8107100b00094003140718080c8034001c030f40c40f04050108a0820700f682c1e184200c002e08241c10100c01c04250803254503288810303800385d4041e52081c4c2c0502c0c00c1458141c1d00300341345002d030000e00103e01d0685003c43e800c0d810043c1075030550820701d1140d80c00611b900e07000d00510046900003a160405204481c0b000240d100d08950b125245c40c012a81c0c0c41e0340300203043c0e4603c0c0001c0c0c04280c40700000340000d0b20b0015000100d20f0000c00001c0d03070346010303004660103a8503001282c0043e9551080380d00880c491104e00e6070180c0f00415650700e4501c2024003a8541c022496241029680104101c0c0c104011269044a04100d14100300301c0c80c5044c591040d501c840a45142c2c617440007000c14a0b10a510a94458111980240007801503496541c1801640040100351205950741c44001180c1941c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 852715341 1250 852714091 852714103
    0x11202061611040e06092d03040e0f1602100513210311070c032616060f1a0d030905060703020105220c03060906060905070519020309150904020705 65
    0xc0510303903800b0311103000020b102c111000c1c040004402d0780580200070440030300055401c41c0d03000c16500b088100401e070058901d00c201245103644240004a0080740b0f92140840203072280120010b110303150344441e0100c280c0c03502d4620b0a600141c1007801c3c05500d003002d40c1c00880c2c11800c00111a40c1c69201512001a0181500101c000c1c120018205520b4151b26001d090440029920f60519041203580d49160320003103844018031852506090107242c0c4404200c1c00042c00c40c4c010041d40d0340d4890020805224103908089500618000c089592601503114240d00212500d4140c00f141c0041e10410514480408044007040820340000c50702c1d8440001a05100d44250004a01828400b40c1d03010014001407207849110b0314a1040c1000c80d4200070402c04603038101c400040e00c0e280b2403e2100290004d5040761003840d041406100c41a40d020707005040e201480015200400000d0808917100d118001c062980910b050000c04075100b107800080907050401400146807807103036629076040503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 852716591 1250 852715341 852715343
    0x70f0c1a090318030d051b072705010b091806040906020c030702010e030c060406081b041404140408180105070b01080f060703110a120906050103060c1103030c030112020616 76
    0x18201255002c44a03c0d20324414049000440140c07460b000c0341e407001801c6005094103000c0801d014603161641c880144443d0014200100350041c1c80e03262103c0e83d4650000e04000780182c1072800e00000307071259110342a503008000007081c00829001c00c0b0540031171190041c001c1c56006a48448500010b40705200920786414200c02450b01c5664600000d8250441c4511240c080c1d0401c0002482c503503601c501b201c00381c4ac50340c00c10300f49603250b62a980110080c050f40c414028200060081100b43d0314001c024002c80044030b060048401084010806000070b440051514a040c400b40b4011340f02c402182d054060180350007410310304d00b0385071038904540070b074010449500604c00c0144040404d0041aa000030641000c1c03008c5800d8240041d01d078400d5010840070042c0300120581c1d58821030700302d4107010343c10240620080d41c4030309007840100f5219084101003460f40c1e01c060780251002c4182e0f4845d0b58480da005086a00c1d100b40c00303000000c800e4049901035420808801815030544540c440c1c3d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 852717841 1250 852716591 852716593
    0x60702031507090510020718020c0f0303010906091a01090504020c0309040614040b0102120405041505040905060109060807030f0b06270405010b0a0302100c0c090f0e100203070f0c1a09 81
    0x82c60301052005d200c0c0340e50341c01400c5410903e410b02c601c0e280c240b03130740b254120031020041c3c0c0c0303404030000309060561900d010a11030000000006a842154003c607041c0d80e0120010001d680003192001100b80e0400c003454040b42d20359404201a01c1c103940500b40038800441600d01e03100ca01d0340050201c5943c1c0d000004090940100d4408a0809204008810000380000c2c480d104e4000744084040c092031240340d00ca40e4868400080428104c1a400000e201c00381083c0085001031030000d84540c024083c05c0461441c043c03000402100c00107484040381e030050007500400c2016140e2010142e4018a1150031201841640006551320080075107203088a5160f010b41c1d0519140440c25102c040300c450b44950720341c20050015960302d80303414080d022181410440c10a961600d0b0018890035484500854502417410b41d20b0515900a81142d0f41c0b05001d48984001c0303001024202d001c250340040015805882070b40701103003d8100c045100c1c4c0100310841c2d440c1030043c902405c10300d0889030b040003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 852719091 1250 852717841 852717857
    0xc111519091406090a0f1712070507031d10050c03160f061505060a032c070509010905010602190c0f18140708160903020d08040f0b18060702031507 65
    0x2400070502c001c41e003140740000a845c20f60082d86801c010500c10384009003918020003845031250b882407003101c141100142c0002c0b00c40c40c2c44200035090f030f08200820307000b14401d0748441c1148051580b0f001d03014000202800c5503107401100440d03158100c0c803104007035480701300700c107403048180480c003401c0c1e052283d00c400c880e2074041e1800320b060b00c0806003031490301700c00c128040c02665640307010b80703c40700b0441c0740c001480400c210390f50240d80601d0500c8032079841c9200007040380440204501082c1c0b90180c944100c266031b146a011300b1201c0c04d00c54080182c00001d856441102170303241810f8080d0040b8072010506840311140c42a108950b803205401c0f00c00411030440d910300300e0140d032424454544050649280142000d84a103200405241c10703514000c03a0400d585020314810800703940c0190100c2041c0d500d078a00361295a220340900340c01c02144290010314a00d03c8400c65034001084404d20795140c01007024400150410042240c2c540100d00b0b0f42c281541100c0302d207501c610100d65810b60 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 852720341 1250 852719091 852719123
    0x905011e02040f080109050705011421071b1e1b060e090604020c070303032003241c08030c0d0203130c060309030905062208010506040c11151909 64
    0x80c3d42c0a40c01240d041c0d06100300701d00810700c00b00300307402111001e080814604051410107440d5102d455182e4449840e0141032442070362262504a100b00351030703100c5d4019035800e4008807140101208008052146880180d104a1602c1e6440707150644074910701c5071030743c85c058511007407811960003080029549850110891502c4200e203a08100c1c00e80701182b801b254030050945515690002405064840d102060301a0600c0d002100c5549000c1001b5203034201881e61440d501100d4030214031003201c500c3c207030707581d8034100c40740c0411207017000b41c1c60301d0661250741c440c034158100038414840700030184900320185400b40010740c0700b411103206068408180d81783c00c440070304031a088075003014548424140080c0d0407000f0300b1f091700c0b4101c5401e91038001110045070301c507206241068103401490000601040150400b50280304210f400340500400740380116010021340b818800c20740d000100d14902d03d43c40380ca00b43d8000d03840d101c1c584900c80a420300c0d241a41d0054100302e4481c0d0a0b190500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 852721591 1250 852720341 852720359
    0x206120906100b030a15050a0605041401180911120103030201050f091605010c0804030515040b0901201308011e0621031d100804020909070501120905011e0204 70
    0x203612038403076040261407a0405031083c0035404020004001d69946000042c144100d1140040050200401da91017041d06d40c04010410341141c460f07104000c081010901103903005d80c80707003501c90310140880340c01c0501c1c045140c4054495103a1181c0850010880700115a5176400381038083c5000380c001181c14104031501d080d40c080d0007003800480340c201d06000d802c40f49079807009100300c40d024030f014840d110160400030750034440c9900041542c0306e9041c0c00c0c2c1a406601301e06900c100c3c0201c4401a243e55082001c0c1d081e1022822035042a4441d131070200e0b43ca04001c070150840b07a0850f5060024aa2100f8480b821501e015146c1010881d20211042c0d20140901640700902034502e026515148241c6000c8007109900d88020140409803400c443d2105006415681c80d05000302460440c544c150030150004000341c40036030183c004440000c1c2c400600003500d4048030410b03540c415103025440e10050090051940856042d526039509910070000401c0081c01e0a8164800507a62444c0104403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 852722841 1250 852721591 852721603
    0x30f12020d17060d020a0506030a0e1e060a021602122107122d050301030309050306060904260d02030f090615010c030302040905070f110a020a120201090302061209 72
    0x2281c108192500c90701240c0075241c0c030654000310282c901c0c440c51001440007410110164000c1a04064080308000304074449402c1041515000341c140e651140c10780401c0410818107142444a6a1280020500b600c003140d004209030b402e1f00c04208180e5102c2e90010b500c0301500138007c07000d0382c06154500c01d00c0d000b4071580c030141d4051820051a04c40940c0d64440241e01c4840c000c001d001c42c596503010310081d0101480700620344101c603004204c200c10005411a0003e01040d000076540060200c0c160500007441c50181500a00c034840655540d07541200d115018852000040c034400d4404174214449009040ca6005601025850b860504a46441d81500405158080d0300260078004018040d050100c6d00d210b00307180050000545003802e07406071080d5481500e1ba01d01d40f2003007140381584040c8140b150062591008103002c0074a03101d9540d603480b401e020358885258401000420070101704100c16500c181442c40000d6640d0300000c885412942004002580c403e0400103d54030500032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 852724091 1250 852722841 852722863
    0x1b0c15040303304106090a09020d0308040b060406080c10180e24010c06020d1b0c02120d0203180d121e03180602130e0a09060518190804030f1202 64
    0x411307082e504a2006852180c100900502e0041c81c5c0000403170400c64040e0003480400c0c1e0050030f44e4112400307a00d401445068100e030700b5a000100140407818914103030103083c003226206c000905008185400f00541c00300717002540410700c031035083e02c4442285210350440042000b0342d00841c0e2807520206a6140c02502280e1440d00500c008035220640e03081803503401001d401040060319216a0b041c000000d2030f2104138040c40c60100d0401e586010303444080c0000385031095a40760325041c0d156401595810300c0302e5410002d41c01c2406401118211015907035003080006244009a901036180c50354039501c6440e0400000d200c0c2040e503a0b000c41d1200382c44031200281c0c5020002100f444103895159411100b000b021640c000072000d04140703c022504001e8902e455400029042c00458040240b2001008aa0350342c18040041c0c80d40c2c007030061842c44990303060007411890081c108444030088500740212081c4c0000d110200200f201c0840244102c2c0c401d904d00e0030704580620000c0d152a40442c0c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 852725341 1250 852724091 852724181
    0xe100e07080f0a021f0311031006110f1c121a1504060f0305060409050609061602060c0406080c0c0604030c140102070c0b0c031b0c1504030330 63
    0x201c203401a26000c40e074000413581085c5045060b001d0030400c40241060708204440703000040203024500002c000800211510750b2900b155200e011001c05442d551440043d40c0300d908014103400c0120402d1548104800e500e01d80301c3c0980c0305440155044489000c070300d04040c050b10038422001e080004c511a802401303010f9207401e280c540701008150200e4140c1d02c4080580764000702c3c4c030545942c0c0005000d42c0c1e000e020741b07503513150440a40e540e4a008848807040c841804c940b403200d031800869400c2c000c00180c0d030a94070b01030400c036041c0d0389004064030f4010010703010054625000028000940524420f6480c4908100d80e820b0020812490560082a0342d20412a4600143ca00500301301151345103c483c40c1c031800c00c120f030329041d809135580501222195400c10210034a001c16054020001120800c044100200d641441c034005da0000402040100c0b00c8405a085254800014082c400d0f041d5945c50b1080640c4c0d1054a443c0c0c4d011624109224032492030740300181480b520700f4115a5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 852726591 1250 852725341 852725353
    0x60b0f060414040209040608060a0506011d0102060c090a080a080901080106030c081902040f0303030209040c0504081f0b0a030f03320310090e030406140a0f030e100e07080f 76
    0x18151080110b1280c1259206940c0000c015020b03844030b4000d440142031850030741d509880d201c25039402922040b00c4090010340c4415900c031260208071a0500841d4060b402403945030313a151012003255101c108481c1d8420f11590300022912004c10001c0c0480e40f0032864151074405010014001c40f0043e04003c040c94100075501036015804101e96500031001c040e00500000940a40301c020320491300101c549a140240c003105041e0560024040d0303007410341c0d0420102c0342a0100311014015801034101071340080c000700010042d013408041419800c203200241c4c040c20100002e00342c6060b81c0c022104806581040800e068100106000100561000c000041c60014160035a550404002080381c00080041004070401e1641140074010000d0304006416108d42c02d142d032500144155070001b400c0350b2403401154441401d882c2d00f20655254a03003264108001540600000800050903201d200c01400240d0407500038007600c1403005000d07084440c1011180c5003001e254900403c113070b900070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 852727841 1250 852726591 852726599
    0x7030206071b0b1305010510061205040b07210c11010b010c03080105060c0f060901020702030f1b120a021914030f070905100f03030512060f0a060503070516060b0f0604 74
    0x9448050b002603031040d051916070391080440410a00c40210141c00ca42c605070401014111140549003550441d0704c40c00c2091001e101440141c41080310000c2020b80c448002c2034010b07020f658010000041500c440316062040d1440300c08a4103014030190000d40030069500d1041c6080c03040c3d445200d800c0c80d00000b240e41a8a000d418000c040c81070f54041c0000148881da240000c0c050807222421040550b1458106010054040e42003404280e22034060080ca84408020005d0b031692803c0881b0300c00307221031342c1180c1003000d0000c0451030510503000740c4140703000580d1882d000300405040c400008031590309260004025100203030b01c0300d000c0c0c0e222880360582c0581c001680750407144060001b02d46580d5001000d01d443ca05a40902100c401e00c40000c42010b0700000540049800518100702c82c3e40d5070410040b0035880038081c1c580041c16240144840f900c9034004503485030030f07400c1140c0f418441c094841e01c001e030303501d6065800580e12405a012843d0a420312041034a007141c62900f09814 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 852729091 1250 852727841 852727877
    0x130f14030a080d090227010b0a0e010e010e090a05040c050105250204060e01030609111c0b0408131701050105090f070305090c0603070e0a090c020d050d200703020607 73
    0x400080545440008a40c0c0b25400d180c84e080760300b4696010704000320400c1c3ca07038850002c404442e841c0070391080380000049008001003090340e01c15411503680b4440c040c2e1038001510040d06214a040c1041581e0b10303038032100e46955a0660054a0609001030145001c0c00d00c007c1c02c2c0e4140e049181040742c100403800c51203081560098515a00344460b0b41108880c2c40014018409a403050803841d0300700c400001800742c40d50007803084034051000c04400401c00003c100000e06c48208050b4089103001841021800140d80c1c16801b5126283d42480c1103c400081e0030399140b02c1d44450802448c00740b40140c007002c203004060040c5000d070381416041c20106030030302580100400403001c05a4550004207005020006c2c204c10f03e0780905881c0e52401c208030008e0515215250040c02103a8aa000240c00c881c0c07841052205181940a42500340618008507117980c010340360f21030083e450f0400d2070b402840054050030030003040d5420564510403850080c2c28420000c010406001d9880c8e5000c4940034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 852730341 1250 852729091 852729103
    0xf04051003020415080a03120605150403060903090f09061d04170a03061503020c0f0601030206030a1802060d020901021209030706051b0d02070602122814130f1403 72
    0xe41210007184524698514420041855010b4200e0348180100c0c4001d054108c0c01c40391b940c1900620500410786c640e400c0c0a45021104d803500c00418041008001003451648050321440c402c0c6059111a55a103482c50b0b0340d020780d03820021034140c0e900c90130010b461200100c0306650140d125070301c5140c5080d4944d00083d240181d131000c000c0b1000103801001500c04d922140241c880d40d2130004200c030405078000c0081d040a000ca00b01071048160446507594002500c50403660300500c128a143e0755640e9100160111080310002905000f10354070051351208098261849034200c0180c6409010000a140099a108131104903200304600c400d56140820350101391919814607513664550304031503010410001c06108168050301d8040c68030b8990104070541191165421118003103419800034401f441440c1c0c01c0c041090480449004040441328001400b191a04100c40040c0760720034030556982c001307420440d03a01c20416051010350740e41603801001e482031105a8107281c4101c4007082e03440f5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 852731591 1250 852730341 852730343
    0xf0510062a030311041a03040b0702060f0412030b06040b07110901240c080c010b01122a020a05070803040905070f052205040204080a14031e03090a0816020f04051003 73
    0x180c81d010310482c1c44e2103000c101c8004281da241c240c03200b05c02100c00f41c411600151021182c20700f0307a82c04111010300c00180c450181d0800d03903003124503451301c1c0e9074020400001c8a84009140e11075090792030a9481c0d402500080c91880f4215503a1081da181020888845008d2a88902e02d008014801020600080d000c56504030503400c03032052029800341c402c55008680104150780000e0340c1c07407984406400c1414140d80c281c89200c500902c0c007641500344ca0030488100d00e0300100001040be01140c1c00040030040c000b43c01641d007a1400d9894450501c00c09411002c6c86500000f800c000e2000c6510845900c520b00740f8101c41c0c00c032200f2000605901c226002074101c003890b07400b254564140707642d25000800b00100110b6072143d40708121501c454400b01c044d1400102d01000c0f000c2ca400100803180c0c07050540307428500e094080440307400c66030400f80100900f8814221010000780101d8002c108920402c0710742118400300c3c0c41085030300c400c000b5030707240500e0034001400801d600c0b64820809403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 852732841 1250 852731591 852731597
    0x903060901060b1b070e04150b10230d11040f05031f0b040f020a0207030204050c03061f03090210090e0603070833073209010f02010f0510062a03 64
    0x401c03104601480c5c819644c0050952100f030100340410000c0340400002c1c1614880310501041d00c41c54200300580c2e000031803d102284ae00162441c00c25101840e0a80d05403807903d03d54280205041400d00321040e0403004c03801c2e40c20004040c08000b82d5114504003d000481c02001c1d00300b580315111113041000003c54814903106c0b95460002d03a03860b042100b07030f803061078801c40d00c5851200000f942e070056844182c0c00b652814010414003403500f401c891080780080c0001190b4075890040008106000c2029402c040d034074851a8010380d80e824000300c001d502680c91410503805d017840319100007000303029140b00b40d1100ca0100881da2004c40c00244000c4a101401e684200000c10b00d02c0b400060424404083c03441404c11800e5500f00001e800c88164074028080c0004440c10340000708090705c489c610041c6d07818020045d2a620498110004c1d00b058400071801c601c0c581c44000555609030788e00d04a1140c1074409110807640036100300158007550030125245540400d007085120741c1e4281c05010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 852734091 1250 852732841 852732877
    0x501120203060d050a230f07031b03060f09020a0b0a1205060616150e030412020d140109050604170901080f040317011401022b1805030f030903060901060b 68
    0x15903100314408101c0ca4100b41691411020383c0307403200011801c0d1141c0c015101c0c07828005002c21600081f1800207480e0300004200c2c26055403a013803c0440c2c204c178401012a0407070400300000d46980907804d203060b40c1140116400220b0b00c1004400041600b1504000c3c2c0240050000785a002181008112940d000090b42e0385070b140c00b0070105c0c4075000413844d01200043e601c00030002e4030100301c0f504000d005420000c40c0da1a041140d1284118407a8605440c0600d010102600d07180d01d042c09814880c00d1011b84008030403620030b003560078200065945800140422003442481010412034564260b8a035140025110001c0d050303030b4001d0071787c80b02e104035600014105070190020584903100801c0302c407215a524510a030b5a0065180359900602440d0313078810740c909046295600941c901c03400602c407106c4c8440301711580d00e0b008014218504242200003140c1d1402d00c01000c0150302c039405150754542c10700078140380040c040c0c43c451441e8540301c01040b1003002a400c1d180312202e0641c0d1000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 852735341 1250 852734091 852734101
    0x10210020a0e55150e01020313090506101e0503130b240a031101050304050a0c0909022706010804030c061503060c0305010f0611070f1710060501120203 67
    0x214030b9200010310150049184025141041c0500400c480342c407500040700d00035540d01070401180070765880f8040e544454140c003500180d01410303030107040e1703076040c411641020044240c1102c0010035500c02c4080d41d40d03a00501009040001ca540c07552880350800b4001d14982c031500314001c4650740c1160301089400b0022801055060f013041d000c03e9006030590340c1500307000c480e804261207900040c0461880c00301d2400c1f95400d210a080c0f0882c1e4120310341000841082c030042d0b4842e80010000c03500382c090f2100e40c000141c1e075000c401002e02070a8800003000345841c810700905a01e80200004000c1c5150614009681803000c0154805400c0c0b07130040c0c403070716180b0b8203a035543c1403000020551400d1904048402103140313200402c482c0107070014081048841c0080c0c040720b000b0300507102ca13603c208100380a0f86006951040c10440c0c14821281c031141d480d40e051601041743c5d04940150841e000d0028494641040000c08442e0700e01c004222030740c907040001c1d04a03142060f41d6200240c0200c0022 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 852736591 1250 852735341 852735379
    0x10b01081b0f0d060824090d030b12160f0f0302030a170c030c011e0504030c03081008030f070309080712020f0f1f09080f06041403090d060b010210020a0e 68
    0x1405000341120144241074560013160740710301d40e01445010486c50300b6603500b0b03000f00d0590024041c8020402800096001d0007007240034002d0b1000702e540107031454107200207010b01044040d600d060142a58100141020038181031101e82e030f4000c46c1101840b040a1025030303004280d032100954005515054544854122900340c001c4a4070000315020100715500306800c10740020109100c00328042e000c0045400140741220000d0f14040e001692840201001a0040c84042e811450040c5560314066403510340030301e150700510307151404650208505080503004010b10014140305000b402c0d82030b0030450084005428418041d1064550141c0d40003191501c4c25880c0c0340703410240c0580440d000c00c02612210707140c1c11381c0a200160390b00300b001541c00c0000c00e04030f0115245001408854982d902c03982c03c0407101c028450503a020030008480907584d5150044029445010045030f410725140001e030925040f0000011301034010400000303403d5028022044805003181d401d841c0c1206413980e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 852737841 1250 852736591 852736597
    0xc0105040f300f0312020c0303040b0603100e150f011802070201030b0a091e110406080a0b18010f0b16081605030f1213020f060d2705010b01081b0f 65
    0xc00c0c40c8401401202d002c2c0b216a00c2400005070080d11090080c0c4450484075080344a038050742a207540061000c240016a40d010090b08410020100c4164141e03442d4104115038000103244195481105100c82c1d490302d00c101e4503400242c00802d1102985007488024280c0110041d4000d11580020b422007160f0090740320b60030701f04001c0c001c09605610740c180c40e4010106852a1546d03881104100e5018880c2030051030380c1d204e02d1206090170f2038a0100241d0b24400040c013202c11680c2c80d460601400e8a8080b01e4085041c40c1d10511035555140108000c01c10f051900300f01c50342c40b0100920050703040303585100b83c442644603010b1a51051503103c6e14000c500c20140c02040b0380000a44188a40e2504c0c01404030700003060b1402d012600d60b01e903450782c480c840c07100080d005000031011300820718040c13000c0c1c0704900ca414004911607030307030344c200700030410102d0841008030300052401d405001e000d05c25443e00840a08201840f810010748010425040390a940d0109000062040161100c0002c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 852739091 1250 852737841 852737909
    0x20d0807020f0a0b010905090a20270f1003030c111201050702060a0605030304140607140307050312131731050301110a090b070309080f0705030c0105040f 68
    0x50f03c00c0c62581d4038040b04900000c4c459250480d0501020420300000420581d02c0340b54040b9140d6025130340c2c1e04d00c0840c00c203140000396600803501001151594a400761a17900b5074611840f000c9a8030300342d000b540b0200c0010384002e031180d03080b6a0030300002e60400344c0100c0042d0000781c40b11140c41200f00050a00e0f010030b98040d055424001400041c60f0002280c1c0e0040c0c5032000144400d5441d1002d040c0d89000314170401d0030005d011002c2811500b0040020a0498043c481d031340085685045528507591103004211016403001640c804043c041d80c20b03503608055180d05290f82c00d0318503110038040c0321090b91404042d000004040d03417120001400014a40e04032610310800841400c6008154135452055034001e500b05150b6074251800300d811100300440030780303410405a092a02d158810381210804900b0b01070030000c04102d6074000c200c9102c400000c00000c1261500f8242414100040b400c2914140a028001032004900025030300341034482000e14803500007400a00200c12403d5044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 852740341 1250 852739091 852739093
    0x20702060a0201060f23040e0a050d05030406110c0d0f030209030f0312010f0b04060c080f040e16140d0f06031202070303080108060c0412020f040e0309030c040507020d0807020f 78
    0x708a0042038064000340101c4805c600b10b80700d4690303544100c121243c4e034071800003078030384a200fa0300c6440d141c50ba01454003c5c030403a00f20307000031342d2a07503c0b5840e01202c03260340004948040100000c1140c0e81c02840304007840e241286003800d8401124903030300c12081c101c2d841400710000004e4442d40c426030654a420030006c0489010000d4034070700a450380d02200341000340842c024004206640c039200c400c411180366181321032070203203032010840e200c000c10541201c000c076040003140d09202020000d800980000381d40114142400c000000d41e8244003481d01c820b00051381c804908401c046404c2e50461054103601180680d0703131604a100400750b0b0f030801032403c251070304041c0149a0002d0503100b902d02c02d842e202e51b2642c89200032a940c1c601110500a2160300b003000f841058201046200c0041c80544195108030030360380010141c0300c004070b0001103540003241c42c1e92540b5042085042c100b0068600b044581409100252a403640542007001c0c00007040120b84078070b100701b020609190501c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 852741591 1250 852740341 852740347
    0x4020d060f0204051804330c030b0f0f011d06070605040803090609060f13151a0a120b01090b13050f070f020c1f09050a0308070309060c0b010b030a02070206 69
    0x78a1850003904207000e414050328003400d10014a210150105004680140c0d070f40880800004542868068012954065a4401c45142900000c501890800207250784010484030910703810700020340510f02589102e10040904403449980144040301c1c00300c3c05401c02103040c6241c0c008900c45100745040140010303d0001000107000e4030002450185030b0302400e40300240c80d59640c480d030722081920b0403000708541c1c1c00450a00100603000d90f07109841403123041c1c1507401e403440700d6044494504848003007001480b00c0101c0c61030070000500c0034040184104040030040d49943d40d141030140604049035944601c6080c40d81d070b40100c0d500a400030840309000c1842d20740c5010504070400e8450001280c0341c030005080311800800d021040c8007000c3d005409420002054007645201c4800368801d0085841c00420035413581100003025502030b00310269039101d1803400a09541003030b031142e0100000d8444100008c0c400484081c112120a001f0f00d07201d0b00c804205034024801e203030009510030000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 852742841 1250 852741591 852741611
    0x919050106060806030601060906030207062403060f29360f070f030b040e030c07030c06020a260f0d0b0108010506091c050f0a150e070b0f0304020d06 66
    0x5400880c1910b00c00e685005041d00c640f0141640e4103000e000702d0011844098040c080b2174804e0f400382c00e42c1030250502091640c61455500314504198140c03820140541e40b0a2081c400780b40100c0d18640c2c0b840c2d8040010009041c3c0399502c8a003031a10901458142d14406403031550b4508107900702401000c400d04030041e500fc00780320101400c4024040c83c0d42c144001820806d000c1012601c544400e0b100c2c03500c101e0348004100c0092409440f40780c1d0003a0b44100e00c0c80403680802c06030011000f008000c0c106281181030441000034a079128008540c00350b02a030000400c20502c20320043c2d4080007481845034404459031a500a1580700714581e8000700d041115500c1c250080e001a20081e03c0c2c1d820740e0390300c580074400d551062005103500003c0346115902c05103440300620780c40602070800e5811022112071034500f800754009040d0b40c0d0000c9001212071800e22442840081c0118500030440e0340d00c1c0090010700e900420920490406020000406640721000909446948204108010390b03003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 852744091 1250 852742841 852742843
    0x9030b180601081b190e04140d270308090105030a06081c080906040201081602030d02070501021201060f1e050c0706031e0902060d0b0d06090c360203091905 69
    0xc8850606100c9401200740c42d040e05041d45c054010441526503c00018204980f040403014040c1088034620743d11605195101030070311a8520141b59696201815040458070b680e000c2d500c01d0405014035010360040001601d010f084038201c900a00f03215840e07a03100074400d40200307460781c0b2589540c0208200305204082410349103035a50001d0312000260780380c452a0303541d140c00c01ca4000303010580500120300050f40300030380c2580070040792040300e282c40e000c210160140d80120000700c50390ba40214a141c00201555225805000e0601c1c02c42196421135000038100c0b0052440120010400310070603c441d8414000c0b90800358054046491712641c561000b0020b000c00300c031560480c591004240103100b4503000d03c004441d0002d00c09030410200412601c0104444420a42d000c440540340c0b07030004409001d04c00c000c070701039040142c52500e086034800810313136a00d10000e10f94850020449021001441850440c1409240180c03241d070b54031200c51816050108907081000068507031420000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 852745341 1250 852744091 852744103
    0xe070f06080f0a020c1b060904112a06040b044d0604170106120503030402010e01210e07081b030d051e090402090603041a1609030b18060108 62
    0x1844154801d960f944142c4000202d004140340d443c915008030441e420910002c0b24410007903c2e0040105280c06484d10006040303c00480c011203c000000c40c00034051442c0a88203101d1030b01e4000303441084907110b01101d0f201c1c107006100816070112007000c5411302c1805c00700d0f038072420141c114044d03d000728180790700354200e2080340c03c401003d42c40c88110101a03448600003250900a00440d041ca41004006c820303c24548105111565841c00c00103107800022191144190042c1c01651741c134109030000403d01400722003640d0500c403ca60b2562050410021200da26410601001030030f82031a40e410703802c2c08070a42c040300c0c243c4a90181d0540c2001680c5020b800500101c0403140f6100d04120180c2c1c2c54000c0c0c4031040d03101900003130f40d0b400809454000701280c080c01400146002c40540000e0800e4200f0341c0e042c2d4840b01c1c04200d08410b0001034400d6504115081c000e03445c052096000100540c8103030000910480c400c602082950605410406c4d90135240c00994400e503031555001640e0346 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 852746591 1250 852745341 852745351
    0x80715020d0f1a040504050f010c0c03091a031302150a0f0207080a0c0308130306061401120e071a0f030403030902090f010806150102100606120b0613090e070f0608 72
    0x2c0c540001a40000518481c62001d07400d200010f00c0008000000c00008280080c02070340c5600956005400740c810a105031150391103951518180003109081c01044401e1540000b50f032030012040319080d481c80c400690741c3c403021490304803495103c2031020170160035580500d400325007400f184100c04180c0141427141105129403c5943c042e5549464564582d04640c3c0901010042c500c20b00c049050300d001001901000b010303c000640d500d903242ca01b291907030760106904000705840e060700b644c3c1c04443d0880d2030400e607900740605c020400d906500ca000d24421801c00205203101820b0b06c051941c09c0e2601c400c01188051340300d28040c100036000c0d1481c11412803281c030840e0002208403441000e401d041e200ca135401043d4a541c0c2e00031000d018011081114158460025200130340c40c82801024040c2020350b5a00c04151085000c940c1945d6045005030b00c2203000b4800d9a1074142c041405c907003110004040800c0451a200001d402c00c60030b50485507044034400000329590350012400e038010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 852747841 1250 852746591 852746617
    0x30c0b1911030103020d110a0e09011e09021f0c170403061d06130f02121605030109030c1101090b0d0b1c0b0403111c03051f03050a0f08071502 63
    0x18402402001c003803031009002c025031003011001003a020910341410416401c4000e05500f40c001d4841c03071220aa0303030080710fa20380a0b85d11a84841000110032603004a00e449020741444003100d998002200400c00e0042600c0b41100481d150902c1d40c4034145482c1841d0308410861a041c181540c045a640e00501043c4d414504020010100c0d240c0c80562000c500c0244016103503603124a004180d01030006001603c814240c0300141b405642ca251040044a040800414111682c0b1106030060035072070740624420f902d045c20314400729800c500d0440903503501103001041001c0c02070045e20f00302590741046c03403c40030101e0003182500080c1c0c090543d41d4002c90781f01001c488030004181d40700c01030400041c000c01d42d00c2c004c00c2c0040e006100440e02d0389111010764240c441c1002442005100000380300d80040d4030b40084c002a02d48046c1c9400241407445c10070b00d030031410b41e25103907540c090740c000041c20614503500800c144007101d8113486d040b40d4003da1140000e10303080d4241c4042d403c203c01240369 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 852749091 1250 852747841 852747851
    0xc0102070516030f0807111e1f171008010c05031f03121d1e0108010803040f05011b05010f090b0a09200105070c0e0417040803090d030c0b19 62
    0x98480c0e0b40341c68044907800041d0f00082085542c481695400032182110000c0203602080c1030795440c071201280408003036101040810b410070412003050000e0740c0072600c516880121200b0907030b004114140e103142240041ca510748440c43d1001c2c0c1205e00c1d134480c017025464514030749001d681c00b0b0002e43c000c0c0840805000f00585180304409008603d20000b810383d0043d4188495090103181d414006c10002c814101c03c0032009c0002c82d002e01c4120466683d5181821110311a81d86c100e41d42c41d0140600f0801507041a00b00b0300e00700b0700c0301010301400f8107114000d00c00302d00351091040c80d40c1030a9030040091000f0a12011100c0141c002c0e1501180d480306108000385400c2c100344a5540d80c503810000c00003c4e42c01c1400105184030071654102d04018042080d0300100b03056800550092012030803640582c6401d0410703110001c800c00344ca183c00541040104510100001524510281151007421000c024036082d2490341c0c0d0102c0003000403000e04108021100d8440d0280c410401511040c41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 852750341 1250 852749091 852749113
    0x201050f0a05090c0f06071a0603100b090423030d0c080a0c02060a11210403081e04080f07060c0c05010e03131202040b1e0109240f0e060c01020705 65
    0x300340c9800302d43d404002d03484448002c07880d141040040715000d00180601e440c164541d1140440c8400390300d104c1a00a09100c00d101c51414100101080034001d8901045220412000141140400f8001800541d11380b000e405031444c03a00c4042210311000710480707665944901c1e080c40541100c200314804940000002842c901c1075010b100c0d1015600c0e4040c010b155a4000c544002700305034125240f0702e1030144030600e208074410b5200c10314198145040041c0b0b250038035005007403c0d0002c0c046060000d130000308051815118180642255000c0d206a482d4210440c0035034140c012500058440c41c182224203140ca50030442011099010703030002d001300c088007103016589102d5100da180d0a10000700c02004082898603040c1500d80c4004c002082d8208420005444141501c0720a0419001d03868819015070b0005c820b0f0005280b1016a0591481c0c408031150550340349180800511141c60051038005120b0105194020801000182c8a200d0110640e00030341049030116102d1041038031040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 852751591 1250 852750341 852750361
    0x121e0a02090f0108060403300b041113030305070302010f063c05041d030a120f091a040c03020301110c010608030909071202070501090605060f100e01111203070201050f 74
    0x90f040c2d4902d50300801aa031600c0d84e088990041c030760762003000d28030781c060203c0462034075403101c01d80107010420100b203034502503007000112010a00c142065490800540000302c0801d96403c080307941504007141c84800030f00b8240d01500d80150003a546a103081404140c500c403c4141e00c119001d200c07809540d5802c0039110088a0304020420b402c1c9002c10340d01044a8070386a00411680a00000c0c0d80901c070400003005842c0d50002c1740740601042c2040c200c40d8004481d0b118240d04200c0346102070140030340355100c0d0001040750882c044245102d910025040c80341c0404c3c0b40d001554054003c200700c51008002c00e9164015400003a141d500703002d800210313080300206640d04014010310b082d1885e12400800d40f2803507128409a2034a640034070580020400030311a4200d03150090401040fa450f10710204148101440e407134a1103641460784507040b0550000c0507506520007821b050350401d100012444ca041c0c02010440100366001007005402c3c0d6064111074000c0c0c10040207500c480c2c6907d8824 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 852752841 1250 852751591 852751621
    0x610120c12120e300c090412270e07030b0a08010c0e01050c060c070f14010219020f10230405030d0605010903050c0918030d0b03060a1a121e0a0209 65
    0x85158180d0403158045080d440c0c00c0b43d10360084c243e004a8407210b080d48041201c41d0001c031004c1e51004040000395040b036030003441d4040e41c3c802a450011010422130001c08106015020300c0d030744040700c4800180c000b40070794406031060a00600390604582e603040e080e8040e1040c00c52400c0080c00305030303c0e04204d501401c10340c3d951034544805401182c0e180d00341c10429820100003a129080c0e680101000f2500c010245040080c0c0c030030001d03a42c1d9000c003032600842c5104803120011035101c414100303580c44000c103c22489001e81540801c1401442c10400d102c0c0700e54014218040965100f480100000040184041901c1080a2010907915001075642c00c9513880003a000e034002c0694031302c2c1d5103000348140e0b610504c6800054248000640c0c91451070300f01d0b9441e55002d5581e040145c0c418030b020031049600c202d244005005040050283c140d0900c0d030300920704d01440d100b07101c0c8081c07108107001d45080c2c82004c0648442d13050a441a1035610391345c1d024164041c01c0b080c000b068108036240b0341 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 852754091 1250 852752841 852752869
    0x30e04330f14040e120a020708120705060a0507090518061302030c070803060a170a020103150f090f020405180118050606030c0703090513060807080610120c12120e 72
    0xa00011042c0090102a00d144c800310806401000f201011420414002d8601035070076a0040000500b0102040e1821403032918998610206004401c001280000c00c682e01c0791180801142e26141c0d16000d40341c10071203800090344100c8103000645d00700510000320344140d00c201c030364003010003100c01840d08030701c41a901010f04c0c6a003000044041043c0320002c40d04488041c02c0358906554840640c000000b8140c511202234003d40340c000c0656a0502400c0c600d5200002c0000702d01e40f40c50039010001407203102d2241d9242c0c0f22180c08000c0d8000354190b138000c140181a880c440042500860340d100c03000d004901c0035580c0319511101900340f42c40340c50f1056002805440c5140c954101c6550039402c034080480070401100d038003189a44541c030201d01e8140b225000411500c1c14204003d0401d1516000703c14541d01182c01c1001d84a83d80740004101c03400e4091f0308a8440306402d01d5000f001ca141c0004080c01070b03010a04007040091112007004541c00d9490400300c032060340800c02d40c4005022 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 852755341 1250 852754091 852754109
    0x31507020c090a150302091b040f05030d0e010906201c0f1106060f040e010e0d0f020a0506010902030403170c040906061706061308010e0a0c06110604030e04330f 71
    0x4d4140014100071525542090440d80e55016401c80361505500300d5005800541c1c0001c82d20100b0455401c003000a060050b00c9c03401c0038002744100800003410880315104035010426840c451200c3d078844503000058915400e01503032a264030b840c0b06000895403488488001969180421007050701c945003500b0503440f20405444540c65000c01c00c02480342030741c41550300542d00c95040c0030f60308091003031400120b03030b52000d02041c1d100060040c21030900a05c102c400d5411102d030300c000255010603007a040d40d014440040e10303a151420120341c0150784a00840ca40c403100010700c940168440c010b0400c42c0c0d07070b01606101a94882100320790b0300c0c440442c00b02c1d081c028080400e202d480c0841c090728003c102a8805400720f503952030710b642581c200d110342c0240d940010b8544802e002880341000e0240c8045d084c141135143c070365034a855031144000c1c40a82004040803c52160350b5441e0045001442c8482c140140148000b182064102d103121000e030f0a8003400c280001c094403600650030494518803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 852756591 1250 852755341 852755381
    0xb0901081b0d06020f030702160f03021305180718060b0424110a0317092b0e0a03050d030e070b0904050901020904060b030403030612120e031507020c090a 68
    0x100620098403200b8000710b6402e502030091250500e68580503520a0003650f0003440c00c104c2c1c403503c41c01c0d030103110b412006044050103000e0015171644130301c9940303261b18400005410350740d612000e8070a006880c80303c0014004e00600080540d945c3d48058107910495504000d01541e401c49100039126520130a07100606048070b1301d8500c030754040907444582e21410101e82040303800030f2542c00c010740070400b200414104a00c0402038100c01c02c2499005901c4002045684010f1445036191012450400c3c0c01802c11025809802c2c820105548050700103440b052010b42c4925044e6150920001d035800040d18064007030b4050301d00018400300300ca844500651401c98030009020240000038003c49240d9000c12400740d00d511588520360080168407070350b07501c80c10149002002c0d1061548607074040550b000c0305101051184800f05402003150420500341d500880100b030600c0c6c1d001d140444442c920004208080380c011503d450501d0003107a0b00c002958641c24001c040700c0004d02d030742c40011011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 852757841 1250 852756591 852756643
    0x90602011a011d01090f0b0d1d0304260717060615090d0c150c0c08060f06130b03161a0c0d05090d0f0f03120209090c03060d0507090b090108 62
    0x3151800c212000624011203200c2c1c80304010000c13403150387d1200d50f40300c1780007441c2d54503400e49206a84414524000c00c0c202c0c0500e220000d6524083c0f8003c046450024407030600f0700240c0c19414080800200c000e032010607980c1c1c410b4000c1e80300d030810b4654030380c081c1c1c0c00028614640001d142504c0319035100d000f41040840002c0c0065518103001c02c07200305104001c0803034900b9800150040d21846550391585166107850003084d86241544002059807100d01071049521190510503403103503003600c07442c44860740a1825005084030512091f01401003a4111002c4d58034801003e0507205403401144101c0d07540c6040e80f500341300315001003100d900440f1038001000d100380c004020140c0003e2038502c6905483d2100280003000c00e00c201c0d201c00075146010704054010301c01e0b8a80c40c4800801b1421300c040c190115a03400c00040441e82810000400210280d660040e40d081751a0480d0444507490340f9440100014450842c1413481800348600004000030009410024004d005070b5100c861f03c2c807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 852759091 1250 852757841 852757877
    0x1b0504022704090b0906010501020d0f09060507030e041d0d0903170a02010b030607050a18080a030e0301060b0f0903120a230417061503030906090d080f0703090602011a01 75
    0x115840c641e401511046543c1c00300d0540e4003014010081103010301500d500d40400a0301c2c000040c0c0d5810148444c00c0d44084c0c005410070704000486545041590f9036151030301d01115051229402107600c0340c544400303980111180700d1554440b100394412624582d0f101d80d810307203581445201c02480d41a1540c04800a03000d0364001e48440310b800d00001c03846501100010342130a0049400d2000128081a42403140e6440101070140500440c0c402d0149824910600d445880108015050188102a500303498509500040041c120038000e9621010303034400418095000c50031040c481e00c81d041c1113031f14004140b012141404180e0716903417101605602c40800c1003000e50603c41240009120014050002c0715203040c19070500c1005d84540c1c41c0c03621044010400c150b840310300941c800d004c5001c0d1a1a400200c4908038803c48840300000b215161500d003034820001d0300d01c080b078800300e500800c140d0841c6405065070380d660003d04c1400c10355206181c0c84e440840e40240000c18840862401e041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 852760341 1250 852759091 852759157
    0x9030403080d020702090c0a03064a07030b040506030607091802070b0a0b180609070e040e07080a0b0a05090d0503150a080f0f060903030c091c1b050402 67
    0x442c00700150504e02e158000840c859000c6074060a00480003d1254503e54548101f00103085a480c2e2000e42e03a0307064822051a84c503014105100e6040100b000311580d2038030401d030b0794041b2070205020384c074504800c009010381001c8004500944c201004991103140c041125031081c40555120f0051514109100301310043d582041100c9030741c2005280041024000c0091280c5890900410801c031203001340314071050261a01c10145003100240441542c0d4134200f681c0003045454007840c1480b06d800000c0081a95001d4a0114851450000b41c0c202d4007048440c011130003441004141e984075104e0318180d131012240c4108941101e0181820380d4003a001035604280d40008031078808043d41d010a030b910301c6580000400d83d102d9001c07541e1014003000002e0340f041000018220505001481d00c2d600e0202030032000d1440c4c80030514549a0715420a900c0d80c4c004074044258503901035040c980300f032103401590703d4517140f210b00c0042514240380c02213418140d0380861503108010f0141c0e031104401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 852761591 1250 852760341 852760357
    0x30c03030a0c0908060c042301140d06170703060e120a03020703030f05190507020a1a1518060406060905090a0c09330e090106050717040806041101080903040308 71
    0xc02e080e540030410300760400c400c601c50f503010304500340c0e102c0c248000c4849044203000c0b03085800742441c403400c11590348004103102d0241482e803112f0321140e000000d08080d111580191940001c0c0009607010500000b0310207007201d0240c80100f00307088020203400d440301c001c48102c1d8103500f0100314425145211740d00900c07031640645400500340b08640541c9007924001d5400c81002c110340301c0844465401c0c0e209694020100b80020422a40c0c0c0d5950002e44807200001d4107804480b003800074501d000011120450f015000300900b4929a1400c07000301403035419104940610700e800404100140915400c40507650001c02c951400d0f52075090080c06011940c0c217500800c481010000740c1c40b0700602c404c54103403410000250083c44894410503501d45074017072030420403250305d1680c0d419481c0d0390000c6064660a02d4a6a0786000500f0300306610910603408200311280003c002030b01e0380340800c0c0140142d109030404034001503000c00441d0181c1c0c065030485901d030401c0004100048000380204485 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 852762841 1250 852761591 852761597
    0x90f010c03090210181e270e0d21180b1509100306050a090602180306061f0807050c07030b160305040803150a050a140a080604030e04050c07201002030c03030a0c 71
    0x45c3c0e403902410f81400940015100d4410002000d07c110600345020b24251821410000d22000d40002d0b4028241000c15603005a5509004082010b4116030317080300340c00d00824440500c2c0c21a0302e2503c000d5464003203404022500159031501031901d401030f144e5000ea4007040b0820030160550701c4610090001a10303103401143d49144400005001d80054201c9601041c00b030080c025941c414103060078401040103101d500740b00354000c40000494100b58142400e407810003074a50359820256034034461140002c3c848c0c0719100d400420440b04425480c031900300c6003081340c50040c0b4120141c0a95909443c014807204041c80041d25060806d0009021a8801001640c0082d1b581000c00d0f25002d094001c48104c1c0940e2401041d1400c060004100508403c00180550714050720b0003004051580c149510503516040854038030030441e002c1e070700419007280002280b11010b428002d2403035100320105008952400c5d00101031400841595401c03c2114003451a540d00c1d0030401004096603040d039014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 852764091 1250 852762841 852762899
    0x50a081c0e030a0b0106030f0c030915111201030f060c030203060d03210501090204050102010b011d060315060d050a0506030106030c0e060103020c030d06050a0b0403031205090f010c0309021018 85
    0x8a450906030302e00070b240b547c40000d905410081014291203079861094241420107a001c0e002071100c1d52101004400c200d4001400c128404a5801c00c2c03041c0307100b00d0450803801c0c0003c414000700f00410050544140b00030008441c3d07000d42078089c0c4c00200d800c29400180000f034080864041c148442003041c4a003640302c024034071048810200e0b8002e8000e80410340d804070303060103156024842c80704410300c00d08020301140f602040741e1b0200c640c1300200c140100e02c041301040403045039200a0342c0351640144815110101c030b03a540300042504031940c030709450414000c10403d06041c41413200383c03604600d07080700113400d100c03210f04210005040b0504040d804c1200301c001e0402400984004640c00e203010503003038580b008000781580207401140d185101000100002504200c0403680150368040105443c0d80e10312013a403c00340c034115846469420301c041d510406a066100c80c42d400d2080742c0c6558240c1c4462021030781080d005405022505c0183c0c41881800e030484a0316540344407158101003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 852765341 1250 852764091 852764093
    0x19081603030204082517071818050a0b0106050c0a031d120d090b0f030610020a050d030c1206030c03200d080910031109130b0a03030504050a081c0e030a 67
    0xc82c11801c404140100341d160030104007001704100901004001218a50013142c0c1e0001e00d1076100c03005072080e450fa003803030300300000b10761280c0382c00c21400451600b04681c0a1102c0b42042c0d61500311245045034040034000004c9452805541514405064400200303021280c0c0d6a0560390b001d05180c070580c0103103580d0107002080c0c0e583d450320039050380010090300f8040c2d4050310203004c2d10403941014040000a0180500710038581c0280d951101044803a0500c01c164040240e0405168041c0a8664014922105040f0340c03d50000298200c0c0d5550310020701d41c601e0601021110396010013803c8561112081020826100f144e44541c042e41d80d4042c40c5803d580300150401485010031215580301046036841071800e2031032511800b016080c2884803841c4082440014866030100a1103681138541140d105c495603400240000000b52070b845e8400c0d102d0402030940d80252003400d02c41c420140700820f50403801320f9024000740c40d03010381075403248040030140d44000701c03024002d03014030800000074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 852766591 1250 852765341 852765343
    0x130314130302121c110a06090f0210030c02100902130b1206071706010e09180304031524030c0e1302130518010905070b0c070503030d0209031908160303020408 70
    0x1407000c03100c8009040010381415040101000301a008080c0a6684045410b605c0c0100c2c1e150f4a1540c46240000c030941a0324241d2040010550003a4210030f0950718a4803244c0c255120700c01400464003122405c441082e40301082d19030050009400105540810452400d04d0700b01441a0100402e0b880d022440311080c2491301d40100c618034002031030340b5a81c0040c10fa9030010107030414000e00c0c00c41001c1220b040490340d40080508010328503c80c8c4d13000c114401da818410f4901865004040b64040b103007944080e0044c0c4504400000d090035410a00e410b60000d40104100b206e62107030321200c3c568070702a417400101c1002009850003800d854191740059850712100307503a85030b1000e400940380c2080140a000c0c59101040c15449a1401d420f030804640000f40303920407120402030070b82d6284000b1050700d080c120598851070b0180302c0450361510202c1150040c2801032411f900302c034007d5410380009020341081060181c140748040200300c41e6861a070721491031160083c02d015180c15a511006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 852767841 1250 852766591 852766609
    0x50d15150b0d1b110d0c140706030e0d08070f050a03140a050406060b040f030f080417031b37020310141509071b0203070f0608130314130302 62
    0x9004100d95454581c200520704582c4091640443d01c0c1c1314090780d500d20240c964950031341d0742c1c0409028610203000104020000781c1e000c1821f1003415a159140c0d215009000790250711815035450199003000361049105150441c4a001e01c6e0f5950300c4400341e0040b06a07005d0b0321032013409080680700d61107032003850a5402100c0c05101301031000034007481c00341419402c484482c1c20094070020200700810a43d10204c10a0040d00d4001c101840d4510151070f040c6024402c80d031010301004504118180c1c60000800540b5041007542e5404454204d40b04039943c440801407580ca10703800203800c911080201d07070b950324420a02c81d0781018201c20800e4000a1510001ca1a00e00004ea1035a00105c54860714141180e00810580c2c030302c00001000d040064035041d00244250200507481101c00c4025884410640314190080c040e40c24154031130703050034010f0f20540180804540e030103010585407480381c80c0c141c0703440d03425580d042103010b0302c12110441ca5012081403031491181c500040b000da03484010b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 852769091 1250 852767841 852767857
    0x1e03070611060709052202070507081e030a02070b0a030e010501080313061d061608040b032d07201204080115060503280218010801050d15150b 63
    0x110341408280c40d51461030034000038103503c00c0000000f401c002c02c2d110402103c2e0204140c208028443c074410741c0b01c0000b405400f8000d0701602c164000080c0000001c10300010940701c180e10510b2005082c1041e40da6403050304004c90069000510800c480d40a02c0090000c0c07445506e0080b8090032406d40003420350300281c01c041300d69003001640d103402804001c0c0f160000d01d21070030402c41400b00f07809200010780141c20000e020f01c500150703040500d40c4002c1100c0026600101e03081e115038450550007480e03002154006051160000507224125a441c418417152110540c07e0b101035031075604c1103481040720f000c84440410b0f04c2a0240a5000610a0107901d1003510140ca841e81d1038400c5507030954500c80c20307aa240c2c60802c941845442da110007101e51000207800c50401e80070640e03034401000c100c3c004048684c1c520125014456002c1103541019080c000d9807401c815903201d100300300c20040f2216000f0181101c04082c05a001d240d50070a1a94290746415105034039581c0116440c0395000f41e103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 852770341 1250 852769091 852769097
    0x70c06091b06030c05090904050a0f1109222a03110a150c0303022d120a0c020318030c09070c0605011e0302061819050418030903021e030706 62
    0x22900c00745009000505008080c0c81c079052201a09418019201d44503065a0364014000d03980000d090060400c00d010b41943c1c000040e42c0c1e800b004d8200a0042c903c201c0a251003400d640d8080384a40403890306c26a850f209401d2990501d01c0d8950310b080c070074a020080061070031a45014540c498040580420045000b161205402003400c0d041045040e069008440c031201008522100d04d0340c083c410286031a85810016a44d01c40d840294036514151303203062003a15800e41160704401e0040021f040c0940d92003c441000761690361840b0709171000300413110300580c8240800700b01c0b03440c106065950301d2005015641c8415a04020480354038080f00e006021415008086041080c18450b5500411411034501c0f0103880b08840c10340144283c2c030019209007000301d4041c110511240503a030502c00003c0000491100064201008042d14460f0b64803d038070305240000100203007081d4020b41d6606994884540d0b0950b42001380b05240703240603030701c410401d00094107141c07400c000e580c020b020152 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 852771591 1250 852770341 852770363
    0x13022202090f1c080c0127060c1e0c08090303040303020a0b1f060f0201021201090b030c01020a0f290a0501030b0106020d140307030e0111130f0b0909070c0609 70
    0x80140403900e5420b0403602c0c003408440001100340d0802018040c0c400307601484290703841d070010720302c41d001d01803401c0303203010080da124140200b0340750040b4020b04086c400d16040c040313410500c000b59064904c41c10040d00c5180d0b540e07a216030245c4541c0303100c06030910850240e030901c1e01c0000881d1a41d0010b401c202c000d079105080c018180411a181240c0c02100d10b5182500a43c6016207a062526030744500000c0c4841e1421030000e0b203000b9010740c2c070f00f920f41401950056a6844d00c040162080d04070282c024051003484101e50b500c081049099107410a502101100f600e035908582c0d050381100204103100450b501c8940c5943d0242c40d0b0303000392080f1601142950440c04c080c3c13565007042c1d2000d815584011110103650b60804d42a100760b00307051f1001c07526503403101011b401410010981e0b4040e0f510346450a001854908040d0041021403600441c690391aa02c4c3d0300e001c0703205401035016105042c8140ca1035850314040859002c00c8500d401038007100341da034654040e260b01d18800c9900300070325 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 852772841 1250 852771591 852771607
    0x290301030c1a04140d020a0509070e090a2708040e01090b030c0612060904051c09030515011d090c090a0c1e05091504031407080c030c0913022202 64
    0x40ca001d070300c1c2c842d0070311040703151500d4050040c4c000240004100e00601d11030140000b9076640001d00746c020000034003908464a0108801072031811081d1695100c1d07407403070021422001040c41151b820040d0440070b0403140e0400351100342c0a4030305440450b07180c98200b00100740140e01d05000d5009007062440451149081d6080600300840c0c03401c100d0180c40284180c503500d1044400c025000340050700c08400c0c1d43c41c0c13030403d80e0034501e48002808090035290504d00c840c80e0311030201380c02c41e400380003603455042d000740002c81440c00a110300c60640704017011004801c1d00c41e01c50280c001080304100e41c4c0510400c8045040710b90100d0700039043da0358039500c001107035070000940031040300088401c0782503000d20074000e0140c1c010344807100e0003080c402c44a0189001e1074002c440103590010281c0800414504c07000307076030f0012801000c41034002c00c01e404c13810b800c002480080c181e000821030031550755041280e0a803041c0800e000d0f80d00c040c14540c040c100400100c12202410380500016030344500e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 852774091 1250 852772841 852772859
    0x143312120a1103030408030a0e010902100f090f08070e07050d09060b03100c05031302030a02060d0203010611030702031c1b0b010f0e040f0201051b070906050a0618290301030c 77
    0x108942c89107504108100000070304650700b1603902107a6013000203615180400903a00400303480784002c4d0403400c0d02000a500607040081d0100c9141c99564104401d900c9410450364000144201d0750594044001406902d400c01340c1907511000920b00181440008442c850544d146800b0a0300d00303ea0b101e1040d1030700d060500a241500d040c41c00148036440004400401520000f03101c6000071681000840c115603047c80340744c4606400614442c0c0301d1000d41098402988280700317403800700f00c0160004443d14801701c156840103030018080c00c441d420068034094400034502240c41000003003446800c0b9000c0d1000b4000a050041d0f1003645658101460f014070442036801001e100412081004006420445e984100d140e0a281168842d511300c1100c0c0c0c0b8021102020800354085c804004c1200041c2e81e01150481e50201d030242106030780d981058821810140700b40003a20030501c000d10681d2074074442500e0410701004c80081071440c581032245190402e070800c0315151003841c402c03c05118 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 852775341 1250 852774091 852774107
    0x1e030a050106022d01060905040b0604061211040b0a0b0309010606020606040b0d170405060304050d0e010c02010206060d03090503070b030a15061b1e030201143312120a 74
    0x19150004013110480c1e0b4010060003442140c8100700c901c0c40c1a0408101002034002c2030082491140a1140381040e01d082640d401c02203039110301941c0b03041000181540e202c0c01e01103042e9040099070085011010a00001d03004110005030006170042c030000320480746200440c8182d6407600005102801d2032402400c284000d490140b00da81409025401070380e0346401a440a980000c585800d01082c1800304684d02865001a5010742d0100420052040220380b90b10b446220795210070720003030307403a005580e000381001c000790050344204000303885801c00e025024001c60090a140000c1a40d03030001910b05941c1d60440c01c03000b030000c400c1c813000018030b01032800040c808403002c509003410700000511400354038110108001c28424007006020451900075a40c0125420110031070009050180c0609410841c06580c2c0e00301e003001424800700883c00a00c100c0524a982c02c200c80003414000c00d41c05080401944100e0368103031031118030010403000710391021200c2501c0d2150244200581070324 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 852776591 1250 852775341 852775349
    0x1002030309211605120712090e011a090d02030d0c0c08070803250501090c1509050907031d0304080f0d02121204080c150604150e0406020f1e030a0501 66
    0x162280c0c0400e240c0c10a00d050b650450021860510303c11040d091103850107081c0301d00051800b0b0001002e03014003210a40011043c0355580740c40010507034810380030360503110900c1014542142448507515500c08400241140ca000600030310340d16206800290074410984100d04c0400d02403070300c0e0310070401203814550041101e14040d00443c0d1401000b56103902c20780c0a40d07500d400030030168000700d01c45260031014240d007100003048200c82c2e52810340f080c0401030003400b4882c401b0700c2c030880d5914400d8010209480d0302900004c515201d282c07080d0043c0010011600b20149801a040340510307080010700300408010008005c014036680c04a07050600b9034034400c0843d0414050007481041c0401101c0b52110b124103650f10648d140e0510041a0250030b0900171140203401301e09061507499004240600f008480400a501c0d41c141c80303843e154854483ca43e40070100b40000760106d1080d9025049214001000306d1502d40000540e11014000608102404501009000300d108651144a001d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 852777841 1250 852776591 852776623
    0xe01051503061206040305031e0709030b07020307140309011b0803041101120905010c02010b060a0c08030a1b0915052b0e01021303120c120e0307051002030309 70
    0x1541840041100340300300e00e0380403a8110000001c240c05440316540d40410400110550752541810700d0003d18907481503450151811b201c0030700a1700107440d4035505004604c41c0e190b0745805c52540d620b40e8003440e40203008030150300090083d40040307000b01c4d092030700c0c0071005000303590344000401c005020b00401c8011000341400d95032900c0002100e00c01100d41064111103107481c2024818012204449c1071080c0501e42401c0c10034000410074150022110031580b50024000003200c01d06000032400396015040012344140d07280004520028000e5812418151021802c0d414510420308800045c2111000103494a04208541c902080510104401038034205250804051110101211110700c0c020760b544103040e034a40b0742006074400c415180c01c2e10000d40d100c443c141c1c0c0310186800701f48400d9650422125114020600c10981400039a9101810f440c003051117400481d140318200402c590144a082008580b56490211000c1940540d42c02103580e40f0304146000e0030030480344420901 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 852779091 1250 852777841 852777869
    0x1060f06021609020c2b031b050417010b10020f0c0a0f030b07030b03060702011a0603010f12141c1b120f091d0402030609030a02070315150b04050307 66
    0x580e40b50012200031640ea0703860158441d03641c010443d041030546503c0c0b0418480702440380d150b803016541e00030415003580d02e082000e1569030b07504811203144a0f80c40c0001070820402400341d400402010420004000000030780c840f214000302c0d2500500010320743c05a8041502076001d00341c10170403400c01c0041074882030420752a0001c528040b050034000281302c00c84280c00100038a22980c010400ca01008085416500f420131000c2d0080600025610002140c040e020a03a8142082124102d41c0251102c1c4503040c90140320300d2024242c43c0044440c0d44480d061309988000410a0b4055240c078400d0090807503031000381c003501e030100700b0000c15410302034007100c0c101190700130310071044540160500120300d40340f542017101c001480d9080701210300b032403045581d011711120000354400d0384282c044682c1501d421100399070f00e0203407040e00c1c80180d01080d018000a01d64420080110300c0e00310001c100c10820b25041d80551415810400c401100407a08006034a800c01c03245000780b00d21410042e03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 852780341 1250 852779091 852779113
    0x30b090a03050a0503091005011806050103090b040209040f080c0d091e0e0a0914010905060f13020f06211006090b09040e03091206040204060f120b04110402040801060f0602 76
    0xb00c94000d40c1108003e200300400022501a0180009483c0c1d100c00700c0308100c00d40c1c6868003902c0300c2e4614078044a00e5860060041800e5000c1c0c8030709840540c00440c0c2e4092659541e017045400c0034010000c4a000c002200000c000840302006083d02501c2c01010b800300d1001c4410003000340c81254881c49000254154031540070316071461041c180c03038102c0c01d1243c4a07910500810040c00a880700280003c81151050320315031019881551468840c0d81070360b5183d10740000008000b4019111820b45900c5e50f10300c5801880c1c854140b1903411006050107007480d10f82c04080040c0d4820362440301c10b1103601c031f00700403400e446800d612001d803095080240070780c2c0c10895034002c64010b0b80000ba008079130720181807002c0784080003610140744004040010780f4440030112911200281c9049008504140c00400c001641501110a90b10300c40e44e44051000141c41d15100200f0240064500c500c800703041862603290380c0000c2c006041030f20008a502460003c0d101c1f0f10b410254041003c64014150701c030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 852781591 1250 852780341 852780347
    0xc030c120406020d0816111606050702040b1807121b03050601022104060507061503030512090a0803060103021b160303200613051614100c020f01050c0f070f030b090a03 74
    0x601c084181f840d080540200340c034580b5240001c3e41e54240c41c0030740c10071000201c480c2c0c01001408828403e0310148000c40e0040e0a0090b07c080714030f403400e514000040041c091a02c2002004c81070365840f44e0106403c5074400424083c6034540b080030f070010b03458404100b1f2a5804018109043d2210264070078149507034107000440c1d010354080c07103040100018111042c8038503500448955a04011200b02660350780c5006486035206007084c071481e01c28000020500800810884220b41d0403a031460b140d69070702c4004400039480002900c202c00407a140da0f020045003040030080304a90141c2840394241141000303000090080f01c0070311218091400c200c0449030200d21140c00417006107400c0e0f24070556103012810011010b40740240e03e00000d100058900c8501413515a1a0003550b003d01c8400400c0d03402c03100c02125207000780d000b03092418002000e51050004081c882610f07000c0d80c603c089020076060a001d015840b0340034021100c50203000340418484000d80140c9400028071011202c1d90b409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 852782841 1250 852781591 852781621
    0x316110c09061002070e01080114090304030b0118092f03010204230307090212480705010e03071a0709090903031d0f1018080c030c120406020d08 64
    0x1d0b50090f0380d84410304800c02d00820030302c4080c0a003118062160740c0c441c18014000c051450f03c190801ca00500410754205010084805076908040340701407980c244100d11126a10010728200300594841900c0d0200b550300d1610f0030085800e161101d01a10360070903110303810101c00a2039100e03910401c000c11101e040d088540602c00300401c07141100000281c0080c0c140b0086074032402e115070002464110354081c009005120300e400720303194445000b0303414141e01c00220b00e11140f03101c10303015124611080c24290303200b4640c034010040c45182403403541d134a03825140020b02180c240c0d44040307410020030224075003071034002102842c2400d007441d20203001420710b440c5201e0020100c0d90750994005151081d0820200320348858624100110076581c1641c1c0c03820784000c0920140a40074540d04a4040c44c0101d41c0c0d82c9240309a50130224a65484200f80d55010b0a032039041ca02c410480d100000d6814003901c100c005260741d906803100c0c500740020b4103200c0c1076910a000c0001c04410450f841118500b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 852784091 1250 852782841 852782851
    0x1110304180e070303020c0a4e0515130f0305030903072307060306050f06160c1805070f1713150915091101050a12020316110c09 57
    0x1150040c4140c1c4990440141488800c0503110b0080f01004414543c0018035031800b1001030382e024411704d60703c010a090b84801100c0d080d2409400951540b80c8000100741200001a285e14201e1000200b41205c40e0603e545002260290044109880c01503002d0321203079070150070415010740c0f64402d81e5440c0242444468003d00348100071000c5886034a041085d02c83c3c81c1d80c460244020b00c600008070010002040098080e00d00c9102130101d0254802e005007400c98401500e038600c1e00d100141003005940107501d8010900700907152120100303100c3c07100030004025807041000b5036440801c402094800c01815070061146d03c84490525950001c4013100107101e2201c16026038440b0b50703000c1425000502c001d0701a148041440075100e01c50782c0007102e528400d2958103500e4121685000981e604c0000c0075140d1140c2840b40c0724954042e2008012a5142d80382034120032040402800490b081641c45070700101100124000450300308024100000e03560b00100380c54021240054005100104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 852785341 1250 852784091 852784109
    0x20304060f030f0f1a01020f0d0521010f0501110a0203060103081617030a2a030e03040f060203091203130b18120d0e0603010305070618180e010b01110304 68
    0x20200100ca88254000f0500480d20002400340d10700180d02030014142210310492000c01da4400444c8560000514200c40030052001d0003000400300170035a0160410f11890740303188903210145040703819891440780030f400852078008103582424001805000300001505190b840a452a0056500091400e044a030300c8419542c0c2c504280e40182c4011007140780040000b640a0b4524413448181805140b089451010400110341e03038440c4290155840040200e002d11401c0704004528840d030030401c0382c0f00aa400312031410f9070b901c10000a000060307020030010703003010942244510744120465100312a0307100450400c4052100c41908079500e20986040c4500041c6c218446d800c0a4401407800d0001800311480b4041102d0090700c0e20389204210380083c0b402404114146440c0054905881c5c00c000105034807410070006a600c480c00e02404007000081420008004c108400c4c1010032401000000c242e0104282d6010309442440b08a070b0f050025900340c40103286800405d4404a8580714 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 852786591 1250 852785341 852785357
    0x12010b0a050903031c0e030901080a050a0605031906061a030732040e06090403020a0f03031e0c020c0406050d020d08040b030408040e0702011503060903270503010b0409020102030406 80
    0x600381e4151007010080d90701804046805080c902c14101c2d032403001e440c030107021302140521041841e224480c044001c1d004c604064003150740b80d10700c0e51140e681304035840c2c40061760300e442c1d000103882c03c1101c81c1049480c6580c0f01855003000040c0c0200030041c06030040ba0390b04900d00145221035408010070040801c0400c07682c409442e03844500010100a00c8503c1651340351745241070092540c403a001e040e01280c0040e0204d5560b0500c1a07a90340f00b0364040d405000c41003129a10a044034190b03540603420152254002c880e070302e9100c00340d040b2004030990300181140080c00040d040800d0103000c1ca1140f880c16170204902d0305c58950b020b950b0b650407607030300c43d51582500d80504140515008103204a40200810041000c030600601c25641618048280c59030703030120803826151045010f9070100a04c071020030024035039402c030150040c401d0400f582000300aa440429180301c0540380c4004107106282041907040c00e12843c54030030016102405484140d8001030b541e4231031885200c017080702403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 852787841 1250 852786591 852786607
    0x90f05010632040902072904021903080409050609090c01020c04021c0906060e0a2c190b011a03040804061b050a030e040506010e1503131e1712010b 65
    0x1109a980c0a00d0340c0c40b00c0b080c1c03156184c039610030007500310103400c4071222024024000b40000c0c00511018850f0034041450203540c60354203002c1c00c6e001c0c140c0304242d4080d0040d0040000342001340038001420744440005560304d0000c003042059a80901902c8103908140030310003043e42e01181d8206056001d89015030303940d20620441c0c1c5e82186500200c0741107407426900c081002903139042a0100c444c0000c0c00c840c40e4031241102421186505036006142004030300b070501d10900c010143c45200b1503030054944032800a0201c41001b1f010000407038600340c49000501110511110284243c902502051b042d4a02607881403180c0c4524060141845804140c10000240409504241940c03180c01c1d01d000164034540904881e60040080c1e2091382400c1c001516544964525401d400c00101981005003802d1801105c6500c0a050542041b52500070380c1c0128940081094110412001070341c03104880d41005060403049150010003000c041210510402d00040038a054500085401e940e59280b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 852789091 1250 852787841 852787907
    0x307170325111507080c0a0206060d02010c0618060c09060e040209040b0307170625030915020f0c0601080307030801030605102412020f0a082e090f050106 68
    0x400c0070581070320b00c502c1801c0307030303c159a42e01ca4070b02581c15030b211414561150031103000f031070082c2c521035001a03010100041261425000385c0b4001d80c0181010400280c064550000755046003c43c4c5003c41043c0401c0410000d4a20802010a625107420300c10303d0b00f030200c018180c9195451247c41550040340060443e0b41c1c40d88105a01500201100e0f9400d50303881c2284070080c002d24a54995005960009110108040281200e94550300b00b0b0b291a50500b82d041c0c009180951081e40e0041181101c2c100aa000d40300800c2e00c00d0030303244407545030030340d00d4611443c00d50141c10410070381d0004c0c4201000660040c115a040d83e92268000c00e580e903c8000e0080303ca5050340c8080c82007950900329030610340c02103107505404101d5640b070f00071034441c8141c504142e1251b00600a8010030801c2081c120922581500e0b407c200d4080c40d040031101745140c0a0704599015019550304203131007600b0001411b0074072484044c1400c12905002c990315141c1e0180112115100c281144000300101e0010058 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 852790341 1250 852789091 852789107
    0x90c08010e1f060b0d0c030e0106120510110304080f0f180405090c031b010c052e09020a0e042f0a080106030b07050c120403050307170325 61
    0x10208000c00459501070245542c901102107085001c58040702004250002030040c0c2c0150780c101d03a05103242c1030444184800411480c580c0030b00f0150ba0710030005078581d0a0107654001d20043d5202010004a81801420f00300c5030003040c81e4061400b074600c01e04006036030940354460741105040346c58240e80e6a51007040c1c0316500031000b1b02d141c00144903480d001e01440010030b0200c00d8404000c15503c041d8850b035100c5440031450b6140d071088401500b0300010350084d070342185040c0b41401800940f5901c86117007081c0344106d01081c4c203200082e80804428041c0600e6000c002507424045e000319034022400d803050a0180c15640701d414130000742031049218444120401040a4000c0316a10a441d54510801000041c1c0320300130710b460000380f040050042206176504038110343d03000d444021b4140c64952144000d902680a0750088242da070038600081c02c01580180c000e10358034101803500320000c1481106901c03001206106000946810312600000502e100400d03d80407241c0c403d0036194a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 852791591 1250 852790341 852790349
    0x20d020102100c030f0b0f0306180a0f05031b1603020927070305060106021b19030c030302011a0d030f0e01030204091509050c0a02060c07210c0201020c040b0105070204090c 76
    0x41c0c10700440c0342140f9410741c040106103400010411402801c04208087c06660712085641580480c0c00708103140501000d0300824030000085462098403030345c82000514080d03406503241c1d080880d901d4814100c02d1200c40c0402c01d6000981803c040002c00401a0602c50102074081c0c91104c4c00600001d5440d440603d0852039107030f1075042c5419100c141d6580346800d00088505004080000071800d0000a042c000c07100142c080e04040c00c071180a001d0407400316160368010000301d101c000b0101d10030355009000b560080e8008180244c152983c1502c00500181c001d000b4506130b08d001c2c1c00f0030303400b600d00e030030420b100c1c50840810001c42c001200a400740b5000440041d00d0700f0b040352040101080b940c0202c0d900070b44280000e546042c8808110b0148070345a030056040040000c204031800c8000b01460f82c40f0b0248481c95454069000c410b100b400365203400424412201c000c107540c8c041060074541d0004480c04e110342000c400000b00540a9824000e0040b0748450050b020459440981e801030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 852792841 1250 852791591 852791623
    0x7080702030f07152d02181c030f0e0a030b0711100c0215040f03210c20070f090e150705030f011505090607030309021e01090e1003020d020102 63
    0x40409082c4440074890200c040030080c3d19000b4038400541703c3c0580e0030018825820801408102504028083d40c8072020f642a00c5441828040716951107002541400c0342c2013070f914038108202e00d0081d007110520a150000d200f0b4018000304a03996581040d0241d07580042421842c0d1508481a1180390f1503041f8810341d40a61910400d1352078495111500210082d42266426045c6a00400800c4401e82c0e000d410a051451850042170240401d43c08000c43d12543d40b0303009414140840844180c46045000500805000345081c8545426a00b444085070040c08145140c24084000031415205091381c0c0f9448da4141c000e90030f41408520700a840902811580e454441401061a03000302c070b01c1c41d03c000b5044004034035088010121002000c19488030303460301c01c078075007006440d400c0800304504040d03c844240c40161990303411511400f00c02e18204c507074a00350100142c4036022941188074400e224000300301e448451103604200316601580c561842c0507280c00102c2c2880c03c484024004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 852794091 1250 852792841 852792847
    0x501090506010b0c0c041e151a040f0e0603060f1b190f090602060a09082101030212010c080c0904060806070c15050c07060f020903010f0b1009030b07080702030f 71
    0x1070b600d02c00001c0610080140c1a503040902d08400c000c111101d95610301d1002c0080907030100c00d00040c0d40024166001103803543e41c440da0b01c00364442740b814a85141954008003042c1008042125400d00010b0521a02804110b140c80000b180e52218001e100c1e07482590041c000c81c10500340341710302134502010700c4503866035550450104441c20b240d0341d1010001651a0400c0800c0c0c03442094050156441503000e0300342502c03000c890394042c0c100048141d80180c0b0030480c0106100c410788503810385142c5104d40019540c5103004001c420344245500607020b90401d044904216400700c030443e48203440b003a06035211010705022900a24182d00320303804901c20102400000e43c2c1140b02108454802c6103c40c1c1140d8454510005441e400ea03075400c0c1c0131605212490000b00e140d0440200c1107111040103041072003076800a03080d038030000780446000d035580b0510301c40307810213809607581c1c6082410700f010b000c0c1c5103580c0d46070000d400074054810050104045140540f0a004039403050000d4502c083d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 852795341 1250 852794091 852794099
    0x12020915130c1d01110304030308090309040903030b03060f16050f0d0518060603070e0c0c0a06151707030503070209040305040e010303093f05120a05041a25050109050601 75
    0x70116001c0003914a201c3d911181000031036205644016640c10310303c01543c106440c50360150340783c07407004d01941e01034002403181c214191550702c02d10b019903000c0d640c003050b414007840905040a1015002c11840c40e901d40400503071f00400c01a050184080d840c0c42607440b07005100f039651070700440d41c00180c1c65082506000c0f411509100855607a64801e059445a8481c4810955140311030b101c0d1044c80f6001600048e81c08402c1c0000d0070500341000140c401c2481d2503a64030084915040d101d20b9045d030400030501c0440d06040441410340a40402000c0da07608503213442e42d40e07001e080c100901c100300d000c001408051003402030758010590b180340410b45503142d01c1c010380f0b9010540034408007a070300406038400c4003440340040d4624019106211042c040a000074500300341d1103d006030743d02d100300c501000300e04c14588010500e50107296110742c0c07903078148982404036144110486603503040500a91580b00c034110546075003089a6a5070210540d03035468114054000200c02400f14092100002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 852796591 1250 852795341 852795347
    0x2071440020918041a07110d090b040e130f0f06050a0920042a090506030405030a051e030f040210110703020423010602070501030612020915130c 64
    0x50003030488480420210140c0c42114124056400580d5000c600e018070006102d00403010160010b00030405e411854100c00311900c1040c505480110015007071074198107c080d8148044514044586403190711103140c00912121800b49001e00c5000052081c08580320064074950b01180c942c0c030900030301c59450b0a013800e8a01c04000c11058420f64204030009045004501c20280a50381c000d0848079440680c0355407a40004e03109213007941099a4203c400c00a0342188000c000b4002c1001442d00c401203600d0780103001640a03400980074200a0040c000000c0d00881658410501441c0c15a141e00043c81c0c02012005001c0c811501c001c0c002091040010044042a120b02e000b600c9414112200380380490f0768600e11a4901403a4000c00f03414070061425411407007200580c1e0118580d02500c120b134004d08220280c0c4188050307072101318108615605405414001c00500c034509091b00c20f590003284c0600302c01004899640007907a04000b0641e601c2c0300c420f540d4510381400300a0402c40c01d20107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 852797841 1250 852796591 852796669
    0x20c0f010c020d0c052a03070909111005040909020f0d050c0a050f0a0b0d060f08070303020d050f0702100311031314030304050d11071a071e0201020714 67
    0x201e03005008660781c0c5400c2c1130181c1040708006500100400b0108092007164460b041150304100c500107060030041429602003000d0005440a00c0c1c0004418034285080100601c0300c00800740560032201f088800310782c1060a80c3d00f191001400804c2880980c40010300740700d045000603610248950115007030010005920480e058143c0f03034424100c0d00d803010840043c80d0505055070114080d441803042d043c80d80c0223000d843c0f821041c00f1035a6030300c40881400b88003c03608081c007261302c40d810800501d42d04204407807091000382003aa1030401e140d000b25500c0e00c64544040d0058110302d0840c4009807081e8041e441c2003010a5030302d5100d01b4941c510000b0038503400c0381031750340d5032010760540c007280b80100032030f070145a110000b4122903404100540d0b1042010a0105181c01500000a802150144d01140404280391119601e03c01441c1104901003142a40d101c842150306a01c40140d1700003c082050b0360381c0301019030302c9030601000079000d0754000281441d015503403400341d41079819041403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 852799091 1250 852797841 852797861
    0x60c0f0b0a0203220c2102060403050606130e1209030307050706020d0e1e190905090303040312140612120d0b180f0105190e04030e100c020112020d020c0f01 69
    0x29180c00b4904500ca8640484e000513010341341000c540010001d00c951b4120017007400144810b050700078034581c1c000886540242d40203440c56002a0f081120914003119443d4022066180c100700705904584140c1d80d84844c042c0c60805900001482d80c2c1c6540e0070010341c2ca20742e5000045500c140e4071940001d480b001e0b0808a000801e0800c20303002001d01d00400302c00f003000303415250f08005200020401040d840603040fa101f043d0720800c00420307070504a004152007007009900a40d41e0f41030900e0000c1001040035003551186151a182024014080184a0300200c04503076803058030004951039403c00300d103588401c125200006180c0c03083c0300c00c0e41051860260071a02a00208180031840100703880c200d13001c4020200309401413020b0300c0c22004248448051110800304241c441000745038401c0191015008609100da0100c468540b030003000003000441c1c50041c0d540e8410394006001d000d0003248c06421540c01285511102883c4d42c15952040d2692045400f07181c40c4484003402014a480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 852800341 1250 852799091 852799111
    0x1b02060c1206040f020f160308061c240e1507020105060d1205040b070b0f010501050c030a0804060908041d06040c140315150406030b0910060c0f0b0a0203 68
    0x800100c0c0c804498040d16021814074005010070b94034841040024510000c03550341c050740c00c0c0071160342d25203c01c01800200c14405100c0c00e08520b1410090a0303d0402003005201d1607200e00101803901e00580010081e036480480d02c1d6808440b242d66171010250401c4030005e492400340c2e0401c11240c002088009019002c504003a90388817900304900340e880880d9800d8006150303000b148001ba0300c440b9280000506854100c2c2441d8071004410026805407106030b5118080100340701030380425500041c010b02d0309003800d628045d0007000503910390240800b400c0c1030080c0c11001600313129181c0c000032085a404002d50b95140d40319070306030303409019204070740c0c070950541000511107080c60700c50a81803201f0394450f440040624807011016034801030412501c4145d502070b02005440321030250001101146601e903d4904100004048070080c14034035218001c3d003001c0c0048000c1100140f0140c41852400310000081400e01c24a81d1141450003440da0742c4181c20042805a0ba40c0030703500842d203001d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 852801591 1250 852800341 852800353
    0x90504050c3c0d0b130b0906061b03210a0e06041211070303050901270902032d07030506031515030c0d060b040b01080103150b0409061b02 61
    0x44481d88242c080c050044580350800c805018401102c00d0348070103402803004014082c5004402c942035542c02080c010b0340d61a45504e003901c414a0040350308507032030300e110742d0800100144000165001070080c02650003100300058115074411500c0c1e080060070242c8040381ea84210b07014020f00303650320f02c68148440d2120303013001c01d580c00028042d1a04080c1180300034016a1200d458000c011800101100280480307465009040541408810020750103034071840c4e1511920000940040340e0900e0034403012000c40301010390701d8000c601380e0707040c5d41704404016145c0e541c000b452000007080800c01e0f03a05000c1884011428414074200620a07880c50781c1c20310803520303002c050640d1014020b445106160344800000c80c01c00420206125100d801805c681d050104c08020ad4440e52180106556540d2201091a1281014003030480081d00a1810152540c90360700c2d0451a48203110b02e02e1001502c4940507401b90791107410512407140c003e0b4040054804d200c40d8a0120b103c43d4580c038000d40074903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 852802841 1250 852801591 852801601
    0x2010e0607050a03030515040518120406050f070816060605130203010617060a38090d0605060d17030601030609020c0c040513062d06050a0303030f0902060a09050405 73
    0x181507a2060398810002c1c003141d1969601a4090000103200c0b400350070304e24843c0d08055403580a490b004050082d130b04100d00034889851401c00c400d5240140b03440e00d080001f0440680d1200031a42441c400c000f045407100c0071445c096106104803524090364003885e096400c1840580e60221044035002c07568000d8071490480ca06c0181c0c0004d214060102e01215110114210b55001c01e544c440001402401d040743c840031090303904c616610950008080d0303045440300480b644c4640c9080c80181c10029400c04003d24002045024440c0000f4450340d2143c0108c1c1032500c0c1d000301032002d1548801030784028408a20340e0b110503042121050300082c00d0074400201d281840c070807250105400f80103401079550000c107101c06060041d1940412440b035a411030040340e607a201c0c0d04040d9040402140d10002080303411503071050780c801c0c079511396468140e04100799581e043c01d020840e54141000304100307100b403441100410040f04080d4002a00217100200f4035844600e44c000e8070421075003004580c580f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 852804091 1250 852802841 852802849
    0xe01020c0d18061209060b04050a02130f0f060f0e1507150b0609040218131d2b0e1809070611060705030612010204090b090609041713091802010e 64
    0x507031003031201040c0480e100b42413101c0070750881104c0d140901b40c00701d002d40301d0001080845200b19603408180d9400704169070100b0004920302c2c02800f1100210880f1f03424055031055401052042602348808041024405406810040210311004062034580085c00501143c81d038070141d0202c403007580e0b0107408000c07100e840c820354085841c0a4483c0d0b08104074581842300951051121046071180e0200744d1041c2d80d03c1d044080b440340b1499001064840351001d242070001c08800141c2025003001011211901148664036280001880300700c81c02039501c0000e0340d580c0c0d090018107800c1010000d40c130701480c54005403140519200c03000c42d525640d0744c000c120b032881901400d1070495001000410740540c841e8003e9078001e00020075440500012071101400caa0080c0d120b4414a61107a514085030301e481c041045e4400000d440c091002e1802e076480404108005611004002c1c0100700610780071075000082c40a00b584050420242000343d0580c1d074000003400c401c07800905010529003403410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 852805341 1250 852804091 852804137
    0xb13090c08240d140d1b020103090303060e0412090902090f100905060d05150609092809080c0709021e0d0906092a081506040e01020c0d 60
    0x391950320605140c40d0311060006200d1214036201c088840c210401e1020b54079a1600071995214048140102c0b005a005a040c10710382d41e442c0702403002080b013100003000800d1400841c1542440e0020f000100b915040c0e000f06406d8101c08400c8581078100030403c0b400c211050003001c12522040307a03295683c14504140d101c2c090703405802984e40e858100c0c803030500040c7e600d44034840381482101962120046800b98204001203020a504d6000b0300031181d0005041e006952015140e45240403010307000300f06c0f4040060b1880e03854243c1c0404450f5007408103064070103a0004e144060050090606050606421518100000c0d00800800103402d8172644219042c050070069040d4041d2116200b0106c4e41d0858a4854102070701c4d50300d807a0014440d4800c025190b403180049031070510b020b0303404d901190103c4501c001d01030000e0f44144184032001441c0742660701c51010604055540744046005048500643d064940c0040344240c4110004507000c0505446a0f541e0708603600303064001107005c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 852806591 1250 852805341 852805361
    0x603120307080411091506030406020c120406090b16020d05011103090109050c0607030f05030a02130f0306050703090510090203030903100516050a1b1a01032f03030307030c02070905010b1309 84
    0x986c40e0004076910308004001e03540c0503020b0500141400782507071010f800c045d103803034042c0418480007405218094100602c4030160031100c61160900d0500000c00c01380d0071400c4006485608034001c9001008001d4001d0045c5a0f960000142c03241080c40c2c029000c0c0c035403c18100c1d0240100c80c4500700701e0078514295000950075a44401104001b8041030300c03294405480103051a03000c008144028032a880c02c00001c0c40000c803074a60461a5041c4041240d1010700300e5800c160810b100ca0011a40014031400c41910107880000ea42c1503070301c0040c3c90344c031555000a815000c5c2900d15111200a0390042c1d1003402c915184101640306e1102c211014030501e0f88820104103211210b00c02d002100e030b03842c138569120300402c1c160a40f020145102da030109078404c40398288914181c0705070703030f55400d2071140d2440e2500c0d81010a45030840000d03280e0100410030010180d030780f45d80c803405030300c01c10085000303049502040110f035851309500100c40d801400c08942c03180e10a4000540e10005202e07102c1c00c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 852807841 1250 852806591 852806611
    0xe10030e0604080307110303090a0c060e0307030210090e1815041a0c04170609070801020705061306020909090a06051501170c190306030519080d0203060312030708041109 75
    0x60b601d969607400d00da003014041c14204110b40b1400d000780030040000b9401101411300a04038180d16242000c1c1a00c07090300b120f4200007200040c6019030f14000b03040720549078111156002c85035002011914142998040400703400d0100910079074000f1600804486800321003610400c920805140d40540c0c1c1c16103006090404c0080c0c0905061503502c0c0ca250482c60105840303107070a9032401c41d400c215900074000032254201204cc0412174000304010030052401c0402507042600341e403981a2175180082040007072646103201401006040d40c100d13580f00c18020031010031801c0a000c1650b6401061008546062419001c2240c100100200d060300e001c050b50b44071410309800000308100c85019140032030500c0c050014940a061748034030301031005001c6d41d00244162440c1486854402c4481e40340d141c201c030301581080032407903070822901e8519040d1405a980d48800d40407a00d07011812180044106010050025070b681c04984140194010825154940110001c1044002040da00c04180e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 852809091 1250 852807841 852807853
    0x7050105160c060b01030906110903070f0f0315090c170709060f0504020c0a05010e0d090e010e130309030209130b060901080714040609090804081209010f1d100e10030e 74
    0x100720b5040001104411b14000ca0f4024203a9103440c1507894071410010703103020200e8001400c1c10204030840082061403030b00c12a407490300c45d0152509840d40400b612040e200f00ca0311001c0f034500e82010500580c000e002e20300c600d65596290a0460515911030014003c1444c000ba151009001c4c48045c0c0da03c01c1c0d48c3d04042072821040200070b5000c03041c0803646000b1143d03000e0100c1c03800c3c810000420703010780251002210354040140304070b52a070415011142883c00603c00f40c1001030100b94801603007588148040694141661043c02039400250b10001203c100320003503407040307418464140f0800420900b130b00c4090420801d08024040c418240e4002d01081114260481d4501640000038000182a0b40c540f081e00d42a51002d4100740c40300d200c0003904128050040000e4003c460800751602d0600c000d0f0301c0024049014452a0b000300325284880c0007a18488496450f51200000d140c0000500a500b0240c035404111203003510501c203d094040850f4041d002c0d0004d01c400036000f40107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 852810341 1250 852809091 852809093
    0x305160e070914030c040921031b0f0512010b1201060e090406110d020d0c0e03030703080610030e10090510020a020322151d100f230a0507050105160c 66
    0x2010f1445859258107100d08401c084403510350f80f080000650280c102c000c1c80501050006c1012613020110307104051814200403e0086032103889900c003507080ca003120ba0740640c00003c84072030140c941152620300400b00006240807000000713050303086018940700c1007680e8034003050f14141242104903400000b0600010005030340c60b40050200458450a0340c103042140c0203000403030300a140740340301c81943c1300f83c40f481e1160070490700548000b0442c002e40c508022584d0080c030104014010318015680c24400f43e0802d806904202c0015912008903035031081150885005401864415074040c001d059101d00084428000c84400b00c00a800540c0f03840a01101040f05560300c2074201840104401e0100d4640b0300840c8192820320b0f10b5a462108018020110b882d4184506025204002c2d0914580301140c0280c1c02815450b40340c102001e005a0b44401c0100550401e14017200d807440c000380410400390020040d1080314000d2000f0440c0e980c680d075000d0180c0c3e0001a603603021031190b140c024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 852811591 1250 852810341 852810359
    0x3030a1103041d0624070602070501230610050c070b0904090507060203030a0f0203070c060e07030230010605031c021216290a02070c03020603010305160e0709 70
    0x10303519600100480386440da95607100e2803051140c02c10002e0042004040c00000c1c03400e0150341c010144084121412102e0707603507854401c0e03c2505002000d5980202e2100d0902c40203520059100811001c480700014603103c102040e00300440e80c0911031002c0c0c1d010103110601c2681035030044c2c2c403544020802981840b104a403541c001b0507986900030f880c1c8190800090042c040b82004004640046440f41031101d201c07002c0d50b01c00841019800d1042c01004082d80d403000001021a800c91000501250ba60320b07041d0501000e50001394200060f5259590708201c82c104d20404201031140b420240310420312082e0070b8800030b01c00c032a81076204910030320b46d10416180316042400280115904040d141354000b8076070300711110000c40c01840f032843c01701703210945003488042050181c0d090201500070301c0b03141001c0c0000d400c50021503804941c0000b08a00d0124650240d80c0003806683c0341e41e507914000ba030ba518403181100c41c802501d0800522220703640b802600421094031040103150800c8552 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 852812841 1250 852811591 852811607
    0x301052809080f040e0f01080d0206150105120c1b16060e010203070c06030915020304120e03100204081006080d08041214030403021c17040818060c03090a0608010503030a 75
    0xa98456008001c8407080041e00343c0140000c2c0201c035042582c1d0700d445403d03c141488140d00184c01c541059154448540d404520280d00104541540720380c0440b603c012942c5011b0f1001c0c80c1000c1180409114106440b2005001040d4011051170590180646103e07103c0d42e4207a00340503404900302c4244005401071b00588400036042c4102c80c1404d2554940340d403441041d50090f40441d0345e44100d03c00b4000040192101085909802d40ca1810143e6601c410f01111555607010054000f442882039a01404510742c3c0c208007a500359190b83e2141d0340c1c180c6580c07103140480b54081c13500400081c40745010640a01044071074858a109981c2c645910301c211140b644180c0422003a00c01c000c0c8111400e601071405140240d004001d036050300b00b040a500c06010a52005000c9182a52105a944c1c0c07512627503c25805410071f5140c2c2c44d1203010f02c2101c3d0103a5142036000c04041020002c519000001d000000c408650703502082d0303034034a01541d1045081c02020b1300754000b0040214007038018407031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 852814091 1250 852812841 852812843
    0x10306080709050c190801060e10022508070303080a180f11011e0816050c0d140d060e04150203010b09010c031809021317030a08070909060b090301052809 68
    0x280030b00e0490101c4603417812401d0b0364860404a0900001400101d5000c0305250018800f507a41c43c440109406020755207800d0403100402c004140c2c40c1402c07100c0c000c1c542000052403050200d9030015220714000c2d000c1c000031101c51409901e030802201c1d1a0143c000703203201c040d42000b4640c1c903610042c1c07648500e11402c0e000d06418060340c141c03a8200740c01c090041880c120b400da41c0c1c924907400c1200d50f181c20000d0081d9084100f14040c4903d0200500110f4483d00301291030a0070840d00ca040e4809041d5402030020380585603141c010000b07450700c00d550459101c3c03445603035003901503821028a482240401c2c000c5003460300b4140f01048095000b84080400c0c0743c02803c1401c411400c01380100300400701500030301082c980104007078001010300e901c04030143c800d41762010f4408504454140d0740c2d00945403504104030310301020034651409030780c900740501402403040c013499803910b2440456501c01d054140c02503203010001802c0004280031030080c0c07489000300103248003407150300320701600386040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 852815341 1250 852814091 852814111
    0xd0605180610140613030c03060509011503031e1205010e040c09020f1206030c2e0e06030703021b010c0306170c0d061e1e0e031207030c0c0516050a0501030608070905 73
    0x380072012407d0b06201000a40c403400b4040303028a010300049007907490742050064444041c42c028400203400a1b0100401c4807600083d000854000200b00c80090680350496007451400002148002c02202c0e4103208a000e8034038103680360350782c080d00d800700d00c2903041c003288045080c0413581a032054107034540d4110000030112050a2420000107081d0044100c2514550406041000103039080c0c421910704c0c544c40c0d0400594500440002c503106200081591b0b041550000300c4a0048001c03001c8a140e0b807500e940200081c3e01d028001070000c00c664042c6c40d01020b847c0c504d45102080000d011001c05002502e4044d580c00a942c800d00503120811402c01c41140211500000404500c9a00091001440c01c0c0f0341c2140440310070411184600c0d8130080a030401c12031108843d4500300102d0708641c1ca860300082181c7c21100c1103900c03200a0744000c2036070040e0800b44440f5000c04444809541c0f04540c880800d554890056003140e20030b12510640d504007050800c81e10525a101d158050300e162 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 852816591 1250 852815341 852815377
    0x52a090118031410050604090f020f03031204050606010207150e0112331a0a0e0f090103030513142202070c030503040801050702010203150f0d06051806101406 70
    0x250b1429030380d155402402d0029408110141c0c09a13100e4040c060308100c080e40c5c2000420459110054141d04254002c2d004075900c29821840745ca0401c22500d61040708058804c2030700b018030b4900e032950001d07a02a401407103512008241c0803254040000b00151689030394642424860041d81c0481c040080c481141e079491840a03103103403d0240e0014102c05004400759041c003c906c411540703000d1a0000304201e40322004140420545e02d00302c1e511113846080c203a00030b241800004035804009485180c21100302c1d0700001c20160021b01619102d1500c1480c4141c031616841458121381030ba0311143e5000054a08459041000e01000341c1500100c402c050b03d40b0140b52124419545580d2084550f588001010001000c3c2845202d4201c440b0344025859810504818007102c3c1c1d81d4950140700c0c64440108071083da4600070f0144029a1114040c4810301e400d8481c1d251405440c1c2c2c40989034000c003800030721100801d0706181c06940421a1074945800000240031840e000003038200350104100f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 852817841 1250 852816591 852816593
    0x41a071d0f1806041104090605011e02060117120d0912020d0f030c0207090510030201020f0102090d150b0d08040518040b0403031d010e010507030f02030f060909030d020706052a09011803 82
    0x5c5001040505204c6001282c40c030f29140004000540030f03684036941d19045a40d42c0b4001e580400d405d0b0442d600051074202e0b69198015803428030004501400030707807200065151100e41c45030001000103006691a20100c0310a15060342c45030311f450444c00c001210b03040d2108600d0701076070004d0078505541c4112020540c4442d84001110302c191103580d006004964108119a4101302c0040506002c100035403d2011140100c0c88020111000070060683d41c000c4659074a51030380144402c3e040103003501c40f0050030b0706160313034241c3c498003038135020311041201440300901070500c450140d54407106194890361151821401000280c4085c0d11840034010301c088039000900800d0001d403600f1000107110708100e40c0c050200d83c0e00d010340e2000d540c0144104003808108050841d800b0070305444d540340d0380c0da40407500c90452180d0210748210503c04101942032007d03d078040e600c50242c4014421a0b0342c40d0301d4101d2100c141079042c40c5045d9804000241751544a5044503002c0206090364008064807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 852819091 1250 852817841 852817871
    0x41209081516051303060b010c02060703030605120c0f040c18030b0915070c020411040b07111002030c100b0102070905091b27041a071d0f180604 64
    0x103841400074491886030038002c0d040100b45803031102003001c0c1001460407210040201403210580b00161100c0d40da5813440e15681d008001c00c1006560007422540c1d600002e140181c010800750103214095025800c103980e00701c00c0011001c0e82820300034402c0405607800000c000162181a0590003003010348131900d011118074540c40405584904000000b61500781880307454460801c4801071960002c1d0107000640c0d4200392100d4801c3d805440c046881c100d580d84120041c400c0340e1000000d4800000e0290510440e045601e1600b0001c46116007040e14171001240e5030702415040c03001a4202d140c070b42a01c50200d0740007000c42c22041c01594010350b0b449180d14100c420844a903581908110343c44201c4071400501c44681560845810740c45850752a0302c0c0d8902140d041c0d106400c0804c090110b001c0c1301c044035058982202a404808281c5403022004154409165010540110b103c10800c91441c2c070141c401c00100c4050403004903400780d07111418041801a0011703030425640e400710b18603400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 852820341 1250 852819091 852819103
    0x50c04150b0c1009121b0f020603250509010210020307050318010b0d060603031808120f13060c0201020d080603030706110c060a0506031005010e130314070302010c0801150804120908 80
    0x406507550010300007020002030300f4106c54100030060312031a0101c901c00a2016032100c0c945640542c1c005880c3d0741c0d030709401c15035039005840e00351403064441c10509a00c1d51240051401d41c900b0ba080c2d4030141c2c2c2c0281e8540980c002134404001207201400000e021040d15030385419007250880011410821250108400b503200610983c0d1490700c858090044c181c101007000c400e680041114080c0c1480d10049030348540702402c00304228079002480c03051039501d0405841e4400c544260001580340c0c0d5030070180405407800001c0b0b01500408410041c6140289044c51054401030082c5140040941d280b40c02446c040c8000c0b11243d000b404a048017403030400c00706210b403a040300300180300d040031800c1614100d00b90b0070740a0345034142001400a410410602c54001d554108003071500c414038541521030010049005003001c1e000b00e198424141c1c150080d181d44002d071788414500b80d80b01d01e102c000c200000210031011a007000040f400094503280e4560724515107103005410340d0f40f00c401c11401c3c88 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 852821591 1250 852820341 852820343
    0x525020a0803040b0a1805060408090d0516030c0f150c02010504170d0206060409020109210b153d03150e090c01020f06071b0c0b07050c04150b0c1009 66
    0x100ca4400c000d01c400c0a845440c0c46c0e0301160060070f20350041d030358809aa410009000520050001c40c2c0a00c4a45825110510007076002060742e0134040701c5010200c869a071803100b41e0310401055000a090110b4084003819034454000c83c44410405da80161540030303400c28100e0400c5010040068003070903808040c00000301d4100a001070320721805001b80350081c040e1038588118030f0000c0082c0180c2e001206c4000b181c10380201d54041c2450444569114507180c01d02a12000c40d0a00f001000030800540349100c01c4220313680c0c480c0008000412060b401c0c00444100c18650105401c0d0462807408002c403018490351074081490b10340100525004415648002908152841440314448045c400603407014020301c01080c0020074503c03501e58030680079014070140320a1650310141c8001081c49268110b4001c071045604542d184108800d0794014070065540303002d0740c09500040d00c1c0c6401240740102e620341a000c0a0b905090704000c2660110104000da031080c100000e0050545016010000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 852822841 1250 852821591 852821603
    0x150c054e07050f06151e150c0a060501120201080415060503030c072c01171911130c0f030b040e12030f0108010612110f0a0e010f090525020a080304 65
    0x102ca0b400c103d0750f241060240580c0c4400d0b003017007100d84032a25419440310000562001460501c030040313020851101c030f001042c0242800005003003231901c5001443d503410908c9090100803a0f83d850305c011000c103000341d000030300050480c0c01140100700341c1400709600c615156800144241d0700c000103851f55001448862071a0807091081001400e0741070f1a04010348070b00000c04480c00d81c40e41514580005009440c1031404941c21100600020411401014904211a0f20b2035020b0b0801407141c00040012034800d010761312540d20110000d0140d540c55880310f072901107490500e40740075806090101011a0000d41c1c0d10608070020710108401e580410140c0c04955aa0a12000d0001203180580000c80268107042c0300304048082070982a100541004a14011420000c009074641203411602903024500300b03004a001101e516205040b1050035640340300407596004402c00f0340b00212503416450103120325074192072809046c0950381d030395244140e69010405a8807181250002e41c0c0954007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 852824091 1250 852822841 852822853
    0xe040518060a1a030313030323070812060d12032316020c120303070e130f0f0f0b030604080309120301080f15090a0f050106150c054e0705 61
    0x44041d000485031801c0f00030781c060f501e0031284402040012681e88001410003143c0f50000000d80300488001c401030400c0800d25590b414607003848101608200000c84808214030007082c10b614105014442107640048445904814214151f00525480610041c02d244810000340203580e0082158400e454503040ca45100f6803180000340303032103070b505c400a01030440980010200d07007001090700c0d80003120341380c06403070070118002080810505400101400e030a0071034107029181c1c0f80c0c11a00010700700207401c0061010205035482500c03004144190150030040c04a0b01040d41c0d83d00540d4044d440300100c03032411281500c0322145520036401141035070040348010440c0c04003448198000210f801180384541440c10010752583c803414002440186001480f0003000300030340156005107501100102c1d46911044003a1400d0f8151104803814024010140300a024012203044100044019041c010800c404006100820504d030700c030850022843c004170701e00d41000240315052041c0003400d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 852825341 1250 852824091 852824111
    0x3021e01050c0102120f060609130b03031902031c1802060f070506181c05030a0504140319080c0a0e01110703020306012d0b0f0901050d050a020403021009060e040518060a 75
    0x800c6d214040c102600c00d0400300201021507403000d170814403112001100244400c07241c00028518483d40d29180c42c1404000702141610342c020015040183c03051104c0003e10390341c03a1400c3d045681a040c4040c003214130003490303405814020080c1208101c4941c07000d161002d00d0f1510340c5490f0048034201485441c0602c0060451700500981c90030152420000071103014010000e40070740001041c08011503990800a000c4c4034128100b094000f6542c025070f0394402c070b20340301004441c44640d00080499040004507000210400484000220907500c40e0f02010f00d45004440114111707000b4400d51140707020101c00b6039000c3c01501d000b081c049400c3d0442071042d000706580e40d4000003000110f910348120070444c841d00c1c1011255100c44244400381d2b01c05441006a8035409003101c0342611601d42010041d580c42903030f00520680c0d0080750381344c404a107001012030b4011914090040000c180341c07004002070a00780c10490704048960a8205a1007216a00300d1400c48101c034a544100c0e04c80c801c8003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 852826591 1250 852825341 852825361
    0x7140303040c1a0301120816030f02071d0402010e150d09031704020d02060f0d0e060411100504120807060e0c1320211501030605040603021e01050c010212 68
    0x600400c04580038042445007110146440e02051050721072071101e51b549103003000712000031a5941c0001c403200003074040f09410000c10800e100300c00c03040503200b1400085a0002d55414101e4940d2a081c100005a662a03004480e14040720b080c0702d41002e0703d60024140d61440d81301030703c86100942c0d40081c0c001d80600b4014120010b100c41170a07641c0c00c0d141030102688030398400d00074590b015074120b60f032015a200b44083d0f074428118108600c1d45880281509602d002c26414000d50040c0b804001d510f802404010340300036808140e1340030450030007040190310a0104034000d03050044010604110940c0c0301d48040d240da0752000803890300406d000500e01e18003d0305800424141030010050000280c0544146940340d4420784a03400012840d48a02c80d00d00c0c030010841c8405003100d20702414109440000301400c00c02503800b007030034100f01003820f0a1902c0740f4403c030f07500100b00d440c141010030024904402405e440038100041004280e10198003400100b980b1003403a0246149480c0c1000c0b05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 852827841 1250 852826591 852826613
    0x30c031109030d0c030e0d030305060f03150a09150204080c04140915100306060b0a030e030a050f090f1504090f0e0c060c15071d120714060714030304 66
    0x200440c40d500780003480c1a51400940301c0351142d0720b030900050059440c101954a20401041554000494074104003050b92542015002c0d07001a01c0b02d50b82c1c014480300701901c800d0040300103078405004d81d0000d9045061604100282402a00000c0b8002c1c4142500c2c0103a030300503000036242d9070100d1444c1c0032904007441042c01d1a001d1030355804282c285040c9030b40d11880c5490314801010101804517840358a002c190300b0055038012000c0004565940c003000d4290024010100428900410590175510110450760542e03415590b09140c5000c90b050030500d904042c04580d0030482d052203081c0c4503180e0b00443e51008400d20038090310307945042090f100f0780d1500c48100400c03e0400308030f042035040000702c03048070f6601241d01030348590f0944c030407500d00b41c82852140040349040050004254100b5200402c25038540041070840c882117003030100c841032208000d0119408058200701049402e48615017602000340300d146000d076036495191001210004003052500700000307000030020140b91b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 852829091 1250 852827841 852827861
    0x20609371502150601030c2d020d030b011b051f0e07050d020609092a0a08070f0f080a060b0c01060f060f050708030406020d020a030b011b05100b040e0d030c03 70
    0xc028000009260400c0e500029000f00c5c103240c0c90310035841c9064000d0704c10f01a8034180700303288444003104001d20090f078006001c05102500401203a15401d40c0309004100b07000c0c00684520242c4008001e4120388101e580c1c03400c0c1c41c640242841c281101103105405d04201c03042c03a40114106051403110790a10782240c0c8000d2080c80000c10850058413800b0588900c1001241c04590300d9580b8035030520090b2100c41802c403942020814003040e40e0300039020345a05c560a50307501c0c016a407003010035200108600e0006000c15541145440c000d481000d0032540310b545a0700c041111070f1303a5040c414080e00081c00102c66039444510a00c401f41e000f42503180141180e00c0d264012440710140034086100780c1700301600340100000000c2c107201040d01181d0101d06e040c4000c6648030140b07480113006250101d0164000f442e40124002c0440408100b281195001005041000d4040480e01d0080032501c54040c0c020391224140c80310141c0c02d00c0000c0700002552004030395690300c41001811640031040b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 852830341 1250 852829091 852829093
    0x504020310290a270b040c021518010914100c1b03030b21100b1e041803050403050114160503041b120506010909020609371502 56
    0x4124892034a0042502c140d54194011000c1c0301a1007804076441142c5504440075103500c08072541450040402d101c2500110b10800304810b84401c801c10042c0e82040d450395005070700100200a0072040c829401c3d40244e40d4812500c40c01c15021480ba09445120070180c81030141607018440c20b6400741725242004240d50700400c4210128100030780b491107605418148814800074400c1014003d52103c010f4500040413000707003806900d980040c07481c64240e4041c1c50b0003102c0c0c1869000003c0e008100ea80c51004114400d0806c032003414812a5000c09180d03070b80640c0711000704140003124403211100b50302940d0b03400c1e030302d6086003803560950b041c84007a5054192604100440300100c00481000c44149141680c1c1e00d440300d007001210707400182a407020909070290005854005441100100b0b40316800b5900507a0ba110000300444070b4a00000e0742040c8100034112452070040050488001c1c03062010f0b005007402441f9120001d14582d914104440c689014824030800080c101c2440e01c0e548 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 852831591 1250 852830341 852830351
    0x6030604020d14031c09030201181e020301110a03090209091902010f050c010c090f05060708090613090f0501060e1f0e0418121b110f0d06050702010504020310 70
    0x180c041500c0b084800005855500c02c0c080c208a8110300b4011150030140c01c04103100088001046440201002c420843c003562800c3c01120050107080c0c0410503490f0002c25805010880c8442007502a42800049a00d5540d901036508078049580151000d000c1d6503400040320303149403060141d0380c000944282c12503801802d404513045008903860781132660a107000304411a0042f1b06541900409491112a500f0041d41e03c500da81d000b03141c031044039047c0184e850460b0742c800c203215680c4244603025150002c1001981080e061103001400d02c00961544042e4a643e580031a40454581c0d400620081e0b0301d6800400409a03c041d2400c2244022241100e00d4140c1c6212400913070080b002100a00c03031484c1e84a00791350754075800402c103400c1c0621000c05145042c6403044080f1181c0b15150701140d60343d5004040030b0310030130030390000c00e50000302c0075141d940c02800c110042c4090095a544066840c1a1800003901341c01901e01079420341d000825035080a20405040c40868548490030724502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 852832841 1250 852831591 852831593
    0x18170708030601030f02040815100f060504090b010509150c07240f020c0d0308041a04080703050304020d06020d091709060403030e06090901030506010e0a0207110118050307090603020906030604 85
    0x280304403904070209080c0090801d00c403d0b1600083d000780e50104826008098000d2100d4102c151403c0c8105c0a01000303098050310340003004d00448a038000c2c0b40001d0414801800031852503403100303004903014100745052402010008088004500007c422501d022174101840b18080028202a01740c0c40d0416418000c4a041890b110211410600030003228604402801c0c1c028080c111045c580506002c54880c0c090070090560364060b00c040380c5400d4200c2c4001c400c2c3c01107822540c0100d0b40950740528096658034101c0d0590400f42c07040c0ea0201d00303c0b0441c00040c015100403c0207403103c923004540c0410a041440c45880b42c80c08041c00d0040400c6508600d95030b1008a600b500c8d4141428030440002c9408201070b4054030504a802070180400841440000244203048a007036100350071a5603100003405043e809040d030300408007480910300111540c094034018051020048030281415554400249040d80035444244074640d500030620550411400c469030004c2c090b00102864106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 852834091 1250 852832841 852832853
    0x3020d0e15030a0608011a03150705040302090403093c030b13030203090603040b0603060907030c032004060e2202061614010204030c060e040c17130204181707 70
    0x107200c205104003a0020001d142800903600c500302800000c0001c00402c00325219065004060300300c0e00b4801d00c200058082245502c0d0f4401c3e12524139a81c40c10700b06844c1d94240220440c01900480134400b2449001c03800326002096a4014840c003c00404210701110013100d403100400c0180100f903021340710a1000c9880016095080300c640c20003c601703000c07103040072030550203030381c405660260000050209012900c0300b0305e03018242c100c0075102140c445d07030049940c2c1c3c0910b10000340100c02d91481040482c2c03c1040582440e03c00c070140301800380c50100050111400c5411001e0782e4034244040c005050310b1081241e548000209220b56110065000205d00b401410328034185c0d41c0b401040c8504120796003125921009464000b952170390b4076460010100340c014000d13440041c0c400000080c05107400d0140002045a540310300f00030240d072081850b11408014140d0407010369081e400780040e05c070381c401c4000140310f101070091105210f191041201c0c01d85000560244400c0c0301a13004110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 852835341 1250 852834091 852834109
    0xe090a020f0109050d0b01030b09030c0a081e0a090f05010e01020a080315060313060f090b15120307051605061201140d240c020105010f0b132103020d0e 67
    0x501180e901c40303400d40c0c500040710b6000040c0c01a80e0070600e00700701d040400c6100c6e104141a244110b400003403940d070310024a5500c1c01511101c0100754820002503010442c4c8900410003585c0300f80d042d504a441c000031440040d0700401c00c5400003403404900301301c0a00c0b14100d01024080034030300b118000c140d0100003580e17203900c00030180c004000000840e842500d0741c0703010316a2123400391001d92649880840c1c1c0821801e144000d440c03c81c240514480949410310404d1003450303204021800e1074641c50142c061580500d508242c00c1140c07105d17410500f0000700b0140002910540003009014070382420790900f18900d074001c40c000c070400d0100000320700c00d02d964181921a16036a078910700e40b44000007525403a0341003001c0c08a4600c41c0c040c8200403880200f4107a030300d21a50080c0b101c013070740001c12801c0703034000d1003145604448001d06112405404000300036280107041c03003000c10750b00c803801140f0100040325141c800401c0c1207491020160140b0921001d106541002a41101984086202c1c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 852836591 1250 852835341 852835343
    0x10f090b0406140405150d05070f050304080a020f06160905060a0f11010204030618050d0806100318080a0309030f110c13180507050f0301061208030402010c05160f0e090a 75
    0xc090842c1035051003d4140d900621004112080c55100e11181c007086a100b0081100101e04100000d480c250040c100103103000310555400b840d50380c4135216000981c00540b02481140500d10340300c04503002c1041440d000e88802c110100005810700783c00343c46410750750701c92400703240240040c00019400081d03802402c00c030750038000d41c0c2d21007051040d4024815a04000e02d818501649490400303890643c000b00c2d6481041142c840c3c0070015030070364551204507449680022461440d0400c94865002a000f00b0800d281c041d107030310700071f45e540241900200c82450000707a50f40449420f160344400500301f00d05044c242440203d583d03044a6448050040900d8090051141220861403a0b0390041e507032031191451180b020400303489c0041d1184420711665205410400c5000200c0c038041c032916003103a501208041c002d4119503180149604014003e0b8144080036108501250040c03185094002114500c450150b04000c42102c071001b20b50418a075540e100e01c02c110300369200042c410415 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 852837841 1250 852836591 852836597
    0x91206020c24010e0919030f0207030b0408030f1e0a0504081b01200f18121203010905310204061701051006050306060f07021507050a02010f090b0406 66
    0x1840611405601d0482c0c00800361041015550448010010030948581a00c200200324025620350804a95030340348800c07080745111581d0f4104600003405004000340002290040ea0840d41c0d40b500d598107202400c8800b50303441c90000041108081c0d1400c100f13079100990329100d419030406507403200360302000100400342c2540d0362008503050010305002e480040190b450000700d604c0202c50341c0c0780a04084823030034103981a915050f14814009405903802d0001c00384400d42088825180018411038825409402411440300c1034452075081c0040c0030030106640d525541d03035141a4040040700e000419500a0506840801280000490103c0180503040103664140102400024000c0000d5405080911680c0401200022043d04034034032902411220b4500300e81e403160241e4151004550035035105404120b07692039240d018016004d283e002400540c10380690700c0300e01c05907500c0010290745a0788105259011907900a0b900b801440c2e0610340300105501c1c04807692024041c500414041c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 852839091 1250 852837841 852837847
    0x10030b04050304030f050a050601080f030a12061d040308062715060a09060206010b071e03050904050a0b040b2e0e0d0309030b1b0a050c10060b04050f0109120602 71
    0x40c0704040040d100510f4000d9444021492603113040b99039512000002c59441c040e41c400020107e0000c80c541d0752103072080d009146405003070b02045491001c0c82415080003550303040c010a50a684844490b6185001c0220001905040c03d02800704040203150301e105100a8079000040060018401202c010f5803c40581513202c801119010307503071103810f25070019404a80140d49550000c00c440840d621034095400590303d40039000038600c0748280180076007815122030700414105171090b00060b0f029203403444c20700f1100d0001409a920540ba121003080c0c030b441e0781042c0c03403409100703540119504403005480525003161401903101c024803078603841c965881d0601c0a441c001c1c4000c012101005052a6003002c0500c0c0c01340c540101c80c081691030303003200300020703081c01103074412580320290a0f80c41500b016044c0e10125150342c0010781c500114080c51328082503070081e502450004c0d180d5400440c0e00c89082c801032024030100c1ca402075041100d40c0c101000310355411440d00d0300e0280c0051015030303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 852840341 1250 852839091 852839093
    0x1e09060302011704081e0910020a08030f091908040510030207200d0c030f030807090e041502210a0b0406031112010605060c0303090d1d0d050c0d11030706020610030b04 74
    0x500f805244e1b006100001080d40000e00c030024840184021203084400301c0003403070b454004036a01c00041a00405007a003c002155005598404103039200c501d0304200c4d2204488043c0c200080b50b803060049400394000b150a00642c9003600414140d003045203001c42c1080d03029210010200b1080d444122219110140c1d41c800e600c0d4285101c0c0d5080c1c00c8a00c2004240da00d141103c80048400019400101c0300c4021804003031003496040c1c2207440c004003c800b03548440d1141542c2c80903109004400320390030840881510f0405000041402c00440c10407105c0c40c21860a100b5280d450000038800ea03c0c1400c00d0002410004116000500c180ca00b403c0c150500c500350790042100b41c12950b88680081020500e20714000019841080004195694900ca00004bc0d80382c0c60014000d910040e014034079180e0604200c0d03803002410307004000315030455543e200460250039288030f05444006146004240d10304003000750700b004114500c002d0403249800e001007030720703001d05d4003000b4903810f10200420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 852841591 1250 852840341 852840353
    0x5031207150b190608010306051b0301031e1a103204020d050126150c0d0b100903020405151f03060b0d0e0d020d1b03090e011e09060302011704 63
    0xa502c12110b5409501000d803104d0000d030603c242440110b803841d0034500041c110005401201e07501a5400c0744040c11642581c0c0c40e1041c183c004007045c00400c1c060b42c40500800c1c880c03264100130302855013090095041401c055051307046950080201070001120001c4502d1021001d5110101161800ca218090300c81c00074001c2e11600e00d182001504280000c00e0007211159114102d48010075a404c0904040b030030180c6441140a1540744040010006242c083c4c2c020010164507031b04101c00a1080c5000c8001103401c2640035001001600220091045041510807507412407010b01044c0b9900045000003406804008c14050b103100307000840307030059402a0040030107000c028402ca510340c441d0300f0300c00b0002c1c03230841000d00301031040d94143c0c05000d0000c10351820301c00180c3d84d80c0500b0001a8500100c004050300110704000c0110000030308400b0120245000c0c0030322464280380c80c00b82d4142810b084000750416a01a8980344c01000142c0e00075507078529100040e40000555581d03801d001d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 852842841 1250 852841591 852841609
    0x1107050402030a0617010606021b04140103030914030c030606010507021f08040c06080601090905100b03040609050d300e0303090c01112a03010605030f0705031207150b 74
    0x12500140003000b84034408030144c2001c8140c44c01c0032480ba6203100c0c00111329003038640d50b2290f1000750700000824a006004510aa222020b01810103e0070306048a07040e104a08264030a0300021117012003800f20b00c0c00a0340c5140ca60f2002c82c005e01ca50104e08000030389850020b419a81030000002c4c00750210f40b00c0030018400440141c8074000070780c0e100c440203000074004480c03c8132400d00012000c15594021681c060007400183e4071004290b043c843c0b180300030300c4090274111000508600c00541002420300a512803886400301007150700302450b001d4a8800114004411f1040c13071440090000040c090b017400c8079003591004074880e40040200c03001040704260010039030100204018100b00009442c5600712005c2ea100c098041407120500d81b00c54030411312245030386905c09018031040e1445880320b04000018000a0807035078800009141c014012041c0140d03400140e810405ca18040c07100d103018800401860385002c1d000d607a080c24200140031364001d0350345c0c0c440d1140d0494803034441c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 852844091 1250 852842841 852842849
    0x901050f030a080a02010c0905090903030604111e21010810090303090b2503060510030207021314040605090105070c03260c070b090d05070f05190b150f0f011107 71
    0xc0d0b40d6468031844000c6c0a4582e04003030301c0c00f007101103100080c0c3d41402d00610f889050164040c60071a140c4034200400392002c000da00110a005000c0a00000b030801c3c0001c03000c280314801d180d502d014104100e03500303d40451000d800065000010080c1503004100c0080701107200b903000035000d4042c6801c0e0001d0009581c0900400715207000c11110801d05025141c40700302118200d514081a90000c80980da2240a842d800c00c906010420041d0300a8010345003261004280d80052020300b5000341c1200d10701f02c441c81080e030001b418082400410b00c9210340103058540207009a180a500c098150803050b00f00070304000c03c400400c1210103103c1024400d0f40c46030003201d1075900780348191440c241c010301000d9400080020100302000701c0015902d2440030140ca60a092502c680c42d981100446010705640c01d008041c0e03500260404281c41200c00c0d48542c4507030009003451042010710840026800d80140c0007003540c88481e0b540c503845d00440400c00d2038080707901400320b6959410701d503071584 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 852845341 1250 852844091 852844103
    0x24080103080f0c010908070201020105060901061b02030708191a090304060c02040227270f090304080609010615020c0109170a1a06180f04060c0e0d06290901050f030a 73
    0x120401c2086c2203000385842c0307000764000d0010307841d510104000c0240c00c1c418540490004c10110084a144040e486491400101a14003280e03450b02c00314204003c00201d0b114200b10b5580841c100213aa100c400d001c52081518000c1c1c0b4a45030989035a203104d5030181c2c000b40700003030100104641e5a07804580111014500c682011414000c045a4240c0401c00d2603220741d2003084540f004500032000002274410418008a10780c039110802004c810001c2c010314840c0c0010440030804000400140f4050244180005181450840244241050b001d482e908541140441889503a4400e034030b9020380380d846c030142d40f050310410100380c074140025800400040356080070284411718500060f105003c01d03200382c5984d0280c5401841d060b4000c9900141c820b0086001c6000301b20a81d102c03980418039414070f20714085112001801091081c0000c840c0a40c03074a0b8145010300002d1801004814040d00001c111036a0b800042d9a03103905000d0540a89507040c1da10405942c100310640c40190804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 852846591 1250 852845341 852845351
    0xe041103030d06060815030a06021b0a0f06150e07030b0a230f04050915040f17310506030924010f0b0a0e040506131524080103080f0c01 60
    0x40618000740600380718082c0450110000034040401c60f107486c0c0c0741c0c003400501074a400e0406036102700094001840c5500000d0145904660480b001c0103020381c094010310144866a00c185040d206a4040c2d0410ba02118000c400c01c00000d804984a00d801016a003000b05070051304401203002d29040750310414490206a03074130412a008e01a1491a034001a035400300308000203424881910030503141c4a400d0303803114112a402c9040201c0083d0020300ca070061084c104010b8440001c600c80340c00020b80780720000241c842c280e058001000c0d8001e02d0130321202e180221460441c4003d2081c41c810140078040020004000d2401400f000804001d0040b081c2141100646210b200c80400d000b00402c00c60205030102c1c00a00003401d44140d040301e581d07280410400502808080c040c05000d85400c6092200c002c24946d405001e241202e090110000000c2da00d00ba844007103560170407076080355506c00c10080c410141c4d403181c40320b4192508011401c4d9a81c002da45025554402d82d100603805510b08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 852847841 1250 852846591 852846607
    0x1e030f060a061a071703040501060b070305190908100c11010609061d06150a03090204091101030b01050f07030e0a030f110405150f01030f09140d08100b040e04110303 73
    0x5640103000340d0f100d078848404460f00b60250480fa5200b84000a0a01081010715904900380302005542c42407082001269140c1d50306480b8910b500b1503a400c801003840840c6440940b5007008025201c5207907440d101180a1804e02101d4469025403485c0d140303541c070b404004140354080c01c4d1808445000800800c00103540c2c004410041105001c6c0c83e0b03c05e000d03c0700c1e244a00c154000402d004040041c03d8021b241c05003c15013489911111059051540341d003080d0000d695948103021074103005880ca240d0b4003500380300040880c0c4a20880c141070100a02088120703850782002d4a40c00c41d4141003000d402e102c900005241c01e41558401898880b1041c4000200004508080c4402000751818400340d2503108180b106002548805034000c00c0c00300e14001c5540c0f01e80c0200b02e0348130b030748000096050440e440d01a108808110051465031050642000b030543c009803450340108420421035055003020428040c40c0300d14031400c8681000c40010400f4004040025002450009c040760365031145 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 852849091 1250 852847841 852847861
    0xc03120117061b090f040e010c03050f0c1608070f0f0c21030e01141e13050d120305060a0b0703080603060603010e032a030a0507050d0507021e030f06 66
    0x56100046000d14030201d850082c1c3e07072881e001c4107a800400d581c2400e500c0000c0c401c2c820000074074140d00c11780b107485c1c1c0e60f401e082c28442d890803610360350340128141c540750000c0c210600c0058950741d4489010400c01e18034142c4c0015015603194000001540c03000345041a880c800040900070700a00050b543c0c540400621590f8001161030004500310500342071000845054214003018011882c2d2003040c0c03025600c1140d0109412544031081c50504004291844618201c0004212000000181e088400c5480c4603040700500c0c040f10380403aa903100307646051038124030108143c141600c481c00b01c1c1d082ea035071450300800b400c000380c031950300d420300c50500401e8031038156000c0b4001d005030800300303140f41018010b00c001074407210000c3d40383c000c084401d00440c001d0600c00002104e045124031000d40d105200038132014410f40e8405885004a0900500b0031004182580c10710004001090040e03c3e080b003214030001e5041c080505600813200424104800010241658041c40701041100d01d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 852850341 1250 852849091 852849119
    0x5010e1302130e0d18262b0e0a1409100b0307031e0b0a05190e0c07060e0d21020903070e07090915031e150e0d090803041a0c100902040e03070309030204020c031201 72
    0x45c0e5a190844400c0403000e00110101074000c0c02801850103401cad0515060049040d078001d01d000c20131500340341c2d0b91250f0200d95001601c6100000e6200c0c0542540f80c04003041d40300224903148030070001ca0704e104002911540b0a845240e000304610004134020604e590000001018951070481ca80e18210b1000640c039444018211901807a007603641c400300b980045c0750700c108281d40c0c4a41000c44103040310112500401c0044616468007080b410f1020703207003446408010003112984540f142400ea03000781400710190004d5207940d14000c800e25441d60b0040c810022281c12640e122220b10a005524198103501c030005049241020360072514282950310a058840e0104e06031600301c5c00c42e003000c90b0b207191700b4424864240d100b8041030214070703540f0901100c003c8941100c2e910b01201d141c152800c0180c81803182d1515650b643d14242941411f020340101c1110746c41c00b9528001c5603903030151045450f40401381c00b0b9640440d044003548800c001700c0700e80c030559805a500e2581e5a0380340c400b5a00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 852851591 1250 852850341 852850423
    0x20f12030f0a090b070302090d02060c07170d050a0f120e0a110d260405090106021b0a050310110f0c0c1305010e1302130e0d1826 57
    0x9107880c009407003403405103d0804030640c000505141c03900c0e4080124040d400151441c0c1d03205e0440000d03000169074840c010010f4620400280801c5441d04103032a8200300d11030b440c044241c004036406a511903103c4102c400c21509410880204030588004641d8500000700101c070301c929040b103440b400c103030002d660505540704128819160178444280203030308261000081000300440b19101c035034120190040d42c03c0b0300c1800b03428101551100000c50311002a8846170140c0c021840c0c801006070040800c420360350301510f02c51030310f6240a004c25502d08200d00743c46041c903a03504403d503000442c08215001c2c80b0741140b10a8031203809031401925242d485120b144140000300058542a41d03038081c5a040318600d04401d449035039410752020300510703135107000c9904c060800c1c0b5203a074400c030a00c01c42d401d000142c80281061400b00c580904403100102c1a020054850030040000000406103080401c06420b07180d440710f010301e400340b484c0c82c2801401024003d041d5411400c01b10820303100302c80d05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 852852841 1250 852851591 852851611
    0x5010209032505060f070b040803040605090d1205090c040f020a020c09010b030103241802030c0114042c07020312010b0a0807030b010c0b04032f0c01030c020f1203 72
    0x103540090301c03010b8582d2400c1001000034502040400007480c007a40034001c12803000c10528905200c564a4040518044130304035001440841440240034040c443d065101c02044001c102c0c400c1c0b0000040c021030411810301c00764980380d00000e07103001014096060341490181061004070604007600d0b01940000800300c00510507810030041c140703040900c0038101c2d91842d0250340740d6400c540310300e8031030407400c03000c114540c0c007401140244050718030610340d00d205806400441200948101800c0980190805040100d071f02c200404060654007210b0444074003221500c403481081700a01d050301c035a021804064952842007000054020000301003a003101c90880a8aa0300c40c414822a0300400703654800140c107110000d400d0318000d038072400d036145050420b249106540d03900d190307290740c08503411800180e80464100c22407004a580541180303461034140921802001da942c0e0340e01185044604040d110082620024001e105542c44102c806080d524540b40d0b0a0382401a60f0088d40d2140c1c138 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 852854091 1250 852852841 852852853
    0x50106060e0105030c040b1e033309060f0a030206070503030714040f0e040201030b040207060f0c0207120b13051b0f0d050c1203090a121101261e01030501020903 71
    0x381d07600c588100c9100d10b181d4182941014100310190a140d00b020404102c00c000d49401319032420015400355119000c8070b600c280d040c144c000081d05e0000e0038190400a040340c510391044860b078039010816031244003510001803421022001403e400010381c03002e50001e100082d48010301101000440c440c0966448002074000070644c0110706102c2c5100d0781501c141320702014802d40d0311001584c0d4100f801454041800c0c00e003200054103c0e802440b00302e45059035442d202030381d41241e0046070900d5200b80090300e00707640391081541141c4150417000303004155100020b81e5810301c0c6d54004400701c0d04002190010100010812810078190814512a5140100e0074000d860881d120b2042c00da80309002d040c10402d06014402c1641e840c4915040e503000500c0351800039101c146550000306018200440420b800303041c0351040140d030942e503504108440c3d808481104054801c403200c185e83c280540e900360344d511148102c84c8d4034511104001001c0c0d0000106201c1c0540107081240c030101c0540c2e00d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 852855341 1250 852854091 852854117
    0x40b031c032412120504030c0605030f010e13080318011d0609030f04051309060c0c11031204051e03191208090d18030b0408031801050c09090403021905010606 70
    0x7901890310038000d601d019002d91400040d800c02d0916201130850405c5814180c0700d5403013207090040c0e5000100001c001008201a42803500c0009004104450217842d090401000114103259200c0018240e40d03400004242300b101080c1c0e045208900c4c1000810100031441c103c107404100c4002c0c999003921610000c540c0c0700780d02000311038640e10b0001d100b51405140200b4040d801c0e001d40f041c4083c0316901c48180001c00c0d0913014072000100240e65071109810140751217001c0500001003180254010400c424043c80d003041200c0664004403030b4041d001e5801b00c200c9102060f1903010b181c0500500c84104581d0f49040354210790503100b104d41c60a1200035840807688044112050708642e40180b488070711890203251800381131040e50321718040c003070f8403038480750350300d038001c0c1c0301150b00d06800400c00902c50a54002440344514220080c8801d0a10402000441c00382d441001e1003000e103c030119007014020801185140030700c450341c5000b9401e40c2002030003000c541c072849011610300307d8245 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 852856591 1250 852855341 852855401
    0x16050714010207090902010203120a0f0c02070f0e061f050403033e0a05071202040605010810061b0203060a0504021e0d08030a02130f1a0711040b031c03 67
    0xc00d40c0342041e80200790092074038003250050300d900001a81580010407800007008450740c166842901c51030401300c0c80c851060000d508545c42a1088011500110018080c0303050180f41d91081300c00c88070000506864000006456184012804031021107075012011309a80003401342088034001e0b01e030842c21000f070b45c0d2502d4408481590920034680c0b468003a400c00c3d085190028441c0300d440040f5203541071203a0b1001d00d021342517001035100d210640c0e2034a0840c6842d0150b0350140000b864400d000f81480101c43c0299041c501400c03090000702884000194554880c41220035001011a060350801803e03100042c802900c060340100c6040741c064861100d00111100104006408280d00a00949410589800182100103520b40801c40b4041b841c103803039004400f03802e5050a04070090301e40b510040c249a200404403111120600c550f20103c3c0b88a800c04007400303802e56000c9011040300c000281002c04221000f404454121218204580c0c107510080c001010040001c8c0180c410203004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 852857841 1250 852856591 852856619
    0x2130612060e0c040213261e030f03010605072d230d080703062301180b0301090e010e0606100f1403010905070807080709050f010212160507 62
    0x400340044034400c80d9000120550702042200490405407404800303403e0000d002e0b607100c400c41d2000540713090303800d003c82084000625800d03409050011010340c0ca90aa4544405044142c443e1440c04a50081d402c5c0340180125840e00300701780400307540da6071505030260a036001a00207448010820300d07001c5600d140c10a08000328144030000c031000905075a241c00c01d41ca9070f6502d80c22081300503810320421010810196800ca50305480303a40d1540b07409100101240c405500c180b001c810541801d6004d480244210441001e0070b01c0c0c059610012003021012680a0703a00c0960030440000000a6241d0103a0010741585c01d228000d102c440a803c90030350783c0d0365041d18881c1e8010b00950b003256046001c1c4031110300300e001c14103003030311411502403100c03850350400da0210509036103070000c01c0340c0c13aa44804880d900c081d06003040241070422440040042c80c0030700070b890040100d0120000c3c1c60f8000c01000c00380308081418103940d00000d000d4a1034400d6a030b1002c9030144240d400c0814104a8040f50f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 852859091 1250 852857841 852857849
    0x110105070906091815080105010314010605100f0c05101b0804020f0603250f09170616020705060720060a1704020f030d030b0109050d051c0201020c030c0a021306 71
    0xf520205030b060905118502c00d0074912500450b6035804460100d07012900c83c58002c0001400001d00c540c5541044194400750120180ca00d915200c010302050f601c1c004482e4070071600d8586030421b0380300c1e540142c034001580200075040e841a10b11410340714006422607003082890111071400c154084500b940d8115040da8020740c44002941c06040ca420114051a409134203083c0f40c20006070101030902004a00320700c481d00281c0011010103101d904100e4040c010710203152201d0900c0004da80c0c0d40c2d210300014010440003040a040c00301068070801c24040a07101c02482151344076000c3c50282c000303410b0b400e44000e064400b24451681450910280c8031001115150325070004143c4000c07903003010000b0000ca034003c40700011200c042d1810040410884510703140068400c0f60100003416084055020900c11002030030141c002a6000c551320410410425560320b944400c8501030340079000f580f155071081e00c804940500e0031040002c4d5020400c1c000c1d94ac0b0303000b20b42d16500003c140c03461409 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 852860341 1250 852859091 852859097
    0x14040b04170f030606070c050d120e1f12020408070b0c0d0512040f150915050109051b1b1f050703091208060f130c080a0b01021e1903110105070906 65
    0x1c0004d00505016009105e198400ea281c0c25010340c840d400983da00010600c00d5482880d038004c9241c1940e0480c20264118100300c07080c0b0b044403031104250403031102c904980b07020848039010b510a00f920a4060b01e000d84001c200b550006621454803682980000e21885014810700941c614524016400c60352521ba030114003a0380c81d552170301d41e00b9521821007000c50308a079485004a901c003285200d00c2c0d120501c103012904822101d40703c201c040d0340040e0020866503240c0010b02400e250b08400655510001742d02c21038a41d8010103815200008406440a60307019140720310500d03407100400429030b0001002c003005280c9400c403085040342c0c103c01004140300b048051010085000714082c0e940308400500c030b02826400c1002140f001e010001800d08115190313140c2d6a003454200201a80c040038800c4100504408840003d54401800d240040328040440300919182c5051000c0c020307161820110b110111494030f00180500c2da800319070030865207000c1c003103030f4081d200c0c207480310803500c00355 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 852861591 1250 852860341 852860347
    0xc0901150c1b0609060216180902061b010c08160203072a3020060f160b010e0f0109020a05090d0f0b010518150414040b04170f 56
    0x401a6444a00d5540507580289582500001200d608200001400742070303403615451482c0000192a0070070008087e0720050003e1010702201040301207032040100c000b000815041c0c5c0c103002042c46407003008200200003040340c130403001e1728105401c00c99050003241d80c5d10b8416139408041003035a5140c3c01104005070030030410340e000300d0b111804202409000700c4a941a042e06030740d014811541903030212071a51340c001040b107015103541d15402c001110301102d0110f01d03101a50340078454510400c40910010311042d003d01d040d121300c01900c0d18803070341401207a82c0d6401141e00040154008004445005080d0300200d0b02c69031030104c50f4096110911114000d034240341280001c0d402c0740b01e2801c00c210040c0310b0503045a0340e18504820550040034240086105401d0400a0500507084240681c2d0750b40002c0d41200300c0303c102164050000001e02d81742c503051000090251841d40f031101c020540e0001808140301c9170030003d50141e441103000c20010784003200d041000d4052a084c401e003500080c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 852862841 1250 852861591 852861629
    0x306090f04112e0c03140c120c070305030a090806061e1002011803090305150c07030503070c0f050f06070f1b02030f01020307050a030f060e062e110c0901 68
    0x101e408440c1c8181c07180100050001644103441145801d03090343c1000a0150244200303041d0031054580c20f4a130005103003450007801c0c1080941c3d032510071400c8400d0040004100c1c11445090006801846c2c0c0003041d030b030b03a8102714040140725251501608441d4000c581c00306450b45803440081c804000c3c00704407000710105900410000c01c01d0003e802081d5501d0f074101044c04035105600c6402c49101c0d4541d068101d0650070450f140c12841d1104945014040092110000105c019030724066498036045540c0e42d100700084403058560000145141c004c44022020040d01040201080e2000d0b412207400c3d5450100c1100c005013100080800310303424109103601104860142e035521400541164000c00c2c1c80708480d0708a0780b00311030b454006600030070350310b1105615018640111010311802e00040381003041c415a041d001400700c601c80d090115214503101203945440c2aa094400290901e07841c100d080680180326840c520314441c06103458540340340c03402e1814141aa0b90320030700b007205c01c244 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 852864091 1250 852862841 852862849
    0x3c0c060f2001090b0109090501140c121b0a090302010e040501060e04200a0f090803070b0a0b01030906060806060316152109050c0a170615010c0501110306090f0411 72
    0x3030100110455500c803550f481c04103140b503003483d00908410340c00254100003420801e085031110280d10344068000070603c81040c41d18410380e4100b0300c05000042c110345070544c0c1c00b10035940b00c0c0c0d038509410720081400d1070241d40007090082100e0003a240c04207102800340c01c0000b10340c0240610004a05804108603d038109a44800d220560030540c070303009841d81c80c0980d00f0360341240e960603000503aa8421a184107a21100b0032004000c4000118103200103035417499a0041e0040c07007030000e039964080c8648140e201e604000c42058102d50100311381174a810590f0744a0008640d40da010340700300300140488040b010031400c2200c00d0381d03100c1e04000040940440d11141c42440710000030104140421001a161242425283c0b10750001c110f24602e1130148007030441d00c2d610440030102d240d1b100d2020b500d40840c0e030307a43c020303079034a60340e0000c034010001651146c0a004016210350303e0011400d0010750302000450003500300725102c5041c4d0f9103400616190f1507040360018a110360a0030a1031281c24 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 852865341 1250 852864091 852864137
    0x90310020f0405041503020a0e0403020d1d1801081b0f060a09030b010e060112021c110d02040f0906050613090c1e0201090201080709123c0c060f 64
    0x210301d4998030706580c44002605a0740e8131200c101601038039075010000c62602e9001034008080304c40c0e6600742c40c60b003510b019407589078070245003007403100f00000030100110301e504a5100510003050b2560b81c0307840340300725050140d090141c0c0c8154401d608003180ba10030031019000b14004000c01c80040c1070b90210510410382c06c40c1585c0014001403030030110004943d2417070103010304040d4500460720b103481360004010320b0600d00c507150400d1042041400516412031414950b04896001040c6418820901c201d10b10038106070a419901c04100030940d40d03510300305581143d1003018113000998a4604101d41486041800480d14188100030004141290841018005e56050103426604000a400d40c0501840700d0714005035581e400700011503070081c400d2a0003107094a4501c5c0e480d803e25159030740c100003100c0007400101d08103440f2450014020b4594003118038401c0e8600d5800360784880f08540c5001c0e080120f88140306140301041c480d00c51078a5150301601540c0c1c040c8400c00052448031000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 852866591 1250 852865341 852865357
    0x18070f090e030c07080d020d0c030e04090c0308271903032d05071209180f0f020c060402090a09150902060d0c0203030109111e0c07150f030606020309031002 69
    0xb010a0002c41c8141400340103203802850080050303c1c071070001180007030070900811481b009000c881246440842c1d88884400c2c58103106550000e800940f5041c80b004d802a190b000400c0310300c000810000444113107690f056003016841644400240b6017040203044404c40d481400d010780724401c01c00119100e82c2030b8040650320300c4003503c0c80480d403000c1b0390034511580d02e40c1004140002943c20070860640803410340b001e013a04d0900020f9041c041034403101101c4e04407140aa94541d58001d080d4503096101080788001d0080c00c541d0760360003d1086454200480d0203034814080540020039045590003803107113041d4052071001c0013400c1000c400004040407002aa0011014019403c0280740c0d0300c50703020000312640046440b5032506d0400b1066607440d841c201400c0d42d00384080100216104d0b2407600055807800310710703218504d40c2c80c1d030361a0034220b03400840d541f280440001c00d4250024900e50150401c1d950600c58161243c205036035903c6082030b00c94050f030052024074102841c96010300822 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 852867841 1250 852866591 852866593
    0x4141603020f0d2301020a080109021e030c120f06040605031203040219090518010c0207060203090904021801060503160503070e0d030201110d051909020d0803060d020604090518070f090e 82
    0x340c400501398085032100c4032140010b03940022510b1f030b07441c2c004246900500307803494117614007000390304a40c600d2080d030340452810040100c0071500a0f04c3c041c044d1010b007100d031480c01001c5d183c14000260540c40030ba0b4507d002e2031034081d02145605010800c0b4490014140005c0c4c5035032140e0382880005c0801d907042e40c401104008000c6240b40700ca0049a01400110841e211440756400b01e0702d017152034440400c1e0955000d10000c1080c0b40d0003009588426504851002140d230392400894441603000c00002a010500700c000b18866030008081e40c0980203111040c005514100410748062106a4021010a406e0f4103110214070f080d0601c12030540c40381c0b0000c6860503110b421801c85400102d101c4440f2501d82040003034020200d48003411800c0000e00900c508030030354000c6a1043e4103814050300d0390000200141145c2c07102580c030060107501a10880e6216680c101c0a001040261440c0003074810a60540000ca42c000400c5025a410000d41030043c1d4a01058900140703011020a107803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 852869091 1250 852867841 852867863
    0x60608010b1e0f0a0201111e25030206010602010c03050c120a1103100611010903140a0207050d12030e0109020f04180c0e040c09050910091a04141603020f0d 69
    0x7248002c02030020514003159040c0c45804419001e401d403100400881c0e44008280a01c0600b0b43c07035014198135011941c41c0050784c400c1c113040c00c203003d4104203071a45105401c610105003010350020703400d4101c4520f58020800041400b8045068400940d80d410426000780b041680d1056290700c0c03070b17400c5900101c0015440c100b0355101c24039500700f15840907140208000400440d500411030100c0404100d0080240780025600034015281c001418659088007103919040d240c000c00c0050003a0074010615034001702d01d49070940b102c0e420798041c00c00103801e146407100074250501a030302d91544d0081540d10710001c004107020007407401510344408a44403903502e0021900350240f8001801d4001d0a2180524282c1400c0308a54401e9204450b0b00340f5100800444100c0456010b030102c14030070001c6925070f80e500f003800f00c202841e001d0302ca0200c042001e00040020b011848543c00301e811341550780102141c0003228002c10103102c0130313401041200c5c0300780181c41d00700c82d07100c0d5240c410030420312 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 852870341 1250 852869091 852869137
    0x618010c021503070f080c040e0720010614120a02090c1308030408060702160e060111030c010614040c140d090f060506030106050405010b072d080d0f060608010b 71
    0xa1003201c40300c500d54200e1400424003135000e03400240b404900c956401c042c09a07082c01607601140f0320541c030500c0440b18900001c900c1240c8213202080c0c0341d00700b03a4860a00c01c02c1c3c600040b8000d0486208040149292309002103007810043d0b203090541c45e0f8400508007000d1103409121240c000200801d0480c042040303a0703030f0169101c1c0c41100180c00030300000c5480f13606100d41c041c5051000750101e001e640c401c0500403110001082d2107400e030303924015100056120b50006031070500f901a1007080c640004070b10f07130103c4201540a00f044990501d0b100034203040d400103210171161408031080010b100da280c41c224a2645d10000c0c0700590b10040c1c000340360001a140c1c03c402c03015941d03040307030303402d4980c81031004503c1d0900030403015007001c50381080b0b00d514090392040544542200140107007145540103100880d45507408469904112010000b031503c0d150500c1180d200417400c002c00d5203003030006403071009075200e103806840c030a0701c82014690a00d01e002e4199080b8052010300d001c03244504079 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 852871591 1250 852870341 852870349
    0x405100c091509030209060405190b0d020604091407030501062c121501080105070801031112060112021906050714030903010903030b040c080f06010e01020c0d0308011a090618010c02 80
    0x4088a82c080c0d840405031801d41c410000c0040c009840d0b00e201e02c0c02c06e000c0c000602e10209540c2c1000340044000145182d00303101141c4090300389080030b0b60040d808a4001112840c541020b1641200c0701e20f184c0f800d43e02d0b400c0a9007125000c0c02907400107500c1c03641c0e000c0340c159451904051603440407000b00d045181c04000074901d444000c05042d0540000c0c480204056588042a0151034000002c0c003241c40c000c03600514007a0144006480840c00541c401c41c20f44402c0c510042840802054414560b15840320003210468884100d00440d01c06061040001051600c0c101707903890b0355a080d01e002d55507150801d02d88a184104042400104031240e40c540d024458403907080d10949000c2024004501000115480e403055601071221030b40c200085e0b0f13202c296003280e006001f400c0180050202d000105e1401305d00c0301c42c10750007541c2d0641c0c81c0103041d00003042780c0c100d81039030704040c00c80c02d68010f180a0130700400c03c0c180c0d00030800b030180054044d074103440c0714028003043c501454020000e030002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 852872841 1250 852871591 852871619
    0x50906240d05010b100201060b09010e0d0506040809030c18060d021306090b150901090512010906050108151006020607050f0903160303030c031a13020f0a050a080f0405100c09 77
    0x8482c141c0d0b440150321070303034207203c0c0070079018031200e00080140c035240c070b07a1031912445140e0310b03141003201d10b4030480c407a503440074001071500d170b0040101c808500e001c2c501900140e1120100f10300c0b92144040c07003c56450b03e00f8003052410811070b81c0079490b4036881c0134030490401c6014100c0e4440600c000c001c29120302c2e442000300414602e07101041d108403040c18040744c00503003c0e0f070194402c4200100301443e42c01c40310281c2269829502882c881500c2d4030304070300410180310018400d40c10800000359a03600042d84015005041e060400a900c0d1410742d110b401042e489042e0268020b8070000350301502900103000743d4042a9540c504d000d50b100d0003c0d0400c50030300c15000b0b01c0b000d006010700515a05200314140b844d084d050404c50b07448824034120381c1c0d410448045204d8000b40c2c6082e002808550169150300c0b06035081c1c96210600303000090482e4001c2d80e40200001c182000107124000056680e40c0227035080b8001e003100d81d98a5403020f000d407094449038402e1125110000070191408800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 852874091 1250 852872841 852872843
    0x408100b1516030824010e03070803070f17031e040309270c0905030a0f050a0602121603020f0f0c07171e060c04151202030406060e0a050906240d 64
    0xa0700b402041e145005802500c0242400b414564981075004209a1000701345012840900301711403680180e000003841c0c07803101d4100540070700005c1010030030410504840e11401d4454040030204d844410070004641c00202c415040301018030f581d1241240b0003583c1150403a010303103465500135458031403c030b8449484c004c5455000300c00400c0d4030a8020648640c0d0b144101a2500e10001460540045e984460f4503074082c1024140d6468141042020400d0103d0315501040c255180c1181c00c030303001c10400003113035041030710b0380c12000f142c0780c640c8648211442d500c5030b0106681030170010000084640c01c2070500c07030201d1088041c04070b15101e40f84120441d40c400400105034501d0071499901400c0354803c1204900c0d845081030040d81c7c030074081501d06036100d140e02d46910503040602100c0102a140400300300f2440003041c4070510106420134002d1311300d03d0781c6034040380e190201914110f031001c1380c40310010340000022880320351604240720380344444025000c064120b440700041c004a24454 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 852875341 1250 852874091 852874117
    0x80c06070c05010f0e0d210c1e020a050303010e040212061503070e063318090f130b072d030b063c07060b01090b0408100b15 55
    0x308403002c201090280f800500c0510300306001c41c43c0001e15a95aa00a01701c0c001d041c86021340211211407078a40300302c60000d103050700510425081c1c02010302008035103c00c1301d18400e000f040382c00c000c2c1e0000524100c407c0d8000029403840e8a45544a50984030141089a00214614207021106001c1040b0743c01030401c401c401500c61080d40405240418680c06a1a81c640c42c81c00c000380f030b68414004100341d520400c01c510002502c518881c14001c809181d41480f2200070030100302c6860b0645410500280030707030b032506240d1240310080d40400340444e0541c10050f02d00030070100141d500109242c03c10028102612030081c80340342f003a4841c050001000c2c503010124000c04149505005286203154160750291501150b042e800ca40000800c0701c80b000035010001e01031015100c54210030b401041c001d203854075414940b80050207071985000850004058002c042030741c80d080011182194000c3d401003960907992800c0ca00030700350384200316500000c10200f4143c901c604000030042018015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 852876591 1250 852875341 852875357
    0x30c0f0d241203080105060c010605100503091513020d020a0b04091e05010303050304110f12010213080c0f01030e120c03040e0a1404030315030c0f090b0f030d0c080c0607 75
    0x151030540c0c040d0590b40815021810300302500046a00000c0490556500340c0300242c2d42d030b190041c024050009584840c2e04070701000c0c40d41d51b02e141c0c0300c000746000b09580350655030700c414049034254602c50143c0d508034869004411650051505c9071900240300c4c0b025081d41441640c8400c8005c190b0420380c8491251500c80d50b84100107802400e040d0f080c00c44c001020003540d410350714001d14900000300000c000b5560048241c000c0d6541607080c100013000140803074240742d84099494041e4003e500703542108401d610001c2900e103c003264102c5c0c003610180040800c0948040114060008a100501c407030188841e680203580c02c0790004d0846421031801107503503230f21701ba2507018541e4006001804072840c0c600e0522140300d00f6400c040c2c00a41628010400c7c01c04e940420342800c00130784c4001c10005803154005841c1c0c807192041c80494030300000c2040040305043c01e00c01081c01c25030000354150041c124102a0900500c5840b420302d000da068103013000d158511840c41c160060b18101c3c0801d0040d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 852877697 1106 852876591 852876641
    0x1f0b070c0e0a1b0f180522020d1a010f1404152d1701030804032616062f09040e010603120f1103030c0f0d 47
    0x1644503c1d00990322803030081e26020300c0b104184040707500007030700d580b096011010b640c040700c9005d0640074101e20b4010b5a0358900d5403404d8140c0140340d09002159010f80f162207282100c4440c41d825080e100e52070390006d041d045e81083e00c00c04100009401541140307880003a50f0031240300f24604031454100d42d0b42541c90f56103001c00701214882d240255034078943e0550912590141946602c8840450a6425500b03100b0074000034200c010300300401c00000350307001d4807009070350030750542640b45910364400b402c00b0741c4c03042c008201c0700e40b090305010080c09007030320035126203c4500e078909083e02c0f905c3c181c1c103a8108a600c4210024040400c584445d03440700c1c1c001844030000c180003001915181c2ca440000d00010080e51780000b622422004085070284494008a1054900941c01c558603450481561740c44104040003c4005201001340e224041c09109120300c18410424034481c48 = true := by decide +kernel

theorem cover : BRFrame.Cov 852697841 852877697 := by
  have h0 := BRFrame.cov_init 852697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 852697841 ≤ n) (h2 : n < 852877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
