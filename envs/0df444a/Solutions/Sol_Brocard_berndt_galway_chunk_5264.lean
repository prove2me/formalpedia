-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5264
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:17:16.836986+00:00
-- url     : https://prove2.me/submissions/1375d551-5d79-41db-95f9-8fd06c861cef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 946582733 ≤ n < 946762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 946583983 1250 946582733 946582753
    0x70f09021c050703090206030907031b05090406050c210f07020606240910180602071202060d111306030510030c05010309020316080307020301050105060a091e0306061412 75
    0x80d1a2003002000c40380901d0b9690000307540c0e1072181e48110030099009280c0c941e02c3c113058042c40e58801941c04269550400405050800301c0d80c8101041200d0014003034040391b030384075102c00d8000c084c01403e1242c960400c100214042e06000320309115403020b11100c40c0c65043c040d8214440701001421001503512203418407103a95203441c000240240b10050014007003031f040400846601401d000f0640000b049103001d14402d402030700181820b0015505a030b070f40380d920741040b641c8800c244100b1400c0200c0051081c05402d10038010303c54004400301c0400c8141d603100c0c40ca1495440440d2101304c50702d100c5414400c840c0e02d80034840d042140b90049103c07071401d58072030f00446040740c4034582c1450350342c1c1d040d00d04544050080c11000c024080030b2039a2540c0e01c24100380c4a50110380220721035441c0000110f11482d090f4150b90031000103945403000700b0f0800454800704990010181c8600b14070220010000d100d50003030340050407040060780c3d0f244031141e0074020402e00d040511201c0703030860310000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 946585233 1250 946583983 946584007
    0x8010c0219020d0f06060801020426010515040f09140a021e06030c0703030e070602031e040b0f0f1210090506010f080c0a0e0406090504030212160f080912070f0902 72
    0x580c3d42d1039002101600d21542c149828401450954000f00300c950020900103004e590040a2010165028041f0b07042100c0801039a8200c0350204c0300450210640c0c9000100740c101507118400d00b0030380c8903000a41483c01d0b29000805414000030350a290b004045480441c00c280400340385007412400801c03085000c9000080d100c0c0401440307000e1590000c1003207800c0c14841e40000b00e0081614094401d00c1d51682d0009440f40e00c003824406010007050120000c0031a601c0458040710003115a05d0300385002c044410341580d00020b000c0006150910030102090f16002d41e1500420b007440d04c681450303140060b01703801d03280e00070a054107215085034000307020341d080056154044012184990b5441880d48140c4000609900d1144c00ca89840c8022400d6136040c0d0005024501030303001c40d481c03400b464540c290030780304080340540580000304064000688401c150030450f441136080c1801c01d041000400d88104c0310321200003450b801184200441e00302e0044010281c00280401d5142c082441c0300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 946586483 1250 946585233 946585249
    0xf0403290f0c210703150609030602091f09050906060a0f121b0801030b09070f1a1e0a0f020c010e0d020607121101180b0601050a11010608010c021902 66
    0x284a00c0040440010b140104110704032240b0711001401004500305104810b4441d8600315407460220b0b1400402248031480125150102d52940c0c1c0c3d21540c0b81e08594404c40070303401280815070050402064500a14040410300e40c1d1481c1c9550b0707504402d49042d0411082e404042d00007409000c1c02c01802c078240307900c100c5451768603c1509003107801e090940403041c024859220306004924004030482e64060303001784c03481d040742d0040c3e2038182e0640301c142209171140382921a00200c00040c40e000c00502014002503110740c001342884a080c00400543c020403815a000310f2100c00900041820032540c01441c680004daa040c80113051200400b40041c02071031034000c065104e41084d42054045640b101c049403c102d60080800e4201c06107040040c003126500c4074200d030594201280702140300e40c4a411996400d40080411029445007030054600ea407007281c01608100000c0c0d05e07c01d80c9a400d00442e402172086038000103130294070303560003420000020560540c0c25050011400940c1d25811 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 946587733 1250 946586483 946586491
    0x1821030a0509070302060c0d0e090c07151404080714150a020711030312091908070312020d1b0207060306030807080306060c101406011107140d05030f040329 69
    0x400044584401090383c0c50000309600013540608001411480c444002c5019050321245888108103070040000b04100d6250455061051000510403000440c032031070745900c02c02c90300c11000036200c031031a84484c240c1e201c2220155210600007030110304002c2c0134a0300045200612015145030382d807aa85e41210350038050034858403240c011a5000c24880d941040d0110300c01c0040840365038904007040e21100c140704a511031a14010f0f060f015000710001740c00b40b01c4e01030f8014084d40c900306041e80c0644164008002070704000c2d80c01d0140368502d40091003084010000f2080000700080c00c070000074030300103554210300105400c0100c01c00c0040c031a6420303500d01650060110351030340e96200125660b8040c4060741d101e188194403890a8843c62503220a0408425901d06401eaa0794800191601d2401051482207076120700820089852000030f0101640c0c0300030045201d07916661105031440d086100050160720300000e042080222031041860820140c8444030a107a00c038251440c64600c1c010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 946588983 1250 946587733 946587751
    0x2114010303030e010b130501050a0b0307050304081e030901140a060b09040504081c0f06090912080408090a140307050a0e071b060207060b04050c0c0703170d05182103 73
    0x49002903c2a00070742241680c00000303060420041041d900303a1015050a1181030700852050001140d004665000c0340e02c11450794541901c0c603101c1d603032071034859805858005103a03000059403a91011130000214050480d41c4004105408100a48410b03104064003807034010f03107000305c00c010a1b1140400d4468541084400050710380c1c550905007828403a04500240481c900c8021019000711540719040c020b0f01d80c902080400d031607a01050449407451005480c01c0e040b40c50741407032648116256640184540c1800341041412004554a0400354212001030f140078031000c076a50400700a91030050000300c8801907110301e080414104080003030540c400b000501d001c1c00e080500c042060310603256020301e0455840180d41030150040014903034191095050a0204c2d8502c1407813400d40c0c5400c91400c1c090858117207142d8072a4080482160000005c801c14044002d6081043c4121031242d440101000e500119103030300c890900546200d007c100e03040002c62070245403454800d42c0d622658117 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 946590233 1250 946588983 946588991
    0x1306150503101d01020c0a0b1b0322080c0102040603141b0c190f0605130804050609190314070603060e0c0a3b0a0308030402010315090606211401030303 67
    0x41c1c140c03c40f60b4007240503034160f940c00040d003041c040c080080d42c1c4141501982011407952588084164424100f224600f0340078420700100b00d884400340314078910008a51428510941c881d07071001c500380c1011214003d6079601050402504c1d8142c01003580e543e01c5a8410102d40c9001d01e019034100308a64021903030f1040215060908010400602c0d04200a000001c001d003141032a011440924240781140e52030300b4500031a03c030241d08400e012440da03120183c98107107070521003440344d581c20048500360b11502400403040c1840c3c900415501850040101103603e40ca1148120314144143d4405810145008820043d03402080c12081d0130003906111603a8810f040c0b030040742d42c010117464803d11124441c40b13100100031103403182801e40d10020402e050300c071080410454001d05600c0003509a00041000500540c4240d01030410041d020075035001d0b0030346403009001101d03099046074020403044086940740c0c110b81c1c040c898501030310307150622a01b0341d9140710607426681072000034141a21 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 946591483 1250 946590233 946590251
    0x20d0e0a201915030b040213090b010c02130c0305070503040b1b040b03070f1404050303041806172a010e09060303040812030615040312081509130615050310 69
    0x540c038001d1200b000c088034007001161100c15070182500552224004a49805071500b05030606d4000d0b150a402e0011006410314a40482c40c0080c100500601e030400814402d1400183d9400c4070702035080392078400c0000d90801d00e0300007070212070380070749114248001481000001905260019400b2440042e035240441c44464640c240e400780d0703080085d80c09404001c018400b03610140c1c03900d0340d0701595141459650f40044e4128144550b014094260300200030503c8a0400740001480b101c80c60310740020702d10703913450300c0d000c115000d010311201541191411120400e00700c0141300100414850301e05400c0c0c10344001a01e02c7c80500344103801040383c000080d203107a40c140300340d90050081200784d03140070f20302d2a80c105180e032044803440e110382042c0798480d85501203842558150303644203400501c2c56120345000d5803490002040005528425080708406e83c81304441d01d0b0040c4540d04860318012007500e004c3c130503105c140c0b685440d2000700700020082c0f0740e070010f000075203209400e1000607040c4c0c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 946592733 1250 946591483 946591489
    0x52802280e070e101103040e190606110d0e0f0111100615021207030e0d08090402120105040b040e030d0e0f2e050609060f060706050a020d0e0a20 64
    0x540e6070100215001000810100c141c20059003042a8003c42e1000c40243e02000d0a42d80301c0c03520820b080d03a560080c00f09200481000e49602e802c12040140020203035001c2c0507440543d09203400000008564441301c0c3c40d011410806000c03071000a0501240141e0010f0104070385480000e046070421417804864401201c040c07081c000031904440c024045203454600510040250001880051288200ca00102c403045401e58803001c0e850350352801c1c8984100c08008a074601c0e030a040d24486420804d589003680e9610060595035107210300b1184560bd00420070080b83c051001c0c0b207010781e00b000747e84511400c2c00320803203142d000c2c0c2d000c000030301900c61f0345110f16204603580c086460744109060801d5a0344510b91f10407006000022404406002985402c280d800599446030030902090200c2d04c0b0f450900003e405080740540540c0c1064020385441d0309640d0195008002144d0008019201c1c680c0c6014012094038030f0402000e05038210740c1c40c44111800144c10070214250b5014034640d81ea = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 946593983 1250 946592733 946592809
    0x30a0807020f0d0b061c0c090b12010203090c0f0409030f080c0405180901112107050c010c1110060b03010b0706060509070e04391b052802 61
    0x4000c3c10b440541003640c60708040d004000e0703074007500c6110301e10024201c02d1041041d26442c540d011040b45041842e16560501401c120501103030322800890789a942201c0900c00346211b90284401000c180e402d1600b8014010003000086000b1810320000c0b001180e007104a1241034025440d1442d0281c0c0c1d00c417005c1074540600c2e080547d001c104195821002d225001e038560284501030700070040c440d580706035030381e6a120301d052551038881244070107504110140b000c0c0398000f03210709020313281012001e0144e08650b042c21984002c1450303545581c0030100200012a48615194020415141000788c2c0004601051003443e4040e403001a0780c03030411415400c0240100300140140d03443d0301b003076440a400b6581d41115a40124981005400d078440001450440128580c0400c0400100010102044d080104000040c0800704640701c100d506500d080900d040c1c082c1300030b080c040c00c80c2d142500001440301040049811a0104400503039a2108503100201c00c20205404000580605408030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 946595233 1250 946593983 946594009
    0x8010e04141f050a0617061603111210151704052104090b040b0a0902090a050a1203091401021207030c0213050105270c0d110712020d0c02030a080702 66
    0x602e001d81440d0000840f50802030140628060030701205490301920010380d224840380206a600840c0412a40d2200d442202260080e03442c0100300705401c0c4043c400264000f02c0c083c4103140c905010007500090961190000d00900d00c5102c22000c480c50300145903502d4006100d200a01040c0031a082110401420107048400200b01c1e4580076141416040d07a00184207100d100c504018041007907286c14410b40402020003841c0e56001814558414000e400070f8000c103400000c00507001c692a03980b46a440010500484001880c80d200c1c58003d001b14541d0784414109140f0882589140c2e80106182c5501406041803940b9001b49040894410301031308030194210901c4003006400c58003540005050750070a503004855210888413803024420341002946c803140300320002c02c004100c07a41c01811450390401000c5124121891803c421394031058045540d42228188194580d40601103d440d405482c20b0030712141c00d00b03801081e124034071040f00030802900001d08200715a81d2900325444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 946596483 1250 946595233 946595263
    0x4110a0f09031403030118060e070e190e010815130f03051c05010f0e041a10051807020c090f0109020703030e19030e10090e0403020f121908010e0414 66
    0x1e042d20f11541142c80394400e00410440c180d0305401410000c1c82ca010303c50440383c40001040480d65516001c84031040100701103036004800386402d071038a40403da01040502480c03032900c540d035450010601d00e0150308030440e81e5901d01450800c100d680c0300c80c40015000341c10a10190710388545142c200d41c9442030740e41c00d140401060240201280980e40b20606035804210314000882e100c01d0b50082c10141102c0c0242a48468602c000514110030ba00c29008600210071040003501c0360005240c50800c104075107501c100000030031103030340c1e810000801d0b1110140c4084d005414500000700c0040c00500843e20320540005010301058030176800914a08036405c2604d0801e504404074105405002d00305400080041107480d03014a8518035000f0080440d44455505500d400d24458041e50000d005405601034550345140301801801010f0240d42000d01d69a6120407210324003d280c03210060038000c1000c0e05005003e4680006001500241c200c2644d00c076415040900314900300b160001031070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 946597733 1250 946596483 946596503
    0x102070f060e0d030e0d140d0c1d0d0c03200a0b0304030809010b0d02040e0a02030a030504031a160e03251406090f1201020f031303080604110a0f0903 66
    0x1003072180e240d20040c005001e800076100d0a010340403046050300c002070103003e815041341d0321081c01c03d4021040340310080c03039004580342807120300c4114008a0b00c407800004081100e0a0b94072000d0020307a0103e04071084100c401c00f42403441501c4011032070143d404002c2040010342d545101c0314620031031701380e000f01d402800103580c141c4400640c03c0980007036600300c0202c0c02900105859050600865074554800342c41007160085036000c0201402400ba07081465010b2441c83c0409a1802e121049050740644c0740d46d50740754a03520b000312400005c48524401d050800d41445804441542c00400c10032451070103031074811340400084c0c02c16000e45110480030201d880565524110019502c00301d510b03a2a28230301c0326502005006541c800c400e0000c0e030140100d041d410303440c980702200401c0c40c80d9900c0018100050400c8614040d441910146641d8000d201e81d10100b650050340c556100600707880c00d000012170b5413100c054031700404c8078001c02d01200080b40202035100d03861a500842c0c1040070b4203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 946598983 1250 946597733 946597763
    0xb1f0f031103010b030a0b060f0a031505160302130b09062116030e030d2310030611070c05040c05120406020d27030e01031803020601090614130e010207 67
    0x2001c420101c54074501950900403542c07243c0c500852800c0c03042d500800c00301e9169643c0340c200000c9100b9246001d600404281c004400320340d030300840c03940f480921500000c240c20704100b0700340c001c403030950303958101740c01000030115840084041c40106c64084600648a0f010b54001842ea030040c507002004842010003035900e182c2c0550348141c041d4501c5400328a42030740e00d030021010743d01e144400c40303410350041104580e003d402d6800201c40f410000c2c2201900c41d00c01101c50446c0d507080c0e50150018211900510a000c154403401e28204448805240340814568030302d06441c4c4c01344201441103941c0c01200300b02d0b6000d14121100c05003205200b161920382480d00b000250040071044034050b160008415207010000d40209000246041c44981c001c003980c0c003141c0118480055034100360b00e844842c540f002081c030389403031814407a0300074008940c1810039290440385650310641502c5a860b14454090b01c401264100c820700c920004107083c0755441240340a84110754008004507544c540d11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 946600233 1250 946598983 946598993
    0x7330309081b150901020a0207170109050d0203280f0f0e041e140402030a0f060603020907020f061f03021c230706020102210640090b1f0f03 62
    0xa0900048114480c0703800d40313650001900300c0c02422000070169104100c14070101144031700165241d10101d0012400174426662682821552111440568000f00d18041d00b440d070000307241000c00c000b0f014550300c6918841c004100118502c0250144402c5060880300d941c45140c01820808000c3d0042c04000342944840c00040d00300c140480046140c103907190307419842c80c000540680c0d001002080180001e80721000050311981d030480b0200d958401c0000141c850916051041c0007540282210318440c4400782c0c1080385c001c0100f0043c1601100d90100d410401c03400310140d03034041e10f640240003801c80b0311085484d064280500714a40c680d042000c0d8480159070b02d0032006903c801e480005590f41010b03402d0303000c4c1500d480140c1490a110103840d03441c1584007035000034014011341341c070801c80e4003c03c4090794151f13102d0105106100356038148000ca00d40c0031422406400c1c00c002007000c0381c888d80e20701500500412126940b1810318008403001c101041c000e031806504c0065441e41c0d82c60301e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 946601483 1250 946600233 946600243
    0x1270305060123060304080307110309090f04230d03020c01020405090108030c1b01090e0402011b05011a09040b3909040507030218010f050c0f07330309081b 69
    0xf01880c2c5881e4510307522801c0c94800c1d01d000715488150395007142c4880100b03030f90000c1e0b07000c4c4290151000f800307041c2c8565035030802c0c0ca0160314a400b001c00301e42040c0c00e00c002c884c071540c0100ca140e15444014883e29940001d80c41800b00164900140c603980311301c0020b406807095603c500d5100031408004145000084010107001101c1c00c03c076034100005240e0740071901c010301011404034201c440100009402038001c2a4000c0c41407401003030440654100e000148074807081920349a40d110503881c051030b81c079030841140358403c40b5900c1003803815544000d40440028017480c00203440110110101901c110b01100c0b1a0442901d502e0000744148a824103400507071405203c0d90030700f004075130b90900038800c4a02100305c901606d0000c6041d4401507492455090780503003001010800300300042020b00100314071200800241c01031304e28211480314440350486840905880800e804205040340160001f020034613410003059401050030000b501e80104030000400007403810803d50907050210f5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 946602733 1250 946601483 946601519
    0xc0c0e010f0e011a1b0d1101060501032901020c090103200904030c0201030915110408070b0a05181c030e010801080118080f040b04080307060e0c012703050601 70
    0x75549aa681d80000c00400002c0c0302d0540c10811101c0b043e101041c8210040112841c40d140c503a415002c0390704500d1038184200796010026458139080c16940d10207000d584000e03c024a030603c46141c407600c0346160455010071100101c0200340e80f00000764028008540a41c02c002c0c00a5200c0d0f030359081858060100382840c80e0b524840c42c42440d01c900e09986000e00035171f016510515403821030350066004020310307172040d600d001ca41e8400401c0031055001d41c05022840e010070395191850914030134a400d20a4214114025050280c1100c071a40002940c50515a11604a07040381c500408030b0744070b070b0300351b000340c40c1011600c20352805064100480000024080e078460480341e0b130b51803107203088410001200e5143e41185c2410750104040d8805072482d217400da5002c42c07a080d9908441c50903039010341c0c8051179075040440e8890504c603c51207881c0b88101040081d11401c681030000901928180c6403d04c0700b212180d00c086901a0024446009140d000040352043e5844031100b2a03580c004d59 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 946603983 1250 946602733 946602749
    0x2010c05040509130524101202011110021b010b06181005040b0a0306031140020d0b210a02010c060b10021c1106180f0607081801140109020a0c0c0e01 66
    0x100105c2d20340822044010200c0e88e0001c04411518096401125420100c400081c403d20ad0410180543c00d140d10062410001c10082c020900084921003800d4a0101c06080d103d25030a101400b0304028103221030000503000c07a00c1108107040c40b1030668450250360489520030901040a10881390941d0042c000d0324001d144550b0075044030810805015808860000031445e20703601400343d8001080b42c10066000b91b1501c1e01150019820141241c000d0095680c03001d4036540500305074113003080310311005500d244481c0303074500d54151890744c0c4521040000b410040482d00754401d0100e41d521540201c60300403c0c5000e01140f40600941d214103000c0103050200c1c08081644915000704510a41080658050041580c0e0261a4480381d0442919120107002e21074907072076152014001c10388075020300d1f11410242d0428810303890080700c0070702003030000e03038500a407550145682c444c0142c11034111030310159aa880040c8215030500603950010040da03078495010900c040961030703030741c11b8039145 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 946605233 1250 946603983 946604053
    0x4180f03051209030c0a20030f150601020d09150c0219050a06020c01020a1211070605040603050c0903060406050402151308060907061704170a030e0c0102010c050405091305 76
    0xf4031405901e0744100f500d406541d500c01890350f40003a640300241500c03062596103480c11407040101080c08d1505000d015001600519202c001c2c2e100d00f0031400790020001c0c80280742000c44160043d054010328040d424142c010080ac0c00303052480394804001040d4003400e282c0c010b50510050015120342805080e02c41c0c034694001081d0700f40b00241035214000140d00402e10f20803d43c48003120b014003191070604000d0f00c03075900c5078200d20410201001f8927980c0e84103580c032031421000500304c0754050094520040c08201040c3c403a40c002410135042074209100080c40d031103d20000e034040b44e040d40407070b40c00032003c1020f0340310500d9240300004071031540703060b41c0659a4440c14552100d5003409841e011507130001c0a8118800c0d0307c451300354064030800d503280e2095809004900701d604038600d003000003601d400a040442d50140010109240280020700c5a41c1c01d014000d002e6005074001c0d180a1144a00001c030403c4042e02ca2040687e0010191100e910b1113400c0304404500900e0031070045044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 946606483 1250 946605233 946605241
    0x1f15030b06030709031e12020609160e180c100c0201030b09090d0507080c06010306051609030c050d02010302120c04031b031e030e030d0e031b0d0204180f030512 71
    0x1e8012684035444a6075044d402500310b684050106540d800003c184003000d0003c80c000800015500c907851005400404213441d002c40b585113403640840c06900d6012514004001403000c10194075000303e241078061800800d0000320600c0c00088100309640b280c01c0c9110302d403a20750400c0809100038000c0e079003880040031780c0c8148510580c040d21030034120b90003003060401ea02d1044008c2e14803075104d2408603181585420f152407401d01b080c2c2003940d516503a4401e00965034031400c9510b0100710f036070501c401c0003031454481690361340041c0f040c14040c01d0114114821a0b21a5040310910291540514200c0c201003901c55200d800c01c0c0000c641c980b0310040241544a4090600d40c11641c0c096518450800c811083c103103202340101c8101e0504c00c86042030b2206940510090071000201d03514294200b00d4041010301c3c1c0750240c40d00780071125001044403000c0e201c0c0f40c900d80081d60140c4020030210104101e8545034411030306c01500301040340a11500301035000d8001c0081e940e58003078024854a07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 946607733 1250 946606483 946606489
    0x5030601110a031d1c03030b220c0305091603140313092028030609050906040b1609050f031e0c030705090618091c120e0120031f15030b 60
    0x11841003c00403046900e1440000078800d4002688c0c02c4005088071070f28450040c0d013601c681c226141010081c0f511500d007403140503494424940d000102c580205400740c42010401c0412185001c05414048a484055041c0f1410800c40301f811162030852407040c1d544030305202c01004181101c042c404c4102e401130314581038010640c1d01444034110200000c81c640540710410010500c201420f00d0345808001a490565118251241d1a00805031816250900d481c5a034184001c01103040c1d04145440c80085992041800d010b46a042d0345004e04c4050382070000c0e140202c00b8000b41d880f0390844801540f1140d000c580e00903512001d81c1102c180a44079810000c0c242001c540300c0da080224540002c00764180b07804900d4025443c130080d6102c2810740c20760200ca2441102c60319000c1019540d103258090340e5449900c4401800030002c102c0158000c48000c003c0ea81c0000020000402001141c0c26440390002000380b01c0c54101158203031946c0e60702e991313420042c0c0c015000c0424908040030417141 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 946608983 1250 946607733 946607749
    0x5090c120f0d090f15030f020c1609050c0a050d1d0d020d05120f0402041b0c020901090c0507081309050103110102010e0d021f020c06040b010503100209010c0305030601110a031d 78
    0x515030085000d041c9080030603807010170000000032803c054079803075481110442032004080c2240800041c2072010811400e08916419035032014180703925160070008168042c0d401c1d5841b4541a03d816942c4003c001606009003500085070241402d07114001c0f0740c00b64001070f000c000551503400740c880c609030050342501c06004040e80f1420750420000001d09001c503070307607005a00502c001d000080c2c0c2ca00791b0130800000c4250000420115007461900700540c80e2000b074150051010700010b00800c2c0074504002c26500400d24002d1a0300004100752403200e40c55208400940428a030802c81e540e0359007080e50780f241c0004503032405940381240382d502d40748001c01c4031143d940d0603400524480c01c98220b901440351801c040700c04090741c28494544810750600203a03008a020702c24001882d4100001c26061a20010f18070303100c11f00c104210b120702d9070050894903a031601801e18079101d59074200140c40410709111108454040c7d202c10030201030b041061450804403045c0d01000703144001092140203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 946610233 1250 946608983 946608989
    0xa0f0e0f0405030a0f1107060302090f060c0c060f16080301090f0b100f020f0111090406240c0f0b040614130f060c031407090311010c0b060405090c120f0d09 69
    0x3c0e0810013850716210b00407050b0b420740411070325202c00e41422040e1442c3c203007101d40c0c20440002e80c000501000078942500c04104003482201e41c54507140070800c400e6642c111180b07290f40680c201051300780b40180410203442c460003101c0800000070f00d0501c1c140d85c40350300c24041c014060b03284c411103007012101c41c45120012200582110a074900e13030041a10082c0381804500c00714440c05047c18404030b070a0082c1c5101000c0195103035100c02c6800100401d5070615000f1007001d41c0030000350311491600303607411180038500b400c1402031035006040407074500008141c0542036149042c180020008658080f2040f03510b64041e071722003071f101c000712400c4140c2164005040c0d40c8500000c0c03404114140c2c048000d0000740c0c100054007441c410032804c0c81400031a0301d040405d80c43c490402c2031020705843c1c0c861400c024600018000f010741da030038074030b4080034027654000d50351280010343d00041082804041c001c010640713040d00c00c0c0d008410b99144a034281900c40350090006420f100c81c00b403815481a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 946611483 1250 946610233 946610243
    0x606031a060a0305060f0a030506040c06030c12050402130533010e1203040905010e160509090414100609230108061f0e01030602041d04050d1b020a0f0e0f04 69
    0x2d000c0b1404400c4025050141c03007954440004a807107140c56a603820440b00940c8120040d24075483c25040c42c2c510404258482801e040c24884035400003903200c203607080c0130144203074000b442e40c445001040c510360000342c8400d01c0c24640030910038030002c40b0b1031080e581018007803c611080d809030032021304d95010585290100c4d10510480c148bd1070801010041200802d040728102540c13091175006a0b942a841a00070510358000d0040d620080340108071081d4041c20140c0c544184040407030b4003d07400034006000110403c00100f0f6000b4140440c4142c7d42c0c040c01c7c140301f0745469007070000051142c200e00c401c9040c000e0302e6208034000840011412601c00a0113090150745d03007041c000e20310000300030042c105407188901280c69042905400d020314002c4500588031420b20050061000d0320365544594103c0c19410030001270800964490300a11514000d0500d404181d0680160f08007050001c0d80450240c40c04220382c40c641d2622000c81d80c184585021340e0f100c031034054081c200305131000340c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 946612733 1250 946611483 946611487
    0x9030302030a030f02120703060e0c090306070c050f010f06090c030501050d030809030403080a2f0604080a03020f0304150c050f220506070c141c060c02030705070602010606031a06 79
    0x103800d0f0090340050040190305001620f48200c0c1d8902e244414030488a10000c00e84d0f4607810700a0404145900360305c040411180d5140c2504500002d940e01c00060081d01005211a05401049018414a0003002180000b400800007004184020341014000c0c4140a40344c10910744400e4800d0040c94101d80c1c014009104030101d94030110ba0401000f018800e96100401000000820000c0180a40c2d0303070581d50441209601c030702d04503500b03030100d40c0182600310440702007080e99030201d41c258106900803d865520800701d00c05402034011a10f504800e40804400c100900c001a40b40d02c81c0780c01c41d20b030100120746618030160307014003550680d0a04114244103098070800301c22300c06a0780d2808440340c501c0343c0b43d8880c009000c40d8080c800484e08030070000000c110102c55076a038480480c50031600e80056a8941030100d2210700740c2c1c04064410b03a01d030880c03103c0303d80c0240115035807150010b041c0c0d08043d481d1440a806440c091045c60006072501c54108085043e403140c0d400c101c04010b00b024 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 946613983 1250 946612733 946612747
    0x10e0a0908030c070c0302060703021513030e1e040e0a02040615020601180b040911041401140607060b1002070303080f042f04180204050a0b0f0111030c12040e070903030203 76
    0x703d6600078000445400744541d10210150b51110301404405100754010500c41c019144026101c0001404e11001c010582d504080001e803c41c048480e50081511881118401a200400140c290619840d04030340b800e40740c00f034401b00104104030443c2c000d0f1000d0141c0e0390340c1e003c407220301e12710681c601c00140c00200050142c03010300307980944568039001001c1180002c040000741250700c03031031086600c2c2030f084150900c5400e150003200b00c41e58204141c950320350324003800c1000e2a010042e1840c81400000f80c20410010a0391000494260182c06420096100c0401039a100c0560000303401088800d000281480200d41c042403040c0d5104401442c0c0e00d258407003006484a90400c900352501c0f0b41420001291518802d072030008400c45c42400f407001d0940184002c817030300540400c0036507042c604202d12076182c09100c0d942c0c1842c01c0c40d1110b0b07048070342c800a5086000d0022202040e0080300400f80410500c14003034425a064200140c0640e100c8070740680b0290000d01c402005a00180049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 946615233 1250 946613983 946614001
    0x207050a0b0307140412061a0d230607030f15050a1403120708030916031a04080c010c1e0810120c0902030f01050f031c180b040f030c0f0b07230d08010e0a090803 71
    0x600303581a601c002b28062150101500d81451422150b180020b40d58211b54001d00c00303140205170805c20541d4100003650b040c5800b160b8180003030f01842654081c4001c41582503201084200b40482d12091b4113905d0300401c0c81c0c80c0d107403580f00b61410a010b10403500b0007101c0c0c08411302240d0860ba800000c40d07000c174184000c20990568028026200070805000f0100102020700400c40c900c080c50f0b9440f0041c030340210580f15684240c0442e90b013000141e5003080901d03542400044180e560622041150481600c2d0454a051003500320401c240d00100030b00265041c510751a070705841049954400036640d50301415640c0e1161490001d44003501179124003064090f1a10f608400350046101202580300c480c40d120716030055102d119160b501e240201306100b00d29403030f04041c022000b9040302e45454540c8007260350194840141c404145459240c07c100744a00c1c1c240c00260b240c8081d50b9910602c2d0001070300008091154034050100440010b00300d071818450789402541c004215410b640300c403490 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 946616483 1250 946615233 946615253
    0x3032c0f060c010e100608010c05030402040b0a03080d0504020f04090803190e07030309030b06031f0b0d020a0909020108060906030325020a15030b010207050a0b0307140412061a0d 79
    0xc16044442007000d510054001e020f07440141400d14018440110b185400d80112141c1398400f00c003507450410315401041d030120450781c00980489001c5011504400000c41c201990f42c002401d00d440082c400308892150f4120512440c000c813510601828030100f44000d441c1c0c0d80d9402001840f041000a030001004c0c00c80e8025603d000c0c17000112040039403c8280340c080309070000d6020984c020f004100304070f81c0c07503c4180d2010059001d42147c00460507000751a440802601c240d85464070403408540d25045200c0d025203030018200c061582d500d0b2180002000c0014090b40000c645000260050909546881c019840076000754030300044410303200080c040e600c0c0b4140960044c80b0109000d079880c41c101d0800b500d107510000510800026010307046039004c800340780c1950042e440401c1291b459140741000c813900201425900e0341c0f0560200c0342080d503450300401a9101040200f80080b401d00340013080e40c440d1200b00888901105648000c51091310010392068000340b030500081e200e60a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 946617733 1250 946616483 946616509
    0x8010b04120c030204020f0909010f0302150304062c0f010c1d031c0e120c0303030c1b070f0f060c110d080c0303090d080a2307050c060c0403032c 64
    0x415400e080d840751300003400d90f48008441d2000081c0441e61205520f0b00314043c0d0300401015402c124101e245a01040f0f540802031110b0701c0038980440041c0c20300005410a04c10000c1c00480d40c11a400c001c518036540d428035003809466071003001d00380c04074404140700300e049c0503032191918221980404003e02d0005a00283c483d0140a100c0b4200e000c14100c84d9940c00004244d1515506247d6182c240981d181e200c0c1c400d5079103648030744000d420f01d0701c0110440380c10610303040d00341d907448880100507200c121403001c03012000c1c81030707400001e104072110700400c044d55181e9018101d0300755208000c5442e5100c643c405130140b0000c100a48003407400d00c40c1e82c098240704610190030b01c1180d002990454008032100c00c29900308440c086441c0d43d015040c030303070f00c501c00f4a0100507440c1410a40000f805081e4804035494160380c4c00f040142d4060016591800207600407105240b0300003800307044540103803104801046510404002d10040c0701c413161040d400030602210b0301000d00082000f4504040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 946618983 1250 946617733 946617743
    0x121d030703060c0302041a09181302040c030e1f110721030b0a0e010513090305190e040f1e0b1e18040302011b030e070612140702160608010b0412 64
    0x100000700700f010f040d400d21f20704100f0010f503a103032500300085c007103c400c406030300000b0060714400b000030095000880510b450f406450018031800c40709030590082c074110098030441d1003050842c0c1c103140c1e40707100380d07002c0c480c5032020a015058481d1355665403070150f01c4009140019582c01d003c84c1518451507407032103007554a00403e01c6113204002c03801c00c68a94005518410100700144a2410410205c0842000500082144141c40e440050a60003461441004545102c1c00c86503d103100309591103101c0c0c00108100090340030307211607400030155048100601e80c04260043d02c2c6079480e00c111580c884014040300c40400310401d0301e0041041c04602190302681e480c2039540e1100b48100381d036200303d101c2e070000195000411406000420040700e010200350900c03854040901003c50500b080301c240d13040c801601c2c0e115103c0e100141854003000d0107203070081e00401030002d50009280c000444294407a41c400c5407a040222203141007400ba07130b101e42800b04020002907280008a0101da8014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 946620233 1250 946618983 946618987
    0x1080a02190b0c15090a0c050d020301110f0c06060303031e0a1e0e1912050921012c06010b0a051c0c17060a05010806010219121d030703060c0302 64
    0x601c1070b000c0c1070307084440b5940341a440402c4048850580b5090300d40c1141c0040020301074030140f80d40341c45c1c0115403801f80ba800740400070303034610841d2025001810301c03001e204150360b210211008070110581013249422040d11501010442e02c0c1008012030340502c0d9034070300c401c42e100c5000c02511041d5070007a1210080340c2d900d0900e1191403010090120080428040204104000203003171403130502264810080300303007400d088100007205841b0241c001e0b1528208213850300d0017900024010301034604001c15120201e030010b41410019030201d2400300050408542a03010822403007800d104c41800c411842c0c6c08103005004003071511b000390600d1038051400c5890100101c501072045e03210811400c4000340c4901701445803681001720b24030158600341c03042c42180380c0140042d84040e01441814180040c15010900e40e9109020103091048040c03902c90b218822460021a0034440c11141c00c000b4040c4240701148030700f108685a01c0a01c010001d1024900b59250000100700141c036007420301d50b003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 946621483 1250 946620233 946620239
    0x306010216060f08010509150909100510030b01170706031109060a090512030a1d0f10080f2212091a03060f040618020c0106030812071701080a0219 65
    0x58039603400c02401d21a51034503643e00100e2000303088290103821091054141c481003003080a41040300c0310301050200e8050b50503484401c00c0c10b00703004014591101103400e000800c07480381ca061708130804a07449040b081150760307a507000c001401d4005481041c81070300310b84010420035203c2d070003030740100382e08030045440c0200072400600103500003e0741d4404602c40c03031400c1040d0b00d4440101e020100c14800514035060b1800301c000c3c6500d8416444880c2501f28412001640c1c42d000c1c18496400300c0609010000d10b40040f004d80801c0046070407800e031050540020b0103a01001c00c844641140c2400b14602c0c0400e1552003000c3c68070640c1100c000c00c80c00301070020340c8400a4845812102c45030060603500d088c50780600c8206110304900a003c0e82c00c20400b04461802203080c8400208148001a2a90440300219001d40f243d584060184100450f017410461480380c26580105c000c0e807a1803c5031295450000c01940b4244540032044d00141c2c13488001d800c100c041074088034180141c000003592 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 946622733 1250 946621483 946621513
    0x7050415031407090c0816050418050a0e0a1b0501090509270610030201080105190612061a0301091b02030a050a05120f06151801140706110c100207150203060102 71
    0xb01191030f2070004501d0f400348400d008114014a003400c40344e2902340d2a160410840c0741035011011880f9040907581c50005824035440d0741b1180040460700b0039280c00c131895040c40e100c5100f0054201c20040504240014190301540b18903088582c00303802c5024540d550900c80403004074400208103044490908050302020500410340b2940d9525803d001617411400010034101c0140c010600038018060440200487c03031881104641c080e00d40740b150f00c40000a00c0e00501210740c8448404d50030180341586040b45040514140c55114000300035000525007440c940c80141142d20000d03030420440804142d100340000d1409010b02d00f13201e460600c10120100034950120b4030111148140c5c07082c0f010900e000ca032001d03a02c601c9040c5c1d0740d040048102d812041d041c00482e0302414003800b04d40003038440108034151811241c0110f4100b00b0940e5207404102a0b1b070085031310b005280250610041c08007014401d8401e0641c001000308402c1c0084800b0300e0080d40044c2c01c6c5c030705611407030034820383c0d0310 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 946623983 1250 946622733 946622741
    0x7030917160e01081e1507050c03070507050108060d03080714070b0f0f1303081317030901090611040b04051e0907052a0a060f0e0a140705041503140709 67
    0x400c100080c442e0a41c90034020340e042a140c60b062004103a100c4071144907501c00022031103034400c840c0240804c903442e0440165614400c984115106000c08554041030050100d041c81c100c0740b00f80c8844c1010b44d04e5000700003000c00c1409006010444034008a91854400d40c480080c0c04524400145084403503100e60340103941c100d5801000d80d180710700300b10210748082d03096500a0b404450602c05080f407560064a80c00004165100c0b014040041c0d40c03c4c002050700c4115100741100c0c019a8030304011003624007809065505407491418801d40e4071f0b40340d0300c0b601224100c481c4181580d050504010030441301c0c50000b480c0075002c4554148020043d40c44071140b601400e146d45a890340c9a40c8454a44681c210701500c00d442d4060100c160316200c0b0000c80c0040c10150f100304005602c1081d00c9484e001041c40c4100c1d07825511903100040200305a0b468043c09098851003110703900ba955000708015074003499045140f02c0040c100800000d0043e11010426a4240c1d0a0302c071402c1d103407442c8100325 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 946625233 1250 946623983 946623989
    0x2010503191d0f070f0f030b0c0d180b070915140f04060203030a051b0d0504030c120f141e13050301020f1c0b06090d0f020a0608070f02030703091716 66
    0x1a40040f0210507408404210410080040315101d020603442d0542544060f42e0300c0c480a00424000310015146c40e05035070807906454010103007040610a50070210304030070303e01c0104444120440011800450040155a0440e410318035002250400e0380c400300c8510324400068650650144810b0507183d4402020300042d251700d5000b9501d03441d100c0b00c0c2c441662405091200d41e546030311f000d00c0008038101c1c101d070741c0c41c102d011011a05440700e18040755455080b4001925510700c0a195810302603001c0e042074408405640c41c101b04903104030500c0d01e140b1a21002400c004044407210000380d42010241003c0010b260000aa417691000400d003680c0c088030071075905100019007050a0100540d186041400440c02000745080e02400b1030b1080c414004130794031550010300584100b01141a8283c02660301410152050755510030181202809580400c0402c15100c1e140c8101880081982c42c69074065035540641860003120091403500031480103024010740303a00da0085104070000b9002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 946626483 1250 946625233 946625291
    0x120403032901020c5a0a09200913060312110f1b060c0106060203030a0c0e090c030a0e0114060a120309090f0b041a0406080a030801050f0307080607080402010206130201050319 77
    0x5d6140c600d41040060300c001d030021281c05103048020071149052401c5800e0541d9090002e940c2c401004001a080b981a00d1944026074181000803040002d00d80107220131041e503480e03480c1e8104503240140d48071110380e0382c150b0540c3d00071104c100c400345001c5002d20130346402a01542c58803603407900390350130751b91541c02c5400540c0c00007082c40004801c82c4180c0191080034541502d40340160030000f40ea242000c4c045038489130022002c22518900d42c0d20000000401c1002041140703400c0d401094410320444070303184030340803c50b00041c40010789488614215030642d201a442810300080c44010074000d2074582d42e0507510090700010792214070030803030504080c0d100da8103030140420811040c3c600c3c0da0060301407900040c0b4007000107600100e890f415140308590f888d00b41076142c6c001c64a440f4055110005611071350050090030768200c0b200ca400b0314001e03800c2d40c038103946100100d1112079450400a00103401007001400602620243c401002200640818100c6078200320040100041800c401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 946627733 1250 946626483 946626649
    0x612040201020d092603040504020a02060114060306010206130f020a030b04061104051e033f040b0909090111030702240903120403032901020c 63
    0xe56804120785480407109140000c2c040d400d054402c0c54901c400451600350761162100600301850a10955000e490054011500c44c0d24405c002942e0b5030080c41100c4280da812065548941094000c907445240e068000300304a885072080d851540b0038011080d41c07840c1d610004240103079121a0440c00960040c4d54513a101d0a180c01c0480803a0799501c40074000c50b0040104200544524030340c04009920072201e00000c41322440401d060210708006d06200f000103c502149654404816010750590340ca034008550882951400f0980b2490241050640b818002c02c1c00520700554015031000480c1c0000c68116182d62300000aa0815a01c900150308031001d0201000300100caa01819001b154003440c0c14100310301025100d10039000700540e280d40307600c0003900741802904444901411503110124074000c20512040754006c0050b200d005000b070003696105441d0040d0030400e008140700d025042c41d0680c06080c2c0c2c880c460248080c8560b10400e1a141c0070400010004900d80144a2089 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 946628983 1250 946627733 946627741
    0xd05010605040e061e0123030106030912020f0a020402030a140403020d020c220207080f040810060504141914090c101107140111010e0f0d1418010e0612 67
    0xc14501000300030074005c5201d10b01c10301052001002200900f442820b02100f00315890207000b17400100300b807800461802c001b0000840507410b5011a00a601071001d4501031809500c049031150300450244490b58440e46542016140940c01580c00031051140010807411500000c42c24400844040e005a0400649064074907010f010309010190300325000c0c0c41d42410708488101d01c0903201120340d06990302107004c0382000344982c00c0300c041c5010119013070b032260790714490280c1c0c409e90545041c6166050000010305800c2034003403417006102e200c060065581d18080500d81066511404a19198854050307172090300c416050280100d0390031000d80b0032031696009018004000090050410500112840200001180d40403c1d80c1200d40c442112182d00401202c54420f05080c04403154030304080c4003a60f2a0020780b082001d0012000da40400104200658001034604400d500e41d40080221440c0c00c00d600208903201401410a0443c881c0148045605604140d4810b0600701d80c21041c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 946630233 1250 946628983 946628999
    0x70902030c22030314040807172e060b190c03030f060e09060c16060903021e0115080c0307050603040503070611070c05060a0903020108060f100e0f0d170f0d0501060504 74
    0x4140c0d444c0325580c185d49000d03e400700041e590405849600f070340c24051b0f081060070710024082d64010f521120071006e8000e40110704c0d1520010508408400e803031504030f0000e0114100000e40d24403000078205e00c0021143e510041d20084000c036400c40800d5524107425525002074820340000c0c041c4c601100c5000e1824580c441d01e0314002400401801c00300740141c43c0841d01e001080c4004a902040206501c02c07249001e80c604114460301018a035a00d040d00d4500130303415409003010100b80065050003540d500d91294031181b40080d101d4040e00225000e01141c14400011038100b4030910481e45840c403140ca4540c06c440e001c4000b512052000500c2405000c50700c00c031705000e010100c895614209402401615800c0c071448000d0520080034000b40c3d03241c1d608042c913416140c001d41000780c11a58810024200c5602d0f2401c207104918042c1c4204050a00c84c406001ca04d1b840b82d1850000f840c0301141651540110b042038105d440c04000d0800c6c4000345001d014000d003a1929141c3c0c030740d8100441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 946631483 1250 946630233 946630247
    0x15082401140412030e06070803220f11031b060a030e0c090702160e0f0406050c07170d14100306020c0307120306090f15150509041b1808070902030c220303 68
    0x2c19100d01800d00212000c15860009c03282c20101c03008410f04400b84a00d03404d00810300043d0098412082e002c009024840c8003851140005012401d645501031005243c429501c1000c0300c01c0d4112b07006000e0074203a24060303800031b4428030000c021118484200c0300092000c450480700440160081450340080710480030f5404041d141250780c113003440c80c01e8456090900001800034003059100d0004c180000c542008488202c1e821400c0b080c1c0c07000c04d1984800240d0311aa226034211481c01c40c0c14502900e50f50762850007000c0e81903450700c500b451030300d5010294120f40c40c0b080480c0030402140c40015065011001c0008098502003500c514014040080f1b0f020300790302c0c009060074001045907804080a003001030f600000031030301040032966070454036400780000c4a070f003052411307455021503503919041c18a560503603134805110308441501720600d00031074131440004d54040c01e001d002d9002590095507209240c1681103007000c0c035462010300b0700c85101000c4182c041031040700380300781540400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 946632733 1250 946631483 946631507
    0x1208070f050a03112109122a120408060a1802010203070209070207170309030601060f02070e06011814040b0f010f031d0102040f1508240114041203 65
    0x3861500408408005070192140e03401c100105961801014031102c1c0c030030107490510201442410020703550840401000304e0507505001c1340d10a000c00c036082c1034650303401c540380b404081e0311800700c2240000500c1884900001300c19081d001d00380f1098010500c42020704020800000145080e04010400360121503030f900e000030301903546111000c0540d8000044480042d8140c404440b99602c046040f1700307055454000d0341e41e54204c0400142001030000141c103240702c040301035490f5a40d99080c180e54141005a240b40036821030b407401c11038000000d4503a0b40c00101814900728901c601c041c1c0765080e40642d00072207800100300004480310306217032217510b501c0203007036076507403c40360600c0c0002e805140f4101d00c41c400c0584a2604c8450141341c00f030006c82154140c8001c0d5151a01c0b1010300240080a0140782d411150030b422081c000d5100f500100d0052030303142e0700c000c0b40400c041c40316003030040398240290602c000c4201e1072044c820b406005000405042904101000c0d0320714000700321005042b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 946633983 1250 946632733 946632737
    0x213050f0a0b04181b080607050c2401030f0c0302090f091b0916030603060c0512071b0b0618040302010e07081c0c021201020d0207060f02032401020f0703120807 71
    0x340a0490020807110142403030b508400d40c06030411003004015452050b54221514900a1f00d040c80320b5141c101b000750085001c0c0c2d10565028940d800d401103510046900c400c02032001080c01000814080800840554000c001140328103031070b600410984001503800d80c0324100d51404111150200344101e070450f50308020210341050440000480e41c5001800c009108510f004004a005000c0d80c00840107560024043c004200c2c420b601801680104152106410804c000200c84034440d00f190fa1100b01c45103061000041c3c1d540701c21005010042040380c000c003520301c5041580e030700c50350018450742c400d034008511200015078260400100c1d900880541d8400c84013204000443c540c401c110512601d0502041c070124000240c1049040d02c507030720203520004612401c0b60301c40d0000c10f01c1900a41d820f0151202d0301000100300d00c011070302d0101d104902521840c013800c0d039070804502d180c1c05204540c1c000020b040750ba81081a00d50046036142c0107418850240760304010307116801002c41c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 946635233 1250 946633983 946633991
    0x70b160512040b131a04030201060e07170c0f1903180c0509070915120605010e302a040507270b0409021803070b0a0c0213050f0a0b04 59
    0x14038a10501884060b0009000d14818000074003201040c82811800503008410005281c4403500042c0101d402507500340c0041d4200800070940b0000000b40034018405a40c03034203a0200d18807510060003101800c0025218010069030b1565000880034020880c1040c2000c00700100030b00d0302608681410961030441c1654918440102e82c00401503001c54500780c802d11800d039519207003124044c1840d044495a044080e00c00c0c0441684401515505204603000300310b5a51a4801511400ba07200f120580c01001140e1103141c1c071101038810401292607200c1c51038054848501e0b03034145a1401100c90074850b1500716000804590300180c1c1a055094808208904000100414240c142e40500015031240222208590301180041e0006c10740c00702030316261603c030354621010754040d900d00070144001500156492401140345c4045030400c448040c900141840180d40e0f0940003002039a100095140105a01c28ec40c000d461140385121048503042c6008041c140841e502d44404600075460 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 946636483 1250 946635233 946635247
    0x20901110c06070b0907030515010e011a07140703140a06050c040e04080f0f030109091b180c0215270d020607140d090804080d14040603020c030d02070b1605 69
    0x41d802c2250301c10750f000850710701682e86a003155840c213060b640c40201280300b18080b82d18070000d020740042c140c9501d40c0303054103146d0b40c840340941d07180351401c1940f4403c00200702c4d190014800398610340c4c1c0c08810030240c1e484d00340d403130f11016003034400e4071900301ca00e42142c41400100461407141c0c070352001a0341c0010781000d003410301b143c24151000f0001811082c0018400b10044035039001d5842560100d03184559079a10782010b080940b40c01c1d10211046030104402600580d403101b0801e080c0c41c510014011150141c81c824006040c02c0b0240c8015400f0308a40c440c483e12170104003510600c0ca40b8000d41a0342c0802c41c4c0c0c2c00400c54400c61104841d00000040c042881c0e01161403600309496140240c0c030701c0c50142c00c2ca0102d106039428192002d1810074004c0410504002400440705010705840e00b040c10440291950030380c031401c11301c89a004110610031607010b603000e440040000e40459052002090b00a4101d0b84840030503514682074104101440d000040040045402031401d02c0c00d2541d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 946637733 1250 946636483 946636489
    0xb0f03190b10080a0c021b090405100f060e13020906091f080114090718020325030504030f0f0212031f090e0106120210080408163915030b09040501020901110c 70
    0xc2c2c400707e80c1c82a80f4220100d03092040410221003102c282400c108807402d00905801c005000c0340c8a41180b00d80c0210014035407a00c040c2c0e02060498010307140f40b20590b10700080001e40c10f0000c1000580745480c5107019400b40c1c0700381c1a40c000e003607103500000380c40b07910300c20172140c8540003130403031619901031407003401420404850043d094001e0721025171213071a00542c091a1b0181c3c1241800c0342c100c000c254a400c503905070840360180b4003e03120180c111a1120f011030361000240601e40250b40710340810284044c1c00801035501c0703aa264100702c5060180c4102d4261704200354010404c19860301100c10701200300f032003440c00a200001c00d1180c0507195901040f160740d100d00008080c00b003804001814008001c00b02e0746200e642140e02c03040300301a86030900481e004011010b80e030b0003d41c110105000c450011814030041004000e410f101c0c5001c0c84403010681201030482015110b075003038071441d03d5802d2442e008511550015899400d0701000500c0c01d0b8244130500c04940c071440444580d51 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 946638983 1250 946637733 946637773
    0x506040303020a240c08060901061d0d050a081b0f01021c0209040608061006030b04050105031e03070606030b011707060807050a11120301050a0b0f03190b10080a0c02 73
    0x3581c02070000c050100d41c104c000c100381030006801c00d8203d003400503920721154001800351140b001100c1c05466640ca41c9403c844200303540700103101100c2e040b000e41600d07140a01c04402414403c2088450381d84a42c0d0315150580c10004d5030603803140b90600c01c190303881c40c1441805020b8116900841c00d01100200040d0309003101400c528141d80d000400e05806c1d181c1d03401c403101030000001102c00d00e0420f41442c1d5006803861066100181c6004406c98a81c5098080d00e412660010024000ca64403941c2203075146022020980300ba01c001c1010000185560144000450003070031450030661608a1020303500104591840151f04041000d018240e0815000e075003103042450900c0c1c80341c8039a81e0907181044030201c9162107124480350152121540402181a0b89059941c503108541d03550211415008444110007888014400505412000d48103800010700e84100400d03c52107207008920300180d800315140000b15042c040042c50801809152141d1703a4034401045480c14030031400c6602 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 946640233 1250 946638983 946639003
    0xb030d08060f0d05030706050106050310080a120e2d09061009141813170c03040b09060f0a08040c050a05030303010e09120309010e16060e0f0a091d07050604030302 72
    0x1040343c03900800601100300301340d94445a0002c0b0400003035840e00e030040e09513041158050155a444c0c4804550850003041002e05190b0015100000404105040e108003025000c00da070400c0449200f181d085200716845000c0b00f1002d40c00f4102c00c0780046c240310361007000400307060191801501c09a03c50364000c403004112031b11032480f1210030307182e50006030103c40c0d0380303143c03401910303d220078031030403400000a002c14607100c1e4207600303c42c60f0010b02200c114001c1109000700d40e0401e00040082d00746000060480c89002484503181004480c8417030701c590030400c0c2c90000100385404200c100266040c1460140108481e0b5010892400e000645c0e40d2005008003010b1001c558003046c007452040108205000700034064980303a243c1070b01e800d40200071044051020344911210f010300d102d450310f217207800c0d501c40f55100010354100000780085140061a5243c205c01c07605400106070f03229124100c41c003104481c2e460b04841c6a01407462400718140c03c403134860641003008000003600003a0449075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 946641483 1250 946640233 946640239
    0x6060603111c0e030c07090e16030c09050c0d02122707090209030307021011010c0302040f03030309031e170105100215100506070f061406130b0402090406090b030d08060f 75
    0x8581c0011041e8150b0091084018940c0f003000c6d80032030034003080c0d0841140d1000c110110703660307891b2032019004100458407001d00764030000c01090200142d00e801056100050010251410001c28424001c07603000c00c0860b408a032901c01485840050322101d0308101041d1540c11b10748520100c5062344800c007910800380400d600184914450f00c061040c0c6076440e8004000c09000941040d02500740034108222a62a5103041d144054950091003520141c546840c2c59850a40c2942da091303006141d00c100036002c0c40f40e0368219280019944404185c0382d03c6a668480b0403140c1d1982d007240c07244060704503c0c490060640c0c04c56120750300244005401804407200701544d00d8461071280391042d00d030040d42d004000020840180419010041c0c606442071108001048041006070009102500c0c000d91180011583c59582801c0c0d41004242c10300080c001450010004000380880b40b180e4008441581c890b6961116460248903907034040f2114100054140b900500141424031a801c00741d00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 946642733 1250 946641483 946641491
    0x3010902070c17010204210c03030c02062a0f030c03180a03080703020115290a1803120e0102151303091d1b1606020307051606060603111c 61
    0x42c81581c1549100400c609a20000182c110300c011a010350301c14082d50a014a12400340300608800c5030f401c2da0703c9600640561191030075940e08a8a000c0002026a40148103001d0f6482243d101002e103804007440c1002421803039100781480341000c0b1381044da1038181d001400103030110f60010084031899070b03041e03258540c40e6110740001510903c1d40c0d0400381c078810340402c46601301901503226003010f035000f0100801c0142e907a080b0700d55490010f80445851081e020141030180c0c01c0102601e8114120700b0291507502d00b03035090741c40440e996030064a015541d613003000c034625000a00486001005e101900103070441c0500d0300e038400b801404682000c1d06486c040e1091500c9a181c44000d044c2603011500d2000c0c0240d1400000b0100b0f55a0805050006401c030003040030a1b41120300c0c0324504a01403041d41e40f0750712008001e410041c00c902c20b0003820800460140e1048210a01c440c3c419000040c2c01ca04102e00242201c00301d070720507030009008014191542d84d0140589a1a241c40c003c041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 946643983 1250 946642733 946642747
    0x506090103110f0409110711090711010e070911030c1605011503061406060412030c051c0206090c060306130203041a10050f040c050a082a0a020c030a050303010902 72
    0xa0007402c265245102107040400c0201d48518800010703c01c40d4002c900c1442030003140c04202e0614070402d900101208010b0f885504242816694203070700185904120300d00c80e1966402d1401c0d50b0303010701c0154490b040a2414040c0c80c1303080c071502d01c1240d08038041d5415031505010092075440b424900b030521060200181741080001d400c189201c1d050301002c0c81c00c1e165240b6041d00503040e15100504411600c000041c19400d00809807811502680f00401c0000900d40f0144d40c50348da03c0d14203945601400c94507a01740d015408a80101881650040c221450140d10303650621500c5160188900707810400e20400350f451a250400441c1d1541005941c2c3d01c0707901c0d05c0c2030001610303586240561101e8003001400004071802c1c1044a20544d4034003480c1c440082000201c40c0b5606544002c644180b2000c1c805c0c1c0e224807502c580c08241402c9103503100c070031105002404240030804600202c800511580015030521042c0801c0c4004c0d802441005a02d03511035032203000500400d02c0a96001c103400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 946645233 1250 946643983 946643987
    0x103030f05030c070c092702010e120a0803070512130305070b07200c120a020a1217181203120a15051809010c14091c06050709030b0603070602030405060901 69
    0x1c0301920b038017a07028290143c6d1502c03000040e103510581d1202070011988a104254103215003034030600d90580d06c00d02c5d29006c6604000f140241c2e040ea0085a00c07036141c1100c0091107170001140100c10300d403905074864440d83c2540c400800d0040c42d04a14000c2d00e0400d40005c1d4103d010b4500c070031b45c800484001561680700c00c9903c1c2e840006005059031042035140821800440e810124040c26503001e50600c0341c40764030707950b51402600000d4002070070343e0003001500002c101a051892013030300a00300210b0b9030035441c3c440350003202940c94800d4041c8105607552a110106c51580200a000b450818400600342c001d201001401a42841e0300c6003182d451014040b2943c0c0e01510000300707404803070802d15260485d0000105c1ea5004290300c0c2024680c0080d01030303407040812030000b6150790b14200410003030100a40e03103070030280e10096101c16048002030042c02024890b40715584d946820601e1401c6c98040258060400d502a801100f401d0020a502108460554100760390a035603e036507483c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 946646483 1250 946645233 946645237
    0x30308060402071208040c06030c0801170a021009080118110d0501111b0d030b031207110411030901200405041104030b0f01060e040204150f0905030105090c010210050103030f05030c 80
    0x14400d00c41c084011070296006101c03030740076038012042c4094848d00c40c84c0540494043c1e030b0326070000c0307803580d00101300c12507240943c03826200400054558507449540460032440c1440c030f00e440411510b20007481512424880c0b8210510300160f40c60034060aa10303a0b54001d0940c080080c0107884010800050210075001140180f508007242581d40c214211480340000e60002e801881e4082c0c00b41c00300e4054031a004242c059003004000d40798260000e1810b2825620145040322003040295100c2910350f21845404d056046030000f280d524900320300d8842c21503512a00a50140180900e500c150030000810340c2e00b5688144d800040c0200210420a114000c540c40241666200010400c80c8007105002c40e04031011038444c0b1280c50b03041030421060380690b0103007019180c109890651021f02c581009411080719052407010b283d20f0320003090031345a088400c0500796001043c1a622560b04024507201a49010020400e41d410765400074002c0380000040f004214011012a00010074001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 946647733 1250 946646483 946646497
    0x1c0506031c11060f0c161e030f020f070e0a020f0c190c0e0c030a02091f031a0109030f03050714010903020c010809060f0f151215090313030308060402 66
    0x4000745006a00400041c0250200b0102c03070355600610340802c40500804000768001c01d00c8408183c1000c01c0048010407a0140794000c2d15108400310b04060009503120174066071500079030780c1b03000316440d03d200a4908043e8001c644007650101c0d1080051200600c030303a0b034100340050740169441c40c5800300c001c1030b802409845071150250400c090000c61a044044524901c00d0002e82c44030f5541e000c0c0d0380d0265000700e0302ca0081c48410070024024074150383c003c2415610007810358844003000550807c66040d0707540f080000c41c0e500c500c3c0c800e1200034054461500e00c800d00e00310481d40c0c291380d41c0d2041c48042681c01410f100001c10b003070741000004500c01c5200103402c1c1c000c12003c9998140256a11101168280820300c0c0130007007002d8017000700d8001c0c480e01c00181d40c0c20079904e40d000703000e00000d030040060031268a04910f6076541e0780d40100d8010403111041c000c118420b100b10981d00e4484c406401324203903520070010452a80d0640b0490390403a40c050030b000d816030b036481d0040780c0648103500c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 946648983 1250 946647733 946647763
    0x30706020f0d1107110f15070f03110c060421080c06070806010c050c0d020a0b0f03061009032409062a0207081513080a08090c061c050603 61
    0x41070360700341da1407281c0290005580d9800107210b02c0404840e83c40c107910482c2c1c4050702117034070b08102c50140d05041d407911081440261403004604140c203017045c96500070300012201c00401000705028140d0054a903090010300341c02800800044030001a030302d01c102e108004440b9403000b480f1051050544460050b0f941000000e5030790090703000720f1030f2104030840780c810108448501081065200e9490481c07490382c4171000700039580200041084c500121501280c0c4006151800304482c4007201c0034001c500d8076210a00e40724106001007240b075041e40284d843c100320066104201060340c1a03c0052005214444907440c1d117070055140d0094102c40902606150910020b144109003c41c0608290310086424554018168808a0700c4610314810181c055101c6180821340d040c0c0e40c1959504107002c07402403000b01c41140d070380e000d00750801c00d08440030a084104002e401001072042d4410064212081e51a0103003034070f01001078501c2000c80030001641ca40c001403458404201c0108001200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 946650233 1250 946648983 946648987
    0x907090204080d0801291b01020d14160f1b12080a0f0b03031e130906050307060302040605160303140108010b150313020d020a030b04050606011d0112020c03070602 72
    0x900341850b503803810480500005441c10000203030404001000880741c0c1c06e800c55004040b01005000e41c81c40d0020f0015140c804c00103203003070803071481c00d200030110150503803000f2900c081802481403462000425445108103003200f05803c16601c82501001c1101c24100012910030060000c107034010001e000a040c55240184030101c4c5070071103505803250912010906c4050714040b2480c080c1c036140001c4a82550051206000005d08500c01b81d0b81c10441c04080c40c1840704411a0b441c0800d0309030301c0340f0481990741c80103014508042c000749020307044505040d8a09071a006004255115249101d8000e082807481c45c4101482500a100c850049500f844020b50311807010600a010823000544140a0040c0e01425100c0e80400c1c0ca01c00c0c400c0c1d40d06288100025000e1120300c1203180c00c00c0780c1c40002c44c440440042e211207a954021400b41008080b039251400c005000700002d105103140c010780c0100c0d81002c60ba84950000c25401400c08051380300c90180d94402c0c503500032600020005800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 946651483 1250 946650233 946650239
    0xc0e043e1b07270506010e010e0112090614090d050c100506011e0e1017040209130c0b0307031523010201110a080603010f020c070e090a0c120302060708100e0907090204 74
    0x50841104486010f04004120a480380d20042d40c4402050106e80e011036140d209100d0f079503014800f40c5d1040310450343c01040781125560307607908035000068600c0e800c100303d04c02c1c0920b0b001d08102c44e00301c0c02018103240d440d010f0200300e01c0b562840d41a44483c031480d120000500385905c101090811156803490800b0014030804000d0010250030500300c3c010441266114485441121038501507400111540055101d58003844035142e0010101c02801c900305001000160481c024100181b80103071400785c60b42048440101a10b00400482c40140002e0100b80420040e8400380c049041200302801c1442c20100e0040c0e0141201c42c0030720404403c08584440b0540d0462a440d1260900300c0003001007040220038030049005041410510b54002c000500140d402140d041e0740180b1003004a809a9000f95607000010b41c480d00014894121943c407481016010016550400384c0e60a0001107454050642c01420169109d040b00b410100c2000c6011010203005043c090308141c0000c0d952951 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 946652733 1250 946651483 946651529
    0x21010207060c050a09090f18050304060e0906102610051305070f0c1b0f06030b0901150c0606080a03020a120e0f01030c0e043e1b07 58
    0x1580d094580a003480c1c1500ea0741032250003100c40010302d640312a01c126003000c0514000700785d06140342d040c05a59007040d450305510500030710405071060b001142c1d600e040c02c2e0000c2050558000c5940504030803000d00038290b980501a594080051414408a001c0600904c0d4250340c1050a06001c800500500584c00f0b8058107010581d10b0a4039041c021668102c08081150000c035170b194001001d00d803100d004240310782010b2040074029140d9565100560710303c1048900b059100032003940c1902c4003001120303094091002820021100441a580f500209542140c9440404801c00441101140402003143d00c10409813116400307d544592043c80d01035035680101505481003854900d03000306052040100020552000d03050b58088016400150060100900c038507092000c0d140d010301d01078407a80309000b030b80105158103226071142e44000d42441000035401d80308807c840d186042040c8022000c480d17440740507030030718000b5034914801d0302c3c24100319420114211741a8190b010b401c503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 946653983 1250 946652733 946652737
    0x1e030207091a0409122318150309010c110a1106031308030406020403020f101403100e0702011e140c2d21012105071203030e0f01090b15210102 63
    0x1074002d40360b4144200402e1146d801d404214217810510880400041c1c0c5443c0079103146010b00d00020b01049412001205401500e400c1142c1541050303540740c0010808a03441008801d00e0102c40c4c01078000720710b65844600003214144031681c0511000008101943d14104d02c0240303068100741403a8aa0502d40350000183d849480141d2240c0c905100ca42440e01d081c103003150711a501d54484503001d080d62207110360140c01c000d0041c203503501040400a034540d01180d04501c246c030541e000140f81c3c4064040c002d9000b0075074004111480c0750000507038240400200d4950030501076004503071214036144070344c0c0b5206042c024014003524100c05401d05244860040c002c0b60400302036203154450b2044c0c0e098400304091244003a02911203044544010000390749600707480c043c00980c2e030308a07201c4c0c070130f554034003010001100041d5032140441100c500034040c075032181114400030301c450a5a9100c0d607580d541c01815071aa207403445944a1055a141c4682d090303c0c13a002e5500d41511103000403603900035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 946655233 1250 946653983 946654013
    0x1c05040918020406090605090711011803030e0601090e07090b030307050a0b0a0614060403060e07170f1e0a12020c091509100b0d2d091e030207091a0409 67
    0x66410a18017007545400c90060348162070024088038204ea40d603a60468004d801030407031040b03655850916006103040c185c0715409143c040d4801181d8021110503440c0341c003005a101d084498640707181d5000d40c0c1c0e000300d0b4400480300ca14802044004400c00007030b0a41c400c4100044c007600c1501101001c010701b90300710314070230783c2c042804100c180d03558000401134007030300d40240e0348c4607104200c01e10001c0c0c0e69504c10802c000c48141103074032042d120344441c00d42e0031407694600c54640c0300c140d00c8950504100100030300c82d4031010860804d46000c200007540c40f010224000c1020701e0781c007480d0890500c200f011403421400240208903d00700542d1018a400c624424140280040f03c00114044100c40e01403040302c10421950f8600801070744402d008102d0084003a0840c02c24080c2010680800082d0566040c3c3c04130780016480e0440c584180b681500c80f0b04c40b4035441030f490401c000300360046014000c907450100003158555901f070082180310003282441da405842e2a00582c20710484248840f20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 946656483 1250 946655233 946655239
    0x3060c021207020609040203250908190210270b041406070302150a150801051608040302100f14180115050f1c050a0b0703051003051c0504091802 64
    0x1101030910228600c0748202d0300301a402c083c0c20002c0a8803820550300035640411130300c10b000918220642e51004519241601c4000902d1195080c0020712040c4000800000400203102d00e640740c0344d0202c2e41c0c40c40d400b6072060910282c548401541c0001d01d00065070b0888034015060351603100c1c110304c0e01c0e40d000303402000804240014510a40d0914200326900140c26400400d90745c210100f956815540043c400740f007094a4a011059a000300e103000d00c05804c00302c001141d0340c500f00c04030000b000000101c5204008036070742484042a00070601c26001d0840c0140450400c4590280801901790501c0f0700550b400c18400f04080341201038510070011082070024481a8010700040420041c140159680710503603045000162520710140800840d901d59110403220a503101c490404444034800d890500d0000b00704a0f80030341c136100783e0381c0c000d007000380300009039045440704c03030b42c4820f11003100042c480b084080c401500c0c05481620700a000c00441485000c8441c00d020380032a40013030040340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 946657733 1250 946656483 946656493
    0x13030606030506100b0d0b0f1801050906150a080603160806040203070602030406051b0a0602070309080d021203070302180303032818170f0f0301150f0509011d030703060c02 76
    0x4020300043c0603450460705c00c40c699a08100c10300001e2002004240f46072944440719160410281c1c80321401f05039442d015214210030f9615007010701018007401002148140720402001c184803890600b5240b001045140c4124955204404240b606456580000b90711044980000d40c01500064417481703680300740d058a00d0ba5650b08000e0f65680524001c4102240050040040d10846d001c0049000c101c010201c40b6141d6094907104120303403020806400040200c0000d0280c2201000502c030f1011003403000744000b86c89624801813078000032f002c000030981c0009403403030281901c88011400c440001c0130349a072820081428110400301d00d403030088203020850407e0315048175124980c42c5e6621a000c1c08002081a940c0c4008030644e02c817080c079424014000c5204212074280030704525010b0305c80003640c039410403083c80c035242485900303030007003004074802c400a02d68024199070340c001081c200a26591181ca0211b4803086058070a9901b600c1512000018480150070821484000d6001d0b10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 946658983 1250 946657733 946657741
    0x8030a0b0f0f0f01021c0c0c0b0a080406051312031b08040c0501050c1018140a0c15050d0203090c010905090709031101120e1f0b0d080702010513030606030506 70
    0x81107000c014410325900c01c0b84602c14218509180e01084400e0805105a0f84482c0c884040c070901c8200c00001400081c14200d504410003070480b1015020b001050340c2d103410a404030718018140d40c40108024050b40d00e95012418480240c5c040d03400140d8046211408011110301c010010940100040800344141d03411407801402181464040c94108000411241c1044015201a440300d80d18140f5882005c01d902c40242140c42032030000c20780c022502d50101c2c0d0034141074112010044204c0401e402484164001401100d1440200e036034280c40ca440107000c1d40800d07a624052030702c1e6440c0b1507000000300441d500340890141d40f600400d0302c0700700f4810307264414048210800c80d254804158140b1061021a070704c081621080c400c1454183c1c0e813000410401d006543c035212001d0300603481600e12110b0121610b489034000d0754086810043d0b588000b000407400c125012000e007203004001100c10540e4825000c44540880132480510629560310b000002001c2030705c03040d41d241c0280340c040303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 946660233 1250 946658983 946658989
    0x70f05030c0c090a0c1407030e0a060c05101118040608030703030605040e0c061b072c09010c020c040b0a170d090e060d02011107080d020318040c09151b08030a0b 71
    0xc401c044c80c440d031b601500c2c0740d0380c2c00d000d00c0c140e400603405070b05024041c55600200e503505a81d84020384841d40e980c070720000380c038a003031442d1070350000341840c038103041152928116003001c042c4c6008940c1421009401503414001c540109510782084082d8040065041c00745901a0410022144291010018084c07400c0c18903840d221144003041e808103080103030783c3c0c1030070440c117030281207900702c200f941c0500380d460344801203c082801c2c5030350ba110200c150f880302180e4a01041a40052444024080341400f900c00075100c0111008a5200b90703030384e40c900c0c045502c4809c02c1801501004004505006181e003000d50b580840240040c00143c1402d00855510303c8001c1150203901c0240130100d42141e00d41c0103443c89072203034459041d0340c8107000002035100420801c0c0d0b01055225005181e543c003583d6a10080e010341240710900590030844050b0301180d100750010100c80c980059464540314a10084820200e42e00845040b4403c50000e01d0512104030f00650290710241c2003044652281414 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 946661483 1250 946660233 946660241
    0x18010e0d0b0109020c1b0f310b010201050907060f0c080909010603021b01060608041e02100f02010c0c05060103030807021606030c1d2b0c0e01050901050117060402070f05030c0c090a 80
    0x5560703004000003c1030f801d2401c08c910449400315200b28543e5030450351420394204e8441c060081c0300d0781354540c40542072650302885070940220300800a0241c0605014000d0324100341c440d6410200100300b2402c4050202c260705a580a80700180070380c0f819695444020060741006001c0d03c450540d902e80340295520520070381d41240c445071540c440315501d944409401210003021008807010707410114006a8411484210751300c0e6a846503588c00d100d54030001d003180c030b08440100078006000d443d00007080c0700044250449a061411040944c0c1c1c03800c00700c0c102100210048070340740f05202c01090460705030304903a021007440d03039901d10140c44882240c1e071440d0048510303c5c0c0115031141d162503080651041c02183c159500c0c070703040341c0b00c00e186d9034961501c5403035000c40d000e07044204c014080340c80e1041c44580100402d10b80000140d064030f108040782000a002e091165600190007400c106241405282c50b540281c15641c0758070010400d01d85170700f46440c02a200744a0080090080d151503c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 946662733 1250 946661483 946661533
    0x6081f051f1401030f020a0809010c090311060c0c150d0507080c0a0e0312130503070b030702071203020c0604180b190b030406110f0406030507020318010e0d0b0109020c 74
    0x49049003040c58140d00154801c0800003543c1050784400c0d2400c4501c000e03000800c2012580e580e64550f80c50207524042c00c644070391405504000718004104040341500a03003840d03402c81103c03c0e070b9070751070100b042074602244041076681102d00e0700803500d00c812010010b0b22407404007910520896441d41000c0b01c00407030460340c180d01001d007070000c07180d800d209211030003007078074041c044984003d034002541c2c0c1c2c0754002a064030380310000d0320020310181c00d003440360000404c2d1410683d8250f0601c0507010b92905191300501c0341116180c2c0e550028188204200400594040c01c0365075a10b0319051400c40b40c2a0798940600100d05100d0305120a080a16010310741522400d505507e00d8249114909176078005001a1100c0b0340700d01c0b124034503c01200081c56401c1100c85e201e0360321b52a2100c040c050b40e10082032881550414010360325031015444002050400910301a0740f07040a05000418081d602080a004080d240c1c00106102c0714950007000d85888131411101c0560315404607211030241da41d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 946663983 1250 946662733 946662781
    0xe0a051b0415020f1204090e01020405150307020c0405180c09010501051c0e01020d200f030105120f0601150927020310120b0f010e09120a0306081f05 66
    0x4010030880c02c40c501500001c50030340c03056540f481101120145001090700c40c81c0c25800000808001c4080c2c41e11824400702082002541424503200001d181c0302a0f081c01a0b460301c0c000000680264400c1c080140382e150014420001c6080c4031107004039004820b10a150988280c1984c1c280e1481d01080b154103c0d00c05a55440c90305000d202481c90080c00d03e01d40c1d4611a0311842c504480c0c90003030014040c030241914000441ea0792849a24110160310783c0c0c41a6000c03070070010f01b41d42103007400c216810f59109440000355a4141040c0c01d2070f02c0c081380707600c460601901c4004504492907000001c48072405540d146002c640390b203111003010000e83e154034801025070b2018103d0a10365005994010507003407000c1d213600d0356840409a0134081203021581914580e0800144502500d007607400b401c10007410050341d02d0005e400710741c2c40207520a0141404c0002c900340c9029807081d00600080d01d00f4000355031405944030004030010304c162040c020310506201c0060031503241713206030310400140f407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 946665233 1250 946663983 946663987
    0x14130f0602220801051e041106070807140a260d05060303130801020405012d230c100b0415060f0207030803070503042d021302090a0e0a051b 62
    0x5aa201002580001d0901200c0c41c0e03000c0c000854003041c003071000010300d4807100200789484d001da6201b24030000e0350002c54041c0210750501c00800d11055a00302c4904060301c2103035551130141425100f5004136a070050900404a080300c030500b4001c00c4850000b0f116217211020390181880002101ea80a410b182903c1c0042c0003400fa44002a0005500008051f044d246000c01d4048125144030300364002c030640c4da400150810455a000302d400c51501d41d071081c00440c45040c024034000014881d280d00040010b200e058180609002e03800d040c1c04107544002d582c0d950042049151500f800403419098245010703c0e00c69207090a0145800f44501d0001c00140340d030500000340d440c990144020402c603c94554003200203080080150300a64654441644915051402034a90414140b207c108100c0524502d0425101c4203540c880d842d604942110076440200c4064000b0300685441d00d50118204000144001c0d0700c44543d40213074101c1e007007405030b6a507009984824058440d001074080c501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 946666483 1250 946665233 946665263
    0x110a0f0e0d0818042f040b0a030c0e030f010b0108010f140d1a04110907031424060412230628050f060406140a0501050c150403031413 59
    0x6590010081c071100d008015100c0401980494200d4005c4d182c0318403000b41c1c2c4540d403441c0541001840c4040d010000420745070504051144030f0602421014205154840d041f40320020b0003400e900011407406412030f181d080003103855a000e0b02007594240c3c04605030f10008107a204404080c03405403581c02d004044941e030340000380041c0c503080f02001e46080240b4071028810303041440b1200d0241c0c2c002e404500c2e5522105003007000004020302900203152a101c40580309914000d01d0395802481c800b081c4440d840800d03070307040000380a03144141c0e1014001034082020402d0640041c2028060380f074005141c401c4040d03054010740d440b45520540c0e8041c20000d0211480588502c80410a2000d0b2040e0024600d054100303985080d50303082c5d0000d42031000c1081034240740c4500f000900c400d000c68005622044049654504640201c42c100000050040d2144908000c2c0040f1507010180080030f41c581070600900402c0340c0e0170307071400e00b035113620100c0d2010400c494048083e9422000782c0103d28a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 946667733 1250 946666483 946666493
    0x110f0a032712140703140703060b0613091107050609031209151302010c0203010203190e0706081303200a11010c021020010603140705010309051e03040504110a0f0e0d 73
    0x206241e280c81e0f207880761820100c005060108000061500c18000b04441400d5150582c20755014841c1389000d1002404140c814070140c0b59030004803581030341c00140412442014074001e2064001c054110710034007041c00140c483c000001c10b03134a02e0b003c141043d280c0701c4013001a1219081624031599806810200c0c5102d11071501941c61148141000d0203c00441c1e404242a80c2085440001e0b0100d107502840d400500b60060352290060344014181c11418010068843c8801501e8030604560140301802050300407039039881000709064607201c0509140a5007030b0389405101040b516550024520704855014000c140d20686c0c1c0200225440700c500541161900f801420200e150707020041559009502803090300082e5015a0f01c0c0040540d604550a00c0c10400780e1080f4105880c144542d40030807404500e070007064a0b0204c1902c90101085e140307524501594201c682d1152510162288010345400201002000e0741c44811800f4609001528260310a4036610b8102d07004400c800c0c0051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 946668983 1250 946667733 946667753
    0x70804020604170c04180203060106050c071a090a0e040c05040207110103240603060614041d2a0d0e0106080618030403060c08040507090912110f0a032712 68
    0x4030b0480f81c13165209000141030b15510542454440404044001582410b0007500d01401d418140345190002803105182d031040300788200ea20310542034a200180307100402c100c420300b10005040c4a0055102c0c03808130a02841134034201c0d0020502603000407181030500a4a1070300e0f4210780c1803040306446130300542c050300ca45503041c6010b00100390241d1102070650310407006800c60f80c0e8000b0b8101d08010001d000303443e805c0340900c501e04040c44100a031001200f0010ad94404980e8001102d8452021903245c0c0310040c14403552500c58517020440d2900040090130540074014401d0010f140242c024038200c580700c2c09425100c0d04035400040703030980c0100340d0310360b40c0e0741c190101c919156498075140100c6104040340740020384014240800e0102c2086080050b014102d0100103189550ba0352000000c4003001000c14030100e50840c031380242c420710000c0030303141d03554066030442b01c120f01c2c000342441c4104011b0543c001d80d040030050106408021102500c3c0301883c003403031088a07500ea031034030a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 946670233 1250 946668983 946669019
    0x1504030512040809010306090908071704080106080a1a0402030a0b060d060f021b0f0a030e0d06020c160942080a1104020307080a11040b070803010e070804020604 71
    0x10200412459208002121140b4802c42c0203c0015032207120080c00101601c8403030784060700c0a42840342d5079004c03c0c00c0000b16030b20305520bd10240800400078517010528020f0364002e20655107410000699003101061074284640326951000d00341c003101c0e0165042d503030290f902075019448400500e0002e61050700b0180c1003800140320702c080c3c070801c3e6225402d58021180140d01c19802141c01407078840f1203644086105a20b00141424103020f01c8415503c00e80b401001c1e080000e4404510704c582c0360b4501e440c04141e04a0025540d442801040a80c0c1c3c0040910055240a95460025021043d407241c040c5480780344251074103d4041040d006207a90817141498040c0540c440254040702600080c000103260341c0c00a00405c00c040d0420000e295003110b2a540039600410800040540c8400200c0d4841801e890000790711030f0a21510100380070350f40205415020002d1928140712181300070314101c42c925072009aa135500d07140e0880700c1c00010f07100250050000d010a10a002c2243c09000351 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 946671483 1250 946670233 946670237
    0x8030a0e060c0d0207210317060609040e03090a05040c14031e040c0e250507060f18140102070233040b0417060919060204031a0907080609150403 64
    0x14519844042c5092420200d401009640160f10410428152146a000003e05503101245900c460348000d003a4101242540707203003078001000100a0380e100400d8404078540a4810002500346840442c2c0e42d6025a400c284940454000002c142c9002d000b40e5803c01c00030794803060714002c122401d100300e03040903003000d00d9030406c250070b445291803c1500c54400d6001d40030302c070041c0703203800f0800065843c05070072101200c84c0500c40300130003c1c4a04800c80180c0341440d0044c1e0f529a41e0404400400040000e41c06140c10400003a00703a400c1c1d022350422040c010500303802c1481e2842a182d00300d21038104000d41144210b03070000781001400039018912081000c400032101c052255402003540301d0f030030020038140046400d01c0f480303000d01d030000c00f1070240700000d00c6541800b02a160303440c84403643d401c0002c50303403403420010010305405403030041d40d019001707085183e04d02074402d503c401c0803909a911842426400200145c001a942e8060504503025000080c4c000f2244940644010070541c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 946672733 1250 946671483 946671487
    0x51003020906070f0312090f02010c081b06010501024e030106051209150a020a020c060f0c120310052e080103050f030c030f09040908040807030605070908030a0e06 72
    0x35881d12648020140d80e8071440300c40d4035141c0c9905c0c01801d0010005e110000d030741c2c50082e401c0b0014460340101e022076130b02420b1a03840d200b5a1728000c0c0451060702d004060340d10398000c00d49030b82c0f0000155541a508241c00745c503c0701c4000c0c084842600f842c40174522030240001e210b02e070f13200c004a141e4411007442d01803951048205c0020703103505510a074048000100c000641030f0150407101c15030303500100044081c144500d545440141c150a016021081c030035400644520114002c00c11148080000f41039140c80e0f00708503038040800c0c1c1054581c040f05014102d090030304c3e140e65004581c071800b142500d840700d1234100703010302104c10840c4031200ca2074a200700c0408003501000c950341c1485116503803609000e41c114a03100f824140d0107002c0c0d41c1507034010f110a0b01600030210580d400b891a007500310780c60b40401800100035200303110020780030301c3e00081c000c140c0c00c0e00880c0200650740640420302081d1100b507801c032400d150318410000b940c0c00500090041600c540c21005044000820483c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 946673983 1250 946672733 946672747
    0xc06010b0d110a17150609041d07260d02070b09040b0913060f2c0a120f020705030703021e010201060e0a150b0a020604260310090e0c01050405100302 66
    0xb002540f0480900b00812040000144050076070100c481e84904100c401c4607010750745c0c6002ca00035000b04c0c8410b610a580f209983d03510a03080c0c0c40c0c1c00f4001c0410804541e1829901d825040000c440151140d6020583c44d4652081c62000101441103000c55030062a0303941c68005a52115085051034a0340700761100d1980384240d1f0f4001103180039888080c2020f41a101c589019400c403020400300031602400d200d050340c0310b030291561080703030701400045803005400000b2000d400c140c480403004010310320007900b4400d915030142c0100c3e03001d400e580072540001d44910401da919203640c44000e60025028040c8031034402c003004000503200041c0008616103407035614010f414803007100c1c810945603413250103580c901c15181211000307107143d0740b20526248000c10000d444010080c4080c01000507516030b5100c004030401c14580c0448044106034032410040421284c5425500c12507001504000f00b001c00c040e80070510016100050311200d2410b41390100344010784035141d00510a1503801e201038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 946675233 1250 946673983 946674011
    0x1050c0703200102010c090501020705060d060801020708070201080711030406031e060303020c04060b03060612041403070b011502150403180b0f07120504360c0201050712020c06010b0d 81
    0x1108508000300b035001c038641c140340c002821901355400502c10441d203850200300c00d03600030401c00700b0389206581c0541d8030b05244110300094070950b07100a04a600c001604410b01c5404405005014400da84040345525100011036040b412071001c02e08641082008009180c025800100c4255076210500d107039020300d8400f00121400d540c400d41c0036030060610310b642481e05114034800303001200146415400c00002040e050b001d4a00e000c0040139658022600b03003c1700e003a042c5461581d0b40101d070746d20803140c500101c0030040de01c513040c803081215001001160000c05d0040138200d00800e1104076a486440c06c90303405a488941d64080703820400089a843c4002000f841d4488104a459944411030b1170302000c03c1c52801070340390030080107110920451045070400601c1640800b0040c0d6441924035110915a110251642c00315140c0503103005816010b4004070701c90242134450081488100c0c1001c4140d109040780c03820f81d50002c0d0010f101004090000e030042c219403510004200565045c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 946676483 1250 946675233 946675253
    0x3060815010b0a0e4b040c02010e06010b040306050a11090123040801140603060108070e091006090b03010b030d0c0b0c0405060a0918020a0f03231305060f060a030201050c0703 77
    0x349171125041000310350032407209140e144600e21550070b860405c0e9000580c031820083d030602d02e2148070746e0307c2c1e80009500f130740300350011603000c07130744600340d0701907580d80d6080c41d1241d0300c18031007101c02c2c1d4201000280c8200c60f41c401c09820301001c4008520b08030700c010044403540d40d0000011420603a10304041007104805010300042c1c8200300001501c0700d01c01c0f4814800a10041c80f07180b282d44054010302a8070340c08207003501201e03456000c400715078035550180d82c02c0003c40c034405030389249404000240300c0c0d543e400c410210b080540007001681545010f242e21110201c41d44400305241003124000907100300a4254441449048682081d0f2184000782d00c542c82811040006031102c042840104058030500405400001013185840c220300400b80058001078020b1003890340c0ca84030307800c114560419050f11004c0c0c0f8030309171145140c10750b0000403100401c21b0980b200e208100008440d1044004818021031006058206061859004642d585c3c40100d51030103501840303500200180400c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 946677733 1250 946676483 946676509
    0x8010507030c031407090b0a020111030408070308151c1e110a080c09150d0c1e09091104090515091c050310141c1203060815010b0a0e 59
    0x2501180100e03903020014140c620460383c0f4034054413290203001000741c02a030040112003880b1101512130301200001e074010075290701c2c08905040000100010880560000c181c210311030340b0365a44540f50b1010709011080d0758001541c02c03101e800452940c0f1000c02014044a80c481c0715058103058102000d501540050030048618040c4411111f2207841c0c2182c0642c0a400301c03900810401007060002142c1c6180946120342c030b030310f201c038242c0865101e0003209010180c0080c1c4110300d0903581c90402c00214580410051100e60714030380428094028010721b1291608610f00e000d190400e00c003004005c0001500c12500781c07246503200c5800010107400700784034040d9540980002203060002d00c4100c84140c8204040200400c2000351000400740c1010556050102c10740b96840d03604080b40d1301850b05941000340f04031110101c020024448100c010907499540c084c07045950b00c40345565580f031550a004014028036005000b2440c241020300040310292030300c101100c540c600490309170072a0706 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 946678983 1250 946677733 946677737
    0x1103160303470108040b0f040f12021c050c03041e03410a0b04030e04061e27020f040b0f03070201050c0301150507020a0e07050c010b012a0c08010507 66
    0x40d1000900c00c010310380d11008403080c00c09402070b2405c1e070346051040700c0003048100d031a0348000214051080e40407144601d154400504031900c8401c030400395030f442040011258255402a40444032889a400e45184151000096092909019401140071201c08810080906d90380f800070224a0500180708102d001910300c184096602c0d005404444020642014010207940100003c3c40c1c00a0304005658200310440c01c05e031950f1a0440f122140c40052030381c06800d000010426401a0100026481882d025a52880c0d922503040417030003110b0003481c460b204d800c8410444000e05800400404404400ca5450580c413134000102036080f0000d4012058008400c221718160240f1803590084803180c0d9150842d80350030301d04040c0300354010720340d000c0010100e035410854446c4810780300503100d01f0050824600c0e110200510a401001c40501c0c0b9608003c503485c40d65001300b54103502440c64182c2074402c070040725040c1491009071300044980004400d00040c10100038400c040c0690065 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 946680233 1250 946678983 946679081
    0x11040303081e100609050901050d080c0c12010605121c0f0e10050403110f06090f04020c0106092703021b030c1522050607030318060905030a1103160303 67
    0x250021700c11200c82e000140540d00c80c00041c421956110088004a640042400c1d5680f00da0311089042c9270307041042c00d82040c0c10700f00c078200c41070b019040131040c0c501c10382d03a42d4400200120300981d54440d684c0e10780120050728281c0c0a20350f218600c40584005581400000d260466021070906000c12000200007040410140200000000d0841c20100b013100c01603031011f5110700241103440b840001d18461b204000443c642600c031a010f80b82c581d140304000700855955000030304081c1c5140c0502040900c0003140025002c0e11204000d44d020340c050707004000180d48028200340c0201d49450895262040740411241652860351150742c801c410311201d42c07596150034442e401e00d481c0d10f0306500418000e0600740901c0d00d401c0c0c2520015901031501080722285000011107020500b8405000c1a060541c2c42d01402000001400090038a40c3c85090316100070b01180c0e128040ca07000c41c0556002c00034000040ba119400c4180040300a0461a18140100e4107907000d0703030f001030f002d8000c0320340e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 946681483 1250 946680233 946680239
    0xd0b0718091d0a031d041404110111060705090907120e0706090603090f0609060603080d02040e0709080604230d0815010504080304170721140111040303081e10 70
    0x10b01c503107030306114000100340c0800c0c242e6014003021307081034042d80d201c280f2685030750365a81c0c0c641014410070741040300742c0d40d035007444c1c00d2010300c4898002445001c2a005542203841c00e20010b00103102d840f4603a10f050801c41c200d4200511000c02504400800c140c0c4000180029140c1c410314006904000090030a10b181481c003601100306a4090030604d880c007500a804030b03c13000c0300000300c0d0341d01a100084820161409200600c241d81025081035804603645c01c550240b6070042003078821150010081c9c0d40d079060219140c0d052409844801d03000403011400148041080c50075054004407a40705444848400c0c0e498000030194540000d00844240404d0860441d4100c0c110301003807a10324a01703414046040c3e540d202c0c07403058151240ca811000d0241101c14000c11015100d0040b194030809095003500c10300950344201a60f480700d122071a28594681441009060300b0701e048e4090515265803001c1e00c80b000014180300b41008a200444203141c80400e030f1a105a0400d1504100142 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 946682733 1250 946681483 946681511
    0x6090115120e0c180c1e04030f150f1b031e150e06060430050105010f060806030a0201090b0d0212010806090d050a122d0b03011404020d0b071809 64
    0x100e181012070f1020001007444544182e8404582811521880d03e4200c1d28901e60706d41d01b24405c1e940003501d0302c0b005140040403c514002d15210050f851901480480140202c5500704e80d503e091040c02110b40385030409680380a500071001c0d095095000c00701e009184950407064032054140c1500100c0d00c103500b8420080c06410041d0800300540d505420035040440311282e5407000c1056150070412320b000b1b5100000a080015a01c0f81d100c0700078000c55070f41b0a40c0c43e001c07925500411002c54007004c000340b124140001d180d282e0701d4059541d00901894008107507040e9210007016080e05408002d1750600760302046005000f01420f10042185d40f401c4946203080062000541c030400400b04040208650300003141041c50f520804005000903016441c80c1c21a481020b15510514021002900b0300800307a00c54016503205030002d00c5410351105206400342c0085400171740c44a81700107803101166400c8002580100303641881c004410900340c01e48414801a444a08c0302074907038608540c012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 946683983 1250 946682733 946682749
    0xa06110a09120b0f090a080f090f01020d09030b06040207020306090c01030b010c0f3c05010c021f0911030f030304030e010905010c032a030201090501050c0306090115120e0c 76
    0x10140e00034042d100095540e40d00d0010303401a01e480c8040caa014041104110706102000001e80c0c170100c015aa01c2140181400c2500403100b03041c4240810800845c5950000c2007003011110195688000603055549004a00402400c001d03040f5070300780500d000503101088468000c90701a002001070f9500c5c4000103099544c00b4048034100b14002c2e003e100041d25100e102003c0c160300005548010050541c1aa03640c0101c904519031040565015000030710303404c843c1801180a24020b0228142c011400c0c2d17980d482190403080e85061482e00c103c840324090784442c080601c2451806405850040040d1419541038040c0805400000c03c1c0002c2540011801003000428201076015500d0f00300040d02070002c1003009002d101518400c2c4404801d50740c10305c3c89503e0100344101ba03000c45814001d001304217650b400c4070b45601e0302d8003140080c60035106072071151600401183e410380c2000c206071103550030180340c6002d00401055408209142c1e01071030485040081c01072207a0b20b004c2007000302c84 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 946685233 1250 946683983 946683989
    0x3050903100b0d1203090b0403030c0e03010227240417060c1c092a090b0f06071137030b0c070201020c09090102120f1501030e0a06110a09 61
    0x4149405070b142c105480b1004030095076a00030302c181c0007202c1d0900050300603108148006010030340d540304100803d5015403080c002d6a07250340e90481c6c810100700516080384100ca1440d8103403815084081b000b6030030096550000c21001e4044c00b4459800c03000008100358140d002400542d0104085c0090803481c10003548244c0508003c00c1c65080020080c4654484c1004481c500500ba594071900500c02e500220321140d4480c002c0312007000c0e43c2940040218103c1060540701400e1100040c40114601520b880b00c1802804d818036908079108104843d801190103c400800740c0e44001e01c0b80d51013001e0b00c002d003142c0507102003100030b1400c00085510031000d000c0848400c0754405001084048569960000c2c00844a55a50040d400142c0c9020203490305075507c00480010045050419006080c58401e0900c880d004d94494544070782c20b6810481d540501400d02c806103143c598441d820201c0d501e2422801e89010281130b448150a50300f1220120740390200010b0640403056100d4071708801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 946686483 1250 946685233 946685263
    0x190503041a120a05180d050a02011404050d050702120f0c041b020d050c1006030809090106112d06070e1f051c020906031503060106050405061b070503010903050903 72
    0x10300100b1000302d04525201405030341445580d42c1c0001c1a050200300c0d007400343c1c1c03003250486518184102c0024010717840403d60200550030130000d00e61001340c0380031160080768080e0140c000e001300f9140803180ca800c02a42a070f84000510310030290442c1c28840b5103884050709000c0c0400748060030900c0b00362255080781111300383c004240b82c4490759020900c905800c00900d460b80c0c0c2d400d4009055850320815020030110540b0307282c000001c01000e0320042903010307402e40f114070b4180c3e038030041540d195030041d5081403280c010380c02203080a00b50407001070700d908074100884046808008040e1522404440354004510044403000d414a44100c003003407005550307500c0c044c202d01c88110040007805880e889214a0380c1480400e601c160311901a00d01e41d0348050300b09901c0345060030000c1035500622034494001c0c050400003061281c8210225015920043c1c0205c1c03803c1902010310119060300e0520700541d002e081400f190720350302030140c450698003c4d60340325100d941201c1011309200d0b5044141603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 946687733 1250 946686483 946686487
    0x311010507050d08060619030618050f0408030405011401120302010e061603020906040806040c090b180f04061b0c03080c0403020a060819050c040e070f09120203190503041a 76
    0xc001031001640034100035051070540840e032245c0011440900511740d60f014600703400301407000140d80c10f034402d00803210f550280103212000c0782150011543c003a12161940c00f4140f0020303001c149510001c41e0883d124a000041c501c40d1407099140d010400e81204c0b0028010012060600d50309005007a8904000170150840e400c011140c0c00398080340300140d20a01d600401c481005a81e5201070390700512442c000d4030346924007850801d400b5651805542c00c000c0c50240062614202461340f5003084001c1001c1d0012521211f59100814000074422155152680200c2e00d110215841071001015aa240d020107480c40345000742c46d92100804403d807088090000300096902c0c603c0020440c0c006007230220071500e541c440c001c02103200250a5100b9030074201440f10740b418a03402802140c00740c8103d0362031612150401c4034a03445601c150000504c4c810414003402440300382e002c41183c80141140c244120349400d0081120321070000361500e1b00040b904002c00b4030001040c60807003c03503e50701d074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 946688983 1250 946687733 946687747
    0xf0609100806060f060f13170d0516050a0609060510080a050c06070305040b0c100f02130b0315121005100e0718050415063b031507020703110105 64
    0x2596402c00910340340c465070312403441c2030080d141d0314101c45000443d00320307045c3e07610b803086098441c06181e440781c19058030000e11200f400ca50f020400e140310081170b66950b0b1401d031030954496903100c0611010340d00740c021804044001003851241d400024400c1801060910740003010409030440d0360b200c0d40703c542011420070001400450410802d1a0448405840c0c2015080c11509401250005411100d00258880d040840002e21016100300d4850602c007210000683c44164000d0015000c070345e642005080c0400c50454015544c400b001001141d0b114010303400188240d001c02c0c07140321158200581d0f010f6414400d00a41e544440c40b11800c1d11802d141c400c0450220400030846420403141c90b02510f0548442d500c0340c0c0081c1001032007846004510ba5040d02e206580b44034140214030700303500c0307001803110407011031100d070b40e18100c0344041d01040d07400e008610703600148050380340c0903121740c9225031601c007210350340520752686c003e1a0280c2107140109040d02c00308910b506100040c058a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 946690233 1250 946688983 946688999
    0x918050601091d0a0b010801110a2016060806090901020316052109010e0609071203030213091107201f020703200a0f060e06071a0f060910 61
    0x541c119424050001200901100c0480caa8001421004001d0241440300c40920481036802030607a01804000c200c0c4101400e003422042c400c60001401203021503075501a038400d16480c01240c00d981505490040b01c05224100903840d05030414801b080c0c0301c00c10301c08507080041c41180e011281100851a608000100c8000d0151224500040000004510442c001e00300c8108080603160184c0145034101001c603580070301000001d02481d8401c0c680003494400000640201b1244440c0f42020366228545040b00698050440700c807880d6240354000a40a00a114180d001005241c405403a41510314181001840400d0300306811950210880c0d080d40c3e407081982c481c9400d1079404409260340d800207900b4180c95600c040c00068070520801c94800400d9003c5848190844102d44410b840b181c1c40c00d00c1c4003ca0042100281040080c42c1d101e04110f00103101282c0140c20020300c41c00700c0103c8151080c8100d4030000c0c40c070f004409105c80d0b030500f003010765003051080e00d2003800c103402d022079 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 946691483 1250 946690233 946690243
    0x6160e0604060912140111190c03121508030a0908070f0e420a05060f0703050a05042301300c0c05011d0d0504030507050918011401091805 61
    0x15115100716460700300300400c0080a074980c00742102e017000b40440d0405003c401d485d40c20000103036051050b41415030303400c188141e401c0d802c119850b40368020620b03816005500140641d450800c610101d00001150f00802000074040f06812a66042d4a190902a0150420100744c0c802000724035404001d000c0b0300d003042196a480350b01034049503503460a040d0425102e1104040c04841450b00d00ca0880861642c003040703106030031095070a00085a603e5040c04050300c46e0001c4002959400d220143c0001d01c540000c1064103128608903082548896041c0d40113100e5003d802403070005103011210070358001d010700c0801d080f603404000442e00d40c01083d0014811a40d0341054043c0c0d105070549406004400103803040780c000c0000c200c00c4641b820900c00e10740085d61a05e02c28071880c00e405041c2c40c032800849045d20781c0400070388010f40c5400c0500001403405000034841c80100302920280c0682445900c100802d40d00034003a65500d4141032a0442e055245942050820550203201050000034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 946692733 1250 946691483 946691489
    0x90617060d112d01090305030d0507090503100e010515420c0712210c14010c14040b2b050903120c041505160506160e06040609 56
    0x203880c1c020000c091821164200b40d56204580c4800d140800044081101552107554030f40701c1228030085203000015100d40c8480d1000501d958030401401129141942016400030110704147c00b10070b86810009003005420b4158411407507903140d200d040032809020740c079040020f0300310111561410b880440c2010326520070510302110603c07128040f0610042080410b40c100e1304041c4849440034200444c2c0340c0c04503030a80c0c80c521408801003603021501c0000e07400b00e6804020000150b0b102d284245086056950305014841c3c61541c0d54003103464040800c548000a000000b89000d5004010701150003280b46001104400e2000b0700080c04820100c80f0103131112909400c00154400036500c3c00072140741c05039221030600051110f1b4130b03400070240076100449500f0314840d076603c0003821558091881122540c0c6001510407210300c1c000e000428401000030b24a9541c4032840e21100d28001b01555a8001c40144503c10a8900d41c018400b1a01c0a42203410f0b9161030f1410744001c0c8020a140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 946693983 1250 946692733 946692739
    0xc011505061b120310050405090c0a0302150c010c0309021f05030a1104080703110112020c0705040218031b010f050f0318100908090906040207020d030806121c09061706 74
    0x3070144035490b08124080444046118a41d543d01e001540c1e55802c10325445502c4c0224100000720701d82080c0820000a90640034100305c410500d15020804a009440701a10140c6401c10441e68055401c1c02200b0010150340c40200343c088252046c45078540e040048012000381a4204001083e030090840c6d030070080550000c20001d00102061603584115403014002e88503d080000c200816400e10500c00d0800741c96403103081550208000c20303803213425640d004540010106115514080d0301821882c0c1007062550400c82e60300000c689064280b881060f148003d040f00c165072983d000c100d600e5000e8080c039043c0d04190f5010140c40c01c900005d8140840b2001d01815521004410408456000e81d1100188510201030504101c903902807107000b406a4114030000b48981094001c9074002c990181041403001c40549003260401000341c5803607841150300d819001e40d908100500391802d0000800c420f091001e0b0100a0052003959005a06004103e1409c2c0c4039000c4031a012607100d2415 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 946695233 1250 946693983 946694017
    0x19030503060f130609150b160f020402030a090b010603090c120f0b0c0327101a041a03061609030b0a06031e05010b040506100e06040b0304080c01150506 67
    0x81000120a006a00b4460740c0280319800314100c0d040b0250400401c40e4030300b84080081c042c8841110f030036003102d80a14036401404000d109490210101160205030068508540b10403e6a0010b0181d9100b034400d481210b468400e540203100000a0440c010801804d0411240c691a91400c8450026120b8020503202421060041c00407544002403e2540144926040d2900b64401500e80d00203440b010000503030480d408031001501c9016000001402008203040115428000041d00596900030307280440420244241c0e1a540500c60520841e44503e01000b41070105149c50b00c0401841a646c4c0410f006408581d44d80041c0c421007501d0308500060312664450309150050900d40c1e0006080c07e0503500a540c0e40c866680403e002640f189000b8014402034a00300b2090303890990701d4a47c0007802600001c0301c18010700840d28a81d9001d00360b0390400395105840009600219012b5480c1d84c400540c0700303190030742803041c03c0c0c2c0d6000c0d602d5640b200504200101d403c60040d40e003040c03901c1010f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 946696483 1250 946695233 946695241
    0x9010204260712080403140604080d020a0c050d0905040b041107080309011e0b1206010f0512070306020304050a0b0f0709090b01030e0d0207150e03281205180319030503 74
    0x3801000064044840c0080e005403c600d009030f101e910521098500c04da9600d44201410004a081401582c00c205030a0620449050311402540104416014001d1700900b500000704103120f04d009140d000c0e26043c030003c1c508018003040e101c5542c20540300714035003240250b0001d6600180c502c0c4a40008000783c495440013001030041540404802442886c1041d1903a500d40780e8000c11498281074414901450b042c210741c503070340c0301d086c000c2c82005400140f0a00082c00c0c081c03801d03505492200125a00141e903a2201801c80c0d0054806940d00d800c0100d003c014026604042d5800c404020480070341c0d0714040da0f00500c42003250056520990315090054080e2f0b10076006020600c1c00001541c680c548070380c0c3d029690329001d2080d6031220700007000612625010340c07003451005c00c014000c0c000d641c070113070421440e070400c80b0110314090782c08091400c04208080a5441130740c010391141c682d03403d05c07941066515035114a099100f0360000d4140d0391508141d500740e0a2103945410002d8880d00c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 946697733 1250 946696483 946696559
    0x50d080f0f0f030c04150813030810051801170f19060e0d0e03122a0102210402181306091e050a120912151409031209010204 55
    0x841c8490034003034107101100b1301045102e9000100115420002100074100d40c0000a48403c90102c4131243e4580500000341c002c00d020740c500e103030300a5042c3c40510380b0540758800103608158900200380c40c101d20800600018a418410043c0c650380180140181451007000990b0b0340501600076012038161084102084401d411006042c09410203441c150410540001c0200341000d1410f8804d1150703008071385501e603814080340c140c803c1860340303c44d4400c104100e4400f001c841481901c182c1d03600704181c00041868905a080d01d9109a6801e41981403900400c909144ca100c40c0b1561410324005003c141031180c1d00760700c4c00d554450310204800c002070600702801501c0c0c001410703407555403e00c05d108001c030104241000354400e0680600c031540350141100c8904281c02403503249040c41607600045407159107008401144108003190701d511140d04902d8249050b611103416a00101c0e182a642e01803021503030344032060030021410b0520380950556149500c10f06911061484110091004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 946698983 1250 946697733 946697737
    0x509130c022127062a06040f1a010f051002120c07450905011a030d0215010b0f07050a08040e0c19050901031503031206050d080f0f 58
    0x1212151040309885540c0700034000b544a1403555842000040080d0160070300141e034101c49482c040c00050506880c4003078501c5c0c0100c0050300c03100402510346981c940074420400a486a80300f85241410030b071103031500f90780c42c00c000403a070100642c1c5040107100d1090807650100403941c1c02c486220b9110b492101c01c0e8203220034803182c2c07a00058001074860f5601c0700011a00201c6002c0101e5046036101000321003100d501401c02084040c11648400801c64456030b40d00149000f2050300045070701c1340f640c0b07050846114071300300d0103280340c00110b10400c0c0c0703070502016595000780e00281a0064406040039041d5005000c6d4665a00011981112103c050015035060030b5010b000c449080d003e43c01c0540356600184110300f40c0f10244000600186031440989040c000503502181c0801d650b40c90a8840e500050509810141d69505170082031f0700100b60500154000d468201e50f8000c0f564440050341c9890f00064010a500c003401d90000c1c0400c0120340408080c40703211611403555075403840c2c940c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 946700233 1250 946698983 946699003
    0x3150f090a0515030703081219063c1802040812072d0305031306020706051609030206040e0417072a0311090a020c0316020406060509130c02 62
    0x12003901410412102115880030303005442103003100e89040720a404256071a042800010300000f010700100300310741c8813040313401d400c80b072a032984241407082c551040e400ca69243c0d100f0400c814031444007080390402d400a129a88500f0264403e055002c072030360324800301b8580f16214081203007d201650865076030f8180c0d000307010643c0540744000e0820300320001d207030401d10b81035520701c0f0325100303541c0c901c24180c0c0c1030034104030f0002c644980900700c0d2701e0a44050708002c2200e0082d086040e41040000d809200070102244901c2d0001500d0400c0740300440702985441c0104140241f11100f400583d40e10f1042e038085581e100305021450303a403481c28202c80da8508070340b208544e101050321802c00c00410303258550310190280301c0400d907801c0c101018902905104c0074001e6400f0701461501820720000c4550701c5002414050315154036142a00e1441d032006102d168032205042101c0114903040c0100b10052003240ba120381814580d400180c2040387e00e030040742a003075940e040c00c44018001d02c110740b80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 946701483 1250 946700233 946700239
    0x9060b070b04050f07120b06010513060302030a061a0d0605061809040219080f0d1b02010521180f0a0b07110f19110103090503040515070b180d0c020603150f 69
    0x8a00d68a000044018a1b8507500311400e0f50b10784000386031548940c050b61035914440d1000c076800c07450b144045d4001c0d0302c0a810b0810780c54803410b01161082c03182c07030b42c1c4140070301e00001d003035a50b0401c80170302c001ca50b078a40109104036030800006c84082240102c42c60641c10448040c5120348031403001a000c9034850945864031000868005400580443d2899980e40c40c40269000d07d40c0805003102e0b524601d000d612420002a07480e04095403141c0045e03d50b0321803a142c1c01500c0c202041048211950441d0316800b50207880202101540050040310310f403580d407000904804010350303100303514810001e240c01c0c10881240e01090300d03500204814403080c00e02c7d1b81504c000310071000031141d62804c00c0006496810035800d40119551107032180c9a2404e42042c05075003040c0c282401c0040c801ca40043c41c03140c030201800b84201086110a2080c012a5501411100d41039040c040906104640b2015804d01c07c1d00d02519000d80c40b00400c50354440e034400b1107655409503280008017000441d02d07007150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 946702733 1250 946701483 946701493
    0x415030e0703032307020a0b0d020d11040914010e0f040203030d051608090a030c1212020c0708070f060c1101141b060c1303081614010b040609060b070b04050f 70
    0x20300da00180c41346003003101d003007050f41e10040583c000005442010002500504084002c22615400d50054108801100005854442440044d50660b00c0c508500100001c0011341008034466a203c3d994400000e2620718041c2c1d8941800b18441c440d00414800c200d1004400040c1196024030888010225907001002641071203807400c203c0d028014200404201d00707801084c440100000c000390300503032641c1d4003074542e07c180e95010f40c107400307103038150707050004084800000b0380290015010045880c40180700d618904490a07181c0b05581d4032031580843d03010424172039958000742030702400d80c100c90b044003500382400041300c0d01d51100c00d44091a120108050a10107602e803003010b001102070b000c890280d01e03180c039550120300c80c025406603a0540300c90108001440c0328013402845542e150309080e50105500c0e01003803500224480c1a080c0d540d140c504805107051b00c035140c042c0c00500c80801015040c030340c1c2d440d2284100c4038058644c0c403a00d0002000c12908004407024404040180c072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 946703983 1250 946702733 946702739
    0x2a03060f1203041e320a0305030904061a040311011428020f0a020f04180302060906011a12040f06021306120b0d021212030c1207140415030e07 63
    0xa8882d04180104c441c0410b144c180c2c540052041d05030320f42030300d41d01d40c0100460904181203600d50210591081900d03044034181a4070343c0d5529030307980d0080d07001e1805580c2d0391900c42d00700800c42d60a0b81143d82d00b1444205036050301e11040090307506490340058100e02c801034090068502d03452080980304031319400140a010281624806500d0403407034040d1104084098a00307a0300d800c0c030711910519903440440501d0140c0740403042d100e9005005040050340e00101800d4804441d52444143c0c0507034020f00a00065220401942e401800e142c03400d01c565040101c0002e0040c8a081a8000f105c0000400b003000d000c0e03800d031848111a80241c0456030356107441d10b410342d640124030418001c901c821900141a90f284c0c0290406510020320144020120f40d007000381c01c804c1e1300ca52030a28400d200c03810404941000065000e882c0114a0340d0311060500c80200d02d09500426131001c0040e40c8002082d241c0004007550156018480b049402e0fa00c0c4003011401800e07003950b07a821a2013218000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 946705233 1250 946703983 946704019
    0x130506060a141306090c1d0406150c110a0311180c07032a060e01060506070f0f05240609090d02120a050c030403060e01051e0106030207020d120f082a03060f 69
    0x70300786030b40100403064421840001000221842407103140d0ac2080301c03146c2080350382c3c420300c90382d00402d1013205100004551007010821040c0c0365042126840c284160811151910300100300c401c0304021600d000d01e28100b00c0045030303400350500c01820320401f403103111440c0f199141c0f00504a41c414502884607039590501d20003030b001100441e10ba41d4a010004565820038104440c08039801007103450842030640d40758484080b041b03000340d5050007004807404000021025024840d6140700000c0c0b11424880c04000e4001d0011b000311031a5845007840103511600414030944646c0e19161782600e820304844151424840c804d201540c178000040c006c0f08004c0940d11035420404640002c00060380c03580408200400b4102580c03070780c3c0820f40d0042100c0780c070980003400c1c5203101801c210462001603960307080c4d21050f80030300d80124543e80c07400d0882c15405039805a00c211208141c0311582c805040c3d0f003180003482030030500010340010000301c2980720342803601c04900b00a800d4210400c030003154 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 946706483 1250 946705233 946705247
    0x90b160f0515011401210605060d09050c040605130e160b030906090105060d171201030f0209070219200a0f06230d150e130506060a141306090c 63
    0x103010b203054407480012420200d0310502e06180c2c201a1203450b001c140e850445180000d0380c02c6246d00381e07600c591b4040f4036922004041c0411400c0b034100480c00c20000e00d06507042c281d00303000b00c0d4002c1d0b00c0c4c0b0504110365a20140101c6580104003800201c0343d1060040341e040c020740364421101941c2c9000e00141812401d8010f5104880d0002501c00781d84403c2c1c0d406003628001d40f0075a078056451281140820920040e1000000f0303ca050301d407a0000d01050041c104800343d01c182e40041805000c4410340c10a04042c9070311101d50304c064482c0340e48221014400043c0454040e00c800e000383d080d0017096001c2c0f0318951710002c0c002d000d605d400d940d500b082c544141c120b003d101e0020381084d62000d07004080442c045c132a810011b44039800c14211081a20042004040715041c0b0005c2004c0080c05030740e2000e6140c0070f990b81460100441005040036864202d010303101500a82c2100c00030041c01340f08609081003410100c448224100e0010004409080e407600207080180c07070840b1145e1140c0e0030000f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 946707733 1250 946706483 946706503
    0x1703042315010e0915220f020f0d0305160c030b16020f071508060d12081005090f0402040c26041205070302120a050d060b031f06090b160f05 62
    0x4020314203aa299810110070100030784004136158069030807904a90003951005901920b642035460105132242c911896028104800340e603030081d00e00e028015810813500d03521a415055500c400c060b2000e0383d00520a11074100b00341c0c2c0300c1c840e0a42e407a04000d0031810780802140c20110b43c049600b4455205441c0098052803a8003620820b100107041c0e80c0d0110f80c000c00c0b02c1225800c020400d007105000e560a040040001d540a040e203505100016001c3c0709112404030113554036841803a0078080000b1203102c0b50015441400000c042041302003a517032080341c1c0264160340219040440303560941d001400010454110101a0600c501100c1c05405062246008a1010590311401c000940303080c80b4482d070140050700041c90071482e0100d900c0003007188880c14a00540f03404117108401b41268880c2e04600c075410030020038071460358921891445601c1c0886044564a45082e82c040c180c001c1921030348040d070700702180345906041e3f6003d07200461504501004100007541c0303001521407503120 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 946708983 1250 946707733 946707763
    0x30219080f0a200d020d150b011b060b04090803040f0b070507080d0e030c03130503060702010642020303090d110d080a0f02040803030a11030417030423 67
    0x445a4080c00800180342400c854000c9440c07040d00d03441c4900c8140d500c0040b01c843c0c0c0c12299689401c40181c60b050b85130144540141032401001d1066000305003501d0b202d03205141040254038903070201080303030142141c4180d8003440006118a440c00440c010b0b0003552405403614102000f0002032209104d00d0854582c030804150b0500c0d511172005841c50300541c1409441ea982c140b04407081220f90f6406032030009070a100301c900740400c200060f49141d10805400010011000c000c02407030a040049640225160000780851030070101219851542c0c592000c3c481104000090340080d400701e50100305003980c4401400c0300165807400ba5480d44265480d04e514854400c1040285115402450712028144050060703500565021030341410050030400c5003550720045481c1c000ac95100400027095818007454403071400c00110012221310070440110350004000700000565509452650808203401050326601c2e03c0c10301f1201c1c10040490000f4007018206401c80360240000c048901c241c00c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 946710233 1250 946708983 946708993
    0xb0406150201050903030c1812030a031d0a03021c0306121419020a05130e0d0c0309092f0d090506060406050a0b090f13060b07060c1d010f0903021908 66
    0x1ca00d402e03541303110031282c55245540c10301080510703981c1c0e14404880c8c6800284210b154503500c444042c01e41d4080075081000c2030750b07010b41d00c081da02040c202c070f1074440c1c41e14050700c0b140f005a113022b503d8492200c400c9000754504002400c06038000c1e40319901500001200c6d1082d03070b81d82d140218040301181d103003010749c2c45910f11040d920710a04480d14030450340944001ca032145040d050000c0d04070010071106c00e881d1a07490403444041d042000500701400c680e02d06c2500b41d824180500380b0000b507001509800d0601e208012179a1041c2011200e08209102d8454024504d03100c0c0c08290080355000c0d008603041400d20001d1100000311180600d0040310304000d241c1c8d07640104007a81003644a101c000201c288003030402d070301d003a003800240000080c080072040c0254080480440b5001d4001c04c103400f80114410b41071010504c12801007021f40e00b4400706c0c10915020130340350000010340d850704010f134070301c000303170201c4c1c0b0400b40d0300000d44d0b020301101001107051506000241c943d008001c507503c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 946711483 1250 946710233 946710241
    0x1906080708091b060d11070501050f0121030e0a05040504230c0112270c180c08041401020c030c0318100917010b13020c0c010305190e010b040615020105 67
    0x443c441c0a045481c00108002403042400d000064011818841035559100c2c8840102c168003402421154482d60002585142a61002000b0041a000722951440b0310500918044440c4010a01e854050074140c440300b0914002842a61f0b55804c480c0d0401c1c2000d0502042241c00c40d100000c241c103d0f00c13410f00b10200c03040c031640d9a544840003140060001c068541c290074a66024010340d03415990070101c942c03207141501c1000078150008565078400700b00100582e900ca040741043e0800844002c1c00b090306600340040c003601c405031020740305583d101c100400701c5100350304850300313102503806581d1100440000c05440350055902c0c1c0c0000044a08484d0040c9800084036500c02e9564482d00480d13400d1078402c41440300503100045240d03588060400090792403580410b02903903409809680e1b07100c039440241c00c04d83c4244000c1e05040c1448244642c0c808090130400c40713501c00c0c8000044002e402084c0324007410240406c0c40d08603141600100e100b80750780485c1c00795044107030020700894a07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 946712733 1250 946711483 946711501
    0x21c0e0a030e301213030c05090118050915070903030e091b0a03140f010303030e0606090a090609020423010605040b090f0f0301060f05031203090c0f1906080708 71
    0x207040501c41c40c14083c2d011070030b07070101250010760902c4520703100b1200103079800100d60759194804084501d0128115078100304000d09418010080d0500b0b8841d005654500480001b00d8200200d0301e00d01c50b902c0d20000303941d05408001c640c05100082c0059181800c01440150602d00c241c0410790004004402415041c01c00440007030064030b0480050720807084442c05c0c01143d400a0304100c0400d80c407070001d030150744107404a0b07500a100b136003a552555403640c0741c090212031036030803260181c1d0041c104010180d5104c4110030b41c00040400b02045131442854030324010071038510001c0d40309180410005107040b010054107408841ea80010300c8990701c9003019038807402648280180c5410030441c400c003508014112000c01c445c0035013469141c0303038184000703400e5420542100c58524083c1408020b03901d010094450030510105c511843c50805240083e180c2c0030108010380203480400804945072103041b2448800029100041d00d001d4032280d0060a41405079404400140c0210200b81c10351 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 946713983 1250 946712733 946712749
    0x60608010f1109010c0206040f0e070f0c0302060f1021141b130f0515030c060703022104080f06060306070f30021812070315021c0e0a030e 61
    0x8400b00042c1070504001070011105207400c51402c98000ca0180400141180c1d81040c8002602484204014915103400d000389410580240042000745a807803540200f50041896904a44a061001711954402c40c3c0442242c844da40300c18820350703281d40d03441000020348082c00700d4588100c003070b0902c9000d1494401c5e030344c1d0a500c0540c04000b200740400645807400800812140070342e540089003144203407224800f1118120f0314142c00140802d146103281c9001c0c42081c001c00c104941003400c2c90b100da21f0080d80c443c4180b11203061062400c0407008000001c0098400a1141800329030410021401c4591115019942180240f01e6074001c02c1d480381c0142020041d03840b1542d9001c0281e4071a82d00e0b403140160405170100d00d075402d41c0d03070078000385500e00041c810b0385881c681124490310188140800088003000c4e1a40607000f12405100040ca840070807000780200c041c0258940c001e4400c400d5031010401e11800d011440c01c2c02e100810315010443c000424080e03200e8036001c00281c002d2100c3c2c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 946715233 1250 946713983 946714001
    0x180f010b0c15070e0a080a03182607050303070503070312020f1210090c05041706010501020c15041e080d030606020c040f150b043b090a020904060608010f 68
    0x16800403180a5411a555159654880f40c280741c008071426000c000309401030362580040410707812810140080c0740d0064001050b48042d0304500c400c1030704c0c102880c1d01491408241ca00b51150b0b610380304e2014801040200c0207004004e083e03d84ea418140b80c0903030b584d0b2240c40110085165580ca0000b440050320964440031050603910346070602c01d000c0c600d1a144010203007600d40d03000080c003003001c2146100740c0c82c00183e29180c1c01c1d6103d0402c0c0c07000718a041250900082903108400503c802c0c3d9001c640c4203143d0324242c1e040c0c03100b4010355601d08054003558211454030041c41024840f00f21110052404441c42074003079541d000c2d2803603021003e9503c2c1e40119800b41c2e0201c03c07030207201c0c02c09a111304045c00480703c00051109070300c0308984041c0d0342e0341d128059800d0040740a00010411018806007940030204041d510303102985100181c5007150421105402e11100252280300b06001d04541c0340d9000307088480c00d00e85880c090380140030500400801d50709e0118012070043c02c900c00c451013 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 946716483 1250 946715233 946715257
    0x30f15010b1c11070b0c03011a090a05090711010203090d03060e040b430206090712030c031403090f100c0914040b1e011d06071101020c180f010b 64
    0x4009402c0c9000c041c06000e0402010190208000d40100d140e8100c518081d44000540d540d49500d032032010560b0100d05011001003640403c207600e060396030081010b00b224000d07162100d00307039155a011345002844550399040b5500020400c004500c1c0400d0310600c00c0d10380c1d20100501511038100010f8000304842c01460842e00c1c5000c1249401d07010414964885084c0b40400c070024410424000ca80c405815229402100741c0c003410025011b01070581e000302c4810003851070034a4581d400032040b030968006400c1c0320954203402d00b030620030304040b0700840c2031020b03990b40c6e4204035420903610303081307420410040e0040e000240103440c0c040c0074501d140b000d80d07900c0c0e151041c181a030701050032003089105c81d0f0150340ca19035001c6c241ca44110342e4400b24042e445490030300600800240c6003090981000300c070305031011600d0180350b5500f010307501c203107070070507210003881001c0401030340350180354907020342d014102140c0ca5103801440006030748540c0f644000460b00e039a840c100585903004008072009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 946717733 1250 946716483 946716517
    0x705100305091f1b0c06060e0f04080307120603080a0315150e0a05040908030a0b0f06070b040c0e100815160c0606030c23010c020f010c050309030f15010b 68
    0x7820074020b4008000d05003200000400f13115240d0818620003021944da004070f034180a861052144c03070b200703150040400b84c09241807850705410040c21000001d100070032000000c0040385002d40310f003200c042d005620341c0c1e041180946034145030940780c208601150000382040c29035220600003025080031a64003801145e0ba20710b560703200392007449944441c0e6410840c10113001440740e44500a281c0c140340a01c90056907401c0c01d10000c402e441d40000400d00405480c00c00080a450b80d1040fa40c00c0c54008250f241d6645a44c6030194203c10a0b502a604500c0741c1810310041050b0000400100c4428204450615060010740301510703104941450142030b20648903644030707005d41114072030a40302e01c10005c0c443e5200d0352103522503205d50f04030591518240d2203002c01640046c210444020090030004284951540050100b16001000a040240c84c02220040110070000c2c0d80303910b58000e090b2440151030114441c1d0320b01c200d140000000c80080d00010ba0700110900301d805100f000003428ad = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 946718983 1250 946717733 946717753
    0x6121b03050612210c0f1204031a0907030b060d050d0818011a060f19090603060929060c1507020c06070b1f05060d0504020127090c020f0708070510030509 68
    0x2103c0381c01c000105d030002e008405510740c001c0d0301404000c202e41201100c16466038114149018184a8082c01c42d00d000844410300010840c001882012240c2c080a545403e0341c2d00b4000c80ca410f401102e000304584910300f081001d8580204449100710882501b084240c50846e8040d0309071405c04040301c4079009018010801401d07c48020004110070840603850031402e0401485154005004100002d504a00601019616000303130f00040800c008180040410098903034000d06100d1000085000d01070920907013600d464003503e201c042c044090b01c03160400b1a071400c2102d0f00803140c000040c010104c5034282d03864008103452949420003440130040d501c01030074900a245070103140400404420740025280c4c0d40300001d00c0f005580304004209820309200140070120304a41107404900100c041c4c90000e40c003403610320b00300d610001020800f4117440310240e01b081020708050280b4001c2800c085500000001c64904440054561990003514440100c0881c2c02c01c2c0c43c0302000d0781040d000f00b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 946720233 1250 946718983 946719043
    0x301060e06060c07031a01180b030d0e010e10050712080c07110406031202030d060803031b130b070f14010c120b1f09060206150102060106121b03050612 67
    0x64603071180300508035101e5036100c1c1c41d80d04141d44d088506c100980045d00042c40030340400060364806c6041c1c41814071900064400207034903519040c525204009840c0a51800340e81b01e01078007041d001003d4942507000303511010080031503100350804e641e00c018210041c0c00003403240c111903100720344000289040c500c84e0b584011800303074202c0e0740940c031a8603040c000c004141c81480e045400c0281788c00841d92032800420142c141c5001d41c1c40324605070000d2080140c210200455000880e001c4c0c0784940c0c3d0786c0f0072001072080e070000c25002403082407004070728082000700d1109000d0703459008525902e4503d4090480b02d0980b2000c0f225080001d000c00c0d100401c00302e083d0008840603c0051504448403100807a0101e240c1680c0703500340001e011400704204117034041c0945e50304507160104604400724010300107581c0350f5040c07140c502003107c0a1000300c811001030b40051a014081002030340802c2c0d00180c010042c00051740d18603c580c03501221960220400292441c1e201050010134075000910400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 946721483 1250 946720233 946720237
    0x6030203120f040611010207170304030f09030c09020a090f0b09090f040804030209040317090c010914060304030806031f0b010e0108040f0b1902040e010611150a09060e1f0b0301060e0606 82
    0x3105c0c0c0340e40d008e10000002804010b07646100701800c8212640f24a020304000f005000498810418845903075400d0001c280a69552000d55000400140c1d6036200300c6d8013110b0303201169100c050b01c00542400131852003103620041510b114116285405138940151500203000150343c014031482c0100420801810f11007049a442402030409008040c0180c8101c01460310840b140e0845400803010035007070390782000c0004041c2071005040740200c60101c010408038440075201405200c44800014a161303001c000f141025998540300384140c3d040440440050030b40e84030241d010030201440361242e5441502c0c0c0301c1c8500e81089640051403c2030300e90406691029003040302c3d100000034591042c134483c1c0010f100415040012040c5585002c10042c200080903584114503080074100940742c0c4bca60b0b80e000d070810b03200d400c00140c000070f81c90a40001c00c0303680a410010300a9284011680480c12050400c1c810104010711030b41d800c1c081014200e4401e401020f25020005010030018144840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 946722733 1250 946721483 946721507
    0x423010302040f020f13030605070309050a140f0f010e190f0f060b0d0803010305100b0105070b060f0a0905060a0b0f0d0207150e0304090b0103050609071209060e0106030203120f0406 80
    0x24005140180f010060081d6031b018014002c28040300450400412a45225255010200f03180c00c2151000941e07900d5218050f4802c0074010049000490a0961040c03000e402da006454085800785400c02d00c0241c0a440e0b001801e401601a0401d2204c0c040300c4c80e8001090f60768000c155015090381c0c1d5440580c011011302080e40c070700380e403200e50940c0c50300d03a000420321041c060f05006403603602d9447d11a15196441001020341401d00d1a098200e0341c020003036942c01075000b040d10740305917507600100b069041400e0740b03d50720264070200001c030040982d1000c0e004820075100341030003039158860980f41d4403945071503841360f08007000175172420101355010b401d00c68422080303480c40d10601007001003542c000624883d010313040040e041000440c01d00c680c4040303040a0074203010510b03015000401c02c1e0382c01801d400074001c180e458140c5a00c20b540c4002d816030740c1f06900304151a04031804138000c0006010882c080c0c850309224102000c68001a08c248142125006152504180c0d0071a85603800317030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 946723983 1250 946722733 946722761
    0x7030c14040f0816120b0c0c12040e06010e060a120905010219021e061503010f09030f020f06090c060a0516060902040617060a051806090606042301030204 68
    0x110025510158103004000070b00848116010282c180340301c450412140f04c1c1861000c0d40c900c00204a0007a19070280800581c0202c1100641c1c0e8034880c400320740384510400c0f511a80a4501c140c0407902c01d40f07000c1c0c0b00f40c4408129003861a81c40100554019401c1d0072601d0f804401804890100c6111301e1140b8041c038440d42c004184d0a10135502c0c1401d90704040e48588540384052020700c007c503810040968440310103282111410304c607900250b10364002401c030518201c6c40c8502c05c83d1742d44003504000c01d0840082c4041294010300e0800500035150b001c800001030062584190000030009045401651448040d04500d0700a070100140d61303014504d1542800024071030442100c0c2e10843d008141341c02000040f80044861040200716174050b0403544109918261003800614000750035640461031044c0080c0701e4a9030081301c0e054851381c50207207403e03105100c01c0000c49400462864010501035400340051100c440072103101c659207051000003c1010390041025142c03541128514212403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 946725233 1250 946723983 946723997
    0x81203160e011d0d1a180703150b011407050f070914130203150705040e061806153a0203010509071209120206150f28080d0f2607030c 59
    0x395070b445c255145aa010051210350a104103d100111025503000c414400340140140d039082da0f980c00c1941500103a6480c04070b40c1c582003184241d02500c0703008000c202000840780caa200528106603030b0302c46800811203034014071000150203039603801502403005041410380d00c2d940d61b00c40104040c400c1d0035001e0764144100114140c049000001890142180d80c3c0e460342e9441c00c08045c49112030001d00400c3c014051850442c1c1c48a4000c50302c0c1e504802c0488002c502c00649d41401c1c20350740100501e0f6840000340459030990f010f42c4202003520600b510300d09075264012a02e410302280030900c5800e8015a2003030018281780d110300b1a55070800e004920000e00c0c00416168001160100350058000d40d10282c144040840b01a40f0010750a1049a0034001d802a020118491030801c0032000701546c15001030350002509182002d01400108003203c4800b0130f00b035001405065041c10800104800c4203007009052150b1040032109074104031840100c0c1c89000d0110010200e400071310080141c6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 946726483 1250 946725233 946725259
    0x50405010f0b0c191523040b1906060302040509060f0a0b0c030d0c0e01020c090403021f020c12120f0402060a140903010e0c040608060f010504020901020304081203160e011d 76
    0x5130241030b901e006400d4000c0d0041e0100c03a0a04568858500754030180010303000300c120000009031641e01c02e50001068460342c480680080b15440d500611000386420004045106907242c1d020b0000c07258200c404602548441c0180f00c600c845060850f40c125540d41c5050101c003120342c00070f02c0c0300c00c40d100480c0d20348501c80008104494489030010000341010b80c441c40c5070360303042012540041040743d030700095052958001c3e5540e00c0201030907001006c4041c2d0031008914640c159030700642c41d541910450072280f00c001003658071040805c4800298000450340000e04a100304c1d102e0395014100c00d240c041c0741c040c195100492139100c0020340d0810428800e8649081c003900591008000003004244020030400081c4c44464102c1a90350b48000100410f007001c014040b411a0016100141e85514060040b1f0841c81580c00c61b000900c9049000e02848142000462046065250500c10304203141001c550382e12400c030111340018000240300018154500740d800f481074009110b01c4140310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 946727733 1250 946726483 946726513
    0xd0201050f03190605060c071a0706060e0621060f04080c0a2f01020c0607050a08190f1704150f0c0302030609060f0315070215011707050405010f0b0c 66
    0x70045820702c202c8450f5030454140741c00c003030140c0307006000f0845070103003003150304040590341d000c081c0310701030f1546811100c54a6464101044500c3d29400c080e0500c1842c0d115914071515410030740303486001d480b0b000d60700048410350203c90300246070420050800703600c07070070920362120201038400c1c0d034014070421050040007030400c0000e00040c4540221010ad540349007000d0f43c90380039629010206442e04034403100c940e81c040340c06c0307190940465000f926040e40e8103120b0b1410241c188002c045920000703444844074034030800014503a0311542d0750413011003a2481110142c1850450164417030031000414002000242117244181c08070200284540805510406031204640b4540120fa400000d100a82c1005408254062001d0340c400440f05c000d000401e0340e48502c0089043c40790382240215503107510a00c0f1081d86050060710f04641c55031182c0780f071504003800f0502c6c1081c505ca42c7c1800141803c103070083d1812202c0082c0c0688843e49001c8070400c0b079600640c402c1a090184080402e507280c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 946728983 1250 946727733 946727737
    0x10303050d0b2e0e010e0a0501080c09040203090a120f0905040b04140106091805070507080f0403051b090a2711040c0806030607030504020303090d110d15150803090d0201050f 77
    0x880d60030f0759410110102c200034080405a0780624104440c0160610356031f100e0340540c0f8100c62080c64504016615000b20f500070b80250305070a94014000001d105c080c05d80000c69001e000e01801298000c4a440c02003601c400c04e5807101c030008214a184108828a0315900c01d1504c0b801c05000482e24002851030134407500c400740c00c400003042c0c2c111713020302c00300f9503407810314944c0840c25200300f115080072070000c3c011340999031004141c80d800090100001030341501360303402141d10004461083e0300490507602811a800842c03402000110005140111680070702020080e48600485071043c0b07106c0c14410300d054030344041d036a00c15100d051b0324842e1524466202804095030b80c03a091420840101820140c0c040e181e0400c160509040c000580d030b01000b100d250950403100132040c6045481c014078070519005805501c4080c0700515001d0001701100c1d40b0b610890070200308004040186c0d4143da00966008140c965401804500b480e1f00f480c440c50000c15005050041c1080032000d5811216 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 946730233 1250 946728983 946729039
    0x15031c030204060f171605040b0c01140a020315062d04030302190c0608061c031101060f030c0b0d140406020d050606090105091e030a0305030f060603010303050d0b 72
    0x2907000a04000503944080d82401050181c5001c400c00c0c0d0320031207004041c440c05400c003a10840e10b012842c0d00d140c0070f001114001e0a5034038029031141c80600006000f4120920104080c55200d00050700c06501882268812038001514044100190b0305100c410b0300701114101d40b0740c0d0103003640768420030700040d8002c0107421152460b58650452078000d003024010b004ea80c050b0380001c401040000c600780040000d0360f40785d103006059680c4500c0003440d8a008143c0302040c121030701254100303041c0e100c0d19103e4814426070003032040981d5025800d10006007880090301d4015816018452002200300034170180600542c0800c00780c0784080711560000c8140c40440721950b0000d01108004214068285c0c04041203030f83d20309211003500061310901c2103280d1513110b5550050807090403440c4000c490014a80039080b00d90660a92401904c1680b0654074406414600740005060345400b40803039050300d0307040c2d03126414000e008007828041d00700c800b4a16401541d0040c00d032010711100400020b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 946731483 1250 946730233 946730237
    0x8010e07060e211e010e0d02030c030301120f0204020d05071707170408090405011e0e0112140109052505040605010c12031b0903110102120915040515041502031215031c 74
    0x100d9030306d0242107131400c050500c90a00350b40007031000b040480341c0170003a01d04562200d40f50584101075032802c406080e40e0030100079403080c030101e200c402c00c001560004c0c1c400e0300b054644529039200720041c0e1040040456400707001404000d0036040000c0094000da8015200e640c4850914040000003001d540c001d03040f0400c4140e0020304840480d03903840001c070042c00c03409024601ca50500c21505040048207a01400c0d9011031504130400003c00d5105611007078019091f2011403280c9281c40d58480382280702941b4030000d0a50200d0a454180305070310850310b05841d4003102d1525036955260012074142c2c56024555117403404c030084215560b404040700450780e9046101c0d0704610f010602914441d088604543c80720984030080d0705000211030300c07035030f04950100e18401042c0700d14039244143d400c01c98100c90440b249002840812019005550116020f070128540d42c1c0b5040346c0e6030144d40d070001981c14001010950554500303ca100d62254041e040d64207082007901c0f4400d000c100401a500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 946732733 1250 946731483 946731491
    0x506040902160204110c0d0f0c23010609020d1109060909090a15050601030c1b06020d2703260c07020a05061201050901120b01210c08010e07060e211e01 67
    0x284140090006408004450421005140540c00300814496402c2c4002b0880b00c00004103074290104582c020343c1c0500010000d03c031898941c10204040d40100030080c01d40c60510084004111001054442e465000b0b40400c0c10841d200003000000e09000d40740400c81d0160b50b10310f03c082404086442031902c900380c4041124101080018229564614501c0401103025583c41c00b40d600380002400450300040c025803a2040c8041400050000700d0748016400b622041411028020004881c000d500a0f1100c0b51100c440e94050060351420b000d09000c40001c120004010300b074404c02034044580058071203140281c0f40e80201d81e03582d0100800242c0715246800410403440c00307488032405055407601000500006a446119120041c05020442c810410343c4c949001c003600301c1c80c05120340011102e0780040d641c0328118005c0205140c1c1d9161401007000210700b40c0e029104000d142036010700300e400f468200c44a40d24550141a154540302c0c001c43c080102c451812001340d01c241025440001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 946733983 1250 946732733 946732747
    0xf0311390c0f0603160311091216080c010915210504050f01420e090712020f0910050a4a040f020a030b090610050604090216020411 58
    0x224502e0b42160051040d81c00700100031004250324030f40042c82d641030501141d841c1c0001c500d175200d402100e15843e0800451400d45001100000b45140c1d2a41480000300c1030a403a0f030201522840f800e110300e4040b8248403801c0140b007502036041c0d50718036150320b04142e00f040c021494080c4004608011074129403039600b0f01c000e000b814403008c410810440d000300b0840d010405809249101f070b0000c0034020f1110b01224218000300310010880b91a104240c070340d26500e815011210982c2614001018821050042850100c1045900f03503160028103c524103510042000b42c0c1c85030040ca09041b0291803800000c80d6141c2c5008400903000c00410118002100e040c5200c1d01c4070700070f01007010300b4075084018486440300301004410b0b1031046502d801d41d40d6141400941c041e404003009411561240d0b00000b41f2109400c801d0040740040c0c2502c03900e4482920344808825140292a48103804000801c10ba00c0143e008121590b40460301c0005121340b60009002c40309800c90310b041078480000c0d01c3d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 946735233 1250 946733983 946733989
    0x501050a05160c052a03150921070204020304060f050a02090423010b03040c030f050607030c21020a0905030109060209010806060304050a030e060f190f0311390c 71
    0xda01c1d0240346180c42c01d0f001c01c0c941c50301d5076690346449100c04d10208200c50341442d00c5003085c070a9800d410180c21551080300315041445214411542522103008a144005102c0c014a50429840b8003800c91a4106034072502000000d50020308101c0360b00b952491a4506105140505441196840b03001a2541e50500c00d0106440024800c03030351340315030300c02101241c00100d12040e06490109045680780d1380c840c034142d018401d403500040c0c0840d00608007481001750020b0118401d50721982c2c03d0100d40c01c2d04100b40c0f5031004006d041080001007400701d105242969000d440d604d2950301c0d008617000e54840100e421522a0b01c0d041d44e249800046403511035030070844a64011798203035080c1e8903618258403420b44500940f01c000341007207444241000340340d403100151407402c09094011a51070301404d0000d09a803941d0303000480030034580310001104e18001e100314046202d400c98824580703039a0340d07919605950b02114080c4910a1008003250701c0072610041d0b10080a41e03002441c5580442e420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 946736483 1250 946735233 946735261
    0x7080a090618200d1e0f080702030c061204020d02030705181806010815040203070f08150604020a020a2a031407050f0a050405060a090c030f180309030b07020102070501050a05 77
    0xc001c0b50490003001c4400c2c5500e908505031804e41d044001d10f0711a00000703945410585c0003000c05014140e841000740240400c600040001501c201d04a40003861303039070180b11a5001e010001c0c4044010039000a01601703010013090f04403071005090320780c4191500e0000301c0d510303a42c3d40303800051001001005910304c000d140b00298071600d01e00034003503507242c500e250740d890b403c40440048502c0310340c0c00700c0c01f1910100f02c183c001c0c060008071a00e0b001d880b800741a681c1c0e05404a0440011000c40118185003011700c202ca80340d019980c0a0100300a09407100e104049120080c2c00005908416400c483d0300160302000146214081020503021a01c0f00daa281090b0707a0001403003a20082c01c2c0c030b5643e5031020a44800c65906903408500c5a40f4200050854860369010525007410703c59000000ba5056100c0c051420008a041011112510703003000c140c0402c450050104182c1c010500c0418018861603038010002c0c80090b18091035581c0c0c483c01e440d41969211540340e20342c002d02507134001c6802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 946737733 1250 946736483 946736513
    0x1206090f0709140601121107030c120c02130209030c15070308100806150409021e0a0905040b01091e06061d0306040c170f01060821030f07080a090618 66
    0x18144040c01c1c5030f9080ca9030008016040e68144040a0510001d440c4103401030803000b90114655611201a405d020700625080360003258030700703401e00d21200250f014080300940c098018104500001c0b0100c0f00b04001d6009025140d458880d510600001d6560407030100496502075402031b483d040d581c80d01400c002000360031000f01b0400c683d801d00041d10009001548022440704018002d0014000b02d001000e004a0207500403a076481042801e007410300c4800e1854409803a5103403096903a0810004882064030700402480000c00100550400758010501e6401801c10703900002c1d500e800c0744400c071140b540c00000454464025607110b0601d281c9880314000040e000f40c901490543c1d6181c0007260355000e03400001c0e0b0050001c11503058100300080300007040d400208101c685404841d6a10b03001d05440000c840011811078049442e21801d490143e1504055100e958540d46000d50303030008010b000301c40301680c070314075040452018040d801e107102b0103884480882c2d255040040c1c40140d240703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 946738983 1250 946737733 946737749
    0x90902040b09150105091f090e0705040501090b0c15240103050c090d030905030d1d0a1a0706180f03020d030c141e0c0607030f0b0f06091206090f07 65
    0x4410800e103e1101c4010f00c02265091030000d039111510740c0012009909818101e1003070117421100c01c0d903907401c022060b0589a20300308140d20b55450038003c407550300c2140105400186011810064140c0c003c000e00907100019007990140302c4018084003451100304c9042010101480c04191030105212110540340d0b001c0c42c0900a40c0340640003c000351085038030303140c010102d0b414404107151160480e20050708000302902c40d0100301e801c4c01862071989020040c655040003d40710f107030f0301e010000c007405c4450380003880321482d10700e0004600d650080001505c0141c1c85424803103441110302101c10b00d051240c8901c1c1101c000360b05000b450324046200840502d490a20706500d2150060f004403280307045504503130340c3c44001c002c0c110320303030750b01500d00d804129004500c1e110601c901041c0584941c113195420003400405116040546d034900c1c0f2480d81116151815064a0511200030030300450090420725441e4249038403246400c0081350011026005a5801d070b40c154424000c00000702500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 946740233 1250 946738983 946738999
    0x18050a2a080f010f15020f0607090906080d080f0702101805160b1e07020406240c151107020d111c02031b1305160801060f2f0601090902040b 62
    0x101c0c00344c08000c00d007806030b0903800814a8085011500c200565241e19410100ba076249081070030029001c2401c501661444c01d04201012481880000f6003aa58061a41d2502242d403105503860001e02005131800045006003100d00040054a000340c018680ca1a01d60300c2c100591130602d103046c40c0000820520042d540c882c104046c1d05203070700341c0d0000c1142c02d11028580340c1982d4191414442c407000250054100b0340b00107540b0f2004002442a40301c0b655118030100703121442110008031501c0010000c20018446018122140e841080c14207800e95085242806580020780f1000310b00b00c0c101d41c4c18505050f1403080b41000c40b10700090500d0904184400c0ca03641e8006500d0ba040e9a00c80000040078812065559071101012080c5400345030042207030342005d003190b02c044181d40030602c0c04a00c05c1d00c0001504ea10528000d001d07010150f1304c090309000c441c0d507106106c0382e000c10500c0107680c003002c00080c070140922401d030003080e51500c000780f0081d040c4103110684a00151b807920074001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 946741483 1250 946740233 946740239
    0x1120201140a031e0609050108030705060703050c0d0e010e0706030216020d020f151809061810080d12060803120103030318060203011d0a0618050a2a080f01 69
    0x400821070284080e8103240c50300c41070301d000c500805400f803051800c04034800128200907202d5020343c040d80c00744403040c40503a80302e42c0d459a81e4441c46400030101c2d40600d0001d00228030942c03100c0d03003060301038011518051005003540c080d2404078032a525241d5442165a401807000c01c0020000d014070704066080684c004c0741c468240e04142000f9025103941d0f0080380440d80c445022019011004002400003100002c540c0c04c90342000c401e4000510180c20b9001c401e15040100c40e103e80001070a1381c0c07140054050400e40c1503c050030040c011043d050001c2040202807020903980c2900d0b5803413a030070580b07441e403600a4880b1a4811441a0820490380401d0b260000c44a81500d425080129001700c40000d1080051041c18010389010303c08000890324004c03541101c0020220041401e0407910390041c0d0000302d0f200d5110b0303004c402c0a554014284242507411007548000c4411002507034940c4440040036040541e60040300c86c01280c01c601c0c0130a600500740c00d4100c01120412102981 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 946742733 1250 946741483 946741487
    0x6200703053406020309120a02060a050a090f120c14010e10051501050a090f0e0a1a06030a0b012003070203071e0b0c0102091905030c04020306060a0e010c0b010b0d0501120201 77
    0x80314682c050700c0b56030000001000e60a00b00004111448044100c0da542d854a40c8002c3d2103440c16110a801c0d00d08010101d00040454080e544125405c1224500c03a05031a503513a4252407201c281c04800c0c400307002001004500e080c100c2d132403030030814400031075118a04041035080840144c403d28103240b038001480088000c0089070003500f1001e00340a1b03034403800c3c10b00581c8d041f40d580e44840c91a20005401141c40e04090b4a40f6005a40702e60052040d04104884100d000034528034094120300b061001a80c03518898020028200040c100154600040d044410315040c40d02814411680005000070440c1010405000185a400c800289001203071850031580941032091611407000403e440c0c00b254000c7d81125112100201030000100c011502002c2049007403240c1d0780701b400f4403000700c5820704207402200e1040d00d00034801d81c0b030100941c0080c1c441e401c0801c9003a0422508a003030500043c4003403082d901a001540035541c40b100c4650420303066808c1600231440203444c200c810380050f6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 946743983 1250 946742733 946742827
    0x10b1809190506130e07050906100f120e03070c030b25050f1c05040210020f072c07050c0607090303080f0405010f020a050d0c030212040620070305 65
    0x11090010903940c861800007101c0d91074032440065124944880c88170600307070002d10803044510a460b00950f9648007020043d200b00c14041010100f1b00c0c240003407030788030311954108028041241000032400e1418484a2a540003010100e8020b40089810b06c1400401c2981903481509032070742541325800f8804820746d080c0c044800c0002e2042c041890b40c10304d0402c6081d5001c842a0825410030030000c0742c402c0c00075040c01e9500303900a00e40001c19404451001c15445501c003a208003e04290f4a4820202100743c000d0680d902c2889044024503901400c1c011040e0042c803080d61800c5d101e00f18400354508000019018000380600c40d07804000080d00441d40e0303540402258005c85840d6542d06015014091410340001098400101110042d4000003d01107100200104015003810352400750104c0c4902c0c141c50409e00f801c0c90000f800034005801c003c84102d0f658440f42c2d0200e0014070003030741a8006c45400c41c0442d00c04660084000b003080100f007111301001c07902150190041d80d40320021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 946745233 1250 946743983 946744021
    0x2808070b0c100603120e01051612090f0b1608040801050f1905071b060e0f0a233703090e0a0606050f0a0207080703030216090b030304050105070317010b1809 69
    0x10084c06c4940c402d1580c0144103544800e24000050119001c0618203045070010b00155130012440c002000b090000d0036450110a4402862926141091030039400104104250b0200e580c1c0104000c003146085080c0540b500a0b1b4800c4103403440b40c20000c84507070300c0294400056200700d01c0c02007005601d80c2d001035030300307580d5059a0019080c00114108080685403055401c16140704000703c038445845d0016107940f030035011307074500b40b8940000345100008103903e2010f4449a80964984601c81041920a0301451100707541c0480140c620504054084203c079020381c0421074542041200140c01c00400b503100c508003404010b040c2c02c0c0740014099000307401815180000200d0250700103802002900d0281074000700701c802c459902e150080d40c0c0e0802d0741408020380b00e056000100201c840c01207405a0070000c024604040c148401124280c000708002d80801c00c0c0c2089425420b5503070f40d2442d001e030018a4250b9682c440c01c1400c51202e500b048110b034001d0703080008100000c910031100c0452 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 946746483 1250 946745233 946745237
    0x2010507080d09120f17040c1401120c051903150605031e0406240e131e150e03070b01090906020408030a03020d0c0507022808070b0c10060312 63
    0x5485106215000400c0c031100000c1c02d038901103426444c0380d0b4100e100300c0f00000c00e95a401c984040245035880c0c0196090750020604d1030100010b10a0034240c0601041300441894429041c0e100c81b035400c001e40342c5900354000807400c0050f94585035504a21012200b40391414140941170010b000b01030b61030000d1098204114003c0003080c07a000010002c3c0f0094003c100440b40e036404c11782007140007003141d035500311490145c0d08105140e0851400740101111203602d01d8000c59528101c0c0f100300b1034010001100c00051321092448040001400d44403100e00541c540040400c15080384001c56522100c1c42c3c0b002d038814400c4038006042c20310a14191a140c02c2c01058601d10b078600307240a80101e4000104d94000403038034400059140d40a05410403550605000c00d668021041d682c074801c0da038000c2d4021410720b00300051250b04c0ca80c48034428514141c001540c642da260814100491600724508494000032100c58080c0200110385036002d044d1030400c012480d5686480241c2400c440e1441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 946747733 1250 946746483 946746487
    0xc06081501210c031d06010f090b0604051011010c020316020609040b040c110c061207050309160f060e030106060504030f1e11010f08040203071223030406080901090201050708 77
    0x7440c2c1141c9112a50400c00128207101c9120300000240c09000341740300030f8800705060f107440c0a5204001900d98100d071100c0542c1d041d440c0c1421110000f501c0c51346038581e003004042100290584034518aa000d01525a035110110000c030001d45080d42c2038802218110340c02800601c460340708400d2820500e1350f040303034995961550140882c01400102070003035030180c54405100c0c800e90300862403007011402c4600b9034010110342e608001c2c0c0d600460703460f040c0c43d082c01000648400d00582c02513421030441411119400f0300003a0045550840c0d40045170302441c0d140c410085160031000080d81c0341d000300d009002940c103059004042d40598403003d84188443c4103d40d0900204060300303201a20200540b05c1ea03600c0a080c14080d0b003440f1105580081c9501da0700645036032040d80d0440c01164010040d040d40d40c0360220481030003d0104050700d40d40440024551a14000807400e000c000c0c0490203903440e00d28100026103510310080c4028440d034141307154040189c3e03100c4121080780307921621840d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 946748983 1250 946747733 946747757
    0x801051207030618050d050705030d0203041b03150f0605030613031205240607030c0b0702010e06130b01060809030d0f0609020d0e0d0323150a090501030c06081501 72
    0x52601c0d501c0c1d440505050710f00090051001c420100020401e8040c00c2201d00c5c0c4401c150007100e103403149000192190308240007074070034001580c0003141c10501a84c12038a4090001e8a48800c80e07510350b004885e450241880d03818402102c2c002c610203200780080800c005483d010200741c0320300340103006818640c2840100010107008280a003846401c0d200c3c01c000502d003411410a4802400030b03000c02c00c00c403507c00781c046841d14000f10303171102d58983d99404242d107147c1d1b50540328560150201d4255501d0301000300b602201080b1040c4120300020309021001501d00b401400e40c6410f8204a08025a0004002030080d0000448100d00340728040044c180441c1140a40240b9454110039245400040c1810000300950171035148009410b0a4812142e641e4500303404a40185191040c5031140344480440b0301c4005140d182c1c031018050103000b1103a00640010f105158641108030050350313500c014000d02081d408404007801d05420042d240c2e08080c000c040c030a01c614000d050410030306034aa4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 946750233 1250 946748983 946749019
    0x2030c0f061e0307032018030304210c0f1505071a0a0905121927170d08060d0b040c03021e011209021c0804051305071e080105 56
    0x281c1c96600ba411016402e09a11440c29185500c152540000079050203500d000c3c2904641c400d0042c4600c04c5807851074213144450050341c40780e074403070380b1585800240000210448e50050108043c0820403100c038480c00f0768500030521008a81103120301200e044001d04c6040190010120522058107110361901420701e000c0704d0a40035844400e04405811080c480383d05c40d103802c41c42c8a10320841c19152240042142d402c95400b82581c0045030140c0d03080507485183c02101d1140802d8140c02d0891003401e5601e280303001c0d03040c160703101c50300c2c00b41011420b4070700c40810311452101c00300d1031620f0501c604041000a403450003500010b4845103405000c24100100b4418200086034090040e10307000ba45030002d010610040c2a80d00c0c04141c005c01c034a40d8910702d0748501401c041d4010019040082c00003110b412f1741c1e00d401c808440454081101040a90342e002402100e00108840803810346000d0f40000d003910181d100d0420f170000d043c02c01552407074212503040e0559105a500381e03124041c040c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 946751483 1250 946750233 946750237
    0x9030b15130506030105181c110102031617070c0215090301050708011703040e010b03060111010f0902010e0906090a052d150d15050411040f050106081302030c0f06 72
    0x1115800703084a05448400d48403500010300c61042100200031a40e90110101c1540c500c108014103150890780720a9111109a140d006120b407982c82c1c00840c2c62104640c039800c9a000b66400c1c410781c00b450044203005948401e00008458001081c2c01043c203010101802580c84250000d00c40c1c2c00c585440c003454494070068640f8540c2c000e00074401c0e42046000540751a8007801090302000003024030301350b0b0071030000844044031034643c0d104142d680b0780340183c841900050400c1d81000229040101425000d0281c401035150084001800c28510301c0050480140d10100901a0100e0020014130350783e6a0013207680700d03607000404503050755245014200300c04a91103156a03c041d40900c61084031000150510502082c0383c0302e0003003c004001c0101d4004919402405410b442c010350380c54172041e80100c0d801510428006940c0c1c0e0f800340000d8196800f90b0028440540d1b51001045000d500c10301c036540141912440c031062180c0c50700441c0e1214a0403611600a9482001000980d21440d003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 946752733 1250 946751483 946751521
    0x918190f0209040f381f060f0305010501080112121b1110020102030c1801090902040618050111031e040b0f0d0506010302120403110106090e070f0f0609030b 69
    0x2160002525040c134000710203181c0d0050544883e8650301400503d12580245410311300000400c4d00e00b00003c4182c406001a002801c000e0020840d100200b070010250762001c01616140d180c17070345440c2c241c490003000c99030164003003410820044010028501d441041c1d80e88180c00002100380e01e5040e14003628030f0380c4400580040d581c12030b80e1303650034004444002c5c0c40e000070455a80c80d00c5c01100343c040b401d03800151400303080d00204200d21004025200c084c0603c40c4010704180e00410341d140c0980c070890704203910880101c0c00007426004101c00705000c550144c075003401e00d840350021903000140e5a0207544000c440004140c9410007090074800180c0300107000d21142240d9401e5818950140c079044030300444a014200008551658080d000b640d2a01e2200c0d4902002591107407405c80d0910425542000c2c42d55a0b044041100c20b10b5001d400e08046444000307000c11890081c8223402540150310000c906034240005000c0700d64041000c0f4200e982240c48060b0030b0704c0d40c0d210800e001c03074021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 946753983 1250 946752733 946752739
    0x230a140106200d030b1f0509120c0904030909230c0a110a050c03060106031a0603070e131b05040f0b0a020f1f0f140118090218060918190f02 62
    0x1007103c15110380d15801100f840070050351780020703602452895115883e0b00c04101c001050050200c2a514100403c0b501030400c104404c64002003c503501150010b007086d281540004e540e00070074031141c442d5019800349845511110704610030800c064810240c4043c3c504140c010340040c2008480d4403c520b0700400c0014481500e40b0704131145429950340302c51607210350090180d00300006a0b14003d106070180c44601100c0c020440300203404200ae50f0344014099018040c1c00c803103866264032000380011105189a034001020203410075802121044847d0010030030208010501900b0f035041a407104440c1c1c0940c43c9a152159147d0513824070f840038000840360311941904a0749440d81d054984149094a1020403900320080d00c1c22099501c02440304009045c2400100030380b04420000300c4540d10700100c0001c200724664001800315180c0c065401130840c00005006461800c0901244c01001e000f4005080d138401e13403510f80e00e840301048030007070380d1316411115001c1c41800d080a0030066130007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 946755233 1250 946753983 946753993
    0xd03050a110f070c0602030f182d030c1203090409030e060d020a03060609080d0e280302090c04030b0f092e14060f09060402090301230a14010620 64
    0x4010201c416080a40161000142140005001d90000c0201c8101a000b0141d251078484c5103401c0700035402040059640020032004400405c02c00d1403d52103901782002e0f13821580ad4051020180b41200c0040c16038481c1013003558580c403081c000030884904d8a4103880200700f800107400e099642184034441244c10100008042c1d40c00c88407030b1300504811041c0d860803c803851b01c5020489414816008170941640a1148c0d0001140600e80200402c0c40040041950841c41d4903904540381381e0480041d039005a1642c24070841c6004130502d94444c48402400d410607146440d00c1b5400c400c043c0c010200003901801060208070240042400303030098261119140a80481842d5000980d4080c1641c01e840d011b6514590b4204021250168800500d08940242250208040d00310f01806143c2d100b9420480201c4e02c0d10300380603601003030440712041c00b0307480300c50b18848161030002002002030610f0310302d1081d95840c1c8241b205054030150b29090781c020642101d00c41940b50b07001c2499407207101e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 946756483 1250 946755233 946755247
    0x4030203030f10031a100302100c030909020f1e0c0102031806090708030d0e0a0b010803210403090323060c220f03060c050409020703080103061a030d03050a11 70
    0x66004038090b852100c1c0307555806000e00c4664100d4007006041000c0500e14040140d03001c900d01d90492645100903403c80c1c3c1c0c1e40d001403001c940d100c500b200407030074550700d50040c190098454802452406010340c81d00704480070840351485840002c018052000f025800420140e40669036407150b070340d008542c2c90422450740c01c42010101c0e0418940d100301000604106004140141210982c0c0e00450408500c20649030140c01c4103887c00034035114110b101c1001c2003103145c4450082040c01e010b542d076a42003029014204070000200202480b11320305000000b07511203070b0a401c4a400c01800300c050380180d03503006203075a4100c4071300c18a84140d805001c842e0a464009143c101c00354580c001f5404840a650415106944038400d94601209010404150240c01c40b1901d4122032400501c1d050711181042c089030800201900068900401441003001c0c034800c040030396078114a001a030418031030000307035103400341440a41059281d8011070038a0403c3d800110004060100d51512008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 946757733 1250 946756483 946756487
    0x60904022a0304090e0f0c0405060607061a09100e01030204051905040b07030f1a060a0504240e01030b0d110a0b04060e190b03042909030a020f0c010c0f0215030403 72
    0xb03001300d00c105031400c20580f180790000228070410000e003c000d440824200003c000007068010101a0403003010412500002d105101d1890482c00744031780c5000c580015028040c0044004015146146c2c01c2d4900f4000400c0c030400140c11070398101d402040550741c502d0201c0b884921590785000f00350600c024001002036642d401803081000d66400c201d1822410301d40001d903070381e16015490f881c084851600150074410024600c89076641070003440d0035a15044d542c401c107804201040d007c080d91000c450025800b620a0b41e144000346400c0c01015400f00000d00100031000004000006207001d078182034980c91a4580201640052503440d60b0340ca0300c0103001d14200c0e640c850300c42d407040090400c080700b51400700010355024111840c1155900d69901c05039224010482074503a10405030030107850001d6940034855000c00f0081c580310319800302c01900d08440400386d61495000b180b11081b0036648421003004075600b00030310480508090002c02c0c410380a10440d0f0710340200000c01c10062503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 946758983 1250 946757733 946757737
    0x1003020409030c0629040b120607021f0213181401080c040b030f0a020d0606080115231315150e0a0602070e04080c15040c0f05040605060904022a03 65
    0x11340691802d004030109a25180d13120f580340328079103070030718002c450380c40180c00d00380d0016104210103401c084e028524001914500207045602c100142e0050b1081d00c02512141e041000090200c0d00650510b01d40310010702c0d10507854025a40c14500e828891349205c80c8a4015007500c02070400d4006942d6124490141c5915420030307943d00590900e042420b0606002500c0d00c041001c007005004040b42035400c22a01e0a07500d07400b519a0317519858081843c820030f21aa01c10798a04102a107444c030703d0182080700141401641100241908500c0785441d01c4102a040d4047c480c000c0004d8820506080d02d0b140c8400c0d500400000d491a03105607015580000020b581c0d14000c03039548465030ba4490080343e41d00031a0042d60080c600340ea010034000390080020741440b022002c142d4084403898a01040000d0342160240d45a0003519401c010102030700000c1c01c040d12055400b0300041d400c22003c18018410712024034001e940c001083d490200285c2c403410a044264404a1343d20401c01c0d41c11960380d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 946760233 1250 946758983 946759007
    0x20108071115090607180e1303120f021803150c0d150b1b06090c060d060e1918030e090c040506041503050a0204180c02030d0c05130626100302040903 66
    0x6c200c01c12040b48900002000c450100c6614800031032031303683c3c0c108111480c0040450110705105c80c1034000d030320040c4640684200801c8400006840d0788210b40c0c1180003149420865010f500080750700c80d403030000a1000c0d644078064003060380e0360340704c01c1000500400c004003401c1040307540780c031002c100d19200200404d050141900000c1e81445010b242d903403282c40550b060318480d4018a1075102e14100840546241d000c06040007031541e81e6a05041d01001044800216103820903000040325541842110100d40d0708162501000480c0c2e5400b4105c0c46d09680b40d030b0300c14051780c1c002400360b180b084200c0e4080d00d000b8110750f481c1c5581c0c50040c20132400d03040b8242c021070b04000004080400500c2900c0442ea507822088031449111030034580200300004280e000c5000c05c0040c00c040040b14000c1020154091381c9540d500c0c0340c02212180403040f00e4000d1420806ca400c144490088100080b901034103000d1074889440d240c04507102c0c09031021b075100035046410b11041d101415009a015101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 946761483 1250 946760233 946760237
    0x10092109030b010b040b1e07150c03060f15030506060d0c0507030305070e0f0d050c091e100e06090a18060c112b02010902060d051b0304020108071115090607 69
    0xb03590300d42036102c4036030065015940d000082802078040c50920702c00f9013100e80c1d100b0b004c818502456500c850305c007c0059001e00c0c0c0b04685a030642e503080d0340c0c503116100c000c2081040392001e15080510400d2000c11031104901055101c0000c0b40496456008444132903502c0e4901300400018060081c007150403d05003640442c0c500400544914060b00e50492000001410f01581c0c581c104200103071400072240c150340700c1c42451079100a41e11441c0485009900e900b0300e100c200a0007404412689500503e5901e82507a81c4004101c00300880c15100d400c01e0080f2419000b564484042c5c000820f40c140710403132100d1180082c0018001158448141c112081d03071501c4d1420040000c0c569568080084a0081d090a5941d825a5401094800d10990042c400401c03021981c2d00080e000b03130841c80c1c8032805a0355071001e0208150140d0300c4c0b64540012405024298501900041d0610000600c00c1c4148000c0c01010b4009200501003092035a240310340c002c6640c01c02c0214581d0303d140885180300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 946762589 1106 946761483 946761503
    0x60503331612021b100f0e060105040e030c07062607090b030c040509010f0e010501020604200a030f06060f12080d1a060f07030801060509031009210903 67
    0x41d0705810018017020080c041075104071407407030640c0e1441c10b01c0c00110081240b004103410381181c8003210001a08a200d403000c170300314414803502e200180074030200401d040386c0100c8003c0c0b09003840a038404069400d803510300c0030140140d8281000c2090100100141e8049400866100004d405014141903542d4040341c2d10250030382041c41902c1c1d88200034000704400c0d46a03140100404d1004250314107280e01d03010124090890481110301500d60400c1c0c01d43c80c1c031100715005582c80303150000d1003015400c00e8402003040e4000d03078a406500203070018000a21a081201194011074440e20707210030080b8501c000c1ca5810740003003051218600c0b945c82030b621200a48460803111000c1d40d515000e03440c0050400405802c0007050002c00c0c000032800b510000741000358402403030400608664a4280070001651196440700745880b610a40e0340201d6211401034100c0f071040380303800 = true := by decide +kernel

theorem cover : BRFrame.Cov 946582733 946762589 := by
  have h0 := BRFrame.cov_init 946582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 946582733 ≤ n) (h2 : n < 946762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
