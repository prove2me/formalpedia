-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2868
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:59:00.016662+00:00
-- url     : https://prove2.me/submissions/25204819-4757-46d5-827a-bb54c0357203

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 515647482 ≤ n < 515827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 515648732 1250 515647482 515647487
    0x10b100521150f060f0a02030909090601080a140c041a0406050406141318050a0c05030718020a091502101a060306060f120c030106020123150607080307 67
    0x81e090990307050a03441c0c80010024019030041c02400c006244007400c0d03080700240001d00100700702541e0407003410841540f101d8215005000c4008190f0301440e511818030781040302c1c2030406440e914035030300824010884e6031400120491516403014051401c40e4404c24071b1414002155942c0d60003504148550740980613010603d4251b20080740c003000065140d03002d2004503580c44c003c205070702207000302107070252612080b01806889901070104180c042c0a40340880101416800c403855800f044c03519042040c034042d00405000e0940042400301e182071682c1440c45901c0c01042e10440e400556200c1c0310344032700320300c01c0a0300c05890003051044c44d0303045c020f640703c51600c509000d482c03070024190040612402d501c2d68014004261030b056444060030000e440c2e0007283d413102071078410030085d00c1ca9285024828814455004155240e6260036006825a4160f0440c4100c1e45048498408000e800d12400754110b030782c00c4d0760301e58040710050119180307108181340034280e00000704c2001100355 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 515649982 1250 515648732 515648737
    0x9070c0303050a050402010f140f04030b0f090c060406031a1810050102010228090e04050d0f030203060a1701140a1b0203040e0a0908160f020907020c09060909010b1005 74
    0x14801d540800030707642c0b00d081d800b00729181560300a00055440c0ca2040c49036116611809a080380301c100b6524010160751150f01c540c0c000d60040b65000d03451400c000c07a845858891691040b05480a05058205100024010701c664080d07207052541c1d4049002140c0b0518403204032100000d00390001c00c428807018810035440c1101d041311030300581c94001c03651307510600076644540c0d040d410ba014080b410708504004612046020720030409440c2d000920b400180c4100790045000c0c20180060b0f030001000245042061600d00c0145401041808001d440c7c02c5104e40440d101c00b069940d18401e4400c3c41c901400303000e00070348150a01c1905000411100b0f910845a40c9022418206464120403080c2d80301c0c00b0b50b104003450f0210500010341810f00c0c90308041061881020b02d1482e03d881404990390300307403070554181c58540001e40d801045042c005070250308070300c11740010b0440c82c3c0c1e40000200c0804000b00510b00444603c80070400c4203100350000000084020108139508240320700040041c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 515651232 1250 515649982 515650007
    0x16170304051011040803030415090c0b040303020606011715130f060e01061715040f0c05091206060a1e0f030302060403031a0d02060901110706030e0705040c02031213020907 76
    0x43c0741840c10003003101c24104a504446581e0091030543d0384035290081e000100a031107048182e02d4088120004141c261000054440c514031981c42d1400c0d400d0003840c004000701503a040c021907101c2202e030b801203071211a510420320015004040600d002140b00c8103920f20005001c182410300240321144243c00c42016034128003404011682d07560811204120260328001d059198100401c0700e0b1000007508215424010b80003007041c0c141101e1050403100840300050001b807012840001c1442c00b480070248a0b892103000b080c00f4144000003d020310f08903c14500c0c0300880a40c1d02401c0c401c100c005500178049010343d805070640e0ba0070b020351503603001c803070450000c0e1070003e101012112100018603880c4000d8a007400104480e0b00b0b00440da44042c560605010544295007983c250030020340000c0d007032a5401140c11030319840b00c607140810f2508520322860502c541d2a080a03800000c0d11801c588058172804203884440d181001b140c0c401d40d011703401c034002200300a18a078000c09034810300c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 515652482 1250 515651232 515651263
    0xc020603011401021b0105030f070e0d06020910030e0c06090a0b0a0c050610081f090c0906140301110a0503100b0c0a120c230705090a0f0e060c1617030405 68
    0x100c8015140c03d6a505d82580d4039022440c148080354900010b070320842c3d032080b05410413011044820300080d043da5240b0508070340040e0001810340315030a1803140250900707040d05040c400019003084041c1c035500151146401204003180516599617210400b40060030034449a640d280c0c1018001400507620309020750383d030710401c0701140d000c000b409003080484114101800104c204000c0398050305804280320f0002c0c0703031214030381c5010401740b0355800002e0100410018015160079003032001c400412419922907403403d041d81650f903941c42c048034801c8840c0e1030310702d58940e92149440c41420f0b06404ca0b002a407000725901c582028002011440140070b120504c11200b440c0c60101c4004a0a040003040f142100101e800c0221030340040f40c0f0460448401d6031003042d00e46004c102c03400011a1030083d40e5484548003440401d1510503501400d4048000e0b001c64a008910500548075014500034902010440c110a004100a19058000000300e070f8550364101401c2c403a42d90f140c41c410320b864 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 515653732 1250 515652482 515652493
    0x103050c0a080d0f1e08070f0c030e0918030d02090a0902040302010509040b040b1002210c0303070f02120f070b0624070c080708030403030305070206010f0b0702010c02060301140102 80
    0xe245884402101218140402043c2007040400112007004159043c841800808020013011403410f0884040c078202590341d0301c2c1e0300d2a12600040102e010999000103000e440da20b80360100303610460f00040c8003015205482d080d207030a0351024244038100444c1e05140404a2004551505500145000d810480740c0e0b90407240c44a80300703003c13071140d848020b0101c1c10401c4849084c1c101500034071010030004100040d8a0a0000843c4600c0c40a200c4140140c0081c0c881000c01104504611807407802c001c82039081141013070f1125960304c00500380000307008141807900c5503140b0130031074070300400d0a50481e00c1d00d9811146607401036800681382100c050351400c00151250410040f46554180f80b6460f0240702c0901440384030356a40a50810385611107091400324030036208104c2d040040400000960f508c1e03281d420010220341c4060b16000071500000300422140f071007174405c082554540c40505660701603030310040e5400007140c20001d4100801000001e1914080211508020b00a0b0260386 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 515654982 1250 515653732 515653753
    0x90c030c0909060d0c0806180c0105042108040f05030f0d02071a0408030a0302041404051b09030307020405090a0b130f0303020a020c03060103050102091302070c0b1605060901020d06170a060b04060f0905010305 92
    0x2900d2703604035080c660000d107040c4000c000e0315200400c001c0c1891a0f592082c00918115100e40c2d0a41e80a900503104c80c0010985c10000e50508102403089608054040c0400500340c150017510b6880a2041030f800403405541d9602c1d00c241441201c0040440e00e046980e40e41d44400702901940241c071805a030740181d1554601d050406000741807244403100d04070f01708520003503406001e40c3c02c10000b0365054032041c03110f4001038899210702e5000340c0c0c0500c0101088075603072402103011200203000701c034094107030409400041d20f03000c0202c0402d83c0c1418056100c000e0000708900c0e02e510720402c680c0c94400e00000006114045d4010003000d101510008814116020584180c2c400c0c410b0007044204881c004010494414015100d04d0301c4017000490100e003c0e80318a4a01001070b42e90131196540028103101002003031184900500c0c02842003240d0b05800340c110360719904070150140c5240e0b115460003003150b03101d500c000050580103400b4910540c0b640d804200038142404116101e201d45050031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 515656232 1250 515654982 515655031
    0x305190204261617151509180c06031806100512010b0112090c080601030b10120b041103190605012d12030306050409060506090c030c0909060d0c0806 66
    0x2070038452940103d02d01c0c143c07038540000d1800c041810b40646502903001c50083d00a1440d022900680305200083c84001103042044000b80010b0507401e80103816000511f0002c00106107012400421901c071612992400d41203e03600c0038440d4554060b004241c104101004044800001e40e041a0340c403900f092120207403c0e00301e820011f4154081604041401c1d4060f0b000c0d0480d0160314459410450a80e65800000346004000e070022100c100500302000309815580381208014142040b0382c09100c44c1c00d40313418a4400c07000d0b02c09080002d0042010849807000c121921032148a920b1724036500d00c0504200000306020300030f5450300410f03658107a82400da20341009200500c1220300d0030b41e1320300d0003010000e843c5200c0001c6090548922000030281d4540c170801c00c0d420b0103490080303403520b440003c111181200070108040d03c4002d1080c454489400401d0312008038080d00d4152407601c074440012005411400014584500075201045102010440600030003194158404908202000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 515657482 1250 515656232 515656243
    0x12050d0f0e01171e0c03160c030806040f0e120c0105090a080a110c04150501081b0f0f07080d060e0f060d11040e0d0e030c09090d030519020426 63
    0x3450000361a880164142c80604010580040800405089000302c0c0c582200307040d21300301c41d0400d0205000c03040003144514908084200c001603d03143e094028140d40c090401d85001e01010f0150f603941a880f07042d108150b0040c004d400c07101c000c1750441842501115200d07808800c841246508020114083d9540006c80c181860b5015a081c3d0802070802d800301d600c1e084054000700c0510a95241c60050b032103512445801c84251468800c0140c02c00f00090030701100030f400200c64a00d04c000d00540900c9542c291034800865501955498011000302c0c4824064010702600d6490005001036403002c0325070080040724504011500e01d80d545201800c6032100032030310240c001c0100c21511002562a0050040c01e11006000180e555258002e07140b80410081c5175001141069200d42114a000c10400c11043d0b01220030440a05d00590b5654440740703010400000e0686500200c1d0720060070140c0301c2895a06c1c09001c64a5550303038940c0008030041c0b40598000040200320060034948003054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 515658732 1250 515657482 515657507
    0x80c01090f0f0b16241b020d11030403020402040b030f22060b15160c080a0804031115070503030a06060e0f010c02010e03010905010212090109030212090a12050d0f 72
    0x250141c1092829501c280c0c168001e8100321007031407a0700c0d110000284c07203440104442181781d0448100d0780b0911a914121003d040100012a0307600c000c41c0a11a40042d0796003c03d4607602d0502c44c0000f0081034640345000c2c0360402544113001007808070b0350100d000080c512403402081c03189000e031035407081034015202a0604c1122000b00416210100360b050b00814084140505602c06400720a41d041c039403a000340f60b50450000443c00d064040c00085d183c0500588100c0d8090308880c503040d41d0b41e0050f03110340e00c0020714070b0f01c0404801c8038503960045400d041c00030320030340c1680d03134006440c20030340725403003100c004030000e141000c041078492041f00807901a003000307800d00d00105c040d50010b459020380948120304000c1c061108481d540c03028051084454410000584c49405400d034003201d500c001803041103036038544802c400100b0380c0010419003122000d00309981d2080e40401080c0040000c5d08640e044840e00100c980030028001540495020581d880c031001a4100c407040b80d0780000d401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 515659982 1250 515658732 515658749
    0x5090c040317040b0703020c0111010b1c06020c030417060c03071215090c0c06060503061e10050d1101020606010e030c060f071a1e22050c0a080c01090f 67
    0x3105100003002c00802508202c004411982400d645000800381588800c10860041c6c00102d4182e080c0c2d600100c000030000e6800000744174491601000c290907950b0000c110b86410403800e081d00601c291a41115014280181500e0351182c42d030b00041e07080c2c20101180e1a07984a0400011010301c910400d0f41c2c001d44190f03450003408502c03198207d000c0c1c01045425945500214400a51424544600300c62640180c0718040190014140001116402d51000b0301030742040042003400c24245410a1403900d0342e10800e42c01d40c46000800ca0300049540002d80c00c4010461070f1014003c11a0704142c194200741e0880e119540c0d2000115200030165030002c0e05548102501a104d180441c0509241c01c0c004800d1401e1289588650081059040c01d00b84440440c0003172007500350240d452a08000da8004528606040c00020301d802c2d60200039404070780014541d402c00030018103010068070036400074000d80e83c203a10307031040503207801c1c0070340c1d050380400d15205002490307140c0548150102e81e41c52 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 515661232 1250 515659982 515659987
    0x2090307030c06080a020f0315040b210106050102010e1c1112040f05060a0207060305070327020307050618041107050f07150c08030a2307050d110c3a110705090c 71
    0x9c0310260080e0205038982d5000f03440c1c9082483c81c0d181c0d488008054481110101000a031440800e800c4030300c113801240c1164107081d16007000303240000b207104411034143c114109000a82e0000c88038030960f01a550380381c2c020b03500b181001e8500311002d041540c104100d01d480c0250341e5403c02c81d040c0710b03880c850f40c00b6070084901000111300030340c07003a40d11215908000c540c001c440044101d0980c140380060b046994141c4440c000c0d41420404440030700301c25034171245004203000b206e131450044a50414030032a15145490400b00508040d0303082c80703a21008a9040502d282d8a06403520350902420040903620b2150008003032180c00c4118a640d0003607981455500c0c0d4550100103480da424003519400c440e200c14a0264641c40c1c1990300c94035060303940716121140c11490300103551808242d007840920071b10100c0300703690b0b0200f079070300c1101a080000d41c40e00c1c00c0c441c03103403581c201005900c0c10f12000c0d0011035018183c000412a034224107842c151200191913400b00000c680382a1100390044400703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 515662482 1250 515661232 515661241
    0x605100807140c032b020721170408070b06150f090d0c03050a050d05040b040e0a09140a02010e0a0b0405010c03300f05070f1202090307030c06080a020f03 68
    0x1d42c441c51508440051010720708110100624a1940034040c0b007014441380c0c85071411005881c1c903007403042102c0c0380070542c5071121079105c070360030010641e00072040f4030300750f101e424074850155844504901d0b4112000d001c81c64682403124083c3c1180d14286c600c480070b80000358041c5444114154071202840c2c070b40b07082c420344048003d556004000d41d19040040074104c900442c01c000c81480040d486100104041d10803450001d007010559411f6000313020301444107202c50602c032419030b000d07240d0f19040e8424550f0750b001090054050660083e01c0d000d03501100c840300741000b00304051001d0007078a40905880d02c1509000160030144218184580107000521456100360010342c14540203243c0300e20012800c05120b44441c412a070308250340440e001c02801c085509002d00d0b509034094103400c000d9450f11004c05010010b140c0400b0301004018004034074164160b505550680201030101c4006c0c584070700c0c007505005218098400032407441000942c569419008075081030300e440c02c103a0b045848 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 515663732 1250 515662482 515662487
    0x170d180b0a06080d031808031303020708060907050105090103020721092715080f0c0406060309110f0103060e0103141903091404021b0c0a06090303020a080d090f030f030605100807 79
    0x1d9081b40007409103280c16050740414000c602441c0500303d00180403641c040d8900d00a0712f402920f03400600c5a410000800507025000708203141105d0080c20200d54960345840128000c0c4910000202011131800800707030300d00e4442e030105000c4440d40e2a8240702035107035510052014110f8039810500014040c007a00e800c0e2098100b5030000d1140b202002c14140c80b1403046003800302d140380115041e80541a608403915040c0102001000e06060400000c105520b41480c003c100005060003445040311410160344294017040003441c0091415500d941c607440c1129000700042e140103410310a24500480040311200e2401046030700d43c450080c03881c034000e54004802941030200d43d205500340250842815280d121980d030500c004003900c4a45000010058801015003007801081000b010074000660001460082c29400c041420707110407101e081d1314050b084680d001002d08800180c604c0402da04044801d22403142034405100340c9850b80700b03110b50002c1c0400040c00040320500443c041d1030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 515664982 1250 515663732 515663741
    0x604090c050d1106070825020d201519050f0d0b0f060c0c0111010606050904023001090b030d05030402060c15101d01060903170d180b0a06080d03 64
    0x180304800303c0a40c507100e400000c807150003204090f960764100007069031035601615240f03810345983c5203580c203200350b41c1d03000b10355081213580005086c060004030b0001e03c1520705400c030002d2940100b81c1c4080c2c5990081c0b04409801080c0e000015010b0b030050201660b01640035644250b1507044100d080501d687c0c1c0c1000074106814103690445681c2d03007a000d0b6034590a00a01c807c6440740000d10784078088500040c10403c581c0ca68044c541d240020070721100b0381c018212007001104440c0541c03070310742c100300c08080120445200c91140b04503c1c03c0c2e03000000007007000740c102c5200a030700b0445400d9500034542c8880018034186d0000b50300b00b0019005150500280c020303203891340304440284c61b81304031001444005444440e00003111410401001d080540d1020110743e031000d0100a030b514144010381034900c680401819480c0803440121903061403004c0c2e41042d485404240000035840143d40303c104075403c1c003901e0100740d000008070000311a01501c0304844101d00146200c00741c1c01c0c030840040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 515666232 1250 515664982 515665009
    0x9080307050c1509040f0207151512080408030a02010c120903080f04030e0d080306040c03230c0d0f020a1b021e03070305010504140f070f05090a1407030608060604090c05 75
    0x6030600812449407550b110325014074406c0703c0016502e002d981062085070340040101d1008a04001c2121510240c003c400c0088030f000c0c01500392129120300d85120f0b5400750360056940351001240070a1031943c1500000201d030110703140e0081840c801d141036009d0318620003025000c00c50030700120f205003088406007507201e400b07880c104808064140002e80745508019041d603c2c50380c08001c0c813100c0d240c24400d0f00030b100060b0a0822034401da000d20302e403118698070503d0760306004400008d5110142d0b4422030303003c2c1d008000704000102c1d9040010009400405c543c0c07000a10400d88805c282c1d80c9408140707991070300280b110107000d400b111000442c0e8044000f040d014015030f500040042c8090040e03e00951140c1016120f00502d42221445c0910041e4070011030703070004600f003212089500c40c0700240d48040d00c500d0925564809100017030011500200140d1440b43c0170800038551590045d005d841004080c1c5420740c44500802044e80d03031500d4007030b00c410808030041013146494a504e0111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 515667482 1250 515666232 515666269
    0x9140601230a090e0703050c06040f090507021c08100509040b0a0c02120715140f15010306030c0612060b031b07060b1005041a2a0f0d02030a09080307050c 68
    0x43e01e4044038000d4640e0f501d09004581e00148040c820045c06000201c0012070136503102e0f061501c1e200380e4003024200c0744a9241358565a00220b81303c41e00c2405015031035450031782e54001d0f100e5a828002e00c44802200e80028120200e900400d003442c140ea51140140c1c1c01c13596480482c2c41e0006960020042030300740c0c105510440302001d640045100284c90120300440c1400c07680e1802a00840541e400b00e0050fa4002a81108000b51710500d0304000740c02800c041c8540e40c07070b0014800140c00030b064075040038200e54101000052400d034454800c4a44042003c001c0c030120350784440c8800a40401d0b1541c0992500102580d01503080c040e000d090224000d45000c5400c804210101e9018002045141c002810000c0d05020102045010048054840c3c08580c90900c089520390001a4194800380284026460707015a1a50070800511002044000e44032100103030300019550f03034043c03071200c008588540000540980c021094824054110000e44100c5400e6402c000f036030961080c2c2c5905 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 515668732 1250 515667482 515667499
    0x30f0403173c0108030d110909070804030c06020d0e011a1e01260402120f150a020c060a050a0b0d08090907050c0105160e060306130c0509090a0914060123 68
    0x214602070070b4699008040c820040c503034603070010325220141c4004540069005008101c070141a849960b0405c1d0700c070720503140a030910345407450101d800203446207002e000b60340003081a01004e01180c2c401901c0301e03d4800208100e03031a6880940c5090a400003070b652019200c846807d45604640940d04000350525103070302d4180b80900c0c14511a80712200700008001c09a007000304504000c2c1851031211000c3c13009022202c044000580e59510302c1059805204803c40852906407160b0140c0d00500c048a040c1d4200b40b5020070008002c000454401c0c0c000d50410b0f211180c00c0c20b08040003105039400c03000c018688070840d401d00a0380500138107041c00300300e81005440b055a4007881340341d0150001c101606001040c40340f0003042801c071100703880e100391010000c1c040790b80d64016550300e22541d11000854070011b400c030706460350f01a003100280c0201c0c0c20b8080007091101d5a201d808210301c54803421181c0102c0c54015955440c090145480c04001c0065400141071445110304108100522210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 515669982 1250 515668732 515668831
    0x2a0307050d02040906031a04150f0e1504111503010e150a06020c4209030d03050f0f0402150915040617010b1303030e15030f040317 58
    0x4101e0740b090b4440d1118517503645050040080c094600b00724a00c1105020903542001d40f9060042c182c1e54158191055841000d504281a10742001200302640300507500c9010104200002080d0308907030445400c5550701d00d40d401840c0c03584d036260340e200240c40070341d045a003032440c2c80c0f49200001d40150312046d407144c0d0f41041a9104020800980b8450f03024020361010368082c00100308100740c006041c0003409040d00301c901ea0101c0c017000d064125240d401c040b070b282040110114415191003d0f0907001d0344018105290f0950401d50007011108200c1c41140d99208044000e2141903e00035032009290301c00000070780c41d040240100342801084d0040100529a04801560196001d50041034200c02d61807000d6540310042d60050260041c818035240100074080845400d41c0802000d0001c0e210751803c241e1a40ca0a41044034040170712256241002520101507081c02c840c120000f4100c0d4120f03128030704282c1c2d41903015400c100041c40b80034062403008000f51040b40c40368070780c114042c8903c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 515671232 1250 515669982 515670007
    0xf071505040f03080f011401050a14160c0e0108031605010209040f050601020d030615111009060b03060a06050a1401020a020d03030b040e0606030a080a051306050a03052a030705 78
    0x40780128401e01c60306075426201d16000e0184a402440c07140c84a4008004000c1e550042c0e0400348960005d00e021552800005001d41d008201d180e1030043c11000401c0302150020b180e02001c044901680719a00840e40d92403c5110300d1409004000e01c41e001840b0000f196451200d8141102d48658009030901440c0d1b03002ca0200c5540c1c0ca00100d4042e01d603010f0040a58040c007e0042114592a040c001203003020080d001c80401801000108180114004d54400c824440320441d084c460b60113000205640c14444054030b03580700304621078040c40000c10308940742e03445880304441014100000300c5103013201d135002c510085d002d8103040d405506240c0300140d40c1d03100c94040c038500c04e0b00e00180d03d10072102031108482507000501501d9002d2418861035030350005184604941c41803142d552000403150840b07060003018044240035140800214829801c40040c05070b0441d0703a40c04002c1c0713584102c0c0500d0394241c0c1781c011500021f0400e041c07074404030810008580c4507150382031562900b80d103c2020f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 515672482 1250 515671232 515671241
    0x2030d050702010c0e03010902010c02011124010302180906010302011b060903030e010608010c05180109080607020607180501050d200705060a0b100207090c02150106020609070801060b0f0715 84
    0x1100010f0b5560802c000041e5004072205950000517002006107507070681c0064800c1e03420800c003905101018140e0b0042c2c4a04208611000c408100d000440c1814030401025140d400e01040b44158840d010640c0706241d0480e001d44507440610040c40140d18540054500140107041680014070318071040303000c00c000340a80707480184256000a0816036490a241c21112560025515039040c4544807408039800407d84010101c030584000caa622901e0059404003087e52103c0d01d640103400030801c2494001c50214480c1c012529105940200b144241d40014801e008080c0030840900c180000320384c40346d0060314100c0810482e01c031000940c918407501da401280c02140c6991203c0308100c2c800c40b05004044007580c1c01e0b1514002012003440282d02c40c400d80c00713881040782c0d0301c800100d5414420090000320075010340a240c4256101c1d07400945400781103952403550310400d4800554408148212000c8451a54000e800c040c8059102000c036804400166400f095400e0040c208203c0c9104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 515673732 1250 515672482 515672491
    0x201060b0301290903100f0b09180105061c061a041b110a0f1506090f020403020316060207090c11070920040b0301121b08010b030717100c02030d05 65
    0x525600800c1840508501d124420340f9226008140110740c0140c90016110a20301c01031200880c1540c0b0a2050030001d04042401a03404280441442311811a1901c1a20b000c0301060091029035544c070107010402a035041c0b000c001560584030003011a4041d03222500cac80c90740303a0340781c1001c0003001c0010b801daa001081400c99a82c1800490a80d9504913564903a0008424051301c0070500d561110500c0c2041410054800d1104000785c6040c20440d91010000e000f101200700701090349600218020f422900080380a0300c15000200c94454460300f000e4103c814590040107460304108480d005040c0210002081c082c820701007030b900c0c0c0d009000c00c0300038025440000400210844801010381c003c070f00785d480c2c0f01c02c0400046c422503c030030040300e040d211101042c00901c0f01d9440d081112484000c180d00c212010716401007507010701074002004000044045403072040c0c0b100a4580c4c02c030f40e10240d20a403540324545909502507282c216040010440c015282040704103080f007410380c2d40803603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 515674982 1250 515673732 515673749
    0x19110a06050708160e0306060402071e0c050f0103020c0a02130b09240d0f0611071a09011a03101d0604060b0108010b0a0c030c0809030703030e03190c1202010201060b0301 75
    0x20003100e03040340d250090004c10149400c8856808250220f6200d90000d0034082c0541e4000681e10240a0580b0590030141d2890807107094011480c20a242c01e8111406134501c01c00c0301c001c0301c040740d600c603009499000303c55001505510349150708015144c140c01004454035a02c0d82d140040c3c135074a0100e40e511a204203082002200d5141c049804003c10341c503607443c030412001d410440480c1e94a00410704040d4401400104041083c45000c1a4010b0800080c540300101d900802c902d64040c84943c0264000002440000051030000d1241d030820300c0e02d03a40603070001121541604043d00a100184814084403c4540c5611030203820054202c8080c2c6926854406140c810350744461868010141c1403036003400c0240300c06000709030030a422009020031440812840901c60300d482129505c00303000302101c3c0e210707a5070f00e03020b8442030f00914101c1c401c0c001d80440c0036912078410b00c5c03030203010b504c80300c4100c013541071458114403400c009400740d045650b110781c003151004070038004501030280341 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 515676232 1250 515674982 515674997
    0xa0905120a11070618061206090c021c0906050d0b040f0504030804050c010f090605090114220b09030a020112110a031d0106080303010b1e130609090219110a060507 72
    0x10b01c03465103010640d0b4454020007100040c00c03001c0e41d5440c001201a07546a180c0011804884100c07140580302940108103181e00e0a06d07034902d0290001036042c1045803101c04d0700c0040c0030304502514045803a01c64000418403c0000300e01101555000d000300c1d50300141700140c032a2840051808656046a045001c56015401d01091040400c0324510300003003441c1c8181c141309084002085405144103a1007030120200d00a10036a000c0d4400780f40f412601c194441d11002113032424140443c50250210070705030100d0010445001600071502c0c030800240040610303031030341e038011150a0038008034040510f6075040c0b00e036941c0a48000401a40c0324640d008102c041740100c2c0c2843d807600d411b109001981c9020720801880102006a90440d000000c0705900d8100580c810b2030a130315002d1400a80540010700c0001034102c07034407081c0643c1c1450740c4440f100358440803024128801d100384600d0400c95160900c40c40c41c49008111021032040c01603840f84a41d44e0344030002ea039010303100940070403140c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 515677482 1250 515676232 515676257
    0xb100f05300a0203040f0803071e0305010f05031c08040515090d031407090e0c0702030303090d08010510050409050a0902130e010b031504020d05071a03010311180a0905120a 76
    0x6005099401a5042c20114903504191752003a0644181306401002604040300142426018021004408070076403003200200841100041c0141070900966659401e001c801207980d08002035141180d91092180400700f90480c2807d40c0c54550081080302c0c0d901c500ca09900d8960710703195030280140054002000c0c240540710014056486407005908614011810458120f40c0100c2e0302040b00e5041c00715415548400381204040d110300d0f4000394240c4800000d201c0700c0400010440c40035680c47e179a4140d0b99881e1010000a02640d042c800001041803000340301201d0964040b540140d510900098121140e50110700b5520300d410401c19503e5989a06485006080c0151204c8040480113419030301100d1145080c1101b016001078010041c1b8082201040020000140680450b40e045502903111800751300140d80240070441e000210403042405908000c0c5501d50b00010018900e4207641c3d4084200c4e0082048040944162054907000c40548481300d0003026801501e59038500c43d603d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 515678732 1250 515677482 515677567
    0x151612092a0815070e04050403020c060f090307060806030a0311070f180506120729040807140301051603090321060509010f030f0201050d0e120705010c02010b100f05 73
    0x518180725043c104050208005240e00080d1401c41c0d072401c5800140e142c03100e050032860501700f1801584c00201c0041c04140041c4140080c01081c0e10840c116549079890f80340403581148207468064041d8008075070030300028028402d000030304801c4421580c4150395892030b040c0d90000341d44069030b01d01005424551840032801903c0d03012038242d41d80f200403980c0c404030541e5180c01d44a00407000d2052086103c004002d0415101c0d65a24030080648494581a8141d00c1e56194810070100c009060440030940c241806894030035000300d4000769000300144019005000c04e10803c0b82000480003c081c00302003007038440802141002c2001540c03a0030030043c4140040e060f008481c1500d902c01c820000a0703443e02d403640c80c003542860102d0b01d41c010f00502c84054100e01c040303a2082d0080c10303070100841e07907054050303c00140904024488110a60000d908132a518400c49800051413070101c00b56500035000c520a14013940313402480c141c680810044ca140e00c0010034070180c84d05018008080d00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 515679982 1250 515678732 515678743
    0xe06031b091f0f180627060504150509160503010329040b01081e03031302060d060306050621061f03050105090d0f050a02071811070302151612092a08 66
    0x16440d441003042a081804a81101d4004800d040b1b83c0710b424070300c4104500090b0003050040070050000e20a107013460394250f500e845180100d9000d4400718001680407080039030450725414454950a10316400c54542c000320300c0305500b041e891003031041d100174100001c410019110764040c2d9845110f41d41040303d4075061084900030b210708240e1183c0e03070304000d0700048101e903000240d554401c0c2c560221032001c254180105200607100038580240007050260a030442489694207da000c441c204105502c2444581c680c1000b04255004900007000c40328509a1500701d142c01c142101310030b658a584071400e45108a500e05040e03042040c24041c2d2503040a5064681282414402c1c1455251a0008c0d035840c0030f44107510440c0080202d90300070107001d0788414550240d4007100c0d5901d5082d414007960700c100340102003242c1141d110001c2c104104652258526103515540c0d164021100304044000d010401c4050700c50403100c908002031100c03500280c4c4c2a1820340c034501d040651030691620b0800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 515681232 1250 515679982 515680019
    0xa030f110c03070b0c0a050a05010b0f0603090a020112020d060f05150f0f18090a091b0f0506030a0b0306090d020f010605060a03150308130e06031b091f0f 68
    0x81e44a05480034041d54041200d40070360b403460301c2c01074032511184c481503d0a89216406446030003a904042c052140c19080350041240c165016500c601401c0d05020051108941c2400f95400c84040000150312a01c400203020701c440c0809810001212020422142160310015402e5140141003040b4100300f50705980d554005014a41004044600c24405120340b1050000b81070000844040c3c02d850003c00c1c03603050b6005800741001d4502450100c0081c20342003020340d440e03140800903c1003040e84417200e00070354185040881c2c05502e0041800129080034080501039612070700159580d071030401019108290404c014807e0a4a81c40007030b040c051f6103c20100903905009003801661a150201d54031010075203400510b180120f032402d01c442070150401032035410000303540c00400d5803001441044d2100d00710911206c0e11200301309956101c0d0b203104070407100c0380408480d140780341200256900c43c0c40940341444200300b203c0340344c040c800307541c010450b040c0e0442e0003030003500b031010b1981140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 515682482 1250 515681232 515681267
    0x2a09090105030625050403080a1d0a050102070513110304080421030c1104020c01060803191718030f030a020721020606130e010e0114090601140402030403110a030f 72
    0x2508220283c00d403450341840900e02c10b00ca000b1411350440b0710550448009681100d605074039103842e900c00522030b05141e211160b0012800030101c041d4607111441e942283c1058008040070740c85c1c4003d000c00321858603c0780c1c01380ca03540e004010f50408204019441548a000b070300342d88130b090804005401c98085404030f2005172000b013a5001903084841c1c6403003580c22001d0288030242c1c0c0070000d4080d2055203890002e95007080c0000480110010182000c00382c6003000346466218514200c07440240003008140311148840820348560b118400c80c1c40384650003095902d440c1107040c41001c20780c425500c0c0d08200754002003003000d11200fa0000c180b258601816105080807842000303641e020054925032140200c50355420b5850754a601109566044900030f004032540400500d000f0720002c41000c0c0074160310f000190003081e0110b485410390740009035507000c51141605100094100400450034000851005601e4500402664211a10030354580070005000c440040c04c9040c0c0850b030015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 515683732 1250 515682482 515682493
    0x201110301140f0d0501140f06061206090a09020a030804090b060c0604030807020708011a10080c04180216210912060203130c0e1b04060f082a0909010503 68
    0x121032111200070703080360403c45241180400040024200c110007080007012507180a040030500d600541c4124403800c0d1913180600035031f07901024010103104076003898421070f400c1d400066040c50040c4007070b50032039240040080c0800311035010a0100c20150425100307044046030402400d040c0b405449852034003a10740c04d003081c0450030010360341ca501410040038850b6220016403468420402c13040204501030080c44241c0c501030418000d00c1c1d68280441c0100b0318040320b501c442d80240011400b401500b20703550314052410011040103155031089000c1547c08018150120209008540aa6005281da9081140100540280c80c41510404814846205000c000d80020340d44219802c50b04400d000d0303038a40c0c03600042c00195510a400074070000e0892008a00000100c494902c40d094008106c90a14415001c03d4801d000d14811800025408400481a203218409040d000081c900200d14811080c4918a005081019011500c20404510984586440448280140000d4000d4034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 515684982 1250 515683732 515683739
    0x50301090b0a050402010e060307030c080f0906010e0c0c0327040b03060c0f04090609020a0914030a15181b0b131203050d0903030204050909031c0b01020c1c030201110301 75
    0x281d801001000c00b02e95910001e001e40e40200b400d0304810074000c0031555645080d01014000b010300c4d01d600e0000030307406000140003280c001c00a90060020384020b001682c6450440c50000390000c20464008600384111400320b2802c2020384000b10b0f410109030326241e40150b6044010301c3d88402544114100007070110951008546242c00c1000d0401880d40c51003152014a400e10a691110b030b6258a00f82e0001403a0b100740d40540b07103103521692002212591020382401424081005546c540c10641940c0f000031402d0035200c6800000f2a0080b07201400c210340042c403646240025982c1403040407568040d402c443c040c100140040004d26400d0444003666551000c105004820024089000003014103015505840c5c107030580744003e1194007030614004019410030711419009540040105030466004010f480c80703191041184030404100401000281814400040c10350151800381c84c926240d030380c10070503035683c4554000c0c4116000d03c1c0c028215101d400700c110800b0010700051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 515686232 1250 515684982 515684993
    0x617031206011115010b09010809120d0203060a0e1807060f05041502120334050a08041412030f0106022109010e062701020619090c0b1b010605030109 66
    0x160020028601441c12a4002500ba132426190311989034846a031540000760000c007401c0144842403089c0d0785c3d0200b03a2a640d05640e80c942c40818051801c4100780000c07c8030060a50240d54031013401840c900001c0c4c3c1d03d85000c1c02c00302c03094070311140c20341d580b5150440150b020441800103000902d04049008418040103041e40100c2c047c07007004100400090000c2c500c00c003c000c404040c012403c40e41c80c141a41e4000032005074403051441c05800c013280d4030f103015507404002442020ba0300d500e89880c002403812620820700500c1110070000d00403410804400821a002424080c0085150389041070b051070020b007030050b400081150f10401002c1c8001400601d001c100c0d000800700035480e0300700c150050b102c1ca05807101d0150801004100e0355100130050208039403450108000044006040c4012031716140120f138103600034622895006000030141d070200380024000d030242c41030f0a81751080b00311181d01c5506a0200880d4007428086104404e1048100820080300200003903129540e91 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 515687482 1250 515686232 515686267
    0x50c03100b070512040b0406020c0915120a210e090709060c0c090c09030b0a090b0c0d0906020d1b080f07080c070210091e0509131502030a061703 64
    0x1c1c0707a020680490071104000342000b240021412001c01a074032940c070f030340c01011035410a03c940001803280b10b4245215050030a1000d0080c401003107900740c2420020103001d040005d0040030340d510b00c58215940e010071640e070000d00c5498000481d00c00c0300079507900010142c144038529940b080c20071005120080390841d09a0707080347c1c00d03403c00403500c040c90705001141c484580c0c00581414101124042c525503c9015107094904c102c00c0c044003078640305c0601040301d030782c0d520003010301d004100480e9518000c14044c0240f8040c001c004656000d4070364644007a6080030a80100c0e0907140d0780c189401a60303080d04e400c003501d81d618044002d8075200c0c1250a03141c80182c2001d040c031603124003044c1041c442d2802c8841c00364024204442c013000d6204000c1c5800550f10030250101c0702c032005401c410f1400c240301021684010b0407483c560f02c0b561140b40507986140c40480b0300040c0740c400c2e003000c44c2840c0003851180f410043c0c001071a525260040291386c4909400300d09a8004104200040f12400e00c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 515688732 1250 515687482 515687489
    0x1060b0915120f010509010801021219020d020f0c060106140f0306150a09090e190b0903090901030b040221030a0e06042304151503090809060406080901050c0310 71
    0x141e140e84180700c0741180d040c41c07240111030000c001e004000c0190003000c0001e003904a80c07007a1842d05071b607079030342c20b03401d00b01c0c050920442e024941940c0400c00c031300031444040b184100034140c01440d128906100d04120b074000b0f042c0c03402030340010400a00382c200a00106004052a0070000c0d0000064081c000540c4103001201025180100210b01980c0300c0310120940300c1840e81c0440e544e01403070200903010710310724031680000d2404c202c01e458811323174085005000001c9014270191a0714681d603a5543c8240000c0c2021341610083c402600d40350340f40d6a000d4001d5000c5c05101e8023606050040c0300c1c503540c951005402c44200001805000e039400002c50b4400b80c0b0b1440e00c0d1002324902d100050242c403e55025001581114900f4550315018a000c0800c010044508001810380b0f240c003048198000d00c0707494410300c9480a190040ba01036044190034600c511030b442c1c604000c2c20005121600660000400900b45a0030003540110920420303801c1250074120034118500046a501c00004900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 515689982 1250 515688732 515688739
    0x4030206041709040c02010203060a06020705060f031906031202010501050117010b03190f02090a050d0b0c030702121605060a0603080f091c1212020406021c0c3201060b09 75
    0x80d0b5103180c148504060300c030880e10062043c80031004460b0024040e41080d1842c0f84507a02c602c00015201740005000001c54030050b01c4903041074489580742d0001d400c0182142c03a8007400c5c01c55178004038198401d40c400b541c8180d00c004480892000c00a017100d40503044541800301115011040d080c020b41241c0c110b80b6440c00070781d44c036551490007040342515800c44803056802c00891104240954025203aa8501030312500c8003d5614010044402c4580c017018102c0c10450010624441da194025503120069004454808201001c0c1241940c000911300310305224003442082040070038000e042d041504a5000d0000a0940e100d48945100c0c00624a40d00f820001d210380040c2c0707134005203070b003100002c2d80d00c000c03050400e050544000030050003910018498019403684c00d4000d02c283c40540304168001d10b001c50000445a003844000039190080c041742e0b5542d03c2c00500701001c03ca9043c071108181c1c81000c1c1c000302e014440041c3c00c034010480d41c0d042c8030341407040c01b0448086ea0f40000d41107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 515691232 1250 515689982 515690003
    0xf0705010e0f04090f032a150b0316060504030b0a0e07140f040906020408011103071d0d022d0402070305031519090204050913030c0f020402210a0b04050403020604 72
    0x104009402013205510091400c5d00e03075226001411f801c900c8442c40e64103090200215001c481c58070302e40d1081c2000340206100551089245101139992280265180c080e0407203c0d2400e140b10119120489039015100145002800b4010060000c2001da0007030b80e041c1084c000c10008011203902e580e100c1c0142650741950b803482c94441d0b40c45010000700300300090020040003a81d07040050284d80140102d082030360a10055030108265403080724425030107544c51184000707810103411171601c10340141a901004080f40e01001da0760341c204e252103181c0d104d0200701c11a81c2c8621906200002405000e105e05e10502620300446d40140880e6841410000b10044030003000f0b0020303040310850a0039010803c03091744041081400c3d58020310942d04c4c2100c82c04001c0d0ba80715000c0030000b01e154030041c0050804007102000941007045814114401807015080000c05001e015210044680c40001415000c0512100007d00d00c45c070441b400056400b80040e00c0c040c0c401075a2900081c00c02811640034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 515692482 1250 515691232 515691259
    0x3050303061201021308030705070e040b0f0406060b0f190503010b1218030c1609020f07060203070212030702010621051218030106030c1d0103050d0302071109040c0303020f0705010e 80
    0x70b6044410781c0304081d81003807866403aa46c07515502d801003001100c00b032045090100d410710070304074158441c580c0301d003580310142c0e10003040340140c2030040c0040301c510361551004140c6401d90005400c003014580d50140c0c907140241c0c11080400401030f82082401020401402404044400c43d142128031150144050300d4814560007040701c3c8805090b01c0e4080413950656a00d8013065500c5004911050101032645405a900c100d1184901e0252020001c0085500141840d0051607001409005070703401301c0d0240d03015a0790b90748122008001030355034070f005110803038401b10880c000d90a9562a42407148030795039015584c80301d2441104a410020540d420203036402c41010320040400340091051980d64941448010340c00c1c00b0311600c0f00d1008482004070038811315200d0490b9007003c018082c000682030190000d40c0146001d84000407110404000c0744c40d00140c0ca401541728001c031554041c034500700242011f140d0405101103421400c0c3c00c201d10b070307400740040350784803021212500120305 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 515693732 1250 515692482 515692519
    0x5040b0c09030c09010e19020901090911090a0305010e010e0118030c1707064119020403051b0105071a07030f150314191502070c15180305030306 64
    0x24030202256101c0e1300903002080d030300c50310304903540543d800055900c14405403400e054180d0080c0d030199400038000603010800250140c0117081d440300e0b51900245480c107000c002c00c1054020303070004e030785c01d0b915041d48180074136007482841d8001050310020050100d40d0041c17082c504603032410240402401c40f54560910007030f4601501c18101601b0707801d80c0c07041c06103424000f40c00c0c030184072030402100512014004a146541900b06201d20804040a040c1090712500715100500328080d082030300c000c808a40e0040c0d03c010310145025000500c92541d1408040014864941120381080418000040020701d10030003044802e0804040c00001c0e910044101c00074142455124146810801c4084240c0860010399095034001d001d40d40686104043c1e070761380c82d60340c4000ca15001d10340500b207402041c080d0344000d2400c2000074025150942c0d503124000c0b080010b8005c940d000714400c01e41400e094200810f44204003240c04101101807642d110300791039000c002c1070341d0b008130320700b50741c10030800b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 515694982 1250 515693732 515693743
    0x20c030c0316020901061b17190503010504060b120f04021507110a0803190e0f150d0b0d150b0a0504051006020106140a0303050a031e090b070305040b0c0903 69
    0x30346502182e0310b03100081d25107200b140180b40103074003e480007070000c110640700751005020b60300e030320341500c0d119070990384d4481700d0440c2c0020714034a0000a004102004002c1d054203000e81d2800c0d542c0c03d841e54140002c01c42100c000e640310421514040002d000c107580c01d070880390751141a6882c250a503584a001003a68045d010800d407400d00700005040b0100010403104190302c03e4161100c09904d519055070780d5032840b0b5810035000781c0d0111082c50700070340c1c4140031120701c0010241540c0d002401c0da0011541c103041c03424001e07024001c0407404800446041c8180200b09904450170400015151160750300d000c820400e0084490b15402480e202d9100d034140c1c1801820054030070009403030008800498015180030b14401075080680014400800c1880b21071074860003460312028a1031550140c038140e100189a100341601c030580c04e215803086401c510540d0001c00c0c408101d0503d54a461041031030000c010380c05052030501840040341e004012540d1150030520231950350300449000a2401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 515696232 1250 515694982 515694997
    0x3040c030602071a09010507050301050d0c050411041e0303091520010b0f03011401050d0c09111b0f06040605090c030f01090201020c0306070509130b06070f11010903020f04020c03 79
    0x1c0d00004940f810000c8200c0b62819040380d2000c0040c0303a44801c1c5800c2d0a03540d00b036684da00090018030061145282c403404403081540b00b200b500030f0b800d564001050030b6a22520b40c840c0c0d10200850204802d005000442c0c03000d040b031810b003030022800d659028200030041e00a40c11064100d440b0b0511560062141071046a900b0180a40507403492005901810200888034003440b060344400c911801c4c14020742c0b07207440da140129000c0382e00789802d000d08894210011b941c81030440d100018044207e2084d1007a0039a507000d225a0781d50802030410100c20400204002a40049100c2c0604180452481c1e00070ba807000d008202c585070110204c1c1b03003041c07070700303d141e4140a510508609007005601c4105001e100fa02950148c4403070344105074840d1011100b000c0894420004038840317141071800304903040301d040300c0000c1504428011504c641c000300ca00301c43c0070007007100481c01c6c48880a4040b004002c01d01e099140f1301d0035607020500945003003803942c0c0a030360080742d144428107051080d01c0d0388 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 515697482 1250 515696232 515696243
    0x21c090b03270604020a12110f01020c0d0b10060f0f031119031d0703030912020414130b09011e1d0d0804060b010309210c0b0c070c0807031703040c03 66
    0x2003401c0d10b59520303240c400a403422403080030749070300010321120300c3c2c0359400c007050700240d10719035250070007082c8016628030226007411801400c0c22000d40355100001c600030701d402010030403001d240c100d080d003002c2c0765107030443c8003440651f500e070407a8203038401c00144880a6600e400b245610038214500014092465032040d0300300c40a0702040001e030f15038040d0340d03a000805031905c2140034a2a001791183e046000140000b43d4000052040d6004200f1140f8201d01c0500009584200d160641d160083e040d41e41141c0ca08543c4125003c1c44003050380301d034000c1407100c000c103d16584c00030400c080780140d0703030507903642c03a110300080c040c2d01641681685518400380c152016000b0ba0f0000138610f0301c080318220303061842c200e5001415403180c4181035100350b003c103a82d03901c41c1104811210500103803000e0700400c21803a522000007001d46055902940a001c0e40d40e407070307069501e8034000801064202d440244e022180400208280c0c04c1c00d401c42c144102c1a855a03a29681801e004182182d00040c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 515698732 1250 515697482 515697541
    0x3e0927010606030f0b0d120507080d060b0705010c171602120c03040302031515040b0418050115080a0b06060a17090a120503061806030712050105040201021c090b03 72
    0x40b09a015005840c40c0b8562141c1049480484020002507108005024102c1d6031000d44104103107009034000d107610350250248a040014582c40d04003551032030b401c1141c0d800c00c081403a0003080400d000d00c1e074514015040042443c4954030004030450300083c040c01003800e000110b444428024450724049505980303046503600000c03240c0c1581e80e0300610003213000f8841c0400c2075820405d4003803c640121126084104440056410400541241805940d1040c5e4404601c03000702c01445412811a20a50000c10391600740e006000b040003443d4410006c6412200300c010008001800032035000d081107501c01d46032114460100c9075480ca21114102030b00502c030070300241050014100704030902c185c6198054016265040314540015540c0641003851540000b5401c000348141d41d81c4580c01504403011701c1c0e5160880180c0341c107481800c3e511a5510003c1c0019135038140500b151b10291260034403111041e44034010540696842000c0c10301c03502101150f001c1c076100e50004d03071004850003000d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 515699982 1250 515698732 515698739
    0x9150513170c21033c0d020f0c0102070606141203031f0e1008011a060702150910030e0111040e0a0b0d0b190515060f0d093e09270106 59
    0x88a0041601076140b9140104298803042032900600890340311501711190b003400700c0004220041d401407ea21021030b003051000030810502407000c3c18541c0d005074000302d502482c00c158101c864119001c400d01946980c08060800580001201d400c54105c03103547d110030110386444282c001554110300c0482455600f800090050030001c1000e40310003600810030300f88207442c098031421000d51400e4004e6404c2c032054015251001c601cdd070f02c0d5a483c0403220310386850240041c101c2c0601810100203c0d039244038081051030300b4899250b001c10049022840c19080400c4440045402042d0092598650203a52540d4698600014800358407010248090910710000d41c588480500c801b00e0140c0307000c0c002251000d00d5500d2000c403a402601031442c14500410075203ca601450549070155101e5003418000f800c00540c11510f040440545109580342e018038a8509400b030716806200c00f042d001d00700e01d0350ba0b0032403201d403c0300c1c1e51203100715a051048411220701845042c400899440c199001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 515701232 1250 515699982 515700007
    0x1c020619050711040603110609031204151106040f1e0807030302030f0f0f011a040b190807021b1002010e01050a0b10021207060203060109150513170c2103 68
    0x2c0c01818852243c0901034048a030a1204a8085110281a403603407064041d030355042400017031101850140070380303a140c0d4040a500e0720b2940161302290340d1084002041140307071b501001c040100c0d96030302c003e070480341000d8803010f06c142c100b42e070042c0500d4400e101a81d50740d0415100c64007001d03441401180c4a104030708002c1c0c000d4004a4000c0b088080c00300000382c002c260342c00d0340c0740b18920804140e03590781d0030440d10200c0c1940c10008000c03a000d04110114040540b040944406014004100491144c0720070042404002030400000d651020381101c000455061002c0001003040d144424000781000c0124050b190031404410103500c0c0c44140b04906c0d03090340060b00c00d110141d600d0302c0c9414281c2401c0ba91400604800000c05609220070300010b000c1e50011078000d0750501d4041d80c07641c0c071740c0301c96103030040800b1841c4003003800001d94004072465a03940e40010001040e4a86580e1103180201c2d880300d800d800040d2103820781040403c0740d0b4003041c4070800070020304002c0740e848500340c0616 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 515702482 1250 515701232 515701237
    0x31e0d1404031533090b0303070c0b040515030702030a050a1e0804060e030a020604020d022209030210090206070213020d0204081501090e0d03150504111e091c02061905 74
    0x410313420303040410800204038103859111410143c0850041251a003107241005000381008103515010070041c000c0810781c1040c90002400310a810f81d0780d0703203140500300100c80700516401249550144200400b0903004001e454200c1c1e05424902da031078000703942c229600c0503400c681010800404907070f0b400d820b0344407101038030451144104025081d424600700d5600e015030950381c00160300003000140117003000d413201c0025900c003400c0c1b50b03504854034040c085120000f0b5065074103039641e45e0f20070043c1581041034100c6c543c0c880c1c104004018194020404501c1201c0c0081e0080d503c1036820b80d03120301c0c00d5044800c00742861300300b15103403a12000842e856011000c01c1640840c52800003103801c42180c882c03521076125160040540d1154041c1c141c014003004d103a917030000000d00c040000e6070303261030203020201800b07100c201782d68070203415421112205146125a0401c000d1054141d91784800c0c0b0070603402100520111480642d5100003400307880340f001071082c03007440c034807e0690440d0004c02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 515703732 1250 515702482 515702501
    0x903060e0d030c050903030d0e0c030109050a0b01050a0b07030c110a0b04180203010e01170a05100509160608010611210403021e220e1605031e0d14040315 68
    0x103062240281401c01200c4e54041e054003a0f505800c03c00004490701c00c00c3d800641d8a03010b62094031004010000042d0031521440001c3d00c0c50340001d451001000364011101d405402c0c02c4402c2e4120f6410104d04940c0c40c00740c0c1c203004003031142142d00c900900c110282542c1c11074070028440c4003503030744412862065400910078820030620164800741e9001080c02540c0c1610b1210710f01401a07032810285d4030707445110190b80b94142c0154150720000c80c405120002c0c032060303040008642ea00f0541d60251802c0c1c0b450004c1c540c40c04c6e4880080c014554040a058115842450b10041400700310902d503041106064a030748181d602072600c1443c0142804c050400c49001300c54070169142c0c4108e050705503418864030564412003040d100e0070200c0e040b10301e030301d8000c3c0c4a45000a80000d14401c251800b00c4052910b03042c1c05800302c1c1009286010801d1000c103050384031101c000810a00d54030740d6502000d80b054424044241200d80b118008141506e00641c1c120941d101840a90380b0f4501c02000c021f807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 515704982 1250 515703732 515703737
    0x3160312120b0d380f060409050619060f0305062703070b0a061d2d060d020d0804151b050d0c170d0209100903051506010903060e0d 58
    0x50081141500b446a005480d40140140001c807405a40b01e413808002c0c2d00ea0b240c1900ca40d208010300c141d0391403480101080324907000e04043d042c8031248049008008003958407541c04d00d98454000b440210b00d40b03800c20340655290700000c802d12603400152100341c1103500d82c411103100020130b1200019210b4010202c00201c400083e80354660020100500d105400050f801006a0350000302c1c0d412101e54041d01d240000102d5075180d4240c85000070641c00c9075686120400309000800c100d04d00000c3d0500f0b04d02144080d180700e82201c2070803c0d140202610b1040359a40e00580135520f84000e21100750b41e110402c2c554480e2581d103001040f00120086000107585150341103000315510060707090541d0800c0007003000c0e04024208444044440d1000c0710303140e2300705a5548030445208041e00f06082c42c3c410243c1c40e980c641c0c0030300c811003500c0c540200070010183d6041011a0020074221840ea0503002c0150340340d562040180c5500341e95900050072076140c900000b50000b00481e004940b100c06a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 515706232 1250 515704982 515704997
    0x304120602130e010f060c05032803110310050603060a03050111030f070207240201150f0509060609150f070c03060b03160e060d020d060e0c0a090c02030f0903160312 73
    0x40341581d85140c3c1c2400342d45000d10300c41034144450760180d010003118074440c2e400c8a1a0030300304092a165640000c114504071300040f0aa1451907130140a85c4c1c0c0000c880505242c2140740c000000c0002007014444c0c24001c0c940040495026202ca42240c0090764100000f171284c0320001c0003030b0803194801c071200505200c00b1004940303098800300c0d101045810341d443c02c1000201c40707400a400c00190440364010f541d660340682241c0c0702c65040345e00c000c003c1240041401440c1400348000054014842c3d8481e903010000300500d40c1d0703040c070a121446075541202e5251000a60702e00c00d01d00c03c2d00e80107811001020130000c200103841e00151030700d036010b4017a218030400c10403413102c0c049007900031035071f011240c44009406411320f944400201030004011280b03ca403562100411541031220391031068001101c020b9060038901c80d22001007800100810a04280b0800213480e4050460118001e403070000d854081541e0070040283c0c0310103031145102ca035942e60300d003206c041c2c03142091032008210103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 515707482 1250 515706232 515706239
    0x5011706150d08030601030e0d020619021c05101205030409140402032806050103150c020f03031504020f12152b03020703081803100207150e030412060213 68
    0x148501c004034040a031003425004181d0796041d8003908010300aa040507640c81e074030000700c0e008001290086c04180c0141c10141130000c1114039403100041d40c00703500b600410910b0125990b4182c01a4182c80c4142d00040c90345680d82511065507003030740f105110004840045d000d105012000f8012500c0d00c4000b0010160030b100c0107415100102e5000e545504802e1840c0001070b0312915600704840550a01003940290340d07508021541b00303030000d5541c0c5984115182c1803800910880c403071204140014450084400f00352035491000a00c1c00e000003845c1c400203080c0fa21282c0580318480c0806030087e80b80d0102062021aa20045503010500c10802d03201007404e0800b0300d152203610705820039070031640d901d10700c0004c6661030301c40048046204210002021070003110142c040d12076040303013402c01a4030300341c101362a04030220680421b192040044d000095a040e03c40c482c0343c28449408180e00c0907407002039045000e2a0701580080c0c040741d016104100f043da004004000800f407012019a48 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 515708732 1250 515707482 515707501
    0x207051903081e1e09040e0a0c03060f0213060509210a0201210c020a11090106050301050108090f010510031704050a03081c23090c030309190905011706 67
    0x319110240900c4800c01415903000c40e401040c03000400c02c44041c52509032840e61246101041ca40c1c2185003070004202511103242074098000301146e040020801303d112903e070030101c0030291000520441d503a40c50004401da942c1c06039101842240c0d04982c80700c1e44e0300d4020788070740d02c04c4c524140300310411518050904402c22103058010917030002800030408950040d5400400050300c444814030003101100c8007241c2d4050145030070300a9000d010301c1c510303520b0103148400c9800c090307601c111011001441803650007001d4070b044600900c0c02c400c0b40d4032081015800d040140307416454950806080003280e1101d102c1e801e046170b21685c051203245a110510b0a001d01403401403643c0440b41c02800c01c04143c0780b0002d007488442907500c3d010a18003681254007202c0c1119400041520002c02103030302c946041001c160302c20315000262508600c46000603440b17104d50304005101e070a0043c92740140c4188550000081d140340c0804000c19615100741410740402016420524840c07000007030494070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 515709982 1250 515708732 515708779
    0x8120a0f0320070602040f030c030201020d11060406051302030609010c0f0c05061303091805060906100e24180a0503150103060b0f0405150f030d0905040504061803020705 75
    0x9202612510002c0c0080c20440c501d502c9803000380d40b00f41c2c0034071000c199030600c0810040294403880e0020301c010f107180300190401500d401d45506004103141d0b4966201e40c00f00700d45034419441000050300f81c5e505d158421003647c407a08040d401d44201c10401503806030540c4101e00000780350700d8000c1804c0c2141c070119441d42e40f141004000e50000030118140d039464a070700e10282442424030300241360301d80390385803122240581d00008040c0c850b828400b090030200c2c1e1041d04102d050741c0451000d400150003504060422894600a01d2094100001c000c1d10403841043e05d4060456150358444280c80d030900000c0012646104038040310001500f860001074040c0703028403043c3d411249a10316107483c2c00403c406003007250005c2c0907100c0035106550318400c8520845030480900303003e04201040c0004003c1002542e402030b400322030f00d110b0407a00141e9440840b8022103010030b1700d40d51b40c0f520002410001c003605011a64510f510700405401065810603183c00741ca204094106e614140041c80d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 515711232 1250 515709982 515710001
    0x1060207141806040605060a082406120a020c0a03090305100c080c0a0c08040303051b0309030a02040b0402073e0105190c0c09020d05011d16030608120a0f03 69
    0x9210344005002c0b0b00060916612840040000910603901c201188150384074405150010ba0b4060030040840c000c1250303284940881001000c002e82480c000c90018840c41d884c80645221010000f00c2d1600b194048420042000b01500c1d803a10082c43d01a011000e140001c0b0b6590060021500f4956003500c591a030b400352035942c09450784c4540c0d001040b85e134000480d01003006450201304000c11065070040009600c240c1d5000d540d102c5103c0190100f642c4904030140c1038200f0000c03440d05540000b1342101031901281d00064a440490000e0000d01ca0700100a010300302507904c6e041e1141c41c01d607111082c0400c2001c9442d080d04141403124101103d8000139000c140c0030303c5482d4030b0501012291119110b41d0815072003480054403114a1050168090b404150b00029181d044900e240240e900500b80c079181003001c1803147c440007121441c01071554501561000d041643c40d48030750800301c02400780605a034410154400381c51074540c010401d03840440d030206c0c8801d02492084c4a842d014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 515712482 1250 515711232 515711239
    0x50c07020a05120c06040605090102160e071404031704060f020601030b041515080f07090209030c04320402092a0a0905040e0f060709140d031b03080106020714 70
    0x8904010070441d9000e80701c0c3d0401c1961040071250303000340d1940002040038110a844250701d940b6074100083c0f800e02400c05c2e000800d0807004007013064510074421190003241504200c41c00c60b014400d070480600884d840034021854002484d011100d250000b00169040303962001c4108017545c1c001c1e0790341c50083c80020401c07911000014003041c80c4012150880c1c400d44408150f002009100b40110010303600a010b45030800055013054180400503c0c000b4117480c0419801c0008210000c6c1e1260f0000c034041c3c2c016911880310440354100d050000d03000f0108402c14180d050120b500e09401c110003280c0890207840d404000c1b40c1991000c80105880380000c805c8841086009009440c094215112080130300c070400700049240c0e5034074040c0d155514032401c0100003c18000403501e02d40b000c0900f07140103201da10442800401c1600f200010680d009680e400c0348504c4a1404559020700b00f108032103024588044501050b0b80700c00350504036201e5608442c40b094803030324108401c27408048855030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 515713732 1250 515712482 515712499
    0x1305030409231503070f08070b0a0c0b130b060414070309052d100e0d140d0f02090909010e0a0b06040e030c0304030b15150d2a03050c0702 61
    0x49240c56800c00511400c206005040c0092104400440c0ca18183c540601e0140c45107202501d60038200031220081c1000c0030030301e00d801d2400300c1d01c5443d003400d8002d4901203140010244003250051021030325540d401155001710380741c60400d51003955114802181c1da00d41c220040783c1c013450980103104010001d450300100c0c40d11011800c0d8003c02400c10111150f000f0001c003120380f2000c0c1d0f030103105418001140440803510b0048898146076450000d03015491034290500700c40c40b400208140d4800c443d04240e01040d403030400c00b05003402000d51000c81e19082c0240ca60140c02c40d034003d0a41d069064417034050b1516603919140c241c1d00b003460612403652003d0b6400b004a24410750341074100c071010b0300000f401d50003d002c0606650201d403c0340901c0e40002004c00c100000904030562080041c04803c24602020000403a5114100b03409005d20001040c9000c3c2e4880690100c0b0241e0743c6036900041c004030240d02c1034101d400220050300860b00d0540060f082d10000707011205041e600a180e01d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 515714982 1250 515713732 515713739
    0x504020403120806040f110c0f030304050c09070309150c020f3405040222090507200c030a0c06032304060c21140c0702090c180a0b03040b13050304 65
    0x1034807000700900142c1e1083d102c1c2c00305040500720748100087d001141d00e8581e81d4100000c0381d1441e055049414600a603c100b0811011484c045800300d111a404c8402d4009516295412006010510000b81011a0042d0382009070301a6a1050310000d0380b9400b82e030689101202c50316101d8211110a00c00c031114240f28880c2c02086d061903100000d40240e00b00c0785c0a407518042402c907004054001c00202c00707241c1442081c0741e000d038098002c0c42d00c0b6200344a1840d00c01402019940300844402244c0011568110b00d0241400700c402c8056014003210041c0205080c029241d80030740c820b11010910f000103102e5035105600c110324907920480000a6079484554450b0003c0201160399420400481e4266406480e040f1420010100500d808629035120700c1c482c0c04440006404400c954400300701203401a19038100b8503901400e88003d04c0c0d1074560b4408000c411303884446100303910400c0e401c008101c03260010702450090340542c804c80c08aa0303d17081248070244c0c80e840c2c0504581d00c24007082 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 515716232 1250 515714982 515714987
    0x60f050a080f12032701090303051308040311060702030d02150a0612140a05070609090b010e030a0f21020105180f03040e060604030c080a11010e010c030e1503041407050402040312 79
    0x1035800c0b20400391a0410600a000305104140c08183e01171156510303404071070107060789401050741200358000f401a80c50340c44d681d0f99609114078400140720803d842000015590781506490707019402134203481d2222000032009440f0043c65611095002042c00407940c40030081c03142c0400e541500c0b07000490602c06441e200950719110450a11512407040b80000045090046000801254072241c0d291030402140c0008ea403a10000c5a041004215070310420350382c0000d400400603003211403103400305000d0130808440300d61414488181c20030740600060903603055118034032881902d20b000d41c15038042c06009803030b209a4815158258801d10052248604000d4501c0d0000c2004000c03501e00340d075a503030343e00040295502582d241c1d08a030100c20180110a02d844005030024a444070005038908000307082c0c12407116014040188403120000b40781c989000342e00300308401019031a100e16062804401c0c101982d085c005540c0100c00001403141014000c0d141542d9105030703048002904d16004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 515717482 1250 515716232 515716237
    0x30901051927060e1c17060607031206050907020d02100504050a02090a0209040504060b18070827062d070503011a07021008010602120403020a05040b01050d060f050a080f12 76
    0x7030b10074580c0c0e44c02c00030448004000007404500f0000031510035183c099000340c0110707000030041c0d141c05418010442190744540445071125810b007044550344045044200c0100240d8000f540c12804200c1403085158000400400b141459400c91f0f00c9071180d4078186081d11000d0310300810a6001d9062000103141c64018070381c2c1301a030700d84014109100b010000d002d0303800a403020340c0c00c41c1d80c44520303034844d007454528810403609140c07040320b050401c0d4000508142000b0048080c450488401003109110701162105030152041180d034141071030401801c49100354406404c4030390031804800307041c448038210070b0b00c250500e0703d840b03085078a82241d064102424072070f41ca0016808200030001030f9140e42e801c1098520558410740c0b998100f00019207082049500237800002c01e200410040c3d54112031282960300c00c1d00c020825440000060369035009040070790400905204d00840c900b8460100c910403200c003280d11621142d521910030391150704508012551b5004000c81c0d0030f41d86060b800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 515718732 1250 515717482 515717561
    0x1531050408070f0305030a0f0216080c03040b18041508030f090109080327060c030f0702060405060301030501090c0b180405070e040e16060e030307030f03020f0309010519 75
    0x101c41c9020a50b0b500c40c07800146007071048003c5013020091161203080c03031040003502000c84404600d4100b0070203a41c0440103070342000808649000500a43c0d241003801610004c201513101d450f11140380e08001e80d0910039283c2d1150041d443d141062418504280d102c000f10303403001000d5841e10326603000c90f030100d0380010041810301404510000700c0080810003084240a201c007038000307072085002c2c00d90085a143c82d07401c0c402e4200b072015000f0140040100e070b43c0721017007110741980c40c80c20388080364940c0140d0784030951046c4040000001d100041d0840d07600d81b0300c650101c0c000395888500345800c5004400c0c00c0141c01003505552545800e140c1d11558000300c06080400c014003c0b400054140d8009102c403d0080c1c00c10300c80110a070301e0782496903018200a0501684258018010a61f40d000d08680501001000c40310070080c58001d5044a520b8040900c0f03003650b0b4074112048134041d01040e1482c4080b200400142640c0490782d02c118404003440c0c000c103280c8542c00c02c603480d0841c1424003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 515719982 1250 515718732 515718743
    0xb01020a032c09090604060b0a0f05011214182503060504030e1002030703020106080d020307030f11070f08100623030c040504140733120515310504 65
    0x30314003580f90303100b8114a00c02d0041c070008140625040c940002a101c0c0c04500074028804540148800050700c90220151442072170718000103403001c01104090404a40113424445800c000d00c004050341811860160310b44808445100e01c00401e844000303e14038420380040038115409000051681e000550070501074070700721203c16041c0000842081203011960090380c00016840101502801030a00500549014001c90484c0d11006922481070300001030421004910076108a8003407404210700c0076800007160001c60311605038607840c0c4045d016051452298046c20908c410850103a00e060b2203440802c48000c152a4900760303c0720410385c1e402b0358580120b604901032919148103080c8260301682410140e4003480102d0745c00c050301504800110340c4522a08000c4c5200030301d50003040b00441c102d01c00c00442e5050304640c1442684902c0d10340030304160071300ca505104040c0c8148813000440d100c0703c088e440005889117505840301e00d22038283e0800815900041c0c181d002c1382c0d00a0252 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 515721232 1250 515719982 515720057
    0x910020a05012406090312031d0d09030b1305150a020906030c040905090609030304120903021002010e01050a0e060112060e0f070311010c030c0b040c0b0a09090b01020a03 75
    0x41c0c1c0d58a082d5075800d0020071003000c1c82c0744444400900202004020545420042200d07130641c3c035404410b040840c2070005141d1170740c91403085546800101c030345e084e0024090f03d818980185004000c110305104c1614082400004603080005140e228205281d0141c002c1014441d13040e00f1014010008000b00d4030399a090240202e10707150314004521540c2007038096681d0314103206200c011583c2c050204d00343e03a03104204009010800008903604150000c01c1140a00044071080701c00522540000750440c92840c0106109a0150400002d95a002000b030000b9580d040700b200407100c18051180e05a8406001004100d02c0520b0029145004440205030309010100203483d110f007200d4142ca040d44121010002d1240d042e084683c514800d1900c84070300c103815240240902c0c1f0b100400b41000d06020003080c204100e00000c5001404043c500c1c980301d6000c1d1034040c0600c0040c1c4110341c049410541061025880030450324400c40c1d040d01d50301c00d5560364900022030100c2c0300900c140c0c1200705 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 515722482 1250 515721232 515721253
    0x90b0918070f09020405090708040314130b0a5408070303050c01050a0506090c0913061e0b03101208160b0402190b04180b041803080c0906091002 64
    0x2d91240c2002d025128000350380c5a01d850180609104010840010002000180000240e0101e40d0201440c050516551101503030500e040c4481e0715544042c000c03210001e610b52880341c1000100e03182d8001001004005c061007604074844100000007514a488584078501c98081c41c1900d4100304181a11040103281c0c07034800179807811005401c05e8021500202e81c401d4840030900600307901100c004010f210b20300b403900104100c41006810001805c401040c2c00501c1d0b1102e07550200c020507554800e00c48990f950700b622800207040c2c034480c0c006901c400800700d07101c0d0362403046a010f01d41680301203d42610b404d001d0103200c2080502124986800c010340030050a07500c60002c0b1560040101c00301d00c1c2054030400c07101c0310070b40300f031240e194040000070404a2a80029a411a4039002d4000e561001e00c80418008140d11034035154803929002c0305084d408a80705401d4081442500c400b0600d440b034690541d5a4054414242da1000b02000f0711055410101e980c900003183c43e00480c0d218100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 515723732 1250 515722482 515722499
    0x50a1b0209010905180313030807030201181b050904050601051014030a02031033031805010902090f0103050a032f0f010b010309050304120f020a06030b0109090b091807 74
    0x100783d21a04499481d54144861141c001e4064040d01d45031700001c40c0f030070350a4482c0581c1c0140d148070103070011a0205a540525000307400080141c1c004420500000b5000d141002c0840d4030200c0c21002d00c240c10101081c1170134680716250060740c114004144584c601000c1000100c403a0303c00c1010030a1122041f10382c1e28501d0061400f0310040341001d82c0b82c0c500a100c4203000001540b00705c202c05440e502000d540b00c0150640d0400c40c42a038041460718001c10020340240c0030000c2c482c1c9440209400201c240101035001700145c5100700c810715007940b15101a03607000e060030300010741359800030341c00280000c0c001c441580c10304289486030320141d6000c13010403203010040002c40110313400c9070702d05600e140428458294414000d0904010001158840741d5681c09140210307006c140030041803c051100600d04041c10307950083c10040e00300d4a07020018080d2076a0420b09022400040700896561001d00610f181700c0f0028000040558421161035034880c0100c4a50313080e8010040041000007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 515724982 1250 515723732 515723749
    0x31b030e060f0f0a050d2703110c0310050402040b04020c0d050c0a1401050405060106020105190b150310030c050307030807020108130204050705070203120307081906050603040b0a0b040507050a1b02 87
    0x10a50700c2d002d81b04c55038000b00d1026102d50300e14100060841c0050703c00900c406010a101031500361030b0210030360011811725450000d0854035294540b0410035442d003c560160800ca110385e1007540e090105082c90400c0c44264010903140790355541003100d802000e54030841c0a0041d05180800300c607000c0140e0344840c0701d0340a0130071801d003459468104000600c00c081108500503e0688001c100c00e01c0c00400140b0421042500c041c0016110504c4113450b54820740d05100150350604110340d21b00b02801400181c0c0071a11045030032102074100007889140205807041241c0d089988580303880c20680c01120582d10080813100600201e50b0f4500168840d480fa0512900c1203864056a40280e801010702d014040700f0340d054681c4040040001160780046501d0f00b040c21056060000c0c8618130141001d0542500520f400c80d1002c010003060218200142d030003480f101404000054900c0240000d6030b4084950388081041080200b44d090312410368000c1c4c0340c803600c1c2c0d440100c424650000d50f050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 515726232 1250 515724982 515724997
    0x1e0c070f0f02030105090a020a05100203040e010f06110c03030a03091a010b041a0426031b0127050c0906040e061302100807090504020307050c010f09031b030e060f0f 73
    0x11030301c05030700408505007449801d401005000042411b0980f541c005100c2c442c4500034280110440d5042c000d14034004c10994004e4400948804d18541e101c400f9444010341a02c2450005041c2c031505401101000c2404000f01101402131490301031240c1082c0d024041000d401c030340f00406447c41803007070b003680c58149006e0000d01410303e60b41c03807606012044003940001b40b5091a80108000c0040c40104245001c103200700c411050706582c00140c7c0c05007540103402241201d0303a0f0f240c13903001012106500c1038101001481a1a0b0b41280c0907140f11642d58414038002e10a900c2940c41040e2403608441d11980020300801c0404d144415050060070300c0d0703041e01e00400d10a601d045020851400554114950300103140880340392410300c40003005918140b24040c02a9400000315000c1c502c0f03041140d09091224000b48034204203541140004c01c46076405900081e01c03480302000401d14414021000380c0c01d0713620004000041c40411a8a5001c28900701e03060f00c00300101414640c41c0005032406 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 515727482 1250 515726232 515726243
    0x5100b09160311071401092d06090516090603150516030b0301061e050406050f0d06090201200a1401050105010507170412081804181209031b0612051e0c070f 69
    0x41880b81d1030589110b00042352254a0b9074030b20700c5c030245803800d403400c4c10644c1d5802c03c0000c100b02000381800c0341800c94081b0768060303000d04c00c14003042012264018000700c078822803030032552220500140040762410348480303008030320304031403030212a1080d004000301500c01000041c210742d480345841041555a40c103446151800b070810841460144205001083d05580210b0b5101002c2d001491a00041c00c00a018030340d668810000d40e403144407561800200a441d8030049014915002c4e0b880341418003c5410f88100066030306010818081c0714120348040c1c46550910b14140e07a12842c0d6000401c2c1c0d00c0004c5800e02000819022140c58540128058a40300743d0720320580251503412414124458002c030306002e00010801c80c02d40c030031405150020300502c0070000e28441241e416442d0313071002e0715030342000c06174035242c0800e0b40d140d070112581900d440110100c8203500c0010b8a404440c0c514203507480e5003110484480214440382d1091100c9112468249583e40b450002020000309865 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 515728732 1250 515727482 515727491
    0xa05040203090d0207090524150408011d0d0503220b0103210306150e03030f28020703030c080702130c05180301090b011205070e09010f05060d0c05060903010b04020705100b09160311071401 83
    0x1c50504130584041d41103437100240603807003031500001c3c240e844040d01c03601d03011501c100d04009001c40301c1c8003201c0c2a0741c444641001560b59081c041d06028141c0c12203c1c05880144030810403500903c591030841d900000f50008041b280307001590100ca04c128416014003003040b0f40000e440109009014902c0c01840d15031071108210032009004503410308500955201c05000d102098101810144803980010000d0b5280d240e403001c03688840d1001640301d9150f04092203241000c1e001005403101180072a1890102d00c131710f004042c00e03190541406480100c5c0a0300501900c91091502900c0600800407180d5150790740e020202d14220407203010885941d525412031030400c01e409110380105d41103540602007442d944a0f50f614881c40c0c0300c0d01e4803900000402d0344c00d0b610f0a401c00000850001c00454654066003003850716068000892101e042c68a0050b80c0c240c9407400d110f034020000b03848403251204d0000303016401003031880c5804031048418441c220015030000d03e1041c035001503500205 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 515729982 1250 515728732 515728751
    0xd0608031e0c120a120501032006030708060f0a0b030a060315090b180703050f071517061e040c0512010603020f0307120603020d0501140a060b0f090a05040203090d020709052415040801 81
    0x9c0a41841c92100e4813a8400300144606168004103035078001d0070403108455092900000245180c00c0c652152071248004010880d840f49282c0c03000080b20700610440300741c500c0a4400078100ca84048009007130f40010408540b110001c40c0408105140300c00880321000d03169202d0615200c5030034564802c69000306010b001132810340180d0102d40702142800d06001d406181800036402006281d41d0042d0001e050342c02c460414074000600c5090080c0c0100991074098000404a43c0400b4080c8202c851010001130750724400d1080b5908500c0c0500014117540305c002c8119264000013008510441d25000d003c000341e0b0b01d080400d18510301c9000006602100d001c125034101c800145240c0fa40d81c5818020025443d081044440081040f120280d9131402540001c10b001081c1d040b9035007151010040040f403050004405240d10f0440d002c60304101ea0b0344101c5000c0e01c2044454001d084140321b4100b00d0300488100700c0c4400c41004001d003c0d841c48800c1c210900c1d0300b150303105150581d1144130700d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 515731232 1250 515729982 515730023
    0x7050f1602060d110a0e010801050d1b0e07020a0302010614090c031308210610020705040c0315030602040f2702090301020c06040b0a140c040303140d0608031e0c120a12050103 77
    0x2545413801c1c21301031941d6140c1000109225803807400a848cc03d19868588130b0400d200c50048050001c507909030900c0c3c1030030207000b540c89907030b000100d003d0341c608107000c42c60400e13000c1809620300c1c00030700900c180d5072403142404403904040c001c0c201c1c01c0400b000200024940c2c60262104110f036100340380b02c00003240b6003d4015840a08101d0042c0d017102078a010040e03020541105480302a50040f50010045000310010100015200d290010142c0302008014040d001082200e9001d1002c0c15000d03140d40a440030030501d00c030308140b209102038502074507640603000740c6400038000300018113101050000c0b5090240c00c813400c8408128030420080c94404c6882649548406100c0c80342d050301d401006610705118a01000e001e0040c250714180003413055504a0303141800c40c0e1410310905540b600d03c1940d0f1340119039444000e5007240c4802160701040415a903603c40351000404208035100c5100a041d0f021085200800814510341204d844c028001d2038000e40c030900c05a401001c801e140b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 515732482 1250 515731232 515731247
    0x11205090d230c0c040b04140114060c1507020d090e070f031103040c0f060309081606090c03060603121b060f06050a0806190903020d110309090a05090607050f1602060d110a 76
    0x40c1f040740741001c0034007414038004c2801e06642015188a0b050b42841001440c0c03401500c00e00d00c158401c100c2418000390001d00d44030f0103440c141d0211580e4080c849001e44001d01107014442001c000c840009040758480c10741081040c0e514140050780f1420300040b45a6680120340c141d5151106030b8081008514001401c0c0042180b80303010007914201d03542d42071180c81130181e8608813034100d4510b038007880349680c890501141e20280b8040755607507924041300542018442a0740c0d010b01c15801c100c01c28000d6034401d602107121040006100e40540c0c0f960001c00380002c61100c081d80c2c440c404901611126000005064031000411140c60502028a014154054003201e002d08154031100025000500001c49601c40c3c1446400d80141500e12032840c000c5402041e40064404203000f00b981642d40840e000d240c0074010380b0b5166903480c40948a511441440f1031032900c0070031449203800c0c00700c400c0f80002340c0300401040c03409041c202500f05861614900d1561082c000a00e6140c1e25008501d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 515733732 1250 515732482 515732501
    0x60a0b0a08190203100306090203030c0105010e070f03060315020c012d0b0d240212070e0f0108060105040b161424011203080c090307030c05011205090d230c0c04 71
    0x606501c0d51a100d5445c0d88405020310005102c40c0d00c84da0030704110364050042e6428811000d00810056a444121500c810070a55220001c01c95a102800100f40700307000e003100b566084a10424082903409280c0e00940c4410303031141081d50390f1b544d14804031611101580d03413000b0b1003082c4130000e5031054440084030120709400d8450131142550900180444c0c070b41040d0442d4003241c8920344000c0c02c410001070311a07800801a40c000c07480400082c96000042500a54803c0d104d8400c941011001518a80c00594460703000c40c4090104021400d60b0000600318038414448411500101c0d0b41c41d8000d00351184180d40e0160020b0600e450205402c44d0b8544c003902d520750340052607503d080c800d162000311103507001d01040f400340005402da400c52400c5a43e40f410107411070306929940c0c1403c901d5034195018543c00200f4500f0720b10445812400380c94003903501c80015000b41e1f003480d801034680440351943c0e900b01c240350546944d1390f0046070b8090301c1507100510251400822500c00c21084600380c21 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 515734982 1250 515733732 515733781
    0x50705040906141e011422092a0e0607470c09180403030b0d0203150417070501020a02012715150801020c010e0604030c0b060a0b0a08 59
    0x340694803555404c518401130729102d02030611054184c1c0012501d0920030b02203644503510000d40038003c001c480600e4880c040503100e490012503129440d003416220b00140040301a60b2140b44146542e298115540810b212070400c80401000c0301f0214941e03412000b01562181c3c2c2c1c504038000c0b040580720410140140c08070051090358044c1e0400c44035628901d030031210740114000011b0b14800d082d0101c600341440123011300141491b01c0c3c035103a0401000c860440010b0304204045016007841c00302c42c1d0701503a00401801c2c020b1410f110074418040002c20a071900c0289694204030820840b0091414500807800581e640141c04070281c00d503490800d2000c65500813050846045840d1004141c5a80c2d000c00b01c20844265240884050941c4003030240e0700480610002640c600b05600034150080c0502c000e1021100e000015a00c410040b540980400c00c100d000c9400181840c610580c405401040c00e40e42c075480d0206d0305503a80020009402080c00c5109000e540100d0072380d006000f013402c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 515736232 1250 515734982 515735009
    0x6080609071106071d040906020a030b100e1e0405070c050d08070f050c0a051605040b0603060f010507050114040c1706090705190806090307140d05090904031101050705040906 77
    0x81401c5a441c038005084c80200200c0003111201110501001d4861460040041c411100b45042441c020b600407014500824540000c0a4090500c41c038102030501082d1a080346041295050104170201d81140c5404100024008100c0b0740da20301c211401032040c1c1e65001242d24552400500e869250a40da5040c02803910400a00552003007161038040301b54a01130780c5461108102d28904a032120009090740980e00c8070070080944841c03100212002114280541c6071a0414024544029207032039401c0a4071001222803540200001c209007071041c80005032050b1900d50903205190300365811030f0101601e01c0c003008030f20800700c0e104010403000c0c0054461030a01440140d518090b80c03061901030f00340b03441c543c200280e5042d2480003c0516000365080c91402031011b544903031250030100c4a0302e0b000c1850401c4000005901c2850407019100d80d840c1c01c03240c1080210000c4010800c030b0800002460095080000b070042c180141940c4e00e501d52100e040000e15410389000390000040f11554 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 515737482 1250 515736232 515736257
    0x30506090309090c09030a0f08030702012004090c3e0303070e0103050606071502040e1008150c0c0d0207061d01080105060c1c0819020c1506040b03070608060907 71
    0x82c1c3c02a00d801854400c4416651040500446c3c10003010100c05004001414404818069200c0083d4481c0d031039903000304880800740c111382042401800710705020040501c01480021000d5020300c0070f815050074004001080b05100e182d1500482c00c1c804608040808014242e000072078003480e0388030902c0301a40c114908888000c22030390103000c5c0d1504250b107e5001c12001d48401003211802a001700e00d01d900340711000c507408065842441201c080a00590006a5200710413140c41c00303651408000c2c00701c00155580840c40340300040c0c18035804210421001c01c2000040041e03461a411580243c0003403854030a0107006a540000030f80740240615113110620ba0344040c0c0541900c0d000c030342d00d80d16040880300030317403515041c0c4014001858850081c40200341d00004803501c40e007030f001410000003030301c1e00d2000168020f05c94180c4040e4015120395103070881c8080b980358002c40141000507081003c3c00040d107009561381c002404031316000140000f50610030182c80d8000000e0826440b00d104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 515738732 1250 515737482 515737489
    0x50a02060c070809191518050616030f03060f03030c03020601051f1103091009031403070b060d1115130e0403050f070602090a060e0907110d0c1401050c04030506090309 74
    0x71303880d404c5d214082c880302c1d07100c0c540c01c00721000020701a0700c0312074200500751880240c007501581004c3e084882c141000060300340b0b407080845043c03079102c0e5503007081c0302c0703450760700303907403645408820b10103041d2202000f01c1c5c0300c802008514029030096903900303c3da0b0100c0c2000386c200300068000c240208200703000c00000c2c1401c01300340c0b40b810324a441c0c8007da138103041181d1400c5002c0c41484a40c0b025070a416203141c642d1014a24040d680204912002e8105a54615a5910800400170408000750f00040c100c0e1900200b00c0105070b004280d200f609602d040c002a100200700045038010500114210b14821001c0300181c0140112010394560303404c0031b0720003400502400c0301c010380d80320001542d0780c1007001700d030140c1d50a000e0150165804645946d80503042ca0300d48d4032118050301c1001d00042c0280e11a42c190042c60400d04081d0010720001ca80c2107230903401030503094500f200000f0003404802000d1192a11901e012000350752664150316182e82840c03400b40ca0100d05030320a1101115540c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 515739982 1250 515738732 515738737
    0x3060b1518010c06020d05010e0a0e0c21060712110903030f0f0d2a080f060112020408070f06020c01050301150804141903031503050a060903050408030307050a02060c0708 75
    0x580c0d215851070515103180100c410601c00c0750001e018030300202d00000c00f2203860300a04c1c141c3c0c10204100d111940c1d201001c4048030710000300c0d20855400704000683c0d41c00d0151b4804422543d19900c008200c000d11b0580d89054800c5d0f907114001ba0280c0000c1c980428207220300c007e0401502151850007803076900083d81c0b4043c10004400c60030002a0000b55090690f0807150070b41c0b10348806000410140d81c3c5003414038414021a80070784009840041c1042c0704100c124842d0300b0f44411400c00391192001100d1521740c004103000625800c02011401c480300300320702c5008180b00d01c41c004d40c15040c0b0b0402410801815001c0b81481002d00061121840709100145100314520700340c0402e649a00b00107480c80c0180010550600851801d2280740d0100c00d811301d1704034060344090003486c4012032080214040c9200107841a0010680c0b40005a0301e074000c80384040c040d04d89035003801c2d10740c20703000d09681c07081d10307140042a0001550000c5a4051051550003036107146100e003041010f850340522407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 515741232 1250 515739982 515739997
    0x604050c2d1905040303080a020306091b0d2a0203030106090e06031006030b0703110a0507060e0114010f0e0108071404020903100c2006060303070f0507050603040c03060b15 76
    0x79505000041e48075240d080c0d4006001e5400101028410603001034050380c014002500020034003400608103e80034000c907401400f000e80755114540c3c600138661044540c080ca1800501c00411071501d130740c841e0b805a0002d4510002c80e0845200800300040c83da184403105507000c3d50018801002038a402400d00b00484a0b9002d030000565143c100103401c1807d406882240c0a1070904007209100355039a21a100f1501c1d42c60810048011455400d010b010b50940c0c2d000041c005c2014400103a456000003540709060000410404d149080009600d03400740c1044101d02410081000410140c7c0c00013401441624042c08040d07051400061084420b80301d060300031350300046c4119498400b00706c14402070301c10100811a41e245110004e2900d50028002d41c1080c0800703039504103030403012071030900400c4001c00441c908001a540e1525031400044180d80c1070044400c00185600c4000c02035114500c2940d03507800d510b0543c64840110f0304e804510f02c1c012203880f030050305403040c2c100840f20075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 515742482 1250 515741232 515741287
    0x21040e0108151f05030d0504151e03091104020a0f081e07050702060d0c0203040f091506080621160603090b0a020d0e030412050d180b0f210604050c 65
    0x1c0c10344045603ca40160640d0001d070f014440c43d81580741c09039100c0003074800d80f2009042003001c1c0310900343c116100b1003000c2d80d202d0302c12604e007900198070703009500800e43c0c41c1c8210440c1140c2d804000014049802c42c021310f80210f0352074415401120390080503030780d10440064901d100d04045420340f0002180c000c002e034040c0040043c0f001c0a655642c1c0a4481c8040146018011100c119100a4480d0064030176821802a506000f00b00a040e5004949e907052440d0210400240b6000c01200e0b0300d14043d11309038020201007003426113404020381c401c13452010341005201000740c454449051085580c0440105440c08450710002801c0a895603080002c01c04c01503128440d1b000c400009003800c501c03084080c480003c0004480750f21a420343d000901030380644200c802420300031f076400130048402c40d1800c03075074041c1441204081e00180482c0f6040c0015113081039000c040c01814400c00c40c64984610350103104120042c0303428040c0d294080f1a101c202800c10802d002e90741d4000c11418441c0c0036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 515743732 1250 515742482 515742511
    0x510270c05090628090612020a0c15020a08010e012303010f1e060803030c0f0d0b04020304060b0f0f0f01081803041206050a1109040b0321040e010815 66
    0x480c5104800740e07070321070074010030450340da81400d81042050003110013800380756411100e1a071000b90003660184101c41040d103a01b0481080310078213600035480342e1a1141840000c0b4212000319040b000a444004070f0712000580d1b54561000141c081c00707050740014500c3d800303000103100320407001045403120440c0f40083c06150b05804000b0740034100d0340c050010b4692070042c10041c0840094100c81c505413400c101040036503112480c00341c5030300c001ca60510a081c010000c2c0922642e645008207040c00e003d110014540754590300080690340b0545040e070740c250715007000da25030f0321701403014054854045803d10040d0f90042c0200f071442000e200d540d4140000e9a000451070f8007a251a0030442c2649020b40b65207a4542c441002c2030a05408242c644524000c005441644984243c28640206801890605c95008200000350045041c00b81e0140200c000d213013941c10110000903000c03600f582c85161030310f0a02d5000503010070140c0c884041d03030303208200c82c040241080604c1c60f0001100001c161 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 515744982 1250 515743732 515743751
    0x60f0904060801151d01060e010807120507030c1205060f0d050106081905190c350c0f01020c090406110403120207030c080307210c050709051027 64
    0x14001d1446522090055003010b0a00728103003916900902603451140a007080f1009511180c580c0c06024050321003c906800880202e40d0f004406061340000c1d1031030910460343c81a112207081c1e8205480120101e03840380104811642c00080e1100e0360080c0400408c00c0340f900b00000340380544611300c00743c0245050100142408020b400031000341070244221141d000c42c400c40b10984842c0e42d00103948900403000000002c010040080404035002420414140c1c10000c0b105040c010312002e03070100c11405107810b0003500c4441c40d0810140e42c0000070300661341c0c60b0414000402c45181c0610b0454001c00384101c0c1b02d5445040181c0c215410410010391102c3c40c843c0340c0c02601c510340015000c00076405c0c10094403580003403401c069034801e06103054881ea07514070190b944d0298a10041c82c00c0b2420228400e5014242490b011660051078501003a05070703521020308008403600705101d0b45441e40c0420074444c0c0c02840500080ca820f0f1144120703d0074031001031103041400915100031541311800ba0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 515746232 1250 515744982 515744989
    0x3020309060a0506011b0507090b0303130510050904050f0108060c0a0804111212030a0c08010e0703050402150d0906240b0a0207050a080f10050c1e131d06040b060f09 73
    0x4010342a28400801101c086c5041c22507980445110b0710f2030b81420065850300c282008000d4510513400e10072216020703400c020802280d40e484502e80401c005052200044564443c0582c6015074050314000c452175051071065410540018825500f00c041000903a940035400304034198010b03000003040d01502c411100080c800c0c0312a151030140ca1058811400d8200c115400031030003000e05041c1000341003c00b041c1501d50031002d1140c8204c0c2e50380c00c00041c1003140203400480d03100b0300c02000c000031100d00004ea10f445d0b0300040d10000000350b036003010108000e014440e601b0407603a2142c4104840c4046488540d41031418018802c0204022505400c2240200310101c00f81030006c190180031529021031550700c2c9505039041c40306100d0030310020b0040300b19100769401070342000420703807030440080604803d16558100b50440c1f0501084034035045c3d8035030144503015040360048503040c3d115000d0314414140010340120b2080d8982400c1c07101b50794408003103c0701280000000c6469031030b080d000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 515747482 1250 515746232 515746247
    0xb1816060c022e05280507030302030402041b03022d1b070b183307170705061f0506180f030a050c0a0905100504180503131503020309060a050601 64
    0x2401d6501e840803d403109642c0142c0a4615070344400c1e0500080c00ca00d0720010442221760020401003801000b0b80c8010910075001141c4c014005171000c078000400c01c6107a2004020100d0410010f6408135030099029150b1003000c150311903c040200502c600108000e5051183c1802945405118400c1a05480b4107001c510020090850940e031141001d025080da0325200c140b20f18418100c010a40e0725003003800c0000c41344600081d004940c04082e02c580c0300e520340d000740c60036551100c011982c0f100d107003801c0005202640c40b41c030203844242400c3c1e058001d00141d40010352074104160f5428025500c2d250140c8002047e0a036180c40c107920b4807400301e000178503442a82038040c02004001c1c01806000220b000078204240d80c00011990b60750012022690140d40c040765045000f1000c002910700340e004000e030446503803030480c0307d41c40c1992000d145503c031814405140765004020001e2008020f5000b6124101e82029499850101302c04c0703442d924000c14482d003142c0c2d03400105000d41d104000c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 515748732 1250 515747482 515747539
    0x2180a1e3b19020a0e13170f0f091503040b0c0a0314070c150902010c0204020c1e0106050405010509070f0f020708070f0e0a0606090303080a090b1816060c02 69
    0x50b20841644400c1c5100d40020030700c1c041e405000c0000002880d882e0444a0503c5030301d900b9140e410100706540c400f500c0e0181041540102c0c04184004240680b00c440280301840305e00d4400e69850300c00005200c0306a5441c3c6501410000c1030041101045180300e0842e8401003182e0180d81c1d40c0c001c144d0580c01400220082c8400302003541c1004240d80e0401018005640604205001d812401881c030065904200d0001c1c0010002c00303040c001428203401a280c0781148506903550f009031100c80d0049800002c507800e210369101c403402c01071030900d4814540904001c0e91203828902d40040f0140000c2c0401904c807041040302514850719a00c280100340c05030003803234141ca07102070303a0ba40011254401070151a82025110b40420940e02042c4510011680f00e619810030307082c5561420385080d0b000408286140381c5070b00c0707840c0016981c00d50a03881440d5251803103904880c41614540f600442c00b803915086040c0310401e02c8042d40000000e05201d034100c032900e1084a201854100c0c008a070f09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 515749982 1250 515748732 515748851
    0x140f0105030a020d02040f0308431e1209142d060316020f0309180a1b0c050c01090b0301051005070602030406060e0c190c02180a1e 58
    0x2d004805c024000c0010942d41504402c030891030564190100040c1032b0715805040403001c0040100b1060754800304c9210028065540c40110509a140315003800c900b04a044a03415003418100181079085140c56002e400303040e05040341001124042038100b02a00508901800b040035608000c1040b1440e22000e210080e20654483c1008e410b8940300140d01d00c06440540202440030303a004500009a078018400182a404440302780f00c01c0c0c2031403000140c400441291212115150b24100a40d00c03d00b000580c2c0e5601422141400c01d28202404e8455003810412601d000700700c00411032065a0540b00b08403100d00c013404120200751103520501070001e003020300100411090007c250700000c01c035944202c103150301d0350380c0c0003c2046902c61002510458007883e440a021584030f950ad041ca600d2000d8440b140d00c80d00007160440510040ba400e48020382c46000c401285140214820340001c1c0740039044c03164881b1115900ea00c9881c0d0610041c2418034107404070b04810f420b01c01e0400c16060031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 515751232 1250 515749982 515750009
    0x9030a0302220b0414220c1106071701050d03120b030102121302040b01050c07120f051027110d020d12050903010507083706080304140f0105030a020d0204 68
    0x43c0d00c0001150000e2090f5a199003003501c0700c001c0d40c200501d1078403804106c1e20103941014409040361008203941e50203134041020a0503803000718001080064000d181e02d460300c05c90000f00c18109828110140c0081d40114260104071000030781110805042410031807011440d04000c030003080c02401000071040005403d1018481c10813420002d1468182c025030341070140104182c0159aa446a0301e8110080da200513000c01c00d4a102000041a01c3c0c42064042d02c25001034607a02e18191103c0e0710380c00d0352035a645e4204402c03140780103e602040603440003a080d900c0b09888214540c481e08022602800381824418115590302c3c0400703140f143d000c180a03d005003400b9005150707810052409000b50310300300101e807010b070050070031920540645402e13200290240024045d00c0807644080d12030404007154141001d075450044d800600102001940c0302c0303240c101203611000030303452454000d502c0d0b400140c0b100e9a0280403241d00484854015036034101da0001c880007440b86601440c00b00480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 515752482 1250 515751232 515751239
    0x6051011030c03070c050a0801020f18010903020612070e0a05031203061512040605100e010b07020d0b010617060a031a180304030c0617270304050d0f030f050309030a030222 76
    0x175070f02c00581d4000d48504103540d840f402d0070386c200c0c4100004104650020b2000f140c80e94500c1c0c0d10800d80781d1041c503050714116582c0e404160f080c2c00c000d8104010003070f00720400111907441440c0d440c03005070440312001e60714a488080b0b9280e01209034821044100000080d04548070480300c407040442e814085030303407007404600000440e102640d0032039006003024049240000c210342079000751101991340d4803c40c0d107000f440519582c00000304a8000f07003041c01140126503040c41d041d000344016151910030b01c200703003410f104841c4010003841c072075500c80100340045440e116403d12103140d2501e28500980700c0b0a4048402c1c10040840c4803039100025012003040000d00400f01100c0894645500c83c140516955194800448840c6250038030248003070740301c1c0407000e0000308802041081d42e141035181c80c04a012240103400540c1c110085410b200700b01175211101e070b0083ea11903c0c0603030940c20550500b5440e44550500c010801d034000c81c0f02520413a10007003040c00301c03243c00b407200381040d503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 515753732 1250 515752482 515752493
    0x180203101a3f120405010e01030f090204050906010801060b0f0d0902030a0b0103120e010201090b04060b19090905060603030313150e101b09030507181104090b0906010306051011030c0307 82
    0x646040b212280160156280c0c50b000680c10741d415120b050f111180210010001107005105040d5144161502c3d4048040581c030303a445141d000d0030b841c402401300d641c141007056003501d80e56400f80001074010000d413110182240c090703034050740031081c01082d0000680000b03841c0014550010342800d003401c1c0000100050b90403406907940380c1392110b281c0d010140006a00300e03180c1c9040503144009400c001800030341c0c5903101440950b4018180311440200080d01c8401d10225041a10001c0d40c410401c028000c1c00c105059226600302c2c0203626514002814507000340060000600c140720b0a4401c0c80c48484a0b00f002821858110440d80c0180300341a06c2c03000750115440207018056041034031a04203100d291000141e0381c000340105001803620795031451501181e04070b203030040d0361442c1903250000700c800140014000a0b501142c0303a403e1904001610b00b000d04401e040c0351404600308210f0f00d80328070f490402205410400012180d0024050940c0329104141e9664003000403014100b10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 515754982 1250 515753732 515753839
    0x30b091510060810050603040b060301060f0803090a09021309020306060d0e0c0111010501062a08030103080340020109030c181103010807170709180203101a 69
    0x6159035602c11894a4010096400c04550301a4071b4011100304001004186038180040c0c100f00058000190203030f49090318440180c81390091250381d00300041c81209481c084c04114050007684404610b8214140103e181c65825032003a00080d83d004400101160f8a8000790369642c0b107400c1d0113010f00008021090f45074501c0004041c0820712541c03040f80c41820501c51141a00c1c02519103003261700941415094142d90f91071980100e003500071229001a48490141d0b0003076105107101e03034890500c03901100000020110b200451700d894030010362114603c1084098075101610810500318841c001241c0c44134050300040c03c0007021500003e58104000b001d5000500307180404c00116840003902d445520080c807601e0059408035a0500100224088030510481018101c502c80d9070f49011175001c1d50980c80c0620f40d6a0340e4140d001040d800d043c400441e901038540d40810810011480c22070844c1c2440500130300407010603842400d0044948800504034488207140342681044840d0a038804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 515756232 1250 515754982 515754989
    0x4060f060305090f1e1c0f0f030c0905010e130606090503010b0108060a15121404290a0203091207050102130806100b0d0b10030902040c18030b091510 66
    0x28544030000f40f81d520081440003040b0711101c0030300a0003500203a821051099010503419038081d054503040f240c0d02c0b42d05c2c0030080c0541502d422403a09a15200038041e10071a840417001d140c2041d55449845500840c100c06442007400c080c3d070365140f80c03c04980c032409500301c0b002d6020710300306000c01c650307070410503107412501c0c220b00910191034144011200c1c440156201c94000414110034449207681e402004410280e900d0304100c0da02d50369065400b41c0f006880c5404c01c0140e040c0c18801842004218400c08a0043ca080e0707203803d04040410745c1c1c955004000614940c1c0c08400f08012a50901612521410245286441e0301c49802c09030700135401f60305041007d1002e1100090307100d00110f9114481c1003d00f00c400b5070145418103039071f01a40810038504046039a001c0c2c80c1410b0f0350399002d41080345000e03540003a50340c070720703106000440302a5a50501880302c0a036020700c03010410031000081d2507200c0c8c4000800c3d110327100c40c68902001e47c46040c200741c6000e410000602140c030340711403c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 515757482 1250 515756232 515756237
    0xc050a052703100905070f080303160c0c0603050415020301032103020405030102180925260c0703030c030b0a03140a0828080402010c020d03091802070521040e0705040504060f06 78
    0x191981c0e140000d15401880c402e003030b07803600140006035818582c0480800c422800741051107184288de620040d10641640001c00400c1c1d0764800e00040c0000b400c00704610140c118811403031075041d5102e110940b07034214420752035800840b0081801510030b0b01520000c00c000380080d901d8400390b01400c3ca8004410f01c8181c0134101020004440c4031003124080c414131401146200480c00c81c0d041140c092040381d0142490b21384694407a0801346441c80842e00c2445403e8610380c40707c4071031600500303940d07030146030004042c00c00b40d0801b401e07a1243c00a0044961007507038440302a6180c0c82240c10450028409807460710045801075014400101040b54030700340c42c091004140c0416010f4410110943c0d0103400034040000301c500506141c0904000749003c0d0400c20700c156a03502021808920a96407031030041d8010800004110302000700013180c404403007080c0c00000d074461005c80710740030354440d0f100e5101710743c0d0108210500480c1210082c21018005100840d11120510603c005501c0f48800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 515758732 1250 515757482 515757493
    0xa15020c0f180c0f220503010e0c010e01051606050a05010f0f060f2105010618090501031e03050c03031003121d06030613050a0f0c050a052703100905 66
    0x1400d1806214580b050030701c8219090507074841103098001c941099451440d050710401c4801d00031103c02d9000c40c00e041c2c0240c031172200b40d81070070b00b41400d503409c40045004030303801082030782d0b096a04a8070031880d1120038030340380743ca401120b800302010040c43e80c4040d01162a11050000202c103d8100d81c0c10798010503044011285e458420801141c030610419002038610269003060901c1585401000f0340c0c90780303240c209822540300d1001101c10130b0740712402184601245c050300103200810751004280070907080080758515156034100740610043e00078503820110a21041502900c15602500c00c0c100c11a40c5030319012080c60703052015808150707030f481c1c11b900e4150b450b64812480c0612444592460440d280e807200c09200d082e42015040c0b46d4003000030001c0c0444c21040b4447c1c03902c0b60141c08804504200c82c09004400c031860001d40504019041182c8410075410070111032082c4000041d080c03688400220a02a41c1c06101060354540900741c040517144003150080781a0600031000e40e103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 515759982 1250 515758732 515758759
    0x2070206070b040b0c0708180a0905070c0b0105031204090509070e16141614010209030102070c031101020321060102070f060f020c01020309010c06020c0a02061c060909020901050904020a15020c 85
    0x16224003440400605511f01008140507030742e4486c1d13a9852806024003a1281140c80d044200d00355007088034040005150345210100344641c0c60003080c01000141d010b002c03140060680c041c030742d10440c020030841b15120000f190444408010880c014030952495440030300b0300c2c00041920340c003444621400a02c9a006040380c80e4429000c451148100f00e040094044803544c072904200700f060b41000d4155820300003500551800e000804600303101b509403009160451400c840080146092030303045600610100800d2600103e80c8141002080c046810039614003004078a0000ba540112591520600d0005211504000c40325020244ca40a940b00c800c00c0780012030f0f685c011901c1c080d00180840000c20041012035000b080004c45200558944085940104200380d0022001e0409103612400f1000d100039107104100240c8090340080c0300103403894000582400c03043c02498440c032903403404030341159111006440100403031500002a03c0f0103900207500c44003114080d900520f44c0380c9554 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 515761232 1250 515759982 515760001
    0x3060a2403051f030212010e01020d290d1707050a2003010b032a0301020304030906080901051e130b0c1908090d03020a020a170d061205060402090a02070206070b040b 73
    0x41c105506000c100f0f0250354615000c00c542d4114200c140c1c00b16540e181450f501c9424280000c100d4072009070400f00c1d00580b145014104582000a420046a81c426410500783d035030103003421950b5005a0f80c080c654802405c40d40c03403403240c1d80b401443c0340f0030590044104502c920394003444070b0040d0320710020405038905041c04d0701c412900403036054200500e00f4445071f0140752009941c102007040d080392440c1e1000401e0890b80243c6e4164040b46010301c0801045030300c250f90b1503000c03070352800911a6044c076607040b41c110891210b2803204140d14100003242a0701111034074000940010b0005000d041c0030300f500c01d00785e0018900c00380c3c85100210b020001806440301500540b160380041082c505045803c80003504001071001c1103000c3c600c41900440e0030034020070152070002c0d9080707650309041c02042c07040701c100e42c2c0803d03400903107c1c04c5500400c0000c12519801901500c2c00d0450b541c0304c5429400920580070300940c07001001c00c1c410140315500300703039910803845aa008401a02e03248040d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 515762482 1250 515761232 515761261
    0x50f0c0601050a091404120908070b130b16030518030d082706060f0414071e030c020c01080c2119091e020604030c170705010509060f03060a240305 65
    0x30710125502902080001300c54007031f084414651854807600b101c2d152503260341401002c2d409008050404200800203055010621004260701c202d45407814049101c0d0407035142c0c2c2c0d2503015040c0507010840052014201191501c000700c000e050b00d40d0241d92050107041581c0075130391440000c60b134141407020010104148640200d40c01c006144aa81d108100300402240c9203643d41c03c0303511850141415040403d40c2c500581c041c0d141da01c10200c0000b072103ea003203480c0708074004060400003602d004da500881d000601a0080c6844201941d6103032040c65907101d20204080700c038107140700c0001c0e2980a0b03c030f86d03801401d01420400d000c807820142c510036902030183c003410702ca40d074140c6601100c42c48510b20000c00d03c042c10050a00e0b581e5182e80c0c2200c0c04943c454040804044480008050140034480140c0803d0814900301008440810b103a8022402d5280d0b030410000003103011540c030007d090b00284801926415000040b075005000081e5580088000c2030030710740810081400d08a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 515763732 1250 515762482 515762501
    0x6020c160611070e360d02060c040b031e180601051005160f0f1103010c0f0f030b01020f0a0f02031605060a03020d0e010603051e061e07050f0c0601050a09 68
    0x101041e60406221126407580584004050715181d415803012681c4a0413228248040003000050342c81c130506417505181c1b14010117002c5421000800601950580035901507441152140303841b40d444000703054201d0200314261543d00280e50800440c9081420405108429603064520302d99030788051151070511002c071400450340a004600c00c41880103100070316a40500303030400c5401d843d52200018050580c5040e10f50f04004180741d4124202400f82034100b07101440e0801c3c05c02d01d60840101030095a014103c201502c1e003900d098660320070002850300c560b03850306458080d20645001400120411b004034041d005900c4440c005501102c103940440e0005080e0514160300c10500310000c0d4030105e8000a1150f84d40c00840325008244a1100603510600040c0000c2c101580a0010020000512011544604204940019000c060810312082c0440301c0e443e130786a429042d40c15005e02068140c0424011600d00500a00001c1c454100c0e01c3c10345032040141d4581d124a0165200040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 515764982 1250 515763732 515763767
    0x16050715050f0403022418150307080f270610050306041110090315060303110c060d23071e090e1303180801021c150611030706020c1606 60
    0xc810405400c122245100d4607a22500400f216802402601c5041c7c05c000003c5400110032520b00190341040c0140d44121840c0c941d84a04511780400e000780784004c0201000c04810070900420f1448000d0300e982c0d02d008070003080c1e1011030000032040a80d25442150402c0618031640b5000032035040c0424114011a0020100806c07c0700c6881801400c0c0310120068040004891000001c0352910721214800d00025802054403403030f606001745404208800c0b60819040b02c0500c06896503403104640d90a42c950b00d012800c40705040e00c840c3c0b21644842407100300d6002d1001c0207a000c5e4450807103201d04850340e07803031211600d401004803004c0c4442e004000090302c0385400b0030481055511074804403071080ca0407441c44114140074102c40c82d01e55012600980d00440d803070200038600645156400441d510421000700901c800011005842c40740306c040c0144201e0740e02e0704480070701c03c48481c0e9400400035940c55400380042a03441c260980c1c4005200c0081c000401c409204420340c00004500f05d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 515766232 1250 515764982 515764987
    0x3060912080423031b0d0207090506220e0d050d0c02191b050307090b0114070503070b1302180f06010c0c051504080f0a020a08011503060c02010216050715050f 70
    0xa0400c0344040f142042103903441c0c4400d001c003030441311403082c55100e00b00b100e0f0041c20415498020191903c603640c2c00105a950030901081400c1d10384840c401604444a82c903001c50301c0c2000a00c00040c6140c602c03d540d2801400083c0742d0b850307041001408078030700b007200c200592040c2100c00c0361a902058001000c0d4541c00030748030080b03001620307000c64002c0740c010340344100d0f96034800080c0307080782c6a40001141c1e62900508909581c1002e00030042c2c1d02c2d075001091405c112640c0d0980c9a22072004002d180361b188001044002c420360342d001e68a140e0103000401e003010100881c007032070f9008545072282d850000d8002074083d445500c0d4000c40c40d0703100000036079107410081005a81c400b80341d10701102c681c09000c00201d580c410801002070901ca4009450450068014404041f03481d0700402403da041c4808004411a003090000c100da8009000068144030420b0890191123501c224588481f00724840c007091000101c0c9220807220300c03501c120100c0c01d00380f1096482d40100700a00900ea10f05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 515767482 1250 515766232 515766263
    0x5100219020628030e010c0c08040504090f0b09060402040c2d1418011e020a0609081b0c030c010f080c0318030f1e0c1f02090a030609120804 62
    0x2c2c00241c20304100103403100d9880780d0840818901e4201070b08024001903210b440000341c150082c803440b42c806600b450668041680340d01d4043e01840340d88955130180303a544001209000308030381c0e0840340a61200d101200ba0811119460361000c003641d09030710036442d103010221840d0081c01d856484d0704038000c1d0b49894080e008840101041c280b0001f4042c0881c40ea100090140044020210f0345c56520103008511704000c0010b01d903050f000c5031a00400300c84000e01d8035449e00029802c00b46170344104045102c18a5107841d1446015503030303440c0703540502280c542841a00104070310310301035001c3c4d049800c00e4000000440e05241c10719925004030b2000008101c0300302a0f40003d5500881c86010b6600d030f903c0740e502161030b66000040c04191010040342c1c04010441d1450b901c51418100c06045040c43d9110550030307240c03822411610314050600491485904003601034820780c2d480248051045566400c16501401c2d021408031944c000701c401d10f14640f8010f49586000399007064144036210304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 515768732 1250 515767482 515767489
    0x905100c11040f0c0309060c0503100332010e01050a1a0f03010e1e10142806090f140f0112030923041a0618060c06010e010510021902 59
    0x240c42180303030041c0e164810000203080301c1c01920b2660455170b17400240f0100070f007001400c4566008500701000010001e0240841a0300307084015644c1000201100314510114241c11854100360394110410b801c00c80b10510006501100c0f0340b0b130120f07009000e150f980001d10002c0300c1203161541c500044e540101302c600c0c14002c0001c0c0502a001e00001200c0280c00481494180003c10201c0b800580ba00400e0340c4200030310041000d290850700a101c0729030381000300c0c2d59080000f8440a1116100307190a9204641e201090500c03c1e11114200704107a00e607020303000a071180310084e40340e2500702414882c4000200d5149032041c14406015a43e0343d091080b500041c1410001c02e4007041041d08011915031101c0d0400703c1980407200400750300c490310300140403e039064501c40c8000d040840b2141d442c103840307100417101d40340f007951903907850322041500146040c0500154002c1d144540000441d900000308840c1c3c0c10b8450455092085059205040380e640c4200340f400c3d655081d400e0b1500e030041c02e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 515769982 1250 515768732 515768753
    0x1515060c0809040501091b08040f0b060f1503090118020f061318020711100917240603010e0a0804050613050d0302061f0303320a0903030905100c 64
    0x38403400d071103850300c80d6500c00035059400c01e0704400f40303541d41c91400d2401901c120310032490180444c20030f41168541030300c650440d040c94982c05404940e0708800107005548a00400700b200200424258004001d8070000c1d00da6001210852565840c00d5207a02c0d400c0d00783c402041c0c0d03055004029004036900780e002c4c0002c1d130300310b454410614070081c5030214030848609400312400d280100010f88400c40c40c1454240341440d1081c2038001c0070291811038046600088400680d19202488455100070725800c92400d40300c441d01214000b15110107905102c2120021070003840c044000f0b20003840004d031110f403915401c000c010310352042044100042e00704000070700101d01c0c44022090a4980c0e03400481d00d01e11540782e003140180c00010803c40e44c0c54440c40380c0b017502840552049070035419594090003410042c042e0511030311038510465548044a031080c2c10040712410169150220000f010300010501d00089011070003040b800305190508056403034084030f580d0307920030301c0107000d881e00c00030f00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 515771232 1250 515769982 515770007
    0x709060903150e0f0703050d090605120402010f0e040c0305091e10050403050d18032a080c1c111c0801060c060b03031606050603030f0f0c0a02090c07151506 69
    0x180581503002504940602c1174400441c0504040c258101c5c0c8c400303008259000d41d8201d00240503051069090004582060f540d000354282001042e2200411040d1200320a04411aa02c28182800b11240d10340c9500b10f540a800f10100700d598089000360207203540c0c0f0500c074400d131840d4131212007140c510f840b41c2c0100350424000c2c10480d02c1c11880110306807e44040c0b01c4c403448010140c101c032404040d4401940c1840042c022040c1d4008041031440f13400d90b03400c60f680074150744801700b01130745c140340305000d0080e00c50302000460340c0d0a149a04040c1c03801101010322550350017060400b1124400103d00c0d0038440705c0c3c594030148281e082010983d90285840d2003520a999600c1d003c00d03c54030104000c0070066035034000104071014a24203542601d000908050003504148000a85e03080c900041c2c90001c428140c909460b09010742c03502e4580740c00c988005c0c0d03101c46403000b4010340c00541c50081840c50f02401740d0340c48001080c4209800e50b0001581d080412601032801c1103003078881d52404455 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 515772482 1250 515771232 515771261
    0x9010e03220f0303030608060a062114030301080c1806030a030f0216081609060b040b0c0f030d1b030b0d020910050306251716090914070906090315 65
    0xa80c540c200c82d4000c00c1c0941048000c41c0c0e50380d200384503248080110036070100414801741b044078108007000b40400000820441d0322a4002840c1013084680307403180105040680c116900e969403150440d0b5115403000c580c9005d00c9001e4940b44c40d5044030b4600b140304105c058020300405c06203503000c543d0070007100c0c94a411030182012030f10500c3e032071010103c010041c100040c04c035214203074808074001040382e120021141c50100104041c510f804180c1d0100c1c1c1903049000e450f100a0410b481c1000c0c11032000514078000000e583d450780801d41e211407040c00d10000441c11003103d60109408a80f824480d41e41d01403110001a0010316150f40003c0d0302c0a805c00d0414107183c0d0b50000b00b8500b1405907003410004609031410282206029401c45401c0071920301081048000844202c643c040542210110361000030307595078030750250010704000d1414000401c000401462035241d4a101591b080d000141d05d81800030300c02c0e10600d1004162078116045c6100c9100300b1100400030318000050524 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 515773732 1250 515772482 515772547
    0xc050a0e150d030311120702060a06081506011403040f110a031a04052d0105160c0615050d06021c0c02030f03040c030506010602030a0305070903080d0506042702010809010e03 77
    0x56540c204002c3e1086c812081d0692090b4101950081c4c2403400040c1100b0501d440c0c4502080403110020380d80c061307103071610005841c688407680100c94220715610b408566501c00401c2c0b00c100130312480700b5004e60b4000c1788030f490118011010800c0407009440041d04004020142216400899100c00c1e08280705108407880e1203903440c0d0030314844010741c03010340d034130721201502c820024000e0260385e81c4007030b01c550030310390090441030050130380070070801d000e00903c0d07698240800c6210b0107036201c006014028801420400d45140070320296121262502100e00d5142184203910710314015200d4444254002c0c50808120107404600c0b50001401518034205881000000c25400d115144c040c142c0e95001d150398544200b005419101c0291003041040515141003010802c01e00666415880c1c808002c1303441c3d00c4050010b000381c484504140c90128a11800e500b071035402030300c240c1c3c4540c400e88403900705607940e00c0c2040c01c80f41c1070001c01101e03030000c01c51607042e500d00c0f085010060604110810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 515774982 1250 515773732 515773751
    0xf0313080d0e01052109251d0c0409110301050f01081b0706090804090203070f020d0206070c14010f0f0f090b04080901050706052410020a080c190c050a0e150d0303 72
    0x1404401761103d0002c1d0304200c01064541f2418101c50036441003c074002110a0303e442815061508000903080700e801030303440418a0400c031441218010401c0950038000032301e0400e80450300340d00a1085600c42c080840c000c0b0041d5000d8a440351040031990341280241c81d010305040c2440c1c3c0130040c1141d80c90303590b10500e40010f040b070b030190001d0310700300c480162649442d8a02030301d0300c00d009801d041950310007581440c1160340013880b160300040d54074081e040400d01b40760410042d50425000040d035420510300e10000c505075032004401c01c094140501040c404481d0740c0d011150350703a6019141441c0300d80042c0100d20014001e10a201c010f144c114035018480d1140c108540064400e41c42100c1c95000403200000c0c050a40c41004c1d90880b00e610481144200c069601c1c0401c55005002800200c0d40c00407403c42884081004c94a00c401680c00540c1494060038071201d40c01500e04c540c00d990b5000c61400303111b002051246040f01c00301d10780c0300350007030800c01200e10100044003007603107a00008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 515776232 1250 515774982 515775037
    0x3150a05060d02130f0e0a12050a03020714160614090607030207080d05130b0301081b0109050d0b0f0c03040203070b0d060302040e0607020601050f0a09090c080f0313080d0e0105 78
    0x8426890110b00b0005c1c4806010082c0019910300ca00e4841440c1e0081c02c000001c02c01245181c0d4403c02e0b00d04000d0780c0c813000d541c01500a4007665001406600c40c842c3c4080d401d5901142501030166044000d210b41500c0758000d6540300001c04941c0c030404001d0103c0096403d050000749165402801224102943c7e10f01c0300d458550004003c0000840201e110080306904108a601400d84001150708641c10040601e903909034603020158080c4039915800241d900134940c0c0c0025101c0604003803940f04080c2040320b440351081e503480402c046083c0000345118516416240903a0340200130705001c925100c0c0d6881b1340d4100c4083ca08013a50384070000001a5a14481c80a448070984041c00e142d01c3c20602c0a03080040590201c0e003e41415080300c03140c0d60b184845002621821800042c010905007009642c7c1c144070740007146035100300c4000349260b800c000043c04060144003005800036072a11100b640f6900701440c5c1d030010664458900c0d220750f000d40040e200c2e461040c0c160b1815014003030fa11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 515777482 1250 515776232 515776249
    0x15030b090102040b1308190809190f0b21060a0b070302010f05041a09060f13051f06030c0f03120f0e220c080c03040b1e01090b090603150a05060d02 65
    0x1d07151103907404000c0140384020b00104401c901c07087c2c00c484800c40151103009883c4520818a07210704103002ca078028507511244a40d011301080b020301200e540e02c038542c80c07076298040e0401164007401000151903005103180042c0c0700703280240548089629200306072600350808002101075540795041c00307512280c1845014461409040512402112190250350341280540600c646070040b901308095120b00702ca41640180410113a580300140034240982400f000c01110304561601c5140c400031609640c01402c00c2d2405048103503120f80d130741e584171040c103451484020711f071044903d83e60400c58000d0840300807050b69802c011440d00070683c0051618002d43d02500500701c209181c1042c202d942c8c2c4101d8220f5142820108164145084002c1140c04000c0006180603134140000c6c41e0f030003100707007903545403410343d11074030907550f11850f500006e48580e101081c0204031042c000780702442c0c001010f10401c008084034005588600c40da00b03014080082803a900000c00780c2c030f410010f031201d084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 515778732 1250 515777482 515777497
    0x15120702060a060602010203090715020f030711090105030706140a09080a0b070905120a110a0e09060a051b190509060703080609011d15010306030c03060e0d020115030b090102040b 79
    0x40c081914104100c2c104403011608900300316841442048801440010b201e0300f65108407c40c0e5400020501c002c03490300b5009241c49030240400714172071040122002c18114400c00842c2e40791040d0b03888105140d034560b0984107420000303440340e110b80c460003d050000c1c904d0320914070748a00302549a503240c41c540562075000720f40d01c28085042100081e03104807020081d2004442d21403481500321b10300d90f0350750720b40c48014000301e0601440c00455541c1c0e422910040000d074000403000c3c0b030240c4843ea19800b003220711345101800d1100280c05042d1200708841e090b451281800e00b81445544c0000349001420b80090500c24100848001640d500001c0c080c9588a82c3c1e0348042c510300941440001103042c0d2041c0d00103076601ca14501003040100a0552002482c808004000d0305000120090150341d41301411043d44c41c1000302c00c0c0450f54100c002a244130204960111020210072400c882c202000c0704458500c3c51000d01c00500162032060300040244005401c3c191640d8210140741d21901 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 515779982 1250 515778732 515778737
    0x901060e22052e14151201020d0c0504080d0905130203070c0516061d0604030b09010204030f0c1d0105031e0c130b01140c060c0306210c1e0f151207 65
    0x1006000303d104240200510364400e03410910140c1000d44440c40110608030b0f24620982d10340c2e0202c0300102096055590041c40700c14180400c507620400a1b04503445401981181d00960b140300c0303003250040f5800403c40e01e01414100c40700401c0b0008000a41019102c40f040000151182011800c10003c501c030070020300c90380600152510401034208502e8082011860780f86c160100c40d10f640e080e003550100c9400c054806c0966481203e56402032003507070001041c0c002100c041400f807010110040707003900d8061011850441c2c0300040c03501503a50074851542d050b404006680f04890000d01c440d0000400903084070132402d01c0c203002504250681a2400703203103507140d0802060b5030744444a1001056010030261401d9040c0c5241c80d210b20004203002c110b4100003000c200c164503007481c146010100c1d002c40707013421901c0183d41c0e52201c3c000640035120303402209028032201040d418410030b08a000349070f86025002d03402030001c00741512490028481d01401829500c0c0e8604817000d10407845603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 515781232 1250 515779982 515780053
    0x31905090f0a0b0a0e0316030c15020307020a06051e160b0f130f1a04060b0a08031309110c19060f0212060d02060c0111030901060e2205 60
    0x80080c4807003400301c01c007224800c14020030100016035159003218a8060180303000c0041500200200345008a100300c844c03041365064400105014000880e0026500045044610440713440d00880c1d50b03002d840c102030340c44101000b007042044c0c060401043c080d00e40d100e03000d0b084000c83c00322110a801880c140c140141c2d0844100040002256100ea03011400d9000e13044181020580b498680200300e000a10080407607040b00144200e0300501c54210b4224000c008107442c03c0c3c81d041c40a08103824595002e0041c401c00403c0d80040030042e10000610440c4040810341b070256400050240a09600e10f076072030070482083c19142c00d01490682da83c00c660302c40f07070b503501c02c1c07504270112500301907d03140d00e074030504c001505076a200410941150085401c4601c0e03d00600011308181300e00c40c6058910740c0b8002881c81d1350080313940a1886100e10400030002c0d69a43d0074420b0b0300c1030007200c2c1c900384000303109840b04d00e52070f6640a040c1c10a004400f102c45100300304210ba48464003103082a145031450 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 515782482 1250 515781232 515781247
    0x22060815010503160b0d021c02090a050a05011403130f03050c160e04060e010b0a120201120203042103020909130605090a020918010f1109151c0e031905 67
    0x12030321150040000764010800341d03080c4c5481d040003000d5802034580620b00080c006c0d04288071a010744420405e04001c00102181c2d2042c441c000f035019280040c0540b02c00b050010b0b00b403404200b40030072501d06071101000e528141c0c0b50312220368070080048000c440a483d042010070714080380b000010b4880d813251641c48001d0303900303249001c2c02c1e11528003410020440510842c00c8060711150080e41c00403007c902800310403d80c40c09080ba0813070340c81d01300c992001c000407031980096555841c14003e8a510348040f090182c1801a0b100071500505a0515810010707080c0b01c505031041c5d0f41c05481e10f401410484485c0001d02080c070140c5d6084045901d40c1c00f25000d10031940b2234180c10a030908000d01e0103c01590114401c0003004186001c44a00300000084080003900b04c00400c0f208500d040159042d19150340046d6001400c0d8180070709803504206842001c1842282e0008642d003c01c02c0c1240301902c12000a00034840d0403116500040c400d8040e0203040010680311800c0d20746031079454418 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 515783732 1250 515782482 515782513
    0x3020102041802040305030a2f0105070f0201090c060c080708030a0606270e0601050c010e0d020c030d090e040f060c02071806060c060b1c050c04140411220608 70
    0x2c280e080076103181c0304003c2003000920000c01c640d046401c1c0d04200c1710400403100070081001c7c079502880030f0010f01a0241101710030652005204404a07100d110403198030480803400c031030100d94010000c40070051309006460265030312402991180402602c1c094282c3ea811a09410988151013259103035442400025040070100ca140c0c04e00320326504030ba000c0c1d20014684c40f400b5104003c025000c40f4003182e05a4868800c0382e2403101c845e40284400d40300b030401103036200c403151104401401110f0720394020b85004180d40c0380c1d0b03140366501da100160400c500d07800300c8600504129200c04151440700c0016020740204401d800c903d80181551030701d0143c182e1032900d8196001e0186034509002402041c1d08400d01000c070540003180000c0c40000e0402094150380008010780f03804507201c9041080041c00110344403803440a8030244146007000030760134440d01090f0750060003280320400604003818000303402c41c09080100c0c9200341981706900ca0b40d00f11015034000c144140c0050070038150580 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 515784982 1250 515783732 515783759
    0x1302061c1d0109021e130509390f0d06180b010311102120030103080406090e0c041202191d01080c0d02060d0209090106030e0c09150d0c0f030302010204 67
    0x204148200c0101544038030005844508a004502d04a9610400b00d0305080003044044984402c03100c27400800d0b4035401c4a05012a100f03400c020084903081142c141030308024003402408403000d0302d003500440d480c0d035488018040d0314204001018894080390301240717203885198002c50083c01d20034000c44902e03062000c04816103a032401404400782e444502da01e000f0b00201c582d48103820001a04e00f0011004401e40d8803450f803601601407000c00040140880b01008001319013103030700d802c03190075a20307507011121002c00c45010550800034030013004080800c00d0040d4100c1d200500721040c14041907403617600150300c0c1e000284074004040b100c0300900340724032103a4017405401b00107180400b0948006820700040080090142c0c4021468803240c07611f90f01030700d40c4a140280b1145480da12581d000b0010003109002402d284209481c0407950b01b441e00c2c4c0d40d801203000d4041910017121400038009002c2500302c040f03584621803200010078034144003060010310b200b94001741e41d540c602a4800d4602 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 515786232 1250 515784982 515785009
    0x30c03071106040309140a050306070302030601080a0c0801050f01031d07170105101e0b030f0402011d150310080a060902010816080615091012051302061c1d010902 72
    0x160300c9041800042900040c03000200c0d000022280f4200c181031007c1086500242c1c0103e402d44102021321001a070581c010318840c03202a40c800e00c003661862480b2065032003400140e00414009001885103007099101441018818140410111400e1075020306040e01c2e11114500d40c0c1082c01c00b0700c4003041c000c6000c100340c00c4141c0240301e107050641c1c0000044015124032040803100c422016800384200100c000140540c8040c0c07501e914080f0300c03104038103000712812030020380100b4100c140c09100e8101a60b044501800075100200c405021076010351000d00040c0100079508000203c1140422681c118140700d0f0201095550301840050480d50015000c1d0348243c580503c141d0645500c40e5051b68440002c6038084820112001c01c0241441550511074201c2e000070141d803129030304070300d2100b100240a0410802641c500d1007106659460080007980001e040280c40c0b00452041a407503143c3c2c2d0506d50008902c000c94860030250220341b0300400041e51228000c3c0c040d03141c401c06440e6038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 515787482 1250 515786232 515786267
    0x3110702060f0a21060f0b0c0d0e011b030207090e060105010f0e1804050c0a06030b060921060f1006020606010e09070c05100e01180f0b0a0b06030c0307 67
    0x1002100d50000d6101d018201c200c031800c01001c61910302ca1132082c8041640208502c071002481d140c582d24060251860380285890b60030340340c90010b4207000f464215030808143ca80640038840f81c006040340c41c4021300c61050304005c0a410b80004905c0100341400300359203c0c0c0c0040010301d15020f5410240c41e000240b4503900e401003030040260b66040100001d0000b110b00d01003c00c8282100090300341c0c1c2001d254404120000403c010401400207040034500310100c50300e25241d9a1820110103845889101540128040c803000540b030800b80390b20f0b00d50a9030340408425440311000c2035031810384100c501c212442601000d10002000b01e40000016241c01c1c40508024504540040d01c8540c00c2201540038850300c03c00603910300d125051003010f02e5440000d84000840c03503012030000d01284904203001d54a096601700e105c032503246d8040055035000301023214641c0c02d500d590381c1c0d00000400c203c0d1807545507580b0030300701c0d80d4000007140b00d07680b4140741c25100e003000c5200034070446507044948203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 515788732 1250 515787482 515787487
    0x1020a080c09091603020f0a0504170109051e150a0b0a090608190f02091602010b040e060c0a0203120103120311070c0519051e04051614090f060a0905010311 69
    0x10303910740f01c5502c2e41c000d032642c01000c40040702d41c5040f0000c2c442c0700383c0f091642001007601028103611100510403207248103100480c2c49a0215000d080300d400309001003169100080701040d01c00710020300b85050900c0c100383d910121400902b415809411105c581009540310343d1030605140c000c01c3d54018041140303080040d80e0400021642e142180c1e105903003c2c0c000001d07420100f004113060022019800741032880c00e1306003207102013010411942803034095428003406407001e00f014031a0340d1803140b083d00101031645aa010700b60a55000380c00c96021800104404860020308105150003503200d030307468040600c54008001c048034910300c1c140703510300c50412000001c03030000c4800d9010b98204542038032074548003888941d42c045481d071040d608252003500e814002c64003281c1010900c0c2060b2000e01c031030f6445079040e0348c0c0a03000811a101182d006060000b0f0410a01d0181141005c0504260502c030010800101c82e80c1240b030000c2d0002c7c1140c2d50a00603942d05000e43c854803500e41c4122030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 515789982 1250 515788732 515788747
    0xb0403030f0c06020c0f0106170a030503011e08061302100305072721260f130e1915140904060213080303011401140406030b0d02090901020a080c 64
    0x201034a14054500d400c000b8804241c2d428410164100c03500c180c00c11003106e0f078843c40582010301910701445056100d070102d84240c60818400718507888920b906549440c95682044407440c0359030201e01718104a408a80300101d2039103410071031580074564420080340c02c41d0191040000842c40061304030101410181401400c0390048803145840c0c0000225134060000c2c000e07401210700e8164011094040071042101307410047d031000c80707110b87c0201400681d21801141004245550f4100c0c42d0284004100f20000c44050201620f00c3e800c0742c42c0451409540c50404200c20481582c550300d00401c00021840e80d18400d10501402c51043c1c040c42401500d0300400a802103080301a0b82e01560070540010304019a6604540c031889003c2d80c04500a03840742205680c942090040300424800b4020001c0158002c2d1541040118507685a0707103000d05080086015048070003000350406c01c400c0ea180c00690b1075108481c070601306d440c0016150084802c0003061100c000d4402003440d10200049c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 515791232 1250 515789982 515789987
    0x7020312060111012004081c05090d050c0d0602030901180503030615160f0510021321020d080a020d0c02090a020a051606060f061106070e12060414070b040303 70
    0x1194070403003d00702070070403054084880e405081070000c604440a1010480c240c202d48490180c030989a00800b110444a001c041c10003a0107181446400072030024003050985250180c001281148034030240c0d111031035901c0103d000e04d503080360200ea406070080108208003030248501e200341e8000044841980700b0701e40fa501e84071321024003600d0041030b1240701c5042c01c102a43c21242242d02944551002407054101085032604044e01101c0d0390140c0e60584031041101d00a031030021003c951000199440c0c00c4a00d40c01060350160b000700400002d1040c0056982c002000c000c890145440c50394441803204024109500034000100f4852070309004800358032951510399001c0e00c80040140c0e503ca2043c000e0318903005030f4035480901a1501000010803040d5000346d4100c2e00c6900c4502d280030780f2007005480a00041071161201d03802000064492403282c07010440e100c002414000340b0180f0203002c1c60602508036419965071521a42078119000e0030490900241201c119941c100750031039400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 515792482 1250 515791232 515791267
    0x61e050a090b010302040f02090901080604122c0d06050a06080118080306060915040906060e09090d0c02010302130305060114060f19120617100b030309090a140717070203 75
    0x1a001b80d644070a0b641c04c1001d02d504450000e807000340603000541c1d58600d80c41e034500c1d0440b030854043e001c0c00d0f60041440c5c0298254204407800c40901d203002403200071404410100340207690f900000000300c1c1d074080745061144034003594a40c480444c83d41d0400794000c0c2510024503410840701c4000d0061004101000c05594110300200c0c0c200e0741d10965403000840001794485885030a80c00007500240c020b0b0164002ca0444406484160083c003041042001100c012a040c0d1803540041202086e490320849100d4162403050400505080c5547c1c103d64610b0f6140e00216010f502000041c4140300054205120184041715407510b81000000e0030015406802d00c0480b490399100c4141884034080c0340c0d415071148079048100440c2d99240720040d129880f004504415006046002190a9290107041c0b81c48034064019480e21a0701c000b03110040385c004041010701c0355510714005004405104c25070280c440d66492140150310a21000d0301c8c07110140240702035510030490740741480b03904c100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 515793732 1250 515792482 515792489
    0xf090a051203042105060c0d18080304020111100e0709060902090f090403170708070e0f010819060302060d021c02040305071802070c030c080c030106031a090a061e050a090b01 77
    0x2c0e50b1941840004d4103060f0701d908060300038502c0c0500001c01c888104500090021604011030a03c80c80103040b500c0002c01d0410940500402c2d410400240554091090000c10f481d0300300c211440002d1007a8050b080b601b00000b1280140c210072020010101c190081c2405400c220000314034101c40030001444011101448501640c080000602414003036050820408210088645d0500c1c11140082000b6800c0b1080c0c0c021605a000c038040394202000090742c10316040c2c48015041c0c40c1e04840030840e00301e42420405060300d6080c00300050312501c000d0003a80300d00c08801740c0c0b91401540007030810b424000d2280d0340584103000400c040781d030003d00c103c1121007505082c8000140361031004080c1c400c0d403402401c1c00000e50300020406c607846a0f200100c5007954241c0300404d1049d4200b5007aa1500d01c4080c1c40050f00d000c203081c01d03581d19214542c03c10318010403110480e6050351080e05403400c1d032000c400743d002c0615000c80b020400c2e00601d03900c00b10a100400017000c0595a00600c10010302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 515794982 1250 515793732 515793749
    0x112060905071208120f070e0609030f0a05070317070305071b1e0611150402042703030c0206070306030519150f05090f03120103030e0112020f090a05120304 69
    0x8018001c0c24410207000d4041c00030982205940c0c0e0900d86401c0d032100c0710302160801c0030340005841d10401883c00e4010ba007a651080c9034400c140041090750303045884079541c14041e0f960f007104025400c0040c0541d541c483e2002c0c0a1031881e41c201454800c09814051032180b42c00c000d03040002e6404800c6030850790780300d1300a10004000810f10005281541c015004041040b81c0000d2030b001800f860004030758159640d00903e40ca070203121506d80308400c00705152034a0450105005281903040b643c0a652a052401c040c0003115030701d0b40b00c1418000c3c0503004242c3c3c40640000940d414031000d64001c003d070609002007442d5a4603a5a134502c1c074030000c0c851044220101d0200801a0310600c96040c2848060000702c404c1c0d55440000c007002c0d6104141445040c21100722400c0c00b000b038444c078920220351800540e01e9510107403900c0000510b030314100100a00480300c8107900d4400b40c9041c04003540c10503101d46480c0309015210041d40c01c00da01c103510703543c2010302010000084805540904 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 515796232 1250 515794982 515794991
    0x232a0d03050307090509010801021305030c15070206070204150807052e020f100204140a03080a0f020a02030106031208281a030d230f07060b010210110307090e011206 73
    0x400c02161444d206412031944071449900009884e50150081d2000c0481c461401400c1540c50301010b94448094000b10b40180002400c00c447d50016405840c0d003030300140526282c49000c1c1d001038200d07603501141c0c09003070204003400c1c44851001c205040c0500170030b985a002084a00081c1448104904101c080f181d1140e0000010030303200b840603040c580c95403412611410f01007100a4007030340140c0128a42c5907822040d00c2e406280407065481281d810289061801d04405003c40d00038210a074600c095116980200005031000d01ca00401940a4580d0600180300420004d08225005d0301c6900c01c02d00c454010a02c00c0d01c0c81c23050320042c8180000024421042e40c0346101041000c2d06199030501620604510041d0000388002aa41c031000f00c14821401c8104007624038052a0320440303480c0000d002c51800900e6a0f17005d411105014011261000740c2c5070100016103405218116504c800071003800203e41d0418000c1d000f400e040654001d9035030400310404054020b940010b042c09444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 515797482 1250 515796232 515796241
    0x7030b0402040b282306040905040f0c08100507080f06040b030a08130f0b070c0506390610030f0b0703110f0315090c0d09232a0d030503 60
    0x4001400c203000b400c8080e800c10500d40c0713103401864180580f06194103d10700e800e80c5207240e000036200001030a401000c640c1040c0c203240e1312400601c001441110f2042100c240701300443c0c009280e9000a007000401010001030240262066400280240040c0321500c024041400c07900704d9400d5105906407030000d04e030301e003080c00a403515089a8015004190000b0303402c2d00000e407440d1402c20b07689100100240960344004449041c461804003030510350040c4420321203440c114005142c480d08240061840058402000c1d414a00c1c10780303c3e00c111060100640d101801c248211030340014580c460680191441c4c59041d0003d01808008003031025090018500d03d0280d0f00412210f00c3c16100c0c180c842101c904100d113660f03c00d8801e000d4004004801010519280ea1801e224103101480c4030f0400b0401c4000001034044058112036405803414000008216401d104c400c007100c500042c85158000087c00750306405952007202c03a00389200031603605131240c0800044c0240c0c1490541d80c0d9554 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 515798732 1250 515797482 515797489
    0x11a1005090d020a090c0e10141b0106090c030203060411180f0303190818030304150903111222150c1a040b06030615010f1809051806070207030b0402040b 68
    0x4e040d00100da03c4e40c500114420b60540c8920080c4c0d16201c190f4024401c5c8403000d2080d58603540e8107040380f05030030042010042c03101c400c0c0e0300f58841101d00c03000482c0b040e8030780b03103020b0590300d0b10741400000076070110400c01d2904c0d01c2d024144200704c8a814840c03604264030940e40302c1000d0340f000350f0301418884500c0c5401d510100203c0d00007101702c5101c1c1405200960700184184816074450b8140307212049010807035003002c01180e0203182d00c0100a000c058140c40310300c1c060000e02105506112450080360303d60201800007074400300840d1040c90b964002c0d400b4800c40c85185820224104c00d03c1c0314240004000500034002441103405c02c11f06070080e526000f0b0030440d03a0342c1e4100c6040c50300c0c800d03c007c0080d0b0703200e100c4c05070794114140c504554481521410106640040c01d0024668002050000d4001d901d0300c080500400141c146864881585038299003080e544d08042080100524100480600c80160015a20700c090491140f454680100114010b0406481280e03503150403961a81c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 515799982 1250 515798732 515798749
    0xd14041208041706090318010c1403090a0f080a021c080d06060f020c011e051209060403030e160b0f071e060606032705070b0705011a1005090d02 64
    0xc48441640c0c0601a1498880c006400510420034101c8000e186480d0400300400ea01d841115003100660500f03040c022250003207002402040e043c44040b14208011442504007002908910801190368650003010721920041c1c2d9409100c0c402001c500030710a00c1000715a40c11541c0d0102d40780480108203140000d120391415500800744200042c001c420130310f442c3c0210045a20940701c409840b29000340c2642c40c2d6210a20311400a05418119280900da0300c10482c01c8103c02d240103410003d00e44420210700300107071754064240d0300000c100030416a2501445050840010143c42900c40a8180b104010701c103018002c2c0c2044086002c0307007061a00c40c262601c0b1a000300704015611499440d500704804680010740300c01381402c1c404603101d4000e000e4000001c0f8529044020350705c4030084ca56a040400c401190385008001c400118a102a005015081e02510000407d04020500100c044090418050103110341d010407140f007580040588407214410360b405000403c05200103000d06 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 515801232 1250 515799982 515799989
    0x1501200118031805010e090a1e02070506160c08120405030f030c070605011a070311010207050706020d090906050109060c030c050706050c070e0405031c06050306010e071b050d1404 79
    0x1c0c480603003200926903c983c4440c4002540c240210040352200011503140b640a0102130700044201e012440031085a480f410b0040e20a121122805d03082c02c1c58001664030003042a10342c2c0d031205003449052550010440d400070301c281050119001da55840064600825403005580114000010180b100074801c03501868080340d00695030386010168090a80c0061205480c95850000040791505601003800b1304002560800c070300f02981c07603070b0484211403820200d000300e5401b84010030018038100050b0000d01000e4002d00346401c2140001480080c595010b8940306003003074000c10a81c0d8101200e001070b2241441c01100e0b000b10b50400340c03200204504020720074070880900240071039000026181d04120401510b64050b503e10f881c4000030419600642030b40c104120084c1d6401c002070040040d03c0414401141065891700041e0804000b60702c01c0352949080fa00f0807240d01e5100080d09450a100c0d03201100013130305a1a03466581c80390441441c2130200e503c0b40c8101d14411001910f005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 515802482 1250 515801232 515801261
    0x61f050712030f0b0103150506090d020603010905040302100612080c030c10020d060e1005041d01020c0607090510140307091e050102070b0406080402041a1c02010815012001 76
    0x7040d03203424004009000303d0b2080e0603102d140c0441113110350b220b4002c0c03042c0e5030594404c0100003400d1504102035544030543c40c81d4032175038800c0704800589814001c2c5000701040715000480d4500b07800c0190400d070940700180410b500e400c2e014818400e000500e0000c07190054101f903103404c6480e0f1045e1842c42440749000c41e43c40b681c588403000741f40b40d80007020310001e402000c0c0002a511110300c900f0300c17000c0e54910b0005103c200309001509103544444d42202c800c00d031341c0c1071154094140e203089a00107403003d05d243c0c00020400510b184c11145540040000792440c8201080c00107008210503000d40c0d0741034031002c2c000702103241b907885082880c0c0030307011038003d01000540205041c03820003024802c10340076029964000444072011810b079400c0707450940340c4031740554569003080000d00d1070007051210b0000c03020354a00240c942c4440310f002094801103c0001d105075000140a0b84001001d2642d000d203052041e20382c0e030340d204c0b800740900028250840f01ca000140c02c403a0261400e40300c1e5008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 515803732 1250 515802482 515802503
    0x2060d05040f0507170c040507030b060310140d1104151d0a0615080c0702010215010608041401020306030c0d060e0f0d1205060a030b1f0f0305070e061f0507 69
    0xd02100d000406107262103035080310500c91782c0d0016a4002c010900142c10590072048003203a260425402c142d60100d040d14001440b00c04250009070f1581054580d11020700c00b00e8028400c4031506c01e415100140d04807030080715080943e40d1a45005118210a07005a80300ca4102070050001c070344840140440c195070300400700d08100c24448021044401014850400da000609442c0100300980d621200784d0718030300c5c15600d03449254a03650040030202c1c1180314414091071402c2103044524040d04483d9145486030601d401c1045088240207800e0006920410a004030303540c0010718482c602c0d0b401d44064020b1005402e1110061000c030704060390900030401045046980841d0b10280c01d001a115403a44c07441d1241107800f164400c45100ba00940000c505102180301403c0566005041410b00c3e1704002e100c149002b00202e07580c0c00501c85001e0240140304000c4140040c4001d00744200c18a0035071f01c0c00c0d0b8005908110a1045c4140885003840d80c0d10300035100d07408580c0440d802c60341184 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 515804982 1250 515803732 515803741
    0xc02030106060314180a0f0c0306020a051c060806071101110d02070219030f0807110a030c080c1912080c0d021e0f0d0503070c060e010507140c03040e0402060d05 71
    0x70080c0400061001001e070130f140001c0c0d50505043c0380608460f4490700104480c0842e42e40301d05140f020200b0603181440c000740000700240041c00104000101a51015214089041200d82d0543c00805131244d050a01000380301c00c180000d880f0717522900c0c40c503003400c803640c14403d054010404141650394200c1d00041d4800d218549400030000c80f4420364202002103411240b40b0341c103008501005000300200c40100c0c000c14103040180c103009000c0c400b900360540ca000009450b00e0ba00c9c1d441142c1c201c8a452f4100083e6400b40135807050390a0580e044459070003107000908501e840c034003410502c0c03541407020206016442c1c003551045d00c1e48a0441d0242d004410000c1c1d9035180c55400e0345580000083d0000450b04080703203201010385008005c20394112464010342e0590401031941003004060790440002ca54039000b0f0000c0c0001800c0001841d0030142401010503a04c488030056100c070410414203032040000c211021141c0914034a07100d500c0d40d1002031001d10512092031030302070a150a10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 515806232 1250 515804982 515804987
    0x90b0a05150319020906150406030c0e09040302060403020105010b09010207030f031e1701090209030307020f011110050915010501021504020d140610050f0f010c0c0512160b1204080a0c0203010606 86
    0x81102c0c000c8401043c5e42d0703076403070030404a40280307120380e80706c89002c1c4020850240070350410110a5003a0a10404086e1100041211550201c0301600181d100a0500c4140342c0c080c4600d9003d8090441c3d4546481c0981d00080d44e203280c0340c440100f030025559000d50a0501ca0400c828004152601000c44442c0749100181074800e110401c04401894000000d201c502e14405ca0b0904040031b40614280000c076020069800d01800185052120711440c4181c00b80003130151501600d425900081d0f5400c245040500c2e2503030031840a88081410001407150b40c0e000034042d842c0c81c0204900800a55840c804140040c0c03039201c004252860780081031100e17442c08a02184120516180105002c0d503a9003044042001d0114442e0801030101480307489520407108028001d0281001c4e004040d52207000c11a500001d20801c103250308104886190840c03080000401006004915410300001440386d41611501400c02003e01c800025003c00c1c0e240180800d4004a130014001c002850340c40501 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 515807482 1250 515806232 515806273
    0xa090c0f03111c09061e020705070e010803030105060a030e010219020c0114030a0207050a0b0a0b150a021209010c140609070b07050304030f02120a060b090a090b0a051503 75
    0xc0400e040c201c14a49200d0072000392058080c080b129155a0406550250010100c082c016101e85459038803145421081d5440581d203680c40030320042c0c1d11075080c01e00c3c03030401101d038120707605014107170004001074140002503d0548030101c60165980c121104107800410780c41e86880381c13a50000c200b1480d031215240101d02403a00780c0e000c2d140501c2032140111070050440c0102030400317070240081908051a9405403158078410300865441700400d444000c00b01c007040320385c51107058803001102c0700e41c1003107203038544025400c1c4103450610884140c00781d110703909024000032070140442e4140540c3e2280030004041c540150000a40c450844a41e0740c54500441d0b440f03885224044000503800f002c841102d0000307070010099030515045554040700d60700c40000c1640c0c81028080d600f50034030760501800850b0342c45014000348200102046c0400d43e0700040a00500750703c2c154070680401c81c4080c9032540021412000101c030769401588500c000303000482107415100d68100b19090302d1101c2c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 515808732 1250 515807482 515807507
    0x604090e0d03060611060a0e0a06050f041a010612051e0403020706110c0d023d020c0108090d0f120e153102040204380307090e060a090c 60
    0x1001d000f541c0d1902c00c10346001c5107050103807000d40e105c0d40005040d44100d500a45aa492140030b603130712442d1301d0b03c8a00c00c0e06c030f058554001d00020442440708000709201d9120020300b01c41040c01d0b10351314104000d030445004207c4050255180d02c00503041c01c40850241180d080600b6407a143c40c14a81402551181079024482c0451481541049400350006031610482001011440c10f03000d19801c1c01701d02c807845c001c0454a0245114696840d05682c10800f00024903604030310104030315928001d00d41241100e040303042c03100d4001400a40e142c01704030f0000c01f400500301142c100c0041c102c2280c51081040c507a401740c51401e000c840f038402010030310710a4001c0080c1e290030252101d0361025110480c0d40d0065241005000c2d607180b08003042201f9401441c0000e0006007000d584910b03030649998200c05101c0c1045107150020300400e401c24072040c0c000702c01c0c0405400d5140488000c1d001c25494050f21602c194140005110795803242d00c0f540c050841f05006001d14100641c0242203a10f1014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 515809982 1250 515808732 515808737
    0x10e0d230d0c030e07260c090103210e0a03083403030e160e09010e01110c0d030621060b0a080d02122a0c030105070e0a09050609010b03060604090e0d 66
    0x30598000e0000081401c1610080c8641c52650980c240318030a101b40b0703521a5410901407190090070940c0c071030a560340210300494210a41580d0b0300d10708580940c80040c1d550030b101d40080b41c681030b81c64144107402988c4d0310002070343c0c0d544002e660718002c00c0020315828014500c8240b840034003411071001c000402c0c0c82a1001d1001c90b01c28040a81c031188112032482c041d40e0a11800c100404050760034940060042000050740707847d110f0100d00396840300580c200d400d6170002d6140180c907401c0090f01214910b9240401600e414074001d00008241c041c20b040701c2c06642580e00e0140115540814819803000381500c005554454a00792690035080b6440098081c08071854078800310701c0300300e555514241880c180041d0405030702d08900e2020213980606071080580f00542d45d24248533440c0100000d403640008031007000104414001d16410030350040e403c0005000440d1140008a81502c400d052895120340d284800309403140180c3d4400311505080048050040c04c012403105103111295 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 515811232 1250 515809982 515809991
    0x40f06061107080703050a081b0a0501021e0313120e1305090c1e150408030c0f0105010f0501080402210a06020301061e02062806060504090c02010e0d230d0c03 70
    0x50320020b4031040136220140168200e52181f50008501e08014412502c5110003841c09140c600d4141d460400035007000c072aa41c1d40014050300f0b60924041c4400d195449250207851840d041c40a84a0074600440040c030100760b41000400c11030041c40024004080981801102a00308110601500701030303410802c00d0145c407204440c40d044c80c0f0301c6028203409016020452544403000d01c0311003412030402e101940814030000c600341100340700a29005030100300030300041c44429440790031654103070712010350031848002c1040980d8200c1e5203941d100e0317011a100d00141c13043c3c0211850a03c084110500c0900580b002e0b1010840580c2c082e40c103940b42c40d941d0b940c40700750190751007140f14018114000580d011400054892803074030100e414964080c01e07188184840c51503d2001e848454000384003194010a0500a15840c0d211302e1030251544d00c028001421020040c0d80c8600000400c0400c00400040400d101c4c43c1d5900620460803070002c2281d079812101c54448014000182d205000900740b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 515812482 1250 515811232 515811239
    0x1e030e1e0f0a030807080f1902010504020a080f120f1902060118110d0902041104090b0f0d03081602030c03031513050405071707080d0806031227040f06061107 70
    0x80c849000e407640421224905042c0307840e148004d0300103803041ea02c10030f010001001182c4140a9003808a004c89d0004280c07030901d0720401032458099000f10744a40c0c8803044d03c0100303c00008074480290504404181d5440b007100b800502d0b4480c0d00c514120041c00d804442404035400189903048407034945000c284074500b03104020544400e804180f1907494144102c18810b0703550b5000790345242c80240f000480f07101441d011107098005a2040c0d448a64680c03458410f81040c46030b2410707649040314131300c4a582c119138014000e1000070340100034006007c03030160321942c002c02c100e880e01949601103030b84070f01e042d40712246c10036000251f442c0106010001001848a41d00032580195030140140952904280241d060080d1130f03860b1000300c0c800d0000024030030740c060114503d001c0960b0b6031001c45250040a1504c2d140c4102401c010641c4204000886103241d0600d100350f00c1c05141e01d1032444409140050040c00d10f00500b0b1039170901e428070001d42c198020101941c981414019107075001e03907 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 515813732 1250 515812482 515812489
    0x215041203120209011e1b060507030f02030f01030f0203070f081006050102010b0a140a050d050a050f03180f06071e110301020a0c02091e090d020105010e041e030e1e0f 74
    0x4c807420140415490303c26402100c1082512850005507450015007094000c0040503100000d2101521165940c030b05222074241e140c01134a12a1325200340c290b00e107048c0071014800c154814480586450a11141081155005d2008100900007008455015030321202015121000440c0c0601c1b96861705c6000030b0994010f0060a250000c002d050b181700307500c0c04940d5518202c10b0b2141560102050310040303400d941c0d003802c050354180258020480010f0f24a0f001e490240111022181948184004810698200b1107100511003d8844143ca9180c0801040c250b00584400030002282c8101703000085985080d4404c1d1640924000c0b60030b101070009041c200c0c4106000c0c5400196848010750150030005036140c0c005c1c2d402542c0b41c0c03406c01034031805202440180c8542c074950f0407907011f96141640c24000c0e58050a04e000640c0c0590a26075a002805580d18500341c140e030800195003414580101c2403117004000c040c000c055512091084500c4c6400038000091040701d103440103a40c18203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 515814982 1250 515813732 515813737
    0x10203090303271f030f0b030f03040801050f04020a171507020d080105120312060d060e07090f1a041805010507050c011109010807140c1501030b1303080601030902150412031202 78
    0x114440d510030001d013600b09044010b490b4180344080c609803540000b031041d440400003000c0c102c0c044e001540d107903418a40c1e2030f400d482e0080d09100c0b06007050717414030025035100e0444ca000c40d45035940c0d4000081c041c140035401c051020703031902c900c07500d000e0400090300d80110b040f010030f505039a225146aa00c1d08200041c0c030050b042c500340c05501c00c0c00058080c0641924482d084980103040751560442c540e0740364140c9100800842c403a420002040006110a000c0e0b01c00f030f003000400910520404e22400180c9080043c1c51510950312421141003801807003205002490f00480240010314214401074066031103501044d250307602c1d02545ca0f117800084000c0e2001382505030350340804c544a10104a5096181d020039082c0c400f0100490803030306c0030411011144100c0d10000008540c03640c200414031020081c0341610402ca8913048800003907101c0c0c62290f00983c2401c0c0001c40c613080c5e001062084680318224020503c0007d0003046001c01402c0424803903109540c0c040346036400c0140715041c3d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 515816232 1250 515814982 515815009
    0x40b04050c011d0f13020c0f0609011a010302220803030105011101060812030601111005010302040c051c0509030904060905040b07020a15020a03180c060f0c0f020f01020309030327 79
    0x841030700d0708810945848404d80000103002003c11410003e40007001003264009070001d101c40d400203070f000e01c3c02031042c0320b0f560f0b102001d00004c00424480b481d241030318103500302005040560001e40300300c1414404d103203d070b5015083d4560480441d20b81400031b559910070701449020812b00d61111240e02814081d40b82544d249502800b900425101803090399000680751a050002c2d000302c103440e04008100081c602e40740303001d002c2101d503d9030061204950701c09617940c080040400201090110b150340e00380054495040000d9180c0e00c02201600b103000c0c0f688c0700307a4045d0914000080c4501c07640c11450245000e07182c4211075840b10b14080c0da44000041c8002d2a180c425806a00701e02c609502801014006060114580e0300c81c180d850350b403802c1c140d03044032020241c000900c8402d038030902c0c410b450300f09810320114400c00c90711076040c14554104000e109200400c0032090b81d034420b10903201070440140880c2d44646408039006044140080c501107100c082c11180310070b42c41c00202c200c424 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 515817482 1250 515816232 515816267
    0x12020702031b0103090b1f061e0807030219030207020a0b190e010203070c0b0a0906031116020f03030310090b030a080d1a100f030b03061e0717040b04050c01 69
    0x7002c005042c0d100385110180d03550b06050740c0b2004100454402c076100d03072007000f03130020420082c4a08100300042c0da085800030030130070814035a442d54594131445403000c203100b9810054196500c81404501a210300b0503000034808869052050700c80e0036402500310f6a100300da0424186440b8443c0c0c02e0580294103441d0319022584560903449801010000c074020010b20680e40303001c080e078581c540613414580c0700c4180b5200008a0380512580141c9500240080e49821720008840c1c41030304c80306000d81d00841c8021a03d043c0301c1c004543d5443c4520741c3c4210080c0613aa280d00c2c024070f100c038400e0580d1241c011f03154140300e00039450380340118186c01344642c03001d81705062410b0404c101000300a4100310380001c104105038600301c1d80d52007410140100c4a40e4500b4120300c20643e000703069440c0954802d02940c0880c06020300c0703580c2c000491901000d01010800d4984d610030080750b41200d0400d03c0c04200f4140828030060120f180b014a2066001704103d0300c41c40e4000004540301807602910f0f520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 515818732 1250 515817482 515817493
    0x20a030503131707022706060a050c07091b020105010e0708041109040b07030b0405010f0b0319020d29010917070503010509030c070b0304080d021c0207050705011202070203 76
    0x2401100510342010310141c100b107012040d540c1c1c090110748071102c01d0b0f06990300072030141d045140c035040000d502080d2090f81c080040c90039910004030740025100030b10449001c24003a03049845101a51a820320000c1150101941c0d610b01c00c0c0180401540201c03089541080c07900340038014002e0f80c0c12204c560307085000d81d80d940e0804507490f90014100300c405014034030050180742d40310201c00d80124062640c02c415401c1c01c2c00080e080313801c0c0108a81c0654100b0004101c041072560450003201c103100d1415640b0754440c4007403c403031450145114116403020501d506404103a5206401c00c100b03078800c030381c190001d00302d8100e140071700014142d002400ba10020f01c0a00c04100c0f2460300002284201c8420305d8880c0006800d40c2c40480f1841160f6002091044140c04100407500007411000903551440c02e0684030f21540e4072502d401c4c0d040050700080c182c2d41008040082240f0040000d900315220342c018902962645090700ca094001113010310401c200715924400c65148079801001000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 515819982 1250 515818732 515818753
    0xc0d0809010c031202031005040e0d02060105060f130305060901060f1401030c0527091b030406051005090112061b020309040e0312010e010305120f0d42090b0102 71
    0x42c2e00c0309401e0011400c018000e140107144901d10f00141d8003860480c50101c032501c0c2000140812501020b820004c0d960110300410f25680e008200c003410f541042c2c0c0c0e07480c2d0700c0b2089074008500303220f51580705540c044c6c020030001c18040d0100d905030007039080d080281f0605030340300c2003000d20310003600811410402c465001c0c03549602a520102e000481420040c0c205050500c092a040c543c0044031041804400c05003007a61401c4500d031070307011001d2a0607180104490807074001c0742c00002c4c4002d0038907640d0800b02d031072402801c0c4a807006280041c105401c0c0c0d0785034088002e100520840c1241c2003410210340034280740e514800184420781c164011810003280000301f0010309114200307520f41d80000c001c03040202a402c10158068125802c8918441d4590b15059241c0103601501c1c18044405000f18048900301c8411121541c0c00100b010500700e071001c4004007a0403103280d0098035150202c14020312541c8054041800c02d24414400411550305c482d0541521010806d450050300804441c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 515821232 1250 515819982 515819987
    0x703080a020717130e131502030103030804150b090c0a020d0c0506060d11060d02040f0603050103020607061109030f1b090c0d02160c03030905040c0c0b06010e01050f03011202030c0d080901 83
    0x910394074038264200c4c04c3d401d950b1031901111a1065503881c400c00041103da000784210252412941082c0001c02c628544c91914010700303404000d4001800351150003011400071086801801403000c0050251015090000f030220556100d20710800140c0a420050f0b0045402072620b010020340060141030f040d0794000405c505441c804004036018001240c5008403510b846000e0094107440500c01641c1d241480c405142c0c5c5070466002d00205801c000c014030060320f0340380503511072607407007071020901c1081744001d5440740c01000c11580c1c2501c40c1d0500041c0014002500c00382d0401d1400b4480000f81c80441403003d511742c200c0318803070703400420803110380912030700c0e8001c00c2e021040400b10194030a1540e1003515100780c41e4400e03000120501e2044c0304074900f40c407594602c00081c0c205080092010b50b41c100d803505000303110f1414098000c1400e4490f9000300121410000b03040c0c10a40d40c0d60b10740c00200344d00520000141d02a204556502e4000c0c20003a010400060300100c1c070034203050b58607004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 515822482 1250 515821232 515821237
    0x40905150601032c16080a0f0201050c1009021c17160b0702010e0105100302030c011d060f031501030203091b0612190c0207050a0b071b0b0703080a020717 68
    0x10a040607078400030700020110701a04181ca001c1d921320903140c1541ca414005280c000394009040c01c02e0b844140810940c1e1000442030045980006118039400307140c00141c0c0ea501907030985a40c940505400142d2030415a400780c1d190620880340050b0000060b10340d02a04c1c2c070001c40040132000c02d880c22007061480d00010b450700314106c80c441e8145102541c0c80c02c0707010100341c0e01000503039181c0302c129a0101080c05101d500100c10380d0400740b03040c50360f00000d560f0102840424184003d00c075180d035030798014a10100d10240041c02440e80d800319400700003a260b00490b80d0416a0080f40504145984240200ca005400204c001d10014519006d60043e0108a94480e540b02c982041410807032803004c0302040c0304651100c8400000c0d80d101500d0300513039520110241c00c640000c0c201f4482070355a202d86130140c0e0342c460510307070f26148039140010540441c040480b201071042880003914048500c0103145161091f50351000075210b00081e10180d00541d44018000121101130082c0300300044007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 515823732 1250 515822482 515822491
    0x3010e0f070e1807120c060e0109060f021615020c0603040b061c02040c050301140312040b0a030b0409060b0a21020402070f0b160f050c0309090405030d140a060504090515 75
    0x140c81000034160004030345080c81d03076803000d0044150f10485d142404482e800050051404d41007040c2104491400284010618042c0c00e040c04007114801400034800c01ca40c46841212015102c07800d170716281035101ca081201d600c00e0040c0b065908241d000d06041c001e44e03014940c07001445040e521100b0402c1078208800d260810001c05048a100c0503940798019200359583d07a445807907481d410400c00c04082143c030b03403940c3d01a034001c10704110304008031002c44085034441040b50f9111030300030354100c01403c500c07007038560300504020004003407006039406800100e6040302c0f419240d40d030758540b14003166246a040f58003a1040c525490240c1096001460b00c1407203401c0c0c0c1103a140656841e4101941d080c2c84500043c0c00c807440c07640140350001d510386105152410810b0400a481042c19524030444500c1406422624082010400c0030000d440441c08011818020507407180108000d204048507004040e9051400014882c00c0c140320b41c4201c00e800402601d9140b00e08105482071002c081d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 515824982 1250 515823732 515823751
    0x2071802070822170102070201020a031209050610060f0809030720120a060507020c090112030e100f021605060703080c09030f010f05060406050d030e010309120e03010e0f070e 77
    0x7011a490070075884035500440c3c1c1d010030f42c0341c1c81e506152022020101c810001841c0340c1c130400100d40540e8000882c012000d0385803915070521131211f02854007034441032000030400c0c4034001c284096909400800301c191f0300240c1da40c509075140084200d0b4031200c02e032503c0c0e85a400800c080c201168200301450740c943c68110114580601d00004902142d40c6200d40030303400c0d0040d0b01c40300304011381401610f80080161008101c800c070300c41c00142c80e000c8103101d001008a034812407602014010302000341c030901c000301000c020722840034001e01207030442e0780400c005000700c00810945903580107440f4142c40c00a4840c44c1014401c1d501030710322210181c042c12004a05200356a060744d03042100f041000010400818a01441142e0005407031000d80b0440c480e508200d014403064803032044240c0e0842e00352801040e5504801c00583c020100b404014201612910200300000c0c2c0000840d0f0792002e05400800515080c000c0c2142c90301040114000a034101040c104081c0085128280c4c0240046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 515826232 1250 515824982 515824987
    0xc1203110f01180b091c0c12020102042d09050f040506010f0e0a1a0a08030c010b0f030d081305012d05010f05010f030e010501030501050708180c15070215030a0c020718020708 77
    0x1b40710201c282e80d0721401101c001018880b946041003c3c003403451185180c2e40c0025400d042c102203844032481080d91440812401000c100e2030b040c041c03400b0b60001004010340400860511028840740020101d0302622a0311800e400010130a01200c1440b089175040e20b0303021095155004900058031100fa034296403032a048940b819155140100d42000b4047d01c00110390301d1811500f141c3c25a000c5c040c4044c8104a684551f80d403644010441440d84089454106815074a85005120204000c48050019031900714481d4400c000c0b15580c0c0b4a0340003201400c00303000c210f5800031047da1024021018030b103000c200104411b5009800d0300081c0b81c000c0c100459230302c0003041c015085501c241d1003503e05039181c0d814407418540141c401500040e004400c019075800c6140b40560350102180c075580103c2c1c0c144514011440c00380d041d102c00507402440008129100d11140031030340c1058a040524030311b0700120502e81400080e07810101c4007130440c54a055107041302094002d4010410a84000204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 515827338 1106 515826232 515826253
    0x5182526040203120a05040b070b01030605010b09030703030315050301090c051f08010e15130501030611040303090302100207031703070e06040305060f040c1203110f01180b09 77
    0x11340102d070b4854806004440d82d1095a014906e0382201280e00c40030000040007690480303001b5002130003103980301d26041c030a510413409000e900d81d0080b40304000190084c1c004201410103401e0400c0b400d656440032a00b550b54a26003142c40c00b500030307800d20036490840308004030307141d105103414404ea0424001901030785041c010560100305120004092103805001c142241802428028088a02c4140000648800c0c041100c059080170800e00d5165511003d48013180c0c0c240d5070780c124a603c5c1d0307000c0c00a1105d00100d07203401c5002d800c2c0080086483c18900d581541e51420100741e6034036016000912040462020030700c60f0408000030000301c1c0300080e003642c000c034400951000a03251441d02220f81502c0340e00c09601031501d01244e03010b2581001102556060200966400b000002c1c10103080340c10352850040c0c800c0004015101142880d90140d41c41083c0d88100c42c0c1c005031 = true := by decide +kernel

theorem cover : BRFrame.Cov 515647482 515827338 := by
  have h0 := BRFrame.cov_init 515647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 515647482 ≤ n) (h2 : n < 515827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
