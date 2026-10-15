-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5160
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:56:53.500294+00:00
-- url     : https://prove2.me/submissions/03c5b7c8-6682-4357-a977-fc46c2631278

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 927877697 ≤ n < 928057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 927878947 1250 927877697 927877733
    0x60201020c0610030c050613080316050d0305071b05010b0405070f1d01050304120c170903010b090c180d0b1014061c360209090d0e0d020607 62
    0x40307603004035550309016850340100c68860025000c2e14540b01e003104401c241c450306001c0c2c240003d0540c1c0098640103900e014000080c00c82e551551031003000341c14100b0711441512140100b00040c4482d5100340280e5006008642d180661408140903000f020100b10800311499943d81581d8a03850b00e4074065244030744443c0e01d680b9500e402492001d40741014a81401c2a002c508a02c1c4039950381e008010380740c02c00e42007202e401e031070002a0340c255088c00402001810050f0740c00c054504011041e4010242c4030800d0380280261b075010740500000107000d58403010002028080f010780c440800c201340c115600700a0a00600d0b451581b00c6540c161310035200103840107075404c005c0c401003001c80c90961b001002600c80c1c6107003007001c00c0c400d101440d540c04a4000305440d5078029041c20829940c00303559003000d2851205200c44105c1c903901d81022840304901419140380043c1018001203400c111b852030340e4941c6220b81c0070751402c0024030191813100702c1c1d0102052100d94003050365150f000c08000c103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 927880197 1250 927878947 927878951
    0x40c231206030303040f08030402120a150605101707051201030f0303051608072d03050f010801061503020901120e0d030b0901051516210f03060308040b090307030606060201 76
    0x500e04211a01041004015078041d5000b0401c0c000010389400b07411a500380c0282d00c29031641ca070740c0700040b0202c1036400c0b0000f180c450480a4824011035042c102c00d100b4450038200074180d0750704240090750b01900e61000104140c1200c4030300d581da6910320a980440d40d458400e1601c0c01522003260244801e82040d1495100203891004154051198540001d080400300104801c5000000c040c001c0040010080201b04042d4042104108161000204048102050710070500b54014014501101e041c00b55003184000080c0f010010f02c00c110a6034440c801c0d5603035100c07551006031701940c000620360f030401070b01040e1101072080c0341c841d4140b00f50555020301030070401030b14010b06480021590900c00c0b0030a0004000039520300c021024a8115403108680303402203140c04002006015030040c00d015048080102402c40010f000d201da0180c80d22a1007510200c00000c40c1102d00501009003543c80800091000240440c0036140060005044904841c1c03a580d60605441942d0321410260f9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 927881447 1250 927880197 927880207
    0x90c0c030f0c0d08190207050f12090114040308030c0a0504180614010e1f0c08070302010506091e07110102070f11130e03044b090c0806040c23 63
    0x70106021140021140d0318005415050204882d00f00841040d0309000c130a46c00580102040014003100c00403410b00710a8a48405081c1c21680070756001070300036400038066840c003400410000d0309a03801c2d07a4000b0000f60961f40c40801681d143e500c900c4952043c018144000507003d20820340702540c201349540c1c04a10545040840354481603031a2406040c0301600b1800700e00e940311059107200c55401150380d03402191a6000660340d5a4450001410300300000420809141c0c054006074000d510955842030165101d8607642d000018100640004d1540507000c114140d01c290007032030641030701c40001440c11109580e04242c400300f000301102c944219411010003443e000c0d018880e080c901c045d0610030341d9000407942c0c1e01c91003907019411840e26108012b00e05d01d07681001103004049900b5406034035280c5040c0190b00c1707844009803104804400a0040b5201c0228010550310360500c0d101c008080d05d4910030440170f070003800d42c048104050128400c0c06103404800c03090103181c8061b041c50380c034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 927882697 1250 927881447 927881467
    0x2505071404091101030b01170103080a0e0d0809091806040c0807050111030405090a0b0d0303050f1305190516061e030b0102070e040c0504020a03150f14090c0c030f 72
    0xc5040c0c1402a8855498000100081815581100c80062091800049102c16400103030340d40301c900510181c07148480800481004100c40c001c050745403568646808100c542d40810258a402403802450702209022089250a0400542d0307000784171041c4264006544200342807074010200d07000d0364421400303201006203050034407200010342020300c2d0049444407030082c01640d80c4564484d06025248139000108417030416408000b64400c010240e95580c800e50030014003500c030503940e000c1c1c65416400407a00d20854010100c200c19403100c05040d6486900d808140c104250480650b0580900e0301480c9000042007030080c084c3c405038403003640a00e2410040109403800318191407c0c989000c031031900300c2c0e80014000d400c4841d00100ca014658551400c0310049103560302c0540c01c1030010618403102c507016004100124400001c11605641e9403455441500491258038040e148407108101c003404e00320069940007000c991600d10308032400d00d980d803955101c00c81600c113080c00070410701a2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 927883947 1250 927882697 927882719
    0x31611010807110714060c0d08041209050a0b0c011b0f110a11090703020f0307170f1b0708070c030b070f080906070e0d0507090e1002030c07020105250507 68
    0x1200b25880d00c8a1803443e02e900c10340d0b03228018044e0003880d80c8280c1c030f0003010343d4030b280448041ea21b40d40f0540340207401249002d0041107042d1070407200000044018171001d0722600b0110104c0e1801071100c80702d140340490080140e408000600310a54941d40d40010604511180715602d42c001c1d07407000780d20344007000000c000c2c0e480c0158400e65034116a10300340100710300140b4004c1d0360500b02c41d695200d07143d61500b0740081c030610103420700380c1c3d401208010f110750301f001c0350074540d40d818001c100300c50390307000d5120381c0300c030703030032280c1c5541100b92f03030503002c02000228054540300d0322900d401c80c5042695220851800034a0b84110b40c04040281000141988520210000949400c1c203401c5410100011500c0b10001001394041102c04103000c01c20340d40d829441e8500300d0304034040d1409941c032819404007501a66020300200e1282000c0358144030014422284a0300d5148401404d00046074011200c0350b0002c031601440409200311a108070541503c4400d0b03040c8294014400180b07048801c201c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 927885197 1250 927883947 927883951
    0xf05030105042112060303020714120a0b0a0f050412110a03020604030e150c060709050109030546020306010e0402060d0c050f070309051905060414030316110108 71
    0x4000d0341007105010014500400c84a000100c02e840c5000d05200503804031504440d07003151030030380c504141002043c1a00032440c041030301d0001c107030680c1c100511010300c614400d46442c140c0c400d9022482501c0030500b205500b64000c00318140114010480b481158261401524181c1e0b1102000642217002c039040310b541c107110300701000900f81500301c075140a900d42800a00c06802e01590315652038056a484030343c0030713200880280058070303001e800000035a0750500b100c0c8000490401540407642d517004500880449a0080041030a0341807490740e10510140000c003400d030410000d001e40098004540a040c0890480c501c18484480c00e0040514140041e44022409080c480034407000d43c0300c3e54100c529801c80c41e0b202048641241c00c048a2030b01c207808080645070380200f03565040580c003030100000ca0300c0c2142d50310000e504403074002850404911400361b12100070402003004d10741050221991950003400d590510700442450303004001c28000c00c8518610a0a05107000c0d038109441a03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 927886447 1250 927885197 927885199
    0xc05030f06090f010b0708070c06020d020c03010219031d15100911040306091401110c0105100e01360e10060e0c070507081005040309080c03070902030c0702190f05 72
    0x480030341007400c001980c00006001c1c158117648009100c40902034082e088904c101d6004800155090f581d640c004c0d00c0309443c28024005004110410010f840c05000b601e103e00c032120040d020310200c14100303034020b050709a883c8110007003050400406903801d0125a40d803044004110145140014602c3c1851419401c8452450319000100c80c43d180c61800f5501501d50043d0001000e4030300f401d00800700789442e50740c5240345d800d017040300041c1780410003d41a000c240f40024425500c07101721000d038681d07080c003805951441c3d54004000726003041054207101e10407100700111182e80c0f4000a810482d1114901c1000e64503002600405070081181c00380610100350200040c1d030802120721f502c1600034082c1d121528000c20224148001800340c04010b1140743c044400003040303000802c0c0508804c40d010350100d0308003800050710b4030307010501c45540e00000300580f07000ca0a001c0a440250800f8204641070b142c28403000d00103803110020302407060701000310032030098a0180302d8042106d02e60449 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 927887697 1250 927886447 927886459
    0xf031c051b1507050708070209010f1502010b0d0f02180a0b1206091002090604091406040b0a030c060c1e0c030b060d0c2603070c08060f090a0308190c05030f06 70
    0x1a442003014602d110703401040ca46080c0360b4504180c103080840f07002d0307400007a5000a4900000800d0320291b41403e0480d400c0591603d0360312514002a800c07a06001c040719008080718a030f000c002600b1000c0051600e100501c0c01c403008021060007004240119401c010903607684c4a20051450722020f0f550026101000501d41c80c030303054241c1600d540c82c4d0000340c2556a00400c0055150741d403501a1006408010307800c00040460507404184080251a004e00030f03481d2110102290904038030400c26241c0000003402424502402201c3c1c2e400900003e8075500300002000000c8140745600c1d000741400b810303424000310f00b1400c6c004141d500181545218a0140c020100040c021390340940c212003844c940c0080142610001070817840070152040340c0b03804002403441c03c00441110183c143c0c0d052104651071079480fa820301022220503500c0b003e0340c0d400b00b40f0700c10009100b480290350102442a8040c44104102005020340d10116103c0c070100b440801003080d00440304110541c004006c07141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 927888947 1250 927887697 927887713
    0x30515041127030a03050702040e0c0a0b030702030714030a1e120e010b0406030803040c0501031e020c0a0c060c051005130212010917040e0a05060901050f031c051b 72
    0x212645407003006122602038008269140034403001d4469025210300250a81d0f408949034a030086c00d503484103c00302c0c4114036042000b4880d406c0001e0030300f00404047d210340022802c00300303048001c1d0030051005046120810500001800400000004801e0b880095480e600301c400c02030019036141c2e080401114170503a450384003e41c4541e031084101701040001804042100030a070140605002c3c01d80c016040c400000100310f5110001c5200e5805070301600a103a441d00c2c0110103a610b182620361220038124007031004010294020130749070359030000301c5102e6900c60791114410318080d07100c2800700f124802c0f038800340304082c0000d1760310b00b440c840c081010386400098102e00c1820618083d00400b528804040340c0031003544888000381d042040004c1b0544105021480ca0b80f1500887c0c9100c82c1da403002c14170501c06401214040d54009040c07030126070a0070140071351444483e0f000d42e81486040300c54043c1c50400603060100c03032100d503111561a010181e00700c0303103002c0300788256000c1e0b886400e0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 927890197 1250 927888947 927888971
    0x61908120306040f2c100c0f0210060807030602282f030d05090f0a061a100c17120c0904180f0615091e1109030309210a0303051504 58
    0x182e6442108080c1506080b1303c0c54005c2440c40c09a42c1d00001030032504c1c0c940c080020076041001c0c0d0500d08016030880d400084055215000e503102449441c4a583c0405c50501c0060040c0e0003804d1300c4070780030442060200ea070101440740e0103035181b02400410703a00c03940c0182d26010044c0e2041400410005841c041e4402281140d59100b160140c09546680d00301060440c14144952480451301000b1105d840a49041c114000d108202100540b43c08500c68001103040c210940b086008894861204208240e202d5900c1c01c14105460748025000300442c0c2110071405034002d00852002c0565501c46908509001c1101c140c08221801c484042c030b07031040051500b11006842170b0303014102007680d04808c0c400c000c074043c0030340001180a040c44918040d604491050303040d8481c9006042c01410403e0b58004c2045c0b20f61512a600f5400402c11180241407200c441e41c10006e4140306407000c0a1103440341307400e0583c51442240003d4841040c4101e240d404080704485c40320459040001128401c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 927891447 1250 927890197 927890231
    0xa0f0f020906071b030b150910080d14090a0620030c030f071e030c060c030e030703031a04090b0702010c170402010e130e072903061908120306040f 65
    0x44000b429104d08440700e8000c81a4607400304001c5034040c83d07105042c00c100240706581c15a400c8a10700421200d400142078103070410807801202d000c80c020305400201c0302e40881b40c1381c1d0480c0600443e5042040105a16116040c034000104280d5660703400d0140e44442046050080c400c1c4207103240c1c014001d003510070b41c01000f11442007007103000f42d0b561420f0302e180640341c9a60001028803480e800e4041c503c1495003001041d455284100f07401c0100324004001502119800e2001503030170340c0103014480019009a220700710294002e070780612424400302c002010317a13070b070000f0403030318152900240300c2032580900411a08840500f44421401c403050160b095104004101a04215004154486507100d0f2625000c0c3c0300e4846d5000d000c080e01000645903102020310800700600107411141e44c4d0355011010549400800c480e03904e11350746590040261400035a11162103a1160040003c2da600702000224551285615040e4481c6003a02c1044111084202c88400c414240b50340c20b00250104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 927892697 1250 927891447 927891457
    0x306112107030e0607181e261c18060806061c060801022106060d020d0902030d080105150304081e04080f07030b060f090a1d07080714010c050c0103110c060a0f0f020906 74
    0x250701d460b0040c2031300000007020300c01e407142a1a840d00441910a14900000e160406c803200c8070b4032b0304210b180a205890016002c18403a607000200044041a01813900b41c00600304d044d881401782c2c09410448000d83c04483c203a40c48412203039400108034104182c0100042d4178104910849015403410001152061182c03094101040380c0c001520041001ca82d0b101e55a500c0d009400c9440306444004003400000c003c1c000c080c41030301110501c0c0e0000000008a03445103a000342d0b60b6041c445e100901c004000b9a40410030711181040c00046080304d001c01c0310803c50340244000b032079681d2035800d0030960010003925060007114460504c01e41c60310b03074545164114403408030008411688044a0110142071207001c502c034002c0c00c0001070004000281301043e2a5000a040c02c1c00c0c03502001562040da0300721005085070482c500500c020360280c2e000a94441e0404c170320354500146820314504094048910421040e80c480300424401e0444c86040d881d031980520440c41c1000940006900d0302038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 927893947 1250 927892697 927892709
    0xa26072d0c020d080a110f0d0e19180204150504050d020d05010b190e0a020a0f210c02011521060f0f060303090306112107030e0607181e 60
    0x95141c0220840d154560520100303504074008540300c0219281c000d2050002c4d4045210512031405119100b40c00881c0714414243c00e5190194010f51800034403001d0142c18031016900c4000c03680004070514403e4803a9481c4401402c0180d980d0700704103d400c400000342040e41c5c10068144400d10180c0c4402c0d520141203901200c000d1020040c5190403405841c0b04249141c014041c060707040036121020051000791000320585c0b043c140d0390162034008174010440d103200000e654109444000f0701074a85080d8189045d11011030058840843ca000d407002c41204c01c2c0140e540306000340e02910718090000240c03a002d20301c10b00b0045811020344800704420401340032a0740d9000d00d04544510b07a842001c0d8449141003c0c042207940b0704000d08140281d22003038070098142041c010740164184116000b034880d0107103080c0c3d6009240c181c4420700200501c1d03001450750320800d400030094100001441040543e40306000c0e514403600a082c40d10640e44aa0081e84008850098100c081070030b01040d102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 927895197 1250 927893947 927893957
    0x708092a091023090108210703090503120d0c020609100e0307050a0302070302030d05070b0a0e0c0414150a14310218030303060102120a26072d 63
    0x302c1403240c50040340641d1258159404000d82c01014800e286048880d805044545000382d80c0e13a500076503211515420450801282407074129064100a03024100080c02480c0401d035054440c4042490146c401c03540034005640031900ea404400d040c00740584004051000d84441d04018401c0d941c0c420320f10008a8003543c454181d40d5010404105541c0f01c01c0e040780440d0318501c0c0504004c0e4460046010580c02802240017060a860003001143c44050703009444042e1991075440000041041401e00c940502400745403000340c0d55940105280805d6012000ba0030b814a100410030a940700c10405e4042c000590301000b005e80844038428000e035064800c48410f40702d58400c058100e82d0580f07402d07c814180e20040085409583c09042e500d0400c100d81e0500f155a04109a5607002c04ca91031401a8421400c1d12804441c01020700508215070802918600c9021404070319907074404d144d401c40300340301070400410503030105514000115104010981220504461030446050303055102840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 927896447 1250 927895197 927895201
    0xb010f0f021f14072a02012006070206010602190b130f03031b0309080d0c0e0303040605030406050f010e040b040314030f07030e0601051c0501020c03030708092a09 72
    0x2034020700460b64a0302640100032507003080450003000800140c3c541001c545203c1e0001a08280a610382d8102651156081c0340d0005001034130080340b641e1928220b04100d07910100c0c42d0035040c2e070198094941d540320050159464034210091500e1016441001150700114072259410750409407554001e070050700d84201c5540745028044c07510701c10500104401c074054000b10925503da03114540e000703141000401f030303800c1d94041201542c00503403001e41100401c0208506c1408954440c00d854071443c10040302642c2c1e0369001904513040795020b40e020490020400081218a00c111644000e0420041c10154100300d10540d501200a100902e810f17405804101898001c030362040da0569405500c595071b1a090300c60b0301840310700f40c40717240100c0d091100103440100007050280c140c4401400c1d5040ea285074103050079064604140c03c0e02c40d95420464a02541801c2c001988214031580f224002400c141c440c1c40d24021028084034254201780405901c40040354003804c0350708200700c811200d00c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 927897697 1250 927896447 927896477
    0x5120f060a171e060106110d140903010e0304090b011218030c0f06050a14100e06060f040902030106020307170a0c06241e24180806010f030204050a0b010f 68
    0xc507006183d00c018400005129140d20394000607401c3c140c07412960780c4d0660002c42c102c07440e0703946440c10515020440481c1000100b40544020b401d841d4402800031580d840600d4030b003421944180c11005a02d0b80310000c1c1000d03942c2183d991003111142c040100140e40d0741917858410504403070002403c10941411036070a10101d041081c024a401c4141040345042501000c1c0c0100003511001031003031003482c0020841103943c65201c00311001350198411940c0c1341c2e4100a0325610114481b848440d082c03201164405192002d50b01821142c2c004644d40c030001e0524078101e05640343c0603a0a95001c01c1903031509640f01e6140a274003580b00034040f920f405030495101401c202c5a13104c140000407420000385030b0410101e10807400405000002615850382c00b40c990031803015480c0c41074950184007528000e0303c01c4120000d41e044070310711020300035152400c2a040c803d080c1c1c4014018840039000380f066241610901f60041055041006025150740c00130b002d4062110880d828000040d80c030b1269 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 927898947 1250 927897697 927897703
    0x30c060c0507031406010e010806130b060a09050f01050f061c02030c07050a061d0c09010b0d06080706080a060b19030f0e01020a210b06070b07030f090305120f060a17 73
    0x3c0c650040c200c0010802c010300c81680e94609100305c01c2c2c00d4910100000d450000869070b98043e14031394200d440b281381c1946900840120140c1982e4000004490018510000344a5180200c070380d0741d81c3c60140d51501f010007010104a0903040e01c100c8041141034003252107001c540c6600090390384096102e54900f0000c1540d401214006821402040466800c12003198001101d100b40315820f141d01c4008000883e0740c0c0c0090760070072071704040440010312070410700c04081e01c2c0d455a540c40101d101612141c1107410030b2065842030008c500786109200454025014410280841020050500d0840e00200b40f844c0412019001403540c4c6058040100b40e50342c102040c1c1507400c20080d0340d940d00100c8011320030a031960180d8042c185052011940b00300346d006121801c800142007a0410403262220585082d000d0071040a2580e14070484e03081803454002c0700411802038550513102c4032105504211100010191242c4540c200108038082e519110450140d03001890841e00004840751045d103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 927900197 1250 927898947 927898949
    0x815060d020d0e160503031c090206041e12031706010c05120706051b030c030a0216111207081002161a04021002120a0f020c0d05011b020601030c060c0507 68
    0x54850700001d041012246550040310094503014100c0305080d00d0355002e40100740060240c00e5240d001004031341a0101d0b8440d103403500b61054080083c03540311607400182d1950040d40031100122130304101464035500b1280ca03d00500380d020603451400d180381c0e00181a51310070007458190b816030002041c03050348181158070081e54000c1c01c8521440a6507502d0140703030081c50302280e4090400e80050484041d0041c142160b504910100b810754a0b002203408058100031300f00c14620340d080c000142010a10745d020000c4a00a482d2004010514401d0040308880c80c0c0c0101c50340d0b880700d1420018001e002072400628403580000507154900b0041c2c0c004040300340040a441070403111543e0805803a00c0c9850360080b4400c4404220500c00780100f40c1c1c132030306c0740c000d02c8840c05414031950802c00d000b0380c0b910744403812501c1650842004103000032400020403800303640d543c1d03581e08104501d034580c50031880c20400b2030004010035813440d914000e41c0314186c055031040085003c2c29808202040100f04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 927901447 1250 927900197 927900217
    0x90c13050c091e1009051f05070c030c06030b0301051005010509032103090c01021c0503060d0506040327050f04091a010b130f030218071e0201050907080c01081506 72
    0x100034442a051001e181c2c60210780c883d4801e0513031500c001c0c0960b00404070f1100b21007000c0c0102c009003100115401a02c2e041146000c00d20404008287c0002d26120b091009075215183c0c40e107183d410118020200d444421a00340030360300d0001848031134180b4411050484909203452a0b454440c94046428045205a56408040c4644a202201d40402c014522401802046441140c041e1004903541d042008044402003241c4485c601c1c3c0701c4c4183c005550107400075100142600f90342d52200d03e403507000c030f600303800244081121541c0e06010070000c100c1d98801d103035451195410070780022070090414840511072507a820f21401006013030103440c0d0311071170700005030540f03580d41791124903046d401038440500c2d401c590388000c24807005030030400054075009800302030b00d078800c2e070398000001c040a45001c050040d110343c4001c1074404c0a045007489041c542c004202030821907002860803071660032a2185422015001d079250b64080b07501a03000f4255001c400042d2852008038080303200d22040c003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 927902697 1250 927901447 927901459
    0xd0b030f030c07140d03080c070515070314090309550608010f0603091104020a0c050c0a0815040303090b040b090c1504090b010e0a031208090c13050c09 67
    0x300c002c1c00c0818030f0812141508035840a0b0340740700c402c01030407507074070040140407030311640102d5800c4403c032024200240c41401200c1c2c00700c01c1078000b01d1010004642c4000000d45413202e1480c40380b800c012554000c0810402182095421030006490b49018154654003a2824041103582400d1000d24440e4103100b00e4a003142d140303030000007984075140287c1c0b120042c1c2c950000003406441040071604940003030300d0113030100381410300480107040124404c0e2502e1802c80400c00c000d42c1e6520040840300e016441d0440403215500d4118140024907071654810300d58140100a180008075101c1c01c2c48840061600460b911480c05a008244207900680700e5010300c002c2100304032120145902443d084021550003250075002c01c4040990040d041c4403082c0140020480040280c02c6042c6041c030504208004445040200310880065070050350844200c0d020004290740181c040d0342c000d031980c409000079007590780104da60b50810400360910b41d41e844000841160261007541d0016200801d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 927903947 1250 927902697 927902707
    0x220b040309170a0201090501120f0c03060f0e01030807062003041101090e2707091a01080f01032d02130c030b030a032c030f03131403030d0b030f03 65
    0x8001c26204440c0201d00b0340007507441480180c07440010707000e040c45905961b120149030800c0e004480f280c818142c8211055111385038890000510f011300c00039558070381c1c0c0001d082480c0c0f604060030211a036001801201204005001040841c0c0c22500e141e9005540482e220701051240390f111518006001200b0002000b440100603102c42d121007008800d036903034856230b6111803524449020907034500c00084403030194881da908049180e2408269024291121650383e451500f0030b5032403107400c2c0702841088900d401e010b50b801001540d008424200c120b072456055a5079003100541036040800800f0425040240040020ba04000802e030301400240740c11080100c1300001d002c40f02109404a401e00b100710405040005080c506140c040c2d40b1500c240c81c5060000c00d80b89a20754021070045c1c040c0c1c007041d006480401101803048460700003950707109600f94003101a2070741500220110129207400c3c8510317070340000a56103174041d468000541000c2101c0043e02d4002c40c903038408564040410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 927905197 1250 927903947 927903953
    0x1303141e0f03060a0b0f070f020a050d1a0f1909111c05210f070609050703050312101802090f0a14120102160f08120f061c030206220b04 60
    0x50b502070302e0280c544c480d115444403400700e4540250700d9400e001d00020300200c1c01044038a0300d01480580058407200c62191903802160a010755170409441211812810150b030412400c074a076882030043c0410201802c02e81032261044116800c0000385c151102c0240003030000d042254680303c17200a0030b075917840c0c00f6040d160510700c1d00200c1c241d40d54041c035601c041d00d03001c00ca44a0740843e2211b40605144c0038100700071510a0700f01c3c0205580b650340e03441990001900c100100310140d4018002152500c00000e1100c50b51003006003c01101055040c00304001c05004803c204081c1c044040584c1742c515a0000c10a140403104003a075210111020000b0b101401c2d40c1910011842070b034103d882a0480c000039800d0307115000781280a046071803800e00c041041581c0f80005a40720b02d0595141c10025403031310510000a959414a840200083c000c0034644443c0b09031000c010031001004040003078401944030b140007051003052001d500d070b07000145401c1c0c3c11640b078510350041c900a0a414181 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 927906447 1250 927905197 927905227
    0xd18081e070f0f14090705090118080304082508073311190812040c030609080a030513150c050405030a05030a081f030303020a050f0a0305040b1303141e 67
    0x211031300e029002d100e403010b4a0342c1803c0304c1d03451090401e9100d00e4070701b180480c01100e90703000c4801c0725040c00480f22000706981e07005000070001030100310020141c1c5c0c5048060f510110401c03040c0c1032941d2078024010048a400030035100c1c1100d43d0483c24011030740740c42040c42c4002102e118a0300c000c40c821f1845a40003a00000892001c2c840e10040760f058100c44415410001d0000001400e0365105002540340701c07260070030481d8000c0c4a801d40c0c0500e241d42e0743d5200d0580d04855800c0320445401700d40a040035038144603250380314680039050025044140ca518101450003091350350100c0e11005112101da0040040f1401010050100c512240c002d0404a0b120b401124017135000503403840208014070841c0a09103100000d10b03983c000300c40c0c03942ea0103030003d51100100005001302401840144058040903095400f081d440215540c81c00d4901480c0c6560010960b01d400307a4500c4200d0b01107507110480d0816500014081540c404803800c03207400d9080c047d2004800c8080000d001c5403604804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 927907697 1250 927906447 927906449
    0xa05060f100807110705010210021308030f071509110d02040e07080708011d0316030e09010b09010f02030a0f08040f08270a050d0210090305010501080d18081e070f0f 73
    0x10781c0d00c502070074048030802505d5080c6880742c2e900582c0a0350022441d06120740c01031501c440c04450505400755900101811038200b0b410764001d01d1070100b50a420302408090200507005030348000c00c81e10400340c4d80e80041601c4602c0d80d5001e0806414414110349880d480f11184005a004548001d0340d40c2c04d84950313801840c00b5004165091401e484044170992204154854800002c1c50414503801038800c1c0d5007040032020340820555442c0740106272900c1c04601e002e046d070b0003000d99460f0901070005d012070900017840e40c00c56008002c1e58045e40d0b8024043d07a00c076107a61500302e00544550401003007a182d41e18020382020742c002540400c1600306d0380840314140c00ca40308414152700400c100220b030b00c210311036160092211503400c001403a003900502100016800e0482550fa2039032580e6013100d00903080101c0981c0603410040100c0c2e0010305d07000c41c51001810200e034032402e0490b643d071141a448cd1241d0302203240b40301410440024442c0b5005090300c00108003103503a440c1641c01c07141040d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 927908947 1250 927907697 927907711
    0x2010f02030c1623012918071b0326101a0904020d0203070f090810050603030c01090b0a0b04110d02030603031b0c1f090519050307030f140609060a05060f1008 70
    0x100c6007006030283c442c481c10406d00801040501b0360100c0e10403c2880800003000201080103041051403250823030289111024003a0b9100602521403003c0c60840e402540c1d49440140208804c10000c03400311130540f81039030030600707911030300701c02e03d00c80c800707150154030344055000d400490020400d1040d0b5001d9881000d00d030742c9010100c0708100c4c05507801c0109015690340d5400580d1172030284c00031900669000040501105d141c6030305070265600f11091003004030780300c24100081c800d08440314012502580011a0b042100c0c00714041000da140c030800c0011110035402100003041c035070f02031054402c0b1001c0a00b801c010344c20b241c45c40584a0142400080c4211110403811a00c440c8020065880d03400c0b40d120103c2c490708100820241a80a004400c0e0002d100782c008242c0b62400d00103800114480c400844180c1c806252004121822a112030301c3c584c0710104000c4440000651260020490180086d0544030b02004ca0110300c0442d84c415040150380b800c1c00a4158490200b51007101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 927910197 1250 927908947 927908981
    0x21516140c10020607051806070b070f0306060e09090322060909290a2606090a0b011e030f08120606160813030b0c040602010f02030c162301 62
    0x59400400400b0303104580300c42c1c0103901590001e910795016000503d4407100080a104003800301d5030014100d030f0b005000031034140c4c8034142480180d642004144005450b5400d040c030034641060300051401c0c50b0781f186c07144240040310101c1ca220700f0900407142c444920100f81e0020340c415070205c0c80016a2445100c0006d500003000050a002601c14641e444042512070b40703c000d4503a80815040300b6151246a004005800000d620b806202c410342490400b00d802c84134010301d01e25114100900200701c100c442d042500300300002000c0d00c1001c0d06541a030b4038048000c00c00000381c03401b04102a00007c04040d080c0c82d195051007112401b624225040c004404807a0340c40805002980c0500d103034040102d103000ba1072900040d4480041c0100d010008160011542e594554031000903080e1034003100080300090511990703a080c061008183e0924a0661450402d4510302c440c038404c13114140000480c00131ba0104021130b51200822500e0110b10351500e01c031103512064001c0181a01080d0208 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 927911447 1250 927910197 927910213
    0xa050a05060f0c0301030206070c0e09070501030b0a0503060414030409060608091e0309241206240f0d09020904030f12090c060f09031a04141902151614 67
    0x5000b1851041c850403202d070035907085074655401c0c4001034002c20000c4610740e01c80400410369030807218070706100d0b52100c0c0007020700c2480c0c50700150481d03d034120014000c0040340d906100c540c81c000f03036054020340e210241d8011304030701e81e008500314080c0c0d403c5103d003107050103030020300203a00c200d46038001d20322403090741d001c074407400d03038050900500101d42c58458106204460652078142e00080f00101e81400c40701c25815403040346085940f141070318408151a801c10f07c00b030b40c14072040161500c10740308100c00c51203440495a40942c000c0208150381c1d072000003244a841801c1750007807120940d024000401d541050300e800740800203000b10803c0041c41c03011a440800e00035010b803208031a007200780c040c04c85081c03110466800c14050440010701c15402000000108594a1200d01400380c0c5103040040c1064940f002503800c0a01c0b00040c0c66200451a0003103070204c0090102c0540c0c103ea84078482e003441c04d11541e0501895070509801003088600101f800341c006940c0300b40b400031718280c0d03000e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 927912697 1250 927911447 927911461
    0x7060c03150e0a0207240c110309150c100c0e041e0c030e06070e0312030609060909010f11070c1505070b061c030e04050123061b0a050a0506 62
    0x1ea00c03040c050700200c12458410890342c1c0040c50416003000e0800000341c03621915884800000c584082c04a0340f5900d40448103a80302902e224a400e02c01a13803416400c2c02d0715003150160b80380079094120b441074480b1030100d240800c4400480d0680a0b041c0203440b50080b00031401002442d48624007808030f03144090f02c0361189064171840301240c140085c80c541e080e0b00b80080200904c1c0c010311081c00e241e40c8401c0c0007200402041000e210b8501680c408100d403a100c0d06041c10b2000404000700550410b000340b111995a8608099100e071098420082e03581ea60a02315002d0b00c011030007407000d949000c009041082c558002410028010100c00c46c001d9960703a200e60030481d40d00d520100180d014408400055414003101d6003010008102050781141d10400300000342e032942d02280424180601d0b5179080c10070f40281c900400420741c000030400500408a00000d412000c0c00c0e108160004040c018480310b441806030070001c100488151180500d001a51210900015521032180b0300010b0b1174 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 927913947 1250 927912697 927912701
    0x3150a0501020a06020f160b100605120a0216080c1b1f05070602120112020117071b02030708060702061f0503190602191206060311160f050a0807060c03 67
    0x8660040c1d0040c82e00c3c10241d01c03880000d420500e8101c0106404000401050520351181c0c0e070070314003a0036029032500304a2070001109a840c0d01440920505000380c101c4900c011440c69441a81010003507602c10a0b140d28001c4040d40f12001041618081503054044000180001d056003000707028448010031082006018481001780031000201920740d0782046100d2006024505e101d4000581040c1c20a004040010700981040c40f1900119402405543c0c0c0b01203000a500c401418602442c10f0514000305071024035841c0050042c14a9400d44c2151030401140000b041c03980142c44490034241c50081d2030b41c6c0709841e00c004d015954040c91203140d882568203011104c00500420201c04991901d19101c030321100140d44040e400d00000c081c040c032400c1c074080300c1c10480e039a0045c6840c40c40798840403148290411000c0620b07040c0c0100c0c004080404070f810140c424210000a0040e904e808445e00080000080c500c3c050303001030f01c04211080c80070b080098480c0806006201e103e4100b201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 927915197 1250 927913947 927913949
    0x207230708101109040c12060806071e090605031b0304062c2d1902010f1d041d0708010f0c1b12050903011e1b27050d0803150a 56
    0xf9000b0800c20400806143c291300c2541213682505110a564480100f42000c44225601080303640e040682000030300c940c8103926512220b039001c0000f004007610300c1c0042034007180740100001d002001000c51f0600c0c1c06807501000010009645555a10f458584200641a010a504c440411802000c005202c0c001008010002d0100052868041c47e151000c80d079140c1c141c43c2d01d070480d80700140100326001031040840c00c01e4541c6d8002c950148520006151500d100010700402c20740681c20140c81c41c001201c1c0021140c101c80c04101041005907110340381c0801020071104e03114080c0c0001c0c641e031040d0800c40450a04280130000c00c40c241c9000e5485803064048245101c0001b181d2000160440d0082c10701841d030751501c18140803040006c070742141c91928092070301490800c1e0900040704240242558050b045500001c001c5100b01c004d06458034170801c404401002e031901d07422446140300b41c2401000d0040004609007414249591154810f445103c1c1000c0f0410f0000010b06100c8540e09c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 927916447 1250 927915197 927915221
    0x5060106050f270904050c0a0504022a011d0d1e05030f090a050d05040503010f0b060901120b03240f090606060c0118030206091504021003020723070810 67
    0x1901c2c10b091500b0b102c400001c1040001d002121191800c0410b8850035510345c402c0d40720b54000c003007010710f11b0108a007000701c644c0b1091107a030041003407002e0b0941000e95005002061524032800c1c0c5e08014030b507805000c14500e1140c1e8607180c41c8c00e0f000407000000307140802000548138903078180360b00b9440340c0c03910034610340320f40c042407080000c00c101c5811410203070b620002280036240d4415581d5205814034042d20140800200046810300c4145030030b200390700d480d5402c00d40422008034443c0100716607014406803036050000507089a0754030001034111114055005094030388050f518003420380b41840282113034003401e0b01c0300c0028010458402001d40a034440c20300902d100e9072003204000c4240c0c012011f200c080d54844481146004000f000b8801880c030980180100c3d1408040180c98401c800001e2101c815540d001d11002d070711120060005060945000340e41c4600307906040010700c2182c1404140700d81008074000511170f02141c00c0d03055030382c0d60042d1741800c1c02c4481c4143c15141020310103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 927917697 1250 927916447 927916477
    0x510030603030519030b030114071805031c0909020406120b091e0c0904090f11030d0e040207030e1e0a08030a08060f180a0c170c0a1805030109050a0506010605 70
    0x1c0d00910302c41c200301c500c010f011461701003503001007a4086804d4034900100da503003a510160074410103d8201c4007540142c224040c0f100c07c070302d00e00320010380d40c0c5a1540411110521404480010610560498020301080c10f4295a52a692030005100d00802003070824024034004154500e0300e8072261241c00350201100c0038880c03802045c0350701e0391000054481864900c0c00c00c0100000d80f01c9000b0081514000d0b8075080f030030221814a6070000c000a50f20034840c4e045170709a1007109800810060801d40152030060b29803000c1e1078251802400c20808a5000c0c2c440d0b502071207100c0d407503400c41c4050b143c141d8030340c0d200581d5484559a68010034061201007045400000c515080491080c110800014240a04e40c43c034000e03c15081142943c1d035480158680b490000c00d103070009040c2c0d01b4410000d01500f084d1420040360a0f07a0f009040e010001c1014070000302c0300f08203180342d01c4000391000a008001100c2c0c2c52a2203585c81d070706110101d80d10701a90b000094081d000d40141c4506000704401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 927918947 1250 927917697 927917707
    0x1504030e150c01060603060e130c03080c070e09060a0f0b030a03030b04020403020411040e0106020a02010c0311120d15050301050c0a0503040f0813230102030901031509110405100306030305 83
    0x300400d0400d008401120010144026290b8032000d001c2d2a000f081035032000a402410000600c000a0307005080380300c00c1c0c02c0e540754440090440100c00b0200c9810400303407511011358441240c248689503004220081907030003400518100804d00350f02441c0007220822010404e5500102941e00040c003580e07058101c5104000441d01075001940203902c01040180307001c1d1250300040c1111085403000078216400f182c00e0041d544807489007070241140e400104020b03005580020008802090b0081c1040400810a10000d200304040740100195005040d01c0b01c2109103504014070050750b2043c4804420b00d0001401e040c18860240904043c1d4505440d0607007282c41a9030942c80904101c40002c01c8036620341c0442c0e02440609243c2d188085082c020b24900310200fa00d805100284c019942001c2d89840310583c1c001048a11001c000e0801140d040200e14a8084c01181039020f4104e103814508e01d148482c802c40c0041040ea00c0c21074034031802e4220120102d04494181c04001d0120b0b5003000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 927920197 1250 927918947 927918949
    0x109050f0111241e040b1306020912010b100e0a03141608011a041a1c051e070602120a14040503030c0106151704060c020102090907080601021504030e 66
    0x20350480e01010002103c1200d010072200d030807042071984a0b00ba035031141c80180280756042800228464040340380c4a485405e0179101d0b01c088500c0604000310704500c0a00d44c0c0e007003100342d406542c0d44a03001440640455840c8842078060441d0b8100c0c64401e11954005140190044070f804000343e9002d04001040f909666803c01d0607140000b62039a14400d0300d100090340305407200104040c2407100000306400030303041200c800c3d10106580643c807890070541741c0581c02c8a1a0a170b604002c408032070403440b00404c4d01a40348012030080c0d01030301c0c40c0a0101c4c0a01c1a400400301c0c4c0c00c020581c141241c104540d541400c07600e4400007940075108a00c00c000c4d020843d489041500d00560180e0000d0f0304d420b1781c600c002071a580c0242d81025490351224010015403645550080c0724070703024248004c41c04205855264103210041000381003d07030310b80b00e00320b03c90301c00d60540740282c2c406031102c5254201940d0250050108a883c18010f00c50a41483c928400020415004d15419203e20580b84e50140c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 927921447 1250 927920197 927920207
    0x12100903021c050405100e03030304110f0d0303020c0f07051f03150e0403030605060a391b1401081302122d07240309020405010603050f060109050f01 66
    0x21409504500c580a9058410b0b80300c10b0a01c1010081900d403a50b84602e04418800f800d0089000507007405448400d6058503140482200d6015600850081e5140c850000040e0414450030350203800281d40508442015050f500070300d403050b034000c1152160781e5800c020540d540254080c2981200340d0490001e071700048080c01500c000030b81d003000324804040d0b502d02c02100b1130680c0b040c400c0c04429000c0c8014150544541005070900383c800500c1c0c0921250701412161032008a004101da2045070640020b0b14040911107640c0581d0915102c0302d2503050104040c85000601070040140103000102c070114501c80d800c42c3e20741030b120002169191400c00044c0706580c031041c1c0c2c00402803001c000106100f4070080003585403889404005840480c14842ca40f2000d05020f02e15502000f0f0500c032010580c4801d100d655205045441001180f030002c40140900c080002d40081c100380011070119019040107204018489a8502d41e41d41c50004503840c286500c15550403105070240ca4000d54031407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 927922697 1250 927921447 927921461
    0x1051011010207020310050402121501060c06061a12010e040c0311121c1d0a1707030818040f14010b0a05070f0b16090602070e10030f0302010510051210 67
    0x20300e00040c24204140c020906000c145001d81404079503407001c01c0118035018620180d6034981c1d5000b0030000c04040a114170340c06060043d0000d10515130021002c000765a00030b1000f51900883c40d20350f0000141b18111316410103401c1d50065201c0c800041901044045400e10550b0041e9065106910f1621081d102c124003c51164101c0f0f10b000308221020b000700b000800b8640e07010401080204043c50083c490300c0700c2910250110421a060303180b0340d45103c04003096540200f564000380c0007040ca95403820409a10081c0700420101c1c4501248110704082c03001c2c6441a5801d1212255403002c030301c200d54003031000c0014680320030300601100c00c120000d00000c0b022414280d20305440740d200c42c20302088504c0125410440c82c0e080003610100806201070b541d449091071440f00d0304220010352641d840f40100d000c1002044001000ca1030103010401c029900180500041c079140c0c1002400380404507441123564080c1e00f00040c5a0600c4200303a201d000408000d00314030151620198050045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 927923947 1250 927922697 927922727
    0xb12060d110907440601020c0d0602030f010e010803070609110604080102040503011d07032006120a06081c0320030c1e070309030308091f06031a010510 67
    0x30840d8404110b4541e200712038012015511443c1c0b04408001d214440301c044082503250030000c203106061480d0081c07a2401600ca030400580f14581d40d20360041349007041d031800d0242c1c020000c89402e424800b16034011805403140d5002c001d420303a00c41c00c4d54034200000f8400c0390107a500401c8481c000c01da1b83e50010500703c0c441c2401020450b11700d070000d0006c0d002504902c038140d500180400c0715190900c0f543c1402200410b044500c0301c900c0020907110380702807001420079aa03902168003402140141084c0c0c0305801801c0a40b9800003d1408481140468a58074040d240070404644060001081350b1500103129102c90007902d059000ca020b440400740c203580c070401c8412420150710001d40031350701ca460b852282c681c407201c02c010011414004548407201c1c401c001c00c00705021030f510001c080260f0342c06007484c44468460340b00c41762410b0f40f903c1d01d0824160300c000c0310700c00c5d00156800c9a002c803805000f0402e48030810001c070b44280c032020712a0a9111b040d0071071001803107010300030ba0150401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 927925197 1250 927923947 927923963
    0xc05070e190c02100c0e271801111308010e0606030601260106090b1507080723010501030b01180608060a0e150c03060112090f02060c0102090d0c0303090b12060d 71
    0x80020fa0041174440860030880070030040251500942001c202100c403a1703a14030a00381c01004035019004c45c142c4064810001401c0c1e0704151030005900350004811007109240710760780c2e0380c0600c0c07052641190600032002d483d401c00c0c2d6080b20000380052503a00820f00107016001710b903c1e05031a0005500000d0700700f1000600f1046500c2e6500c420b11a010081c42c00c881c02041103141e910810a03489003945503101c80890a011303240110300c0103020340d5a900d038080e580300641c4402600705000c148469100507170943c01c1c000084100512501440e040b11040740c602030104502d100c0c0e60007030740c805001c0c400e0355502040018510f07a059402c00700d003003001c001c150385545080050201c0001c60031150a405123100206014455038000140140004a0142000702e00c2a42c2c0d41c440d4045542d8030b020b0302c07506010408079034800007941220104c00d001070000041440318a8031001c0c078030391888140c02051045900003114203480080740c50060310000c80410641d40c050400981441c924000e0f14408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 927926447 1250 927925197 927925213
    0x6050f070e062a03030106030b031c0c020409020405090106030606080d0507120c05030f041a07030503060405270a050d02060105031f0f060611012a0302160b070c05070e190c02 77
    0x40e641e86a03a030015840c1d80f01440c1d41307604000014043e518040921070003580104400003c03444840356146e60040c0034548109800389a000040140004250196206107407105002a800d01540804200c9208110a2101640e101400354070b82540c0b01400002c2042080850000f03260309009440500303140c1420144582640c869615540100d903210000000014003800103880000e12404140d03d07006070721303141800b40d5070014507600010301900c4c0910344460101e48070340b408038004014030790007058200d80000d681c2c007410f644112007481991240603802e85034034628804280d540c1030300c401400803c0c9041982c072480301b441c031010f008070320721903034454000341c600c0814021070f8000d10080d035403034003401c50302c00e082821690903184048151440040086c00c0000b000a45640d400c1203040c016215000d0a00d0010751169814006002d0041e4008100d600741e0030141d049011400386049401054075540000d000c15400e03100075440000301d903044110345403260412002d021491060f12001c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 927927697 1250 927926447 927926497
    0x14150d02070803040618020a150924030b09060a050108090c0301050708090c0a321c0b0a0c021b0d052b020c0d0602220306050406050f070e06 62
    0x2a00718041c200c5000c02c00006000a001e850700402400b175165046144091449500003890743c1d00611400400740e2601102d040c2890141c51102d000380302e0310010000c00300c1b14080c0000c03000305116031180842d241140d10383c07407810720b92034652144201511414416003000015101c0c510000c0818030f4034412466100d00c1c0c4d440a001c0c07a8007842285e1030319805820030305030a506190340c484696014624078541041a8000d099040507000c83c050807003a0f41801401196010948034a0700d150003142030302001d40860745c08100c14803c640500c1032900f407a1650041c0343c0644444540150040c3d0003c050462801da10304000c80c80620024202c004d40c45d000d541c0e46041c401c9641c0c0b0f542840d100b48510300c100d441e0141d03007038584100c148003814031564a800041c0c15203841080250a459011640100c038101c40d0007204080c0760a251500c260310b03920314111020782401c8408a80290030500840d02d028200300c1f00d140101c487d0f0300c40c6d40300820400c00380714454001060305c90100b02031048503521 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 927928947 1250 927927697 927927701
    0xd03020924090f09040b01210b0108060105030712030207090b040603052d0102090108011404060825050402040b090904020f0411070c0602120a050309010f0e0f0606010302030114150d 80
    0x601e018507074003921a4100360410203c3c582442c84140582c0f010400c00c4006030002e001039054540800c0300c0c40c0040c001950790a045850008014000b180140000c10003902c00290035040f1201101180d512540b83c44616440c1104444014090b0740245804d00c03400e02d4075000200c401e103004d000000d00550ba620350b80d14051030a0030200742c0b40c0580c0c0d000e030307400300c401010700076007900d4800290319000c101130008080110510802041004603080ca10701c42c1c2c0e540d0800c50080c001c80089a00340c0e800c80140814030101071600310840c800c0c2400008480c105402520119112060f52a003031003030300800d20800c03100c0100700306d030f02450380001c2c148195520b1151594100c80524841d890702c0d560310b0000400301d07085d04103506550042240c500003207a0001103510700401e03480d05c00d480323440e0001800d014060901d03030020298244034802440702000554a050128442d080ba40f40f51281c50064080744000c0c0540b02007544961945400750520021a06d80300c50b0b8280d804d4034100c424680402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 927930197 1250 927928947 927928999
    0x10b09010c0b1906030f26040e04050c0613080601050109030c0501211a04050109020f07021e040c050c150118090804030b0c0c10060608040b064006080d030209 70
    0xd240340403403006400e00942d21f112640f50f00c021200b82008046042d0107c002e40614414814000102c100050400c201407100e040b120501500312070310fa107040c4500030720401ea180120388642c0710f84000080c003984a0b00000c400c50b90400480320b074a0781000d0044500d40e60804880b020f200720305031740700e21a003828803541346140d41c100b000301c00608007503007000151441070f404001d40c01c1c014040141d141e100c0004450400d0342c111080200f55101c800c112070458000040709600901e80320203d40d805412100606112a080040c0d41c4100c00424640340c0300b001c217001c1e0529550300d0345203002d04107001d80d01111500b40210045410180e0701e90301c900414404030307200306115001080c2008030701010000c595031081404002d100e168241030005040d100c0081018201c4040c2001041598652030b141c00d07404c202c00c03a4003000c0441140300c60000b03009a0444a5040c0d1004200000d089895209000a4401610103406d1064000d84210040d4209040303403a070010940c40d42c1c0340c4860200132080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 927931447 1250 927930197 927930203
    0x510020c19210b07052d1206090f041205121009060830070206160210020a230c19150e01051204080918040b010b09010c0b190603 57
    0x541460070142006100315625030b0311800007a2003a2190001441042c86681c800105d103080c41c0c0f1002400800005401d24010001e4408004d1034200c0d4030f43c8864000701050307610496034014940fa110203002d107000c0210b9121140c25001c00210700012075144000080128502d003c0c2d09201c618444500034500c203640454034942e610404101601281c020540140300141c064201081d400c1981001e9042d041400e0003c4541010f5215210300c82c1c0055603513054000c0c01d05500d40d900d0034115240000c08030410303480303a490604030031041e902c00628070302c284d54407041141c4400030200c496164403039480340007034003401190302060391901c8000000302c8200a40401440e81482c1c85d017409190f00382805424208600309107100ba050b60441d08590181005180010081d0b98a0401c00744500a0320306003039008102160789144001c0461215003e540103101e286d8050341c0c0c0c2c0081c85414404c0c000001d000c90600844078020408841e0003603400390a0303d05070440d60480510000864170150021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 927932697 1250 927931447 927931489
    0x90a0f020c060603510a020a110d05040e0402060408060910050114060a1b0203030f120907063c0c0317150f06070c03050607111203010510020c 63
    0x229291070100311405551117045600440b0b6404075040b0000150650790000010844082d58a881d131201455002c0c0d0481020b000c480038107100c50708101030340c0440c40c403800245403840f46001080000c629500792031003a44420345810310785002502803020051003607a21500501c00040d10000034844944600200000b03016140c0ca4046604202e4006800c100c0103266a401210882c4e00e0303075400c44003440250300f0607141e450401d00e12034001000080d0029007500001c03071400c8481d80348601414040d80c010f01641c200e69119400682e07150118441c0c0c100144891880c050102042c1d02d03008807640b40c0c01d5040000c0203228000c881c0c0704c02d6012400d40007c030701c1134000c810300d54045080000c44030342d200052801d040080c09810030004000c4400d11440602034031983c160380b000e0032605040d900002c0014920703568106039407164401c071031480114903400e602103910036020600034582159001d21a045074204001c1c000c1d550352000010095100c6d81e03041d0f4086503514110306000e00c200100c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 927933947 1250 927932697 927932701
    0x20010504030813020901050d020415271104090914070305030307030c020609070504020d0b030109061401120c1a1605061b070302060109020a050412030801061d030c090a0f020c06 78
    0x801090220000d1040b4040c01d400f450743d41c01039440708842411600110780c0a490034080c0c0c00080d004121200380b032000e0307824050000945030316000d107005241000402e90011040800f46c3c0f8010750340080f143c0c10340e000c07080009000752411584200f0000b0f00035440c02d0200c60860b501c0301d00c1c02c07644d5041982c13a82d0011042016a6071715000d040c15010841c03000c0c03d040d042218031603035211414001c49202c0d0780c01050081d05c1e001940e0041810540040c002c0c842540c60381045c0004041051524025942120000ca21104034210820b03030740c0c0d031004500c0c0b06949404c429084600191a5941b11220104400307100d5900045840800301c0c001c07005040c450801c5c00b1014500d10040d04c030050723210390612020f408240c0205525046520512001d0380d15010003104031118841c42e002003d120803041d004205160340314040c40d060b664180c4035250800c1c00c040070881c003110007400aa500d40d005a00360582401e00e611890b411520070400841e45940700406201030760800c0804006a40c03101e01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 927935197 1250 927933947 927933953
    0x1c030e1005010906090614010819110409061d150a1a031603050112031206051906021002040f03060c210f0605061612020c0d030e03011d1c20010504 65
    0xc22131005111102003000303040d1500707035058042001030f01e005041c4150003000428069101003000c074105024141000816020a1146190b411a002d00c0340f403585021130105a0000124003017107504264590020507544041900300302621a8516642014000d5400940e000402d44001c0d0044440c6c0000b41d101c1c41c1292007004100c01480c200030805081500402a007101d00c0b02e51070311207806151158030100000c1c0c803038000d07003103ea005070f4210490519094a418440f2401025aa402d9090f01e100001005002e816800303a4024240e119410000800005200d41c0c040c0d40c90080d44d06212103d466500c0040b1010300301d541548000750313208c8084524500f1107101e09005007004640c91424800d2009040c0794151580d2802000342141000240e115802005000f2030540c00400f504040845480c0040c1820f640001c1d03a8000d60a001d94403030005040040d1002e00c00a4200900040c0007940c0c3c460001344580c4109400d000750b03000c0b11440022203210b4540400c000500105090409207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 927936447 1250 927935197 927935201
    0x100f1a010903030807181a0c07090911062a0705030c1801030b0c360612070f0c05070311090c070b0c0304140307050c030c030109051c030e10050109 65
    0x41555040107034800050001941001050303401108074504803080c05000c402072002c200079908800042501c40344400c0c1005034030402440100ca0100c01e440c074181d03907040410182e900b6600002d1001d540c1850344001414198050300050005041c03051907202c0901100741c42c840000d0f100030a5400c140303001c1c01181030030018020111000c0d501401d076050444c40010780000180801480800d03540b0100d90b101d421501603402030102120079550002c1c2c0750783c11529401030300c480100c2c010b10071071040030303036140034810349204070240c0c0016403442c0d540090484101d60004585024810441e8030040404c008101c69000365126500084201c6020020031250a038000c2c8190300307c0504020060000c0d070460350040e006000005d042c0d840f6107440c07518841c0740e80307100f040e005070303200c0410301074180f0800240d07903501d106041d02602c800803000701c203040c2239424958000e40503521940c1c0c0702d03035a0701c2c801c807000e290b59015244c0000c441b4007528103642031404e10140e540030703242c458005002d01a418 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 927937697 1250 927936447 927936491
    0x34020f07080309060301030f03180e0906060f030604060f0e0a0f060f060617040c0506030903070c230f031203070207080f03090916090312020a0b0f04110d05100f 71
    0x2041c015410500e402c00080e10318441400000c04c103010f28000ba208141c080e00c00c000c8400900c00c41c2c42c3d000c0b5116a40d02c0c000701c0301181e06c503006104110100e0028148880c48854114001d0040c000598440d20740c6005001d0024414001d15501c98821040e4002442030302450380c490141004110002d04010f000e4540c044041e1041c01d2801c54104107494000b01c1c0e008071150202e8169105645500f08052010440d511540d0030801c0081000103004003c402010000e10948000110649070407810040d81c1d420f2880080314410081c000c01c10385414269178034180c000604680358456074040f43c0c002c80c1c10030359483d0f026a0201c0d00a10910b10140040c0100c1580030004605040c0b0701c1c0c000400d1840041c0040580c144158098070856214100c514041d54009c0d01606d04032181c10320095960917000000e4803805940d10218804403081c00d29a800341e50402844106222a20208081e008071440204d6180c400c0c40702036420300c4614001c030710151601541c00100d20712540d240760300042035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 927938947 1250 927937697 927937709
    0x603020f1905040204060f02010e1b1003020c060c1902070b1e07020301020a0903120e060d0b040e011b5301091517060109051305120304030e06030103080334020f07 72
    0x20165258803082c0410494881c0d0440840b442a801104840198000d01c01e40403004040c2c0102411c004080c0c00680041051940c00c803042c55442c0d0035104100d8451516005100d1294802c01c01c1b0a11184040c400340c00300d18a40a09910702103440d4006800c980c00401c548021480c506410401e000c1544020711803c00c2e03500706420000e02c0140000c40c50b11980a0000340c0079a158001c581903205d95000e41e040d000310300c1c0200b20b9140200c421164900091504400107040d04100d076024072660001d203c20b000500c7c40107000d240c50701011043c06542d80f1100c200066250846e00d4103c1142803004c1c0c003c0c03040c4d080008010200007507500100c05a600b05043d461009009881d401d240000d032a130440341202c00014607a1a420720f02507224920710720142880c40348400c0059810003410040d8050391003510703910700654400b410301c00680030921002e42009024400910f180c1140c8603202041004681070f105072000402140800040040c0c500c801a0711220b44c0e001c203144100310140c00b03018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 927940197 1250 927938947 927938953
    0x11030307030c020d030c0f0501050910020a090b0702032b030f180210020f010e0106050a0503010605010507060f02040b04030f020f0a14062118010f0603020f1905040204060f02010e 79
    0x24007618082e024850900009001c1c01344500d16005142c0708851603443c0c994012039011840109040042c040c02d003c0c1e80851950203107103400540c086440c030840b214825141c48410085140c02c400344e225420005060341c06001d1340065141911034008040c04410a00070040f02508040400800715034803040c905506614101070030032400c9104102c07030502541222180c0c040c0030581012030412041c04800b10a540c204a5080d40782603043d00a0b0007501c40540c0c10b0960507a0340c204040c00da0301e041c0314013408a2010003e010201b0641e402205001d205000094941661070191300d403541c0c00b96100f42d1301104000d031030608600e0b08884051969804950001c846401c0078030661041c4444ca5030584504800a50009000003c2910714480c0390080d0602038549002c0c030702000c03501c503023164001c1903529004190b542010b243c450201644e8026210030181044181446517009004540c0c0c034100311a040001216607a600060000c1c008540c1e07004840380c5010400b9096560154860131560 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 927941447 1250 927940197 927940207
    0x3c030408070b040317070c1e0305010e07050d121103070c09050f060303041418010e01030201110102130b0a0e0a060306092f09060c01060b0306121605010f0e0d0f110303 74
    0x241810300940e46a201c0300c00c1c4986c1d079400900e482480c0c602e80703900280d0b0394001d4100c444d00c0701032008034a0084901904c000e0288048403200b881d1181e200340126075001c2240000c91004c0780c00580501425015410103c42004488140c0c900c1c64222103400c41f502e1007020f105000c8062a400b50070b4010030b41d002c0100302030a003100083e8490007107000701188040c64400640d60340d507500c807a21200103514400a00c0d20b507190300100c1c43c88842408240d000c141610707a00d4225001c140700f00c965030b80e00340c0e2007428050300700304030b0754650b60228181c05e003003008071084a00350b6665480c54000624154800060312071501120304144c61150441100301550308000f0600300c1002460b008440201c45030f001e80da410007100203000c0340541124680b55601e09840417036800a0400210b0103840126040060f6090302c2825940d40c2d44002e42d651035003070a840041003030303501400f2007070360306031250070034816041c401c5002c01d07400c0303c1c40b4000b40c0c0c52400d24003201042c1b000c80c0001c210720360000c0c1c002c1c4d03284c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 927942697 1250 927941447 927941453
    0x9011407080319020724181101140708161514091213050d0303060e0c07050c0a0510080604060b0c010204051503091b04060312080702010c020d023c030408070b0403 72
    0x4030b082c9004561040c442040ca081c06e40c007103030344401d0301d4943c21840440781c010542400010303011110b4006021458422140425149034806d99a031a6440001c59240440c0d014144400108901f002c5038800b03000840d42025090900030100b50301d4a00e2080400c0303250617103c0500c1e000b00c01d55030f01d401d018200143c8400c02e00b005a11804ea03103040d203440c0480c414a2504900404071a4446501d15000109200120307078400028050b980c0504211003004c480c600c20040070440ca0310466500c405031400600c40103009800c1c242e80400001c1c4005555a80d68101c03e243e41d000801542c104d940c0007074107101c280790202c5080b070300001820f202421450b0201000d130761800c00c074000601e500c401441509469480d604040080d40c3e0058400900c0c401585010b0100d041c02c2d2004005542000c0241d00664800a4061762441256000f0510860015045401c40c03400787d200c0c0c01500c6403849800c0400c4010b03c02e561a850004c0015592a490710141c581821040d801a110740f1004000030004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 927943947 1250 927942697 927942713
    0x11401090902030c0c0d0c0510020f27131409060708130f0c0b0d1811060a03062105150c03160215070305061306030803040305090114070803190207 65
    0x241d03008a240140e50303455218085440d4043c42c20038401511a10244c003d4884c0e1000b00f1300c101902c10000c4840f9500202c107400c0aa0180000d9014190000c2c05542c0c100c82e502e6400e20040200400c842d0701250b9030801144540180c4c0c803800c4c000a84a0413280300004aa00e005a03110000c60b01030290b40c181103000400c4140082d0002c4407901c07590341501c0602c1644201d10400d00d43c0b01048110441d559580da00442e088240c031106030300e02c7d0031040c907000d1070b018501d903440e268000c4094034104515020000c00346c00c15444031003055520940841c440021000d0f010300c0c1c441205008031046000d01d07200340f03012481041801440e01130300c03e01060107540d4042e00d801a40070f0500b01442c0c000c0131000c03480d01c0411000501c0400302ca8041c03000303c98255200c58007480e020340d140725007083c004240c00282e480c503200c02006503800f00005400329201c2d9014040000051504481308441505007062641007040182c404007400400d100705142e125a1107414541180400e40c20a8415250300f58 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 927945197 1250 927943947 927943949
    0x9050910062001090b0703180b0615040e0903120702151303210f0e0a05120702040b0901090506030c010c031e0203131d070513170a060906020a020601140109 69
    0x20300c41e0002ca81000c02824140c07180ea0485142d00070030807030707840c0d041a02e01c40e401034800c1c00201c1d00e84050691009034510402072140e8101303e07115103903140e075070600bc030390044c84e040d40105100a00011910800040c0254042c00d4908021921480100c12031010008081d00304001c1d5448016103501c080007448000e40d00000407200040e000348181416144102c000301012042c0c005001c5940302c885250b48280c00c0140d80c40c07020001e004202c0101c80e41c030700c0c0c0700e400500b6079404040c20f80000490840100000f91020308045085174000d008100030b030300c0c20303000803200944540401c0035508082001c80f0941000340380c28514688281c4000d0b00c0b0107000410315283d4603800180006103030003001207400d1002c10542041c21f2594411103418040c88000c040b404d06960390000c03400c0c551141041e205030714000ca8004100500e0b1416140e401000d4030503002c00c6001c0d04900d503001c51070307a00c10780085a026800c0036a5a52001c04024101030050300314407110b9444032450301e1282d0703010302c15034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 927946447 1250 927945197 927945209
    0x709020309120703030c141806030a0e0312040620040b0a23090406090608060106051c0203010e09010509010911040c0c0c08013c0f0b041b09050910 65
    0x16a40d840e41a031650414020100108603044000f03410f100b00f5516900009645445555415045c100796104c41c62601c140d0f40084441301600c007a03042d052034031100175500071250781d034006101c0540c1500d03541103030880c44803196818000c00130442482410b0042642510b4484801408201c0708080306c00e003801540103d0b44a040081528001140038610200c0920209000b500440c03402c001e03e031525610501f80c95000e207061480000700040d241c041d140a6841040c00b500c2542e003068000c40d0700c1c0d00040054242c469a4100c0104681e0851000f94060700f20b90002030b2441c50b01282c009d0a49501801e00d03005a8504100380e0007203441ca2590800b440c104450114030b0b041c0350702c4119801222503002401403440b1000021365081c055200c504c0c03042403081c5c0c158440400d800c0240e00d4101060460b10f0040e961040042e00307280d40c2d840141404904040041e458060a01150840340d0f01092102089500314140e0500340c0c0154070701c0c006050440d922441403402102c81c81c42d0164034440c803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 927947697 1250 927946447 927946451
    0x26010e0c01112a040e0109060b040b030a0c030b0c07080408030403060b06270d14010e1501210c1203021e033903030708040b1510080c04090c020c0405180709 69
    0x80026071349641104000005540c003d0014001030708143d0010015600e0f280d02c104e00d481440301d00707410046004000650484c4c1c020401324516120345031083d10040031054240010130580001400c0d0401610144c6140c0c00110344a909500d01030f012101c80c0c3d40120700c5042d092203c040342404018034629000918001c144004004030049408900d07403003402840110300d069405000181540304001c00044241103c2c1304039000a891001c0003000c2c0520040460300509001c41480c058114410641c4a0302d5803101c5281d5407906184a051051710480040c2c02100e004100401804440390b500101000078624010180c07012000710140c85c101400000d4600040a0070007402040003002403110500390b955a20b00a44014413408040300c1c1218203520f080c001c2034055415210402c901d09015100021503039812409a4414500505c58041050200804285081580075403c040c0e04142c000b003d00c1e540e100100700582e24002c0200c1d001d0064400d007642c81c0a00094114100d40780e034200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 927948947 1250 927947697 927947773
    0x170f0d1e05041e15061d01091401120f0605090309010807080c09120a02041e0515010f0507050c10030e060603060705040302190b0f031509060a26010e0c0111 69
    0x100000104c1c091300000e4601070000455001038010711502c80244200f00b201607886407400802c440c0804822107508008030010300070040949095118980210a2464440c80380d903507800c1503440466070006039800104640344254ac01410203074205140d4200760000785000035440145003e98040c8a100d440c0003511404940000d00c4000445500036105004011602d040307220001d110003100d0300c81e0751400000402d1103210b48189550248160b4406c1c58042c0c510104032086d411030001503465014000c2034102c15552184140120165900e000c65a110102250303410450b00a00e598040c0d041581041a600d40c810101d07400e41741d0480c0c85400711803000050885003030923a005038544050000d003184d504002c12001c0c41c030a480284013542d4802da180103100b0b40d40c0058803010f0b0407a042c45024480080c0c41d82c28000f80a4041c07041030100c600001c4050b0949200d407500002d15000224070028650b406511030b40b603202c881c002845c050b1051449200550800e044100c0518034200c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 927950197 1250 927948947 927948953
    0x30615090303081b0415020303040c09020301050a0b25060f06090b06032a070f0b0604020a08150409050a1101020d0906081605160c0602100b0d170f0d1e05041e 70
    0x40c1c4024112586e5101041160003802175500e520a490544641704250f6001441c182c0c103008487c1030b11805044149001e00d0301c7d00c0e405164001040c0400041c0500252080300e481c03590015620394003030280030400e6500c410b09642180c0440d00f003006440d04207800072a0306e4542c1000ca9400408000301c1081d20404440c0d1069082e000428960106100068000500c1545c8285110341c6000b410450f00c181c55190422040b4030507a480d80d03011400641c00622503c02d142211001104041c00228422915030b803901d050020900049801a80c40440407000f941c0c1046241d0103030185007040c0c1402c1d42099000b80c00100d0040c61010f0018a011a0440c01445101600d1050032071a9500f40790315580d14064010148500502c401840341503480b91600d000b5000c0c0403d200000361822404074aa500ea450021b0b00c40f01d00341540c5403080101310a520750700c10003803c9007420303047e0000b0046108021145c001d505003001000003410242070202240050348540100201c0600080c0eaa00841c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 927951447 1250 927950197 927950251
    0x4150e0306090d090611191110030906050114091f171014161107050d081c1118031c030605040b0a060504030b0a0e0d03061509030308 59
    0x100000d030540246800e0020000d0001560509500700340c462841e903507181e01040350506409898914198050b200210f10b92880c2800d401503540121414000c1101d0300011030319507a5000d240000081e40c804216042c84440d200b840c0c0904465020a6a030b000e040b0000b40131090080c2c46c020082510708a9590b9640d11005000010174030044021003440a140740c1e40c0d00c0d11982011114005c1c00e141441d100500b1084280c0e101c1c00701c503429400c0803100700b00120b232112002000c1c11900e1188143c042200c0e81e59400501400d0f11882c0559503070500001d130504035080c065009014141460482d00f100e9070a0016600254142c0f04000001400400001e01e042d0944070310120035449040c02c10a5507505400400650300300f540c044c03007018045424429403100502c601000030703000b80030520001e024a4040348d0042d94503040403414014201207a41041280041c0c0c1c0c0100e6600e0500700444580c070480080c000021341803a91a283c41e44e02c024100031001400851056440f40c201d1030303c05040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 927952697 1250 927951447 927951467
    0xf020a022503060f140f010305070603110c030c0304031202031206040b011b03030b010912080307050a02030d060906051008060a210503070615080604080a031a0622120203030415 78
    0x450010302040302000322000040010880c405500ca0b02440011958601b48a0351812242d001000342042c514081049004180301040c034801d000c020001c500001800304080c0c140302d5250409075a48a10303524121400711030310303c282d60542d00103001000c040300d040c43c3d0803079001c1010ba4022492006450041360545112121400c40d10040c071207040c103140e40b41e4810f403030b082c034280c8841f011207803140480400304544190052845a00300b0020b211640b09002815811800c0c1c01100d04020b8905087d5090b21402d400c4540010394a00c4200b250340b50080a86800041a0501d0a10b600700300c004100c002d0b2007401980650845000300c4000c00070008560a05250404c1c1179030344580c060324000c00078003503140f960031000100300000300e00c2800c00700b4418007847c1e2040c0702d94a8030701c00b080164050880742c0c4424103100c44151034040503407030b01c1d001414010302090720080d0900e0400c4c43c000c1718014036080f00f01c107445030518007001a18000125070645603004410703641c44082d220210345a03400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 927953947 1250 927952697 927952703
    0x1b082104060501080d230d1103010803130b03010b0d0905030d06140907030506030d0e030a2012010b0a0905100f270b01210609110c010f020a022503 65
    0x41508010501003070341d10550580302400151148004140070403950880081442140c19000501e41c0300100c4000d4010902581d48090104900001d407100c0d6000303410990141d0066000080c6500d00b017001481c2d2500900031284503a8190350406015052501454403606ca2a50f42d6101000502c4410000d85640e6036160705c0c14090b40b41c54510388030159204d0341d038140c0548a1040425001e901a0040500c508405001450b4034491a60102c07804c0106203080741d0140503403074510011943e04441f02c1294841c00c403200e840b003101482402040e45441c94840d9a50349801100105aa03840309040203c030301c10000440d680d01e51955010b004612503120ba4582c030044180020200000c2c1703a83d2880742d69000714050b8418803c0218400c3c2d841200c04140000c0021003040041120316846441e40d20a060000950944902d101c4080b00c0c0c1260300c5400007180820020702c0302409004a82841c080382c3c00a6041c40c1110001075510b5820054441c0c02c004054448840011076910f03072001190 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 927955197 1250 927953947 927954007
    0x9090c030c0806030d05070210051903090515040c14010302090604120215070c1520060115110309041d2a0f031b060d1a101b08 56
    0x1882080940180740c41d40c040408160060005411440c000c592240d0f0700000792200c07860b100c119030070489034a98080f5100184482441010381003114552503040c8601c0036240081e003039070103050980ca02801b00300c8041c024540ea4040000140140a2001c111220700c80321104016042c40141c01034050720520310b401040206000a48170584d904400401d4000e40348103000340c04070801a13013184600d1401804401d0030213001c000146403840d08100c540b81d24a4400d18540145140c003134204407400d080d501981c04070005100040820301c03183c80030000d83c20045540d500034080b15403030340030700036240d40301c3d6644e1800345001c070701b910440d01c41507640b1409856550f038020448454940d00c0300c0620010400117000e40200342030040d48643c400d580140101071040b0313072403a0b04003051b254003ea15006801402030a805a1041c000d00910f0f0302e600c51861407403081340c41071041140c6c3e41c1e4880010041c140c3c50341c01e076100f84142ca20100344d42221040d55901c441c1c5600d42900050469003010f217503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 927956447 1250 927955197 927955211
    0xb030c04021b031201030c0506040b0901050306040603020d051507020307031b050708030a020102030106080a112208010e0a050607021504030c03050f031f05060a17090a0b091b0904170a0909 83
    0x21038521300e5170b058074484c020b4a00842c0c2ca070401c1c852907014174003d0119604003044641425030140020390ba00010051012800d19129404598400c4401e4011102a030041e002802102d14089070f059000c00a071006600f0100541c0b0010b141188408284c2b0428040700d81d81e00038440240400005071242c0c50071250346014004009000794402d20411000520031030100b100d2108902039a42105a030480050a00e03c0c03545000c16030580d641101e000c1842c080f07000244400c2c0170302544039200c1400004d82070015603410083c1c00c0c03140060903241150804810f4802407000100031640058141c17504074500d126601d81a10710740b0078800390031100007000c4204805c148680c030214403158407403032041c0e84d003039910828400303d40524489840441c00d10300386030400100d40c0c2c02d90b5038413809480c00c441c8000f0131611130b41e81d01032094400e81800e8000f41401100e10900f112540110b1900b0fa92800c100d20342600c89029000e002034039400b903100009107076542144514107640103419004020003901c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 927957697 1250 927956447 927956467
    0xa1e171e0f0a050907050d080c07081014180a081804150305192a0308030108032a0c011116080303072c0402090a0902070606180b030c04021b03 63
    0x1407000c40710980b00b181050300203105202c004c200d04045450242061000020366500c2c01445d82084145042511541301c0c0001d246504105c0c0900c410040d00000400b0402e0101056443d070009140205807680310742c0c642d00b03901c0d00103a544156038000d221a40c0780d00aa001082d10014188416948541014803055500e0b4618002034112480713503007110150703003904441038ac11041070400501a4209079043e4104e0070410851034000003c42c0340c0303c07940f00380c807641d54a94642007a080b031700c050f07071001c14095600c1e00f0403102900e6404140d80658032629014004d01e683d0811f003001c01d81049002d44c180f6060300c01c20004601c072180c9005d8103014075174954041991381e8104a440c0d00000740d40510f502d4803420340411140a1225104450045a003c41705120282d44100e503d00d8114810690004152400384043e000c801d204000128040e440c00c006c0c2002d5000c1c940e41c44400c1464843c0001c01554000348400004e03106442c096156200c4891704400e22003031441c1d54119000c0003c4502c0701d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 927958947 1250 927957697 927957721
    0x906090501050d0c230d060b03120705071802120f04110a0f052e080106020c06180d050c0d38070507150c050a1e171e 52
    0xaa8100510800c4103a9890081010140e0001000303404a4440c0320180100009681005d5218018520005001c24544c010407032504000b40d0075502103996400e600014a028020200d00307004d8010103034103101850310350340d46400b403070702c14038140e500203140e02140c02ea040c1c0c06541c40c0759601d141d40c1d41986455000c01c01c0c071800855080303446e080e12a16071007280c41c00b0306407a02900c601030a088030060a2805000150030305044210004c29011481c00c40903a030a8454000144d6031b030786100555240650280c076006400b642144130f00001d00a410380040c205041d885c403180110b0341240200090f080060401c0d60642c0c00c960001541c00c41d00c030500414803445080c6c410138400390540c503c0c0001c01044c000c28a41540086255031402280e101d612a1000d042141d00545074a680290030203100b400302d410903500c4001269000c1188604507400010032a42102c0e0a41c090400c508681001070114146a10364074410b804400404d40d03503031000b0803083c0311030003410006129082030380d00c01903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 927960197 1250 927958947 927958949
    0xe06130308310b04052505090a0e010c230307080c1c02040f030c0806040b01061d1c060f1116051c051b010207150c0c02030709020406020705030601150e06040f0906 72
    0x403584542030601b800100303008a000000c211120f840300304c0508000030400145405401114196118442c0313031907000c2e081c8074107503d016561301c4540c010603010b0388000100800000c0c0c0b90340c5c40c209001304040650081096540716545131109a03603480880d500260922011161150441c40031801082040c08040d4000130b4030b00a90719010500c0c0d8403050301d50f032110308980042c0343c07003000c1004004ca180903043d0926801c002d4078100000c4850003010441d6140c0000140802c4500b000703a50003440070522800100c0504801d09008940303200904858601c24503200c0f1244000070140c51050010034040c403002c1e50341142800e01d5031542c44d60018559000036a0b241c0d50600489000000d0000c14401c9402d403d50000c10f0400e81d4010071f0340c0314010b0054516000900004071003440040e0f8080c80000041c003016140140c0311824000000c0c600a5141c100c01d0103a8004001400581002c00600e508140300b49018150180e414000c91134a000b10390200243d1505100c0c0030072a0082c40d04444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 927961447 1250 927960197 927960203
    0x50d14010e010608011d15100306050703090201080c12150a0b0c0c0a05030d090303120e0d110c010f0806150417012003060d1101020f0a060e06130308310b04 69
    0x44035410090b040030a00301d100000000d0694040880d642c8903000d54002c0a0b803001623130382080c00070b03a52621000240e90003140c602c0e000a507a01c403003e0441da00302c1c20482c3c0200c48401441d04200b6401c1000701480406403085032a1307110651a5202e1ba41c607181400094454000400d442d803108110b2141c0d95405460202c1c03089080403030209840c240010702c47c803110038507070341c54410515540701078543c040c00e07043c01c2040c0c80d00c5080c1d10b131a1000403c0030302e485100c01d668805a00100b80101420701d111444402e0400c0700380b045141489078401040c0340c2040007185c22500d1414903000203a0103100c1c07680068030080003c40c004501ca1030661010f1500141c8400f26030001c02c0d4500ba00307256100c00c81e103156001302808000c9001c9030100540404144040c0100e90081c104a40f84074078040421904448603500da511481c90f0800c00c0c4030040d08403244407120704580d241a07401a1001c80014032210a806491406004080103440e4002c0c0c03002440c5204491003401d81400c2c092203d0444060b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 927962697 1250 927961447 927961451
    0x60311030717030d0203061801080c01140306060904150e100305010501060207180209150301290a0c0305160b04030306033509060f1201051c0c050d14010e01060801 72
    0xb29444031200341c21028502d07402562030420900b0b2031100079000606150b80188105009948510380485007034041d2840304024a6404910400140558251104400182820705c140301d0f460f12030400b034070746e0400c04807004109000c0505140d11050010340c8014001041c1e501807215140c01d205200003582d014030000d0102c2da880745c90580c0c2c4c3c0d00040c4140140403034011595110440140c1c007074030820000900141d0003000701b0541c030046400a0f000054100040540c040d0103640c000240c448003031601350490305217800002d000c0c1032000511070140078050300146100024080e990480041a441041c2c24154245414000c0c020056800102e403001d0031f0b06000a481c8901c04d8035202c1001d0100d4a0b0498500401c0700c90490f0b802080e140382d00980d003404002c1500003ca0040c1031910700c0780065400642c0341000304400d00c0041030001110003000080c5002003440050000e00352407082c1d41c0100841d9080c80c241508500b4411201511b510b422401b4500c00700c190801411207043c1002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 927963947 1250 927962697 927962699
    0x90f09060c130b0d1e0b0307080a1a09030d090f030e0d1104150509040f06060501080c030a02090111030d09050f1f0507030b18010911070f03120f0603110307 69
    0x2945028030030070351042c07a041c0c1580030401801c00054020303c0c0c4412211000300b00d030300365000c0a801003030b43d60000d5518641c680403031074028282049150000c1c22000c000b80388030f01842c0c80b08445080c10003c0d80110385000c1000450000b0204100e49002c0811502044410301902381841c400d40e8904007100002c0749100300381641c6c03420b40601d0210711303001802c00040358501e03010440103101c4140042403100c80e1000000d001ea0b180d001140c0310398013980019407014000d10f4108100c41c219008a41031008030b005118403500c0e11402ea81e40310801601c0141d5403100c406c010703502c0c0d618036a590f0660744800a0b1a607195071160b0072a03110180300707008031031000142c062900d0f200c1d1103440032801c000c1500d410296228042e6004642c00040300d080c0055000c041c1c0010864000b68880d403150494040c0004202410240c410850304074220039800c0c0c1002d4160f134940400d217543d650f015080000f440741045c240c50300da42c000e42c1e03580001601008030540e64a480700350481c40e22a8035100b4052160 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 927965197 1250 927963947 927963961
    0x4120c050a0906030503030a0506010e0414040203061f0611011103011707060318060f060b070803010f15050405040207050c0415140409021c03020a0f03170a0b060f18090f0906 77
    0x343c00c09580c1e103d0055415030780c17640320400080c480100054104030300c21284090301e455601c500800415248502c2030b00e03280c2401410b03c6c0550180c01246410806801d9010700c1c00b5407900541555128a0030700d8000640368070203405040841031505102c800000002941c03800d014001074062003c0701078a010079901ea206030b080f40c02c054070200303000030003d0400000981c603901502e0103558070240000c0c03441d1600b00480181e0080001225030b00400001400740e004080130000c01031424007044c0c540b0281c981c0008100b805948580d078000c0750007060400400c2014440c290120038041d108101c43c21046140c1d5000302c81034895407410100d003114a010f00c2c1028041e5a600359006010340d0405aa245403085001031028030503000c5014410700e0800160a021010b90000e0003a80d0b400c0350350b04402c03500010903401410715004186812421950b60312240152070004000450369030311401c0680701e0003070b940e40b15801c103540041d0130b10800c488122203820b2240251566012911581d8400e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 927966447 1250 927965197 927965201
    0x4091a10080c0405060c0102070c080a030815030307060504050c10020d0e030c0603060904020d0f29190e031e0a032306060703211e060e01050d020604120c050a09 71
    0x610320840000d0b08200a010b9410948003c1c49481c150034001443d0490356110040c4849844d0000c1c4500d4104020100a06a1210145412824205602c1520185500000d65030300c0340b0b00f40201000d0302c0d18001021300c2000c2c8520808848050a040d00d02130f02460003c1d01d400d0340b6507101e00865400c907114100d0b4107000949054500e0058100c52858503428200440c404008208a034000b244101c42000100a54946154140f00350604c1480000104a14a203202c054500030078114940701000224052021803140d41503e0040c009581319459081904520560b0036612150307440400e0030700c50b146814004e00009610b9641040340c500c1811028040c4590072200602040640001c9500c23841c2a4005280040c841e090110507003c800d4034001a010f05503039008006969a42d148624208071020040f5044c039210f010400700d400d1590504507a00103000c1c0b64000e140c1c14809404548880c1c08903405810450801038015020b8603001080510f02d0240e14024050720034000744500c094 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 927967697 1250 927966447 927966451
    0x50c010f0f08040f0f0804030b040605010506070f120908120714030f1c2a09050411070314280e01020a03080114010905060412140c0109051504091a1008 67
    0x40e0380b400b285031566111000410b0b0550740c1510201c0c6a00a9038001566010042c401540300311400c071a60b10723060070701e04104e0340160711090240d4402c0000000042c0e00948100380c0c254008076a1203070f90307504401121056603541001c81c981c40b820103102440380c855000f520b26140324501c94420395650080c41900c0380201940000e0b00302c01882540015140e42620102d04100150001501b040240056020410051601103042c01c00e0301d0415613554400d200f5406000c01741d0701401074000501e81110710b80314181300501004141203841c2d0b0109a890200c815100b400680c42086034080e40c4c052426034005e610110114948070310b401143d5001050b0140d9542c2c00d51038030f002036840c0440314400741c01e1949c00507040100784400421690f0300c9502400182000c01020180e0f0880c601d04514406040c045c0a5660350007100e21314810b80e130103140c2c042a590145c401b010728040310641e1030614001d6400c150201400d008605801d840034640701c00081501300c0314179810341d20124040d2034125007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 927968947 1250 927967697 927967727
    0x209040506101b14010227040c080c18030a1a090f0703060216140f01060506070b0c210f100e0411010302091914090c03160804060902030a050c010f 65
    0x4500311086021041c0d19030009080c09200349460086580132001d089a0004081208400d94920802d00c5d1a0f09042d4050010b90160303410002400c1240000d07200e09401000c0340c0d0012000207561818840e641c80e130441e00040941100c12003003091402c51344210f62940219101c030214000607001000010390340415084c0364001d072821034150b07152400a0b503ca004640c0c00d0710b15180326080000c1e190354002200101301000751528405044481d402d503103071984a1489070605006080102e90084907207074200d02e8807085070382e0f00c1c10003500da086188500084101c0d0150044100884c0710000303d24075121780d4403c1140d6104e9903c034a00c454505205032006890001d01b18140407a0b540a0b80c020814410010400c0d40c030139149295401040b1b009070800200081e003003022091030f0034081c003400c0c0c100c03504400e01419440d0070842840309900c1c002c403da00300b2100e000481d06100080e4051100c4a4000d01621522503031070174130786d59442100c1c007194001682035100d0001540f1071042641c2c1070038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 927970197 1250 927968947 927968957
    0xf0d0e0a120305100b030f01090605041a090601020a020603130c300302030c0313141815130f0b03120405030a0803042a060e0303030115210c0201020904050610 70
    0x10321000120b00500b002422090b201504101c046034014202000e14490320002c6c0c41c4401d950706290303225003070303441c9940070502036402c11704030327200d41492002c070b140e035092007507854107034a03507500c80100e1404140a0000e90482c200005000b040214584581c4080380640f0b02194850369920303020742d4801840e500c6103640c82c041d042c4440705c1c070800c1c201000002c0c0684110390070100c080103000c2c115400008400c1d0f024a44900030484d91185513550f44803c08129640003110880c44000031928000422a0303140425a1000002d6640c03031400c1c0c1c1c0700c80b81108108010b0308046d640000c0007803440c280001c1c8a071190352401000e980403001100c040d1480540030b011301041ca070f0f032070001c5500b001d001214560782400c82c40d05c0202c5c405641c0c40c589100740349803004041c50044050003000c03802c15060b0184d0400c00c014000c100d075104501c00704102c207142485480004ca6039002c40320312258018403007142400e080030103041d0305401400701c2c5030341140c080203180c0b5550b00300608080c05841d2f00000c61 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 927971447 1250 927970197 927970223
    0x6031e0e0a06051303140c0f060702070801050c0403080a080a061d09011505131107021807090806010303090b16061a040e0307050c0103020f040815011502010c1e0e060f0d0e0a 77
    0x362a20140040c03070384100c1248c00c1075055240e65428500115581030041c0d1281c030042000c640c0034000c5540002c051481c05141a045858900951040450b15014400450b010440d920100c0d8058402403243e03c2010040c4048100c2500a20070305440e0400d1035070070603d003c0b42c012150615101115130041900500441c3c42854201030403180d0b0b10641e0b903040912645002da19004116420900c00e001080143c1c80e0130200070741101c405410401a95200f200140700194000d4401025106512140d40c0c483c07009480450203600c0c0c0540042215061101d152001020701500030300d44034003280c003408a50b119003522aa00e014000014180e075000b804418a00c2d4042c0d8010680c241ca05100240b40513260242c1a140202404a41c210850140d0040000c0010324460b41105010b0388001d100841e1488402007045c900300c90310003c1034803089400c160460050504e1040142c4c00f5088589400c1010340300d131890b07000f0141c040c01c0c250400c180e8402d52000455550015584104001c1d618 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 927972697 1250 927971447 927971477
    0x22115070f1e0e1903060513030504062a0515010603140a0507180806150105270a180504050d0c0c06051c020c03220b0406031e0e0a06051303 62
    0x7080b26030b00c142401a4090303048296151140d000007000c80240407103180e135195107440c5044031002400005260a420501303c0001e03880b50071101261118a004021f04008442c0002481003081a601c40030405a084204000010030340321076000c1c008940600c01e0fa40c40320f041c0d0a546444202004585100000419a00b0345a01503030700441d407071a186001000c0700050b0440400903400400003644000100710b90001090061040d030031083c41d01e10305000340e00025103460060070901108840204026000c561504641c000040001c0b003000508010003208a0f001020161015102c0d4060702400c02c4c041802603040e0130505901c004003001c014034110044502d130300140e045010030070b07004905116804046c00a4240e6001c0c55018513a6901138500610020140342d0b141c11141171031000403c0005072040030350b0300b216114100490300419021486039151045540401064a4662101c0740760b240001c84400c140d1182904006603103800c0c86610103514150b10060019021116403040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 927973947 1250 927972697 927972737
    0x141c0e0c10050301050121200304050601060903120c1a0709060e03030c0304050603130507060302040512210c010b09040f140606090a090305072f0a0b070f022115070f 73
    0x806807c4e5000042d44819800790007c55001000d18119410700120a0006000c001d000300c0340144018100a0318081c42e507a60320061000c02c14484050280034040720050000080e905c030041c1c0a0b405050101c3e24081e40058100910f0b4054900003900c03013100100117044c0041115480c01008006501382454541000f40b10340c001811800852040410000021020400a0050701d004d0b28056150741c20070007030100c80c42a84004042d59841034047c000b020042100e01d91008001c0720410380d84000040c01103014210194000782c001d0007000804c014000e450584400c018858640c0100c03100c1740c00c1c00b887e543d200035242c01d54820844030115850190a901900020384241000f0341084000d84401000b080f185098600281500a0900b41403044611900d050340c000c840111690f410110020164025200010001d8540700041030075551950700c3c144c02250050700195103650a4031030941c90300327168011400f07040c50980100d00e8090141d1800300d0640c0e00e6540b00c40880d80e0011078448 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 927975197 1250 927973947 927973997
    0xf0518010905041b0e011809030c06020906040b04090e010507231b030a031a0d080909150907021c0314060108040602040b040323030307141c0e0c100503010501 70
    0x30781010882c1d41c09203071940c186030460050014541c01c030f81c1d56150106184203d0b1203161f841240900d484d041e04c001076003020b9002c82082d0030420045e00c840d240c40120768140300d0b980080e656600c001c40e000442c005580c10005a4130700c024000c0c8a5512201825280491500c0d00d8400b8402c40800e404017411904000d004403100c2001100844003014051908660202a1410009860b03020000403803501c04500760722a88203851004a200d115190325006d80a014403081c0300701041804070300c1034010703c0d14024022900404018441c1000d200c0a541e80c0d20b28000b11141499111200544034000d100d0450150120000c601480d41d400004440d01c03180280300301c80255007480003207050407841c0040c1025602c5142486000b011581021009001900c48001c40398802c108015a01c1e5104001441c1c60381e6044c1507545410703152030007400180101002c0c8210515001c445111400002200da0041030199404460141d20800407281d902c1f00b40107250105a003845c800310b0100203850042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 927976447 1250 927975197 927975203
    0x161505010812070305091c020f060c0c01050304060207210e04050118020904060807260102041208162f03012c0a021306151d040f020715060f051801090504 68
    0x244c41d01c0301b403000255079a8007100c8074440b2480031801c0c10b070850500801c0591007110844810f401d050451380c220f5507504046150307604105000c0003060803c429601a1442c10f540312865007c8003030444030504290a0b082c01e11800104490030118141c145840f941341a24402d0365405041092502444003030344c00f0311800c81c7c00c240e91704e0303000420342c2c800d10904018200c6070b540060f11290400382c4009114020300c00387c0b050791040004201141c00d0380a0340401c0389c1d00080454407402c00010051031a01400d80240c07421b680c1481c1d4a641000005d05641e4034181800b00c03452911414050500301c4030501c44002a9480080040c042d00c0c1d10403004003800e006400403258480d070345030302007040307080c2d01c2042d2007061751034082c00c0c400c01c0340c440b00014005c007141c6400b20418004c13282008200e46443c4030203000d1990385002021081707090301296050394000210b080c0300c0443c001010014202c0344152500008401d0006c5003a152400130112003110f0040c9400c2184d003442c01c80001490050000c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 927977697 1250 927976447 927976457
    0x18020603060d051b041406090103120203130e18010209090403030b060f0f0a0806150d020a0909020a09170c0901090b01020106050d030309120e01050304030e0f061615050108120703 79
    0xb00340000d004201c81001000c29001c02e8507000101d00902c01900d00e05400001c0350104407013000490b44914002070f044a0f001101007000c0b41d0344000c144d00f18030400c058486c14050303503000450110384072070240340100c070314440c039002d81260203001608038010700110540c0403058601080209100c0d8025009000d4020455460104070254900b0a17520428881c00080008034200352019040405c044d400710081d190010144604108100913100b400b203a5820706501041c0c55500c00e03c25600b18010300094001150340d01c0d008031001c3c001080500c0b0f05043c80005204407442900301240d518482c160107480854142d0801100c1b6010340011110103046650720440041d45546207070b40001c6840c066100020a03809604240e00d80c0d00d0300714808002c1c05000011800187d81c46011654000d400d842e040c909002004001019840362030310259020901007260361854014404a5444070710481107034004601a0b00c800c4e0039101c003485a825240c114082c118004010507004000d81c51013031a007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 927978947 1250 927977697 927977719
    0x120a06170106050a0905010b0307140d0501170601060f021e010b03031315020a0b070804050703120315050a06140715050f0109292e020607080a1802060306 68
    0x4116802000051064032980d15500100560304013100d01d1070241c02c402c0001d010300e60508500034013520026200d801000804180900c60340742000655400018006080c040b6580d00da0302c2c1a42240001020078050041400004606010705010342c00c1102c2600a032000c0c0412940342c0c8405500d034003291281d5500c806a501555405100819406880305036150290f41420910110303010900059020b641c0030403264008a2450820309502c06081c1c503014025507114a8050b013441d6082d8802003121114540803400700e40c0540000101c00c15010880440540d940104800c441ca103110352800f003200c0b481c0c0b91151031004e10003443c110b07002c0d6950101866190008004540341140d842c070b00b180c1c01c5001441401c4180c0103024542da02c1e07403100003440c0120540b070403450190070541403040080703414000054500204681185440e003501c031f00039902d01e440180d21200c080724108005006400001c1580713030b10b4440ca82403001300444103801d0300010781c00c2c040c2c2039102500c07041e481001501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 927980197 1250 927978947 927978959
    0x6060905010920041202060306030f010606020f280201031d07090213080307020916120f050a15080303360f1e0a0605042904030e15120a06 61
    0x610707008000590703000508290300010841c0707081e102440b04641080402c01001281e0003842c040720f115070100d69465a07501c0320000a49044100c2c0a000903550806a000601903000706200d80c41034030810955492500211405031034102254070180030b8000d038000c0d0405944264401c0d0f42c039011044c4907003240071041d58498500b0600354000302c405030700040c120007480c0c130f0088164000c0401342c0c000c5080c00d00b0b0794000350142200401e012800b810140c41260414441c102600e5850700855040154071036201e07028001d00401c4400b05071444c01c2461010702c0c9801c0078010012942050041e60464541c00704440c1d00c480302c0c40912170f660310350210007049040d01a01d080700c0403610744000d0000404030307580c081c1403052500d6668000c00e0080d000d00c030f11a10101c0c0700c0d9070b01544140005642d6a442c90a940c09458180078101100240c80050348100d11011120b8002c0d40030b9115002445562002c00c003e0401c4a84220090740b4180082a002021520043d40100c0300400c0070610a071900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 927981447 1250 927980197 927980201
    0xa03050304180e1c02120a020d1404211b03020319110a0801020a0809010c090515120c04060e37080615040e0f120a1103031e15011b060609 61
    0x98421503851a41d20240d20b03801d80c04003c5444c0c0003403840311681c28640c7d240c0c4003035100c40c4c4074100d0400340441d00e1035100c1aa81030000302c801505d4051154446c0300050f4401c400c040c43c040da0100c41600000c01410b00540740280d680f000c0701d038024000c0c0030344100c0d0039000c0b489448600084801c0010805c5c03400c0c4669414250f400941000400181c59034a6240010320203003000c1c01e02075580c0d14000d00514640da0021a030b0b0305890041c0c8101903802800701410a091003080022201d40d0b016105010505500c44001e0044510a5540105071600182004248003948015a85080c02558441041c084a14a500c001c00180000403151039032030b0005818020702b03c0d60050b200032004091141e0785418801c130321a903010702c80180f094a5410942607603406d148003682090410114200d10014070520301104112200e0060b2600d9040c655142c1c0908180000119801480304000a0074039450703038616020400160740c0c1000703040018806081c45800d22a05443c69900c5020100e03841d0114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 927982697 1250 927981447 927981463
    0x6161b02040216060b04151512050103050717010b060403020d0302100e06100f0302062209140601090b0c0607050a030905011404120c0809040b1f0c02010e0a03050304180e 75
    0x43e03074080502a4500001128242865648187d00c0c01c0d22010030003c042c1c1800d0f043e0f0700406034000d03a407200c1800c05e4511459000c04403000340d0405002004103d408907400003210091000c80c0204150203640d0b600307072008400c002d03170000d6041c070041000d89052400d00d01c4860007401a0741b0088004a185416a900d04074030903400e0b4001d809001c649100740c80f02d080107110348201409858215400603144d4858000220007001c015410aa115028068044006c1612080c10000c0644900300301d100300f0021a4038601041d0920000a82d101d11103084805010302e05001c0c10b456902c8840a90320b41d00005048410160359246d4000050350034403501c4000c0800382c0403041c161500c0c3c60141c1c17034090b0b0300c81f0300010440d1582071480081c5000080d100d10704001c0310040381c0d03448284045400020508039201000d180c20134050500d64219040d100028002e030f03200c600e00400e0005010510041e0300c4024550b510800007003181141c0e112038000d41401c0b40078042001900c980800b4541540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 927983947 1250 927982697 927982717
    0x20111060f1005060909040809031507230702030a02040c021f020304110f0306070c0f0f030f110102130317040503030f030f1006080601050a090306052706161b020402 73
    0x80206100d030056114400c0b0340208821104145022801c0e0085802c002c000f802c0101074000216595035103580502120100040500220070035280219000300000c2d5070320b0000c50448414141e003203440c11f4850840d80c51640103801482048250b500b07000007091064001c1c011801011a2020400382c4404c04403015222503001684074201030401c00c44691080e0340c241e209104860038a2510344010643e80d81c4408182042011a2281c3c18003041030480d04000504003110314a40008140d08000b05d211201000c0d920041040d9428011074200d00c01e07102a004811420380741000015044040e4242c100c000d079171054107055640010918580003422a5004031308003104002042200444080d481001c151002c1122454a01e02070403845000c0d2800703041000000c1c04a40d41e90040011074019a44100308010524100d122286030040d02c0c121345a1035880703420703040001600010303032500a5400c859041e445150304030043e1101d800c010200302c1680c0c8402d82810250380ca030f101401d07040d80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 927985197 1250 927983947 927983971
    0x10906050a05090103033908030901050f010821090402071a0a0b09040f061d01061a0310120312021c05060d0c05040c020304050a03080c15070507060902011106 70
    0x400e280c2000002041500214042e40280d401003011980c40010034030740c20b12800c1c507400d201c8486103c103000e0544015195080c0f044503510b407420001040021482903150900030440c0e6114040c144561a1081c440d01e0f07007550001c170502c41d1540c0f040d10f030000400c4071502c2c0245005c1d000c1c2c021906a80025205075052803103a0007080012401000c070301c3d809001110100041480303880041c421005c0900003404848171001c906007000600e5024401c08824101400c01c5c2c4055060140e0180503240074500c003610700401c5254482400384140c90182c08212514290356060552190b494064514181d042100d00a403c98048420b07200404800c0e000d464100ba40910041d0440299003004d07021a008007141d09981003c10002009041540c104a4000c6080314000c10200e1460140c0d4000503409251250008100f00c018001052014030140a8483c0072076000c1c55058480c07000c4400c600801c2c0c080058400041c1c0c82d9001900451050400c0452100d81401c1c031b81c40c5c00403c455995144d6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 927986447 1250 927985197 927985199
    0xc0316170a05120f1204050d0f02030703171e240f0d150609020a230309071e03060e0328020a0b060d02120615030105060109151205010906 61
    0x11510380030030030406039000000c12000401e50707109559440c5400b01c0c41044540400d000703e94004540440f5901c0c4594650840300d401c280c105181c842c0d165010302404100c084c281000f070107001109030b5188036010b0700d0304030f00200348484013051f00c4c50041c5a00b41e40e0300c0201d01d82e40059543c0030001d00a02c00c48030055010b44480100c80300090032030070154815024030012181da41d40342d080c0c010510b5800741c61240106072041c0e60f0409402e264120b407113214000b08500d07040780d522840a600c04107050032401494030082a00303184910083e1004c035003641008a042c0404541d00c41e84240107501c00310f01c080d08594985801701124400346880d150394000095160f404003c50b6079100c0b40c00c0c810312804004c1d280303c0c41c02070340e01c1c0a4414001c01c01075101002801a5407600300f24513100e034001d0040d10060f030505e1125503c40c50100d41ca0030f040c00b501c0d042e50741c09040503c00c10344a140180c4921210ba8100060303c4985680c40c0e0b1003008000c0150080d403200000341c028140200310f24180032801c0d0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 927987697 1250 927986447 927986459
    0x20a090801050108060606030411040e100902240a080714030109060501080604050c0417030c010c0e0a0806010e0408030c07020d0302030301061101110a1b290601230a020c0316 77
    0x5218113038804030503030740180103100300342d520402265007166004034807518036450100030802824403410f5603c80c40c020307011701c0300b0b000d0303525044070842c90320840750f140c08140d04030031241090340ca084034003200c2002405a44c96071401115103941207a0300342490302c0b030040c5240d01c609041e802600052a095190381e4104699604031100325007102044405001c1c5103018124001e8600491162044540c44103803030110f100001e0040713071000303000c141c005e0040c503082240c0a0100310f40444214021f011050000448140105041c2c0c1681d1452280d00780540b250344a080301394002801d15424040d0412103200140e50f40554219201c2c481c1d005103440758501100904510498060311a4590501003400b985403050011244042c909082041c480d1a1000300181005010703080242440c20716a5451450744c0398034251910741d0f04030a001c0d14280d450030300440b07444e01d11100c202d60304055030b810030107034500d5600603050003010303841110700150007000003070f243c549030410210813001342c19014091 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 927988947 1250 927987697 927987701
    0x5041211010c3005010807080c03030f03010e0a0b060a080402150405090415020c030f0403120c113105040c05010c0308040308040614040614060a0f0b0705070801020a090801 76
    0xa22054030000704400801c1e02806002e4004054074000c500d0204069030803040c0400404040f4001541010000356844900b259a43e255074051440e5520074000b41e20020b280002c01c1790303d0b548a5807002411a41781c520485031000300940b0380c840791900c40b00102030700d07210000540003580035a0350300c102c030381040e00501441c904a060140e60710441084180202e49803054510740040d4000340b000040030305902550024054210744611070b000c00030303109050302d50a0028105503400b070311400401304080e01042d1001c00c54804010720040d4800e12840003441c0846001190401080750041d980200900c0b06440030901c82a101700641d03110240300c00e201c10744254501030402130030900e1208a0949000d4240000144018104400303000060308124040d0030108a108884d000004281090b10b0301c2c0d805850748002c0300000d40f003290002502031a06c44000d200b19000b1041a560b030a0604030609010383c040c48058450388259040000d03040f03000d10003410034002940c0c400044ca030038000540e003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 927990197 1250 927988947 927988967
    0x902130f060f080717030904060608070f08101202040902040e010207110a050607140703050d050c0628090618030306051306150c02031f0e0114090d051606050412 71
    0x5140c540b40382c410700c11181c00103040310560b17000d031048403039221402200354914842c0e41880e9400070b04042000070748640290a080c0502a0794031400c0c884400b1290880310070404907000d00760020106802c001c8002c5c84000c025109001070804a0050420f4004c6000c0e03a021006640e001c0e03500084482c180501c5c4500c1d0f55002204441041c1d60a00d0040003c24902a00b50044c0c082221188007504041003000350900a5074858152486841d800102904c03503040800c80d59142c1c0210300024016082c4101d01d01ca1420003100c071900c4941f00d2050200c01000204000c49140c0d03521055841116458924816041d00c240c1d400b143c400e05040c18802d14402c1242610009420300740d0601c4040f04100400181007036628085ca800d81e038500029141004444507030501c4a00c8c018000040c02258015a07564280c100003808441d1a148000e49804421201c1c01d1054002c1d00703180003030034814401806150407109031002202c045031990700c02c0703032404c0c0d4040f40e03074070000b0303580351180d50300700c58500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 927991447 1250 927990197 927990209
    0xf080d0b0a08070e070c0b0106020102040e06040209090c0a020304080f0106060207080f030a030f181b0812040e07030b0a0902040e07080402011d03010e1f14040c0e060102010902130f06 81
    0x940e03182c604441290380d000c00c1c0c0208580f14000400245040d8401c0c0813814605420101e1542c00d03507035911001e8000c5d4420b0003034201c04100000007030840d0405000300ca04000e00070300403071102e503180e560461482c1c0054070764400b18007080100007070848003085a00550030b030312000025018542000a0f16005155004141c035411a4481142419000c01a54009003480c2008a81c569854150031700030080c1c0401140c80310a50b4040350309110417100000c15400c6a26070040d40d403921030744103569501c1c00d0200c0701e0501c28200024450410915034294101d00c0304d050110709140400002503901003107402c07440c44581e0210302004420550ba9406401040d2802c10b41154241600020701c204507014100e50100c11042e4020171540b000d5020003e0000c441c0140c0d8801008048000212605040300141090524032185030814020f42c20b2406036620100d9554041d1071b10510381c00340c14008140354155545c2d040c0b01e40150711568020759849080250004021610307820303543c110360154000d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 927992697 1250 927991447 927991459
    0x30605120607090e06040f1404200303040b0906040e040f05070914060d050a201503060d26280918020f0d0e030c071413090503070f080d0b 61
    0x2112002da0084081d006071260031603c2c01c01685c0d61000718014102040b50b04041d40d183c4091780e83d100341030724043d501552080702594007010300501c0f40100e0b04200c81d80ea070b505030010401000032005240086c882400068000386c102695241c030b4440c00c010480c0c0030781e440941800303042c041010a0206801800740d171541002006204050504150f400400c40c5010303e074145c2c0c102c0c3c240302081100082969201203030204420441104059080740b40b8412801441b80c1c1740a603c010034181c0959118003c003622180c5c0d0028291600088001029002d07501089024101d8541c0380c8001d00820080d803030946030071100145401207114072400034904c1000c015003138406203e0051804280c03010b50703480c40c07000358403502c940740485154440c107000b454000b450000809800c04000c000f41c2403031041442036038850baa48441e9211160480f8440759407200d03402c882030681543d10740c4402d0480707000b40304132400c100d259a030300d00d0711128042050754100004034036076040801500a405a200f415120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 927993947 1250 927992697 927992701
    0x15141812030a0806092e2105031608071415070e0102070302042403110306070c0f02040c1116150e0109090c1b0804141c060e0309040c0306051206 64
    0x14541c00d805400d840c070445075100852480c0c1c200d00003400581c40500603414800004c2c0c114035244c40c03403920505c540d01e040407c4050030003804030343c600c143c250001c000d14038102000401c280c8804207940200c0e2035170000d109420210300b025902540541400c80181004003c40200640c1664000c11940c200601590b0041950360301040b81e0701101d034162004100e0094400c0030619400b4102d51540400c00405800400d0249158064013810750030b8080c1d8045444419044823400f01c02500540b58070385010100c0c005040c01d0344044496503d610348101c1f09100a03080c0360405201c0340c14500240156030301480401d01c100c400d82002105801d10080b01019080060012102d0b071185a41c1555105503000c0301d00d0007004080040d0b80d884504203820350352864003e07960741050281210054079200350207000d041c007600581580d070b0940032045249405039507500140c0311102c0c0a40385070000380704400e04c503282c80c000e00002c14890340b800700d545810801445282c03220a0a6014031380d1000301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 927995197 1250 927993947 927993967
    0x90203071403060315060102012415030b1f02031c0902181308030604060b03041a0108060435160201020606041104060c170d0509160f1514181203 64
    0x4003404581700044280d0740955854006030300510101c00c54240352001c0c80d09440b01c032543c1411040c00d8607218070200195001ca0202101268906810399401c5941010b200d0b5000103110031011003205a4411a0304d81035201001282404400e1289407409460348180350440c584030002c80f094170018000401d003441d0000700280e98890400014262405c00008035040f41c85580081015007020415195a03091601d4400311000341c00070b0b0102c0755980c0c0030000c00d280c40b0108030f00e4040d070341040fa40d401c8410f500d40c4070700e0b540c0d180f1951400f078803000c0300c126001507241c03101409441d0303501444081110b03180d0001a00302480107040f280300303d02d010449070503840800d05640c05c0c1ca155203044d95506055141c00068402c5102c1d002c45c43c3d49010403000043c804c1604401e12440046007501d0612241115480e10807400340150005144560020301250701e11000a120b0b8000c586001c0500501d0b0a000d45501e0b481812100b50b402541c00c440d034050b0502d070484600280c400001545440d080741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 927996447 1250 927995197 927995203
    0x61c02121608070207120203161d011203080c03070e0405190c0e0d06020a0c050102071b080a02091b13150f050f03150d0b091506040c0915030908040902030714030603 73
    0x40a81c06c4040011007440301592000c0060b01c200c00c4400c582c03e400c4c3c50f02c076034044804100c12030a5003103c08070540007140c01d10721032541400301681a00e4414685d1150b10490341c03e5080101582e003040315982c031881203070b503035400307500d0084860b18801d0428122001d905800d03202c8080720038043c0b00e11440381061a80b9481421491950050340c0140c4a04000c0000c60708000f0080024240d0f40c004555542403100c0030034400303400421149192076840c2e803851300301e40721103503040040e6024100070000b035801c0e00d11030320184900c840b803510f6518107040c40c000107041c007040d03070041120b4542c018402c1ea452900b1840e43c4118421a0410904000110140800030b101c0180040b00d4001c030030514041c01d0300d807001500c1400d6801602440f080ca402004565101c0d01c0c09110130707034000780002040b640d007407602c0340c2c04151500d503641c1704085081100001031000340000301c20805985160030b601040c0f901000e48080c1000c285d01507583d003030440f401015030a0280550355a07520400500115907000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 927997697 1250 927996447 927996449
    0x3070e0409111f1b03030e03070c0f05090f27030d020c0c010c0c0308160204060e0a050c190c11100206100b19031e11070302100c0806061c02121608070207 68
    0x31301d50000c0c405141d480c049001c1c0042d402601481e1001207036500802c800a82100c060380c4071482e5410540b580d1740c04003d00d4410a445c42d101c10100b200208038801321900d6040700c50210000503a91141042c420070385164400904c00c4040c55011950903c800b001b4880140303419000d19150000c14003980741d078881c0301310310b1100500c01180092040013103204601c2250040e50028800c014403642d8115603001000116098020039180c4030001d05a031001c0c1042e02c0d400c0c44103102c060441c0720b03002000e0f100c8214081f02541c0040c0c040d0405045ca64038101810245180e0341c0c003803c410b04100c502d0041c0200c00e07400c5929010002d110038800c3c81c01d80e4041c0e1140c01000d2501140b0080c4d00540507106071041c810041c103240c100580c010b041c09030100141691342c400d500301e034800500e29400c401103c0e504036010000542d018049005854401c000c0c1c4100c00c410b800120000c2681140bc83c00c90344504a0781c04521002c1781000326801e41208a19051b48041c1004501450702c400025210f550f5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 927998947 1250 927997697 927997727
    0xe16030506040e0c12150a0f0f0c050306120106030f030201020c0f030319020901030209100e01020c04020c06070804031701031209060503090715211505031606030203070e0409111f 79
    0x840c08416945c850030450344c1c482da003480b802010142014a6080007400708040005011420800789401085c803d114031411910b1f280d89540c10f5840d45010440359810200ca5143c0710340d00d581c0c010002c59120030412400c0c904c2500016500d03881040c407942031040100e0b620b0120b4005000b0014800c41c000c05903c10b894004800681d81c003080b1005800038020310305800e4200010303100c5a02020b4000303804400700c1c04241c08a508907000101000107030302c41c5030300d04aa10b810000220343d0a42c0907104d110b410a00c2030030400051842d10080f1461041c0c241d01c19a165003040104da2a556041003240014040038507002c0d140d45001580303980e8a561034407d211020800351850520382d0300c5825100704680940611109440200c0160406042c80c0348031400361203901c44001840303240019001c441882c60304241003025180400035002500014540740c284507000040451035640d0b07105848071140306611051500c3e0424040c00310103000c038121124200104100b0401050b0401d03018491034407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 928000197 1250 927998947 927998959
    0x109141e0a020a1b03080f011202010c0b07090308030f06010f0c030e0d0203161701060b090a030605070c06062312072c010e0405010e010b0f0d06060e16030506040e0c 73
    0x2d260042182c207105000e0841440c482800d0036131301003541c810500c900a21a00888074404d9894000005901004181c02404502c20790740c003500080031111070310343c030400c1030800c04070065072510350b0001d81e4000c5501002c80d0b203d8204005156800c02c04001303002096250007483e905080c1d03400340080b0b00b942d568900c180d0094901c0070442d0750811600940811000040308034036500c5081d800000061040b004140d400c0000106603c103410b400d07548041c5000b45501491440c1d41c81b0710b0001c00028040c501004005032640740070400500401000705220b0305000401742c0070365034030356180444460390740c480c1200c0010b9507114400010000191a1000c119080c81c20f03005007078110ba1101c0c9202080300c00c00c1c0400008101280c0540c0074030840c0641d00034013006500c155000e003210304004140fa400000219588207a09140d075a1020301c901c02c3d00300085a0761540080e400c0d1502c12070310810000a00c50840e0a0541c5c140506030b0042016075003401000c8101074416140c0c0260715901d80150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 928001447 1250 928000197 928000207
    0x607060b030106050301020d02040504320903091005030603010b0a0f0b16050f0601030c0f0f1a1b06010501030e030f090d1b060c030f020d0f030b0a080102030109141e0a02 75
    0x1075403c0d03120f0001044018000c540d00e03850003048001940052084030702c40e13860200a441c2c61440300100c161540062081460b180c00302c807150f0520171802401c1440903200610a495003521801208000b8100e46e4813865264589001007501359000c0b500c2e0309000308181001080311030a0420f0310303015100c0c00d45031591101c06100380c5001e40101c0d0280601a4450800784643c155400b01c0c009040e01d010782c440070704182c0c490078143c2044986110f08140000300d07180030048143c0000b400403181a107242424074007891002e442c400418803442003189604480010441e640e01449070314a00340c0700340090b60400c020000c1840042c00364962041c002e109041d810020491541d0314115000c0d09090f104141d80d86610006108544401d0104c01241ca0660840407043c0000b0303d602d0f01c2c545981c1d0304040c454204100710003600c0700349400b64100d0300709040821010028009903002c2c2981407400508110b69416420002d40050902d21621403428840e208036201e032074000380d01000a200140e911 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 928002697 1250 928001447 928001449
    0xc06160c0f0b0613060306231302100e0310050a0b221a12150c030609060d1b0611100c050a0c050c091510030e0c040504170a09091401050607060b 64
    0x2a400c1013800f072075286004408010070010b684031100d590301d41d0141c1168400d090307102d10440d41042e2030248100ea0507031006001407a280582003182402850711806011740100441e14051000f00e94644082e150420803007042601c2c40781000c039401c111241c0400301c4400c96201d030654410500049420384904e2080000c1b82c0e51402c500e03007140058034800d0f00d240c6105005886e9601d5041e101080540000400c803e01017400c103880c09035000802100c0d040e10f83c803040122102d08084112003c0c2d00780c58880c544002c01d03c400c0340c001c05140d160700984401c042c1c10035050a0140d41c108950b14900004c864407143e0103000d0700c00944050074410441d48186c00d0a034a003d4011480b036510004c1c400c100310490400303062001d5004000e8884012405010074160290b5820b5920000e41c0c0c0c0c0b104204103850b181a03007019404c2400b912045a2070902480000c2c4264001c6603041c020880300070301048800250b200d1000003815202c5002e0f2154140f40c0003442c917104803c0c000e8105910707a51704c0c500d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 928003947 1250 928002697 928002709
    0x70221030612031620060a1d030106090e0601050916120905060c09130c050307050d06240206090102041404021b0d0e0a050306011508090a080c06160c0f0b06 69
    0x28030740b0410120380d210340c100e40c200c004c100440796003120b880843c05030f05208004540808400c0c61300080106080c9a609102112004000c0041f420580500c0d14640c080b51002c0c81650080c0100c810b02041d14050440a01e00e002d01c10780c4010b0003078030000100032023280c0b803e41900c074401c19850100c100c0900c00b540400a0491030f42c0152042c0100c0003400a030001e69002000c448901303480649403180364111040458100104030310108104000161405104100514290500580018405440c0c00c600741d641000e0656000500100e15003903194250100301095105c4403000003945018140a001d02140c80101300090260b1740100b600d040102e0f0340c6440404504805044425010702410001c00d803601e0900850702a00c464840414030713080101c0c41e603060300e00129003846481d00500f0202d1316540010080c41003400b0380f1821000080804008003000100b030340c000c0200c2e00780710a1840420f022070320100244180c5521800000e00c442000113002070f0001d01d03519a40d9504400300384 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 928005197 1250 928003947 928003969
    0x306040f17071505011406160b062101050a150f060c170c0105010f09020f04120206040305100f1b020c01110705120a0b07090e0a0203040f0f0303020a03050702210306 73
    0x100c00144500368808124960788080d04840e000741c0406e100b85042d0040c400b0901c41d40c051011003a80500c4510023103405011100d41226015000d902c4c8151540c110440c0b14548080c1001300765103c40038000c0da04124081c0822a0320311480380d54000380703452201081d04070207100e05002c0c400d120049405102a24910083c44c2c242c18609039918208848101d000302424004d1580c01d0522280100f0150740c00d209032644803c1c5d840c91180f4160401800c038880780f00c3d01c1c81c01c82c0c0c0400100f001100003001407000361495aa42caa0204102c0b68503a401c00a03030305035020042c0425840c44900600300d0f80003a03070020703211081c200340e07824400e040712131410030144d604483d40122900c0c20200003048005202281680900c0c041403c580710010708440d0b5803a188030715020020114041001d1076541d600840e04548200301e080e09801080c3e44604000c00d8112013500483e501082c8905c50303e4043c041c5503808206840030f000071003420305903483c4c5625420343e041d2802c0b40100000e02d41e5154480250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 928006447 1250 928005197 928005203
    0x60b0a14090616140f0d0e06070515071b0215090f04182604180f0c050c160b0f16050604080403140601060212032806060e0306040f1707 60
    0x203948410040d03509000c940e1200003150000b4001100142940c0c0103d40c00405d104003101501c10f56419000407240c0d0708050540ea98000000c000da4070014208000705c0640f42c815501104451a08880180a0440801d00c50b40589060900c941c010303a140061000f000307440c80000d54550507400003154003c000701c2c410a80003807401e590001c454000c410303e070b1078452140031111f803c2400404080210700c2003004140490170305010620004180b091602c0e0300b24070099002910307091030100f50040e20038081c0c40b100403d40006003200d5203e400c0c81003401c0da4076458003c2c21035a01d801c00040180c80303050f180142031800426440d940c4004004ca004526420200311541170906061507050395000380300844420f100c40f640c0910400c0d010800d98102d071036640150080c2d41c24030100400580c8010604440810b4040c444950039103485007420408401040c00500f460500401038404144445421300ca580300000300400a0f101290079120954000f0020294003840b10f1240300310301403e9401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 928007697 1250 928006447 928006459
    0xd0c050601060815041118060c0a0308090a2a14010e0112090b0c2d0403081b01021b0712080702060c070b030406020901020d0908060f0c041203081504060b0a1409 71
    0x40340e02c5081c0714045d00381d011f106204030208042c40410895180f207020304079105500820300302c1c40400d00075502c0307942c0414a04107940010b41d5a07075844074105001d800c0c03d00b8403004048101440c05040320403002500c214510340c00f0b85941c0000203841c2c0909024030394104902030780d1540038504c407a0021440154010f6554840333092040800d2240c1e000265503050300c2d940d061100a055448003018240f0503081000c0d60315007419a225490f15920210f1400001502944c001241da82c003440104400190418400c6101130b28903445ca0800d11154442d0181c04070b035070882004200e47c00d0845001981c120f810369603582103611042d041c00b40a903c54001d4190100070803081c0140d58000700308042c800d0f0300355040c4820649041d02e0540c500d0003074000c15030001001a1524240e22000e85c0c2002221401c0707401d00303030395456802c1c409111007001c070001760103032050081000b400e03d41c41142c0a8126010b000084c140700c00c0e032005000b1004580d00b045000840d8003645603880003101c0381040060b03c0c0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 928008947 1250 928007697 928007711
    0xe181c080a0b090402130e01061505030f010b03100909020a09020f03011a1e070f020a23031c051c0603120e1801060f0207091a030d0c05060106081504 66
    0x1801800c000c03200014098103195062515103031803948103105542c01001d00980d02e125124050080c0034134221a15150b5035072a001c121919032405003404012907594142c1d407403902800140301e403501a8818941306c801807040c00304040320136a90b0300668031b11140002d0660060300005035100b40702d0744081440c03880052080f02941040004505a580f00751007100380c800040e210120521510242c0d42959900d03181e205071600c55140105070300c902444084078030803400d40000b00d207101c0d80d5202e020300450032201c044403020409202c041c50030045000d81000e00703001c05d101e4003141d20040c50300200701000941840c600c00780c408034042400c415000b0000780c1e03141d280802c0451066502c40c80411a9164425401d1a2282d440440c20110b5000e046042c1d2030143c05458101d1003400c404258020346601064408540c45100e080240c0920f1030800340f54418180360900d440305a84504018030a10750801141c80024002e045402a00d400c45081d40c0703090084010140030030000351300c141005c031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 928010197 1250 928008947 928009003
    0xb0a1a0901150c0b16111203060909010e2a0102010e100c02070e1603050105040b0a140a0b030f0103120c0305070b0a0207050a050706022404060e030903030714060f010e18 75
    0x3104400705e00c2d0540b02c2c404200d503480c101030380c5c48400e12850066078504000040075400d02216140e00044600700110740001003945450421034401e400c00e801c00c0965582502c001c040140051000001b80020015220480409511074107540d818140d45501c1b40c0003c04003902c200000c0e402400c00019980e040e0a02401002c5242c0c841600d20780000c0c1844000700e89403a0611030020300403002482800c1c810720346896403040c15000c40d01654081c51000f40010304140c444002e40c8214030301c8640d00e0f800d604510f0400c4610101e15550000c00509405101c00250440111041c2c140c00a08800056540310000c001030b11440a004000d0302600122200700b003400903d42007592856029030b4082c0b0702000e010b2080c010129a52004c03c1e0301100401e02140c86a800807840701a010292440c144a0310040780c919400b505d81160111225a00540030740414030040e074000c20b1014441074594500300f589a202d000c050000d9050262010030a01c081204024000303105a42204490030404564 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 928011447 1250 928010197 928010221
    0xc033010061206141201020405220c0c02101209141c030c1d0a0b0c0a050606060720130e01020405030616090b1e070b0a1a0901150c0b 59
    0x31080102055090181109281c450f004103001c0d20300c96014410150140c1003040890380d400602c0c0006550f00f00004145a100c1c001d20020100710401110042404c001148007140d80f6042c1d0201000b0110640400584e9240990703903c41c0454507122020040c5120280010800e071400100b0042322a14010340c100c1c0d01080b8003400e105c400080c80640c1c5400c19058064a51190745000050410500900b40d10092510b102842174050718885400391100f07070309031503680525500131031a4442038004003000803c00c00543e000c90156040740c10f00c6000d0741d44440304041940c21042c1e88046407501c2c4160307111160381c0030095107604400d00603403100707a12050003548240a41c0340203000b20800140340c1c0d00c8400702c0d200040d040b5900c2850107803510020841942208640410502c0e0024510200d04250300207050407900a424881c81d90902d5400c6000701e444400c18510b41449100e031440039655055125411900d840900c00012030580c0d00c03c80e182c22a1060007040c945820b002c0c06a41300c900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 928012697 1250 928011447 928011449
    0x1202220b030607030e0607020c010912060b060a32071e050a080a03060609030515181c090e131203090f0c050a0506120a0f0603140a170c033010 63
    0x60070b417111516030b81d5080361100e49c42c100040c04203c040d8000c100b481600340407039a425020b0b0b02e0003c4c0c6c2a061320002040756010000140000d600c2e488106100040032410602c250f0b4048040b082002540042e220703140101c00000d4000003c413811041520b51081c0d0341102d47e80e02c00c0655120326442d182184050b009110b4000009140c1000070880a0084190713000b42d94211008014841d18141c0106440000403c9292401e007000303103e60f403685041080303840e036800743c183c07080c0d580c920f0420041224403254465106840300c90305008001c811b04000c0280541c209000303200c0038070303540800d030090442d0050040c640004c003c0154140420484054141d44085445590407692901044194040c41c88940c0f8a4440d52001c00c071000d001c3c4e48070340d02203c135050340801c1c0266240c07503001006100f54080740842e0441e07030141d000c00c0301214400b01b018171040307441c3d0309020216009ea541c134020480314803c802e102c0881f080b004812508030101d40d814945031486607141c0203000f0f5983d60382d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 928013947 1250 928012697 928012721
    0xb0f0a06060314130218040c061403010513050403090f0f0801050a0504021c0c0b07050d090519090b060c06011d0601020109021f0c0b18071202220b03060703 69
    0x2400c040450000d12900461004040041000c0d038241c55401c04001c40440840b403ca0f4801c003002e46d24030b000c03041344510b01c1c801d50040c004042c840303260a03400707480d480c000c5161082003072080006100503a5040341d10004a48208000103550351545010744421140790401607201e02c500340700040d100580380400003a40c5603000284490744400d08408282c68042d103000307500c442c480015030720748400546034500c4980140000c440c0680e0394000351081c2c1e4482441a66103800c182d0032070040581000300c920003072005035028560300609440c4040241d099000d0030049541310340380349502d42c1c0c030002945d64140801c070549829582d250140e51440a0060042d1800c008505c0007410320360040c4034801d860798001c2d2810311620307080410807200d079055055550502080070901d0f0081540343c140d05105000d05400340c041d06600d081e51070310300300e0650301445501d4000c142c0f803001a02c54074031000401440d9000c001c40e40d01e80b010307488048e196142c0c2c843e4261192104101c1c029505410001c01859 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 928015197 1250 928013947 928013951
    0x807030f0e0304080304030620120c0910030c170c1803010f0c020a050d0908030405010e0102150f180f0c010e130e0606130905060f0c0d050103080d0501061b0201050d090b0f0a 77
    0x1702d000504c01104005070727034203928501030100d03203d40f00c0c0100504d94055440c0c54100d182112180000e00804580f14480700041ea403048041d01d40c0e1f0b000b03070601d00b0b03402c03040301080602d00d0048100c0c81744d4452194501220020409100c220391403d402101c413612080e081400465000c810007581c031540d8020555861203508603000e001c90148202c0400d4610103405507103480d003080b005443c2800c40110841c118171a100d042c01c0811314200217540a03040030705080040d420200d41d2810720818030850150b140d080262581c02628002410040c05102030904219021190340054004044411642c4210341000342c11604510049034981c03056604840340b00c41c0c040b41a40340400c4814a4000070031035401980030070703e42d62152001681c018840700c0e0162400030080d0081080e118282d0040300d040b5004601c2c0582d44025005040c0036150500c4c0201070b80300c05100c811072035022404c01a05000700081c032602183c4072500590419508104507220354100441209500d0311308540100c2094 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 928016447 1250 928015197 928015211
    0x11b0b130c0f1203050901090e09010c09060e1e03030c06070806010807211e0c110c0105030601170c0d05011211090610110f060f1909030807030f0e03040803040306 72
    0xa007030010400c05550200b880c0040f0b0030115074056604d40d10006811b414000890300004405480f9900c0910410f00d03540046006075a00002901410464010310240034032032041c54080d0300c42c005c40d907089000074210800824908000300f030a511500d4500f9545c0e02541007005407450b04840b00318090042aa01c500540e5254941201d900f15020b00c0131601c100e00c100058024174483d0070440b00811248000c503107480d0801c00c0c140403a00031210b01404207105901d000f80002003804851039282003070800c6455840c020340000c201d01a1030407003c21000700b00780401c0043c80c01d801601c0c0a59801841009507503115407820100025010085805540c8180c801e4094105050800d002d05c1e00a000ba11051090f00016903030404c0080440c20305200349020400c40580c100705103030007120800c0c01c0a60314101210303000c23284810780071200d007002d0030107400000180c0e000a11960080003450300150301c41c01c103142d031005000501c0f0103509620022030041640500800104200d81c41500c0401402c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 928017697 1250 928016447 928016459
    0xc0d0e01050f1c2a0504060f08102606010e040c0b0307031803031a010f0206060d0f0602040b1314011b02030a06110d0f1401090c02030d02030a09140615011b0b130c 72
    0x1b8401c074050940010b03041c0078440341190045504a07082894400851103030b54540c200c041c4e40307d00d00642900070402d0110702d107030260307000d0144502410506600071854a0f00740c842c511081d1092181c20700380640000080c03030a81c03281d4803e5010a5a440040c2030300e1585050003405000b9112a46290070f05001040074650302801455034a0f16080d005840140c0e00c080411081c03004190f02500c122604c000c404e07001940510040c0007800110541e5a01d41038405100840c0d00079507001020392103222003c0071400c0c2e80041e40d140d8444d01c15090000c45a002e440802d0404c60858002008a030402c0c1341054000300520152141c540142020440c60b07400900c818140d89400311924400c1c08900700500100e6003981000d03091000d140101e0380740004110302c00f02280e008445243c500350740c4181c002d0401001c0904008400c020b600140030030706054843c803030950807a84403281031041c2034540c3d00c014141c0710441c004d1240c1001c040c43c1d041c5004283c4000c0da50742140700711442d40741c401c00030441c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 928018947 1250 928017697 928017707
    0x150108070c0b0114181302120a08040806010905070f0504050d0309030b040f110307032604031e02031006052808010c0507050c0907050301090f0f05040501020c0d0e01050f1c2a 77
    0x6c200c40e65401c032003500d041602807054075101c0d1682ca500c03d0081411050200303c12100400041c12204001c0074690b251804c240d0032980054411010803030441d004440d8964003009403801d450782215401c81d8041689400c0d50050790b00d500051120034128208020301200d41058502c0b54043c0c0c00400c90603980908154540e1210f02004021140b1840ca98401d00100c01c07000c500c081ca04410345140a86035200d0003502100740d6121b131708081d200412a02141401e120004580c02c0300c481c280704c00707800c0c440010402c5c1008149091030218140000310491a116400c0000b050540c0082000309203007a40240980c0c40520203a48a21074074000701c1c428141441040d110701c405559550541c0d00300000c2e9001b078a888511056040e854440e401c06000040c4150382c0103610a00006070f03224540c81c001420003801d00ea03685c061092000810308682d81040844802906072142e035603898041c80241d0390803140c000d0200300a41c3c5000f00500c01c1d12284128039403001d8034441c5a48050f500a04115a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 928020197 1250 928018947 928018951
    0xa1d0a06080d08090118050d11161211040e0307020a05191701090c0f0e0a0e190206190e1302070f020d0515041209050306150108070c0b011418 63
    0x74282d4024803441500c2407051090641044501c800414915025151b0030004240307090180c0e034a0300882000030602d50040350701e614086408001c1c020400c480b905c0724501d004a4801c0c0041540c490019100b0060300070661184040c0c010010042e40803c842071036600e8200715400c80c00307881003400c04242444c10b60aa40f000105078108146014103004e03a26171752148140c0d102e22150b4a6108050000d0a151500005403651350340e01c1d20300a20b000500890110b001d40020651468401d0001e0604400304400c10112800056000300d0680e038400b1414500c600c6108079040c81002e4070030410395601038000820b08008880f0845201c001855120407403080c400014012075101d44a5801414920202000140104107850300c1c0700710382c58032480242c000c58040366081c100313030170501020f174100354504081e1005034010900381c07405080c0008190101c00b600c5043c0035070400007500e00ca124401d0a8501c03540142200c0165a551401080441c011724107030b84200c0c1c540300440702003c80520164 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 928021447 1250 928020197 928020209
    0x8160902160609240c080a0203060d021c050715020705060309100914060405010c1d06091201020c030f0c01050601260606091905040621110409020a1d0a06 68
    0x200c1d0304403a9a0700c0c1e030300030a441d003802c80390b141038410445001e0f00560a04402a0300d07840d030205a050002030000d007001350051168203d1031051046c480f19840d03c9803842d08055054400800301d24581030000b040c0e81c1c045400a100b440741c4400403034070404e4510307002d0681742640c00b1601c0350740d2070b44100081130000b110030003450750011844540640d4030b900600d9800380240c0ca09480a1407001281c0c1c18104121410703a06030317455902880605038410180c9514264080000c607203a0400b0001481d00c3c45032100503441504e03202070792486080203604a4103014520302c1203c1e41c0701109204d21005422a09000c58035510b0140010400d500980000b000703030b0700c01901307201c09110003502c074801840d001d0509504035000f408000e405441e001c20f10030343d12290f038055900c80f62405040000b9109280c200d1881c0b030110f0050074403c56000c0a82c58042c590202c0e803409500e5904000c680200b1000ca0080d6006164400029500c14090000c546050b40e0a0031484c250361003681c3d9100740d591620800b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 928022697 1250 928021447 928021477
    0x2010e0d0507170d0b060a020a0c0915030b0c0409060f03050f01050c0a030c021606030e1902090601110c06040906060f0f051c060b0d0c080a0510030314070c08160902 73
    0x80510070010003000c0c121310703c1500046400301200410300d41e070400c00030800907034841090310003031110344000240201340f03020080c405104d90354807004500245100c001d000c1e0341c207203000c1075541c2109001e0b6000b51805200802c6003c0c1e0b558608220300e21584800c1e0b4181c0900b1b00c0700c511001041c01507612a022801040780741600452080f4020b01821f182181140190a81d12811144031041c050040c5038998020411662007801c0c942002c07002c0f0400c0300e500104010350001038803801c02640c0d110300700342030500c00d51050010341401c054828104583c4074000160120310030400d9030000d000e5a4981c1c0e201c043d0030700c2524060b20001204222200412000d0040101010620f500101502a48040131558550f01c0700782e0b25154112900c506503607030319440401400799104554070b46c4000d81d20024025800d00302030304200e8503110700002d400c02481e54000c07646820101c040303803103084d8801100001035a8945840c1e0700e450503480c24440c0010714140000313882c01d40d07009a840410081e151 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 928023947 1250 928022697 928022723
    0x15090316020f04140a021b07140d17160c050d051f0b12030d0506030303010f0905041106120108120903030d0c030b100503010306052824030302010e0d0507 68
    0x81041014940802561240d10383d440504c0e05140e10580c18062802920003689428071743d44041440c100c004e481600c03ea01442c004c000340044e51270010380202c425156814001400e090942d400000b6503050b48400d04001007541c8405280780782c281146000e004140c6086464030b0401070f2510450b000500303550f004580c07060401d000c11002c1c4440260003200026003060704404900004180b09030f0707500541003c640c0d011f1130200383c003030240c1c0031800700c0245142d50f05014a140000344103000320026181d48070001020003008000c4030300507100050500382c9504440c540d100e10a0750901899055004510f905a8614038200c10f80e00220307070080c06181403e000da18468000d10a031031055042585404407003c41380c4541402c000039030303c10350f109543e0f5030560920034160766010704030b0000f4102184a81c001400c0400040d0750319925500042042021032180d1048100d00c4032100802802c00c180000c10142c05600001c5142d150f0010784002d41a8841c0565440c014804040c0940d60740a070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 928025197 1250 928023947 928023949
    0x607090f05030a20040c0918020c0a03050a09050402030103062c0307023a140d1b0c0308030108100e0a0c210605010308030604050a06080c0d03090e091509031602 71
    0x1544d001203503102c00709048000001d40004040e16484000705011074882c243c140404e0444039900c0c1c01c0e400007810290316104a5458039580ca0705001c07405001c2107400310341c18450f2880f50040030003d1000410642d100d50316800d2041c0200002c20f0554241c1c0320240815415a170250000e00d0486910405181800c0154080c05054406c4011030041c40c40b4682c2041a403052590301101a101100ca40c0351208980d4a000110b0b010201c2d40110303564000917100f02d410f50300c200c1030108005074011105100c4e0081c500044881c28941000b015040c012002192502e800121581004440b050034000c1c0c90420103c643c23501c041c02005046280000f130305000e81110f070184a08200e008195680b03207401c141d11764204980083e00102c42000001050201d41e20b0280961034220100c4441001364500d45528181d03035180304056a030043d40035607075050505010f0120700c0c00a149403e240c8280c0e181081034503464460307545848901c020500042510860004103456074044030100c69902c8004d260 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 928026447 1250 928025197 928025213
    0x304171e030a03020f1303030201240302030a0204020c3f040302060304060903050d14040c05030303070906031a04110d0c05030c0702010c06110a110708160e090307140607090f05030a 80
    0x500080901d400c1042030002144a00d1b06020003035000fa4000981c0402644a101c030002c070200500f82c05101414041c40507980100340c03460190b604540050740d80032000c2d0000c3c180030825084c071643c10f64455070084103603107444400d1014091014003024000c0300d442619107502580c04013a4200506000040000e2605e030320000905010b4240207051940300611081600e02008102c50503c611030244001c10440c000c070321003d02005c80c040c50541c900204000c008420703e115800816031600040900406542c01103030760104060824051291903149809441c0d0001d000502c1452a041c0e043d507240b84244180c0c0d0017010348841c0f1910b0310780c0750380046030304489901c4203039005559031707505528500d041c41c0103003c411a103445a800c0c81000c42203042c2002c04591011015400c65500e00810890305900c0314140e99417103ea6840d80d444400d00680b460040c40c0e001020903010a0500c03450b1100014000c0c0704984550740c0d2046e140d141d1101c0c5070303454650700c1401d40503071001d01503c0000d4424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 928027697 1250 928026447 928026457
    0x1020f0102040e0c0912060c09041b1b11120601140109050d03030c031107050a02121603030309050c0405091615050a1b150603021f0e100309050304171e030a0302 71
    0xb800307046c4031b41108100380d050040566100d04094000504458241442e0241e8020745642000b03034602c1d4240d004010380306490900480c403034903101031040380070032a0162800d400707200c0c040c090203501c0340c0803ca1315030f440b0400e0261805120600e411618070790f1250720102c094501c0501001c000a032155800c1d00a00003445441b0245511240901c4400319440b002c0c3c00340900071001040400c12a0042c000683c000c00401e0001d80c000c445000d105111600c00241160307414640005e107071195003003031420441c5603441d080d4040d04200038418030000001c0e040e00c2c1041c10781c1c0c1d40345410b03035503c0c4000304000e00f03041c810010620074004000c490307005a0152101000c00c500280c107110451b903a0901d80d42d0100100501255203590900c1541041e45806000c500820240180385510f030801510030000d100c501032040c590501215003041c860380148003185c0e409011a5212030325040280460345100c6058040c6204040e0a6500010b0403283c10f021814603201075403500060f0391003240a5440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 928028947 1250 928027697 928027699
    0x3030417030408010c0c110301060321021507110d08070c080904020702030a03020319050304050c060a0c0b09010b010e030d12050612070b09011e0f12090605100501020f0102040e0c09 80
    0x203100c0000d0003c001c0c0a90313126604582e031404004411468090180c0c0c00d06403185020307a14115003800051040d001d46840b18100c0b40d0a04110002c03d00308030300e040c2c0b010301a200516030385414031455a801c800d41e448182265400d945240c1c08403c0308444142023156000000f0b1407528648002c2060040141340c0500007800240c503004030354001c20300d400396440381240142d00005118034500000c03141e43d00764121a10b00076141d0b0910b51030b22951940300c120070901c68817000550b440100e008804084026502048111a5140160149000740904581c16000c81c525041108592034041818480030440d500c1d04281d05032080b800d48018003000b04455046511444103444e400d01c01c1021800a00c06100074696505024000400c02d88002c030710008502850080c24a1464004006809280951408004000070344200354003400c030381500a45141d00e007005106031580e45141001c140e45080e02194540f848c01d0010508074072440c03003113561410f001d2000c51002030a060042101140c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 928030197 1250 928028947 928028953
    0x30c0a0309080703080702070f230303041806031a061804141b040b0d0206120408280305390d2a030911090603070e010914090a0203030417 61
    0x480e07580c00300d19803103c841a030100320f0314001c0005903981006500041c0401c1480350300c4492402a030f0341780403400c1d0010810510040c07280110940c80400c1070b00c00406000143d052441d440c5180d8100a110f0750006456903007001c1c0000008a24a04007180661000b5100000c8061043d003150000272001d4400c5a003004003422034515000c040041381c8245410400304a240925041004115014019028000c0d003401c00900056507070300040d03500c1507461b00e0341d024040d0385a00d0b0800b540e03c0b0b40b10702d1941d0031f258108126603200c000044031441303140302c3e00c040000f52907103640d9841c150820701c070302c440800d2589114440000e24603540b0010703810f15011182820b882c080d0315810348000302d045c0700d259201200b5280703003448181c410f501d0303100c4242405c10222600b070310f541b001c5515181009004804007404500030780c8041045800911804600c5902c0b941c480d05502d019020081956000300d5801c000303e90017140208960b245164010001d40c40c103460151403890340e46501551280c240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 928031447 1250 928030197 928030211
    0x28060902120d031803020307030f051e0406260a0908070605070f02060a05070203030a050c0d050f07032304020f1206010605190e01020d1407020d06141308030c0a03 72
    0x1e203480000d461011421005400d4591880740001c0c01c882c807440740c101d24583c0000708140801e07004400c855000d030f00b61611800c3ca64002c6000c1e1200c1c4604500d10054510604490b1540007400c8064000e6030841d940e0203400011081d50211603011980c40e0900b0100c181d000f00fa0900b007aa1300c4040005e100d1121103050a42c540c581d0021905c0844405010444c26480e01d030b81c0b190306018030740c0c0c07000c00038804011504090400179528080103000c0c03102c07580d498001c50360004021041d100c1d41d00e0007110500c0345180c450182c04810000356655400320b401c00518040a2510700300707500c001c102031000911140e40e583c0030807a00c0310302891529001000300401c1546120305020b500d018100f5a2105617442c0c0303000130361000c0c8004c241000401c1000751201c40403282ea02240c10210184589012010b03051500701004041c820742000039130006010700e621041065940000d11003503040f0004070425070b94080c107424815103440004110340e504000003102e2450500180115942c0c40ca0300007450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 928032697 1250 928031447 928031449
    0x6050f0c0304030f050c12030c0d0606050f0315060f07140601090e03120601030b1509090a0614090c0d06090b04060f1a0c150106110609070f090f020c030a090f0828060902 75
    0x152340b00f526a0f48908a001511400c4410309006580c010620303403600d203241c04044042004540006003002404005806003401980d079501d00b540d1104d1844000079a441c0498617007a070304085a440d21940c0b50250000014a1110034410345244000c004007851608030103909424004800a01c92414140e850481a001c0c1c1c036544156020040c0d0f000c00550f0f545108010009852402003101040905010007030141c118210304602c4119016100c6030455110702080050600071051008440d6251250001301c02006130001c001d003200580701044510348544851f0348000c800d0080c414900d070220004c454083c60303813004142c00c60020044c1c450a0710f5100310312400d50020307404000000c145e80200a110041030002507080b1002030010800c161820ba107800652000b07110b220b041940d84c002100811040342c0407658024910f0b000d403940c2d290880e40140040449020b00352107440c20388401724042c0d40000d00c07907203c115240c0c01d211710f441c0d012100c24080042d207402151065200c0c1036030801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 928033947 1250 928032697 928032733
    0x16060e01061509061205060f06090127030b0f011401140c0a0b0a1406090c090126010f0e0601080c070501090609081e16060c02160306050f0c0304030f050c 68
    0x1400c92560f0b4a960a600e4500c0041207208030001c0c03e1300062038082800100c0d0b07100200a2001d000a0362080e4a8500180050300c0d21901d650301c40e6803640b007000950f82200c41c030b851a0010307030344100c0e0501e215882e00078020b1040d003000d0140110891291448190543c00b41c20f00c40850714029400c103160002c8603e450741422103d84c0c040f42d0559054040c000040034501402000c20202c8021008a141c8680003c4020703102500100a80300e0000b2100516441030304522078002c084510380000c40d000c03600403107050301c091146500c0345401c0c0d800420b030005c201039000e00880f0141d451001c140c5403080243c0da02d80c08660210754943da0f904450000505034010442418050014641c85d0f699402c0140258402c3d1485010102010007919455000740c0d2006c82c002c9c0d42002c0000f41c0341503640f409030302d08034140200b406480203000d800004c00140d501b00d203201d101d800344015500c4d160524900114002510001e010800d551544441c5074440d00c060300c85204824212480f10083e5402400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 928035197 1250 928033947 928033979
    0x20918042a050a06020f070603020f09040e06010305161a0901030f180201030b0a0b1b03040f081b040c0e120c04020a23040b07080a02010f020d020a0905010516060e0106 74
    0x4407104807000c10051450200210401441103001070101c8a01c1a2522921090140140d038140b5501080320552170200354180c031000c89014004100caa12500701043d9510b0092000b00d59510941224100102d8044e9a0750215a202e17602c81440324505c100860554205643e81810181e59900000070301c2c0c0d860250a40e0550075410b0b000300100180001030558142c040060b010ba0000041002803508a400300c0f0005004000b800340c009501c4104142944900d500110040703e54183c0410740135001320303452045088107107000c20382008000074001550003a400500100309178850300580d0707007403c4512111140c1c40f035003a5203110003184001401c0b600035000d00000208840541c5241c010248409196881c5500c11182040c0c40c1030b200c40d006105d08040104100001b04001140700e0003504020142002043d095483d0221098903100941211480c1c0c0b000544034203001440794000c00c116021110302c4220070f40c80744c071a03480d81009001260140a00c07996502d2000484c0060068500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 928036447 1250 928035197 928035263
    0x312130b1c0518060f1b030408040b03040b0703061e150c0c06050a02060912041a091e0f0907021902120609010c0f030e0d0c150504060f06080102091804 67
    0x104181c84049645882c2090040180901c0ba0700e0400b8000001c948192004d1465646c9a0659807a80e413803400580a0003150300c001040c10001c4144030030040000c0c24680304001e00c3d54100110399031016070503a4449220351900303810b00200403e00c5000c4183c00400701040039800c0c9588001c0c4165200d01c0450b0882c2e01080c0001c1010858480745581030040641040041c401010520130468401c08907208a1040755418290041c184c500300d4449800d8800c1c2d0400202143d0308802c1112495010b41d0600c01507510880312086020181d151080a00d80140b400e035000b0108030100034015551003091070020f0361b0203140aa8030000800081201c0c9108102c100f0012a92070300d20034001d00a03031200341010042c907040984250303141070700146029801450f840c101040361942c1c2420705841c4014000101f510381004100401d020340c9400c8031070030400480c001c00240740c3c0c52801354201d01401440d1680300d0083c4411580c00c0b00d0b01404260018000d04440007494145400c00942c02d09240740c7ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 928037697 1250 928036447 928036471
    0x7060915020d0c0905030d0c23071401080f1f05042c1b010309030306051e0109050f151e0c0d03060b040e16050409020403060b0312130b1c05 62
    0x81c0e40714140b07600607001e80039000c2c100320582c00e0501e80000e45900c50a8144010803151500720018051700d040c1f240743e0100701486280211650441380d90301c600d076500481059a02540c6003c00030352180401d9403140b504c1d61000e9060351034424102c139240103a00c400c150201c00c0c0210100f080e0780c0c2d5220750b80040f840055aa800215010f801400031982074204600070f400180d9510041e401d040c9070849a20030920700014405039601d02a4000c10464010a4210301c10000d019030f2104812601480400240c0300c021301c142c2d880042050300380025070040d811900c41c084d007900c400391107000352138030400007826a9541003c031041040701d90880550280c19034009450302d40d1441e018414900545000340580c0e1170f050070600c031034a0309036001d840c801c642e0a004040a0480e407064085d43c01a000140c400d40d643c1c0c0c0d5078180321001c0c112948125200740207420b6030f45080c80f640b608440464202c000704086052038030302c02c1d0545400c002c44a401c60300c60400c00300300e01c0e541403007000d10801482c400c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 928038947 1250 928037697 928037707
    0xe070803070b09070608040b070302040905010b03070909020310061110022206020a020d02011d3307030e06070f1704170c01080a0b120d0e190b0406050706091502 71
    0x415542c002c0941540500d4001c42002e01040d03a1125241c2d074007940001140302c458451403000c5000340701d40c4d401681580d01e0a000490301c00c205070015030240d05544e58040405071508800c10480c40191000f1030045a400c004100c43c03405042030611011440090315141040e050410313090b84c4c00b00c0301a02c210401841000100f05c094005800900717400e1004000710841036011841005140c08060306104801492051911030308680030001c140c00341481d288000b01c1d801200c140400ea52000c88031608425041080c42c0072541920041c6425954610503280c100050000c0e0358401c510a41c1c1c080b07070092050707020407041111059a00e8078141f4840c0d4851400b01c1c2010500011800030807507070420032014040f60b9008070b403550401c07415000069141d035407000103110b07800310603180e031598054500000d41854200c0c40d070400c0c418056404242d10f50014100c50325800003809101070352401440305100c018892405400c0081c441c00740010740c0580e68480d40c21b1703020294003211400d80c000175 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 928040197 1250 928038947 928038953
    0x20a0f182103111005270c1c230d08130b1e010f051201020a080a050606040e09030a020c01081021080d0f0c050403170c1c02280506070807030e07080307 67
    0x4044030000c581040309158035203846d64550302d8002559140b07104240c072003800c071079064106000000d00355110234114000410025494401c0300c03051003540183c002d1038020820103000d0b0602a104085940e07140710644415130301c0d40180306000d4241c5680d629015080c0e805500515000c40c0138002e10500011020315250400ca901490791400f04481e03401070100100702c81e0403c00340c0b5040445d950f130101b007070768a02c004144a402a47d210140329030003c2c0501c20600d4002c00201030080ca160300f40c8100b00f2500d00156290102940c2000c022450b8090070000f2144a441210040481d210501d4204031640c480c1041c5400c000300c204149030399100000c10040e901d11505c6403288a9040c400d081502e15290405094000b5625100c403d00000d200b4040300810b10694030250008401403280003910b544c000c1d41c070107100c200007002d901400b00c0f42c2c091b0f100c5c120b88562400c0e4000c00a280580d240b0b00c1c21100f070f0308081c110500b4541c8442d4192000310040c040c25010700113410082d500c642d8181 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 928041447 1250 928040197 928040221
    0x18091b03020a0f080c0d03050d02040b04080609010b100e010314040b15120a031b0611030906010b0304080d0c02150717060f0108061012020a0f182103111005 69
    0x2a2203c8040d04505a040000c50000b20b00b007854500c0455a8207030074045403c0a950a11030301c40c3c03400310107100207000701d04009100041d10a40b40082c003110340caa07441c9940e50307088034180715000d036020030440a40780006109003590041120107140114640c0c140054542c1d0b081002e41d4126064000103040112504402010000c040802c44200c1800000d0400441e20303040741020103000c1211320001c6285513024100d5582c001c0e984000308210300490b031034041fa40e54200741e68a03212070091800002c0d0441c20501074038000c0f43c0084100d450f0550195008008241700c214250542c003d6405036000d403818416207038030441141c0c0304c1c3c60f41001c07216020124803800410707562080301141c103c01c08a9030300c5036295a001d031056649140c2582628011b80c2e01d01051001110060300009020b1030141e0301082001035041d507501c903058160207e54107084403410900422140200c00c0800480c02400000e505002501a00745215000d00d500041800d040c03408006e62986c070745981c1030181c040941 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 928042697 1250 928041447 928041449
    0x41d060709030b0c0a020f1e060108210d0905010e010f11190f09080f0304060f1b12140c010525050301050609210622050718091b03020a 60
    0x7032404800075810340d5141c0419080240c4041c2904002254000509000704045180c5121040854001d01d03c40070311040b0040060881c4d65050058600016030322100051100c0c05048010380c40140e41c884840380e4480d43c01c08800c000c0d540b62103030022804984284110701c500e95042c400464200c6a64040609039115060455800303401000002c151b82c8600c1c4281c241034040c2c0c5822049854441341c2101c40401980004815008800309001c90200001c0148101c1e507458407008103124103444250340e24210840d22080801c00d40703c4080c00220a0101c08089100c103080c40146030400d8010681c540c0c0001a02084980d03641040c03020ba900c148000c86130000c0124041c501c21403402c88010f190380410322032107003d00c8000c01c260406558140c15040c42c1d8101d070001180b55400c400c462590b442c42511710000c0f4605a2141002c0c1d41c09480c9010103158000c4024201640360022140f40c658100c252050b03041d5491382a6000203400c000c070125501c481c247d04083d03040c19401040201085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 928043947 1250 928042697 928042711
    0xf091109060d02012c1206070f030603110d1b170c0603090717030d0e0d1d3703050303090c040506150a03110307021b0409080913060302041d06 63
    0x1042d224280140e9000e0301e82603a504000c031055610203000d8540b007001054108100e50f1000003440841070000d0f0014515108a00c1e507038031032201001400d401d070300b01d62440c0005800303001c503690000b190b800c0c605200d44071035109801e03010551880c0c0d42d1005003030751240c20909001c0308450401c6d100503001c102e0020b1803001182c88519600300105059a40c0302da0b40309040200b0894407401101c0c800506c00c5e9664400740300405c0c400b1502d88001075499018042150010401c0b02070b50b0110340c01c02c1803046182340e80c00740103410626102c0b460400030610b51015800c01d950044e0364000040c1001034604011882040296202c0c18400d4156091516010a1502483c81c083c100400c030340d5940f498050386c14a5020a5030b48088414080307000e0710082c4001c0d07600380c07800804c1c0002d5030750000700c0c00324003101d40303c024801000c150100b209690f5011405400003000780050134a616141240c98110800b09500048481e602d030f02180c165468034062055621b0351180f00c0c0c0b5007281c180101580030603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 928045197 1250 928043947 928043959
    0x2041e080601060c2907030f051305060109020c160b0c0714060409020a050c0f070f050415060813060501090617010c02100b0f040608060117031315030f09110906 71
    0x3c101440100324610030200a429002000d40d4551048803a00e282002483c00f00400c03e0340b440c2c5402d024010b400010440510b40c1c0c07034600001c0880007049024151070f64050060015a480e00d00084080c0d0059200c1d1046030007000301c05421861b030701145800a10305010000c2e103400d00b074101c0b6030401c100c82d8841825021007021103002e6586040c1100d0a0311000d02005807140e100c04821542070003a10031903101c1d40f150401d850301c074a5000880c00120382c2e040401d0b005c40c2d0348650034070060781c0320340e4824843c80c1c01902080c03204070701600107107500250001501c44001d05a845080981d442a48101d00080e501e03001880b20031800c0120300c2055a0110003403000040c5034000a5075a4214110103400710b99a54800c80c0540e5007188102150100400a102507a1074042480d190301080c03041c08131114216408662225010040c0e4000d4908041491100340ca4601c3c0102c0c81d000700031000041564030300f9850030000b0300e88a4440c05602490140d600ea40313074201484032004024155070702c140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 928046447 1250 928045197 928045199
    0x1809071d0c070210030923010c0201020f07020f1c1a010b0f0909070311040306022101050a0605030405071502030705070501110a0303020d0e070e0f01050d0b0a0c0207080102041e080601 81
    0x603803181c0844a00302d0341900c0340460304004801c00c50043c107211800501e4815280950110705a000e04a00c1c200c400b2540204000c1d5054003050b4203d01c81c4244007080d00806028180151901d042e160080003400741c141614035104d00403e6550140003101182c3e40414142070019002071600164050040d182140d0300c0c1c44a991300f541ca4034028140a04c0c0720710081800910294480e030007601c00102084c501c15100d40d207a00e402000f940000c004038190a0155070008060705400c3c807183d040360301c040d200812060800c601124031f0ba0004000781d500344107040d0b00094020500200c41c03ea8070300395016545503070681c6065410305055030b004a0400c03c1c808048010002c01040c195007071641807d0040e654145451101d01a0040180d060618000c8810000d903a80c00d456015108100012190055a895400300884101086005011800d42c14001041901e25078064a10507240d030044407901c175695020070b400e9a01a40114044d2210301004404400480f030403400a8680c1102808242d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 928047697 1250 928046447 928046461
    0x1a100f060f121e0204080304030204180c0509042d02011710061b050a060903080f090a0f020409391a0f130f030b0f1509061809071d 58
    0x2c90301011801801503920500c1c0c03902c098003030f00580c0c5901814003040d526544d4500d0281d480c0c1e0081d00c0145d029900f400060111100141090b84509602a50140f074060030b02c2c0601a507114001e004944a01c03122020384c00344504450340c155400800d0041d19480c4600c3d10004100c424840e100d5494018408103215181103048a140103842151604c4086c440034494581d42c0c0c03401c0305001812a0081400710000d0007a236400000005011392030311030403510740d0f103601380041d0703c01ca03240703040e54101c01c120300d001601c04004100300071700040c00803c05440586401c0b0400502d200c2d6890352664010b440006211080122030383c144520080340e01c840d1a1a8650030b840221200c014840c00d0009003443c103a0490398140d880000750b4124103d006a1038030350381501c4500f1400140c038909140c0b00010501cce0345000441e8450604203601d0655000d2950501004d944094003d41d0302404622819240c404054040343c400c0d8000030080c4195440c122002c0c0c00f86801840d00601604400c0400c100c2e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 928048947 1250 928047697 928047707
    0x60b0c0615060904050901050f09030406022a031507030c022113030503030a0c12050105011704021507050a1101181701020405040c120f0c0e06071a100f060f 69
    0x20041d418200701c0603811181001403518415940b01d01d0b8040d05d800f0134040d184205611052013401c2044030581b80341c5821031303140c0d6030b4091762040000590025540d00402c4003d00079030201008002d10000b61000700340300003410459266142240054948104144141c1c180920704022200d40050450888400e40328551160b501c2c202d8114240c0c00141c407500000b204080750011600301040c0d03500c0341003510290f00076180e080890800203490424818840d8264440c1e18103c50f0f0584843d2400704501020400140c07009205903407180e042c038010040314000f00c0041c0705092103100909544601ca1a00341c5080545920041c1080003800040710404000c58070003003520f0342c0b50305c101c0c2c54050008620f030180c8261703008903400034241041c1d608030541000700c00c01c10b40d030203480034070482d07207070850003421144178095500004420780319683e09801c08000420032240144d0700e4580402c203511641e10701410071380e002500d001c190101000014000b41a16001e003038986441c0c00d0a00c0c6050001b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 928050197 1250 928048947 928048951
    0x1180b1204050a020d050f072c060f031b190b070807140d21050708060f0a0f0e160503010503120c0c10050a02010e0a020d06090c1a030604060b0c06 65
    0xd900940300c003080a00ca0100a9100310344c0d070003800070103440603e02c2c2290300c4581a2200f0780d018402e62401090b40c0c40303440c42c0103105810903614505180620814543c0c500c1c0084c00613a0800241010340010791028172455096828800440b031302510101c040c0284200301d002c0084034030350554010711110015400311a010380d0020366443c0c980c40a41401c0104005160072181d09214101d10090000d422000d00d0220040c0c00d444410114100101c040c15202c080314100009001140003424030b180050541007040006000724040c3c07910b5030240900c070106500005550b501070410801e100c0c5d00c20502c48600d402914029086501d040007085d40c40b001c00754000c5004a01040c01814250100425515010010440d03400e042072204090240e5001180c2c140041d420907450410607940095210300e4540c2c040c160400d2103180c1c0d111000203080d071036011a40c0091820001074041513222421340384988011103140c0c2c138104041003008640d00303035001102111003070002c1e060020340464501c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 928051447 1250 928050197 928050217
    0xf3003030b120303090a030f1719020c030310050f03070311010c02060903030d0b0112111603051308010b0907080403050306090903091905030601080705060715060f031101180b 77
    0x881c010030140c1c00140c2064040c2100e010340e22010040000795003002422008041c001d031a10001000b800c2d504403103541c29410741c1c80b0301c8114030001c98210700c02403000c28103c103c0d0450040c2040802e904030390440d40107a5881107a1642d90303109000e10303d403411204160b280200c0040078501e245035034411103905550360075414400b08240103002d54079079000312400035000905a9039541c1030f1602c07100c018400c5203681d50014104200d0300d851901c803031043c00b5081c00d00310b45107420040b041007000c0840c801c0b02c9040f02080300074011800714501150719040030313014101c00481d9410b0114140722007550001c01e204200100c0f802408040f90700310088907001f03002a141440f05a807800c00741451445900c08240c5c0000d80304048480b498401700100c01036440403400c1d076a241e40c1c2c2d489030326610140c1d03002e9550711000400070b140000307032000210400489100380200d0310300c0da101c800c1201001154400d03900c0c5410302d018161b803507078003206403014080080c42d8030700d11504240781c1c862140203801c844 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 928052697 1250 928051447 928051451
    0xf180509120903100f091103010509030d11070210020604061109010507030f0903080f070b0105060f121503060415140c0a0c020406051309020a12030c0204091104060f300303 76
    0x4065280c80a001d6441340b08200c00c400d02841c01c9440c10800100b400d0070058806031490b005420315464103001d001d0156009000039030138101031518090084c02010160701c82a1020014a00182c9807500e190480e9181074002e85000d10b041c1c1820b10036242c0111402020310030400082030181e0300502512446900b501e4480300840d0703100750a8842088540010380200307004120008980b01c07480080c501300d0320a4804002c680d0780c1d442401100d01455103008030444017482204c002403800011a0350145a5180344103541e107611b0b0100e03081070010740b002c1c1d4461440c3c0d043ea00303020102d409100c031000018011000703180b43c10340c00b4031402e0045035100010450f00094902c2503540f190446005440010a500d00441e25241008000d00030110b0490103500c00c1100010401428803d003250503800d600c0700202e0b071581d9401c0100400039400129540d0b94010784162142e101e510880020b0300c0e40410f900d03051810310f0071482405040121107144240358000d6020142d00c243e0f52000c0456140c100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 928053947 1250 928052697 928052707
    0x3030203030414430902030601090812030103060b030703080f03100608060f0112060b13080f0307170703120c02010b01031113030b060a1a030610080c03070f02160f18050912 76
    0x8240c80500c0a03810315013a0180c034440c04508411560700940c06644240c8070254410b50b0b4001aa407510034458038458115000d00041010802c02c0c0c002000350703a402003c0d00c0e030302512a0384540d11a003141c2180c004d24400071040003a1052500881c001074503007400d20400900c1d0240001e400c0000e61200641081014418000e03190312607042a400b6008030b440c0d41ea10303282c642100765020b001c41d21410310140f0610642a0620303d0102c1103030f841c203401071001c0e915040091484e0804c0d6100e01c101b1010058039280f4810140030354401c07941090080d60000c103052548500040c180c6a8102c0403001100c8100000e2406080001c94002202d5100e075100d20aa9141400100e02421a91000c1e07807a5a0300071001103126040c0004500c14001100c00c02c1d12012608401c0f1403130038048a4903100c80070f080011944140c011303009206002d42ca407044075008014034032288c0b0309034a40c2d885440a07640401d42442000003591144402e1b0491410800c11031808518807a550100c0d41440101844000f42c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 928055197 1250 928053947 928054033
    0x60f06121e0705030d1806180303030b1302030a02030f06010206190515090103080d0f050705040b030402150d090606210209070903050d090509060f0a05011b0c03030203030414 77
    0x4003e00004090741c1c1412140d0360007900001c000541c80c00341d00488600880e00f00c4c011050b006400c0800001610303694115902580100036103030803554800311410b00711b07090140c82d00065208201940002d612820000c042c0b901940001d481f250564001000b00300340c903040c48003010105074001e140444c82d40c0b03800c01070f004000319864840b50403042c02c0c00041b041c020718100801d94211807038410400d48030154581d1045500c1582d0700e80008204010402440f000030001d950840d000030100301070301c4540c03402d6a10700d5101480e0030450a0b2076005600c28021544181c1b00180030b509000c07070f415000f00c3c82d001841c45115400070b204500f6000481d034840e04c40e564641c091540b04041328564080403402134600205131240c117110381c01e040005001da091085680f03109010262644590320305002c010f4986203115200380f104101d55030304440100e0300000c0c0b920001c5000b0340145940382030900b8042c42201d200715007c0b105034803042c540761041619070001208603843c4180180b01d100c04c45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 928056447 1250 928055197 928055203
    0x90201120c2c03030309031b0c01050708030c0c0610050a05060403110d0503120c0714191205070206070b01031a01150c061d0f0d11152205060f06121e 66
    0x200442d60544804010405107090000040180386012810041a4400102340315994146280030360300045c42440b42c0c8001500c054003540d08088d2120040f418282041d1080d0b1820104445c45100038007025810802d41c20310315141006804140c40c018a424295121081040042d20500b406201d01000d11303028054240165201181185542d0102e41800341641100360002c0c502503411034800c3c5d038405c1595400080d03408074a400303260245111100ba444e100d500c0100441d0f40c6080c0403040111000680e00c410041c00007034840c0c49001100d50560410300204580c00c5e4104e00d00c44e4880300140a40800d0048100d01d8846a241c86107810040e442c040003d044074104560a00c0000e00d1507065503080403901e034100036113140480b03031001851030302100d000e0045100803443d9003110301000c00003050000c00b207500c505a541160500301280d048006019440c90302541c07190002000d00c41407003d20180d01e03402640c101c0d85001d9804d601c400350364550480048012803882000b000b0303c016a014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 928057553 1106 928056447 928056527
    0x90106050c0a0210021914060f040203030711300d32070c06050307030e0705060301150e13020901030e01020435060a090201120c 57
    0x83c0c0038070406001c2400700c201103005a409240000e207400900040d42442000c0490b280021041d82c2070030500301400d5281d91030070301c0040c40056a800025a102e06070051881d0b5050b000310070000d0100c80315012182c08403c000c110f21800180d003940c0320b4030400c62400c10b440394107402c0c0c8000c07a5a00e52845803c0c144413070011030384500050841001841e000e1080d6440d2420748103403101031408283d0b40c885400910300100300300ba09507160284206036042c0d080103020386424200014401c1c04140a0b02507400724081d403403080c46106d800c4068900350040e081c2c00001500024fe030780654040013000f800b203810030981c3c0c4881c010501c00c84003160410b030180c10000c4e1028440c00049003400d100c005c0340e060500e060fa40b00c100d09205d5070b030098402000000d200c21580c8000351004000455484c3c540d0700e080000c40b583e03900300d000c100b080c401007254a11051007c000c0b40b507440c00380c = true := by decide +kernel

theorem cover : BRFrame.Cov 927877697 928057553 := by
  have h0 := BRFrame.cov_init 927877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 927877697 ≤ n) (h2 : n < 928057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
