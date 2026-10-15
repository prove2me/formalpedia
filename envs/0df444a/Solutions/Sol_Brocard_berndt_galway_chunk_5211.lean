-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5211
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:06:40.165589+00:00
-- url     : https://prove2.me/submissions/c32dcbb0-c670-4c7d-82af-d331a66e2235

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 937050359 ≤ n < 937230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 937051609 1250 937050359 937050371
    0x50601030b09072a1b12030e0402180d0302030301170c03151909030201050f0a021e0f1b060403090e100509040206160c141008040b090a0c03030905091e0a 68
    0x1042d90100e24131003107600365a510005010900d03201c054000902d80d0042d08259403000032580c03000d40c15400d0320140d49a00d0302c0b641e1610b8101400007035003205640302e02d902c0d401003041c0e81c0350b1101d16000444510a038007441d0b07258100444084902c0207206000d18581c400000f0703002c01c1d01c001030814012440b00d1064106a40c0302c03541807902580b6030b0ba00048007070408801c1e404060301500228001d00e213000d400e01c6941c1c1c070520050704078011800000c2044d0342c90140060000c00410040122110008155141881c4404d10140e154094041e440c015840300301044181903000000c8400740410304540d80740c500702110701801c604810300500c0c0c440c181d500049811542c904007280c000407111420203d1a0700f050400c40700802c564400c1d500c2190802c0c1c6400582c5c030704190070703041c0740e03081c1c0e2242d80b4107841b180c84100b40e1103002011180c2c07034032480d1494808140401c8006000754400ea990ba10000e052606100001c2000707000740b2600d19001841321040f006420035180d00c440026070000d10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 937052859 1250 937051609 937051637
    0x40f05010e0721210801030c050906130f0222051804050a060b0310050f09060106020c061c090b040f1118060d0f060501090204090608061b18100e0301050601030b0907 73
    0x351044035611201132503415803001480a4000303601c076040700d0086047c450b4045e80c905c01d1005061044462035800070b04404400e1340c0103900d42c4545d043c07008a1070b0050410120007468040c058151480410580b40144100f0030780c503010f00b04405c1b11114404044081c14a80d4980b03030740b919000c0c80103001c60f4841492070307840d46007001040703204c00c40301c6800c3c082402c1641c003400104805480c409664001e040010a000b40001100c4407065000b400d0a46044c0802c4884410b018840346081549612110400c0204986211160250307001d190440784e400310510388a4810140d1400c924002c03080c01c9105907800010711038040e40103c00b03460300c5041036100c3c607003412105819403004101d10b25100010502e15003503805001030340c0c4803000c1080700da0b41729000250755480407205031109480398135020f400e0414903405400c025001e620340503c0c4000c0c6c200000d40005445001200040c41a059468030f40b0b024003c45e500540282010003c849030003001c280b04e0000100242e09002515410ba50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 937054109 1250 937052859 937052873
    0x2d1c0c1b050109181b08040b070f020706030209010519032408061801020705010905060907090207050c10020304030f081e0310171009081210060815120303040f05010e0721 75
    0x2000e44021170400d01480403244c0242c001141074506944e0000c1e170b40009042e65002e100300c00d143c0c01d01500200300e0742c0e10b0900100c019500003200030381000414801850044403090b002d043d000629140440c4050510b450b640d4040780c0142c1d131486010b00c10500b04500440403c00e2500144403550420184000d0411280a44941400100301c1d600c0c1820725801c1c001c02084d0540a00054002d07220029a2540b48806a006040010b0525013000b074102c1400e103442e01c0e10300704806c807500540381429500e03110060424400715040d54560400618003490f02c03040a549045100c02100c020b065091413190011140c4103400352441c2d4448443c09500303500e9040000f40c0d452402ca02c1d040c441c2206034507115640c1c2d003006090060b50940c040102e0450f0801d486103006a034080e42d41d0107580d43d1013039891000c070039025103203c0d040500c040c03040c140e8160500040d40300c0c5010f0021940051020b29100f0b003160a0001085c0709900b14110a12030302880c00c0700c0d415401103841c2c1d0015200e504c4d00f0044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 937055359 1250 937054109 937054121
    0x6030207060908030f240a05040c02070b0307051201050111100b1507031d030304060c15110d1d03031012080412030f0305092d1c0c1b05010918 63
    0xd095880c0110400010001017501d05100b00074090860340e01010003103000108000c480b107050341c0000c4089040c4000d0519074040d0f001c05485104440015640f0800c103945c3da4000e852800c00110000f4504018441814a10340100002e1800350044060101859160071001d0b280c110003d8940c1c06075100e680e0b032652100714803c0701092155031401c180c98040d00b1958182c210034001207100801a402d803030f01106840440d8496140d1400d10715042e5610b0007600c0449144060300d07a03461380f80850107120350020349120700b210a4002402e1003c24420210401e03d9011505a5030003001002a0300c18252040301c101d03001a01e80301c041480918044840d4015034016a00300c0c800000c0040c28954800c070325001a522644081095171903402600c6d803107503001e000c007200900303820035440305804007070a6044140c1010400c0e6143c800c40362454044211041200000140c800810541803103809041103280340c0e2668020000c0a1614002030701c0000301d44540482c1017200401f0200426080d0012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 937056609 1250 937055359 937055363
    0xa0b0f0a1e0e0114101a120f0f160203090d05010207080706020307120606020a0233370e1302120f0a05040213051b0714120f04060302070609 62
    0x11641c1100c0300e0140000038500c08064190641c01d00402450041107503030814003c0743c04510318000e081c140941c86c01c008030b0303540b0222242030b020050309520000c02c4580902448048841c00b04a0410a4401c102010080c0003964405071100c0c12006850f000411a00c580105842600340f00c403107800c0090080c0102400075240176000541103003000056030007948074001d5a10341101500c2a08000750449003d030041e0009644001108000352621003128010b486120015000f0203000e0040600c209034a00880310341c4030804205141c0d402d101c000381503000c0958103010090008481d02c001a802014601003041c4146120005c5003a200d0f40072107140500c0e500f409641d40c3c91036551400600314116544450303c43c01074045011880b69000340c0b801260000c1c002d002440c01065500014180500041c08100c010700066120b5142d020103010600d0080c890714400501114107e0700b8407042402c203907442e00d820080c0e0407000780d0342020342c1c1c01d03181d0074580142c8900042c0741200081007030f4400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 937057859 1250 937056609 937056641
    0x50601180305010c02120a0806010302070c1d0103110f150a1806020c0307140603071206050d0501240510120b120319020c010c0212010b091303030507020a0b0f0a 71
    0xc040300707000054101007031003107981d4210b48031540c0141c4150814041c09006000085005000c41c403558803039001303001014000c04000020507510300002200081c0e100c00c03c0044001d900c010002e0242c40b00c3c600e85500c10035142a0801c1d003aa5000032000c80300712034034141c0d41c1001714000079424031614880c18080c85a05a00142c5525200040d40c0c0e0894214001d1083c480e030500868604042042d00101c24409010300d8116100c128064440000704100180500d98078840018550713039504600d5002c60040000240080f62801c90704401400b241c44049a4004603104019984820103030042d8140f0f14035200189034052a003401c0030308941500d03158803500048030b480c54814044002d00440b400304038244040c080f03089041c0c0c1c903200088030040c041602c2000200140c14101000d12414201d800005407003404d40c00040e80320324080d140701c100b00690071044000c0503058810f050700008180001d020300c01694bea030040b07000d07000b03114920040c00c520114182c40c07a142c01140c816100c0b081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 937059109 1250 937057859 937057907
    0x4150504090f0b1e1b0301093801110610030f060615271a13180603050607020712030309050a02030604080c1009120f020709240504051504050601 64
    0x4407441c415041c1300754040b5003030f40d404003080303944640c444022104014000300707900b182c0c070f80b0301700400818252600340c6070b603248144200b100040302d29202e0582c039822408404440d8001d40010700142003403960b1040d5130301c030000b4802c01e490480d001800300c9a01036101101e40ca594a06400a0091503000038080c07050300c0030716010b55401c40c610380d03034465128200454818041c03480d0320b60100103214007c246011040701608260040009004540401107585200e6658110314844142080080c0d80010b0b606c41d414800c1240c20701040d50044010304c0108805800c2c41100140d0b060f401c64020107041d524803030501008018071500e28205d40080c1a07481501e064200301c1451752043e41064141c0c080c000d8115004178092240080c100d070000001703000603005220a6070002c0500c8501015882034410000707403400c0c1030280e11070b101c3c0c80f4014404207150841c015503000c1e0aa1b008244a5030403d400c001c2080325403240300d0404001124080b0703854640c400141c50490002405140500d4908 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 937060359 1250 937059109 937059121
    0x307020d030e0c180a150b040303030b1008130f0f03080a0f061428090b010806040b22020c030c070317040e012912090c04150504090f0b 60
    0x4604103426040d262400e0003880d042c0d030020360700c0707000d840c05255000c0103040c1c050031039003902c07443c040d40054001c0e00010304030484040061900500d0f44920f8000310f001805104042d414081d480400000f07542840c6103d000c20b20140c00301034010201244110502ca2810611406072009610290401c01c44660441c2c0c900300142040d07030440d0802c40050030300113a00d00c10b048500c250000c07074021034038a0071025170302010021924034850520301900c40c20302d00701c18455045191003004180841d000965080321100140c550403004050721301c11031600c0f081c54110389078000d03a210175852600d09001d40780080344040c8000d000c0c400b0720b00518400418082da040c100081e442c01034a000d0700700f407205400c10b070070070f1441841a40102004d4228007401040443d0518501041c201d052040d851440b1000c68036130281c940103203100042c85060f9105001c040081031000c080000801e079010b1180f50f08072040355080c90454421640259964100340d01488406a00d0200407070744a1000d1403142003030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 937061609 1250 937060359 937060363
    0x60806040c05060f0f0313020918150c040902090a030804060c380a0905060c07031d03070512010f06030b04021302070308010e13020d06020309010c0203091507030c0602030702 77
    0x11101101e140d04144000302e014035102058880c0d081c082e8401c64540301a0110040e840c0d040074184ca54082c510b4204140140d54a4107002d21074551040c0c030759019030149400340c0c40d120a0290309040c000c94102441040158041100c00350b401001c030141c1e940315005c0108940e800140d001400741d01d000326002c5070181c0d02082c41c001040c000c00040c0a20310181c80b1902c0c1c0c0820350888024407000450212078500032411714294401140c0000251440c250349516044c14400c030b4140f1801ca20006190303003015049850141d80a01d81102c00070b004180201180e0f4440a901a061140201d08203014070003074250400e02d800500c01c4000c2c08520f50f0b03441c0c03501a0240a0320704074440c140c151100711540b941f0b80700f0f0710385c01a05039680c410241d1034003d0305000e000005d025010201c08144025005d0782b01c0b02c4155001d42d20810006039a46890304109085844801250085400030801c02d800b035550a000c0c8000107180000403907440c2050b10b000c1d145038040f9000109218004010000181e0f00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 937062859 1250 937061609 937061611
    0xd051c0905031501080307170f0403111e0d1b0b1303172701090806040b04020306060a05012708151005011110050c09040204030b0405070b0f2506060806 67
    0x1030b000c03030708040750030107002d8030344942405014080c4e8418000c070004039611565854000589119032403602c0e0300c031220035a40354001d40003660450314150340f00d078150500050745040003e0040c00301a40d00390910000760706502d5000080c1c2407036441d80000b2058002d8000c1c141c010031001e0718040d900e00c01d001881c0c10007581403005440000c00440d040400c040c158044035041740108200881c0a0380700100041101e009000c280d04200103048003007842101002030601550196007070188034076003441014601540105181d001e0b6510400412403a6044100e100741e2982162841c140d4090981a6107500041548501818440c81c461240d000000350007042c005c0f494800341e1a01d06880710300655004000000e20a00d5511000f800d445051043e80b0041d0450600d51006281042000000d4281d0308650800d48601040e80f0900c010000200100002080e0300e440c200c1c101033900301450882c4c01100c4825144a0b1007500e40c4100d0080b00c2100442654000b03000c00905440303c5103150364540c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 937064109 1250 937062859 937062869
    0x1517060106090605071401091713050307060e040f14070801031202010903050409020711060c030d0b150304030f020f01020f191103040b28050a18030c050d051c09 71
    0x1481002007072052140c54004162049510303018900940d0f43e64242903940407a58044031035503600b19000000340482d0001c007403105003080d4140c441540a0710250600c00310341c00079200b41c1c0420410001d05401a4101222403021a03001a204000d140058054081c0d140803205208000781004441e5402c940418103072800361503540da140040403020f03402c07128401c10103400710b6024441003000503556002056804c0c070450342107150002510101d45240c00c0f000e40701d50650004100741c02d858480c0e02c40d8005d045002c80d5a0540d000d43c050500c803032440003420150400c44441c85200340c00d4002c01c120f8010500f480001c55450f81c6401c00b0786495086000d200d0400843c10036048241407203260141e1070707500440041e40c035107850010200443d502107455609600384410440f0030350713030307104145090402070b680b40c071a562030a0040007450244101c511040c0101e103010107102040100c150b40094480580c2c0000c18100c3c80d050151038031560100d48400011942001010140e102902000f115 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 937065359 1250 937064109 937064113
    0x10c11040509151311060307020c0d05010b030f010908030411121209010e010c050d030e0c1504030b100b0304081b030d090311071a0703050c100519060e07030c031517 73
    0x5100e4551307642d0080b20000024000350b02480880c1418039102004503005000c40c011a12070700ea411020414400d14a041580da40e5034400c1d080d140741c14144109400007041c0c4c0001c02c08004995510020307808080c0020304178003032040c880300310707900c84c000c0f0101043d120004440d40c0710418452400180d000c2180320380002d000e060210b5807540241420601294803002510104482500440041c1420700807140d440c401c0d20b14140441d1900c1d0030010707040c0010f00d0803a40d00c9080d410a02002040076011851100b0041001c001341d20780002500e81082d4090203081d89c41d0400082890364214510314440140000501e40d0800c08003035122803082e501c01c0d11404616888081100e40710302a600c20b510301507071600001d5042c039402e100241030040c441d003441d41c1003546892a071854220404907107030202d6910424080f00ca280b03c2e8442c2540700d07941c141480801c3c1800e80d5041d01a002600c801c0515882e00c0a5880e0a400303a0000b0101e15203400f81d4010f0b0b10741c0c445400d0182900400150514 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 937066609 1250 937065359 937065361
    0x70f090510150e01030f2304050601080a020a0306020708090a0b090406050609030706030e0f030316020c04020906121305010c0c1719080c040801020f0a0216030201020606010c1104050915 82
    0x503051030b03040308084060303911003100d462528401900039041184070b22140581d84d065400d1140041600c10400c18011303084000c0c10b14203454103510b09403041e0804810ba920201500700140d903901e18110a40e6400080582c54003a9850000240d01468004650040b8042404250b0440000203001115000c41d000c1c800b1560343c0c0c090142500ca880c03525034250f00611014400c1c0344c06900004074101080c011201c1c41100f0540c034a04580040c2c42420980701004407000c29190304000410010b442154214a071001110005001e44241400e11650700807010014071120b21600b900c00b1800d800400900c01454004c5e0024031000100c1c20803540c41c1400000700c44020700c0316055070881707000c0800360242003403d0142510700c0d0300001c0981d40c00030010000401c4c4881d085c00640040d610900ca1251204520000642040d00e542941041d80003060800c00144c0e90000d80103400103400c0c01d000c2e013403200d203003861601d059400c44582e80242c10403040c0300700b515000900001d075440c0108480c0e0b00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 937067859 1250 937066609 937066619
    0x10030b030d03090c150512090715050f1b0c130507030c050306030727020a08250806060307030e1c1e05030c13030f0b010e0702070f17070f090510 64
    0x11201e82e036102415824200100b4403505c030055410850258003030511600b130580569a452060800b00c800c06040c2c0c1040701b04010a038000c10706410f0f460b0b290b041c001c0c20004a80948040c40c00754040c0114401101d2903840b0039006d05000780c254203000540701600c85480c82c000c070b001030103080c0c0300c41000130325003408103c09501c940b05490241400901814a962410600031230390181c8100c0503089035100340031001120003502c0180119402915500000d1174071580b0b0110300311000c210b424500100d1170240c89025442950560300503c01c5804076102d40b2407a00440041031060749500251161112180074009414598076100a5075036405080300c0010b560b4034400165038040701701090003880425000c010000c080c21001c040c204410541959a40380c04040691071031040d1014480e040050000c40328651400d54802410300080c040740c0e107441c4030b240618019110381c1c5942e011602801500c4101800703110014251601c013249002d0700c44501c030000b0322058528034009a402031000031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 937069109 1250 937067859 937067861
    0x12010e0f1609050606092815200c13021305240307180e1806011409060d0c0e07030605010903120e0d080a0c0317100302060a050910030b030d03 63
    0x500c07480c107451001403440d0050820141c036025009950140003030000c068541c4800000140303060310b010a00109103102e50502e60505180e03041a100c886120580e206555048a17070081414a5060700825070110110300e507090a08600c136465008501615050002d071a64000e4910360b5201401e0720421940c6008102c0e986000d1021591040c0d114001040310f2001c60f806598041d195082c40c4008602001003001450550341102c001a005041403004c51170420303690050111200c070042019504280e104984102d0425110748039080003c0081c51544a450f113180040d41c1c0888800c001c941c5404030f1803a1a5400c4558000092070300200141070b41c131540040c001c4039042407001017035181d0304000b03c2d1119488014540c03c8202c0030707040d8000031107910080a9030a160341c1e5103001d44030189402081c2082c0704041c06603402000d0103010030451030046510403a45c0c101d60181c1d03140c40c0c17108107640340d0054104495204000d40042081e4a801d80c00045030710104800751041d031407800c0d0f0154 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 937070359 1250 937069109 937069123
    0x100513230f0c280801080c0a03241b0903030206070507080a031d0604060c03110c070b070309080a0f03081e07051803061504050c04030807020f01090512010e0f 70
    0x5074030819400c0861403481003080245005505840780c40010000d80303102c0d45050381456119000202031000400c6081e0040c815100440700481c1c02041c00707490354940a411812407005199010002106032201040307a40c8500c0b80d0b5080d00500c40380780501800e0140c61845039101c150058010314000900c5184104110344807241d000c0783c3c4605205c01281c2c114010072440c5221903055800d90b10208107013131b0400141d841640300b20008a03101c1200d0070700800303907480040b596001030340a218118800a000c0b5007041603400c3c101d0055111901030038101e03010b0080350300142084c042d0812500a00c208850405911402502c441e4010b031144080d84003500d01c000e00001c1010340590105401c244640000c01e200703031039003400008500c120304c0042c1c1088401d07035400e000b040e40401c1400d1141000e010b410b83c8202100303001802c5ca491030711203003407a10615100920900c1e030315001d007500741c0c000d42412015002c054003283c026600340e42290700801507011341842c54800c1c984030000500b0005101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 937071609 1250 937070359 937070371
    0x1b0f030f1803030c0206070206030f0907120b011401140c0616080f0403200f0c0a05010806090c0310091d010b0405090316050f010e2a1810051323 64
    0x611615450b41c0c4007241c4c0741003045400c0340e224004000d44070140c2e480002550060654225a5981d810034403800c6103050406c0d803055074003060704154003000c1003d804000341110940045403030011000f0004850900510910180c0c069000c40c560040450000d001032080c102869040940c01884005443e00c0608441c440d0845900304002000248541c2e00031504840c2d02c080c2012840000030440d080c0613150015004540c4808070461140c0741c400100d000070300c000c0c2420703488c1d800c140f0007041d101c110080000b03915a900001085078002e0740340e40d030300c001d1142e142c0401580010840750240c400440010306c0c3c10f5800c100a181142c030b028400c50b4010b40501000f586032000346100d40803c1d1072401001e1b07456014840b5118501030b800e005403180301d1840c40c047d00c54842d0054252401c41528403503079003001c6040500c4042511740f000c94203010710302c220301110107540d0103003491040e021a03000103070401d14941031483c04080c660800080f080382ca10307480b180c5501c1d0280101c4081803c0300c0d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 937072859 1250 937071609 937071647
    0x5070506091f11010204060e0a1707061b0803040303470a03020406080a0506100e0c220303110c1804032610090b01051603030c1b0f030f 60
    0x10b80c60402560103940c034081545040000307400c2c82d508082401c82e007155000401195020401034424a490710354035005c0e0465030081c26124407042e0b0499034402d0b50b8040e070740900c00d9150f81c0c2d42c06580c041c8080c820b05580080103a0350b03407a080c82c0c01070150902c2009000c401740003048039031000000032003060111012400040d43d9901d040c0262440d141c0951078a500420203076004030158465004903005004004007e0201943c18070700a0300d00701008000840309100410244005194030b84009d030000d610402c9103440d040164112002110b141c2c00701c400c80c5100d1b100c008100f40d00800a9454083c0705020f850844810303900380480b040201c4003140590b070000c0006000240903c42c40c1602510304005c500d0701d030028081c010300c1000155104901010740ca0020000384499004482801c9802c0c0b034041e00b03004c0040c0d900d0030103800000c001801c0c1602c030a201202d0714403c2c059128243d2800c0c070043d0002c10035040081401c5d811410940000710301d900c14a81150060035101511f40c00200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 937074109 1250 937072859 937072879
    0x702071a120901020c330a05070e0102030c06060f04060e1602100b0603130f02121b0d02100c150908220e0f100b030f0601080f06030d0509030a0c03030c0507050609 72
    0x1804076107a00d4000d48944d04c21074540040c4d91040b00c9a0000380c0703d1f40c41c05e00001072600b0500d07005002c00c5410060b20b8119031003000502805000407640030303040310701920380120100c040310015020300183c0d00402d4210b2001810001e90f0580131040c180a882c844d0242c425640304070640e9403c1d00c0403a10031030b8005404102052140350001004014940583c1d807160707503a05035900145005843c000c14001650058480b203a14855007151940e4904c4202c411800f690300581c00b20300d10305440c0d013101060100d0394000c0130603c00c40513500f10301d901600804120038034051600030b0302904071034104c0c0d0001c90000e02003015016800007031015600290703040205542c0d00d10090a1200d80145007049106803400c001440408102c00313540281010240f000b100d10742200010700700c0800a2500080c040c4840c18814140c5007c14907100c5082d081c5481e980e1001d050000c2464041c2d5034000400d604180940001030540c00240091101c0c0319500381d8003180d580d9005c100080c081e20310400d030b10003c915 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 937075359 1250 937074109 937074133
    0xf091c03031a100914120d050301061706010e010c02010908011806060e01050d021005042606130b13050a0c0806090f010603240f091101090909050303010e0702071a120901020c 77
    0x14090700086001b00541442040c80320281e0400c1c6140f0043d002098020005120903908417000e0040c00c00304034030210711443c10400007081c11103aa0411814094080e5201096911a004220181c1041002400540d030451210b003511018050190f071f800d80b40403030100300c0c44203100c4082c0c12102c0040441c50412025002c002e8504400e041c071005002c0104000225407840229040c038820030703220507400000380d0ba81903e00b40708008140c0300c05d044885000c0e02c005600d181c041c0350004030b450404001c55103546840c51034500403c901801101480c4400112043d000500a210b04114402c0d900131109880401e401d9680714000200f6112148034184c60f1001010110840300010000c04a1f0824540300601c0841d04280070035a183c3e15120f000c001107580003201000209100d8104101d2005c143d180c0584901041c0074052810165001181000d4402c02c94000038184400e5404203154000d6049002a0300c8504480309210002c400281c0c861018820350700044030417000f0744001c50b194 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 937076609 1250 937075359 937075379
    0x230306090606160519060b0d0c0b1b060c030403020c03060405060a0911091005090c1809041110110105070503010803070b0c160303050411040506060f091c03031a1009 73
    0x3a4035a0f001074020080b01c400854010006240c150040d04040040756a150030304000761f43c01c0f0740c4210301481c0d440d90510f00203a64500d80380100c030b4507007647e151a4583e0510f9160400c00301b5844402a00c141000e00100a1083d0010750040b4440d4089a001d81099000c1c10344401044401800641092000802d1400a07420503042e05109049050780c441d0040c00141003c003080d100c0701c02c001b940310340038465070030a54020341e04040321801c064200301030300070a452000c0f80c84515034051a4407c0c0490200103142a01440d1101e00802030013070000055030003030800c100c1d03143c881655030030131010800380c50062007102d0694400034055807030181035480380d116402014207003408260741004004440210440c181c400b59100f42d801241605050038500aa044500b541c80d2055250600b4441c665440700101c43d80200103004460f11060201c0004900d030004461144120814080102c20035516a00c0600b402c1d1249880c3d5162034400410300207002800004240406e03c0140180000408 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 937077859 1250 937076609 937076617
    0x90803130303060306090b0403080a0533060313210f0e030a02220608060105011b24020301150201110318100912020f030a0804110f090106230306090606 67
    0x3a0402040f42560b9030340310400c450b489202030380e01c603580b20288810141d00254580c0c00070103503107003032019040040707001400744500c4140540010134001e00200c1d000743c0b42036401d80e008000b0100c0c1e849103886403a210a00d05011400c46c0d092500350720903600362400c110004982d000317503951340e00641e81d100d0040d5440324400c015160b143c4502d15040c1c00603600c401101d40005501000c016038000050602e0050f01d1058108009a412001c01480144d921601040d00c41011803c0509920803070f0500710051110118004a0b0307203103441080564407201e400550481d0307000342c0070408800109104030300302d4846c0707070200704032800800200710030a46201a0828440c644410384c1d0408061104803001c0751010032085030549110884d5400d0f00342c040c00201c1e0740c5120755000d07519250820000424890300240001d0a4040002c0e0b505a02c3e190a40a600d2140000e00a0301c5079584884021b03143d11390061107007001d9032034103140e8075aa010801c2600c1c054a0301801e009240e448510810901d0b0304 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 937079109 1250 937077859 937077863
    0x5120702030f16151b082a0f0c0406030203150c0f0f1201050f0f100306080a150506010503100b0d02040510180b0c0303040b07020a0f12020c0904032f030a0206010906050409080313 79
    0x20401c140601101080118003a914040400904030123114505050804440d01d102510480c540b403020030150324082030001900c0e6003981c0940041d038800081c8112809440102204181c1c00329244104544040007402c0c200c0503030a07003041c03d82c0d0741c00400810301620040e440e0824a40c0c0c1c448061401d010700780b41c100682c0c504000c525241c440d1042c92510300001d40c10398444400344040000c0501ca0321505401c070001303203001461840c024901c020380c15200d00c00c1007400100012010303641e06031507050303c0141000400740e55600c0c20403c0d000300b825200030707846480b5a100d5000014110003140c11220b011a1300070103141150b80d5070b11a0303105410020181425030040e0090300000881d15558041903e12038420095400b00c02e2000a15000c9141003080c00341134003105000100760088110700c0d0311000f00040d5001d007490300b085c09502a030b02c6d030514500c1c2d100210364110704030340114040b810b945400c941007280960310000c100660751180350140214108101141d101d03a40c005444060354 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 937080359 1250 937079109 937079137
    0x270e0c19030606120803040807020d12030207031812080715020309060109050603030306181509010906080c03071a0a0509031009060e060405120702030f16151b08 71
    0x48080000c10400c98012000310924022120203100300a554403400c0080c1c1203503130f5201d0300c044241e502c0d01803c1c803000c0c00140800340b0109802d4115541c83d5100e642142d440781c120306c00380c00090009400703274106070422000305515001c1c6054078000388400b00c048800115000d940b0040381c1d01c45583d140d01030041500ea0112000202521007220700003107008075180c5004011542c500100c00c0704840020b441c403482600100140700c01540c4404800f13040701e605038440011616040ca101c104078580e00b00c4c140d00400c5501c0006049001980428215000c00c801d4440c0d240c401410151035801c54015841195251200094600300400140c110b08000703082651803c5800310000c1d2600d0040c41c0410403407911817a03510208447c0303000c0c40760721001c110001c004504081d51180d440b6406500c1500c0100d030041040015503408000f00b2010b01030200c03d440c0041103e08603103960107858061809003e0051054000701071140b43c0e4503c842140c4000803088035080c4d030b0303010036940c00403517100c90761 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 937081609 1250 937080359 937080373
    0x91608010b0a1112131509180209041a010f020c3003040305071805040c03030e21150106090f051011010c030b1201091106161e030306270e 61
    0x1e0301080082a100c420884c2c1c006440b10210b0380915801d000e0313a0004488650f94002101d500781d00000b90006442c00001c030f030314041c0342c0314208400078003503101400e92150400300c501282d0b1184005407801e0010070703a20100c7c1e5140e22034099a89410200300e283c0c10411102100302c001c2c84100c00340808105121a60040038118031000303145810a07042a60309400c010303000c00c00c1c00c5441c80552500710200700180240e03c1d0580310a802030900d80f001030b00307002c0940c1203c1899a5590368038411014501028906012096100c503651001d025410121442030400420350314000c4581c1003c650075031030203d03442030a1001340140580074102c02000d01c59090780c0040100e81c2070041d581d52039074540e0001000d0024034108010400d6685001400340d14109002000c90302c0001344440c03010302501c40540d207400841c21007004d5011044054580302c15441d400c690402d2441049450134069a4113108958681c0c041c1e800d850960100f65a40d08011055083d6400007900030001c034000c0c40c0c0c00c0d5601 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 937082859 1250 937081609 937081637
    0x212070314030301080105071407020f0f0409050105180102070b0106030b0307092417030a081305120c0c062703010e011e0f0504020a0b030a0e010207080306091608010b0a 75
    0x40d05580701c1c85040700b5040440140300c000000d216095018100e0700d45044944120342c40c4200c54072891401030300508481c1d0300003003943c55640000e00b410780054410024035229041450081006642108400c8808034010542480c14000c2c1d61100c0d810184404580c2d18101c03054000b8500c0b640d100d60103024142d40018010b9151082224840080000b01d06050021241e4240389024bc0c000c0800f21030042400010b102000040c0c0707810014904004000345c0380e40f04515003442d00040c0040c01d07841507428019100070400701030800050aa801c0b200b1001e0070381c00700029030003188040d07071910102100d0300d0142d00c0c0458401180100180000556401400d8510b0075104841040e01120849150500d410b650f103120f01d50040051100404c403030308156001810b509118861078100890100101348034000b140d00900451101c0c0008642d00d101078600900b543d082103c0079132140d40003c00250702c0b1504800d40100d1040d05a41c1c09002c1d07801c0001d40b1000c1e800c003280c44000c019024045901c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 937084109 1250 937082859 937082873
    0x42c160e090703020a02010506090c0a05091c0501200922020903060103061b02010615030207150e0a170a09150318080714070b090409060e011503060507050703050702120703 76
    0x2c00b9100a541c05a0785100d00000a4296031010300018003d1580604000034a00c0181c180c0380c408600e8541745941e40000d0001500c1070440d0006210080c02d544024070800c20b0550006840280c014102d0450726031400b4414028003c808480740c120310440103420243c00d84120711003091581c4100107040c221184c01107881c0800c260000c03201c071552440d00500c0c1448040c100e01d466511031001b404010300344102030114100c0f4001c45403c0c1074003c07994038100103c4044841d0030341c100c10010000451007419203683d8003131090081e00c0280d402888000d2000041084612201e41030319075203041840c1c10324405c09426a0003a400400d6a83d0350211800ca010803040758649000380c1c1600e4a4451a090000f160f42d80c0e01f201e840c0f9640104820004405680b0644942007003c0701e001442040b28103200c005040c644070f014011794a09103500075185036800f84e07442981d0203050100180d035180e4000351007901c22004081c010600500c182001407500c52408941d0105500a80c2d1201c1d503241c2e2580 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 937085359 1250 937084109 937084111
    0x90a0e0901090b01090b06070204050414030315011407030f0c06020d0603030519021c12020d02030108060712020913020708040f08030d0c17040f1110020102042c160e09 74
    0x4102a5111103111051201250819001d0144404201b10781c136131040000b0014416071200130f002d03e4903000083c0500a000b82c20503e85030350070068a82e6881c0240c100100c1c011854041c13070102c0e0303405452500f40800f20b4159024590302d600d50a815880c030917010340d0145070307041c6c00300e480e08e400b084003041c800403c0c0100c900030f501c651106902e40301070048801d50755007500c084104561080c403031807a0100c201a1544664500380c01c00c000c40e90510b00240020b842801c541160b00c500000c000250b09070001080c82c4210119039500840e4100200308406a104059049900002c041d2912410480c1c41e402440414899039005260a075a1480d514810708198800c40141e000030030030204104803400745948180e068a0800c13455500c0c820300750401c0300c001e40003410300e2040041c03150402814541c4115441d100800d0703c241500b0a6400a01035401401248030340104558500280190041c4890603400d00c40c40340d40c0142c1e1080403410f41c5000c500102810006007003540f000a845041d035607 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 937086609 1250 937085359 937085371
    0x1090f0b0a06110111070c05010f0c0506100510030905120c03041e0303120b010c08090415080304051201050f06040b190f051c1a181002031807080d05090a0e 69
    0x440d0f28504401d220340c00c40720b02030310b07903800b170030003041444006a071398801c103000d51303030300f4240f02c241604204004c482682d50b13581c00030114401c0505100d06030058040340c0007140d50440b12407982c9400404102c054940500e8010b2040c0d21903190400d031091424042d02115441c00c0440e820b103595813030034030440210100c0b030f41e40d1010f0490051017810362103403c1c0e00860043d01024084a8180f4000a00107075aa280c044c0ca1920041020241c0f0740d201d40000c030680a0010b00d400019842c0c0c8403043d1203074801e100742841640c801c0b69030320004106000e031074032440c108109803415030b8442c01817001824241311320f643e20225007120071810f05200046840942402450b81d440c4ca4100018031480c081d91000e4031800840012407600040e1a0364170411050700c0c180103080c26500c640807104482c4000c800002c0290280c0c100c048500c4131079902440c03143c0e0b505590720504d81c00141000e61595124050500150406802584407078010340042407101c0014050881d695995503019410390415154 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 937087859 1250 937086609 937086617
    0xa020d0e0f15060d2028062006160206100501090e0403140d0e010c0e060711120a03081e01051807020c0904031e0503010f03150e1510080a080301090f0b0a06 69
    0x704c050203040c140f01c6c040700c0100e204041d803100654624040c2c02840c80b48100d03002c220361484500754108050051440c0100355a044030440d040440003c91200c0c1c480784200300602c0703400c0000e5070000c007004201040700e1045e142c4a1949003803901070411508010001d03405c0c00900d03102c00c0a250a11002001c400780480000590003240032000c90a413450300c24003c0c100180b030300000c8015550f01c411100301c60303403151070366000c0c40281000c18030182c0580c00b07131661409100500028541c21811036031041c1c01500840c01c0c0c800381c540360114181000e0080d507030804901140c0c035610501201c54107400001c1401100d00d00600c00300040d2079024219021000103003902c030800d001003916031290527003030070500b801400c541c1421075125001001b403001a2404120f0094007140d03041d107520561610800c24251b8400310700d20f030140800b50006840e4240d04401c681c000040c01030020840592090b07104940500d580d20b4040300c0c2c0f01030070909038070f141e0040e52001e00320039640c0ea0b034106100800541c0c032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 937089109 1250 937087859 937087913
    0xd021203071202160e07110a0212150105060a0203120712052701060602060714040519031205030c03040f02030114010906090b010306030510020f0d050a020d0e0f15060d 74
    0x4002424015191038100031351300b09202c01d0100041c00c1c9080f40d8400760340d1405041c0c400c3c0c010980c0c2e19145102c200a500601d02d2240619180070200c0c120b03500c0070040003080840d03680c0328248010362060007031940042e0014800c810320648036031000c90f0082814505846080702103400b0790300312801681c0c480c0c0c1a041030b195400103070943c00c40d4401405115002003120f41c0ca0100c0203501c0d124000c04240400c100c07440c240b81c1c9015500182c42c041d11018140790418480b02c4405903400c01c840c00191501c41000140030481c1744540110703031183d201c40c42d410f41180c80341e13a6100081764200f003040340d05540b03448070303055940d6030f15010074001c00b48820045910380c600300b243c8044800c0b0750800c81c105070400301e0a0002c43c400040f00780040c0070f802c8005944005000564080303001f09104400c0c0541000d05122034200e035600030b0304442200d50400c0012380714a10610784d981c2d4451a060b25250809a074284c902c5d0900c0c842a584010040c000c210790030425130f03403c1c3e00c000c04180300040000d0041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 937090359 1250 937089109 937089143
    0xb0106080a1b14090307090614041401140f062502040b0d02030613060b090405070e0c07020d02040507031122080c060f0d0b040903030b0f011b020d02120307 69
    0x2c0501010841d0104120800e0940ba110091420301100e030701c003140703400015501641d40c070304010b00b500a0000c4802007140c180c88040c060507031104680c1482c403c0d8108841150388030000d0140c18101c52102e03d0400b4200c5000c41440800e4008900d1154040014003040304103110f80c002044c074165000b12401071021184c410002111282d42d0178038040c043d410f0545006850010b1402e40202d20800001d040150030b1801c40e0242038640861600054180d060208200c8009880c0302aa555005c3e00b08440d951450b548070304c1d02690030080d61200c0c038030741d640e009418149d009035017080c1c01e4603020440980c4010350303c110f1f600c0001c81c41500010342607010504101340e14101d0240540030301404640709144005600360146140300b003c4840c4c00103608061000390350011440c3c210290040c82461554200500103241c00c8403254007170041000c4e0140c032903222b03400150342e410580d00e035411510215001c0c05420002000c0481e00002e2648001d4004c010800150100340e200c0d4000c003001d45000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 937091609 1250 937090359 937090361
    0x2060409050f1b040611011803080a200f0c1c0c11030c03031909150908060a090323040b18030f06130b062d01021e070603180b0106080a 60
    0x2c03c202100760685002c8005601a0400c460480d099858261b4558150900d030500600d160004e00c541070081200c07030410181c0180240d40708040400d000c2120550b14041116150407403034a1124040042000c60707a400e42c1040070301100038100084440820448000c40c03032048801c1074240206000c100750504120211881e420000400e030041c0090b20b0200d0042a40d07406240e04082c120100304080516061180d0b2900d8001c00e2007900c440242903a40c5005000305a9902982c01b19001d100001040d0118a0048900f081d5043c0e950300f1041100f000c88500c59640d112421030390200811001584400d018041c00c0613280003d1002c50310f80181c1c04051500c0016607108403181c000c1c000300606110300d04080300170300ea084800f000081d9035103000242e080b4588041c0d0000e9161000070985c60780062000611001400c0e000c0301c0c0c00c001c000795980c03402c502280040b615a8030041050000f688a504200c82e4140c041c0b030702805000203aa03800003645000d0704074a000a20000800000c0700341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 937092859 1250 937091609 937091611
    0x12090406060c020d020919020f0d0f0c0206070f0905130b10091805070903021c0c06020a0209160201150b21012402160905011406030115030c0c02060409050f 69
    0x210b41019510800640d02080c0c0040710000040d1041d00300710700294480c0c0504284000f0808003040855441303e1010036042c1e070350411044520349501d040000141203440744101600300526030000c000719941c40004403003c189501d03815040264101002403070792035141c00c42c0e80c82402c86202080030401e1030240001490140059001c0004408042040e4149548010800400f009001c0b81542d900d460039a83c816469100030340101e03115204003807441840210140e51440b5404250b6159610b0f103040b640c0fa0b4503104007a5103e030119001c18040ba800c0050b01858404600010401e00d120b200035134001ca000d43d0007440381103000070f107007026400700b01203490083c0c4007040814465410284aa04164000c00d01c010f03060141d02d000350a070b03d008102480000c2058141c98107000e417a807808001401c028460403000103000981c4d82102d1500f541900e0503220300012000060350710f52402c8028282800d40312040c060600e01c0c0f08050b855000c0104060000c07468042281d00b02902580680f00d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 937094109 1250 937092859 937092869
    0x402030c0415051e0109120201031509020903330a090212070812030403050702090709172b052506060603050601270b130906030501051806100302060f070512090406 72
    0x1035540c40e4216a0024803040687c0d000300c40f000c442000d80d02c01600209a090ba28641040c400900010034040c1c0390020080ea540580c03e48004178682d03441c0f8501c600c03240d0b90440c0ca5000035588410f40e1045281e0a9900001e1b450300400c44030182c0d00401ca041111540c0b142c000d030072074082881820802c0003002c0302818000241c0385149802c0c1c4000303009024540009220321030300b101140d03800b8490a4400d001d000c0c0c108a4001c082c842c1085103548980c0200111004000031128070490b00909245904101c100c4e02c4052800340300c0c0c00c0d000e201c4011041c02460304603400e00c140d008101f0b030380f1179940641000d85000400d03080c88000501101010b010b2031a1200c0d450305415880c1500e140008201eaa0101c800c5031600456264491142403035000f4071056864400c0000c10710505410407030007180d140001d40c02e802210550707140c0301c2d50708680c05070801003180710400050034070300700134018400f001d0061340c10b05242c0c0e91a60f09003014034440c140050404503a504052801c3c1c843c041c0280 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 937095359 1250 937094109 937094149
    0x70b0313290402010c0318080304090b1e0d2102070e010b09030a06050c0706020c030702210a0f2a0503070519050402070305090d0c09050105060705150402030c041505 73
    0x2034a0080708508403100070300003810400981012402c1602400c90740c00700041c0720070a08035680c1c481e8441a940d4100344160081c60741030a201c110a824080280d406c0034060041218500040c0e10512281e02420202100c262012002040010041c0e043c1d600720b001080e406005140e20b0562400e0450206800424080904018800107680c001a0302d0500587c0300c1004a202e0383c0b240c442240c2e40c028110b01501240c000100c04240f240040020701c2d240f8400c94031040da4052600c4c2d9082050326145104003240d02007401100860741110703001000d86d2050350065410b80c001300d140c40325004440004816411396100038081e514040c8003000180c14195a404d02554100000d0011203d951007514000c0303030300041400c1814032a1040b00c076803076000b130282c1c035a03011503283c9603c02003030700d01c1098505032030000046610f1038600200e03508250017030b0003824040d4030350010924620700034204903031601c03900540c0c01c9991120702a500030740e00020107110301e1501c0d1905000035205451108406a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 937096609 1250 937095359 937095413
    0x1030b011401020a060e010b06072d0203070b0d20090109141c1e0305030a0605011d130f0c0c02280605031e010f0305010e06070e0111070b0313 63
    0x42d9a000414001c0f11740c01c01404140306010000c542d004007210381401e904114006201030610040181c02c0d84180303500b0044e075020000002214540d0807200c1002540750300151000c1103117994034805850230385403006001541390000d00d44400a88004090021880f0300418201869a00010041c00910403140f54560b044000d000141c03003080621000a51109000c0e121824032486407400c1e480d158240300d5905180483d4107014000d40c2003124100ca0090400401080c01e510840c143d0200742c00404c0a1030703161750309004101c06000b0155113603086641d00c86440e010407103d80250b00c0e03101c00580725204150380d2130040c4000e603031015040311b00100c0c10101c9a00050112401e100031190035142903501c03615040412480c01100e80041021a03031540008a80c00400c00440812030707115000800500011103030468441604585207004a03540e01078a0034194010031102e050000702909072182c00303445200c49500380d001603175081240f1004140320303c2046104001c4003080100740c0c080410f1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 937097859 1250 937096609 937096649
    0x3060603351b0d05030402090112020306041211120307090504020f030c0306030313090c0f0c170f0c10050f090f0303061302090d1b14030604121106010b0301030b01 72
    0x20450310a0911544031800160802c07224102800b071154482c0b46405445051600d00c030001c00a07003094806a20035810000000f5200d19501c05010700c50350301a014011698403610f90781c2400721007955460901010071002d59980380140403071918100307456921912400d00d104014040402c0f0b41080d0b00541c41080700000000c0000256540701c4034112100fa517076920354021a045010b25041c1e61903580072000003240582080c0c06c41d540c400c9041e502d0a42104456500b01d6064182e03401c09000c0400700440c0310f1a0841c400c0c020307c0500c0c90a001545883c480d80c40d80313450032a003485030707582c3d0680d608140401c0709151030146130030102c010000d1001d0418481103a460b4400076010f24468000030340184601030858041d9807000000400c071074072090007810002c00c4600086001c0c00084014000030403903aa00d1841d02c441e80070080c000346107903955a0340740c04014080c42c0d945410700c40700d480036501c06481042060702808080c100f50381c2b81d514502e131545107024180c1180b21118140050078031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 937099109 1250 937097859 937097933
    0xe070b09060309011d060604180f0320030406020303091207020102071e09020d02030612010e150613050106050a030b010314040f170d2a0813140703060603 68
    0x10445021290160703243c8460040d2070040000700c1c2400c0d456004d80c0b42c1c80e800301101040c81840342c80166001e10502c1c503441c004100621b505a0000c0c1550885c3d00b0b0040424402c2100401542e00003240f4070004001000131031840c4c2059210b00010f900000c01c01040a205000b00e28501d01c245540340c0c00c100301c0b40d0000c0d440b00e400d4042d084000941f12489119644c0c80c0100100030b00d16144c0c1150f07101e50b1085c282c0007941c42150b03054041c37a60300d0000d207000c040510900702060b0952000d80342d00d920200b803440005030003411141e48182c1d1008051300710010b900c00c06008101584856580340c482c2107025054512004100d07050515022a083da18031520441c03545c000c0c0d00030100c04822300180380c4a00740d000ca40d640c0c20341c1828007040043c02030406a12040244000c880700c0c181d107241d8005010348040280e21180c0015400b0700220f14140c0d8004c0c0007a444901c00d629421121884803d041e2a0a0195206591803900d911040081c4040401d208171603180030301d010b1015101c4001148 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 937100359 1250 937099109 937099117
    0x30611040305060c0a0203040f12050d080c091c020406120209130c060f0c0c1e080109050703020f01110a210e0306011e0b030f01090c0207140d0303110304150e070b 72
    0x82001070f1458003035209000b11006081c4411112a21544070020042b580712a12012181e038801c8100c40a0f00e98054903106105940c2c03032400d9880d002d18901400400d454186009110304260f49200006a485000e0100900322101d00c0681984060042041c2014003819039082c1e4004500e030791001c94403068110059480703e00b060789402c0c00d924004c41c0c40784010403000d4154504417101144120a449070b0070503a00c81200444c0304c00d0b488800c11800c0301c0c3c6428000300f069024940410060411451240d42400141440e881d0305194903103450500720785e101b0445100381410004c02d54442c25440311041d005440c0b409001884503180400d0755441d042c0540290300300051500703d144500d20903400090300c0c10311009901e07400c24480401c3c144c442801481e20040c10300d07040c040c1071440043e008044a01007002200326002901c20300c60400210003068081645a158140d080714508000b1400f4610499080b5070140b0b1004401c0121110810051100c0d080305108024800b03400081d6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 937101609 1250 937100359 937100371
    0x2030904050403120f0b010f1d0405180a0308040317070f0e0301150e10050f0907120603020a030f060b01020105090d08092e052a2b020403061104030506 67
    0x4081d2103505068481da0402030314811181d0030180b2000b8a96519003244129403002e0b22003142c84000c034401540d4240030800740d542c2e50300c89c011341a0300610341900015000301415043c0300105441045060400c10032980503004200364000f440109644805400016012018810503900340080300900d1a590302c8031140c20841582c80324019694207601ca0258045c2c01e5287c03046290352480b8440682d0b0040f2024a070101035070000241d642081d240d15060400300030700300d1030580d43e13810058070424519000c0000c160354075100403005840f0307884148050740c099007081042c2501460302209030b075000c590142c116410002889026103001800c2c40f10b414032030800c0c040c01e0f0364158006161203000e1040740025000c0b0000e40142c141141c0441d4542e940008041c03042c0e5031001c0301d5581400010070010700c09217002c4105a50200154090112002040942d45c100308640e00c008108032041c2507984440343c1d000808008100071403046907600e4072881d84150400f4130319107810f91507010050007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 937102859 1250 937101609 937101611
    0x60901060309170a020a020f10050313050c030a38060411091f09060801050904140c10030203062706121504051c0509150a03090b041a1602030904 64
    0x2d14010403403004030301400450741885a9480314035001d0000d43d5a11405030507401400341302c1e5402514100096411405001622058034503101c5401950107001c03001400d030f03064025500100d000d640c060000c074031158008d4044000c41c00c3d03200b1940459090803207007107201400c0b000601d988084441c1180e9844002100c00181094002071402207601c646c40d07000380c0c4803070007201541d40e0560480d030319040c9001d0360740d50720481a1202d0003a03900200031300445901101c0080004d000031041c00e00c00310848540307410340e01c1d00e010343c0004c41c240c403c5034044400030035008000c00c48603080041c6002280c1d03614400308542444100d542030060301016241c03d010304080780c0042c580c8031041202c0100e03181c4074904080d40380f92074107140f612020000044105036414043e1403041522400a40c1c4008000502c0440d503442a40321120207684180b00280916403254140004504140b2116220318041c1d0b4843c40809415a0140456640140900340701401c480e401c080440d400829124034800c10b543c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 937104109 1250 937102859 937102871
    0x1506040e0d0302090a0b16030201181a180607092d0b130510080a051b0a2d02030c0f0a170304020f0d030507020307360609090506100e0609010603 64
    0x4082503617010f40d500301800c14500080c204210002034003440b6003d50213a40204000c802e0649044101030710502d000c0c203503030342007203401b42c0f6030031242040d0b5006030102d121807100c4200c10048901f014001c417103c80120307083c1e820400c40c0381c0c07480d90f0803003152907015481d00c490401d42c05040721001160184040181000c64003991141103510b058000e400010003560001c48002e000134039019086920546190505005c180010049407081d80b0781005201454202461f41d24126240c480c13014000d10407034100707480c000e0309686d030691200324280503602071541c505031016943c0c600f05c20089844030340c0e801440100003040340041c48040200307080d2000c3d5965121800000c500f2060a11081c1d4400c040403038002c10103812500504101c0d1090701580c0d82c0c1a9294035100c09040403c01c800d0b21290384002d54601c007021090580403504403044c0001e0129103030400d020031140c02010850b41648510244001400808810700041503091000c03607081c60401d02040c10042d040c0700707640515841d64 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 937105359 1250 937104109 937104127
    0xa08070605180d0b040327030b070c060c050a08160207120c05040203070309060b010c021c02120303070507141f0504030c0215040f0905150f031e1506040e0d0302 71
    0x280c0e840c60520000b802040380102c28140240e21404c143c07401c40101701c1b40300071152490688441e013a001070446801660b0f282ca162540031060030000c11040420003200703c2d100000f03c0b14400d04c500e0180c5caa4030700d41c60301603801c0003078820040a4441506161003030741c90340c0c500b940000c02c001a0f40510710100e0310403035186000c1440840a070001c0341e0083c008010803010310307815801001e2443c0100c1c8103011040010300150340003001c618002e504103070003100d0682011080107009882c24400717005810120301101c1c61a056030001c0d5041c8001400c0054840140100d043e00e4411244014001d004507200400c0080e85803001e1540095845440d0f400040c145800303030002e40201a00034280c00c14282a00040c0b0f9100d030f00501813100703444040740e004103a40201c0c2c46098844e4108100754450911800104001ca500f48028140e0500c1408400401c08500c1c2180c60903646040c0700611007948002c100040e800b200501c0c40380540e2601d5218152007200180ea800e99054904005035103032501 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 937106609 1250 937105359 937105387
    0x30c091a1c060b1306050901020705090c0c06011508070915032c070504110f0d0902210303070306060507050a0303050a0204120f060f020f391b0a08070605 68
    0x191000403072545004400560840200d0041900241c0800b01300111901c86100303942c2030050454550040c0c2c4004807d025a081c10034041d9040202d0303280060915000c0c10204c2c0c9401c00c241c000000100748440ba0302e455540210070160032401c582480d600c801e05004902a000040350480300402d62140d04098000b00100794411001d648840c6518104200b92842541c0b4945c910600b1702851030b0401100030074443d481642c1d040f080341d19601d440e101e01c1020302c002800401000303036401800c0d41c2e10035042029400720013901800c135102964032440c4c1008080c04854840e8010300038000100301190010314082492505160715086c0000d158a40c4810100280115000f4100c40143d03402c0c4001030002c1e03200c60480c100c0c85180c1c02e1107941e40107107110702030f4007590b084e0000d87c940500024503031142d410054140c80b80c40b83c41d20300b0341e5130b001013604804241005000344c01c0e41201c500700d1184c0c4040c1f40f038070800c0c800682d90503001c0e88c6054501552a07025101c0d104c104640840c081d4042107507 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 937107859 1250 937106609 937106647
    0x1e0c0507110d021203091206010807031407121a100e040b0a11040609080c0a0518190204090204030203010c080601052a0307050304050910030503181206090607030c091a 74
    0x2515200901e40144c81640d920741c0070781d003124420602c0c00700d54a041003000a415042c2c94490300900310f828030715502e01042881980584000d402243c4001c2030403a2030040215407140511290841c46800b02024150f00c0070281c8860b401d401407503014884262020541604503900890250b441d42d210f00001d0000e01d800034a42000e44e600040000c1c4596206407100f080e5220030b816a0017901c02c0004100121405202c7c268000034410700550900019010f915070103401400c0c01025098001051000c0381c0c000e4002026290b80800c050040d801c0c02d1281303051903680c42c00e1000d45410040006005401800104440030154004c541020b0f580128410801115481125103402c0075240040d16a0014000c0b140904010390020b0304146a1440c1c4104a9801001031440c10b076005540c401d030260000569604006000f01e1220400c1c420442a881000d00e44042c090b2410845002000e41c0c083c48120401c000d04400240091000b486d10a41d0480c80d00201590f01d0b148000d0707043c01168 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 937109109 1250 937107859 937107863
    0x1014090f130c02010e100509300a0210050f04020904121133070c1b170d09171c030b03060a062c0a09020303090604091e0c0507110d 58
    0x42040c00c80c0b4640c0f038054004021101c2518252484c0d40c0c0c400417600e04443d41201c1404055004100080300020712015604600d0b01c4003507a00c0040000e00200d0480d90720503540078005a1000540385504a8584a615000f021b40354070f100003824076400060500c03001410140c080c1c3e9070203081682050095a9408120010b030b419508030a044201052a500c8050444404116140040b131014801004a2446100d4644810303034010829201c030001e2200f107007018104222011404a440b80c448941d00201d261410000c003244140980000e0071000c03503902a02496042e41101d0344050808501c038000e68a40128010003044010b404401500700c54004c560140a040705000c01c0f0040e9410800c10342d408503241d945801d10440300101b40205440210b035602100001162011110b90000e031407803800101200e0030b107440c030030004009034007940c44190542d13503e2084250405030702c0b071403180018580c0010004003481c08000b03411441240b0000b050a803009524100c1c0c0e43d104003402d05210703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 937110359 1250 937109109 937109111
    0x80412110a0305070605090c060304060213180c1d0105041208041a0c0f0a020105030402010e0f12010f15060906050706020c0303010e0712090507182007021014090f13 73
    0x484609000d03103e0741c0035842c10f4540600740000103045900024038000c400401034036803851940c0305d0312288000d4102d159007410899020381d0008003076503035060641c0e400c0d00365100040d902c01446000f07004101c1c10424580081e942da03000000c144c1c2c101e019102101d9150750025035028151814142c90711940d04201406c0c2529000b0740014132441c009001641d041c0012900b0803994a1009540c5980320b050090004004000250055100301e09006510401921000703048800a00056040c04114122a82690740d402c580400b10100c2c0941044840c010300c603500881d04080f40105007004c903010740d03405c0c8100002c44604100c0c01d035049813060340326507041c1c0c1d4895840704a005e51240c0283c400400041c60600c01c020601e202c1c0c80341c0c1d8040d41d0322000a0280f1440c000204030a01a0200201e00c0c441d0364920310f0004000c80410f05440c3c2c440c2120069540c2c90394410020000300054000040022415080400361954811207030b05003002c480c50300408020700000348411107441458070580b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 937111609 1250 937110359 937110373
    0x2040609150305040b060f030c040905030c1b03120f0712030b0a0b19030b0301091509020a0f0e0105040510080102070302150c0a081803090a0605030105010f030c08041211 75
    0x5520030003003000e5503034415074001103800d18507040303090b40c2081c0c0b07000d049440c403007010410a14040c42910f14201c00601a1419280c4120001d0100c41810505581503000043c600d40420400d001240000c15400c030b0307480d1461115400309035510740001000301d440d000016041d00f401c645006640e0f60303544c0b00c070240441c0007866500401602030310443c00d014101c10f01020441403008025114070500c1d008105600002c0d4103c2203004e0001e80207581e406551715291179010804a01c3c480e0084400c1081c0460704502c40d01c1401a0700d080c036485100d00035100e00051198042030410340b8119902101c0102d030a44540d40501010320b10740e48200c0c02d6620008019003010707008584c1c031080101540e140700d0b496990904108072841801d030750b140060140d000164100c1b465a0018071611400022241060401c02c04502c00001581041c800701d0340200040200d0341e0301200c00d804012252a0902000003503c80207812680b001d00001c0210705241e940381b848500c00d500c8610109510412074210b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 937112859 1250 937111609 937111619
    0x110f0a0803031f050603041a0415060b04030212060f0f04110d03120c210911030102030c0301030516150804020102160f05010e03030a02070e1504090803250e01050d0209040204 77
    0x1d0341c000091900540900f0001d8a8504201543c0c030841d00080740003820081d00f0400580c010000704201c88c44a145a10150444407510446002e00540103c007030382c0307901b075004100c20300519080c102406c0c0c0c0604104403900c102600c0e02c2d44c00c000d161801d21000c2e01c030b51914070b13100664003204a4000c00341448201c2410f90040c414049000f204804000301d505c8040c0445a014649620000ca00500200d5015800d05507000b00300381800365070400d03200107081d00041d0030780e80161581c5034256404001441032250901600451030031421b50441c102e45002040740c45168840070300003c3c4241600000c0559009000000101015030103480711203807549405000e9460038012540040c4017078011a4441c01e0010840c0e0049117190010702506160120504030030300000e1004e1040960f110314102e05403502e021700405584224006500c1c0d04d0096803030464a4144501c04e81c03a00c0415240245031034000c201e1001106003803900554400c031044681002c1c1c4545821160041c0c80001c1c0011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 937114109 1250 937112859 937112881
    0x9030d05102108030c0901090504061403121323040c020d120e0304154107150203060d051902090106210902181315020403110f0a080303 60
    0xc0c2c81c0345003503240818180305845545001440c80c01428210200045011030601c0d002520264205140811140340c503000800c060304c1659000340c180e886040302214651900344003021842795074800142c10141003115120700c0045034032860490b220720100001c04841540710b000e21000d4041c0090110095502d0029640d4102c101100006900c007d400080100ca500442c1c408190f07a100940c20f1505000a40031401044ea201400f1b1100c0c2203c205000d5440758031207502d00640c3d0800303007140c100303050000a00c42c030300e50503542d410401001103e001079001416004681d421010040c4c5270703039829010540c00840c071900500f0f09d21801120700c1e400c1c0ca103e900040304e6072003901d204240d079a030350340240c2e1a4a640e81510124a07041110509001d6059000703107001c0d40010000403d40c3d4400d585c18448072000e5408614000c5a4142c8806203c010099003800d501c807024210b18061031070300c0b83c280c04009000c00c80e11402c03070502c54080720703510100d90301c029010070070540f9964204450010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 937115359 1250 937114109 937114141
    0xe0a051c0807020c0d15150e013201091701050105040c1707030902121b15030f01030f1a13060b010518190b04151b0b0703020a02070801020a09030c09051e09030d05 72
    0x81d190a411300011036100c1540c6441c031508501050001c000000e0818283c0340c254ad0b0303050740ca0400410342400250404e000c142c3d01042c500724400020302b94180340512080d641004800420310030762000d003070404510000501d610646519001440001c50f1001602d011248850151144901d410484070311002c01203510083c1c0049503904c44811360034680300c01e14041201c60328400304000c80100003007420841c10460325403040e00f00c1c409100c0d41c840031200c0e2560507502d00342c400c019140d040b8100803480c42100e618000c2400c0190810040889114807400321081b003e0292181e4040907440c0606816140c000d456421003068480f51078a000202072880d0417507000000c0d4100c0c03000e000c11aa480c0c1c4441358190840308a0340181d58a42c0244e000e5404406560210703c13900e203000912400a1025084c0d4481f03075940c0365015469030418500700d2096800401c40d0514000a109000003e01e01c156041e8214000c60807295544060603415805040781d460f402c2410402001016040320541c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 937116609 1250 937115359 937115369
    0x4171f0f0609060b0415051204032724020f010507020d17060102190516030302060720030a0e030304361a060d0e0a051c0807020c0d1515 60
    0x100074150361001c2e00320545015224180448508010a01c8200040b910b08080a952414414030301002041c000000712811501600055001401e05100412084d6003003107154540c41c40800b80d6080c1540e0300208017000c2c2c80729440c00c440e04500c0c0c09040c001e00c50140c0780c0c1e0b0306000070015494100c00194852250408080015005400e030303108e40b00c4106c0c00e079401480b040c0c0c02000030100716154500700b0504500e090707407140300e4140804002e00b42081440d0255229501170f0a4a0400c0c42000e8482c9aa0080e4000c0300d6a0404d08030045401c0041541c9001196260071900e43c0b0045000c03038118440d941201c1844400088801c0da01c6204101040041d60400942c0341403040340780e07076541140d84040c0903642d00c00001011105a2800c8070103410310300001080041d2a01a11030740a1808500203402c5031181c021402c140c81003400342c0c44096001240717003002d00151519040094a032030030411380e21300c80d010180c030b88428003010f001601303031401e0030100400440c1003080c00c0b145040c1c114032135 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 937117859 1250 937116609 937116611
    0x11060c0d0c05071104111c0b100e031504020a2607120206090d140a060914120301061202040f26030405130b060708130608010e0105010504171f0f 64
    0x1900003807a100b03800300e480258010352000c00140f041c3c02008090102c3c400343c1e0310318000c240102c29000818031256014044087c1e00010414181c83c10b00c5205141f98029800340301104103107841d5a14085841440350074545003102036030380d0700d100050b0b6004180d000728400b40e0007494069480b1035800c41e214070320f490540446a52a0741d0300c60052041c803031184000c1d000001406035499505140d60080c52044c85101c154030105000c0d00800d240c0107140b04156281a20f40740d41c2c0c030600c10514184407981200c0d40181c400341c011482a005284018031800d0100b02c820400000754070304a41c140c0340a0a040d001c50f400865441541c070b60418035440e81c0d44850f055101844069070780010880d402c8a6018250706201d2200303240d041d00900d941898a40c0043c000c1209200082c101c600a00309038803240d81000200b400c000c00100000016040340e48040101001844203070782010581c0d0444000c00c43c00c044614559514905080c0d03031102c90600d400b203230a00b50424540c6a00180400450100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 937119109 1250 937117859 937117871
    0xb07150f2c07060f0e03010f3603050306060a030e16030615240e0a03080c0609010b030606060d091203020a02190210080c280e090403021b0111060c0d 66
    0x41c291240c0075485a6408142036076404800b1a0260701d00d02e151000003400010303141c0f207000d90601074555401c030140b0300400c141028048512142810520703949010960295508a958090301c90b11014004511030040850113000d00c5220344c0041c6003004161044e540307141d5000e1211550041c40740030464605080c4001c1c5810360b80c05c0f0040303104a5108601170b01c01d070903640c800002486004c51054003000b00510741040103803202041140214491841141e48541c0c0c0101c003821720b1400742c481b0131280d0504a090445590000341607400500032281a991842c0c1c811034040203060303100005000004100c1d1141e4003039011703406002400915001e4924203104000115404022900025402090b24842d01d11843c450941c4680c441c005001c0c0e14905a02418413600c1a0081d010310303031a2461240c48400030b0f661040b01111031100540342207181d4201603402030345940c000d103550445038000559050441e0310031802400d04008020a58125052010107502c059115a9001e2009410b001d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 937120359 1250 937119109 937119191
    0x61903050a120f020a110f030f0f0307050d090312031e050a0f0c17010b0a030222150302040b12090111180907050906030f1906090e0d08010b07150f 65
    0x8510000140d84c8103a0604088041d06c0c108020b1412400b400e0340c051140231121091213408001c1d0340c080080c284021a00c407507551410a2600c503111140208020f10101c0400c0081c003074074000702c1e02c032a0354200403824441c0009044440105400400d0000341000d0030311480143c09d501c80c94118521840a05c04481100000c0d0b0303000881400c842c5044000c00c004020702038450005d80310034982881c02525281c4910313405507050644550001c8a250049401c2041180c00c400c006609009410203504141c60710034094840d01801e0012854000c0e43d10011b0718590003036201c0d080c00c8035002529911030204802e0900d03050900740e84280254108070108840b540110190396808a00404c028999520001c01401114000c0c00506c0c0c001d640000c284083c0c002409454007a004030700002032003000c0405c0592906450041c150141306d402401030000d82c40d840101c07040345030401041c0100007219004c1000400940343c2c8070091616060040c0c02c543c101d006030b001c41030303841e04116901d240c0036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 937121609 1250 937120359 937120363
    0x14130b09070b09040510080f1c0314010b07030207030605071107090921030608030a0c0b06100e060919030507060f0809070504050c0d06030b0105040c1403061903050a120f02 76
    0x2802250107050040c018583c40c3d19182d008240e000c0034401ca403910403651400b88a02e40513103d2111841600042000340c02008d2145040980242d039280c288144000d00c0c50385000090107000d6203407004e00008000e42458000c100c0300d0000c507400701b03007001107141101c00100401800e4010115a0040f0700d000500c0071102d00440c41030a42100e00d0034101c40c1604800355a06c26107059041c14140c40c0c1600040804041c4094100c40d80c0d40c0d00d600e020a0010320700a9104107000340a1071080d0480d8110000711a0301800e002d18014041c1c0c1e4451b03a443d40030001a01000008141c070481342001007000c400c111009c1406c030119103094aa800d100710300c0ca5000c1d03a40b07200071100400c240d031000004000c20303e065003066400c00058102c00e4501205011100240d60084c0c0060ba40040844010002424071b446241010f2032146070001008078030ba500303a001444082c1005220f503141541007101c0c030a4960f0050015544603046a54010140c40c050030103900318004800410240e40195481c2400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 937122859 1250 937121609 937121623
    0xa1b08010b0d150504050f060f15010f0c152406030605030601060e04051009090c0e070f02030f090a08190204140402090604092328120e0414130b09 65
    0x4004400c007203c6403412004401064010001d458074401c079034045120250038403006014040f821350202840c501469040101300a070321200d8100050b1043c5064481c0c1d10212000003203030301c842030002e02e0300781b80b0405000d4403c22201d00454408443c8100015203c98640c000b21211500c05015195440b400c05440746808d1003824042200c154007284d203490f00d43d101c640e000800308020016651180e1400089401c032850072590901405400d1000e0b50101c00340507840354040ca03103d0001c0d1031026009484e4010021449030000001c00c0d429180e40d900c0705a140900400400c45140041c000c0e90000ca00c0e5800d08161b01840c54500800003d01c0049810340c89190041c000c10016120350702880010300c10b620b0152245014049841d8000c80f20250b080c01004541d8018002d044001d080c40364103400320011103159801e002c501600103019030240340309401d11420195042c03101040030070043e00001c9002c1c0c032282d21038010000c0b170384000d402350740c0c2940c0115509640390b030750620701507a5106c2c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 937124109 1250 937122859 937122863
    0x522080609072108042d090612021c08030702100e01021810020a08030a0c020f161208090303040b0d051b04090b0109030f050105180c01090b0901020a1b08010b0d 71
    0xd41c280d010b12020b000c80c4030414195205250701c034035240e074031011054201701e400b013107020341b6191030100300a42e01d04900340009407694103c1008070602e0310080050006000d94024000c107244460580c100c2c484a129030740407604036214542d64640184025100d4640007661014985080032802403580144295a0414a54803030555100744601c100002c01100f00020070440c031692420400041c01b60300510b000303001c8030f0008103446010544c081c1c00c007410303040e48042962001a0700c0c601c50103c10380000032100c000e8050510f80305181041d60f1640700d2000016054400028006010b201c0c95000b0300c402c205000c0c0400c103540315a06140e0410b05d1001c919041c56406005c20b101b022920382c0b0281c2640414104812655920340c0c0310106090103002c00d4905075924020400c2d040140f012440400322908050415603040d1070000c1d143c06164000d5074080807010408060b680d000300054811103410060800390003400070000754020000e0f02882c41e0310750030582000f5060502d81c2550a240e070f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 937125359 1250 937124109 937124129
    0x319020718051f0b0924040509040203071a030f060612070e040207060608070503120403331a190807150302070812041e02090a0507052208060907 64
    0x41005140c1c00003030540a000042c0610203018065100c4120320800001001c0c42c00110fa01c0d012034004100003c1c09442488681c1c0b180041d449940b018940d049030103940d0100d48482007910345001003807401401350049544600000141e04500754180c02075446071000c420060f94941d00c10040c440c06025101d00010b040ca01c070408520380070f004400d005103802000c0d10043c04c1080c66110030007a2001503024405a420125040c00715080600402c82c440c0240c00e02c00d45040e203036035075410740a5803106503503903414030701d900c00d142c2c0f4444060103180e500042c8505002c2107481010460980c840b80304c606100d05030038038090071800d40000c2d8441c100d41c0340101410b0300070b02e40025512040c074108606001c05908020020014694502504038010b980980e1051072502d446c1c0811200200303201c100380c0d114072220901c0182d1307408400b0780d4000d0643d6400325060b110608280d4942c0a8128200404040754800185a42e284103510b81100c80580894140382c585412035a11803565000f500000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 937126609 1250 937125359 937125389
    0x6010c031b020103230a05090a051b030712080c07061b0b040515010806010e010b130605070c0512011a100905060724020702190b040504090f060203040503190207 71
    0xc500c4100210740101c0c018180450743c10904e003401c1180080202209015641c15800d02040c0b50561003180d9000c21050001c012007191916080d075500102d229550961001025081c8a9202841080d00504150003800d0030307030420303140c405040d400540d00c1c84560b03c03c8800024200b4800c01c80d02c0c80c46083e00b00304804800103070301d0381528444010f2040d540e030311070b003540610b4081c201c9500368024450600a06065414460341400da000e0603400305210100501c81900c940400315040021078015044c00c56a0311014030f0700300c40410361940102e034000540d00f50762002c0c2006401180c92003843c0c0d9000c64104103d4010030031a81503070410180011049038003401a41041401402418005c031044201c03410111000f50548200002a900040c0c0110b454130840c204030608800035021a210400f48600b05054038015009034480c0b58400c988544295007880384a0800b1440a90048002d41d41c0c2e180c9401e1070340d41c0350700a40d17011101200e402c00c00e03140d091001c035407001902c006800081c51 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 937127859 1250 937126609 937126637
    0x15040b040312181412010e031612091a032e260606041d010203070f200d081b0309160e010803030403080613050907080105010f050a090f090c0608090606010c03 70
    0x110905c1c58260a2a5035a07240e060384500010000340070000d074800064603003a03021346402d142d8504e41050810074082caa500038072640f040f881100101200b0b000c2d1036522907447c0211504030405005e5410b000e141e00e105030b4401c28142d4456102a200075030b00ca981e10102e15024140c1020341c0420024440d00710078040b9003c0d203440e400201d0404000380001e00030300d138910300440c00ca0740b06440c4000806d0244030000790090304101000110b160710000041d803008c0c4000610341700c0c001c200c202420490039800140107502050b002d02144542d00d40290384a14211000e203540e4030b03012599003d864032035807001030725080514916060340c0001c00910301f5034603107580c01e0701d03e80b40113400550300040382103404078441d55611031584100142070060401a107041c05942c01c485043c2c0145407500c2d1564800d00268031784181c2d0741c1c11140c0400700016004d1001d25000020310411800806584001100180d01a80404128080c00240040e608141ca8000056401e04100240140810500e14240702 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 937129109 1250 937127859 937127869
    0xa09090216020a0b1e070302031b0304090609150503070f18090605070c06050a020903190609082d090d0b0a0e0102160501050f07080615040b0403121814 67
    0x1196141a0008024041c00d900090100c0d40c0c81e0001c0f01c1045011685084217001041943d082500242c00303280f501115490094807031080d0a6120041c0d04c20119042e080b02c010011a0300610030808108102500e9115200141c007000102214411400c0b2000c501443c011907110102d8043e21003040d001c5103401401c021903001d484c019a07126035076500406c082521805a103200d05800c1d5140750200440e40340c03080403600c0143c1013030720701c600c107104940c0da0fa00c0008440135100c0c00d0700c041c007003c1103083c688070001d044d909070000c1a600c404909424055000d250415a84d040d46a0101c0c1a40b40042184198000d1101850f03000010b1100030340840d07a001d0581c3d4011031880800b180c02c1c04090700c0c0c9420399102c0000c1d80450203604c003005003842828840c403504045000380c3c3c0e240509049500411006003d010507101751002c2035280700380360201003244d00a05d6402585521107503a412b000d8030f00c1040011a8010980703810000751071104030b0403040184d440b82c00254640411040501c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 937130359 1250 937129109 937129117
    0x120a0c03080a0b03070311280b0906070501022a0607021e010e06040c0603060b12390403032a06020f090607080301090b220b0d0f060515060a090902 65
    0x1280460782d40f80c004105032001d10855020314060b05079803090000d0b00341880b02400e0180282861440481210130000c602032407003000b00c564035010151656038600000d00640300d140b0f8000e0084d8070004250030002c034020b518010710010200000751429250380301c0ea840d2903045421a005030804a035103c1c0094413190400490f0f08001d000117944080711065900e00b000980f019a80f40d045884108401039060003804040c002499100e800c081075594a45040c80001d00b5407900c45040d00305180e00c04110030301e0802c000c5421071a070103c28604440e1b829066003e408180c0020b01c83d0004c1640c280258410344c40c4d40748a00418800c0a061074490030000e400003e4001c1d101e49081084032f956030784040250002d240035104451b0b4a5140c51440012100b2000034117001b440341c40200c490b031001550038070b840122042d901094402034000010505213250100500c40e2180c55222000d1004d00e40c0400e12800c04401000c1c0521030034010009980600c103044030000344a560b05120030201a0064 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 937131609 1250 937130359 937130371
    0x2e08040f12090503060411270f18062505040e060d020301021b03091305070503010b0921010c0e120a240504080d050619050f22020c120a0c0308 63
    0x450b00c0b940d01e8500207400c00c83c060350180d0302a102480040103d103820703c1b000311025003211070801c003440481d1203405d180400411509031451141c0000d404a400d4010140d4910000d6054030694039210441298070380260705045540d841075503c2c000c01a010344111425141615038001e465039940d41048410045100d049805540070700c0380c1144e000d003004428000081a40240d40c0f181041028000b01b40c203054041c60455040c1028414940e404c60112819030304600304103951160340703a01103075807a1910100e08401da1481086040c0003003041d401401550184c0d07544200102042d420041c50103581c1c0f0395a2203980011082e140041e02002c00007019081c0b00300400c0c414404100346e01e0407618115816140581c000501400040b81486642d900000403903051b00c2d07048902810030070304802806124000d21111590003620307603c6150b00000135580ea1030f507078419040010b580000c0c0d0007898400e4060301c120700c1d101c1e801c03201030300c191140c4d000c55540e00e00307803001c0b1514200d640c2c82c405005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 937132859 1250 937131609 937131617
    0x3090c0402033102210609070e060d240f0b040b030607030c0201090f0506040213050c090609041e0b19050303090603040309150206070f05280e2e08040f12 68
    0x3c10010703107074400d6103c980c0100c09890248a041070041e00c0c1821030040c4070025542200d502800140c141d0f101090b001001551132449402461400c050101c80005191484a0840c1401240c3c2015901300c400301060419091010000c10710a00041e02c3c1e500500300d525402c00000507012030301c01e61004102d00001d01c00810455915200c483c45d0b0600400180c0d071030740080381040103608198201401d80b030000c110400140c0b4041400801c54080c480c96039114010014103003040d56100c0d088088420326202c6076280d42222442c200303004003800d22400d401112a03e08401092810000810803070342d014001c1c5280400560811026a200078012014045800400b04050b00c040c41c801d40d07003444070f4000305041d04120101520004d01e40c1809400c010b02048090348800e41c2040b9021032200d0540910807002806070255500c90018074000d030072034170b60380030018024121801c4021800c02c03e200f0340d050003030038841190038210807034002e0b100c1c0e0700507004040055440b030406a04052a860 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 937134109 1250 937132859 937132951
    0x427030f0e0904050a032a03050d020f0a0e030106060201150504050c04080a03050d1a0d020d03050906130e130b0f0403031b0225060c08091201060b03090c040203 71
    0xb03203a6103426901902e0329071107640071004154200340796002c6250300b581d26000c0c600089600c0103100304904001400c100740419083c0b010119a016561380441e028002c946902100384011308117006a0066442982000800149980107104010740200b1440380c180310306090006200240001900300d440e050700030003001604c2003043c0700210751188a55100341d134038183c3d0081002a0786c80d180904403404440740071507856680d010020f862065058030ba44039040c949050554460050701d1540d604000700003141418590b42e1b4921a0030341e2a81070001d04a9240c1c156140160310030741800030809462480443d00000c4406a1a948103100380381c0800c44403a4500d11510a41c0030030103050160303004407604500118108864601c0c1c00140c0704030301c0c0b0f041c502070000701454035000016051a40c00110011191107000c01001030102c020000d114040e40c610070702c0c007140d00071110300c0703110701170741f01c06050a1a20340200c074068809079408882000c2c0001450590640c0000f00c6086254205 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 937135359 1250 937134109 937134137
    0x501110a06060b0a0e191203030e011104050a14011b0c1e0503010b04200c01060e100f0b16021c141b01080921120f060427030f 56
    0x30182c03001034000c841416464010000c009800e80a07490307111071042d400000d2151320f00c1d4a007008001110410f01841c085240300b07080c1503000b0160448009965400c240b1031005140844000b00308440003914201034250742e4143e5501d0712080c03d0410b50001d40c4174401e031141c00018051503200c1c5170043c45c1034000c00742e40d10b1081c9060884281c19541003160f00004211900e0284104500c2c1c0e071042c0c0701404520349034010300f03400b00960f1070700075812180031950300f5091001b5449031010f0504045180b0450034900c07210f5004100c4d030312940c0295841810702041e05403900301a118030300085d00e248564400e03540d08000d02c3d03103141c1c00c2c00300c0848036822440c008502c151844245076482400a000d45050698824441c0214450b0031030500613410709000029100150322501c0200303440c0c182015003440c0c5042c3c0141c6c0308501189024a181e0703001e2005426402c0050341c00340c0c604440030800702c1d203201c60141e5100d4004031344113000854042d042011038000d08011036541e541c1c0c542019286022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 937136609 1250 937135359 937135361
    0x3090d03140d0204081e010507020723030a0605181204060302180913031b1502031b070b011401081e0c09060a021b041e020a1e080714130501110a06 65
    0x580c0300b102c0c5a0310100b040da4213043c0921700c0d89582e1b140c0c100240304900e807140e0042c1d0b590140303110b201101c0744440c40c0700041000c2c00c008859900350080580711000c00d6402d05102808080d6000c0306048846940c1141d401d1001511103581e500240c003041c141454190160300a42000c8011540520551544203549c0d8548a0070741c03141d20454155070f61030744e550400138405215549034440c0d0f00031100c10003010034000051200408a00f110241eaa031b0340b101e0407680b42c601207252010310340c48003144c081c080054410f800741c10394200c00e500c412054034007001101c031010141d41c0000425007261540d110349500343c03401c40d400f001c1c000e5514075210f1010041501c0385c1c0700603040e10058010199446120040c5801014000c10403601441103150b00454030401402000104c0c0b100da81c0060785003991806540c050303d040390a4001c8071102c12009502070b00e803820881d07110740041c8180d400d50400f8040041034840608107240301401150400c0b0055840c625050006047e91081c0da181400090b5a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 937137859 1250 937136609 937136617
    0x12030e0d080a0f023403050118120f0807080604110c012c07050d320609060c0409110910021e07120204020906120a0e0f03090d03140d02 60
    0x124050180e56203a02d071100400c03c00e010001c55003190854440d80701002c54146a000316514030061039040d07242e110018001c404015880181a5401c2001407101d004c240902070050703034010a103101401d00480000c9400c0c5034812400000f003842c90010424544c03244645591100d4081d000007910f003d440c21540242d04081c030034588aa449400a0303210b406810b0440c0c1c0810445600b20340310071509600251901750b64011140a80c420030124402e2020080d00144d940403080d01805900c01c0c1b02d030560f12501c0051491007128031815021817250300c00054218460501041c0a90030076007006241e00141030050280e40180e802404910120350302d0351001d6095803c280c00034005004a640c6154103000c981d0417100103070301704041c1000060b207075814000203a82d044030016aa244000b000800a004010410005030012401c102c00e41400b0741c01515801000c20880d1086c00384465010b583e84544000103801241d46071080d80000e00a1030348071385003100d001c401410700d50134000120403604 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 937139109 1250 937137859 937137863
    0x90301050c03071701050d020909100c0c03090617040209060112021902011401030825120905010206060d0f06091e0b06011b0b13140d03050a05150a12030e0d 69
    0x150002c01c0c0b0240b0344d0000300240444001c0100c0001c1507141900103190030588400c040e0094504000094071818140003c03a0020166002002a007648a800500700918107804901013800c140000c6030041c0110065140c00d43c004101c2d6a41f940e8079824003100002c0505024140304800302c002450031f465001030070652809a806240074100c0300c4009003501c00c0b08503e4110318488100500208040404850358941407001542c3c0c0c0060004a45028048030311010b0418034045500702401e90303000701d460301110001d82c02c0f00c84503185c40042040e0010035103c000c0c1001c00d94030301c200000b044d40c2c105083c101e005c0d106100d400c01d01c0b0190400c0340003c4040448088a1003410000a9a023061102281070200081c145191035903a441c00f01e1840b005c1c001c001c00084184040e403c007d1590011480080800709550501302c2107880500549404e551000c00c580c14407000864010708a0700d50301025400500684001c0e24001e0642e4a440c07002809401300081c0091041198445c0035560070024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 937140359 1250 937139109 937139131
    0x152404030812060d0f0f0314042c090a110a0e09030403051002030411010c0f15060512010b0a150c050d0c110d0c060f090305010501062c03030d0203040809030105 71
    0x1031000140a440080b0080103280b00c3c1c0da4464032003020410740c0034130489890380700344140d228124034102519061040c00700710b00a80030000d800b1034201882c1d800300c0c01c000068486071b028410f042616135491501195002c88940c0003014410204600000784a200d0350b020f060145001c0c0c49109040c41c608040b42e86001c1039200090070000c01100300103241a010b0300c03050450560070550303540040c188281c002d003410000c0081c010f40038030010303d0041c12220f600c6400007881c2100d00302160064600c900c42c4621402845901b0380054030103000701441c11000a1129000b1800c242d900e0900105815400080024940d144e0303000880800010320f81c03005513150743c0311442c000c0c84d0803208102c0e000c00c034034016003030361081c4800280c51008035400e07958581811032840305a00b100f215414140c3c0e1000c1d00350344c2803a0000680c103400071507003182c11514410030101d20212046c80c2c0300c140d440c2c09260313805910410980031401140e47c06035800030b10440c0c00e41d00c1c00110100003401e40e0020344190707001d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 937141609 1250 937140359 937140367
    0xe07050c060108010902010c060902060c012408030c0d1808070b18011718030705190b070f0207050904060905061e150303072307060905181524040308 66
    0x140c08100441401041d16800a001c5030929900003007000a4150005100c60348406050045554500c151080d80e5080720007040800e041220740d4035002181030320504520100c0ca80030500c10804000c40c2d02400d20a40188116091031808a07403410703c944c81c42480781042c050114910506000800060003100c48680d1244801445415070690300c04409040c4119840b1482c0030b58040c45580d036124000312600300703103c001c1c030402d5801d610405030020030728010b903113081d52945001481440c220303000d06001451641e650005032200440c81302d012001d640071403400c020a02c0c284c800e0726401489020041001045541c07002d00d018400d0310207100e01480020100c445048101d8015400035a0900036000990a4004252207104070003002e03010340748109104240400d03200c01c0c1c002c0744802ea02107a00c05540e0b910000c0540c4070078051580304103c05000c0f510303000c041140203401140401c0d0700d44841180d010420a80354608800c41d142004211000c1d090f942c0380001810041d0300030000c29a51b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 937142859 1250 937141609 937141627
    0x30c0914130f050f0709051003030f0f14130f0e040308010e19020706050a0e010b0f041a060a0903050f070614161407090b0402030f07050f040b03040f020111060c03070302130e0705 79
    0x15941c0c0181610003c9490003000c09c003090b40304807420441892820a8100401c00704401c41b84e6115207410000d206500084140341c802700380b07280740115103030030325a1f120040c0c888008440e80382003a10054000f403102d5005119a1100e107030700a4000ea4400302100e69121414400750aa80129505940c071690b01c20410004018900507400301455103002086940b808500041040004005490103281d89081441c8a50490740304241039810090105480300c2c03882030028440800b5000c01c858034080c034241d0540011000030060300707aa5603070b11428128140001900c6641d005511808240305d1080031060102c0c46805102d1170020354030f0007622b030b507608020713501d8262004100ca1134081c0340b0420401c02600f401503000e5400210f5468481e03941c44410900c09114081c1c4e4000d0410300600000344001c1000481003424400d10030388039418010783c00c0b0b003695150001150b8801d482c04080000490041c0310b13500074954010345d0a060005030351920742d014801070b0211803040c0451000681841 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 937144109 1250 937142859 937142861
    0x20c060a0f0528020a140f03091203040b0610030b04090309050f0607051209010c120c02040b0d1a100e0c0310080d050f0912030a0306030c0914130f050f0709 69
    0x3c3d1009a103424690b0440c090282034440d5443c0030300008403560701007601c0405c0c80c0301d4450768480d4180c1c0444552100c00801c4072880341e0b401a186001c01d8070a4204204a4515040550388595000402e03286159144400e0101140b40702e00b40300105a6901c400100a945910540c1c00003400b13645d85c9407031305d818141884003800038034403098401d003400e018800004100196444501c1603a11006840725078500040c0c400c030040100003418a60b0f51300c129144030303074003010784401c0c0d5001719400e1094038524802d006000340d60031009400c3c034161000200d074003401c030000c19420103010142d03458100d942d0a00d0803290f0f207042d20043c00070030001060000302c0603802a640081d01104000e02160005030f070010f8441c4c4030307400401c01000070110b6850704030790737072002d44e508001c10540030b40c1c0c0e8409001400a0041031180421600b03000d80090118010140e8810f140f020380614080d9006620351084072511002c0c07920b0115144507880b10900002003080c8505004006a2001000d8083c02e03e04100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 937145359 1250 937144109 937144111
    0x2010905010c11120a15020a031107020603070305060a050312031b04080d0c081318060b0c07030609060e0d080412020604020108010506030702120418050a0924020c060a0f05 76
    0x81c104040c0d01e505101084682000c00455030702240e2941c00c02c65480070381410107585240c050b10803d80031840c84402d51945d0000d00c0444960754041100411202010740305002d09030019411450a00c00030314024000c0d407045804c02801400c0702d100540d9440000d1030421004040c40f81c44034013005002004c0b55800000000f801c1d0581114202070911003003a07500c40c0b540b0001d034200846650020280941007045805403000b55001008440d140d0402d54007180c01c803604402061b00d00000094003a81600540344170f5a0a070740074009007071a40d16004060710365408282c030b100750f8a000d1a1200031041042c004001e2260302c0b24425442c25003048030036200040681002d64100c2d404100060784d0050300c0b541513500849001d502c1e84c41e140d000320310b049030b500e0308004404000036000c2600340742c2d94084032205481c2201400540c0d00c0b840c00c2030503030380350f01002080b04210000d0400f044c910400d885000300d090043c01800c4c03021030b0050302c0c075201003a00c028080c0350b40c8030540700f41ca42c007502a131 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 937146609 1250 937145359 937145369
    0x1c121d01025a160c05101e030f0b0316050909010504050312090f1f29150c03040609030c0e0411040c09030203030403120807020625050d0504050703020109 68
    0x24107840d040142401052540030707400d5000307030106400600101035091050340c9481c00c0e0080f00d110f0101881c83c10030f410f0101406140c0c401d450700e20700c0c42c0c0e1061040100e20301b900c516058124855416060640c003400c80c041d01c07a00010340701c002c1322940342c0b000c1200000b0f007800360700043c030500d25001c107209198001034407202c3c0c0759040c0390170040030600020442c4c10b51074510b0030602c9d850369094601401d150543e8201c030b0341c2d8000c10403040d00703500b140b07500c0c2e58064582400811111002c081040e8070722201c01c0208941d2160741c500d141e00c03072034080c02c0b651410904061140ca00342c000000281103600c140c0105020800d040e41c20b00620089041e2000900803d0021503642d041075200c1c1c1c40400b1004000c1c42c030403500c820301001a80e10400402005503400f904894803981c4a180c1700f5407410081c00c1e41341c0050111000100300e50320000d8507500400f105269099082010000c4684041c000c1061900784041040031140c107034220322035140f040340548050b00d0709504610004104000035440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 937147859 1250 937146609 937146697
    0x9151803160303080c0d0c020703022b020f040219031a1c0209060604050a09021b150c070507050d11040c020606130203090a080a111c121d0102 63
    0x41215020341d6000084180c039010306240c0816940c2c0000e13458180710f6040d07030150043c1445070400403d80c000411a00b41c80c03086820101c07542c02c1d9000d00c00f0b1204001c0b1060100b80c2e1141085c00541000740007203084143c0504050303d45020380c07015503010328030500c40c4000603617201e00940c43c0c0701c002e4501041d0040d00b00c82c0c410f130030300d0b040c4403034501a540890040c0c814400d2101186240c5d40300d008440c02418043e2040814540e00c400ea000250000c1000050070011042e040c4000000496a00704007a9403151960361500e40100d071084580000d50120f505200c1c103400810596604151030100f0362058030090042804502407106441200094806540c85041404440d80d50003103e00304d01d4095890050f10386d43c602d0f04652500c2c12101000d44070b14000606450700c1e90b0b1005048201d5050346c412108142d10310b8107104045412240344900041c10200100c44070489504100c00c03110415840031540b00b11540041c2c00c90b8801c1110340e5180c001c01c2c44a40d0b84071408480c1b40d4402003c029 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 937149109 1250 937147859 937147873
    0xc050307150e0307030605150a1d19021201150323070c03140304060b1908060402040903020a0b09030a1101020f040605070c031a061206072309151803 66
    0x401c4a80d0140c003203400d0080315200154980c0707080100200454000030140305d103040c803010b240004072a03032600900610131100c01090708003c4188151018800f200121041c0e540c501d01035051907032104444144603000c000c4403403c458112001d5010700032800c1e014440074020180074045601ca0002100702119020204403200301030100350350300c0b07010360a00400c440013911381281c4d5145403180120155802205020901400703078030500c15880181c0e15080840300441c21546a06818840d000c0c13940e01c20f800081c01810280c00680c107062090040fa0540185540e038510301e48800c54820081d54408140700010380e6000806d841041d4181c0021444c045080500e45440d1065000e61410f000d0000788890400030300d1a901d5004540160080c004100005800c221181040e81d200748101c1c0d10104d100124440410b000e4040c0440d511403540c0c00c0b24003500751810203961084c4003040c510a000d04551521030702c1c1c801110038000030080f5540d944480c2c445003028002d03142ca40c0240e01000f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 937150359 1250 937149109 937149119
    0x605010e0a0e0c01050a0201020c100c09081207060b1c03020105060f1509100e060301061e0e0108060d060e011406040e0609060c03060402130b0c0c0118050411090d0f0c050307 77
    0x41601c1c3d502d400203203822951010001c01c280d0181c4152001c120305803040728958207c0d00226409400301d20704d00c1e41c0d82d10780540d44001d85c82d41c41e05406103124060b00f04209041c0020300355407240c61404e401503d142180d056160480c000300c210480c0031340160351a501005407500d04038038800352010045a80c3c4032544d6048240364020301074101c141d800b4510141c6126000303070007604040c010078002050242e90350784903100106460702c49145511024a10b80940300c0541c0207018180322844107a40b00d6000742c2e2440c04029103490719150983d0446d696804003808000e00780a41c40d00c1e10340383c2c1120800c0c0d04060080c441200d040c0404601d5682052083c481500e4001ca0100d81002030004100d072070b51690000070b0000e1003005003000c1d0115884000240820390079000d410403400340420380c7c100710700c03410065034424400e828040a51110b00b10511803460306034403501c14660880384403828840c846001c82c801c00e040020035074601c0081d040d007404000c4804e030789502801d030a40140c07407924540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 937151609 1250 937150359 937150363
    0xb37090303030e010905010603120f0503060609130e1006030b1012140c0d0c0602010f05060f01050c1207050120120a23040b071101060509151c0605010e0a0e 69
    0x26000040405484803860b0140349003d41015a2080e0800002c00c0100d036286402c0d00740300c01e11500d1001003460201070007004c50044040c1c03441407001030280745c9415040030030010b030484460b601c00d80702544c54000703540340b11042140e0f40700340490703280c0041d04d40d046051011004034000c06102210400d8141030201c1803030603041301901070784004408124800c0c411940d05142c2c00c1c0c0010341d000a240441341e401d05c8101c03140d010841b0034640081110140510311501070310412542c26422035500a003411030dc1d403007000201103c4013002c5c2525821844000c5c0700906070311400056800c2d0391600401c1100e804400f03141070700702004008080c945241502444005040107001c0c002e00c50b44d90842080d8079605200503270003100c4042105045207064a000081e80b03c095900c90005200c4d082d02c0380080382e051203810709484004100a0b4940c2c2d4036125895240005035036950002c1c4102a0070601d180d0719070542c080c00d03103d81d03000b181a6040514012600c080104001041c60404160092840b40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 937152859 1250 937151609 937151627
    0x29040f0504090c0909110f2719050c070204050f010e0c0a0905030f01091e0206030117030f0c0102030601030b09011809030513170c060c070b0c01060b37 67
    0x8191030128200741681040f11000700194404940c2c0340c01d00b0b401c2070410262002c280c065140441d030701d0508815200503c4100020100d05000c282d688241d840b0308207400e0343c42c2590240003036908101d01d4030310f14521019543d007034910344805d01d07003c240e080c11442d241c061580e010031030030702280c403940c5412040b00302c0510251441d400d488002411381190342c40340180c80301070a800303030445020880d0894442e008041044091701c6001c0420901540320300e0000009408a40050103942540d00303201e003014201552000780500e500c0104000c5002d030220101400c0c840101c080010f03100d1a101d80050700f60f070a5920078603c00c450003070051040e007040d07030000e03001250748039400900c22900c1d2406072107070b10500b4042e69940d44000b100040181407032103034200b0481a0780c242c0b100c481548060150a001c0e001c494803160b08840c900f4021004041d02400c4409942d500100301d095a0307920141450380290b5250360381c038541c44500070b00001e19410503600c0b080980c2044a032803078400d0004120000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 937154109 1250 937152859 937152869
    0xc14060c0304111302041d0105040b06091207120b0103050c0418030815090112050106170a022209060209030d090602062e14090c030402011e0507050729040f 69
    0xb01043c07410f002900c0b158003030301c80c140d4020002c55642d51a0844402401078046000e42c500304c100e000425282040d0183d1070210038080d000500b0903011300300f0490100890000782065225401c3c000034000d94804903031159074025a0296165419805c200c2d0501002c003145074000da00349950f030201e11083e074a07088240740e0149851400f54541c41c0075034500007001800c45501010400010400c14114021001102d10a10080002da90748280703207200d503400900d0114207034102001d50720143c24101c107082c1468074090308901040c0c41c2c610b9104100c41a1250983c0c540354042002c480c40d040400c8940c10b20025412b02100b0a0724060340250b035036400030840e2010700000c1d942002c00040b81c0c003203003501c003072844000c081560319003c103007004010341d105191040d041d44010805c20800d1000f1a0302480c1c040e5180c0318141c4210204c41d105c4100031316220200b1404120410204405010b910054019850345c200091120b42541c911202d810403031011300c40342000200401c0710903415010880d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 937155359 1250 937154109 937154123
    0x10020f0708031333020304081204050d020d14040308030405070e0c091e0a03150f021801080c041503020304021309051608070605043b061305071710050a060c14060c0304 74
    0x87e840c0d140c17111440c0501d82425442c60519828082000404580300030044145c5d42110201c808080046940c00040d4508000a110410051000c1130850780210761060080c401c80c0c02e2a0b035280740c1c01507945403c6400180046011401078a14605143d105080148100314406011910700c00504050340e2880010481d094118540782460b010380c01200d508911000115110250041503129003804090601c2c000355074480040c009803c204141d4090320808905841d103000030541c03d070f00079840a00300766417000d0045021102401036002d030152152090001e8150f240b020003000c00e00c0101c5801c030400c1500107103024412254800300b43c40c12204e60100080807041c00030000f0040340d454901c92a02621105a8031024894441d25580160000d0301c2c042d881004980c0345c441142c505592620000c0d41d050b00e0040410f11140c4065004000c248030810700c030340d03110002080030f8510b034414404281c810300c000f001d211a030340041c11407001e1000501594030b030001144886102c0188010925 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 937156609 1250 937155359 937155361
    0x5070b03071205042307090e0a0c090f0b06030103080d0507020c18102c061804030f090b041701140103030801050d0503072f0a0810020f07080313330203 67
    0x8400c0f010004403490f40d500398680700c04005d842c0c81c80c0e22180d045c0256000a818150542403035540017038102107280d0000540440c25091821250182c8289000c0b24410307a00d601515442c0d03520b04000314025481031000582d01d51002c490001604c600804a10035900149551034a03610b490003500c81c4a031700324000c800d090b81c644144007510145900b00c8000305228114104613510300380303034100c403044101585810503554801000503da0071a0010541003100001003000a070203800703101c510021508001d0301098a40c400c0d11120b07040784e400391010355031030744a03070228103400e01c6040f945000f1418045810b604584001d0120701041c0b003020702610300040a042803020501c1a2480903038080d040300002264900c0c014124a110403c0400407030340c1d5a5900e40e070745010880241194448405880c0c81d02c100c2c0c0d170201c020b4000caa00e060501004200800008614000940c030a070900e00c4000314074901828a40c08000300c4d90251017010521a1103e190181c0c03200d5100c1d041e0984100240c0e803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 937157859 1250 937156609 937156613
    0x10c050a0318030e150409090602030603251406070f030509010f0509030a1202100509011b020a03020705131413060b060a0813021c0c150e0a050f0301090f06020705070b0307120504 79
    0x5e031060303600030030240e03103041c44c04020402160010341c0254402c074200d459602c1501300711300101d0f00004044000f80980f1000300f0180746400000c40900c400108080e0626441c2e0b00c07441c0108018243c100c0c0044c60001c2c519005d90307084180341008428502d030480c106001c540120741e4500c4440030182018000411a0445074400c20507072110242d821014011400d010085a003e0f1908294041404020030f9000305650f00c000b80d1140c00302d81690003400c445160000f03000d01d90314800c1592035a40e07190581100300b940c0740008140540030700483c0003c8070701c1c5070034000212185d02800c2403040408000301d03e14954014000c1c1d4001c509407040e00340d01c0f603452001800884104510132000c0d80d01e04204000e00485400850480d146c52010144503810070074115031990122206940c001201003013070007103040c42e2458403000140035000150011458552901812011908031500c0b500086c2c52010408140581d00c01400b65112481c25070034556009020724240c4072070140403503554800641 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 937159109 1250 937157859 937157899
    0xc0304090e012009010f110a0b1b0a090e0a0b06120717070c020f0306010503120309010608150703060803040f060c0203120d09350c070503010c050a0318030e 69
    0x241554640a0009201034185440e00140c101d4203813a40481c4026100c4100140a495620610103d0304054a003080c0d25603601582010040e18900711112042c0c0e0340d018040b9400c0062218113060f80f15081c0c0d9518100141080603001840c5030070641c141006244141c450b241030312031750485010f90164550701c0c41405c84a148081d4030300c000c00304201040c0308580b40c001c404204514000da0391000c60103018030a041d601e2600b84207503030701030b840381d5144078410050002441d00181310000115100d80d50300d541d42d1400c3c2001d600700040c106228288004990144584801402d82070080c608040c5080b03916940d0b0075661043c0c0c4203004819815804543c0c0c203008483d204100403c039540c8400210701188000c01d01c000c0111240001c00c1c01451100850303080d000c0010403107080c1100b0308104038150a0441d006450f04060505c2400e00c0411156428041c08a15241d691769064a4071101800102034801d0300c032041a00707c1c44808540e0100740d0103501c50740d030294144d0ba1038500d00c0010042070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 937160359 1250 937159109 937159121
    0x7230f0a120e07091413020a12030302070803010f050a0e04120305460e0604020d08070b0c030a05181002130305070e1503030f070f020d080307080109060b0c0304090e01 74
    0x122040c060040041001130041e4031001280c00000400069542c400c034030700c0301c11190070304007940c0814100400c0059200082c260100c140c440d01d070250a0500710340c3c6000c0550801c0e0007000710f06c1c1107607500707005600b4084600c40c014901c1000700c810500f00f5449803030711407403034600002c00c0545601c0010111010f58031680e44444840015201c0c01e042c51100201d0711402815500c400006500001c01440b014011802604040c1c0058070481c1c45550803c000e48107040002c40e0600c0c4188109004070f441203950620649a040c5000d80d00c1c03400e04c01100c120340e030007482388550600a1005e4072103030400003408030074450002001079981c908503440c1e0b498a0160303403006103144510380c07012403c1148403503c11300501c5c10400000d081d81d00501019280e0040384544001601e0070f015080c0850301035482040d440703001900c9888503140325210507465030b0040305d1079804a001203004011161003803107100f00500d40c50300d02a0500c0b00c144855500e9228912910440d16181e241d0a807466030300394000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 937161609 1250 937160359 937160381
    0x801050d030e030f010c021006061403040f0b090f100c1b0203100609021e1207030b13020c01020a090e0903070311010e01020c0f0106050109031a090a050607230f0a12 73
    0x83e5900c090444c00d1601924a480e003103001402a598401c2610034140651419621991104175108a440d074501010380c00080c01501e07500e0741e0590b15801314030310290650103445075030090010490280425480d000110502014052070004004541c5600c04100350040c5004603200c41006e4480c00028070309801d242d0400c03001c502e040380000b44009182d00410b4903900e80c800e01a414800c80b00c0d210201d001c0d6501c00028010100c0c000b0724203c0c800d600140010f6030080c40c41514030040b9190700c00700d0b0420045840c0d2a0f5001030110441500460364000034508800468642d1820200640c1c480c060b2403070003000d03c4400c91340c20519400a4002010404440000710f4488400e91a61a503562851030390f99000d5180040c0421294400c0460809803a04600c0381020220310046101d9003800c002d1002c0ca0b1402007041c5100016818071025020742c0705c0d40d64501b040b9004802d40c1d8101c518408070840b1801e170070802e081c0032221003c2030703401461050902000911515400c14050501d070901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 937162859 1250 937161609 937161613
    0x1e130b09010e1009080912010f050115321b0f0c010f0201141803091003020310090e0a060c110703030306060e0f030a14010f0e030d0b030d0801050d030e03 68
    0x4000399810154002c0540145200880e03452441211010007140c2c29068050000407080040e2042030070481100101030030740400000740c42d1180034030030301114002e821110f01c500d0b990100c804501da202d02644092405035000343c0d070428410203079102d00140c01d90030090014007c500b0b1011a590703840050a82158403003951044001d80827401d4555128081007404103202c0910052200d10500c220500607229200e00c0a503915140701d505d800340741c41c81002070755110130402d4070b90b03d0722031581c4035241040c07a032005a142e003007000011000020680001c40c001c1d1401c007100d480c504000032a8591250001000a40c001480b5022500381002105140303a910400100008142d0b140d48410300711881a0313205d050760035080d0b00704103005424605c01641a0300c0b510320680815428002d038084075601000000e5201451910304d0151418104120310642011900300f000d41075501800f14125001c50182950558800740a0561749040c01424050318411072a90304150040b6903103200f110300101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 937164109 1250 937162859 937162861
    0x220b1203040b0a030507020a0b130c15030e0d05120f0a02190206160c02030c01081f06120509031c0b0a0504140a060602030405031f1b0207080c091e130b 67
    0x10b40c00c11594054100180024030305400074400714404a00b40000c640c0c40a46034680d5100c02c10756848005104405440750b145c02c0000252084407903041601d855040d0b1404074816415064141c2003121444180082c003004000b144c0c5ca100a1100a66100f41c402030701e10f0742a1200082c040080c002d0003480c800c41250080400340705900055000e04c218003840e204034003c42c03606412507681d4071155000307405501c07d0481e20203942c0a511015405618010146210300c407805150010400e0b0b58030403004101d10f01000c540d00c084901580e40e0020081000350b260007a0b61030604840450786100c0c10b02d070390790f4811141c060703507030343e0030200091100400c02d10107031102c1000403400c0c0c0c02c281c40c9025014a44040050000d0010064030212200100641420440c0086048643c9107406000c42041c1d07669030360160490020400440d60501036005190007420048507078507061268100c60700c515903050402c14111a0356440d2001076540000c189010b032182a070b0307180249103402004145c4006a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 937165359 1250 937164109 937164119
    0x6010e070f081504230108010b0a09020a120c120e0303010b0702011b050d030501140d0305180d121e110d0f0c0b01141315090e030f03090615220b120304 67
    0x80035141440d100f17207107072080030b0b6603d00a603802c031071401e08059002401701a08100900381e0303034068442d001d13007424400150040518140708407803070f0207140404038400391000c0c49886402c0c8500301d00301c94850011480c65050400c0d050660048440080c100194000d010440d100024040011542e0010803100c20102490001c0c002c1e02c024002c00f42e90700b40012289643c5d141814480300c2e401c2d015118185048403101b0400c40121201c2079031904050440985000a10700b400e800031a925195241020f01241121040c0d244803200004420020148906040088040341c0d0441c42420340c10100780390101240140c400e9810b5140c00b400d5030024400000b541048540005000c0d00c048401c1000c585450340c1040444e01031507943e0001000e0a136081c00100c545901561130340c01c659040700e040c11030b804105035041c1e00894411001c0e4000900b88090440c0715411181c130210101e890700700c00c0d40300100c0b8540919000312480000d5490780c02c3c00805454000080490120301030a4a076220785030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 937166609 1250 937165359 937165391
    0xd02150d0f510627172a0307050102070e0f0a0f02030406150b1201030f1109090a0c1403060a0f02090a09050415110406080c0d0501140306010e070f081504 68
    0x64030907007001c20320804000100c06010400c11110300c2c1204060803c0500741030300d0012518203240048480c2c4a00c000074500085169041b900d1401620300714040400b003c13040c1402c1643c0d9034046815540212014058001c1030605603a206021095591696a592030349501504001c546148440d2000042c0018896580c10200758003d1801001074680e945203036401d064030074044c40d901d1300c90042c0018000240a289a400132600800700c143c45901c904001a5500344291916545640302d00604000c0003171442c108001400d5502105012510703040100303031906001892180318a6440c3d490004492040e13060ba00c806e00094102e902c81600c48030104010a010748083e03400110b424195030320b807100d074091000802030200c0c8031410f00b8a806401c0d6400800a0501d0420050a0094052101103407150074002c216840e1101c003010100010315080a00c10b811403d0b1541262042007201750304980d07607480c058002e02e002d4215946160501c0e402070800140d042d4418141200d00c0021100d07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 937167859 1250 937166609 937166771
    0x90a0602060906160507020d151e0614060702120f1c02010f0c02030f21190b09161d03150601021b010212090d02150d0f 53
    0x44a01202c6640c0c84103503041d0350b01010b0010b5138000074805c01034403006003000c0c2000100d440c890b104400350600d00803400400d603010b1400c1008030342440c104115182e182401446c0090807022204003d1605060200c0c490b44600003029014421001140344801c608200901d1120294800c1e20015020032111601c1c403035020741d003030f0015801d0030b41d005000741e1244500d008411094001318a0030600c5220840d10f038004c1491400d0101609154410700420070610340d1003103030788030064000d03030500210200883e20f000742d50a0080e4000400c015441c00ea051015400f444c00d41083c00c81c0109050901048040f80110150503002d907020710004201002601405100c09800352010701d001201024000c2d02c0c04110140180e00a1141c02080b80c40c1100801c10ba00003c1c044848228803074001c100c90f21034000c2e2075147d0341070004542040d0b428a21500c10003043d11003080c488a9001e5465101001100182d0b001c240c19030300a4404440208050300001c03c003440d0703a00c540151454440220141c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 937169109 1250 937167859 937167871
    0x30402190e0601031406101103160809010914010c080c0c0409080d0c0c0f030f1e0c060b01031802060f130e070906031e051b31050303070b0903090a060206 68
    0x1003020780000d0102d45100c003151046d98041c203003500d1764072500c80403502e68021402030540d5000400240340c01010803a8142c0900d401141241d5580c2d01002c0010b1001c45194130090403104c10000c2c2c19141d0707a00c62007c40001d50400702541c1c03540200c840c507604141c07187d40750981c001d141c014214100012400901400001003100700a071a9180c88180c4031400300c4100204090b5000c0d15250020b409003850308001242c2c1c0c900207110b52443c0120300786040b20080e4507404a403004070343e58200441e600980700210828a018011000f4032405225a900d41c01b900901c103860114560b4a0f880b144400d8452512121000b5817015580d10714041c19070000b41d1b0060009000e003140811028000d024504d020f87d4401000d4452104858000e4018075016001c00452051203280b01c82e01d83d44c00010707103400301703030700b242c0e030f400c00f5200702c0000d00d08041d608900091a101c104100515a030100989001c3c5422440d000d60340d40d2802080340c11880f8814240354010554800031a0b00d0b0f5000448a10803c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 937170359 1250 937169109 937169111
    0x2090d1109060a05090a15051003020c0c01110316050c090f0f1e070c0c0e070e09060f1f09050d0609060507181413110304030f051806030402190e060103 67
    0x902c1d00018002c040d4100d000345a0041141c81c00b044801246a0107005031414510440400340e8603800058020825a15a4000284c000c50f2000440c07000b80041c0010070000d00300030382d41c00c03419042c0310740f640202c80c0468a00003900165106004007030020b01c45103400203103001c825250100c0450241a000c0e142080c281c00202d00085402c154025081d020907040818040d8950365200121403129801310b08540c080c0380c580000401140d11804140248082c2d103d0903041c944480501040540c000c101e10720442c02000e00b80040d8036030303401c8403020141c48030300c03130007a550500b0041d40d00d0344003035003c190070011107941d800602c60306511040ca00ca01c1684148466120350104503042480c6400d01d10404184400400219445031048804604050015000512a400c1c100111130001e804020710362000000c100815511650020700e09407141411400d203194a00003482002240c90524046e140020228040d503030703219030034000002c04c5020200318948881d02c2500704e45081e03a1040c086 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 937171609 1250 937170359 937170361
    0x602040f0801090f08030c190801092003010e090708030409060608150a0510020109062a0504141012021c0b0406080c0411070c080a170a1d0402090d1109 67
    0x81043c020a15003640045a41010200507120004940d00143c1002007030081004104107820040d1450f0b050440300351500c0e4441e42c500051141601c08c21b084102c0c41d10310a01040d03d000c0802d070300360303070544a4881c81e050559582c0380200340b0b4600c46800000c1c07548000310b40011081c85540100090780c0079981c83c0135068485e403003048a2254a80d500c9503018180c0c281c18030490030041031504070032000c1d1001250805075a00c1e039401f1038912604035061840f08101d0818901e041030041d1031000c40a02d800381c1f400c3d00c3c0c5101c80c000d100320249540d2045100420210317045220740d1017600c44064501c401c55907100c0200c400aa4807180800d0162500d00b842c903002c0c002c0c502031180c441221142800f0300054031000007080000e00c080340c00748a00271401c1c070460001c1600518208007a0121400a20a50465051005240c0c80b44031602962010820510104e242d0004020720104050300303090200622480000b4007a029080d10309420090000c0c500302404144405404040d400359280501 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 937172859 1250 937171609 937171619
    0xf091f05040504150b1c1425210204051609080705011b0813080d0210021312151518051b030912040e091c0806060c010204080a0602040f 60
    0x94a8080314003403d26010035001c12428644c0d500b00f6442e2490081c04520303000c01c070280c4641c0060f2102d206403103c01c80c6841303842410104200a0251191410344100560318500c0c0c82e80e01074116008424000c1d020710f41d01800c0310405c45842c1c1129900270022f001d14609084091240307494101000001403900c4070000d50b80c813012500380140d41061303683d403020010f40c050214042003240d1040f80d000c28100403107014481c0c560342c414040c05510303001d403c8071401000024a0145600102050980704200f80881c01d40d180480c1c50407140504480011106242410501540b610b0a111280f90800c032000b83c0c1c2c488a41001400c1e6000190041c031030501c0c10303081c9000c03100c003242c54024440207a400544a02501f10103154025110000c07982180056104a61242c10a9104c03200c0085810305000c0e0044091103048a121104011446401c1001500420444000e88050b018002c00101c00e61084408e404480c003502030b4408881101039149230000007580140304541400242000101ba = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 937174109 1250 937172859 937172861
    0x80a0314010302060a0509030c03030d06030c0e2427090d03140f040f050102071203050c09030a03051c0908071412030a02280c06230a0b0f091f0504 65
    0x70582e50050165414130000d540c050b02e55a00228000307a240c42615000ca042740d804100428581c0c5034440c000c60030f00e10f0b51034001704180031500100e103170311921b1081004030b0b60042c04200700e0000e0307032520302c00080407100801e084016502d45e00c40d540744240042c84e0038464403e815401007e4200c100c5460012490048003115608014043e08842d554042421141c05006440d0418064603606030106490f565103030890780510422684003080c09000c1030a0780c1c2520070160301840711042d061070452028002520b40107201001801e20101040d601401d11060300301e01c0d070391015890204900c440354107114010b0380080c402204d9404459079404001300001c40c83d0301c0e82120504020782142c40e41c14024000c1c0d00240d5800c10548070000c000c07100d50f001c440300b84480340c64907120305000030150b0802c9c2090300c00c0c8042140c0398001c2220724528064450107505c0d03001038643c000007004d4034080b0000e0600c645020000342c0c400518010702c01417a9419035030524801000c84112070715a56601400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 937175359 1250 937174109 937174111
    0x302160602070f20010c0b220614150306040b040309090204030302030304121b0308090a150c0906030227040f0603030f0912020f0405100b0406030231150207080a080a0314 75
    0x760001d02443c48020004031f00c06c3c3c2154200482030300381c50300000c5098800200221403002510150344408003002035a00205155402c910b80441050302840c140000c03076501d20028100500860181c0b00082c00c0c18490a454009002d4454065503902ea0b05d080c002d65076081580c3c180c46035089415000c0c00c2d14045c1c0c600d203280019050103035030f101009860a480e3744000070a4040b0b1340c002d4507154000a940c80c4501e00004298010008000c09809401492102c1c650003207018144108404540c0b00ac50708400c4020701103110103c6610b00c03540011401406203249041c07603040c1800408010907800000c0d03030b111480180d44505d11560b41b0300c82044180400c0c203001c0c0d0400f04104030100242001d4000c5036001800702103443d20340c0d1380c400a20000358042d50081c0006035004c01d0380f074241c1c6149000d807400040410071818201c281025003001c607a240f84603004021001d0003481c09013900a004500c0141081c00580c1c0d900701c410b0900400c15404107841d03400007032810000340f00d4400944051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 937176609 1250 937175359 937175423
    0x904020306070c050a0b01090501060e01031a120102041a09090c0304020901060c050a0203070e010501181503090f080a1206051e06090d150614010507030c030302160602070f 76
    0x8201c40d4480b45002d592242040c1029121401085555400300c1d0010b0062402440d4050700003801cac1d807402c02c5c0106002d4100508a041500b0140c00d0b07605080c00300c40f40b02001000b15501851589002c06190081c0300e03d0740310b03200d50280103410041840320f0030042e14280d0000e5904400c503607603401d5402c80318070049400070b62102002006019442c40b9404500308544101c046810700d031036580004e0700e40b01c507a03400151081c0c0344400500c40c1e540d026000400749503040880c180061b04101c460450300311030040c11810580e45800d5042409803c1102000d8503800900f00d47e9075204580005221881a140d860340990601000045500f04401ca01c09801d118202056803003489008211160f031015514a51050407503010b01e01240c40c04c0103d00d202080740704000740386440c00345441d10344e1040c110f007113060090500c01c0501003a0401d50910b00a9403610b0016568541d110850000b400a40005800248042101010030444a41034039015000d182c2c81556101002140003401009a10b2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 937177859 1250 937176609 937176613
    0x60102120c03030a020f21062b0b0601140d0c0306060c0201020a060e0708100f050603010b090a0e070e070f0314010f0b071406070f23250c060c020f09040203 69
    0x141460700c0c2d0345e010704040c00101090918048441d00e01422101c0c400c005800e1498845042c001d0310b181225858030458100042d0060302204a45040d041441020380500b0180741000082e0b040d0f8443c00100122007182008161111510141c5000074a081e19640010901e400401f10304035001741c105102c0c003a0b059000b051407410300c0c0c0e0380002400040781094002d01c5000b0011900100900082240700c0c441030002a55809110360700c403d481c400b80100c1d000ba4036140b4040015203a030f0203680c0d403100f90800003080141b0041c05e8a807401c441d907840141f0700700d00c1d0710511601a501512440001855070380c01e200d18980c46070710a03680344007031040507102003a45030200846c00e003e0018000e00ba000d400386140740c0e0100b54202d03003061011a03032040002c0da40360150983d160851103910f264000745034500071101c01c40d0401546481500300c0000c502d12408041a41d0380407240e1100c071100d0380308d94491451565804040c1450f90307816000c0b841511143d000c2080c80c18040e12048c0700d940c0040c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 937179109 1250 937177859 937177861
    0xc080703140703170904060906060f031b020312100905340504090c1404030c0302090a061a2b020d11090a0e130b0103120306120b1b160605060102120c0303 68
    0x2d840c105548017440007600961108800100c0146a00c5940d0041520392217440340c04420b0007004089a132880c42d41e0401104960102c1d81459000080c0d44049200e4254082d5940b901100700c6e2402c041640540400d906040c1040840d600f0007084840c03151403c0e0b404101e40398030724101c3c0e04d00200c0d0400e8038001001800108040310b030b241c00c8065202007900341000d540c006009044141d40c01a042958800c1a0820800450070100e400340c2e44070200300c071b0401c0190304000746449800a20140e180c5c040e6004a0302c500d401e00d000411042407100351400740e100c094a5808900a50454165212842c2c0f90040c182480b00b0317050200c0719955001040012101d0800b6000a0100c8000d04442120551700f24010009001080e1083c0650b008080c4c12100788015040203068a00c1e541002011001c00b4642c60300140c06100c1c42c980100c10048060000c00902000c0c2100d0300659110301c0724403100c0c2035120705120b01580118000c22084c0e00b0744445209180000d0010f226604200c0801d0344200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 937180359 1250 937179109 937179143
    0x7050c042f0d23011502060c09190b1b06010603091a150a1d130f0b091207080903010516050d05100510030b030c0109080c09040f0c080703140703 64
    0x1100402282c2803108000035540c11000840751010140301e003c0c5801816100140002ca058800e80c000700241e0380300400581c0303400501329041d40900030f807a60203a41010201800c9042d07100d2510050140ea828540c1c5568086200342030109041c5500c0040f80a864004680c692003030080daa0301c070360014011241e0854013000d00034442c50040802c80401203031a00801b5950390b500300301700100b1223040780d0151181011500c48007071134080e01c013032400c5100750600c600160146078030081d0250451103850b015554007090600f006415a003c100c040c00c00940c5108014002000d09403129094008019584d500c60085590010041b0a54080ba2052100b20440b1a494020710313445100380b20200099540c0b00041045185081d03103c20100303031619450600f0b81003c0000e1700480d4424130b031242403607143c5010b8544940d003022045000d12044000503050181070040311150316484200c1c1220f1503660709105442c0c2c00310307000031a85030641c0a12030204010004026040c0d81e0405071189407400d000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 937181609 1250 937180359 937180451
    0xc050403080d02160302030d0c030618020c1518010f0608331321050405130b0913030206070819050423010204050406082802011407050c04 61
    0x80c8801910a4080008a8690700b01645903000c04e8031940081d9101c1c1055182c46084c2c0c1d0054010104061030702d0b03010070224100081d0003100084840c0c2c01030781c8460000c0d0072410209031440301009003880038184240d103801d4800d01da548000c0781c0001c200c90b880d0507110ba070548a07a4400c071841a4460040d1203680d490480d80f000c113082d46104d0350310340b1000c00544890400c4040303c6d80806030074018600002d01840801c075500c5400070943e11407007135a8000001c1c265020718001e55000c1c40d01060103d001072083c0c0c0c030601250000400210300c40c40c0240307600e900c1000341d580850060041c2c0004c03030a1706004409450085404e240e5a0b82d03050001c10b0020000c1400030700644107030103640d0602e5900714003008100e007442c96000001d80c2ea50300b4801404166800380e03020303210307a50100c28410070028495960344501f42d0740e0042d0b100c0f040102d00048540ad180c00c91600e040c03900c00a6242c040040003c0c03280c58848083d5010301203141e111a280b00c1c0c5640004070512600c0040660840032251 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 937182859 1250 937181609 937181617
    0xb0306010e180f060c0d1d06010603050a06090501030c050a05030a0804090c0504092a0e030a08090607080d02030412050405091b0c07030b0906130c3807060509010c05040308 76
    0x450219183e600001d42e450b8039003142a1010b4442c038500148204454400307000c0e080712040409106501d0813640000700d641c9610500c20001091f075541d01103000140c19400c448010000c250082c8981d58503030401c00d40b01c5060b889030314440da0380d03603070009500c2c203022824040c560f801c4094141420b1800200c900903013024840303102080340400011414202c144034003403020010303508152030002c00390401000040c9003000002407140c98041065141d8002402202d6a0307404075805841d114140040781131406201d0004000407004103400f00341b82000da0185204501840600c00c449981d2001034a09121340e0080980155100d0001203503601094a0340c030b042071020750000d00d04000c0b00c540ca41003508641013112615400030612038582c40400000b0b802242010078940b072200b19036202c60b032842d610b00c40c200c004001d43e06d04007041d81502c0c3ea440d00820b8000036a0b40140446001800b0a90240008075a0700380b03030502251030080144595096004030741c56035440e040c21a1146046600 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 937184109 1250 937182859 937182901
    0x11205010609110d0e07150c0c05060313051504030f05070c0e1f051e12030f0a030e0d02280206070c030515130309050607140708030408010b0306010e 66
    0xd200d10000400e42c0c003510501c00180c0400d034842e038845945188038015200501d001c1101c0f0f50015030300f845040948902400d08038000c0c207240c5000903072490b000e205c1c01d40e5940402d600440220802c905800c00c04155002607100c0c4090784d802c0c0ca0101180924120103550103000200b0a00c407891003180103000600c0000d0284009031203017551007480000e040401c480d02d0b061140c10038440d01059442584042c058401141c3c441549240c181485404c01d240c0b1204a108030020305510132284400d004a540e465401001d80e650760703101110103030240292520840c290703c01c55284040c100d101094000401c07280030550480412202100b03484611150700c280e80c0311104200c56000183c600340103400544c400c5000d00303032451440c0701e200d40301b440080130140c0c51455035405100190344400c001054410071211252103814504020303015500c2c80003070902901c2450404100020004080c1003100d102c20700a20450f040542403640b908805e110703100e246000c640108920845256883d000c4034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 937185359 1250 937184109 937184111
    0x5090d03030b03060c1c0917030c0d0c0203031b03070906050c0f030c0c010f050f03190f0504110a050607200f09070c03090902030c070609060b100e040e010b030601120501 75
    0x20480000081c200001940c1d0001410070026104441c00f806c28114840380f55080410807000056803544070001d0081e0b0855800c0f4200040003445042d0643d05840440078425020401d2500000c0060741e00c0d40f043d1602594450421800901400e40b0012644200d1032903968440080c0b0b0841c0035200354006010b83c20f02030181a0000324100410400307031000003000e800405c05103541030000f5088100d44181d80c0704100080101c443c0f1a00c502c001c0305d0700244030721440d41c03200c050300410400601d00c3e80000c9008908210900041c0170028401001810742100e903c50904d070b80d502044010700c21001c0040050000d0090400071011101c003c0700300c0f8502a182c0f08820020700005600340b001190350384d010408000d682414036500c20a03000280520300c03011031840c1403a004520300b17070083c0d441c0100160b0f12402c00404100346074000e00d0007008080c0c08400f0100d2846c030f01611102e41e0025040c059481d0092015901005001e03260150304054040c102503420101900107021881100360f50795 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 937186609 1250 937185359 937185371
    0xf0307080a08130b031b03060a030c0905061002160e060604030804290708030103080a0c1709010e0a03020904150e030a09140f030303011e0305010c08071e05090d0303 73
    0x1804103000041c980341c403440c1c0d2160b4a0300c2e0031803006000c0400d604104541a0240200401d904010052103940f1140040003034590707842100045c0d81141d260801040c5440b800d90024003441c242d0821801181c00701c6041d0045544907108070390356845a90220900544050308012400710030104c3c40e00041d02038100c1d85890341f84c0c0c403074000c0c50384103922004200007003075610310342c0c0010081d03d001440a00107203940f030b01107543c0f1034032581c1c04103000242810b60005100802c0c1c0d80210b80a05159074442c109002c1284480705200c81d0740c025103001b60100309111407410091410241603000d403076000345001c580d92201c1d111800060f124404085845a0303c5400d8502c0c080b04101400303020886582e4a100c01d414120005074a0b101000d00074020829000340201e6a9008402e0b03d0540b002c0b24441da80c1808000740f412051801980090200d52900c400480d81070350000c4114071039409030321160003403c01c0591159207817441700a200300084c002e011030107252420300d82d4449202c1c000d190100794 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 937187859 1250 937186609 937186619
    0x90a0b04090204050c0304032006011a091302090a05040501050d1217040b012c1501021609140c04180f02091c140d0804020d0611070c0503010506090103110f0307 71
    0x440d14191600245d059002c41040205a4054030010074011602c10314180d505c200c1d0000ca950b000c041c0510354001c00e010300560790705945e80f025914034210042c507841c15041140d00b400c0080d40070340035031801411846408125402e0601800d8100c8801400c480140c2c0401c1c1ca0b01d190310106050b80e2400c102003541d030032468000302090240a41d0083e12051541c3d450184145000e501d198504900682c0341e0982d442010140c00d201c5034054611640d404110441b900101d06104a11503440421080940c3c0843c1844c01d661110260303110111102580340c545100651060051344600902100102048000000d45411071040407031489409414a4003c2001942c0080042d0b50986d005424120010034806955103000318410590003070054445000402464500e0090002e80140350744c420b01401c202c00e0754014502d6140d025161601c039039081c1b400501e141600e10402d4400d60034140800c0c41440e02c100d90604880c0d200212408140081c0e083c4281d01c00d82c58045a454029010700080b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 937189109 1250 937187859 937187861
    0x1704050a0909020d150e0120090906221401050301021c0b240a020d030606021e1e0a030f020118140a02060f1b1606110f0d111b090a0b04090204 63
    0x75200006100100d0046481c5800e1402c446191000e00e1070710f900d05107901d5108c6003110464600410940f42c2c0c0d40140d45010103c0c070035074407546101c1d6841503403c02410320800395a200b028161903c1d0f9428815980c0d0b002054280c0c007501e03d100100700c1d404801ca4445040c02c0e8880140345402810182500c101d0b51000408410482000750342c1941c00941003404a5050101c03452149031418200312030750070500002e650300340c4651521029922034000440020081104441c2c0f40c03034480241940c4554200c03c00c4e26100b0201c800c0300812804403581c0005801030040e007603841e908034001441d014098464449213020040369400a00903c5003040143e150381c40240b403200c2d1309640d401e56135070700311002443d6000003607841c0b0715640000c080d0302c08088009401c4402c88035180780164500c3c411840c404d0078008014141c0b2028405c1e83c03102d18005800000b5244400410816110040b0b01c1d14922882e0326824a0029440348039200020b280b51115407043c5440d900c041c0c2300007110451035005c20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 937190359 1250 937189109 937189133
    0x60c03011d072c0102012409090303020f31210f0204060807060e040e0714031005040b0105090c09011e091806030c061103090108040204271704050a0909020d 69
    0x20710f003001181c0c4201c00d1960240158030034580030b4040c11090024103400c4480e4039140d8001d0390070032500c0300b5005042c507100e601602c0b02d980361900e40b195640b6075482c2c0c0c042015048d442001a100c1d000046903400c41c40d0030b00c44c2080b2500d60070266078011060303005200200740d05400f128440c44411120005da10b880c86404042d103114001008124142840944200c2446100d24413070760605845500001e808100e003005c91fa003800035004450b044000003403d242480c0342c812160b914050802050040c3c01034a503040307400940314141c01e5100c0c0f2906041501c40d10905c0382c046044442919808581b05006070b9001c407003440d1008240340c90f41c1100070401d014403107054025032124801e00901000003882801048e450030018140c4071141da45940b80e002d1038110a040c40b084e58006415525580c110000c8000507690042d003110070711084000410101e40c00742d0f4034407803d40052003404e403010201c50035200001e001120403490440b0b4400030745450b0004036000803200e90311100243d008a060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 937191609 1250 937190359 937190417
    0x1d0d080c01050f15120304090b010309020d050a06140105031e07150203041d0f0c090307031a070e04050c0412150c09030b0f04200127050102060c03011d07 68
    0x400181c1002420a1201451a0500ca2045c3d0400c1d4403100003040000845007203480700f40300414103012980c0142c000b8041d1400180d001101204031800f00100404c515140605c41d41080040742e54920545041c80d009000b419050b501002c800800850034100260481d100c0d1402c851040d91680180d000440c005850351000d64000b0900f071201c2e905103e904143e60b42c4101104000e4034180794801382c882405482c401d0031910001e151510790301d05200c0d01d4080d54005041d50b021000031032850f030403150100d902c0300010712940c0c0c10300420f02c0c1501442e8000e081a10110b4202410002d0305c180007805041c04544001c803d1150902c0504540940340492515031698058a841d5007002c2010000c020b245240310b880c080100400500b4040b0b0305029403000000080c886075036800180c400103000000c22150f106801da81403181101c0395000b2040d82c00c01c0c2d0135900740e0340307078005d00c0d10346c070300081c062444900102e0540c00c9586403441c148980c0b14a061170038241042c091500085c1010b681c50703032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 937192859 1250 937191609 937191631
    0x304060e030c061305060c0c0a03081b010b010906110a02030d0206060a0602070b07080d0e100b0a08070b0d051e090304030c36140112060506011d0d080c0105 69
    0x440c11140ca01032120201c0c0810566845141618070125134080000b01c4c01036034480e00c000b0600300100e0b001008079040c07510015010074130321030301ca09140140340c1050b0101003100c0a801c4520b00823101c18003403030744040e01c10f861b55081182031110a8441510440c1840c0140c880c2c220180b0160791f0030040504000100e4001c1d0000d030030903905100d80b4102075006801554001c02080022000724003c030f8110365041040240c58508485186014240145001c0110712032402c0d0302000350b09562040307804200890343c141340c01c2e80d00c0100c15100c1e00d442c4207100d00303070605100c00c8032103420b9600482d9101010161408119020b400202040c010664080c0890361000c2420b03c200a410040300000c0c000b0340000c40c540900c002e0b01d0b00f2a04580000100405040204111200000f508149090100d001c4101115038403942c01e0101d012680d0803d5038628240000b080c990b5000d080d10440c07024204651098806c18441440002c0c450702200303c0d034846082220322060003003842140e004901100b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 937194109 1250 937192859 937192877
    0xe0f0301061403010b06131a0708190e040b0906041a030d02010209091e070f090909030201020c120703082a03040602070201080106024303121211090f0f03030406 71
    0x83c50308641d11050100d00800d03040115903c2100070f03943d100300701c414072078403044a541c10440d0702159024803c1d00401454003c81e401c0c2030700c1400c40040c02e2051840d501d41000d50b5028042000b6203403013501240c0c10440ca00003091003401c2c940c10a208030b114012a107103000c210000031a00d0509886c141c040140d40c081002c404503d00a62500e070440000300c00000381402820710008003160140c101c40c00d000d880641c0c01d8506010390031803801080c841d0001c014602d020f04010303010f980070440b01400c2d4010400c441c04443c0c0c0040c20b440281c3c0e050f80e81c0c0f00950f51403400f13100c00d200302d521801e4a503072811076000d50414812401503118034410310015840c0c43c140c2c030000d002160180c001c1e50654100c905510300081c0d01e04403103120b07031401d048003141000e850860030b101420b00340d84130a182d0b00d1081c804014081042002652071400d42d0303660090940380c0403c042194018100c66100d590204800283c03450701e401d01e4052100001c00200080694000007841d41d40581d10030004180144 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 937195359 1250 937194109 937194149
    0x3070b04061103040c260f07060801080601150f03020c0303040f140c09060d1707080c16081905031303050c0f030102070510090f050a030923010f0e0f030106 69
    0x401005402401d0b5140d50342582441da9483c1e00e40d0f81070b070003030856500d08039102800c24807105071340186009400040d104c000c1068080541c030713280640101e801040701000001924040010510b048400481007079050407041301c02140c0e00e500c440b0b0440c040503000d001401c481c40d401d00007580150f205440b40441012203140c1140c4050f000c00140c441a00000040641503d44201f8a688803038201c075802d4905002d0b2804850060081e2010054401c0c0481d80f08100040c181c000c00d2400c441d981203d01c2401448240061a1000e00410700240c220703590f0b445210100d076903619402d0f803240b01681d040010001060309180c10913401611203034030050380c0d03900b43c0c101402ea0780e035001e80c00d8000f94a0051300b5250103543c1c1c05801d000c40c01e030a80e41c20441052100c9205c6548186074010248c0708540c500d420300410044e045d0259542d4421660710701581004a80000c58902c10103840d280c420142002080d5440a9420001500311441d00d490080c696020710a4801800300c907101c13540400080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 937196609 1250 937195359 937195361
    0xa09030c060813150906060e150a060905040518030c160801020403170a020a0b090d020607170a150b0f032d0c0f0d06031406061f050d0e03070b0406 65
    0x1e0384028103201c1d910007070040200358181d14074a1035070465184d4900c00400410075004203000e413800307080c81e840c0403004241d0324070b05024280240104080391030016060420072081e04201c1c4558004200d0740d400411850816802c425030201c0708061441c10140030000aa00310b40c80140b4030021608802040b55034030080c030300800094413040000f1410700b419551844030424a0b0201c2d070810a401094031504140b00308000240140c0c0007405041a0510010280d9030346200014000540038040c00905854420003003c0c6d600104081c222403a503c40700740200040c2042d98404c1700759170031640c01044604488005111210003030030120707500d140008010342011442040510000c101072805030249640b450120340080340214140d5031041a210320b1403c03842940da0710410141401c800205210304100c61000032107182058507500c2c0d1303403241009030402c1d031445150740605260180ea21040e00c1407018011040d50f4030000180c90b0ac9a095030751458101180403510410349400304420001a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 937197859 1250 937196609 937196633
    0x603060103112b020a0b09031009020a1e090501050105120411150a02150a110a18050d11130e0601170307023309060a142701021e06040b09120a0903 65
    0x1b00c08a103034104118a0300003601c510b001c07192001c00c1394541744203030706554988040ca401440c9503107a81d0f00601c4500003698500c1007c2c811611824985000042c15502420840e003e10300644008500c81c0d41c0d658072044142c20600710b990700210344821001030307601c00d203000340309840641d0010a13030004a40a003070320784040100182c030715509041310101ca0101c100c080c2c6401305e04034100b003200012450104c40103003000758030099001d82d1420b40001070200e0102600540d040654400d8580900710824100f44c1300e14510801c4140e10a00042051116050020301081c1181080c3ea19109040e00001e0048030300070792000703200304086860300e01c0d80303003882211000d086c9615805080074015000200e0318004c1010100c01e20001a07071000050048204803542d09401106842c450072a0050408030205056035141c09882801150030005d26451464801c66403020300400e0f6a6465a6480341e5003000504020007e102d5982032008c0300c19410046c01e000b511942d102a100e0b032650500c9040840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 937199109 1250 937197859 937197869
    0x901080f19050a060e030f070c1401020105070c02060c101e0b010903050a1e0515010603050117030301030f0203031306031a010504080d140903070e040c0e0603060103112b020a 77
    0x140201030100180780440c080c0c0c2869001340d00020062540c829003030961103444c298081007200010200200031800a0440c00c2d10b00300c41502240a842e8401a8221682a2094000301d034200c42c6d203030b0040c503000c0000c185080c25901510b80342906a030034a810f40e2400403003113803107404000f2170ba42c0040c8144a10005401c091a02005075403560321000d48a941080001d44645106985442171480031400303c4d40c00d079449003c0710b1340408880301081a96000b0302402d00007905100002034555411100004503205203409507186034610764031a08445807598089802d03000910030212030000703011000009141a480104421012030500e00d00d00445048940c1442010702c401e00080030b0020b5043c613200c04608100d01e0180802100c88024050f01007055494494a41d000c00c0d452107098801d401984140103002909840b900017015042d42114056090b80c000d9004101141d8201561040c0001c06030020322009024500e402c1762000f6006001c541c0b20580d005803013142440c0700e084005003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 937200359 1250 937199109 937199143
    0x172502090a020415050a170420090c0a1d040518070e04030c03181a040e1602032b020307030b10030501051f030e032a010614010503040f020901080f 65
    0x1509183d00110180c50410414080101c04100d00741407074050044d01510580c010186d4109103014501201220b60001090b50489c66030245130f8180c0c24810b0f0030301d0149840880540c00c14110100441e0012104400c403011550100c1000d2001d8889101da1800380e04089a10035050407980249403900511741c1c410403c0b0b440501c108400710343c0c000c030041e81e0b07181e0610300385000200041c3d158a0340c0c2d199400c4250310125880a041314448800018001c03103408451008076980d0316030140001d03004102200e03015030410059800620040034114907000031207041000c04a40312100030341203030000c0f101c12000c079a40d0b1b0080c2034903142c286401d103002003161030244103035818580410115401c10004a403a50081090001c109002c0c0e004032203182d0700601126207680500c0030a03020012127003109850300d480301d441e02c0e140d448107000342001c0d80c1e5645480c2e02c91120312001100d40754002003064400c40340d402140c02c010303514808114000c0c40f40000030100d1040c1c0d14040b605184010036130364454 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 937201609 1250 937200359 937200367
    0x2a0312120a0b04140a241a0309030c010e0622170307030e0a0b1b19080c07060e060105270a05130b0705120a110304172502090a02 57
    0x14440c041030300350311401c1c4074000714080c401030340407034094060713080f07110034581c10f0000f044000401c2e50b204100d0071210001c6001544905a0b184d101aa100e006e10a113411a4840d691041c0b40c00600458110b103541c03080b00d182442410f011421200c040c0c1000955422980c10300220641c026000394511300e01038403007141d119490382c2e8180000f40c2200a090812070210000380182c0c004d900680e00c8a009100b81c40c040f41d4585040602e11400f2601280084541e222044001280328207480b000709820b501d20740c070060120002c0e1112030f401000b80407499810841c0c81d0008041e80101c403100c42403100180407a5052000f003000150551203081c207102f150212100030106e091800d00c0e044070308404001040d80350b070110f182141c42200400f902c00250a02405102a0300a0080c0000542402030154070344038828070009a40502100400001082c000301d03012032104003c9400581826030800c1c80c00d98002c80b0040c0d0130045420b425880c0c12a424600294208004803d0317003c040c880c0110b10f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 937202859 1250 937201609 937201627
    0x20c0a0803160302010b040905062403031209160b0a08090c1c02240a0315150e0103140703060503010f06050306040308040813090e011406010519022a0312 68
    0x540e00420b074009000d800d950110000b0f160007035200d64414140940f090148010300c0c100f8540e00c038025500220b45c1040500c0314421240ba5080c05c482005009010350324042ea80d100c80240b40a000c0c1682d003890003481240c0c0c1103160750103441c20080103200c4c44680c80f0914110080c14080d401840340803150480c0100070b40a039104080416410810b400c0b8805000c0940041000078040000c0c00b02201c00701455025010400c101500c0e801d800c664003840304040c210710b100c1503400c261040016100c2c06540032140d0b00d0140c4002c1107a030310185400034558190070240c400519003a50342d40301195580b60184020f040a000b9200e400d912032906004062070b02c00801d56510008201804011720b13203011034200b00d4140c003190400750024403110040303a100d2081c1d0300103041d800c480130f50075842d0000b403141d40900e0145003446500d058403054207081000900500d0700900c10b10100c118040d0080480c0e03100c1e00f0041100842014418107010002d003182818600480b0f60030b840d18080c0140300000d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 937204109 1250 937202859 937202863
    0x100804140c0307230402040906030b180a140313030c05190f050d1a15090a0c140d090209090c0102060717240d06090c050d05101a0916020c0a08 63
    0xc032814400104441c1c105005030240306480c0b01c02661740940001000100390040b60070a2094034000c9440103010707252130040034011502c000040800b60401090b0070b001c540562060246019090103032880d1181d003208291040b1515001103031b060410040034444d40c04c0c4081700f43e1949446100a260b05414400d10000c0740c0594410f2520647c1e0101d2400c00b0803c50300501280c2c0e20000c42000701d80d00304546070500d03580c1c4000c19a0700903622140007402103022070048031200d60703050b190121000c208000000250740051042c00b603464454610100680300d101500d4480c103d0b0801621a00e1001400241420030240c4004104403100404144010707100d044160080102e04201001d41c40d44240d0340054440e58405990240800209030180501d6400003902184164140642c07e0740f15420854402007032040036007a83d0145c1e9801c3c8417208a42e0086081c0c010016a212528503840700142804204523640140911900b51341d404c066010440c9000d10041210a42401410154034036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 937205359 1250 937204109 937204123
    0x2301140c1c0c0c1b0801111c0c090f120506090625090b0c0d0215091e28060e15072f0a020a0b04061403040809100804140c03 55
    0x51102c0d5034412441ca5540500e00b03403540258052401d008203107915403d550f2032a0184600025942480144e0381700500820845d128580900140080d80803e150306000602e107040310402070040302c40010403403104000800004080d100c0e030110400074280f41a030305092018100116a6101c40240400c206a202e1002ca034100c88002810500304141c130210303407078510ba900a0a9900b400541d4a007900d101145400ea2640c45400716025602001c0c030351410351404a4100030240c2292910080440000403c0100c208a94003120307064005c181030842d08245100c0700300341e004004601001000950f0241e14604c0041d9005001000d035203250940307071194010702400801106801c0050038000043e24040d045c02e840d25210303210101c1015072681c0b05a903041c207a1041d100c034800003540340328003001c84081c0d40207a41c4110040803194404091500050411a41c11106014814060300c5651801c08244200c1e80d400c010360a141c24030391031541c103c5d031402d2101e4110254040513610005034103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 937206609 1250 937205359 937205407
    0x705040203221a13030216030302120703180e0f0f0403120e01021e0a090e060604060e010903050312010e150108040311071e06030e0604110d2301140c 66
    0x307614901100d00e402d86101d090081e0a074200b01002c403c4c480602040a001e0b40d030b4510980031100b031b018101403001c040321a01c0c407006005a106c840f299800c101844007134030703052b0f2190800c000505210f801c450300906064000361030f90383e4041d0030403c130341c02d40f038079100d42251210b104802c2e1400d20740c070000d0200154140310310f40c464a4003105901d50b01d09604036a80004040b080b02203d042000740c002b659800306c0303860000203e82d640301181500d480b0701800d002e454001d118030314007442d107034083d252600e0010950341402040340c000000314105200034101c0c0d2102c03419104066041c10244c102440e0302915240381041c900983c5001a60040c0149810a4040c200b5128034200410318034540700064102515404000c040c11460f41c0c0d85071b100c9015071341182c1b400d1096882001105541c0c074001c5074040c0601042c00e501c4c400da0b003030401110340703441d0298901ca030091441683c180206040c07102200c0c040c0c2c0d0754000740990031412600b604c0d0040307031861400b8684403040c2801410b44d000002c032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 937207859 1250 937206609 937206661
    0x61407020607031704110415080622150f18050a020906060d06080a02030f0d0f050706020f0a05210106050f0d020912211207050a020c03011a030705040203 68
    0x9090905000b80b0700341d85800c05219130040d507417605140901200b01003440d6035025034144082c101009200231319034800e88007200002c02c41661141094869010404180010241220100700219452550a1600c0d1146c0b02020414849043c1d0300c1c1c08450041c82031802c220f5241640c840040c0010611100c4560100d590035410b480d03000000f68a8495401e8208840346030050000f0003035800f28050714110700807001d0f101781000042c041e5466401c0403040c1000100701d4a0006d019500a03005042d529001d04801410300c1510541d0403141d500515100010450104011001240800c062140114005140c1304903515203000940b190103901e1100b800e407140401e407206900000d138140d40c03848000521030440c0d0421011110344076500042000d04449901c503a00e0241c500761011101916151140604135130740f5418200c41c680c101110100450107043d425401c2c80e03800b402000340360b05540344003841c100c10050030180340000726800303030340141d00500402c190940600701c500c19080c01c10740 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 937209109 1250 937207859 937207867
    0x2120f03070e0907120f0b06041a131212020c031e030d0f0b0913020d0b060111060103030305162a08130909021c020a03062d0b0103060614070206 64
    0x20064815200c0d03040754076006154801006a401e40c0403640484000341d0090401006c2c40145200c400d030780c403000e60780381c01c202d040204001c0b1a000412045100381c640000d04c0c10300d041c2540c410b8000c2c6c0705c0c1d40011030700300180030341c0000c0c0454080044040c00752400209500703560300020030307128800034105541d0906090310120705103c050049078104601d07000c040043c410103121140090824200f2079000740d8002c030008010b01c480621110000e40c0050000c1c0b0f45c0440e599400c5d0101f00024151410082c84560364180c00108001603400b0f14802c1d103002c500c2e807920300c8409010380c0b4042200400c10406c0700d400c0c0c01c20204403043d24103a0030020031045981220741000d104500c9407103403518208040c0302c0005101c00e1241e005d115240e2007203904c64619105c8100705400d07451071920296220300d103000c04000255003070340b00300d5040590f40702940c0e801c130700c0c4a40340b64100891100442c6071520344049c0c400c65a414403c0801800080c1020000c164240c03800c20040d00807d80024001c2c00001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 937210359 1250 937209109 937209121
    0x50a02100210060801020c1204080a060207060209060a030f0f0b091b09030604080c1209220e100f0608030c071505070804150212041d060f1c1202120f03 67
    0x12159182600c42c54100340981039868004a000358400a0701c0e1b4154025541011001038013081114200d030010030061812040c65203503400258090782017110b007194200320f1681143c0b80e600252454940329280010880030b0081ca404c02c0e0f524145060f00118500b40441c401550ac040c40e90b60059140d40030180c04041810f4a41058425030580036070502c0b0740000c000400045000404e181040481910000021260102c10500034000940d900074203008441540116511081c8406152820045001d0b500ea4040c00e040900c68290201d8803038441b50055560780d41c4c0d02802000b080c190f4019481c10300d103451a03c0c0c1b0b8901c2c901580c1360749045441140003603131143d8141d446064008800640e030b0380d911120708500044081622000d80503c1400c04400c20504050b2421103065042e0081082c64001c40d100741048010201036010071012030b8103e05444007601e610140d11054560809180d0310700300743ca01c44891480d800c04640c8076007201c0c03010007200400d45003503901c0b1920342500c0ba1182c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 937211609 1250 937210359 937210363
    0x7150501210f173103060b01020a1b051905010f051e0d1a0307080d14040b0f0405120c180601020a06051f050f030c10050c061e090604050a021002 64
    0x800d4060640c84a0b02c00c464002600e520040000c40c40c281090105030f0106903107600c4c1c44010a04465550000300c0042011441640215005105c14810f035101442c5913079030090482e1000d01b102450184601003403041d820b00400b50400444100c0224802601d0040001c22440402d07a401c420000d01080560b1564003a80760745401040c0303202265120021410303864010409440f841c030380303e107012034442c05c0350401065000680d0b119401801034140040010b540803418101c0450120b18100400500001c4040180903c40641c281d010390300c40c40e100c20081401d44d80c808040340340d000100590740075620b040c400c980e9807080c43c403144096500c1d000140e0034411032030740c00f5080c44e0400301000881810101c4001e00009060691041e07941c440042c403807881540f100303d503019808101d07018030901d400700d82a006551140380961400c040034007080e041c240140d44a401964840d02d108408541d8030b00d0159100b40d6610003441103107440d440c2d151751036608005c00ba000b61008800c0e0324600e842 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 937212859 1250 937211609 937211633
    0x30619150e01090603140403050f0409020712020705010503070c1101031107030e0a0b0708040308030c0c1c0906031a220e070e010e04051c1209080715050121 69
    0x48501280411000c280003410010000110900248200101141c914040d1043c000c4c84007005044c83d4a0f43d58941d4156416403100b402d03416200001d00c00024031540c0741c001000340a01c5036400001134040103002a16240ba613400850501c1018420001150740c00020030020681020782c1150a8000798010b900400c520500010040c0b4006107050a060b00103402640b00034050350310080041c0c1c0e800700c04181e402175400040c06114201305c2000420050000386411280325400146071006202600c0e1a0426210b10401d0346e20b40094211707010b035003290f8110010a690f003418041a09418490300b4015010326001e0712030049090701140c0d403c0c50300426413030710076090010030603034190100c2c81c1d50326140c1d171040c0f40c4c1d880111000400c54419002e0f5850040307501000520f02c100b00a0382c1007009001d1550444100244520090107040c1c0718060740c04020300501040da641e05090034450300402a0050802100b070805004018481e4610b000c084c0c240316408140c2032a40c031500d050650320381 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 937214109 1250 937212859 937212869
    0xc081b0f19031b0801120b091219020f03040b04050d171b0124050d030e190509150906060702010e030a05030307110a0c1403030c01050a0507020106090501030206030619 74
    0x1041e4001807100d405511881c035000c4000200300c1c20000c01e0804076050744090003901c0b82840c0c03048200e400600d071458155003020785513064482ca0309031010b6660b01c0360011040c5000b0300c1d00380c160b40e12809406011041c0f0300740807075024500d400e04000414a041c032032032155078000c5440c01d20310024802c900c4400300a01d1310311030b00165542e0207200700a95800c06000700400f41d51810003d00075043c6402081e2200410004c09844000d1030701d4100810101d074018103505202c070002c25400c241c0d80b60034121b00612016011400b66509000c180190118002c0003500054000d07101c90710030340d50b4010410b40c07240088412960760480703840102c5148000c01111601485040003800030000088040c40c0304421030780d120b0682100c0060305a6840303121007000f4012044602047c00f005854104050200c00040c2c120307440c1c4607261140600315001103400e200c07030aa0310010301c03004650a0151700c00030b000910040c400c0c1d50440c2c00081d124400030301014410103843c003100036000c2c032050000d00208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 937215359 1250 937214109 937214137
    0x10e060a030b19151703120a0b010909140a05060d051b011206140f061c091703070e010e0103090803010e07361d060d02031c0207090c081b0f 62
    0x113011003c2c14503a0300d14014070b84010303001080110801c2d0000103580d5800b260401c403040c41d4841d4514413008000710326660b410007421801c003041c00c100c24024076040408801150f8210f1605004100403540c01824031446000c5400221021890002d00000200000b00440341504400c1e001030711001c212110030140c40d408c2c8003000440c241c03220002100c01809680841c4181c00c14000c01c0000e2083c2d404001440d0340d4a25103c006c02d06a900030b0b600d040c400c40e01c20400c40a00780c601a1a40c108951030f0780002c2c0e001030041d421756404603044d00100c0ccc0a0070b0a1205941e50381e2081c1c0b107400140182c0302070340d07514800151500d2154010501e0f07d51002e07030755000400e0102c13000c507605044401985003400201000100d0000c04480c0050445e841080c0c2d070165181e007810003c0c02190040c003603a040c800c1c00c000001a0300881070ac2c01074554250010705c1344a03c0c0c00b8035002030b41c07d14620201800f00d400c1c20040d107241e41c810344580702d039110040103699007104030224649000d4606495504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 937216609 1250 937215359 937215371
    0x327030d02030c010f020a0c0311011d010f1d03070201110a02060a0906030506030c0904060b1f0e040b18040b0a020f040f03050c2b0218090102030f010e060a030b19 72
    0x10394002c4024000d00e00c02d08020301ca070f03540a144800c107920480009600245007a00282c0103e072040a84281c1f2005d40c4001160901101968040d0018615900529650341f0320820b56a03091174841d0700345403540c845030000c140314201e8025132a4003903410041d0502146d503008c02c80108090218042441c0d00916144e101c170415117000340920602d0007a000440c2ca0100032900d20315000620501001d070040c404c103a9960b65680e1403002d0b0a040b5480b68225400000079000700c3ca05405040c05c903507042c0d80f14628035000c002003005a0f0701050006000d410510040c10300f18011907141039015400558140c3e441e10307400e0180d0000e2042100c4885440130104c0c1c0031460070b00c0901590f084038040c82c11620f054980350200071514a00c105689420205c0d2018003851079044034500407450700090601144845680d80e1044115040740c40c00840d035400010003034011100040700307003d81581a03903c55686090303000308402412a00020f000f004490780002d180b03162000000d074000351820024001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 937217859 1250 937216609 937216633
    0x50f0a02030408120f0414041805010b15070c29030901050403111501090b1207080a1e172808060901090209010804080c0a0512070215040602032703 65
    0x22500b0501450995000e68aa08211085503109881c0300c07076601c904141c940340ca00446001c1c1ca10922904580164903010103001d100364020b403032510a800786001084846a680400000e4040144901e0686200380405408200c10040c1c20068600c10000702c1c82c90040301c000c441003441322124460032120004208444218190031080c041c81c030980341c0129455812400b2030700c5280300320504a07400ca0315401000b06a42c9a00003c8200c08c0140444204d0148420340d507003090320a070481c60140d80955822010450500d03031200030007203c240103070301455160351a07011440700d080c4041401032000c1002740001c5019031814402c12540c513082c8000314054440504802d10440c1d515100f0550f034000044c20008600071202d0119050703440050036611592907982c140c020308040c100314801e1310354000018404100034110080341c50803094407610f42c1e104101001c080b00c400000c00b101c0a0208103d0b81760000103866402d031103140032980b10000c18001400f4003174141040c0742e1503ca0740040d420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 937219109 1250 937217859 937217863
    0x10b060d09050106120506070f18080601050f0f0105031303200c0f040c02190507030507180f110706020304061b050c0f07060e010810120c21031e050f0a02 68
    0x400901c02c000030700104c0d503141d10b000d005116940c00034005810110002d6282440751a41d9502e00105e030800e40fa14000c03130015440c00e03030308903008032180b9400b410040c0418542254480e4443c0c1c0119a0780d15940e440d213000030854000503200404074201c030032811080600400c642601c401c0000e004540b44022204032903902e0309104078850191412600070b9403031741064010802810900d8004100842c820042101106204202580d290140030b1011001503001d108590003000707859410010308699005e4141124890281c00b903a1910f8001c040d41d0401000d02075614540d001000161207545508207a00581100e60701c50115500303d80106003202d4000d409020a041100104c4800300005e20425030388032445d00031070003c100c1c10521141150310030500150b200404090001c29141e84070b040c040c0074807005108941320780c40600180240510040c1c5204008241c0d11082c1034201c440d1400f074800d40604500a0718441340038000300300640036101b150b010849003201d0369036642c500c1070000c2d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 937220359 1250 937219109 937219121
    0x2030c011b080609090c060a14030708100f0f090902061b0304061715040203091c0f03050a0219140f16051509030a050901030e102408100509010b060d 66
    0x450100004140c103418058244e41c030440361a0001d00c100c20f40c000801c1420b4000110200c1040702104e0304400421900740594001c2840f0b884e00400c50400f40080c81c080e45158003c40071020070f80328200035141c0d40007940400c450070844002081c3d91113002155036440344442c44010001c058001480c0070704008000c204956241d40c408465600c980c180b80784194064540144100d0100b002c1855450306a00444e0016101d904884424242004ca40031841d210007a00c40490400185e489420343c00d4002c003544010407120031464498552085a140b102800001d010001c800c0043d414064912040399a547d51107804203442d1010700440300d401d5880c04004948a0041240040c41e240c08800490b014a000b940554200300290030200c03995003001c13084030304040c0c4502c0a248107503824005d070748109078103603004582c0c1d8845a61340e03150031001022000c07510380034001c1084049030216031840c18075407a0801051640324082250b002d00303c070b8000140d05c0385c0c0020351102c020345107500c42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 937221609 1250 937220359 937220411
    0x903020c0a050d080f0904020c06070c061d06130302010e1e0d140301060507050106050411070b07080606072003030a180e070e090a060801020c0c01020c06210702030c01 74
    0x2a40d42152902d06204403600404002400d9903c107101c2e0741103611107140549000100130700010306200003980c0442c034110003500c00d000031030b4542c031004040c81003602418200720940c5200b05101c0c00303140700310795a40000401a0044140d05d02d0f100c801c01d8801e40040344104100800c84c4c6600306a45c80c1d0401d00e51300618039110034414040100c03505802038000d1003518001d0f200d154116860960141d40660242000312840c0d5600d0760b010a10795150b00c602d040c2400300405954031003145d8a03107a0340101340070f8880011301c2104c200300040340d80c031501201ca0044c3d01012143c00142810403807074504600b00c4096a040c003000c0b448103000b5901414103988242c011002101581c0d840c2c40360000750205541020006494200300b15032407c04e40045500007880d02c0001904959509150342280c00041110400b134020007810425580d0400c040201320302c0c100c070071a16011400f8101d5020b010750116011f503000407800051040c5000f407099030101b4280c0070081c0300780c604c4466004610418a0a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 937222859 1250 937221609 937221619
    0x81e010f05030f1c181505090f0904050601090b040e06010b0726040b0a0507050106030606090b12060a0b0319030302040303030f05100905060f18010e06150426010903020c 75
    0x400042ca450009078000709105401038148000c607604030490702c04aa00c40700892001217040005502880140e54080541065940d541c5035000c40013002490180422007502c680e04020501020540c0442c01c01d0440340c400c10b001410800e09408240a4800e41203894040c0c02000000603c040641c0d00800c3e00300c1c450030740c00350b01900d18040d1808062055039400d1014005200600c02071000b44020004000e8070b003442c1d414481d040c0c0d00c00c1d096611a0700308070b80083c0c40d0b0b5003c0040c86114052a00040022110380741c44001305202107642d108010f000541c01c1d5100c4001040949091180761b61140310f00c15942121a0341782006006584544012000280340800002503002c00781300e118045e03003071403074003165081c54880c51b01c001d01805070400e030f4415071891700e80901c1e6842a25038001d0424007419001e156141c0030080a03405401441c484c0908002440c2042a9403201c048030b040e0380510084c0e4100388100103220008100d200010a40c640c41d240b00c440070f040d00010250311040d004c0758 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 937224109 1250 937222859 937222873
    0xe0a140c040512061b030c0708030a0902210a1b050901091b3002160c0302030d020604020a09050c1b150705130b090607020d0b0f0f06090601081e010f0503 68
    0x4049a070781c04c402c883c00e00860411864542144145800139500301d01090541428101661a0369000354402c1c1c41001d18070b991242c0c000d04504103e141284401c0740c2c105100040c11a500d031a944610324182c00400551300301c4425080210b41c0d902600c050040940340650380c0d0f8584002c00001c04207115500124000030b041680a81c0c81081d00700034483e901140044d40c3d14a40300c1e500300580868000040740d540a00490025200c4940c411146500030314013400d5052850041c14205031f005d10001085401c03810411002d600c900d0748810403169144000540c3e079454410a100d180140030503901034202200941d00c221b4000160002501c00804415005807600e4006076075511411441601c01070600320200081003146000c0c1002c240e0180007a80740c1500d590000b14403075180703501120101000c03000c0c030000c0313100c2d01c2c0101e60000c001a04600c03a42421800511751403401000d6504011002c00044d040315440c1b211030070040c03a810011f901701d58542003490444042c41c0a87c6009214046e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 937225359 1250 937224109 937224139
    0x303050a09020f0103022115090a38040507051c0b100e120a0302031902010e2e0938060405060d0503190915090e0a140c0405 55
    0x48152842982d008203c2085142020b00640194010760510000f0500300f148112401c80f80e180c03541e00c01d06512030203802c01403074030003080300400015092202c044d03c0d010780c8154107142c25088d4803c5901c0f000041c00c00518103001040d041042c01c000c0ca40041c109814040d982c0d4000300600148a1041d44001d00862031440010485a0034112150b1007038281450340c1c07100340203442011b5000300280981c2d440c510500039031403410515074021001170703000181c00e51642600d40001e0701e062400d8802480340001112002d81d507107244003504186492000078845603070b01d03042204400140002c0c400d21000b40c1d641403590300050103400460000811902d52410030b0100711a401d609410301204520545401043c400141001040c0640054003082800301040040002d80080c100d1401604040759008100800b0300001d03500800314071759442604d0002d203400074418001d454103400c41d81307400c0c0e4270710705903034050301d0400c0300800c1d19520a4140b0010a40440040c0140c0307800b5602618115682 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 937226609 1250 937225359 937225361
    0x1e050f012a020706081b120603060907080309101b20061c0b1512060109050f011d060906070501050105180108030414030c120a0308062704061d0a0303050a 68
    0x3031400000580200c070013804a18042c08400350410352a0050004503c410201d041841c1d004400c0800d4403a12101002501d240403c0495440081c0502401400f440c0c10981c1e07a883c0500c0408a1090140054505295202c0d040b003031300c2c00c90400070045104506040c1194400d080190403000d1280c401e60041443c24007030100c41c07004040d461600404040d1070b00090091521070150b9520a00c40d14120050b440003401609903520080311602c5107003001c0002500c910708036407015001d0101400b41d034106d6a04480b52000b81030f41140355491400c4144009a502c1c0b04410175103a000d00c021501c44140101540000d040e1a425070b140c00c9c551904000070080c4407030074400c80c1c5456004000c207104260703201c0801c420b00000a800c07240d080c030304080051115089041e02e00c00c0c0394442038450083c07550050030f480d0030041c1a101085401000c00d2046000c0c0c40032118010350001250101c2c04100c0301c0d9001c0040400c0c000c18105811044035503094640804510a40002c0d08101c0450b81600d25 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 937227859 1250 937226609 937226681
    0x3040203010e1c050d020702060a09080118080304120e0306190e0a020d1704090221070314070e01020309090a05090723010f050d0e010e011a0d1e050f01 67
    0x51900c080c4511a41800211000c5d0711000e03030116080d03028003200b40140c550130301402c03203500c3c55200c6109160805650b17078210341c111820104035607590152400480d507901c0440c3d4219410a0702c50402401016055a41c030000780c451540611402c0108460184c1e110030014800302024020700080c84c0019050359181403d11010354400411403007800010941842d19203110544a2868200b540d201c5081080381c000961403d200d00700115842c03440404a1034142e071100a038141002050902607005028030401801c01090010030b02d401500d5a0080003642c04c907800007058008180351081800b409400107403083e446520403108040b411a1300c060b1102c800d803004451481c134a4503d4001100c0286042814000b0301104004c25041602c250013003155046000002003084070807442d01a013196048900f810765034040750450440d03a40c2e40d4003140c1203e03801c58161107040100c0320502c0401007403c40003c041384280c2501a40484040d000b041940e00c064a00b070380007400a881c0c04d112040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 937229109 1250 937227859 937227883
    0xd0f0b0a0b120712051504060c081e0a050702120d021207090303120b122b0504140d06151e12030f08150a030b0a061208030f0601051e03040203010e 65
    0x603038011311090500d40c403240c3c8454020000c80e50250642e84100089800540b403e0b81c2d103949443e14540a950494811600309141404014004418001d00000c1700c6020708000e0380d03d40c841e401300342194801c01c80b00c0c0d00603040000269a503110700d08440029400b4000030b0070300480107000a01c8081c09230f04203000b1250151074a521a00000d201d41c0020050711034000d030720a070001e40329410160b0800080c14000100d07017580421110b10542e0500b840c8020703600170100301c01004107100c00c10254041d00c4141c00c00f610f503441d084615143c1310020b00980030100328480b01d2200c0000700d01158401c10403000c01c3c0003100380780298480301010b0b4000e0b00c1c110b010f8041113090300340d104858444c00441c0e5001034168021a0204480c00001e4100030440e0f00680f121444d010502c05482858840c20740144110003512414859683d80c0100d030b03001c010b04072100580d9141c00101103901610890750304461090041920300300c10780a10314250000d40b8181d000303620b0b0134021000301c1c40c00244084441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 937230215 1106 937229109 937229113
    0x91203050a050a05130620120f0702010903200f120406260420030709051914060d0309180b0102160608010605090d0f0b0a0b12 56
    0xb0340c0240156081c0c6141105200c100d0109141980d402903016002241007600181c0c0300003c111188040da0007404005200c0e04041d1103030070418480c1741c0241000c03000342c8400e0000c034200c41d000d42005000c01c7c009005e00300340316070700411042017410500c200c540710103007103490b10304000c0c01d145280400c0c1c02c0402c05004e1644c002850264072a9031513244024201d440d200044510400340001d4143c400f2040740a011041e480322140380d0360009000c0300c3c4070300c1c3d070f9003038140c01058201c0f48070200c0100702895240313030386641c01844507010400c906101541c48000400030201e848110072020b003d126240051401807040c41c4441c600758000001405602200001e81001c8004d0261030b43d540302c6150511132950401c40b580e0558240707150040d00c070340c030b903c0102d18034a07509032002e400d821806034154100110001018801c692150060003420a107400b4091081000138a25400b5 = true := by decide +kernel

theorem cover : BRFrame.Cov 937050359 937230215 := by
  have h0 := BRFrame.cov_init 937050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 937050359 ≤ n) (h2 : n < 937230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
