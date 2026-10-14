-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1694
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:15:15.641553+00:00
-- url     : https://prove2.me/submissions/79abd378-3c98-4055-98a7-f119c8e4658f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 304496402 ≤ n < 304676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 304497652 1250 304496402 304496407
    0x608071202100503130206040b0309061014060a0210020c0102070c060503010501020706030b1c03020f0c040b06030105010f0212040305010c140703090302121e010b03120f040b1e0c06040201020601050105 89
    0x350b100c01808440800181c58002c4d500d5642440e40b0b2100034100c0f02c005d420601c00140016541c40003005180a51100c20544003076449503504d910400c4c105000303200101e16050700d40c41c020320b040e90081c40851010700640c0c04000340d040002d4202e8001054001d4281d40000b80c81c41001099110364025207240d0038094155410040000e590f12040d000340740c01d040d507844d500c044554560307111036598420740d81411f0390440c05140003500c440b40e03a4006c509038400e801141e5034500c0c0c40c2c040c0040c1c07004003070300082c2940e01c1c103001103d6106490240d0000e500401000481e821440c40013400514080c00002c01e40d00850440240302045184418401c81c405000c03c2001a901481c1042283d8044a558120800c02050f143c10701030030b80024030720241d10140c0600d109206412054506100b00c0c00d554111408505e61192807040c400c4101d40c100d01040144550740841e802b43c0041c2d03505603600c645415040c64042c18582c0b1a003503800f03d6601c29000c02003150307810442e45015000c00c1c0b07440c90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 304498902 1250 304497652 304497689
    0x20102190506060114160302100b0f060702092e030318061b0204020f0417070b0903100c0c0b0f1b042106090b041214030606040306050601020f0303070201060807 71
    0x103444042c040c144604100390888003e40408004068a80241140e00868102d059603d0302a59403012100c0120340340c0d050015051a6190983c0e2404501501810a900e4007a56901b045250580240345905640444090104010406c819507065a41802146050905505026100c0500c0d06280d00705000000c0c414018070764400384101614080501d0300304047e01520000d0064040c8031458003581c030020600043c5c01000003440340c203030a405802e640286440c1d8010401e144511800704c0d8250b440106144d07540d07591503000038144941850511403101c2140e541c03012000f400d1340c1112000c180c600034401c84680c800d95500e50b0100311901d56290519110250a10000100004094038102a80c40b020300426812040c07405074030016250181c41c0030301d0078003100e81441c140140064400d10300c410b203103002e0404603401400001c099504007807862741d0b608050440100303c68114003900111a13100e61040005d0350160480d80c00106a042c2000307883d6140c40c9e00344c0c4c042c038481441201d050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 304500152 1250 304498902 304498913
    0x60c0507061512020d0203070b0d24080c01180f06210519020a020c031608061303080103060b010201020d110301150203030c180d0c03030c201807210902010219 70
    0x407401c165055901100101700c1d4000a41403082941c00b00c1240c4000094031030103200e442d0f00a448452816405420305410305440c0702414200d8001c1c803400394007540008155600802107403010b2480c03603102c0e0720702e40d4a800080074010407035031104000c140d03041e11611308185d00503400c82e0010362002042003503140103000c00c0c0300b00d80350150032a0780c298001703a0359004610a000080f4500b00c0a007c4803c1d1911035105510a02100c5c402c250045c0242c00200b45a2980f8100c0b01c1c01041d05550f42c82e5169083d0380b200002404129034060566608110030400072540707018552440001e580941c0e01da626107200320004280c49040c40c1c003150010001c00200321210001ea9240e0720081003003042910b290004104800003040019084441000340001090790101404101d58441d10300300720303110b01c520300400102d998040d049a1104103218580d01108c160412035a104601e403818480382c800303074402240c1010a84210705681921802c5d03007010740d40c04005680100c15000311540b04010540c881 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 304501402 1250 304500152 304500179
    0x2040f0c0f0f05090a080a0506010b0a0903060f020c010f0f111c0b0a08030c01020c1504021c15020d090203150c0313170a050a02070b041503110403060c05070615 71
    0x18142800300e0b01884014a520030360580780e4011001e010f083c5803940b5410495030790b600c1c1d990100c07028450400007151181e600800e940c0130b20095201c0d02c031010700b544d0b2110094144011020052a4240b10003d52103000b4001c5072481004000c0009410241841d00825101c848043c4481e55400300000720018000140441a040710528000755a07049403002907038000150303002ea125444040360b9615440c1c07042d4001c011650070070381118101000c400307100c000070404941c080c2d88945503a42c03445059009041d0080741a210305101e0b041d8043e40d01d82d410803604200c0070481d01e2130351000410700314241003084c075a035007d1a01c201c41440c640b0050f9844507100062100c490400458650400c00c01d1040d1030604c051803c91105031540c0c80d030b64006006401880c4220010720507201d000562124038400c44041c0d072021801203403400d00d000426406010800c4030201401800c000c00404582d0340c0c813404c45020b50b642e031203d6032403459040c00016176290028080107010020341c20007010f11116034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 304502652 1250 304501402 304501427
    0xc0a090e060a0506130306060e07110115061206080304060507031409060910030f020f030a0506010c080a270e1b0906030a0f0f0e070f090504050c12100905030702040f0c 74
    0x2060360f600c03040210b03461000b0920350300050a088c101100880c01daa44501214032842c0c0980ea070825035400280316900340e13490300071116088600e0400c1403001c10b200e8000414406a20603001c078055a032030b200c45103103601691040e000250081030031010158401ba2032140074200d038403441e0500302d407000010780d988100c001880c80f0b4040344140d8241d07a03009802c400c042c0d6811910844d15a0f000c0582d040c0c031a030003103903007104152809000130324540c092030304400e00c0742c0c01401080c18401074502c1912503491000340620700741134036040383c4445504d051603075002d8506007007040c0407401c04051440381001400030004160005100324070854031518141d070750060f550440850001500034101009002c060340801039142072942080d00040d0006000048458000c40b80425035036403441d50080b0349007600c0007050340d0003080019a2914100102d0403140c90b081054501c0c41c2c0d040090b00d03089604c000c80c12220b54201051220a619040c4111102c0c081e92520502441491400080c0308204402 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 304503902 1250 304502652 304502659
    0x1706060402070219121a040f031d130e07050a03030507020634051009020102060103020d1a070314070c031e1b05031b010c08010605030402010201140c0a090e060a05 72
    0x103502c034295a20b1003600b800c5040750703043c0503510544400d5500e8907003051400581d1014425003291241940e0724107010310417900600300c0c4002d12216503048818550b0103e10005035040c0307040c5490340d681d81c2403180f03490034440d000004400b80322140c40350420200c5d901083c401c0b00e994400b040800c0e0010b048500b45503040f41c00903510f0001d40c10500f09000340c100040090601100b040c05540100d0721020700c1e075030181d0101c5d00b01c295a0500407003580d04c00b450090040c2c1004004100608007440d0100c40c80e0720810b01d208820403103080500036190f0449001c00001d072aa00c6036084202c001a0701c50b000b8000d03241544620000f900e010300322801103001040c0c81032031200400c003414424041c01054518840d28502c058901d803c0c803070355a17000211040100041c3d14a0028030385414401ca0508a00d030303071a529001e071310f080070944482d00000e005034155529448052840070400401611440302140ca0a1f154000746c40010110314590300902114956003040c001c0a03954860100304898046 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 304505152 1250 304503902 304503907
    0x506090c0f0307090f03060f0f200c030403050f1c1e05160203030a0507050c040b1804051212090613030210020901030e0304060503010e2805090109050d11071706060402 74
    0x400c0807102e03130849621100d074003500d2180c00710070070070240c1000c0c800d10550f0380c00703010b0b8584029140c030803100404068004101580c60601009504a014100c601c1d1520144c3e814a030756a1162410000b008a510100d50041c08180509201c07030003184510002510b460702e0410101200640710790340e542c40840901002245d00d80c1510100726003420b03c0355010b020b41c1d44400c200403014000c1d4005000c219a030f401040811303840d5007407611810220301c6009200150030f0b200c00844415900018005403954000c80151031102a40307c4000c1c04c0300341d803200c10b03103985190043c6194140301001c1c02090311070840e4480700c400f10743e0000c1c01c2042410001001a07550110342c005030300030200c0b018401c8043c000481c0002d101c5402102840c103c0f40c0c0c3e5584081580d0f01d00302408002c00c00d0300408040c1e244156a404a00c020300d0340201e5104050600000740d401d0075407650362078a4046054500091103c40400364a000c043c080f0500404604400c191800c03031030003060703495500c0100a18080c81d0f02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 304506402 1250 304505152 304505161
    0xb0306060d0b130c030b040b061e07061e0f022a0708060405070501030606021207030503040f051009060c0c050613032105070f05041d15040e0a060506090c0f03 70
    0x15544911400c10005001031a040451000c06020304810011300300440d03e0407521001c103003010f010700300c580c1100400040c0360135044075445145030411030f19005e8a400c1404802c00041d514400c640c42107000748448601d04070803d400c00143c8540c08201da06080c014050444c914074540c81034001e1404c981c214129a030360500201d07281030030780e51020343e00c3c0c41350303400380400c1c410017082041c156002a40c051010700d40b00c41090381d07614541404c0c00808042000460082841100903603082813041c51075004200e015110146040640280950159502e800c60340070003003144126a10f04045040950710040b0710b496082e101c1314024151800b18500c1b0303882000305881151101d0002a0080070b05c140350744079216050080c0001c03201e910224404005280d512401401502c084a05071508500401458200000c2c0e0b07078000780580c030465507803513041d10282e5190300690320340c421114014a002c4030203040a400341c410152406006004910a11050310520011904584050114613981c4c0d1203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 304507652 1250 304506402 304506427
    0x3150b0120240103020a050a12060b011e030c030b091b0306040213060f090f1404020c210a0e04061d040f0f030c02032103060d020307050406030605060306010608010b030606 76
    0x4503404100e905242c915140800940080c2100341a01e00039200d40c0c080c0c588560030300810046502400301c0860304142032200043d6150800901c2890616200401d40002d0100c0820f4840b02c04446002c00d4503441141501b940c18820f0a031380442c2212407800606004110184000011908810b00c200000004a40f912140c0403036001e8102402c000e10001c0d6100e400400071480c03a000980081e40d014400103091000302c24110960f210000d1a110348101d000801001b540108070b003e80314003a0301c1c0c51140c46035000d441c008210000703211166550b8040600101405280d0807040d202c0c62a215080c05110322010810002e040380c40341c0400c068881e801e016801c00b10750ba0004161400a003080400c1543c0042140f140a1095084440009440700743c103400c080c4055078400c2c0c0c00300900000303026162411101c00301a0002d800d03503c805480e000130606a60080d00309484443e2aa81400300a080811030940103000c5803420501302d5040c0aa01c00944c40041c0070700e8400c02000c0340310000b501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 304508902 1250 304507652 304507663
    0x13020f03040b0702060906150f010c1401021903180308061206070e010e011b020f04230402030f030a02071215020c0c0a080c0919020f1303150b0120 65
    0x91520888544034505440c00840c08070341121540d0040c00780d800460b1502c1e0700043c1d120301a4505c0300d110403c3da03205100788801c880542e11898108008001d0ba2000b18000d500c280140c48600000981c0c3d5030410b600491403000d10b02c00d010200340c40c2040d90708202e014091196441981858900442d4a4060005526a4282d004113007a40901d1041c07259207508441248681c810a0f00c8841140480c140151460000110711040f4081c0d181401b00062501c000460301c8688010000544603484141441440440342e540c03880c0440c8610510080d440c08020b00201400e003a4021864031031031140c001d445400c540300d000306602c21074400104100c08012407240c4140780741d50441d00c03411041e401c6640c40001910260180503440c401107800f00c000b2482486448004d48600140d031100d007000240d9406c1300e00c0c0c1c00c81c015070034000418480204c0c0024141c4007c20943c508803d4114140003400396801c80c0c08190007403034200e2800103660040480080d040440083c0402a41071410340d40c2480e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 304510152 1250 304508902 304508917
    0x1012050a09081c0c051809091e15060a08030f0307090b0f030711010608031213061803120c0e120109020a0f030b0606181c0516060f020d05091302 64
    0x24001050741c48425203c0301d0fa03200c9803128040d080c400c03508402d400b5940d40c86181c0c3c07501030818031140c01402d1802c2c985881500820501c040720390700030350300c0e402001400c8569040f8009411480034540451480414150403900803500e900c14035141150a07552442020840042c09c2c001000180c00340780075440b21802044844d403d0395403801c00d4014000160b100312085804074060311112891800144202c20039035424000a520b003040908951928a100a0880f0740c0a050068454001002d034010488004960503240503070007414900541980307655041d40d0149450800582c459035801000c000f85020282e40c0600340040848809001d4941c03030401a4003c020340700700040044202d02140c00702e0340560340007106c40c1c80d460304104040c440d01080d04464104162107000f14508040d80d240c072880e00c01246004041942d465604083c0b1040c1d062243c86400307078040048541101544004113401e2000d000c90b80c142c150017400d1800b03000a1140241281189603500f00195030403034030712 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 304511402 1250 304510152 304510163
    0x3100621050a0b031009020f0d060b0a060c0203100e1c050720010e030102040308120c0d0507020102070605060d0b0c0a031e0603020a060804030503060f0a09050a0b040b1012050a09 79
    0x62919900c1074020741050f20620b4083c2c4105a40310907400036903ca404c042c3d5a00034000a07009281070300304500c64a800038150b40c0e0710303a03e5030516410394031017050f407000384480c0d20b4440c23007019640101070928020001d0301d60030505040ea00da02c180008a070b260442c4228008100c42618480710031a00790040003c010007aa0340f008410000c3c170618408103050000990794224040c05a9062500340c0c003540c071009009005c01d000140c4403000c90703003086a202016002c0b041c144003100070000c05603003043d00c0050150f540040e0f0041031000c58066190b1183c01580e10850307620b40c070741e2000166000208226510310380810a400308501c21380080900c008244041040036500d0ba507103500821191000305c1c071810f80a200002d2250240360418800d80c2c00d40c40b0a81159540c0c000d002d12001c425031041da200c5c40d03000012426102503c40d16002d054402d6001500162003014030046804206003d88109040079004c00c006900071000b09185403498000b0940f9150315041c40054804003800500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 304512652 1250 304511402 304511411
    0x516080313152a021f051b04120f0602040f030302031309060e150303040f0e090705010e1003150302060301060c0302060105060f04121a0c0c010b0603100621 69
    0x72150341903001d2445002e0120300d141215404140b008036504003410030041d1050a80040f41c00142e07510841c061520350054400440c0c0503078003080384001c081000041d4a40d00c2c000e10003100e04002552003406c003d030040500d402d050400c000401804083d00a007140010008082040701c1c07601514020086060048a40d0b5220b01d0041d4580e00051181c085101c403038540000c0c080704038055030007210364850301a61541c944103040083d04500400194051104110000d01c0100940c43c0500404641c1c3c51845036040521392681404010362005041110310b0201035100e80d202d080c5a20b010016007000507040071010000d80380151036510283d408000030000113201c6400c480030a010342d10aa0940b0501d03030321602080718901484100414040f800d1000340821583c000da0840c01c3e50148101030b10f0400b4402c84056103c40c11100b00c500840c3c04264440c0c244424007851034900d00481d5290700b10301d0480d0803035505901e184036000c1081808807185100c007840080f044445d203c510403e01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 304513902 1250 304512652 304512661
    0x170106050711040b090c0c03042714010302030303070e04060906080f07150203040b1b0601170f030301180c0516050c181902090102010b0301060e010303090605070507030305160803 79
    0x901a81009105880203031180c040c68046181c10301c10000c0181d1300411101454503102441009a00403410201061204010109801c11140cac2006040c240c51204c089594406040840c25644442c10a0158070902d07801440169000b10a0320f81c001c24618101d0b40f40800000081c0260002d940500c881c0f51602c4800714044e0404100307213100711462000c8035482581d58170740da400780e09000f5a000c0160030178803083c8074040b20000204642e05918480491900349407581504000083e882502c281d0051841d00305405028401b011030303002d12201960031503140200e246080119030f0300b143c0e20340703a5402040000b01d0141042d10707140708001201c0c0c60003611501d0031550742d00114510b60300c286a07581c9003100c01d80640711b015204038507400c0c000d07070741421000c03c11002e5080410701d039066540f61041030610361001d02c20b54004201d2030305035581070b514504003c1c00640340d5401c17103800c20404019901c0800c2c0b000500104403036044c5442545c4070203c01020194940d0910010402e00c030000910 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 304515152 1250 304513902 304513907
    0x18060408010527060402040f3308070506180307030c090203090606040227030c0d2306010605070b041109130c060f021e250f08010c1707170106 63
    0x1103108441d103404140080b958010f100c41115003811442103150320803c009001400c05820018546d10110004174540c0c15039a560034038100140d800b1041c61081e03002a8510500c0700c88114014414600a0030050f1b080c180410f11510410703021040d039000c01e9030743c210180c0b8100801d10045402018075008251607528490196100307880c044003600c070340000b10301c1502d407501c200e942d40c515031049052194040c01460341720142d603007241d95040c012403000f00307029100d074040c02c28920b1090701e00040380418a80c54000f46100c0745158021648503000502c510394001044590071070700100c400c0e2069480d450260b4681c01c03603110290b0410031070750511580105050064a09034032401d0020012a1a80e000312038110030340100f00c00507032110034564001c0310a0240d101052000200340e03103040d50f00040800001342d04080c80225005044001c010701c1e22415003840182146070020b02080303c424100800700340d01074216003640391f42840403486060107511300c2d14503140100d034003003015070351800302 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 304516402 1250 304515152 304515161
    0x1d0118170318060310120213020c1f050c04121103030f040602010b030105190c030209030d0e0102061503102c0d0207050d050706110f01050f041110141806040801 71
    0x24a0b4510952001051149028402d4a01c50400c0316840c42015241000d00c8400c41241102680c0181c440c0001e80c402c88541c3c001001600029002014040055442c95604130b070000e0308200c2041c40e0500b405400100c1c1412542180d142d804541001402400c050100188440d07802da418800007e152400081c140003410840381d194008024442d058000c1c50b0a0395000c4918015920b02803540014419099018134042c2c0d04030301d030060600502c2000b00f441c0508010400c1c000c0b540603206000b5a45e4100411a03104181807c0e00b8600c110a0f80842d940348901e40c102a0f0b101d40b40c01085402c844560703018101551440380c040c0507100100309403901c6d0303000c80745008014003507104080f402d8100310102c100b506601c42c0c0103008031480d008080340e03008a41740710409070b8003880c200e8a040f05424010f01d0b01500110070460b80074140341c94140315106210940e14020310480503c92222a0441248040310f07242c4100c4035038490050b03544a92700d401c0c40064a80c001000b04000c075005105510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 304517652 1250 304516402 304516417
    0x4050402033c0f07020c12031c050114011409061b030d06080f010c051801170108010c1209020f0405060a080706021e1f0f020d0e0f010b011d01181703 66
    0x4005200d41c40d405456843c06204071400300240c0d0041610601c24200041c0c3c0e03141065218050b241050304100001c81c501c02100c801d41400c9448000500440341c016000c82e603031740c00909285801103c0d8420280150050743c130390a00c1a80041152200000354041c3e2250056101c03040d66602c2c44224062802098035002d040b460780b181045d5501c0042051044032181c4959840e513500b03255070710400d42d8000120312350403410404810708908400c0004003006001c3e08250f40085020014a580101f0110703004880100c668203044024000da2103210449007a09826a4085115540c1c6004600c030001e00b0761008685104802000400580c0440d4109004200c1c1d0469842c00c1e60f0040d41c207071380d44800b0440d000040c040000300030b4820400c1d8024906240c0d10030000d41041030b0854a03800315912a207c00c100c0350050328607503103c90000c3c4268100c1c050242000340341c3c0091810010b050541c0040c03c1c3e4180180400304184045000342c00c10004c1242e02c0d0141907510902040e1503c0b0b4010303c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 304518902 1250 304517652 304517761
    0x20412051608070b030406200705010c0801030f0212010e1204081c0503010b03090109050703030509091f140f03060a1b05030c0d0504240b0a08070503030405040203 72
    0x10003010714000c0300c404180864058070010440d481c105070150745281d0000e40210354503a9250503698213240140303805204c0100750201c558851400341000b9080d82c11b4880c0314010420340100501c001050200303180c030066015144000d003201c21a00c2240108440c080c94082e5101d1000002001845100100143c62140007607940441c3d00d103c00d80c05044a070703d00c0c4404140c00380018071045202e4405075601905020001c039074010761344c4071a03003400c01320382040e400a00d0008066a150800c0d01610382c2001d1003452000b00400164501c0c40d070055903000700ca038042d80010010f0911780d1000c417107006268005080c1c0f025400c25600c0a0001d28502006004840038a21084492406401070300e02ca4802d280740149040c12107000c801c0244001001101c218040c1da6408030000f444a01483d01c907403220345c0008070b001502041098410311a0b100c11065400040c0134045920044260b82c100c50703061710056241e4403190022250690240b031f840d030b211000c0d0240742c801610520200d0070f050f000032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 304520152 1250 304518902 304518913
    0x3010b030102030402060706021e040b0d050906070906050d02041a031b0f030a090c150305010e10030c090b0a050619080a020a0219081c0b030106080606090109020c030d02041205 78
    0x29003414241c0c0421078000c1d510030b005004000100f0517640092000300c101e14002000c68403015030500e255003150704045601080811001e01e0684030303110341c44d00a10303284010b280c20300c1d12003001008400c180c02100208440400e000d400000903806503009410142166200210340142100d00d0350030807103400001020b00b405240c12040f420382110300e01d042d85140a4a1661800c041101414410f5400c9501d03040f4464001035038025040e82481054003558003040a5150018180902e000589039540040e0070035400c100140740b665041c412100c4641001c10a10070200c0094403100865100d150061000251a0003460503081c4801030001d0365102c003201500c80540b0002280034403101c90015a00406070b110035001645030384a900c5101d1000c16107071401c0d0030024a50303203e641d9240d0200c10b0321070313240c10921b02d028041e110160001030018559443c024001549011040c0300e900303405a40000c40200c01a0103108407128041d070790350255526a56403070124800b59900f1800d07159801113 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 304521402 1250 304520152 304520171
    0xc0c11060406140f04030609050a0c06111b030c03010c02210315040f0b03010e010c0801120c0e09010906020307050a0e15030105100917070305070f06050a03110c0115050301 76
    0x20300603141950080d65a0015002c1410b12010341c070ba00841c0c50100342c03003040c440040080c0c043e0069500c5a4442c60103842c0f000301078030b070000d004116a00700c0c1d0240f03d402c4903140380124001484176146001138001d00e08000304000440e04003991385240d01c1d059400c010340c90610a4000903203201d0f00341d44400c20510182402100351a0303000a4509000884003508000c0c018640782c1c01082140381044000106201540b002a00316501e0920b010303216511581d121500c50703040213030940180000c13030010400e01d4071540c034004440404d001f50404004c411020443e0f031042544010710341903021804669a082064002c1d03d5500031180740c02c00100401c40410143c07c20088041306071030200d403014156402d140400140e0021002c5034002c0220101000403d1440551960030724507200020305503190543c01c066050801c5a000400200b82c2254100915540304044514030b850750b02e0001070303403650000780d0a4030344103060000140e50308202001084100040e401e1007151001c50081041806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 304522652 1250 304521402 304521409
    0x3031e020a0509011d0d061d061501030e070f0308090405060d050714060c010212010e0c040e040b1b12060109271107020901090e0105130f03030e010f0c0c11 69
    0x48426030000154288904041c550080a410800301586900d0301101c03206178020450b4800103e0b000c0d141552500f001c84652040382c0e2600d0b510b05590801750140e86089071003104954404106903040541e02c1c8000c4200c47c406011400203028640c43e0600c081d503680c100000550480071555100e00e16107008a0218500096009220b0398071101070100c0b02d250800f005080b0407210f00c4a0f812000412208800240a10040040c88001034443c0070300e505001c403826130010000d00e00001640104401d0058000010702d541c0c0c041e90041311202c46940c0d82201140556040030100c0c80c411012070855a0b0308004042d0314824203007030381c9544800c1d0751001107007402000d038040c03500703240035011004041520941081c0500004664101d207802c46690204000100c00d9200f2007803130343c1d1100300009210080c0121900124206141901c0e14620740b1b40d402a80001a0000d040c955290100d0305028001e4005c0d810b5041c40c0d0b00e081040810691019008254010040301c1e50204c40958405a01c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 304523902 1250 304522652 304522657
    0x13f021e0715110f071a0703111b031c0b13060b04180b090c130e0c0909070e030610030b090708072304290312030c070c1203031e02 58
    0x30b0b042440c1e180c000525401e603a0041c0b01005003119264010402a01e816070490028042588204010b51041a0001c10100103c0f8041e08040c205410f000c00720016000703140a64840c2d100419030240d481800744486403a504c2203400c8103680b1b803480b00e0305903900c460ba507001c1d100b0a40e05550764102c159a000ca0401115101e00410010440c148010f11403031505201840c40c1d030360000030000d5125010400142c000c2c0c3c085030301e42e01d0908c00117018400f080c0c85859000c0241507100c0d4031041400c108103c1ea0300ba0103240e5849015180d00000505068462040701e1403030380000e03007902c80f0742c14146404601d05c403031404217036451005080401c450b0031000801004981040c0c0c0940300030381c103150791610140216851014803400d188218041507a4900c6403402401d0a08008026071407036468600b80e07000c841072240e219401100d02a500d1a080004403035000c10401c00c01d558400091074405208145034001100c1d00c088030900e14109509a400110b003e031048074068010b0b82c40e84252000e13803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 304525152 1250 304523902 304523917
    0x60b0f01140a1407060603121202120105061c05181e0601031e060f02190314071b05010905012406050403020603070306150c020406080c013f021e 64
    0x61010055011442c0c80f4021004440b0a101501e5150403695180c0905a80785078009440036a080802c0d1540c0640102100010340d0310003c0a40c10082c6645542d0000001441058000d480028411000441ca0344091a0b0781c4401c400c00c000501342060901c0c411003c40c2016106071040d0810582542d404c0f8a10550b42c2041c0300003051180e00307555072824001008a408001c9003846a004400200d05019060a4640b00e080058072641f5810400e42141c007030a00308414140f1f0050ba400c1200c1c8104900c0da440b048504200b00903100b031202c0388458030380c48200034009500e080c5a2a041103019000781403061003483c142c1070307600d040c1c1d040041002c5452103900c0114204000410060410401442d840385081c2000510305556410a00c0000c3c0d4801c00000020b8030b04078007504510f041e210b0b000281003070400400001e0b8184001800740d00c821008450743e0301180d4403142452032002000300a00303079140e0034500c3c0c6010040318035000e500600001803800c414042024106100c010960701d40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 304526402 1250 304525152 304525187
    0x103060b0f070501090c061106010e0c0909042a05090c09030d080405010b0a0b0304060c08060d020402090d12260c0307050a0311040602030d0509030a09051507020904060b0f01 77
    0x1401449905071449501c0798004540d55500c4440140204460303508000c0101055103601c405500708561140c10801c05802c11041941400180306c20804d841c001e0b6003070b54400703803460341b03640e04d4900700702c0d4002030081e4141035035a4002e0443c40c41500070303050f200d04648081d01e008000d6140c00c0022880303405200f103003580560162210420719407043d460341c1d4106009000020340c0c0e00070074000c280c0005030b41d0014107240000005010400c00d00b480ba543c00114a4a0700380c1ca02d091010020707425000c1150041d05c129004107a140b0240d4403441c1d0340c404290b10001c0000b20407040e003005003002d10040311156052815103036043e800716116094a108054031403680d4516a100c03a401e48007070700882400410155544405855001090000c1001d03148a400554981803005c100700240c60001305401c24070f4105021216490307410120340000e443e01190198032400c0c0070f00000380c0d1401a4003010f548092603500344404e110384c80d44003020031036080e2a41e0410940c600c00641e00680c003c07841550 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 304527652 1250 304526402 304526407
    0x30206030f1008060103060914010b0913080c0f0c01021b010c0b1503070e0604060906180c112b02010b090105040e0705032505010206040b04080a0912030c0b060103060b 74
    0x403a580c00321080d42c005070075109001c1041d215084070385880800d03001121140e0342d0362800000e000d8a070007011400030003003000b030202a0503200494004100940a07101101c800603804c0704211629090750300300c15a40c4112503040c942c1002465881d040c0e42c02d07040c00b41c00b5400c550146818150083da4011106842c0c50b04149450781c1c0317010405400900120b291402c1c4400f01a5598040c03190000a2207855010112420203070b041004641e40c3d0780c4a40061444c05008024648500c200103401280800c0000b071147c2c1500801d9480b0100a4111207060190250000c03843d4413201481142e00180054545034400c2c20390180e080b501c0301d400142e0300c850100010050b070b140c560808200c83c02100d00382c6400c1c0b07a1b00c0340800e240c000441ea4038030075403003008026408061034100c144000c080920081c421400e25883e903803030000001c2c0c006031543c0710000310391804030f0191401c00000c011100861030442968280204000002703401190300c4240503000c80d08542c4607000f000d06030382411b13080c2131 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 304528902 1250 304527652 304527661
    0x60b27010e040201050c16030314091c05030702190816050108150a0801020a05041e051003090218090303040605010b041406031306060b031b07030c140f100209040e030403020603 78
    0x7001200401c22810848200302d0812041024044003911081a44184410905616004d40011824152480100b000f400240300c5580c494074100c003a06078200e0440749111443c1489070440c07003190350203900b0100322213918040c200440a803004581b401411703120480a504400003454520b8420030f400565800d01003052035030085109480254000c203101d014503642d2a119099800044001010500105040150580405c0200c150b0186429500c0c5600d04202c001000e011011002c0810560b0b2603c6510454a800d0300c180304004540e1000702c01e519108100c20340c3c9a10449086640030304010000805d444024182c50545a4642000d001ba401c0d260a00c490764000801c1071520302000328903d00421468805d00740031704800d00c2280d5480c600f81843c188900d2121401c011a441e00304520b801295001c10118001d80e801440c021a039409200070704e20344451090380e40468090310200090181983d401807041c1701060b64184520b10011004644038029480045d400c08070400c00075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 304530152 1250 304528902 304528919
    0xc03020108070c120c03091401020703080d1103150f040e06070c060f05130506090d050d021810090503010b0916111e010f0506040519020c03090607060b2701 69
    0x41d500825030f260003c20400580c80d04140700c00080000301c0480c040c15a8401851361184807540540404000c16800009001c0000e50303c03c050310015184d400301180d1002130520a03002006294a0400119124100804141103241040000070312842c02a980401142014003070002d8605d1100e000c2c0c214cd84d0b44001c2901c844010f01c0c000c6030741c40da45610124100d5094031030940560000c030003051000320289000b521340b810242103004030780d216002c3c140c040c40e4044101c44094220a40150300d806581d600d811101200200b000d5010341e003225801c90b607036445076400b411243c2c1180244100c0b4469018000003c5041c2e844036800b54002100b06403082c0a800e18581200402e001ca86a0204102c807103d26140302485001d81651a00708102e0310200340c4c0142c0360001000c0314104001e0429884000c42d140202c880c80d52500d4000c0348444082009005807103124a000d4800f50340c0d03681d5890719500034040c002c40c00e40b0482542d40801c2d41030074a40e00c0900027840045104a02c1c1c0d0814200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 304531402 1250 304530152 304530167
    0x1110f060c1b01052a0c031603050c01090b04061a06090607030c080301080a0510020c0d2a0510050903070309120507051f020714061c0209040c0507050c06070c030201 73
    0x31400341803802c00a040d0085003481910301c20945e2039103502510803010303410089070303a8000c02209000b6040c0075440030340801000f124485950426588040f069600e02503680340500a9103664552030b040340d00e0203000c60b40b0031591186100d404200300340c004034000101103d00c09a4400c2c0c0004040c4000b02007400c0007002414085d0007814025903107910b50355440b4071507100b40c028071026001a03891400f00030b0108100ba81540c0c1c40c52065081c44001c1c4102e40d924010b030047c1a04000585204040480300d84c900349a400b060710810768054000740c10140c0e074400c51190346280c00b62415000401c8164040b0982d044180d05545040103246401000b0050b400c50123010350b458000c0800c00039841da6511031031060240066045840600c4000001c0e040501c140d205030484480c000c2c500da680d6a41804460b1013803481e07440c10740009140501c0000030301410342403a4005142042e20b01040f03400201501d0024820740868000b100b45409002250040c090000c1015801080c28001076000380c1c007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 304532652 1250 304531402 304531417
    0x30910060510140d0b0d080712210c110d030204030b150f06070510020a0c0506090a03080c0c01020d0603031823040b040f150519030515060102070305061501110f060c 73
    0x1c000c40c054030203a0000301100360300e20044840303240014084003086410f402c2d0040307003040c50408000c5042080c0c00b0745c0c014ad280c42c00c005034460381c030200e61002c0d5009043d02c94411010804561036808101c502800031f42c00b0780016140a40c00e40006902c02d40741144031301c0700c940041d0808920003940814000240c010544c11074050140d0004103102010b40e00c09400000442e5075a2100d041c114104182414001f030010089a005040500007083d0042001604030340d0103140300b50380b400024112802800742c410102990b50425600006050317110f40131403500b00301141803c40b0a1795810300d180b0301c00b940100c40310307aa0500852010782d5240c070f03500180301c0d9800075001080c5079408001d903100b02c0c1c81d07040403000300f00e9a42400740201c3c20281c804c41c0d54150100384074042242981c960304c1e5a140100d810b002e48076030110018045034420b014900c02980e0000032203c035400c2c4510400c050703415002c4041d0024204404824142c4030006031030000c1421003000d040d107901c5650224000d40d00495 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 304533902 1250 304532652 304532677
    0x1c03090302030c1207120503131b050307150207081f050601090e0a0c0201470d060e011b0c02040507200606100801061b02011403091006051014 63
    0x1510301503c81400314030424051410070315540c600a24191200031140b00b00c4400701320062003005441d9603000d803603005413500000d08941d9440003500c022841e41070b6412183d058010301100042154a0001c280d4004816400782c40680391941e41803030740c803114031454111100501e221280242443d034049070304105c1c11b25214a100d43c45541030102a2029070ba8200b03002e0743d5140300d4000310f43c20700c507d10340441100f0801c4451030104520a00701840541c007141c1c0202c1c030003000000f82c0144402500c0480024160400d1460300341081c0005100030311680d221b9509080c62107400c11081d040035102840182c030b407202441a183c0a00009000080c807250902940541000304500800d10142d640000803000744400e02d00082800049118141c29a0a0298042c010701901e0740050b21a001d00e61200200944407016000489010964a5010007a0200041070100c800004285070000c580759220600155580310103005900401040030000a500c080c0381c60b50018502004080c2d000d840c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 304535152 1250 304533902 304533907
    0x30f060b04110a020706050f180d050a0f0606080c0a09021b010617163b010f0e180606040209220c080c0304030801062706020303181c0309030203 64
    0x1a0100741210340d9020725020450000c5005401203504001c1130005e040d0038034000b800c2500c90302184a850241e14403001041c0540255440503071501c0d50500c81494202d03044542912450a200c0182c014a105c00c0c0c90941c140400402d58800018a0702013000000c2d01e180c0c40681341600c07141c000e420015200c440d46070b60310010700c1c003403000b4000c010103000d80000fa9000c00c04060340e003a262002a8901860803a4441002c015001100481b0580740b443c0d503c101d207021581d1070385185690360268100751803184440022480c3c4901084200a40e038a514041405444044280c0d02c00071845114402562025000a030349041c41c1d00076020088000d007103040410003e0701031001140001800c0c521403595503071501034059010f0201038000d501110a1803841c10561001001c6080c14081c01d01841030400c800300070a41c20118554076004c55181c4444190348811009480e58015240c056400c03000308060b82c610940400d5510b10700b02164403e8095100107034086d0b01400e4111010344c25400103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 304536402 1250 304535152 304535171
    0x20d14070204140f101e0506251a0106051602220e030306010e0118030f02060d09031e09081e0708120a091202030604060b06040503030705010504020f040c09030f06 72
    0x1c50200d901412014200c0b40c1c2900d001201d05100e00555400107003100c100a0303401c1050484501000d082ea1000c0d03d501c0d0391842241c0400c2541c0d80442da02d240d40119900c0f00e142801f292006001d2031024a402b64405a40d031880120741c00e008149080450300c0c0003e803900b00525040181401114400702500c0207500300c440302d041129501c507820140b680000040289941c1d005075121066202401e0041c18a00d60680e000c03903080ea80c0c0001840c03c08078031995025036807104180e4005840e121018070a07616607180003020050820380284107604010708480c1424040c5480109940c000c80041c004c8410584002e041009500b2001805002d22540030941c0c0a0602007d04d1022542074906da465030713031080c024505211903100c41880d1844144410040ea00852040d4020360040d102281002115001030360300e114035030006515100000e01c800070040190001886103000f02d6241c1401c440c90b0302403205880b0000446000200c40c8002440003891318107808031a107014a50002d0340b0f006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 304537652 1250 304536402 304536431
    0x6060d0b040605060c0f010509120d0b0a09020703030f06060503090a032105101502011112060a0b04060207061106090a0b090a0b01061101200f0f0f0304080702030706020d14070204 79
    0x17003042000d05802a0700c0c101304654090280b9a00459604e0041400004240060215004091951649584805e2820150b039078044802e00a01a06402107503200440d01e4040c00400d42517100da80b0050030540c00150a90042c401d40e8801d496550240c290000300e0f0f601298a5103040050080c01e400e0007c00e4002e1011910800f0301c03a9050f0110142c40303034109900c11903e80000307881321046a06200d034a0100c2c4c0c08000c160307021842d90281211760340c0c903400d00103605610150006140d091012800148544c0e0005100c81140c040d521f410151409210b6840c1e00c401c01100d00c030600b0b41c04600c0090014211200302031b40101400306075510741c5055690703d600c1c80d400781e11403400030320449090200d0600070710031203a200300050055116060031b4414040e181c0140600710907001001700c0d0790041c00c1c50341400c4403030030078452001c0e03507a0b4074091803c02c4013504190300680c02031186003c04900366000081584201c0d00e03d4440a00c004401c1452204a074010341003243c00c40c1e10742100600090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 304538902 1250 304537652 304537657
    0x90605090d0b01030c0e010b0f19020a0204050903091504030c12020a0b0423040513020609060c031b07050108070e15070b04030c06050a0903170a110711130506060d0b04060506 77
    0x140308410041005241c6907406c13400700300607000b5010740c0b542040803503400c03044c3c0d00441d000381e40303421203650100b00008010390034503001400c0030b900903061408220446101100a0100c0700c003c441c2600b92030840c0c0d4000034a402103000061203568198401e02486140400b19070089100514141c8059100c1c004046213400076400f0080b250050f40d5401e9800552640360000303250f048d04d080249141200f00c401c2c04c1103482401034056400050102c1c501d440b45005c66284c282004102c964071558000c03040b1640c0c43c02c6050301e03014001c0110201c3d56600c03505c091801039150b0359070fa03140c20315080b0030030080d2112100140c01c100f0042010100044505070444c0c821400790701d07074440c0c500c02c034280304050702d41c01819003070803038640700c103800000380c200b021202d405400c01d044040654031210303260000d01c21483c50f05541c002c0855404c040040000320454180025281c148951200d20106000e0750b00035200503621803c04d0108090b49140b075409074190900041020510b250303198089603442c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 304540152 1250 304538902 304538909
    0x31009051605341209050f090f09161d010e19050601020718090c0801020a141b070b0703020f03251a010b04030212030c0309101e080712050601090605090d0b01 70
    0x204420813108146174000c07483e0802040290f45001c200b03240c002c0000c110001c010031001e074451164000c103000d08402c200c191320b125050001002c0c1c241d140c05450401a4100c0b00011a01b420700002003003540703860b04018043c1e5061041941145031440d4594040e000090900f070441c4640c000c00505125800c41c3c000165053f80c000082e07240342c9040c2404c0d20b0701c158100c10303096030042140c10860780e80300d151044c081c6101511a910782d90051102c0380c2d81400d03108a600b207445220400f00340d841f80e28001f054454030170b4003243c01500e0040000342e22400750b08140d000440a280f04114014030460503500d410380304014a0502a0305d2000b04c09504000b030b0000303507000b00082014021420880284480121740400031424a03641c401c21a940c1e02c201110a400391000b01070000003070f802a1038a44da007500d00d00ea40c5035080c0c45048000d01955040b0780580c0025500b000042c2c1d652514440c0ca40603403010303500d0b4240c0d9030800c04d0946499002c4032100c0e4102407400c0e0003001062251075401c0c081c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 304541402 1250 304540152 304540163
    0x41205070209010b0307110f060127020a0201061502010504020a051002011b08010611120306060c03040e07030c030c0f021e0316050f150f01030f030c020603100905160534 75
    0x403421b140600034140c5500c006150116888126000300e00e075000a0024112907001c8040c2480d48040004000010645512605020300220702001c003541c0640081080c4d620105408440803c009030813400c0e910259800b82d040144080180060f007000d2600f0294840540008544c0700507400f17008060750702501402002404d0540103010460f40405845001248a801411805c00b00e0403240b200c0e21000d0b140030b00c00c010004209025650520a5500803c002d941500544c0707021600540546121104007001902e0044402c41c7c0c180100440c2e01902542da000704400d07403070510401000002d8004102144c0300034003c1e05020b0320460500709220384070324050110007410038101880c20780280d0004658a016404012200440c1c1e0b402c2d40c112131700b06801e50040d9a4604064803204800d84d0003035000b590000c100543c4070038800061084038130101c1c041010b50f5940e03080300b0402c888034481e1030005000308021001940c210800401615a440c5040c941100d41540c0e95610440120121135 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 304542652 1250 304541402 304541407
    0x10516120206060f100512060109050303040b071104020f0a030e071e090606020607050322060908031501030203060f04021b0a030c03020f03040f090e0109170c07150206041205070209010b 82
    0x141030402401aa11904042d00e101e0141c0c5c41905002d00140191503030580442c00344800500168800c5040714010100a01501c7c0e86546911411207664404101550120103c104004650805100711124282108206c600b0540e920030203c024084c10080e2884512500a0204c2c407404000005000041d242666203292841e0103003510546801d0ba2005082d50421801c2182d220b800c0000c0b2a4000d9841c503548000341c0c203420074010f443d00500c01c050071103450a0340310b008003c3d204000310300481c0000010700d0340f4200380c00110282d10040701c0090b008135200c04802010b080503006010321030314060002d0580d00c1901b40e030070702c3c1102c0c440054000610410600c428150144203040c4160004d41c0598074081c100303241c000240032680300d0401110381d1032001410958003036010351007840e4841c00b003001da511400700310b60b0550071910030881c0c68010f00c44001007008417603024a5081e00c0e1900a051381d5591900c1314021058480c240e04240300301041500016910215000c1c080c2c90103458464 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 304543902 1250 304542652 304542661
    0x10f081504060f0609210f03080403112a0916200f0c180c09060705010209040603050c01021917090a030b040b0a050f04020a0306051302192d05010516120206 69
    0x4450301b5129080701201030a8892240811800101c04a0041d0076080c080d999440d01d14040320750351100c01030b0380c80d14000c07207103550000c0e5928005454050400c01407484a0030200c0100b085504098541e000c080e11058100d0300b8080c0505840e2034141d00b00392035120103125075030303c41d820440d42030b4240029030440c040141c031a10301400d8031500590207000c940200d280c4881da0b04e510744109a4080d1241502048020401c0025011150404405001030041d0360b0f492400b25030310103d014016025002d07280f018400d44040c0c1c450345080340e400842c042980502d080e0407184d01c0e8032126034690005071143c4044042086a00345c103014612501c6004a1468a9290201201c1c1e02400310404000c01900303001c00369072403403060b000f03580d00151b0004013601c50140d482a40e04100200035000030740003401d03aa0329400210a0011101042c0142c41548264410b9a05140001c494408000800203042c081075200303a002c1c100703011944266074206807541d01e42c1d46104508000c0500180d11210821 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 304545152 1250 304543902 304543919
    0x1806120c050406080f030f25111014030411031c09090b01080106020606010e04061a04090e06060a03240e0a0c15050d0b19081b010f081504060f0609 65
    0x980101603050143c01c5c408007201715182c403840794510f14803408001090b03c00550383e82031040e021009694410400500003441c00c07042200080c154035202c1c8401c00d04848007640108008603e881445880c680b82d950340c4d0f038900104030401490310786c052041a4008202585480c80c65908a40544404c10050b103405000c03000e1b00c140903075183c108100c42c0d004000c2030342c0001d01642c1008007403d00c050062040c101140c01004140e0098402651018820301e0000001005100351112944240150300d40d048000b80e0b0303400c0c00d55401c1d402080d10b0404201080c034034907241036500c141048a94021000c16807110590b06909690880d0b900300c0e4242800300101142008010002c03800c5001c0c00c2d800003d0050028003407140140320711512149429540c0d520052000804070072811003100c0341da2920001561b6004403098881c1d600c1d69020410210343c000c10743c0501d2042c0c2d5980b84881d91356005203e03900545103520890300103440701e90105001c544289000b01800c020b503180a0000c2c94205d10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 304546402 1250 304545152 304545161
    0x5070c0602010c0503070e1807030b0316050d02100e0301020d24050f12010b1305010608090a020603160c061406010216030203031206130911150c071806120c0504 71
    0x1220075a890104000d031020341040560768001d000c2d003010b440c28210711010800008541c403032000c07108402c501304640b5035019445070300140c205408a6422781d40110070780b0002c0c1c0040c054168004e10b96450707440103103403e145072802c41c03c492030320351212540d0002081c2660030030709000d0700d015141d07404010024030b09250303185520206825204124a0a008101c06a001c2801c0c0c0e4003400a14a552105c804250801c20000078090715840380c18804600b804001c1902f07000340c000040142c030115070320040c00113400d070790f175900180914616100c1517616440b040c0e8440010042c0f14240b01c8240104084d440b480a0340460451f10030701911340300000a0a240c0b41540708500030525410030300160b10300005403040c40b807014241d4141612041c00080c03c4285040f800c610250808554008025002e84413070002f41087d42c101060310b0440c00342082d40d008440705843c259024003001c01c0310040c0c200440c41c0300e442c40500019080e80318141b58541c0500400c00780c03071108054004004a081c140716 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 304547652 1250 304546402 304546409
    0x5070206161d0315010e0f15010c0c1706010e090a11040b010309020603011e0e060d110604050414100b0a0f030207031701030b04060c0806010e01050310031205070c 72
    0x1400441c600a051404116411035120040201c0c01404a03000c1c515019010b0103500024101d840720a03c03130502c030780404800d0046480a0b1100d00210720030103a450304217809000c01c8102501110042c00044480004081098582141080300080d116a00041c80301001038090054901c82d1f062094210305031001500402c840c0e13011103c54400b1520320305100000032011a404030f1060544c1c1c0c0100d01601e004180a903000c03000200018110083e0303140c4440c20102d404c040c0042560700c1d0034805d141c4204841003a0090740e2415084000f50a000c210140460014129410070752500b0204040318a40c1c1101e0103c0000c3c5030510000034107140030240100001200075241c0701c0f9100c4018810746c0c0c1c160f11407050503000b098903000c0500030641400e03d803031001004202580d59080840c541601034a098656610300110300350840e00c5014154411541a182c110f1451101c90044819600c01040101c00303268080005c400200311080d020300c08600c65a81d036450f0145410300c0c0c0401c0d0030350761 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 304548902 1250 304547652 304547657
    0xd030c02011d0604090510050306090f060601210207050106170c010e03030a02071e080d1205130203061602030d02070c030b0705180402070303090c0b0d0b03031314060403050a030804060507 83
    0x1d000100b1640c614084130161241355001003036680380c1c0f0385600446207594100e90340c1802160304000c0000300c001500707034000050780c0445610f5180c0c13000645414600741e841d0100408003c881029907245500189051441203000058041e41c07618074249200c545400340c1e801d030308510788207100d66a110b1030321040458102d01440c030301524120040d41d031381c10908ca80c080e00c2a10403e001030329242c07201d040c0001c1c102001a10b4030558810740c007c000300701c1414103000132440c3c8404110f0007655092000122179000d802802261240c0d0451171040607840800c1045100c10000e00c01005a14009031038242c0c401c40003075000d5420b5103442c00413090028154000c1210a221340b20340b00c0c1c0d0300b03500d15140b0f00003640c0040e600d803007d0404401030701d410900a010304241500006407009644000d010100b80c1c07400030071140c8040c8041507203e1241c81303d01c5400003615403050006690242c03440010190041c865440c040e600e40d500303420004094020b5001c201514200030034000b49004085e0f0001251 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 304550152 1250 304548902 304548947
    0x41121010e0609061908061b1303080d2a08090a0b070e01050c0105090619110904050c070f2109080604030c0501060b041202040f050c070b150d030c0201 67
    0x94401d28494100902e10b038800c01100002c1401511401040d140c12405901408809905c032201d0b9940d0712410b44010580e000d038440b0f200034070041c00b82940d003098540100c080b003251030740d03e856000f500500000c0592a035a10507441400d0003c0c2400340854016100700b18911520b0310020342a0a0001c262200c1c0341c1200700e8003400211031b03a41c015404280c2c1d040c041440c1c0c02004c0100c0b8036000e400c940c056158646014801c1d4403200040c071900c00c0f40480c3c46150510030520015050b6103802d0100c3d0200c0f00c0500c00242d441c43c00f0b0b0001c0e030303014206440c1641010141e864401c0c030828158000e0350b600c0e405c1e20a40707132520102d40e9807943c0001c09040045602c4e1420460303ea85550003800a4100084481d07140c007080400e400100040c10003401c4581c4513926841c040036078015503c0201d00c914580011000030203454001d40b48280d1203405c0c4141445819192012114402000c041240c442100d181200396107044180004900030b03650b04d40055110f10000d001228101020784030328410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 304551402 1250 304550152 304550159
    0x1005030102041214070b070f05120a1e05090303180415060504080105070e1003020a02010e03031807051801050904050a0501180213060312030209120118050d0807050d02071104112101 80
    0x458101c800640e80a00e07941d18107802410460b08000d000402c5040107c0000f92400044e80c5c0142ca0b44800198403400c043302054219041d94603120f040c00076505a00140004e004004080d100140e65845c003610218001c50010440d4070b207036441e6040900070450115090242c0f00092007010751140aa041404000341404d00040a0b400c4407003070082003540014501940a100f034108041e4006010300b100d440b4204140c20b0009070440611031202c51281ea00c0000c1c041c076040510021500f15000f0420303032a401c001c10300c02c5030340c8000d0040d40d051080480100028201b4403030303c984140c10188095501d40c191040001c1150032644036000c2c542014000c0c8081040315102210605203800c0060f5107220071400b1951240049960720155440c1c0302c1c51b0301c2c841d400d41c03041c00d04d124030407000e079040b9000340f04050b614010180c0e003d0000071402d020341c024142240c2d00905090f401000c54520030030b0301e00001025500c02e0502180d500d038000c50210703001e042502c0391090311000d1007070040c1250b04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 304552652 1250 304551402 304551419
    0x803070c0323160204150308270f04051e04080a030f0902010e060d060b070503070201081003050615121006060f030b0904021c0f0605040b130503070b100503010204121407 75
    0x419180c0100d07419981102c50071507175a0740c00003403051860071850316259030307e00740b682d0160805138102014a084010344044d21111080303640e00094000c01d020040800c01e000d00c40241001010f92404141c9510207582900240284610032840350100315a5441c00c040c000b070540f0580440d03005d416040c82c0324100140c0e01318018284510041c3c1d4026220b905208212000d00601d6024006900c000149007050001c044010704007d4000c3e2180542c80e00c85203c1400d000301c1512003d40030360401c40c081040400a9958a101c02c00020024070407510502007403414070490100340364011703507100420081a40c114060345103400840c182040708800710400303d0405040180000d11640080707400c880508001c0c002013101540020004011025916184004103015141a1449260000082d03d0407031051100c8141c47d90000103035041017119540d02a5801c400741440c2c1c0643c04080c1301103850f480900c05000104000303400040c0c41c1b0b00034286031211030514805070080d90000340052006a1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 304553902 1250 304552652 304552657
    0x30b0607150507050918091504080a030e1c1d040e1e010f0204080d081b160501090605151806010c170c010203040b0603060a050106020c010c02010306030803070c0323 73
    0x1d00840d004107141c0d551003004c0b5264450a04503940c03014045c2c810aa0900480d405a481a4194802c44490004440d075032a50000101d9005014001c1040201c400318400d07008504021b050340300719401100380941c4c10000c3c02ca8508800001a082d0380001e491061106840b807103046c051b9410440c0c00c01000005444000f08542c1084101c0e40380c1000409410952008c0d18040c1024405c640311500c408055448114041c00c0fa800100c0c0c0ea00880c0c000f1218940c03504242c034070000c1c1c880ca00821041903846080030800107071160b559036000100416560f009962064014061440000d0711050402c551800440000f040300ba16020030040d451b40c000d1007216847c6e400c0703520742d00c92142030003e2000e82d00c1184d12031f0401d940044180010001c030f1802141c09400d045040c1c071016641d07032036610704440007441510016445403000100c103500444404421034018980891a251280c8592155034000e031075083c0010700710681c500c141079208c0380c400d5038030003c02603010084400c171410440d00d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 304555152 1250 304553902 304553933
    0x5041d0d030e0d032003040c171204090b011b1202010e15010e28050601090b2a030904020403140601080a05060604051e0403020106030c0504060f0e09010902060d020901030b0607 78
    0x59031811000700105040035565174900c803004c5a20341da07141614042510b81e005114001c3c074040d0006501d51080d90100740010345035019800303e800c117894402200c02408140c2155414481844c400310304501501182c100103d0184000b06441910020001d08462441c1513059194015442003170511030460200f604590480058908548801d0f0f64a00c0c14010284440d0681e2a0b4000d228860309a9400440c80b03600c1c2602c0e000d4060340e903181c140e8001d01c44c004001071510060021403d802d1081d241c00707000c590b2013a044034104404000401e04aa01540054814140c0d4a000c8043c40c0301c10056507024010030710207404641050358845070381c0d000c080c117624407031510359001840c0e11040501c5040c4c2010b030402002d0751410a0f042c0a40200001c2c08155000010318001158905007402030004445d44100385503030b034520345048500500c3c00136242a10954a4051490140c0e035990302038025200300a60040c1e840100d24005422103070703804902406110144030100124010034042d1081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 304556402 1250 304555152 304555157
    0x30906070807140a3b120c030a061e0908030a1e0c020604261b01090210121104080a03050c0304030803190e0c0112390e0d051e0705041d0d030e0d 64
    0x1c682d00c1b0040141440340007000300c1c0d014841d51120006020650304a0351603c0c0010a07540a20a8203060000c250380b40d42501800f10384041001c06e0078012690321407007a502c52400c2d0601c1080b0300c80007444c10784400980c1d600040c0d1004080c4414406207805a2880003aa50043e1003004d40c000101c0200c0e0245030f0030600807542141c03d00c0101c890030b40000401d00d40c0104480c0201c4503100014240070384e046000007450386014942104144060300302c9013610701e0f81d8000c2c02d148420340e40c2120306503c0010b8035040f0b40010b20000001801300c502441c0103401d1340a10714101c40080710424216030310005841900d5002e070400a0640c3d03003040c100c04140c021404081140f00003007200044c80704040410070042c024040440205100606c03059260940507565520000c0988040181c3c1c0001c4040150113508581c2c44403044200b00d0401a40403d24202980c4e1071b565100c000600325800c403070705224000c0000c24801621a0f0030700c907003002c407411070070704000c408050144656a019004005000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 304557652 1250 304556402 304556419
    0x90209180703020408030412060506030607020613080714030702030d020d08060f0414010602031305030a0c09021309063c15030605030f03071205030906070807140a3b 73
    0x410742d110390101d40180c6610400c07a95200e5070ba0440d20380d00420003a05454843c039020104450b032500ac41c001d07014682a03401071215803907015464003503000d540c000302d46808042100f140001c01d00f13044806008520000703552151032500525082c507140302c07003280031900f110380301d003643d140c10400c000d40102c01912292031010340a0085001403a0395000034214001030f000005182c2d500000802d9181050050301141e280e688080c140d0702c59002d80018002e010108060001540c0780e8064100301c400c8600c1c0f070101c41e83e00c0e2209411200290000040d40d000e508001032202c40510035062441d45000950480b41e800d0340d07044910511a0203400404100000d0b41c1b0401880780e0404c40c09024028141c422583c1c900e24119035039400003004640b419403101c0d0000180f0300401c16248074031800340150525641e143d10407581001e004000c0c40500410020000c9901c0075400640781c03001454071820003101140380620b090201002518540607000d82c1d04903a0034046c2a00c402403100103842848 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 304558902 1250 304557652 304557661
    0x1009060e0102030411040f090c0b0306010201020702120d09060801150e1f0806090a0b01020d0e0418030f140c0d120209060c2404030c0201110a081308060109020918 72
    0x10240c251064001501d60010081c0403d01c29401650000c2e24001c58081040126000c2c040e000da0307a040340043c0400800e0f45040126044000040d940058148001840c00b500d030f5000801001c1d460342c400465500c0780620561483d081b420300000340040d4101900550b02d04000e50b89014030098003441000b4181c0e64000d840c0e150070746480613071a036000c40c0c08900a615600186010b004650301c52003556400041540710400d440750000e00c040c1a405801c410f203960205403a0054410080c0d600240c2e0ba0b008003c1c003910130039104c0f20311482a9503103160381d80030038001058241003800d00a548072040000100800c0700041001803400b281c1015100324401401c00c0009000d148800d03504001d00249000400e400401c030819211b580700910302441006444c030b4032880b0400c540040206240c5814400903600400c0c03984d60404030041160011000c680e58154150030014500060101d4400144141d00d01880110f000d007a01c00c40450a0100c2d0000081c0b0260344136070750104c101518030106 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 304560152 1250 304558902 304558913
    0x414131b05090c070c090c0e01120501050a030209040f0c09020a02011401062f030304030c120305010509340801060207050306040503192703060b0d021f0c02190303020601171009 78
    0x5c0c0c00a00c505002003000340d40040028120342c0305210180e000841105401c03059148610170503050398009408078043c1d1b400c40d070074030020003070150095941003640145600041d50903c00c21016040200c0c0160302c40d100d82d90081d0a4410324001c21003211011401844034952050803002060b04101c103103d80c03010440380e1204d14840a10100760360340400000c100c103064104601c00c041511420790441100b843e801c04404460081c001d10390700241500200f40c00307082c081da070512440c010074444c8082c0d090a19203181300c840000c070300801140d48600100242034040c40000e0042600381c01400c0c05290555840e1307201d2051010411880b800180328240301c0f031103000942040a41c0c0010040707800c0b6121060304004000f844111089424091419100e00307244003200181907014104040040c030ba10308450055002e0781e18001000030200b00e000150f545c00825000d00000c00c420030100c603080d800d000741000016080a21402e080d041d00d0b80d107201c400224a900c0c4400d05200140031526898030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 304561402 1250 304560152 304560173
    0x1050907212612010b03070206100f06120609021c060b0a0e0915030a060516090308090103050912070614090f03040e06031606030506120c0102030d02090414131b05090c07 75
    0x244002c0d110f07040010642d06044001180a0386140d000c0381c0c5550303500210a0340d0002c4070b005200004110700e40c100403103405482e040400e031030701800108409440b64038040407600800b040040d10495461b04040d00c803210311685000e401010005443d000c00d10034098203c01840342801d00482c40c0c540010302070003140d041c4510341907004080c0c50007000c0d42e09024015000581c1d20b00301d003a05080c2451012401550300c0d50450754070405203803c00200c400190b008040c0100100307036900035642089001a1440d00170b10b0340512924000410403803640303686510140041803a0701c5236001080a41c40403100000740d600311070700e09051805030b940300c4021904142100700103480162030780d0008240250584c114510402040d01c0c40d00c1ea244059000b143d4031a003441c0300d44d000da04200402443d10308650001c141000c0050300203e4141400a158003c9840c00c55101b0080c00c03c001020040200c24503d000e0049580b91314450142d040c507001403400c2d04090b0071a100f03580700140810030040007110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 304562652 1250 304561402 304561417
    0x10090614091f18091503060c030b12011d03030609190f0f0e061501210209100207150e06030105060d1416020c0d080d020318010509072126 61
    0x1400201914000180030707406032211180d180b030400c1c0f40c081102e904510820014108040600d000e00d40345441d0107004004111108003019107800d500781050b242d85107200101c3c540e640c00020010310036419500104c0701d03400f00a056410400c24400c6540d41d6500080e0010150f116552003004044210401031120714a0041c190342055a405c0c0080c9041e07018615455075041030315003503a9030000411140004080b49408034100d5440801ccd9240d04030a040c2c40c0c2c0420442c014903046070600041e50022243c9400001030380580c00c10f000c10b40b004002c00c203204031a070404640d129000340000b0301601050003890701034480030581c0d440611254210b80903e4103489010f070b030941007840604040088451040300035100741c40104c4000c0c104001c2c4c41040640002c500d6040880c10744c0890080c3d40060414140c841d82211440d08a090038498240940b580710020074443d40703070140d066001d070840410205400040740007040400c0d100344541501c00720243ca400c980300340c050b07550841406003d6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 304563902 1250 304562652 304562689
    0xa05040305070b09100309170903070b0301090e0106060804030507030503272107030c02190503030c060105040605060a02030319150806010503060c0301081905100e03091009061409 79
    0xb50006041585680203290a00c01641c405001a0800300150107030384203c00010500c41c00c078960030504940c00c401401d26010001c00740c8210315603074007460709103810a8000c01d60103551340c02c0302d0a00c59004d11454004207940e08000d18607203859100904140118007000e4140700780080040c02500c50700c1058041d482c0da00c2007a01c01c40707003400b00c4141d13070780c3c889078541c50358000907000c142c6100c5c41d0a0584160540c5991030100720341d010f5007400015800d070b06000d25039000b800008260382d602800030740440c1c40114010805507140c0b10404c010303134110b070784100e0250700708025069850b41e000c4110b075481120050b6820f01d0741e489021000c02441d81c20103c160f05140c1c04004252202e020a1060489000301d00b180c80b25201e810070030b51584400c0c454001c21b0350018034000c480c590b006c00b00400e100d00500a860842c502e20300c068042e2103862101003401d0f0000100300720180341540e8643c40c0354400780303800c07407589007000c5020b010360b100d4440c2803100240101d4080b17100d58034000c00c0e003240810034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 304565152 1250 304563902 304563913
    0x6050d14181501050d080c0a020402120a05060603070c03030c0c06150603061a0301170f1606021e0d0c0c09020a0302070b0a020a020a1106070606060e0102160b0409020a05040305 78
    0x20a0074654032010350744040894090110380c0b2040d0700000300103a043e101c005102020045850395680500ea2040014043d00c0c00b03a80550710250380c461000d8440c400c015100c00c5441c1c03520741590800c80c0d1005042500c100707024410b01c0320242c0d11481e04c401a07940341c2000145841140b4040d02c070402020340040000d400d11440e55055085907501400300c55a54a041c04656151002000300704030f01842c41801840600c010841c00c018000c02940c4c1c05000b00603540380300c440086090500b51001030500d0310120804e400c01069a0403c00d90300b042440c00480c01c1010341000d0303010307110b4035140511000c00406a81aa05228908182000514800904543d40c50440704050081d40001c1d806880115403440040c4410409008480b041800345e800f91a032014982d40301507001e0048003040d50448010300c001c034000303200c500c51403010306a07030b1319030810b007500c4080020703c0d2003155840f80340321406001d000c0003600b445405480507174003c203002580740c19040d0070864841c040d0380c0c8090002d2050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 304566402 1250 304565152 304565161
    0xe04111206011e0b04080316080d02030c18041a01080601020c030a0b07180305030405060703030b0d240e191a01091505040b03100b150a030e15070906050d14 69
    0xd141140103003200525140f6511580c8903001c80650195104180701600100b085c401140c1c41c0d44031856409101e081d9150502008500810032038100700c0d407072130601400050b00080281c1134001e161415508640c140304c550040880014081c6140100340d0501c00d41c1d1000c00c2c0a42e00900841c0790310075015017200c0d45900503091414206509803105800b05000d54120b428000d0041824000e8079040b600541ca428a403a090141c103034002d4005400305941e400c00e00d101c580e1170302c00d02c101d85030280c0b800c00300003039141d9129040703400708000002c0fa881c1703056411003004401080b40c140d44074034a250401d42180c507050070701203200751a2100008031402400480c0010850303109940b4003921030341c0144881c0e01e0b0340a010440e9125101c155255002201014903082c182d0001c0c01003204c098180000088a155052107a070405005a00440d03210b14007484001c20030401c949110198002d803525904007183c000d000780e40313940a01020000006140700d2600e21a070040650100c0e90b144d88000f81c80c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 304567652 1250 304566402 304566419
    0x120615170727031b03050601030305030702031c020306030c041a0112020903030403050f060702010203040b0c181c03030e0c06040506180319020102210406050703110703030507020a0602070e0411120601 88
    0x181c2c0001c42e482d11040700d244c14900700d41011340d82035944c00030051004c2d1f400d589056686400c01440002144810040c40360f049114101e1030384041d00d8208056224102041010f040c1010b403643c0324012032070320307110229540c1d80c030020700f2121100303003000c07240b4424000346907001e0712030b440d41c064042c40000340010800c070f4000b8260b01c2036030b03070a81070307441c03d44884c102217090b4441502c000d064080644042014000c50700f00402c500311261004010b080c0c40000850906072029003208208100140e5001c14550036000e41c194941d041c42c040e1000403101e50004606018a0144c9401100086900300c8102c1c0c0178102c03942120341c004d0403102d1000e8900c45200e4401e50095003280140910342210b0008070350202249034000750f12030098141414444201e030150045501a01001400001c00c040e200043c4a00400303140240c0c0c503240e6641040c0140103032581d90781d10040031980808010080e000842e1070301034126030700c40216401c90007080e001406e0801c502d07888200034044c0800000c0c4505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 304568902 1250 304567652 304567727
    0xe070f0f0614130510050c0708010f1104030b010312051b0d0e090f0610200102131e090908040e0f0f090f0c13020f0a1206151707 57
    0x1151035075503a0485080c00694a918014141183c06400c0c2c952000e00c04e903d01008424140e4a0600c0c019003881d515002d501e192008680c01552103940d03e100c0304980c81030340d002d1203042c1030020713030032914041c0307582e0b64202d4220051101030300701c0c4c00d403a83e01c40510784544125004039240680304c4021818004640b42c6805a149981021600c1c4459401441c00d0120b1158404c1d1403943c201159690355000340700c21009500314690400912100602c0c11140c0d00b50300f130b4041e4a1075000161200d107585c1509210040302d4020841d90410960440d055005028942013600c40070000415094407501c1c004087c1d02840e044090f8180c224800c210044104071003d9200301c0e1400f4411940e0b0715000306542d00c55010b10f40514154000110403141400d03c03803500d080030110984014078090b006c220b400c400350041c003980000143d2002c0c00d603507617032414080d000240c80a1480000c8503c01c045000d0501d09000282080c41841d04c0d0018220070700400d8240c3c8503a03640b1a030f02c41e0001240241d002d114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 304570152 1250 304568902 304568909
    0x10020705010e0103090b0a0b132309120d090c05090906040c050f030c0f03100c02030a03050108011e180213150803210901180f060e16090e070f0f 64
    0x142e101c1c001c1c40240d611a000d40341446400603500e0039551070b5401c02402400d50310b00080d1308622401e040c41c01c010228880c203007801030041c00704001c0750515407041030440006010303615141e0041072403181100344071080729901844058001403100c5a8545140620341d56804958861110300810402c1e0502007550791280740702c2e99126040300c3d100d80c208a442015010415015030000e07201c04001d04003004a0304465a00404a59044205416a1003038a952215260041c0c0012030540c90048d010300405015149013002404140180c041755400982c01c2049900c02a07101c180d5241e607440d6289180e8103c6401405165260341201e40120151416a00d08682c0801d80200001c2d25903001c0142d452980f0b10030000201c0070460408981030010140c01686107550b10840d0100c1c000390010541d003403501c6880c40c2800d082240c28644100c9200c15811070664020700f070341c44480200c0c1056141510a92a00041c0f40b150141c9064681540c1e034001306139004c1d038100046070f806241142c02c000c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 304571402 1250 304570152 304570157
    0x5060108060d0335040311190308070e210303010519030816080d05090607030501060c020306180106080109050c040c0903210302120a0603110d020603010e151002070501 74
    0x958558009100c800c10071000003600040c2e001030900d000d211044601c407028024405102c40a0062001013a0041003e0b0f400314045160121303c04404402480990003d030000e0200c141690055100a42031a50003420b2004019046610014503528812200c240d5002e64026410600c0c50180382a41c0340c4c82800307114443d0f100754941c40c0145205020005c140d81d806044c113814031340480d4020601401f203010494020390203121000c0107002600c1001c3c8105a410010080c0341400d002c050101d0724180c01080c00c000800303a000001d030310005022608000000e082c3c20030701d0500c0c50003a005141e10703000b052182d403c1041910a0002c00140812400c50460b42000198200c81e01501c0140c0c1e82c1c800188400e42251011111004c1e15170382e0760815203982809403500902c02156031000004817202c450959581c002401070103022036803445c06003001e03203400d849070080b034000071064081446203440c011840400185c00804002d2030100b0001c1c041d1440602582c0008040d41301e0f50140540d600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 304572652 1250 304571402 304571417
    0x408060a05070c08070f0b0c180628090303030b100e010c0201020c330c0d03020f120103150e06010b1804060803040312180315090c1a0a0e04090206030f09070b0d050601 74
    0x8400805088801c0c8070449d80321001c0a5071500280146500710010118424901c054000e9030031683d03611807082d204150b0313a410003140c11454080d0845080d04856401080003244090405811094a110800d401d08140d48400c80b03a100403454602e0341e14041b50008080139480300c0c0303c0018081000130814803048c1c03440304031a0390010102402103074022007250f88640c419091180c0203034000c090700007403681c3c40c518103540521203c0e400c1d2400e90048500c8034007201403402e10700c218415103807a0400c840103050369500d001d9988000d4080c028017110500710140a004141c0d599030300500c014140766050701d0311695a030510820744554080010003003002d400e034891100c0c1032035500109890f80f0001ea401e2101010b480000240715020b4103d07080c458408012820341c83c0103c51080b00b682c4000e0055403900d2075040203021008d0703429540d0040b82026420380041c1c1d5040c094951110500210740055a40c225040b85490003d50000c00381e03202c0040d00b14101185030300005c1c03040100b81c80d1000b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 304573902 1250 304572652 304572661
    0x2130b100f0e0306090c06030703060b041211010c05030f090a0e0a02031e0402090c0705031e04080c03070b1219020a020606040b010c1505060604081f110408060a05070c08070f0b 78
    0x113031192811034500d1080c0e08004044400c515005010f5a040041c0d0b10300001c0441c1c843d80c20400d6680f01d50070038018422030750500d004001c45000c01c1141e5420a2034403a21501035561116504d004070980c5d100501381c00304605038903889654064000748071014200c5000c1c181005002e00a5000303072040c1189209aaa503442c0c4440501c0c04140550b80c090121040c660754450711aa030b942214001301c8083c0401c106840010f0341036942100400c51101070f03255641c4c070300880c0314600b41d48000403234000c3e04540f00030491035101138103a44000580911450b459900c040c5601c1c080088091404541c510103d038180e0a1039000070703640d1040005607070401850303103802c0054810300b02e59039004000c0c50b20010b00d01e2640740d240d0041070b0007030350188c049800d243e1105191810103501c52204e000c81c0c49000d680ca40340d202140501c440007500241034a141a007010040d81c1c8803030b8000c1c9042400303620742010610301481868070500064101041030346400883c5848802503096020545090040c130002c80c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 304575152 1250 304573902 304573909
    0x1504060e060f01030b060604091406030d0311040b0f070512090f0d080a0f020c130f0f0c1b030e1201020a080c1603110a020406082a0d02130b100f0e 65
    0x11030042e80020001c01e210382ca103039201718019400074205a0019001d00c40064401014001c940411502404000c80d42c81e044061502c0d02c180b505141c0205030422101103050035014086400f5100c0100c2825550113540d41d05000e44d11600d44010034030302c144c03c4550801740c00600903040b050000c490440d21000c2d0a410020100050400900b00440421189140f540502c000305107280542c0141c5840002001c00185030100441840345020f440d641480d1110039203200b000c00d28181240e080004903802800104404c6200c50544200312004088205150262a00008808005111411803114150158040d40180b00440701103520000482e800d4a2004196006034a2840009086181e00c0c1c8040b02c000301d9010b407130b8030540100b44021000d62258003500d009031802000800003149450103501e0b039540307203450050783d04003510b4940700e05d43c6d200b020f4182c1c600c0d0100d51500c10101034004d4800184503260001e54051031000c034200b2075640010740040c0d050b2140c0c072018064026002070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 304576402 1250 304575152 304575163
    0x1090506040e041406070f1e05040302090405030409091103011404020f061b010c0302120c031303050a0203160c0f090501181808040909021c0506010501030209030f1504060e 76
    0x4855002505200500422915164980d030050040b0002409400c8010165041900558031000056100440343c2e01064020200241c000c0149815080c2c0390305245c00105203004a0000038441c480c504041800e00408006a40280000c65010085040140381c990f12609490460502075420040308011010710900e03941d00c00c0f44c0240210716120700e600100007486e8848d0140c1a803240c0b003c0c01c2850445800d20034048000310030f4030700503a1b800e109200800301200040c0401940070b81002045030000c80c19808095255060400351340703850b507400c0c0c141e040d4020f908042d200300c081c1e9107021081c000040002011a1300c551f01030001c1a489040c0141510401d0003815040ca03113481f0250308c40155903108000318683c80380e0503030000301c6641c0d481e01c1d2540036604c40d0060a4440c4036600962808552804c2e0214848e089a003900d40180d403856240c2d0b10500c1854140345d804100b0f94203903181445110322410740fa50a84101c1c258400d4004403100b416982a99401d14084d00c0b1410005e00048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 304577652 1250 304576402 304576409
    0x1803240606170a0c05040e0c030402120d022a090403020d0807050a140a090b030103080306130b010c060b130e0724120c0903022d0603060f0603040501060e01180b0109 73
    0x3941c0d6401e9994090100180080da8054010405c1c06c003c006041c1d90004510f41c091913004420b503940e82041c0c010480b1140400c5412045038204405c40c8001315000604c420726111280440504002074036401401102d400014903006203e04040004056000c5188816458603803a0742e11143c84d414822200b601031102c4031000f0030004805520b5100d0402e001e0040300040d172410508036920340e144c074041a042070b40200c46803030010081c00182d00e4840c0324400c41221201082000424010008100c495400000703042d0741d6035100821080d4813a00d07441404001c0c0820240180100c4000840d81c0342407500c030760030b40d08500201b10510711084407043e91515110380c1c0e642100700d4980541d240144001541d0340103000c0f00800c000300607140c52082c060a07011501241d81398401c80100c0903810f0003001802885048100104045540c1c0c2100100001c00161111030700ca030713514900f49006200c950020615210345d5400050000c22402c5420001d50100c02e040c031205d0350840065401007060301 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 304578902 1250 304577652 304577687
    0xa0801081209010518040908041a07030e09040501060317070b09030406090b0c01061a030411090c0406050904182a0f05040b041d031b0f0705011803240606 68
    0x1150b0502e039031060018016842007051740940020202c0e0000d0101c4045090480f40c00130086070412801d0b03841821889941800c52001d40780c0078060741d0051807003c0c4030360341e5032140424002180601009611080180d54010410020b40104c0d42024001c0d40007403000b03c4035500481d001419100c0c010065400301c038065102e1f940090704255103401c0d103402c0348008200e25940c0c0c010000300e400c41402e4540e003410001400c10f40e6030800d814070100c04003000700901d01440300041446044100c031022074040b0b8100e0300d0308945918403400098041c000c81c03841c16072a000d5000280041c8480381011a08039a05165a11400c00c40340f10901240c03119071040e001e140e1004e0b0002c000c141410b0704203150f401e000a1002a0180c8111408000361020083c54940d981c004038041d030120420041d4905501c0700c901c010300d02040311407a2250381d4852401428100100410002000c20029468102a56118182e00c1c070b0107280d040068400c10035914000308040c184500050418001d10300211000c8810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 304580152 1250 304578902 304578907
    0x1306080118050a030309140303040c140919051f09140916050f06041203030e0f01110f07210e01030b0a081e030d0606030b131b03050408160501020a08010812 69
    0x1e1310180d004008032a401c0e01d540d840600458511007050006502c114404c6812012184c00c001502ea035a001e4260030354051000001030140c400d240f00c424902c085c14008020072150f0300d840f04041c005003486440702402102d24400b1601d10705a030026540980f14080402c801c2e920316404550b2242054841c00100202001c14049800c08400c0030b0b90903c0301404071890660b0b0b03400c24480c00566500282c0000317941e10013450301088244095490f1040f140c1c020700c1350050030105410305118940b5407c0c82c01400007029420440010581103403201c00851105d80d00701c4880d8080d1000044008083c0080d1070081140010b18081030f0882c00c1c0c0380c0400080108005159405d4003160002400029a110900200e1300da581680030700405003490b0794020418008401c28490101c0340036585900d40780c10100d113140c0100300080d28040440076480c010507030381c4450a1045043c888c80d404004a039813070760b6a42d000c0c00310540040945001ca5692410145e0344d4620035030302c414081402e021812401c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 304581402 1250 304580152 304580173
    0x10509060f150a0302060c030c010c0203310306110310060c0c061b08040609080c0a030b282310030206030a0f02040f1e0b030c1b0a02130608011805 65
    0x40501000b600d440141100c2e40e035585940001e0850342001c45811015440000c0c1010300b22020300034011415481c2c0021400c0c400d281080f44244c45040d003c2c40a0340311202c40480d1100c3d20f140e04200156080070701042111860642003000e07900c00c480840f00691051000030b111403041c4a66028190840062400103045c030604540c0d501489903e500300b101413543c140e000c00c0c0100020001002652140310115180111040c01e00c0b4101078002c4c030071640d1000c02c00103d40101892a0300980701c0c5100d40002c0fa03018581d0b507185400c0c41c21540c0d1680742c10711410401c5c400e0741d05240c40d801280c41003d00740d030303403c00e40000742d00590000941100341400810001007a540085002d6002c5000250420780c5420098507016891742c412002d060f81281d181d603441c14082c6c00580a840c204060a00d1441c100c0080b003154401c528440e120641241c5040c450301009009940e84154018403065603142d80c01c0c1390342c02810841c01042425403074a006024543da20010101c0050361080c06030030740d80d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 304582652 1250 304581402 304581421
    0x910030b161b05030702041109010306050402030c0a08072607080a0b0a03030513030b040c05010813051b130c080105010f030608100e030712030906050109141602011b0203040503010509060f 83
    0x4164800c8400d8841171284e0001070340c0d507010b00c0d044191914429034903290440d0005080d9081607101070701aa00c100180a0101d600c80c00b00c540c0b440503424149040e8481d0070046440640ca0034096050b00814498240300a42004119004186503503580e00d4a482d080d4404045a542c19100ca034840c145150800c00280984007914200d070b1010b4849101c0c40c6da81c1c075403110300306049500322001420040b0600840d88c02108071500008200f07140b11440215544031659041c003803018490102c2003603102c5030156103a502440a80c0030120b0b0038440303040d0b880005400b040c000c0c0603071804942c0100c1815210f610074421082102d0382d040c0244568001d54a0401c01006039505107041800100024000301ea40d0580340e50300c101c81541c0c0001d4061035801c0c00c80c2201c0068000c214050305085000c0c41980850600030740012040c100c102c610b41d20104281c1c010030840712003480b9400f1718003e00390500d07004405081143e10950090140303944964159458140c02c543c94500710081c800416032500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 304583902 1250 304582652 304582697
    0xe010501081314030d0903030204092a050c0c04020414010806010503070f0302070206090607030207030c0b03070c0204020c010b10050a2a0f08040801020708030108010e070302011d0f0910030b16 85
    0x40e81c00a41e45085c554420010542c4d00d01c180a40200f40c0004080050044511480408100f05012100d005100c0141205000304006184041081c04503105c40810414000d016107030760001c0046658954401c80c2c20b0b141d202c02e801690108003400b00046145d4021011244120a990f58042c1d017001c29080560081d0409181642c11a4050010340007503202c6400504001b40a500100151450362404403140c8000c5c0d00524041341043c804d102c022504440e044845503811a030142e158840d0540030350040c41e00302c400503803000001d80e0b01c0401c603410500614001d00c1c02d40c0c8102c696145490000010220f0084d007908001000c40b9803000318440490b181401880b40105901d000e5032200d5050a82c1c20105058584100000041155540034845c0c0703010a241c20010345400ca04d5500060412624424080c5214145090710683ea6450302e0841c0c41e00700c030080074100241404590403890200c0c2e8081103600c4418400030408032101494000c000402079550300600c1008a0580114a07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 304585152 1250 304583902 304583933
    0xb16032a110d0e030d0201022718160e043c020309010516111213051507022d01050a11010e100b040b06040302040b150a090e0105010813 60
    0x40100400581140000d10620032140c0c060750300c3d00c00700c0001e8020181032a51100c2c890095a10421101030f1028160160030016610102e000704400402404581c2d542d600c14450400864030404020341d03007280113486c500214080e40d8585408030017106010032110300a400d140e514034035554401004420f105119884a030040501200d440b04410980c166042510360800594459041000d2041c4580480c60700c1c540c149031192030f01011807851501c0780c0055800c00200140000e05051700e0a81a20700ca0003040081c00a1201d11004120b0014981080303800301c0c0b1600b42802035040c00083c890684168404610881030300d070450708015284c41d840401d0355005d10440810b119100320083c031510030140f038128003801110180807594030454450b03841240c416864200f52a0755511484c05507026a82d041d1030001e50100f0100014a80070602d031400d09a44d20001482c0c1c1480d54810f2840d07080321001d9152030b01a90300c070801903880380011110303049805894821100820144100c40089 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 304586402 1250 304585152 304585157
    0x51c0b04050109140601080c04020a080621030a230705030406030b010e1206040b0708100605070503040b0f0c1b0f01180b0313140601080a0b0702100501030b16032a 72
    0x288a0303481500080700552101c4d015000300004100c030340c50030f0000b025070101c1100d0461070702c0c41c0940050150031015181900803140440b0b08a000440c41445081d803003a4001100d4403840c03040c0d40149014080404e60a44411b4060310140c0d000203842035800b2941d0000245040c2410300070101c000b0041001011304118500c0c90480701c54440e00d2082c461180b08030060140c80c038040c03c200e070344540041d0888042007604c1e8200031801e001000580b00781c0303003c0d207800c030765403225801c283e07146000b00d0b0031100108000103030003042c849810f4010034000801c88251044032400c0080100381c1c8a204844c0c1c0e40007404017000003019803086401481c0c02c0804888050020340301d0304513980c10380085405800c1c5aa150000f1400e10041030314105a42c40c01000518056041c034007017079290980080000c155044100119681c1ca009011003600b003009210204180c2d0303901d00346200541001c0d10402038480d0148030b4040075038440e000300d8464801c6d00c0c044030420220802c1c0314503001100490b0408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 304587652 1250 304586402 304586411
    0x10302130609050a020301030b090d0f0c0326100e01080c0d0203010f060603020a0905031c05030403050f0304030e0a0b09012106050418110a08100b040e0a030305040c051c0b040501 79
    0x40c015428403031140a04c3c1c4c0001c00584942c15450150400700300a0b103401e0b0740364801c9614096281d44400d2000c411102031070180000c5041d45000da5158104003a5201c0300307803004201485100c003010009120394040101e00b40b48903035500450502540038000d004030340d08800c50700b1700700e828901d1286604071320190001612036200014a81124042e40000300001d4002031160700075075003c07201c00090072080f006010140344000311400b21421080040d4103010b00400060107050241040c3c40c2d10b070b0604180a075492030075203001010745103001001845120403040111380e8185440541d01e0109040e110709100761541801e000076101d10160101190391600004102034989004208080241b0135084154000501e05407134041d001680346806070a810300200a80e11000a80b10021500240c001503031986801c003090141280022600b41c40c4502d9081504140d40b40e4884d9100d60701072407410045035218020058050402c0da29404d2060032800940c0c0800c00c0010102d8005101e40000107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 304588902 1250 304587652 304587659
    0x901050705100501030204110c06150a0f03030521010b160203010b04090b150103050c070609020406030b04050d0f0509060d050c041d0405010509060f1501020a061506110708060103021306 82
    0x82c9080c1031408001416521a0010800c50609002d12150020500115070030042c4103102581d85030401491968040754000102038552200140c1c940680305c0c01d01d03082c0318140c4a060141c020b500408040381c621185a010f5503e55850720340c042d058845070000b03585400489421205136502c2580140da2555a690841009596901c61102c05a07c81ea90350080d0703203001d1139400582e90200b0305081c1450b007040b040005006501041b45e404a90107400001e2458540c00450001d00c51500010078607040c0405100a100000071020440c2c01d00b85d544146c98640200100d1b19402840211030704083d040c4502e0f00d40001c140c0250342e008649805a40c18150380e801e05030380d4500121821100c1c2002d41c024441400703420700445038400c6100d4000c02c401d043c00c40c19070074000002002c1041d041249404801282c0c4217100d94100310b50131a0051004c5825010307010410f8541c1c1c82104003203000d00e0100c1d180c0382c1000c04c01000f11441900540626803854085c0540b100d504a8000c000d16034418010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 304590152 1250 304588902 304588913
    0xe010b0309331e0106020709060503030301050a06080c0702060f070212120307230f0901120504080412081c0f18050a03080613020a0e010906110604030e01180806160f0f030209010507 80
    0x113030003050241d0040040b0b03450140700108407580d61b000310340650000c00040c455601c850b00728100326261860f003a200e0f42d50305048002c84d80126200258081c2c0d00264005824903450040c00e485402110310110407002e8120b0240d0f00d0421980035841e030401032000a84541c02401d000601c40302c035041c140048140d40003807008a5000354440039201c8000305040c070311564040713101202d054204008000d00c0c103003611040480d00443c41148144903954008204105500c0103030b56001380400d00700c115020451440c5400ba11152103800e4069191000c80c201e000303102c0c0000410550002d0207000384e68180e86088a95141c010403454010f01c11425003011000c0b140b00a000b030700307002d9a40885c998000700006005102c40d50041c410401c4000701c0e1103c1c580e01056494205515092100040b0414001138455040e4600f0070106240005000203211102003955449460b12810b18030301001880c2081d140340380100c11010005000ca10b20181050180d4002d000d0a003050401504040955030340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 304591402 1250 304590152 304590211
    0x3030510030b0906070810060219060b04050a050103050d020a080304020d020d0803070c0c06050f09221505040e0d09060822150b061c02070c0e010b030933 68
    0x3c001c03080d0710620400940b280e00c4a403494000c2102d250344d456403031030080e00039621094001c03c0314240c000442504204100e550004859040280c402e0102d03143c101060401040e0911060301e49006880c048400c040c40460000c42c03040d40070000a08607140c940034060041d80f081001c03071300203007481340c8a00030a2080c00958400d0034280c2d1290900503c901d84600c0b00c114583c4003009200c802c1c0000d45880780810169940700b001507500b45400019000010101c03d0040300b4040702d01c1c0b0b804440080804030ba90004256a03003034030300780960508003402d10740d0f5028041c2c41764009205580c0520056205022454221503811804050080c0c604015100813610041c00c0f1102680c0c100c4400030500a40201c10a800c011100941400d8826a0098255280480300d40b06a6800a0704104002d8a0b86003c00034220074403d803802c070341c1c48184038126035009071094485071080126590640c4020040032816048229103100e522041c94818520030101801d0010f8080c50f200c01d080f9044903800300c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 304592652 1250 304591402 304591411
    0x110406120f06091103181204180f050705091503060109030b1504020d05091b06032a04030b060112110f030421030c090501091d07020a080301060f080105040e0a03030510030b 76
    0x100681c1c0c0e4181902821980e0114085041d03143d00f084030040c07d414985010754085500c03040021440c4861704494000901ca162100400185400c0520990070b03882406040d208005580340010304e00e40700c08070074040c00212501400524403880620000b4000e0030403e030800500450b028290254600017000e9800851344041d82507a00d0b020007140c00000c01524a84c0d03610240785502000541c80428414400100000403100d80b054400c444146030441c40030700380c4e80c0e0354401c40d221a12850100c10044080d07606030b002a1441c1e1255406407164421420050888003150f45048110b09030020326400052082d101d000c01062048d44401c0342142048120b000c40e80d00046081c10640042c0c00c0042e0303900303701e0412100b084240915090003569070004030700103183c104541d903107a1080707142a051030f8000304a4400400002903c940002d4017200d0207010352152034140ea212001d0004443d56015001040e80c00308201401180c002d5000c01e070001c0d000107903058480d44a0b11802c00300441600d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 304593902 1250 304592652 304592681
    0x10091d0d03150b180402030717010e040615210206090402160b090a030e191802030a0c050c0c010c080c1b03150103020325030b07080703110406120f0609 67
    0x1450100350311400c2c0c070810050001803002c04c1c01c11030600b400040702c1d05041000d600a540c00170104d90010300a421590359182074011018466860310f41210f500801034070115002424500a844005a40007001095840d100000d030780a9503a07006401545844000030791b0408400c022960064171280000d0007168401170040c0e01d0480c440ca010560840000c21038030301d41d0061446500000d074441e08408018100b15800d03074402c60b00c45909100c140890740150901c1c10080f000b60b1141c2006e8000e903100c0d882d40002000000c60840c0107132284d2284204021050704040b00c00c1c0c0c010760160014070501c84c001d0440318182081412007a15103012403440501c0c042201100e0080c42c6410000078000c207072502808003241d40f650340401d070b5500ca464042000650007601000c8409640011600159001444500c050a110700b01074150841900d485002a05020400c0c04c2c03d400d44003203400315660342d9240e0300c90602c1c100c5101700401e20b00840034800da4a41000254407851360181c901400c0040c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 304595152 1250 304593902 304593911
    0xf0a020a0b16050904021c050f01030c08030a140a0e12070f0b12010e0c190804030206060301060b03150d0f11091608010e040809030610080d0201020310091d0d03 71
    0x90400825801d0010080c00b020340060042d803404542c4003003034425030b5009840158440c038003e072040c4003810309080010206c6252008102c01c0c8140100f5040c100c90045004020003615244415201c3c4100c441c030707001140c0d541581c2d00440b50000d0050001d0805480e03c0c1c00d01c407082d100014400e0010f0031528105d94400c000030b010400c076000140004007012203004e07190800c91000200402d5051003a54184d241c05400266542e113901c045980d4920807032010304c41c0e04201c1304068640c0704155400c1e00188600030001d849030405100302401d942c1c2241c245030655031440c05030740d020001c201d00c0340c1d08680c0304202500060311f40700c443d800c0755215460150713245461a06104ac109002082100560414000f24121b603400054450560782210268101542c45050410301ea00c030f404280b5815200b40307407c101503034101482402c251003203a000d81d1600000c0960803400e0703010644038200707052645002004210030540c00008405c03050540b002c0d01d80e41000f01b5600340710707202c607180002c42c0d02e6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 304596402 1250 304595152 304595173
    0x60c03060602010b0a06111f09030f031a0418061505030606010f1e09050612090f012903010e0d0c06060e0432031605070e06090a110f0a02 61
    0x5801188081c04041c4001c00c003c159000014400481070b105003400d1001c2d001c2143c20100c2c00b4800301c40c800d100c6101c00c4000040724130860005004a0a0990003e40203507221040b0324428000d81c507041a808000c000115000b41c100802032903505550b0b07801c51182900b542c00143c03280120b4429010903001400058902024141800c4008003080d0403c000d0030b154040e49038016800f850f003448203405c01c402d2541749010954800c0c0060700075550180c00498104514401003040c03512400a16003552008c200405400d400c0e1040601160f1080208a03c43c0c96000c1b416500c03c04040d400a001065000c2c03080a024240a140701719400040c5e50b21501c0c60031320816000d400020303c078802c4101418549078a801902940c1480080030041c902da88070701d000e00310707040890300c02141c0d01e0560380d07280c0c15030325940c2c9a501c20520443d464001d035a40000d407001c00600c0c90380b01d41c0003c1c00c40241d40c1d4036040440020550f040500c004800309100035401607a20001500300340b04c82e50020724011a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 304597652 1250 304596402 304596407
    0x603020f090912030601020106210c05041109040e15070903050708030403200111030a0512010801020a1710120f020310110901050c03041e17030a1d180103060c 70
    0xe80c480c0d0030301490003007007440480031002518442480c000881d0710b449880d0800101d014000c00d41c01074129070500c19a102e45002c10310704560045204680e4480f81c84d685505000941d58087c0c40007218030014400035500c0e09082d0000170003103046a05030303440700e12031a5040c90548015600c180008400140c1403080120811410014000c6a0029030406d072441c1d6508080710001181c190340da481d6043c2044450340511110500c3c0081441500d8075290400c3c4010015040f1071910035040701c40e08000220218188215080121300c0da13601c610020b22413240c80b000c0480a009032100c000151000500218403590b0344131414031030041c0011001d05801010326110480d54012001490100c0120121290008a9045200c28200540c8460100e01d1050440c000c0342d1050030158101942da03000441d0070940c2000351120020b00b4141032480401c859628056140e2a078042515116401d212801e400030304108288000c0600c1034190104518401d401400e0b4401c40e0100e4641d1900342c0020b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 304598902 1250 304597652 304597669
    0x60914010503190804090c0e04050108061012021804030c0501050a050f061804031202070501020d0504052a010c170c0d0e150304020904051204080d091a070b070e0d06060302 76
    0x480201d00003c2004903240d40e000ca100781c1c82910300845d0b95500010f00030307015100305502003000400030030403903a44e8206543ca5482c1142c0c25075181c070301c100021403404541083c3d201e85a80203003146210010018400183c44d102030019414480700300203080000c3c4e4240140b500c100313400fa0008c195400d10005103546220084e00c007510a00d030700d29440103041d4a1550041c0d210745c052070310f420035921030b0300c900c4001d1040000251a41d400083d5803401140c00b0340205000703a10907011900b081c2011115000074081d10001c02440421852840c0143e610800c90401d6a9009140038070170303207240701100c1c8140d0348240b500c11300d990000501e441003103420491445107180140c64501c4d03100b1001c4002c00c0b072071100031300c000c0c4101007050204051210411440865400401d0704540d519214409a655412050984400030b0319140d804900b840484501e01040594100104c0c101a0b4079520042451170040c21501041094481080a070b40c03100c0d2218012030282000044880c154014000c022 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 304600152 1250 304598902 304598923
    0x20601092d2004030f02090a020f1201050307120c090c0207090c080f180a02120109050a0308010801060f121101110619060807080a0201051b060a1409010b03031c060914010503 77
    0x40b0424403040012031140c0486604640e4121111901c90350760319404c000a0043c03040301603550901080e8000c038440f04810060603039008404035030a0710f9840c0d0b034203625030305c1c40b1000400c95076450500308001030050300914280c0980d401030381c14850300c5a0691089905565048000811140a03c403c5001820b031440d0007603640c0140d40c5008031951080d5541700c403840d400a00940403100c40b0280000c0070b601c07200340d9030750000c1600c10500c42c506006080740750a0107102129442c042000886200e0000350904a5122080b801b915101641702c3c3e1f540c100740e0840d0036050015007101541116803d0040340d10130010701d01b0384080801d00c852102e00320b030842d410161990b403001c6000d208250700055120005542403900998070010001000706041400744c02c1d0110b84a118148241150590002e1040490309441c0f41ca055448900050980b200644610303019081000150446119860300b854241c05d03048010440c143e4513100c82080304d191070b008104102e0740314010301c200d00c0d0078821800350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 304601402 1250 304600152 304600211
    0x5060709060e01030b0102030307050d0603021906020613050715020a05010f0f0c0206060303220b030a05070314040c030209180601030c061124040c0b0c070303020f0d020601092d 78
    0x2840000170020b552403001622500c00d00c08045461000e0700c420b504164003540c0d000c0d24240d01c5814000c0010420940c5e4010600940501400158480320080e15401e1040c0c00c100106052840e01900c010070741009040c00045010390990000410401d001c3e0201c000343d03184000a038401501741d14030880340c0c088070010454204000f480007542e400415651200c20065603a41d1b915000703140441c7c2c950150340000703800a0003204000690100d44d0200344503212944013030005a541620224410804440042c80b00100c40c8041c0701504103403c00d00e600050380744080640b60b03980b0300d03040e151481c00d0703100f05c0f4489070981d028001e040c0d01182c1c5002c144007010060030802c0404000d18100707501448503a04c42c1004400180038041405295402445801d00c520750b43c4442c00c40d4070b030b1101300b40e02095025200d0280750440140c400154910264003640c082d0840e039003052400000303000f03000e1180488001c101d058030102e501f14688502c90094910700010421078292015400c82d03085000440c0c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 304602652 1250 304601402 304601411
    0xb190204080c100c0b0103030507060b0f01081b04050d050319030e0307030c0206040902070f06050702030c0d0c06140108030406030b19051311180405010e2203090305060709060e0103 80
    0x758650010344685008401c9440d49101c0c51040b00071180452816000742c80242203400010502d50410b00401100c1d010b0713034090150140366014001e100700c0c5203070352070300090301c1000003042c0001000d090041a0b5100500034581561280003803810900000290780940000580842ca03c1090b46e2466442142e4101408070041904209484c2d008100d005414081102912011940c07401d00715006411103280440d10b0300c95601f030030b40e114105d0250460300c29180c240481d2031207000005a900c1418680000d0400000c50041103d0346100400c00300c0e446031f251003000010300c5002001e1406400100000d54590b480c00000070283c070b291400f4030703015010110100003041d0030758140006580e8240c03103203100d1001c007015060040071100c00303440c50680301050301d10140c00c801820505101080300c013800b031039032603c004101c129000e45a107401420003403100c1d02c2c0b0318903840304c070301c1c0d440e0080c20004005982c030744410f03080c41e81c00c582e0840002c507846020720005030004507114a0000030310f0100b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 304603902 1250 304602652 304602659
    0x10e03060103051c05071505011e0e2a0415230a03020c0313060f17010506040510090b0d020310060512040b0a09050703060219050f19030e0303040b190204 68
    0x19110039280d5030000c0d103202c00d0440b803072641d070145d0704444c0d2140e80301083c1c540024580c000f40300140002c0c020a2400e068000c040344402c18445448400e81d2294101b84a840d00d07142c21700d45204e1030802580d0790340314080c00d0f556100e05040c0c01400041a401c3c00d401c10450110710001c00c5020107100c0d80c0c0ca01e64840d880d035040d8540e001c041d1011684d1b0390030300603580c2c1c407100c681b82c2c6180034031150802042e0140c0004517409602c8841091913603c03540794900503841c19400042428400d0150980051060000300300b0fa140641411107071482d6402c2502c030841d11703003120201503440200d4036016140c000040c0043d02c6401100700c0300030203180c5042c41c2400e452241801e1904ad0191000c0c250f05d11b8000400c0c10b0034001d5001c0b040c500d90040031103043c02d599282c100060b4000d02e0508419420070317100c95111034000c50841c0e48000d901c40c0424501440d880c00610800b400b91030304402c040d5684003a404a1408000a50003580288412070151800c4038401f404184405540316000b401400b041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 304605152 1250 304603902 304603913
    0x70605100b041a070605070207050306070e0d080901110312060f09040b1501180e090f0313030b0a0b1c060e0d0207091e05100806060607111315080c010e03060103 71
    0x6400340c0e01c40c061401410503944119080b64001d190005c1d040038608024004026000280c02e01119001d50546c0ca0a5a40d000c0c00c0c2d030034039184095031745c00070714503803004000543c46802004401014105802168880141c0601c0c54000e00b41c5001c800400c481400410310f04401e0300002144c00700e0329403095150035903c8506400000d80000400003481920040903802010051170320000c911032035034155514802d20a00050640b42e41001b13008914035003405607004012652070b0a10012a01907940c82c40d52144c2c1c003001c0050007805640e0342c07075000c141e107651200303400308112214841078101036210b402e03c1c100b103800070f80c20001107901521882c151190003089000c2194102d0381e00283d0410224405010f042040b401850704918060412500c0c0a4230032440c42690501c1045600c90303525282444800e108030307000608885c3c0749528002051800521380b00b01c02101c01e0000c1050b050801030301c540720b40b46810045007030b0000303605c0d04059603100280c000822012401081c1c55403458541 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 304606402 1250 304605152 304605157
    0x50a0b2a07030f0c050f101d0109080405060f040909060b030c0108010501080610021509060412020d0c171303060203060f0a0b04050607031107091a030f100513060504050102070605100b 81
    0x1d00c0602800707114113000e001c0d00303010302540040b60704244d5140508910007280200341001c0d1548883c032402d0808000f6510500c5110380b601e902c039005a103003500f0241080150f03001910107246107281000041440356a502908170142d220750000b00c0c0102c89941054200b2000620396810050b020004200c0c80e81d0100e1081d8008105441075a840c07900d04904034141100d658100265840e80028800340041c0015400d200b980074104007081e002841404a031903500302c00c0c0c000c000031840803074440072510307104a0041541690401c81d140050f0400c0d1100100f5940d4030540b40c09a004c000c11009013071985e2030300302c90b001c00c907a0080700b40c3c1030210a0000717001c2c41c095240211404154001014000d5200081d54000042198141a96040c103040588081c1c909088801c40081c50070900d4100080d802c420040054064040d07486500c4100004050003403648103590b8a24101e003000c200c2d01e10070386001d0760085002503901c41c0c0c58180002511700117498050301d461400b00030400c0a29030001e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 304607652 1250 304606402 304606427
    0x20c040501082a0301090215450120010e0111092409060c03181008161407050721120806010909290103061d04050a0b2a0703 55
    0x4000f540600300803134010101c0ca43c1c021340101f0241c2040e5110340501c7c010f042d460007840415401d00e1440c000c00c00c0d13408035012007a240c2000900d00b9043c250b1210b1075810b44600180741001b000c103101201c0303511a41d81a080c1c51160396480140c00e107121020f00442903c0e103c4c0c3d85c550392900c00113130003040074002142c905c80558802c02c000d40903004600d00455540b1000204003c0d101c00c8415540c1d81c4903400041ca1000d1844240000b080d42c2c204042d604142c01d20315140c2c00415520040c07416603403500003104a04011081c15400c01010a80c030180028600803401420b0a40c100480c0c01c85004030700903210008443d46810340000f44484090350241001480c0510b425140c1e000140d810400540008040d18100310758400d203030b1a0f414000700010802100400703148400001942102d00a00882c10b84071100f200b505031001056141c00d8010384160200c4c2c1451400d500d40719000f0034151280b410089160912460401c3c0b0001c40356002d044c440c0c0000c2c600885035501030030f0031a0303074034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 304608902 1250 304607652 304607713
    0x1050606091512190506010305010f030f06060305030a0f0905030c0307180b03070303120c170a020c12030a15091e0f020d06030b1b13120f0f03020c04050108 69
    0x28850100c031007401c416950311185040d01c90b9494240303001044c03100c90700c10034141c4800c2e2034000090b0856210380243c80c100c60b03e10b411b00c0041d03400c4d5200c41314610104601900c000d0344a0030300100082d0f040009100303175001035071a40f50000c18044018070341e5200b640300d5840707a88012203041060360013243d401c0445a5155601d2080c205c841c0c0c1d16006003105040309a40b43c0100d1030004281030f0040e50180405000d50360070800e803c644801078131079888111207444042c0701d00c80001c1404402da8010040344c2e01c0e00c403c9604030282903c0c0408941d10440d4030030034140d1602510340d60201c0800c4000301800038400140200340034508801c105c44200341d1074603407064496862140850143c2e0480c1d044040031f0b0750611801e503c80c00c002000c0c030800c1e20110091110545440481d46401c010344d205001000f10f031940c541c1c034080100341240505802a5000c4020315683d0380010180b44c0c207820954400d4014050542c031b0082000101c0d03405030301030b56090f084080001003c1412501d0010540c040d070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 304610152 1250 304608902 304608919
    0x60909120301090f06080a2301090b090a060b010c0b06150f270109050901180b0a1401080609070c170f1804060803070305030c07052107140105060609 66
    0x60a21840c00c0910000c0d8584400004004070381400729070000c40d526840b0b40d106002041d580d035265995080350803c0680303040f10364121800b440c0300da049503030b1802000c400082403c1d42291660380c108103003035946021b945e010016100404c000b0b4000d14031044000d003000a00300d070390b50300c2d2401d00d200c009000034844d0f82004000c0e0307220380301c40d4141c03500010403050f05902c5200c62030021546040308190302d4103a03484829a135055600c550040c40a42d100500100403a0346400040490400c423a50300e0b0090ba40c07103a05140c5036845440f0028001c003000f80b50780300095aa84005011700c18050596070040c4034000401040540044110341501d40c0405102d070668462040c01040d40100d0700e007500c200c035000071181c0070341348150081c90703c026044a080003110354500c0810360702d1151400c004e000c5441070000034618407844024050303084c02501550001018032141071600c0c854100c2c04c03454032502191b00803d100080c0840541c00160320020440d6080582c0001c40c507000708107440303200d040319 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 304611402 1250 304610152 304610161
    0xa020d1103030f0304110f03060601120209060c01151d13020f010c0203072606040320030d050408032202031c020118030e10031401060e0102010b0904032304030b0609 73
    0x80007100c6503501481d83c0161030b82801c0c9031900f803056032240c1240c030501d4041e0340c40640340741c0426540c0c0202c805855144015011060f48400ba41081c495554054418401d20780203070001e0082aa00c011a010300001041c10610003861958104c107403841d81814500810000040c6100040310440d01140c0d40c01000810400403a450340120350001d41502690400084200e181c44902d801800404107148454070741c583c21a0359490300f101c0c05000140c00e813819a900b200803602d8800c0004402041c0c3c2c0c900302c003810841e01074442c10f59044030311510010801214890107046500c42c5000c08400c0300c003c00c429000251394541c070360380c0c000380c0915410361010818001d6005840c07404074074800c030390703103240b1401c010b03100a0801c1c0c1b0041c020368403084c40b640e120307109202e010f5181440c50180d10069081c080202c400802e42c0c0511415036607184a0040195560101e2078400d0b4400d079142c0c90f14130007591450581c4882c1c00340081c0003040a01c424000120000036813030340314006960b6160b440d641d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 304612652 1250 304611402 304611409
    0xa0207120e0f2e0509090a090c080a03020c010f02010b0f0108060f03010e030903010c05040f1e170d0219020d0f05030403020a0e060306131511091e0f01020a020d11 72
    0x3850b96450340d2207608418034a00eaa1031411140d071110940002180e8200068841641c843c482d441d4071642c02480440081c0c081d10f001c1d071041d4959801046803180300c503114880359181848542d8251701691044e23042852541e48031100a0344d0500f05e20007404065400707c00318121180750fa400d86d0500030244005100e6844021081c14030010040c003d20103035000740d00d40747d11780e03010300c2d44540a9401e000c8140349060140c4101c808446000306003070b01d001e10f07100d100da80d58071b45404111f0500c01e5220740050340280310b4260503804001e64000d02701c040c03c456000b034640084c411000c40001514005607003d030380ca1b0031041500a070480501c109103030b01e42c81c1a41c194400c2d0b070002035004c0540786003c9a0030700e0a801040c070844080d0b08a400c1e40d155542e107400c1ca1815000000c101180041e0f50304040074403a00400b4040034103484803030070000c1703100001e00721a00c402060395500104903544c40340382c5880d450210403ca000c1c0050905000c00b034011400f85071002002038455940c0820383e00a646 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 304613902 1250 304612652 304612669
    0x70c0203060712020c0111090a090603050d0305090a0c080f061f06050702030a0503040e150901031110230c01060911030705071104050103030507060f05190e0c09011d0a0207120e 78
    0xf41c0d0f82001f0030542048034008003d0b600502019400fa00808130081060340140c0710350404e4a40280060180d65a1407004074040c0100074542101d0340126020710001a41c061448000f808441028018880d00303c8402c41c60030b0001040e14112824840c0480254914500c110094445030701d8259607401e054004079140c540751804c010a41c1c480060001810700002d0241801020032820039002d0380e400c1800c1141a407404c0c003002c1c0104501042501c1e80d464a21200088507001e41841d22541a03400c50004ac2e00d55604000d081740c660020385031054000c01e20038407001d81000c004c10424518680e110034103a000c0203003510b0070300c80b0000f02501072004406a1180000380100184039944e12468011f000b90001601180c460342098141111017241d4090f861244001e5010f5020f2003440a4410707010b0300f03100c21644414041d007100c04d00540c59840f0b070580030300700345124900c16450f204a000725846004000c481300c41e00c1480004000b070100c40b2844201259482d0080caa109424001007a01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 304615152 1250 304613902 304613917
    0x61b12030405010c020714100f12050108071805040f0206130305030c01060302010306150e060906070b0a020307110a0c09021804020d060f0b071a180a03090806070c020306071202 78
    0x2004084204001c01c041500040041180c9900b0b558400d83d41e800030325490112110080d174030a0a80d44080b024620034841c035140035101c0d2800c00140c9404c015880101d40c020b07000303051aa0410107040c8641340480030b005909260704c040c200203624040d152440381c4040380c9002445035030002400030113460400b9000000e5074022050700d9549070300503812802040b042c0700c2240424186600010175190400009152081030380750090110001c1e0200604c03644019840c42d4414400d02000c40070030612101c16100d4100c072400140e8070b051801d8083c00d40391400050004c154802d900c481d0026103005241c104445103508003603214200c820312010115407107064150014400720381c4681c0709900d43c010008494000e540c4090a5851b8110b85501d4800c444000d840f101d080703c0c03141403040d04680d01170350141074815903800104030348020303601f0300c1e90382030b416000620361400a002c5050309028058004c402d41c101f085c0c60200b40d9020a44030390004007102e01b03004920070070300d141000e40e070115201c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 304616402 1250 304615152 304615183
    0x60c0d0e0f0a11012a0c1512050604020f071202030409050c12010602030c0a1106130303050d0509030406171008070f0305071707120f02041a01030f0506061b 69
    0x1d40008440990340e80018072060320001041d25a07000194085c1e40c03120003e02d69191001c42c00a140039800000c900340c200c0856400720119000a030145201d258040c0c500b0f02a0749021203045a0041c0390306442c00500303040d214920400c02c4001c0361309200c0840d5100c66125182d800f103031082c0382c1d0590650040740d10135203180d410241001150705540340201325243c08851a6200783e600c03640100d82d40d015240031003555521000800b40840c04150090002040040c462840c0c07030303840f0b0703940c800d0300480394400c4000c02d1020403c84000050b501886070300498020045041901d490340c020400360b40d801600880307201440110703007080242c0320703000058010102150302e07160341d030600f14005d03410610054541d4000c000002c02e01d03954107200c5107140242400145410760500325840755040711000300311142e1a05009090068585015a02807032074041c403200d000f1080e040000d0190340610b0400740070070b4642800c01c100395403020256141040120076509840008580151a100361151101e80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 304617652 1250 304616402 304616413
    0xb0a120e10050103120207140f04090c080106180b0d0206030a0f05070f1107080d050a113007021f090e15010f02150a020a1202070c060f0c05060c0d0e 66
    0x991038082d800680c100c0b4407130114242c06107619030040f80c41300443d01a00d002c10940c511400c5040ca06039080e203242c20401840003031410030035a1034804800c4542e000c1051a5103866042088148045140310701403007003a0180311105504c0001000c042c82c0d52402031043c003002c4045a58154554410b65442c091144100100d050588024181c5940100500001507403a04c028245440124800307080361403500081800c01c18190040c0c0345030304001c091401300403649252007500c00080100c0c44009103925984900442d070000f034045014802400100d142c03e0030445800142c4800ea07148042c03020600d8417062800e000902280d0b41d42c4607a0025a684202c40144843e0740035018030074006103801d80756070170740050f4404140e07121141100c400a01c8550320001a4141469030020189014545003001c10200d41044400481c1c109250980d101e0300c807024180042500040c1880354a030b02814205811541a9038144e070b00c01c0000c24060070b01e08049103500c40c45280c0e4112040114441003079a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 304618902 1250 304617652 304617673
    0x40804031203090c1211040c020f07120b1006020d030903020c03010f1d060103081213290604150506090d0b041401140f0103140a02060d0213080102040b0a120e 70
    0x1400707040000000d458440e00d0500005d00d25968040c03034040c4075848005654080110310410000b0102c4081100c19409000e202218500d4203010400c003410144003900c4a02d05030b403c001c1020b190003024a6803002c04000c041c8000c607000034809861181d03518000c2075070369452604904202c0d071810703610b4142d030814480381241481c640290401007041580621540344d0541600c1c0d613440c080c400549810410000105c40c5000c15041a5121840340c40c50542d40569503181d581355190f40a081e115014507440c4d000c07946c5072903c0381581000301220240001134078100045920402803003030910030100011641043c4d02d030303c488040c0c260340004400760f042c80c1c241003045415604103040000c3d94a00543c0b181c825a03400b10090181c002040140b202c5da00350340d5840034a0900d16928200c03071203540308103001aa1024001c0442024503a8050f841c0d00341004000c52600c000d410004059005000034414801b0b0001034811100c0c803460302030707080c404a04050000b00a125080b140c3c3d40642414035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 304620152 1250 304618902 304618907
    0x105090a140c09010e040504030c0318080a200915060c070f06020d0813030905040e01090203060a0c0224070e01090b1306080c030f0c0904111902210a080408040312 72
    0x41003221002c0c1c03654406484880c040004642040720024045040729164201003833080004d0fa911700703040800c1c0c040440e2a01c019510300602d20101715081183c0b074226240604042d0100c0c00f8551080d02c00d0324035410304081c48130118030700b620014004c01c00440d150010503030401c8a08003c1449401c50980c0035200c1c10000e49403100380a80c07101140783c6801258508121440c01480c0076090754039403141d02e05000030480501007015124440d50341307800c0a00302580c1d0500006014100e113110000e03018071307500f101a040c401c41c1021854407058401000b142c00c1c030701c821055441005450301c5c05440f2103403c0161803030001900007020942011454900102e50420007405441198840c00d1a81d511020b041c00746201c102c0703041c1d455440d90404603030b00d6010500030b4030310490000c0c000300b40c022144032813412903080f01003900b42e01c10010740c09001c00c9806010103803542d6564009020704056000142046220f103e01c03850030801420002000d000300309050f1400f131540400108840c001d500c0c0c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 304621402 1250 304620152 304620157
    0x81e15010306080d0806040c0c1505180f030f030603070807030501201606110904020d0506100309080301030f0c051003050a0e0d0207031b03060e0318180105090a140c 73
    0x5103804a85040c001142e250700006100400e1485652070804541c0c3c4c40c0140300113084000304400600604c00300c4180000c5c80501444e82800300c0d290002101d180204c0c00400b480080501c80306c0c1500f141d0a515100c0384040300315100d0b4001441260341e6a1200307400729180000c43d51144505002e0300001204000040d00003850b01c0000110381c2c0001641400049000d2050820211228550030426400200704c4d8000502d9021040304190801400901007000d81c1c1c494801d10b8180c03036036602084600e240684404003080300529041000480030b6a80002610041c08058403603a0341001030340070459042d10344c03006417001130029010014801d102801a22064882c0140075003071216001d45010001100c05045250b540105030f928510384840041c100500700b84598562074040c08808129a030064000c20021030300296074804082402c49080c0341050181c600c20408410800c044c502c40401d420305403042100e1010f810b444a0101d100101091a8404112545202045074520a5402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 304622652 1250 304621402 304621441
    0x20a0e13140d0f03050403090905070c1401022d040b180f0f03120c030705010606050408060c041410030f0615110109080307180e010305071404020304020a0501081e 72
    0x50403a101003911940c1515040310814850020f2030036180d0070b2600d40719030856038000e402800e1070000652541e0610050720400c072000d034045203020402c013007001110b5038141c201c864131400031070801803100e07083c0c5640003c04424400c2a03400002c0c900d0a111018202d130010488402c40d1503544250244440e42c940b03c2190b49807003aa10407a0780055403c100c3c0000c1807000c0000c02408c0311550100141d440c680112040602ca4402032103920005202442440c020b0217250300c82c0c1e42c82d140340801203442c00311b00819200d10000207000070002c0301010510130305000c504840b051403071050a0821001407000c0c07504022507a0900d080021041d4a100c40001000196600c82645010b4085000e080c6c0e80c0c3c07c41c00130802d2030100000b5460500c5101e941040500e07000945841681e81c0110322064042a0015605900155800c025080f0b10801300170704048181d50640c110b01c0c0039000900000c19034407459060220207800105c007511041141005000300d0404400c19040c500040e040c0c4013520340c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 304623902 1250 304622652 304622663
    0x1009230f0301020c0c1c02120601140109180b040f0203040f060b060a08010312050715020309070f050105160606080a03030e06060301020c060103081c0606180e100e04020a0e13 77
    0x9001039505060007180c515152540041200c1d040c403d09000c0303000a1500b0402c88050314451080050f42c0c0e03280c03c0c004150f0544002e0045504003682c4000c005085003146060201e106c2d0104003030f140f00250000482e080d10030005840c0b0340d10307010402070030541c12085603040c4000100400c0124002170009114010300040116281c940c0c140041482817512844c0842d42a000400015806094a00706400b071032070924140f180030b548000c102c04039000200c0c14250084104032b85150100440002030080940b10540c0b103241000282c03151182c170448090103080c800c4a0310a2040c180c222070020305050003282d0310522641801802015131900030b0b6298005c08c000b044041c81d050081d5201010600081d003542c1c1d00e90b54036001298000385d03840d0509008814400701001d11b6215400042902d601d460142440400c5ca1007d086401c0c3c01001c0a0a01c0d801884000150540f0040030380d600a80108410b440314000242d1a0700c9990200082d00a40000c0111400040c5107000307216218a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 304625152 1250 304623902 304623919
    0x30f0305090115050d0623011e05061c06230102190209180f030d06080d080f0604020904180503091206010509040f2f10170402100923 59
    0x1190040c03d07203241c8a00d40b035000c461010180880d1401c101020a024450070300003480c0500d06461090202c3c021500e204409581c1004204a0010746090340d460002c020030710f90300c2400c11001811500580020344c1c41001c49030360f9401c1c031480b10350109018000d810703030f01c903040109007a04d00119012019100d0040c00380400c5110080e042254242d18154010002c0360f840c0c0e00e4181c00806841e0b0200642d00c0d0344248641014400c90503c002e01c40c0c4801c980011844034281003415150801240e41101009410000c002c4042c50030000141c020404440c0581e0324040c0e040043d0203041c07890b41d200d10f501e400921a5040040c0040103181810058501010345443c1c0005d080d2034003400d2186c203400c041c2d164000b8000810f08208081000c2c810812511070b0f042000034141401160500c201402d910004400d99525215410396048025490019014141c00070001c2000f880a04020b01800017415000195800303038003504040d010320030301c094028540240d800100c0810701052030050152 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 304626402 1250 304625152 304625161
    0x604152301090f060503040503120f010e01060c030206011a070203010213170a03021518060702070911041413090b07030c0315050609010e03030c0f0c040501060801120314040504050103030f0305 85
    0x12010b840c03c0301c4a000c8210440c03494104295010b82c401082156240420026004048440e036407060040f010b40c1c03070b407040a41c182110f2542c03403401038100d20240105800400700007540040c000c0c3c1900c050040c000300100260031086a64000c60000039031650001c55441e4010246034041d1044400ca510303409499000030102d1030719450020405001604002240019003e9942ea16504408034076000d00c44071650008042c02d040e0113171240801a04414002c015101d001c1c003404881015164007280340c01d01d0a40c056117002103608245006504001c0001e1388090641c3c440080700e5000740b460091850030082c005c00619a100703d200100e460800800b011088000301c003815900c0c0a003e0900c0d01c2d4900005468212415400991501c401c0100c9140c903081882902d40b940d13410401804c0c1b90385400b0030001543c02c160407600030011010300421010f02000541c1d00b802e601070401c00f103c220710140c4903c2c548141e410064101342004000010103521031504080c0d01903d9504102c940c48 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 304627652 1250 304626402 304626407
    0x2071505100614031b0d050601030b01030b1c1b030507080715080705090406050402040b0d0b0d0804180b0405070f1706030d110106030b0a02070b0a0b180604152301 72
    0x600d4010040003c9103d0040d20010154100540c1c00c081224440c0c4407080200d4a1252680c1c81207400341c0216441d282800320310758060003901030742c003824203040c046528140082a0040020145c161021048440c15414060104a280560f0842c3c0c901139003540c3e1641461a13645280303120b50300d654421040300042c11002c05180d034405130a542e40700002d07a20307042c0c02103610313811052700d4950059450100045580d0340b807009000401d05003140d10707141e81a10b1411301c125403185101d14000c00520a0340700000300a84120740565a03802010341d0304407440b40d015801800032408940c3c0042c64181800700d159040038003920440110b65803422084690900501810710a83e00c594040d84589480400c8501400560721603611b140000a10f0b00d5887d2152450300e101504e19111a035800614002405149800c450748003003a0f50041c485080c01d54081902c0802d40904000c0d440c220101040c420ba6841d0040766105004a04600616440d001241ea940003d00e00c0c0c80101c28111030718213103d50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 304628902 1250 304627652 304627681
    0xe010b090109110405010815030f010b010e03010212010603110409020a030f051608011505070816020a0509090c0d171b0105010501090302130207170705030d051b03161202071505 78
    0x1054064003d041c00d02d00700054551f41c03c0540f9111440e80540343c0e250480c1c90403c41001e40351111000482e030f070058a0000742980720820040d81c000d0340108820f050740c006024850b0304584651400140c0c3c0031040c5100c030000d0042d81c000000c65400001c9140a142d4981c00c00d4803098000781c410007141c2c550814800f900f00d600080003000c12550001000440c81400c0c0c030001e00328803401d20310714052480d03682c212280e00620445071100000c101c2d4509500b03000b404d5001038141514a10701504043c40e55a03a50300c207031a0034600c100035034111b440410400d041000c443c0c0c2401203180351520301e216044001103c0e9500116055840d203c0000b9040d0321a44080e81225000351605000581c3c1c000718202035440741500b614079025011410054814140051001e9406a00603544030740d0003a40c0c00b0190790f00540a01a070144003101585051894400c985d000551b030303004a54000d03680001524003070b0f80212070711560303440403608a040c006504156103c000c0903007410003045e81c3d40040101d010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 304630152 1250 304628902 304628921
    0x11b08010f060c20030c0310230c042102060a0806090f0c1204140a0311070915050103022d040f050d030206070815130e1603170702040209040e010b090109 68
    0x580038030013507071071000880050307100c0050306031042d104021001c64035082c0c85034581e100150341d40f20148481212000e42c4110441e03400000c90f0541040f8101084900542c000c1d01c6810b000c404000d01e0001c6001c0640d035400b9800b0b4181c54a61240060250694004403502c0380508042d0000a02210f40c01c0c0f0346a10400a107a000c50400c081a00c51144450b0018000c540c10281d440580089503010400200c031a44607640d010458071b2080c04d421304250a039031000242d241004040c501c80b16030039954030140c5800b882d0040c0c8582282c206443e0400c100180c140c1480300f206c1c00d0440301c3c500302c0014002d0b04c180380c42e0314900c2075031b403400e01104409036100500160020004140000d2152001c2508000b00c0050040881901c50018030040c0710312100e018000e90380d40c03044004010a105110b004440c0303043e40c00981d480c58031a1010800101e1582c44c44c4000003e801e821555103a054402510006e8130400c03106420000c10380c02488290107107881042ca0000003c3e08145501820801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 304631402 1250 304630152 304630163
    0x2030408070e012c130213050a09031d0108060d1b060206180a0c09051305030f070210030506010e01080702011e0f0b0307060504050f0a0503010c0c0b1f0e09011b08010f060c 76
    0x1565500007600c0451841c4000032640000d0f1fa15502c54483c0d4603004960150089080004080404d8500900b4a03008801c24000c6076402070b540d203040f683c0007009164410700584040542c2c1c0781d503207064003503003194280000062001d000c02150559002074030798800d01c055020190f1401d000f0405650390120000c005000140409041c0203581440c2c1101d904209044400e0395601d40b955a0741c0c0c210342040400355140400403401000350301c1c001520440c424401d040400040c140b0100003064003810614290500c030494001c074403014400d60001007100303d410503900080c00c1808158003c1d01d24140d10041c01401c100e180359a52a000c101001200c4c1d01d030f00c80360f01d403500d00024031104e00c0c1c071000321503031081d000da400180c962000e00035802d001c0301030740c0d920a0000880c036101c1c80268014106400115034155113561b862400c0740c2a40c151086000302c040907680c0c03021001e0141201e5441614014002100c6910040d041440300d03060721a0740004a00740d90315003004540f201c0381030070003505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 304632652 1250 304631402 304631489
    0x80a110306040e07050d03020a031701060e090c0c011404170306100e03010605150304061b0e0103022d0c0d080402010507080a02010f060803130e071e02030408070e01 73
    0x20381c1c2ca02648400c190b580380c07805413065943d480300014a001c0c408242500540c00100b2103038100759002d012440c10704850050350f145541404001001140020500790003641220f0101d85e4000d402400d4821418408000784182079088200002c1820103503000c0b40e0110025074103901c0709a0a4050701e101d0070340500401c1149159950032901004de03140219055540c3d400f020a098484000704d43c041950140129039a0800d45002000c13100d0b40315001320542c02072182c0202c060f5100305544d094003801d01e80940c4a01c4030944454001c56000100001a070001018600e500302003009001544102da041c0c3c2c084060304441a5200502294024006081003040c400081d071f0540c05001c000c1003d1000107119017096000e03604444407900101d0260384086456a0b85051240c201070141104001c804600e0400d0071002d00405400c1d10b050030079103036554080003154420130984000789a1002210b800517034950202607440d0080c0141004042951704d44421240c102c1d00305201608001c6200c035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 304633902 1250 304632652 304632661
    0x80604020a08220b0a090218040b0c1b07031212060b030a2c010f0e1902061c050c030105100804050a03080601030b0315100e01120204020a0e0d0506010501080a1103 72
    0x11200100401802d01e48003030403c14001065202049500c00d00d100b080026003e004c44c0100084030818500348031b1144800400c00c070018052005080c1c101061008517915640f4800c400c49020005d200d007019688980b600000c148402e00004040403405500e44849540601d40c0b00015152a070051f0040c3d214108049003080c0b4aa44c041c9044540010420505042891040b00d81710742c2140002080d079101c41d2801c0b02c0540b907105158040144c24000c0c8002c106083c0c0c60580211494400f0f4030401010540c1030b4034000f44c1c50603603048008850104124603201c0401842500700303000d89801008690284054180280b40250003550001c00400c0111a0b9650403544000c005043c00d0406413107280082a985040040d44403410036800f80c0700c864604110300c0f40001c600b81c0c4c014034140008200400c4040100c40f82e042e80e41d40c042d200582e450910080944218584520080e08100024a80d205010021440d103058607400d1340d5403d03854854515000641d411861284c034940c20800119 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 304635152 1250 304633902 304633921
    0x9010b07030507140a03021e030a09050d020d0b042901031a0402040b06070c1502121209160305030c0c27090c0306011e0801110d020717040801020703080604020a08 72
    0x814605100b00803013144500b12209090600d14090800c80c0075030300402c0c01d5408a5480310315581005514001181000604040106019000d208560080300c04580381015034480104070044c4640000a80d01d140c1403a103000c9071400c06085205104c0c0d020382040c0b541c046c12600d000b5041f0fa03000f1103564107038203084440b8190100040c20803030344595100d00303c0038551202c00262060303500856031812400d00d0800540c80680800c0e01070030854021504400040503c0002c1e12225040040c001d00190340340340300103280000b6140049a82d1014240c0001000b10000003031090001c01c1099030314410f12007082c8006116031f07844a1020251708003205540021004110354000301d1041102c0f06812500d003c2030904800382c00c0880099280e42041d440c1c1c0741c866030810000e0021100810a207815145021024040c4820140e50a500001c08070248010704801140d450084038640c0d90319a80c500c18a4000e62240404030702040601c00001c941d803605100b0345500c0a42da8444010682d00c01061 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 304636402 1250 304635152 304635157
    0x1020a030c03110c2107050901060504170c060f1908190e03040314030301030b0f0426090a15031104050a03030509060c10060e010801090c0614040b030c130509010b070305 75
    0x398001440303550340d110980c0c0e8601c46401c01c410030f080c2132845d50282c0c642c50075052030b20b150015401900041c00401400d039110040b601151400720302410203680042c803413400c2140e90300801e5480400410518540031800005007440488002402e61542c9448416583c0f0340c0202c40c1c81d04c440030314003e50420340f00380e60460524045903005691502d40c0360354038020700c41d49000c141642e0340d00208c010b02c00c02c100c6584440d000a40b402d440040d0b49000d03500c940040500342c10508045421792a440701c062290001d840c010880100100e80446c0c40b4007503200401d041e40070440c00039060812540305541a84211800d56601600fa0218607045880580d141c0d40030b00c001c150802010482e8045d202c50610140450f0000c2e0040810154544020307c3d50125040c0c02c28070301d9034581140c800c00907003c02e00e210300700e03904c6041c20101d412000da0342a01c68001d03907104000a100010400404401c448005c2880948420020250586590500c114044240200d0034006010010000401e005101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 304637652 1250 304636402 304636427
    0x60609011a07020a0e0412090b07150605130e160825030b010b040302010207060807051207050c07030c0e01080115030b06060f0403030c0209090105060a0b0304140d02030d060501020a030c03 83
    0x2101d07450056290301064640f24594172a18419081100b800200041e00284003483c00803490000384590034040c61802e6403140d003000501449110703030015041c59807034011100034000184059039800d80780000300e020740921746213044a0b004101940484150041150090b500c0300e0000b0982d2100c0703010210b81c0b8071110507020041001030900000090030a10040c1d010740401000745446914510001e403424003540c020000b40a100010000320300e0713100081c6c03003902d0214060490b0f40d807075014094813580704a0103c40800d0003100c00200a100c2c10541480880e002d2154107a4a681c0e2544806d00700e0743e0107640501c500c10040802c10100316007101d05034000400500d17140c03030a200003071498081d5002d980701314003050340301c1c0c180f005510b03200c81d5031540001500003e201c0e81c504140001d0312450903005071a026580400410107010350700e60705014080b03460040700d80c1ca412010020b9a290820b805a410f01e0303041400100c2e13154408140c12a2042d41510b40341031603c83ea60701239505811952 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 304638902 1250 304637652 304637699
    0x10206061f12062c0109020301050d0f0c03020603151f0933030b03010b041e020f07060f0504020a0807140d05010f0c050405010315080618032209060806060901 70
    0x10001c00e150040c004e2109024545800284410a0074025030440d64016440b1004903032060004101541b100300c119090301e075104c00d240c0e801007040d26103401c1c05100c5410183d00302c4808010407500c1c444c0f03040c030046c00f502c0c12500265405c080c000e0305480110070103040000075000030800c2050b408555806160303e0025802c0307412011407610104030241c82000ca900001751104000d42d5141028070a90702010425241807100138144410100c12903010340159413901d500052210320550030000b03540040781e1141e020301609a5031641c03c40035203001d80d4187c1c4106602e0030002420880068003000f03c0e000140300310107419600b000c210f00071185210a84540d501e800c8100310141c168495107200c0860741d2603842e00d460030f00d0001000c407005058003604140341c2032003e01040d072002880d107921041012640d84101901000c3f01d085005181070850480c52030445000d00c820110a075078240c4009002c00c124003a5600e150503501c1c101680d403103400101e06001880b00d10044c06004060580b0b51 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 304640152 1250 304638902 304638911
    0x7060b010212160303051302010903120302071b0911030f060d0f0f12020105070203040602061609120c05100503010e0f0c1b01050103140a03090626070806010206061f12 74
    0x150380420540c0c446030f03402001015086141c01010b4252154580020380e804007012055401e60000c0c11040031404040e01c1074042c040480d084a2003034040343c1e002d0b6840701034041c40119400e07611700089014000c00c6041410540403100403101c1c00140c0f8410382c48000c3e00345660701c600092029030010741409561400c40c5035080b0000c561100050151a403242642401710b5090354002421584060990700454004000420849a00060054000d0340300b0b09000d42d84c01e900c0c0021303035110001c0e5018038181c0703074251100c4050045682c450406c03108180d9284c0141c0900b6101140e02e48000d014034400e00c81d20354041480d140900441a600180207006c0600d40300d203c6542c184072072584816020a40e4540c4014010049021141083d0f01a43c80082074010050f5030068441c801e14003c4008000d503a4a602206040001d0f0802d000f40300340214011604004100400c41e0404407020380c05480340f1401b043d1641170102010084510740354003419201e80307007001104c2c540c03075549000c140e040d202d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 304641402 1250 304640152 304640173
    0x1416090605150717072103050114010518030a1a150a0b040e042d020a170d1101021c0b0414090718021201150906020f0c0409030201090f03030506120f0307060b0102 72
    0x102c40c206c1c1004407030319000002c0d1078055040201a2401600b2038451040c40b003158138000d9030000143d6007181c15400304492040c8160303011a1030603c0e0004007400308840645071007089581504d805000d10280020066801c06c2d20062200040c0701d445842e40a4404110800002c80c95045e406d8006200d850740308003101c91005200381c056000e14401d070f120f01600303018804502d0008000c600034156503040344882801801482e4441010200020602c1080314949618003020350484e03c4281e040b0170300c0042031851402401c018903400b408a0301851403e0404131428503100c25213446006450028241c1c1410240440036520300700d000311900607000c1c000c00c803006c035555100e540a8040c0c6c0d420907a00c80740b100802080e009881d4440415504805e203402080b4901003144c41803000305039004280e0500b00e01e012801840c032104003501100380c6401c10b00400d54550411030140e02e007103030000c0c4442e10911905844030700325000d0242681c0104820b900141540d0480300c00d4000c140180ca103120b89 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 304642652 1250 304641402 304641413
    0x90209010302130e06030d1106060f1801091a1816050c011a1521100b0309011508030901120906110c01022205090a09141609060515071707 61
    0x8144c129621002d141c0080001c903080030045250300c0f90540c50100070754048011060340b11800900054002e40c0004003c10f000e494981002c030000b000311100014641c0d40d408004010181c080703603680781300c0d110442e07580103280c10921801e42802c02a1a4115921703210f9a01440c0f0107031074003800a10900b44244d4040c04821f10400074400780417141c402d4100104010458600740b00c1151030700618041c08888280d40ca00d004070b4a440144000014923600d0381075580c0c41507005e90703110000101d00042040300700c09064120030707966842500307543c070360b40d460341907054403400b803d46c07014009510061015030b42a03181d0000d4640314087c2000090743c0c4442e0b034202d03a40f58401d00c08142969000540700c4104543c80004d40070441e80c6003070003491507007010002070050300b014001c20143c5484406803c02d01245d201003a480030201c004550803810960010510b119507071040c23000503880c0c0040014541081c505207100d124004600d00e29041055407a42c041244801c0e130000e9038042030048000181 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 304643902 1250 304642652 304642687
    0x10201061505030109060b07050307080d0f0903170108030a0f030504060e0a03050a0905030c010507141e070509010e0c0403020d051005010b43020f1003020408070b070c090209010302 80
    0x104075580303079503481d0305040c084010340d60039034070281000a0410030040410004416564070300d0380000c40d565190355481b2060f0103801000246801c46180aa40504064021940303480c42940f80c80002c29036aa80c00040d5240d0003a00b0222003ca401841c0c95090184aa80499405845503000145140416240d68a0003003080c2c1d0880220740c000509081841c9c00840c02c100500c0c00320000d03d4034018420009100d8062107000611403001a40171411401080c4030510304503a600c0380c41a82d446210144543d40e840a10400d401149a040003107003801c01c000140f0320848210b00a00e24152450342408101074a002c4195198003805204c071250301e0807030140a008240c90814507441d21941d00d03103001c01d440340741882c0c05400c0c61103140024030007002800030400d0780a9580c03101e100440b0700100d0304c407081e551102d9038000c4081c1c00c840380254159010f44290f500510480e019a500d4510110151081a8028101000b521002c10503480036400130030201c80185005410082100320000107070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 304645152 1250 304643902 304643939
    0x91002070317031f03050a02060315130f0b09060f01050c0a05030301090507110303040c0e0604020702130f050708040f081305120d020c03011404060e120c070501020d0e1e01020106 79
    0x140000140000c0c2440d4060316103018584c2009030103494610f5546070303600d044d0218000d002d07074008070001390400000110340700a10400f40c20714041080b44060b52004007003242c9044892460701d06468158104039203401d01c20303140605506160446c003030054440350003150050070a48900c0b440680007980520165000b4400041d002c1610b09140c000a4001c2c0402c081c541110f038024004c00010079041c1403840d007290807244903000310b5119100420003070311035040b0107900003c50b9044d83d14902c0003940504259a10a401001a41c0340e00304101c410b11415500544441c1c0d0070b43da0718000c1000e4000904842802d60400c4048542e140c01242204000960004c07694014400c0788010070b07014040d1107101ca030f00310001c10020020030000b0b1000351019201400156841c0e9019000c82010003110b0701d81100c0d1240b490b260485030140d2580c1c3d050600030103005000e031032408541e460044968044480303008100325100004c1c0d02240e030000c1c0405005904545d210040041c01b0f070700304820300181 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 304646402 1250 304645152 304645193
    0x50607060207020d031728150f1211040c05070b0603030403020909150708010f14060c030708030a0c020106240c0b01120302010e06011a070305120a0204031401110910020703 76
    0xc00c81140c9007000384801c001d040d405140c2a0903005000e03440f01010010302c4900009001540d049034007110012320340141c0141003101101da0020680c02a9070700e0702c0d40c8461041c070381140c00304000020b000039200841144c501003502400040300140150002d16403240d8040c0403282007640da90005400c1349029140c03031140380c1007484411015001641e0342503020015081005103549040b0f83c000c580c0750380e40300f181d0b158000d110080361540e4440c0c0481301d14401d02000c032038445010f030a03d1a1507a00903a41d969090785000300d40d585090042c01004100c0b004201c0c4007140c1c000c5241001c0750384510007441c070208a84111030704001140102620b02038500901d41500846e490710b030107800c6503001c1e03110500d141e0041c40100250414410a80c80040c4e5021145840b86e80602e004e4070b00b0300601a4030480c81d0542c4e4108000b100e081e42c003410440c0c0c064150440746090442e81c041c2200e000e103600c20307204182081129903d041190f40b05180c4941403045445c21940c81c0c0764060300d210f8203044c8006 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 304647652 1250 304646402 304646417
    0x902030703140c01180506070303020d020f030717270c0306010303020303090f1b10120504121205040b0c090105160b01081608061f05041e0f02040f050607060207020d03 74
    0xea250800400108080a0a00d4070700c54803107420070001c0704070f91b1003030b5840b1382c500044050415100c1d4064400600c0e00c004195100c1052032880a11500201c0d182c800007078902c020940c01c992000700141c010510225414803825410418550131210b0345152181c600ca00d25090905450410a0754000d5000707030b02454890808601071405e00d0301d02081440c41d0740c000c600340728208000d018a074010400c1150030038140181403500359581558003000103141c81c0b03024204020b2110314100190300342c2540c2d075002000001c0c4034000702183e0080e140680038140b460002110851414014244800f05041442c00d000c404102d01d2161044100115034a035820401001070100411840d100303603005159290403e801d143c07109548030f00041c909002e00c28203482490308c8626075170b865809401c0191007031203c0741d485034030b100742d020222100c0020341c1e2514000303040e1481c075032090380d00b5100d0b403204182001c5c1c50322003041002e400c850800c0d02c8081c0c4c00c200d0a80140d82d100da4690829100351580b08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 304648902 1250 304647652 304647683
    0x112020a051c0228181503050705150c030304060c0e030307150605030f0a0602130e010b1308030a0c02090a2c0c010503040c09091a0910050c090d0f060902030703 71
    0x1000705094003042008605030b0035005104182c81351401551601c0010003610120721030f104000d0007040000240c401041074012042c84800b16240080c0d40050310030050040c411300e40c04410b4810245030507210303081071000c81c002502607044485550b01c01d1510468200108000a007035078440307a03040300c034142c0300200d059400c5001c0c0240030060000b20090a010550502a140c60ba1200b03d001002c00d6400100007415502d2610504003034114841866042d6841e0007140c11183d110544c2070b84a1600f104000404010000448803000290b40d140101c1e0f9a01d0350034000b1101c000380030100e036a91504019140d414002080c0d010083c41c0031107401c2d00002c440805800e01400582c8241004402c008200c0492000c10f0548200d440894000130b80c803205042c444480e040e0300d804441c04042d1441845a61344000901c0f00c80351000b00010011615202800c0c1c420f4840c00311420340190b010201c0c000420b9100c1c424202d1140910004100c5004c1130b40000d0412140da0012204007440c040f014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 304650152 1250 304648902 304648909
    0x50106050901021b03060c3403081305100c0314090312010e06011709190302160608160f12020a0f3c020c0402070f05060c070b0112020a051c02 63
    0x1a0400c50107040801100301040042611070b44010000c0e482c1da01d002903040080822311602098800d40510b0380720004540f005161030a0345804800e070002000320b004503843c0f81c0600408031003141e102000b800400c490507000f078080d11074402e01e074051559440402171100742c040c040c14411454500a1a035410908400b0f4040c1c20041c4c00110070740201c2e40802c01c00c2e907040250003d24207081c0403009507558480f0307221450024014801040c1a840707095240c205600011040008480c03030300b0740401c0c4ca466010407207044c44100c0d01148070b210380406c00c1c00224000c10003d8181030144c6044618a0400d0035004280e900c03080441e0f00151420404403242e650041d00c00d03040705075036119600d0306107031008170b8020384104955903d6a0110780c0301d216984e0703008010a5081c00006442551100400d04201250340410310091b0b510340150f900090780300d28014122501c050b444181c09000d0303420070036081d2180030514422a08035a00d590085241d0740c45c01d402030000064030103800819003452051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 304651402 1250 304650152 304650163
    0x201020f060c0a0e1f0e030601050409021e03010b030d080f06100c03030522050102030402040606020c100305040221030c10110d0207020409020406080604060c02071406160605010605090102 83
    0x189262a040801480b80021025040707070b10810191803d04030885034603002800c01141c2c00031148104900254200e4500d410010320051050202d01b601c40e140e84c1d910a00c02940e4107484000c0d8005070841c5120007440c07049842c2c0301d811030050000101c1d0920000400d140c000700001e8207001c54580e1040107040c0040c00103155000d101924218580c2ca01d002010b4080611060b00070107168583c4005101c3c80020301c9070b0400c40c2082ca00e000f1140501c0c1c10f02078002c0d4003d41d000d038000c0b4103000c808200140000340076000b9523009005c0343c03082542c00c20110000c01d07000c1c10885e44918420402d200000e90742d40711300b8030416004041e5650b020411030003442d215130f44614840803810038400c2491084510300303440d1541c60340340e03015907609400d10000d001083c0c001c00003540303e8909180452003050014500d441103109000400081942c0c81090ba0b0f6400c245c8100071001e0240b4960208030300b484009000d000b401540018150f00b80c0741d49030401e8a009820900c0051400b2950a18642c3e04014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 304652652 1250 304651402 304651423
    0x604180f0b0a0e15090709060311030f0112060209030a11120c2b0501020f12070908060c07030c05011b090e090c1207090c030c03060b0313060b040608070b07020102 72
    0x401c000000d80503010070307905070301441088207400b502c1d000624101840050480c0b0074100402a00351031070000006002c1002d1409000d000910303105003001400c0c118011280104e0710060002c040e80c0c43e0105109141e940390008444845d002c2c480003e15450400048945074440c1110303d1584010f0f1b420b108000b0490a051003082c0d1000400310b0064950b00e84415038200e100f200d01c5030240c0300310036044803807001010041066100040f41d011540110014150004501c02040880d444002c01101d10703094030f00a8400980050b00442c1c5803c0c01403000781116403003800e24000ea28200d4580c0350031203104102d5080e8030200224003480302503000c140400944000c4210705d00f5400c0140c0601d5071645050308031400741e451410f142c7e02841040100f40000d021945017031096201d242c100401038445ea01402022a0403da400719401c990401628800d040c001c1b0ba580d0060140d07224100070b050316601060300255949008550850280130b80c07400391810141259942046100092901481f0f05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 304653902 1250 304652652 304652681
    0xd02180f011e0305130507090504170301140402031e090d120e060f0c0705030307030c02070909021c020418050a051c1d13020a120c020c21010605060418 67
    0x204024202511400d03019100c2000e8a0b000407641c0e02e1948102c5100c1542e000079210781f00d120720024804c001c640015120b5403140301c000f40d8202060072a120b99000030b014034000704044410b0601c450409070b0142d0b50100c8406600c095504450f0a0515251000d6400c50225005940855403280d0010142000c41c20007500c200003050005c4c400903100c00300500a8a581c00f1100c000c2103d0a2181c03050700c00954001c4243c0c1d5a904004501034010226001520094007414200141c001c242c3c0c0703d81c00d241600070b40880c1c2000460640700328000311510003240c7c059030b1441c050121401c81c00d15480c07140d00c54402010542420708001d072030300c0b400302101c0d180d60b0040404c2200041e8021a0080504080001020111401000210600350303a040c020f10503840814000d82c2541e019082203030506442d08200b064000004003261203801071140d00740c10800300100084016a58a138038035000b8001780000403429202c400150941c1d00642c88602d0f503008014000c6030702c5046204980354400d045 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 304655152 1250 304653902 304653917
    0x218010b1b0c030d0f2703030302090d050d02010b090a090f03050c0a08030a06170703080a0e0103150e0414061003060c020c1008100b0418110d02180f01 67
    0x90380408688181c58020101d4281208240c15840d030401c42e95144803001000e803001c4d200c2d1000000c228500b071074000800104803883c0031500c58000401040c40c844000c800308401810b607142a0301960000002c0c41c0c103e48004030407400714905100e240399000c41940003249a01c0c02030100008088050441242940350011910010365072004001003103905050807901d4001d90001303581072113400e07a07010304001030020400442c095250302c000c09403010481c00114076080d010155a4602c1a800028503c200c10440780c0d0319180038085580d40e0308030514010807101012088000f000080d07600c0304024080c00d00903c400c008401c288091200c04110013003429107403ca201e27500201c520710024054950715446610301510901084019500103400703c040851510801172a00c14212030f9592001007841021800c0004282101d04507030fa055040f000705040c3e503007030350010701301255000001030080191070302c0d5051a0014201d10104440c0350042054020140960400719550b42030400600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 304656402 1250 304655152 304655159
    0x324071103031329150a0e0709030b2d0106020d0f0203030c250f0b0601020a02030a021009080f010b040c05270303040b1b10050f2d090a021801 63
    0x41c3d4080c1d42280360000c3c0c2509042c01c4584500c0d059000104101c100d00c3c0f45032041081c105004440d0441244c026138211a406036208102c18038004141c40b0345002800000c07040011801c000600ba4108091580000c56040740355034480000940c0c0b90f1441e0282081c10042240d207070180451000306890303003003114554946900083d200d100040c0a03413601580131440408104003156003103117a449486e6814062107141c1803030b40306900c64500c1150325070041720024945510109100041c5079020780105200c400a40c2082110520303030322144104202070400040b802001c01440c41a1610074000062801e00c100074001075802490f05034061000800000062072401d4003400b0310300b8400303040101d14a40c0d40d07000074250710480e0710007200000e02060100749247c00c4001803101302e80765000c4420614420b86101d00352141280c07000c03c1c0c101d546000071101000b0070f0407100100703402401d04a00f180320070403031514140305968240745944140b64440860600525001d0072141940040b03046602d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 304657652 1250 304656402 304656421
    0x1209051b0306100b1305130e0c0103020c070303081e010e040308090604030f05031003150c08100b07032106030305040302100e03030a0509010903020301050112050d2c032407110303 79
    0x5224a060070342000485c07801041050101802820b0300500d00c2096200004110002d009548c000a0050040b2400c0c80d1056020380300321040000c8840151034001d15640301540d00b814014009070040003203040348442d04d0940310300c1601902c0034250130034803400c1c141802004060300800c1e001c001e034410824000800d800019030200349040c0d00c0e207680e6983d90191000f411030070303d52006101d004c1c0000560921501b98011184420f071300c1d518100107544d40c00d4140390000d00c40c410121190002c000d10800b00e4410b110022525135406080d001c01910441f00340700700c0d0070741da00a40000b0b102240034000c515040394005510074103442c00c01c0b085040640000c0d203c7c40b03880b03a02401c0c8480010598101d03402038000c24000c0d60024020081580d590000c0d0440c0c49003100c00715400e00503c1d035021031f17071303400340600303801a42c8125078003801e48040c642d10301c108420078180b6035414801d0b045035041d1500d40c403140302c2203010100c2d409801801d00135805000000750312005032964000b4403c0080848 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 304658902 1250 304657652 304657681
    0x912030209090f1e07080603210406050f070803040602120603010c1d03010617010c0f0212030a0908040305010f0b030705030f0a0204091103100213060c20011209051b0306 75
    0x210791480c0a05180c89040c1c200d84d48610342d1503105000c040764000c101080d5005a40d15128001c1501034030408204031409104101d8800c40100322641c0030f120074400c072032140007d8900114010402468252281c41e1014a5042100d040325000c0d000901924400c2500071260782006c41940207005100089001511121448509551aa40e40312500342c0d2a82e007500712030010034102100303041160107135100300c1c00f803e4840040b4011071080c1d05d4070002e442c4000b41c960b0344040c0030200346096481c1c00c40004040c100011080d00d611305c05020200c0072a03002e104880810b0240c400000d40741170f04505043c14200240c0c8154440c1d041075074412020a404107643c00d203654100d03000518102e203072a264194444aa44140c0c0502c20b400b9110340e50041a8000c00268542456000c001a0f4030071040350348075104000108190040f400e41c5e0045051544240d0b41000c050404040500c050b0f083c00040361000c1303100382c031140d22190341c00d142081c1043c07181060810503409001d2500d8034510250002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 304660152 1250 304658902 304658911
    0x50613030c0f120f1e032a0503121e010608040204050604060501090e19060e09102a0c0605100e010e010605120403020a02091014030c0a15090513091203020909 70
    0x30240344200801301030a1361003c41610188401c0e0010350030000d14040f0441084000000c2c0a42071581d6440010030940109a200c0011841c00100c4041d480700c0c01809440b90440051300103141192f0f108500145003e8a0290740b006403901d4940100b00130758001400040c0903510b084010b21183c0d03803000400381a0342001c440c4048945039100301c0400d80c08001035448007d86891310100e040d017180e40c0c465004001142c01c64544090428103042260201d07611000040482c1122452441e000c81e07020003510100d09200c40c4901d0191601400e4440c112848400880b00e41340511580710310080b82d80c05003513600112403480d814500c001e001442010741e0392600d84200310005081510804c420341040c0e81c00780c844845402c081d20347c001100030034011080000d5800c58082914203002501920120004100710780b0545041c03403241020840301d40c0e1804010b00960003090715200e500b41c50700402c140c0b40002681007545c1c24120644000300504008240c01040901c1d503503914552f026410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 304661402 1250 304660152 304660163
    0x100309030c02092d24190905060307060216050603190e030d0c0206090a1b12050703030305070c0f0602091201091406160c080a0207050613030c0f12 65
    0x16a5060405581044001e03100960203101c0c54100801441c40035091034140c01110a1940a08103540d480c8042d010121601070040400c0310016800205010601100d60000381400070003080340c1440c8441103006400c5480507a4960060040604041201d6070082c000e40c8054220b04646014111038101e00748a424400c0c1e2012012035125030361201860442140f17800704010100c4141141500c940040c0c0035190401e140c01801e105141c004559a8480c642c0940645041a400c2e034640000c04400ea030800700d1051990008a040003101c0014408a4012001021150b00c0c0d0b14004003926401403403072013003207900c0c1c6620340000c8595114080d0240d00c00400740e16882c0100c04a00c0c800c003415030241e269828003611070b090088c4440c5004180300460151000c40d594031410002281e820400900090f4408402da0046800003000d450700b04110301c1524492990ba20020710142c200e03c00c4281c11008800e0100200a50404e100004080705404410100d00e00340c1a20212000311501509 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 304662652 1250 304661402 304661411
    0x20c040c0908070905011e0302030c040c0e150c010507090e0703020f0f0d1a0402190e040b030303071e0305060f0f01210b0901050906060a0c080906040b180d021003 72
    0x40325405080d205000d841d003041112012640c0760401d50141600788101c0c600a2001007c1c440c0b42c002e000c50034030a8a40250091624658032070600008005503002d80f4100040c0c0714184031241d031102c540184000d044004661110850f000036421207401030401004d001e1103180410410324180303245c55000d03840c0c0c1030040e1910f08131079a2100512605100744640c0c40d00140b83c0c001444964005241031005001010391403d99070180400c91003001a1011908004a4120105403250715102c12811002d000450000c12541c0400e25540007a90040042039811100c1d0f40c2100c4803c1001d2829022443c0501145c20020082100b540500b04001e0190f1440c41c0b4001690340207400d1034420442111030b40d80c41d12219803900b00280181d940c000e1243d031104000050900e040b20409004803001820b161901070b8018003501c0011075450102d40c2e240c1d090010b1a0b081ea50400600020a1461459540c070040000c26504400303ca410f1207100e04d898280d400d0150b04d40e81e02d000e0101090b81030004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 304663902 1250 304662652 304662671
    0x11523180c13061101140601050d020705070b0406030509060907060c080a020c090c091311030a0209180a0603060e06091e0304080106030f05070b0c0309010e01030f0e010606110d020c04 81
    0x8092103500e1601e40c00c0d41c1d24802c000780550f4024104ca11924804000b040f02e18442108084800390594041c2c1c0061b0b0140103600000c02c0540c01403440c1d510403030864131001d6950304500c40c1600f00743d0104000c683c5d140100802032034140721240d40800040058102103044c05009010010042c8010300703503041c041020402c4034003c2058880c08207008052503420300d021090060182d2169a001d801480c40401c00b51250f071043c0180001e243d0701e442a0b42c00c596858200c003009400003100282d00c170844d80140e96070401c81c0c0807224000d00586c0c8020507007e0071800c18030705a40920048004c3e0303610500030001500b10100319800001100c0c84584d140405036543c6502e10300071a005043d15510b4000000b0812800400052469100340c0580b0f02e40399450700340320320314000d504010802e500200010321880d88920711184134198141800606842a1900c25045410710072a20725940e6640b08144186500039200c04101c0d88210002c1100c64956070f0002c0d102d0211104d014000c4d0307190081b05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 304665152 1250 304663902 304663921
    0x10306090905060402153c070305030f060d08091e0303040608040506060a08030f1318020304050606030c030c091308031f060306142101152318 63
    0x800510500606225030806402c00715200d00d4107603402c91007030354a4400c45140000280c180e48107822010101c503100d0101c840c008680f441e0650054007510a50440807d10700034000241c03c0c5079000783d413070035107c1c50b020005024040f800341682d40704410318403080001541060817a078104100b0b0b9030700110f903800400d0018a1803030a03403919034075000204000c00c50780c0e4020303491440390340200300700c0d841c94880c2c0080c04034800907402204450340082000030617881d0303078034010718200305010000044a03a07a01c04070300d85101d440d0300c0e941c41710390000248002c0c407404104e461342242d001c8025069041d2000b0010740d840c2941c58200c2d0040c441c003030004040180c91542d14051f281c0009440307580c3d01e00803081e24200d25143c0700709a128181c100300801d00921901c034400a64036000003450b000d0020784100720030b000541d9401c0a4084100200b000511030038061102090070301380032008030508010031b000c81d1040c1070340d9007064442d09224403003140e62050801c0030389400185520042e80c5454004c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 304666402 1250 304665152 304665161
    0x281a04090f051c0315050108042a0f06020f01050c1605030403020d060b0102060c03160305150d08130b03190c0512100e01050103091101030203090a021302040f0f080d0e0103 76
    0x500300e80260a089403410011101c0309030f41426aa0741000411148000e180c0d46400c1806043d00084d003003000213002420400200180000c104499402c00c3d08401692558011940200840910066082181a0b0100100c840d0101d0001c020310140c605221546c00500524000d40a220384c040400d1090200134001c80d0040c6401400c0d102441402c1d0030007801810345072040c240144242c60005110104040030f8a000304078180c401821400905821409000085e02207034105d000040c040c40075584015030b42c10000d00c250841d644812522480704114101a440080700c40010010804034084220310b001013a8030314080003504040040046401e801081d50203146000f80c01c050010500c1d407100e82000f00c441d01c510880281ea210b0004605803605100028060510050155815802a0051a0b00c01c101c0c504480b80c0907101e800003002401d4625898250715070000d0248038081c025170b03a440281000d403008140322854003075090794880549960303c0c2000722400e074004150384280c11 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 304667652 1250 304666402 304666433
    0x516020f0a080a1a0609070f0f1b0c0305190c0e041106040b0309011a010e0f010e0d080d0c020a0308040b060a03080307021c08010f0e0c12281a0409 65
    0x44941d404100d184ca80d25001400c040b090301840118000342c481d240c4074400600c2688640d85281c882004008141d403200d0030a10b1100600c004003c41d00220761804441c90090b90103401e03102415443c40c204070703061241003448a40da086541400b8404600c4985444040398240001c0d0543c5541c0c80c02c14940354218503000301d501030350000d00044c54800c1000514020100134002b04141c6024030071240c01150740210b801e01003020b0000d00354030b07480c2c031280c036442c600010b040c50001c101c01c070720026846e10213040080384c0400d00131030140f2038403080384981d5540c81da06000802d600e203c940c4002e89040c4005100405404040c40010b00c3c544a150380c02c80119804441c003034490502607406512940050554008102c1204483c02c440b8480c580e110f0407507541031840340b0180d090200105071801c0042c60070b03da100c0204204010442c0350161680714581031620f0f6484119076041d410107a00b40080001035541c24411482e44110320360b400b000e1258801c0ba40042c003c1e00300d05c0c11086101300d054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 304668902 1250 304667652 304667669
    0x50f1b06040309080114070c060c020709050703060305010e06090a15020f07030c0308150a150c050a03090807080303011503021602030f030d0b0d1109130c06090905070516020f0a 78
    0xa007071004242d0404145820f40365004002d100b03c003000c0c42c6841d2008002c41d0f0800001d41801c00c1c21004c10350076803103803202d20604d105480c080f64448021806a0313a060710504002a5581e00030414020288500444410164050b0000b41401030941c0d0740d524203030f00f01a1000f2141c2403c1070644045604548212a124115a03122803d42c207001e8249280c035901500414901c4001600c003a070080c2c00e84805100003801030441900f007500ca102c240c060a088801403101a400c2040452300402512a940d8420baa401c00464204000c107070802d045507100c80d42d59031007840148400e6451000300082254186001a00c80000031003560b003160404802030740500800c085601400e0b00030008005102c3c540344e040c042910020248801007502480c0038100040031020002070349000003505400054441c030303a0440c809292624403070340c40968420804628605030403c49501c1d01c0c010254091070904140e800e203205420b014030f48450134500240316000c03465001049984100c01c0350003421040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 304670152 1250 304668902 304668913
    0xd020c281101020105060d0b060d0c0b0904060e130f0f060c0207060305071407061d03180108100806040b0403090b0c03071103010605030307080309011103040b0f06040507050f1b 78
    0x200c0900d40806000a42a00c00482200000c80e0315401400303450701a03400504508501c441c2500e81c111280e60182542d81d02c803005080e1907002c0307840009440041c0518a8590341d079003c1e0101040120742203079002c0e44d07804419104000c0100940f1550110503500030070724001401071440c1905407801c11120081819241c03070403400d070496000070303a03406480c81d0703403001c01182d110a50140c8040c60901a00c015042c401c200d113200140c0720fa00f00c98081110240e141608140b0060054219041502034010f4031a204220000c00e40e4072540203a000003c203800f080801c0d0808400645404c8010800303410408100003140815105143e09001400000301c0d4944030103020380c0c7d45890f540311040640345640501c030a046ca61a0601c507141c11a5001070056140c224690756030102500010600005d9550301c030100910324080c0001540f1540c400e604003812840c0c0b25812440b091005844107010380d19180130000745e6901701040b640c0407008988059210030b410380411002c0203500c0c540c2d02060150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 304671402 1250 304670152 304670203
    0x50a02060a050c010c09050604090b0a030519110f060301060e0f0a08011a06030c1c0b040606050d050a05010e01060c02120f0303090601140109090b040b030d110c0303040b0d020c 78
    0x100140000070103d1000b4808010406812a151980e41c080c0c190b11202c100300c1003110b20312035842401c6055002d055175456a5681c1c071090b05180c011641c414001c00402202420007002814050303074800b04944c1c401c402c80203180400c0042c041401145e0621610380b20f010426a101404000c80b8840104408c4800d5202c1904901801440c9500c0c0f51001c006aa032401e50310705142a41c0c03013600c90308100ea050021529185e8041701658040596881e9201c2d10100d02c0e031640c1c0180c5000d0200c1e40c450070782c4c49240f0064030040ba04024840001c0500e0b01e801032103042407190000d41120510715000101e02c8150000415850307070f41c8491001c611803400c088200020200c081c612691100c1305450040c0e9071585850303209400d80c0d504500189050b01c0601c0700700c20300e9100000c20300000d040060560300001c08039160903222550340d80402e01c540c00680448408002034a5022415000b450801d450583c3c505480d01903106200c3e50540c01160402c0c24040c10007083c43c1a017078198540409641 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 304672652 1250 304671402 304671407
    0x417160807090e03120f0c0706020a03021201050d0c0501080714040f050103110c071214300a121113030809010201050a060819110a030602040509070e0a0b0304050a02060a 75
    0x40784103454180d4248003c0040400c008025030304d6451400361000c14a80d510150310341d000708001d1070300750f401e2000d000c43c40202d0f0081c0702800f109091038400507038980b0346a68074504080c05030301c068858417412030ba9000046e00c0c3c0800134210b400a0070000d2554469241c02e451030440a00e81d101c68000124000840402050002c005c54000f030320108000e1018207490290341c0f0505010070540d9002d40000c000e008001d200459805000ea04400b181d4605d101c2084c0c100305e0892581120840321528020300d1280d40000010301e03840040e00a0320381201c905018207842400ea490300e90072982e4800b541d04505032081141c01802a03503d2070951142c49250500b410740054840301e005610740300c00190982c42030700c01c00341510300e10300050040003074030b105403038802c080341d14200c902440044d860080c6813600c41d0404081c1d4403440c0050385807030811082c44540308004040c5030812181c0030f40c6902c00c0e00d40e02d40000c2601c1400551555035502d40c20241e00c1c00402c5a4000c1d00070760005940a482903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 304673902 1250 304672652 304672663
    0x240603130b060f040c02030d060518070c050307120206060f031c1407020a030f060509010213031203271505062b08070b040b0f0405061302010c0f060914070b04171608 73
    0x880000e01002769070b880d01c050081407104800c0c40d00c2e50100f40c03c04520014003030240741e60010300c16021a40b400a99030b40f168110381c020002540940d001506000141c42c1c44a50028403a00c20b60040043c031301015804001ca010b0000c01d170b4144010b8000e00300e003080703030401207c0645402034603041c805540c0b032600700308084982505407205803030f04012032a0b4030018002c03212075201d80311460303021900b10b468181008001803c4001410394658003410703c04274018100d2102c101440c000b105081207410030343d0703a2008024076600e1a83ca0031007044400d0384d4140c0d2401481d85480c0d107210750501e0550b5004600343d4081d4001c1d15949003c80d0420800c0340d0400303958401c0703204541200301c0e901c500001c4602801c1c1682c0040c4260001000507450940780d0340f0781400c40d801494840305009880c1ca030182102c06220050b1112501c461804043c84490800d154400d10b0b00c0c1c0041c180240f07040300b010301500071030044c155468442825802c4481080020081e64820f44144d031107829903c440d0b441e80c2c1e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 304675152 1250 304673902 304673917
    0xe0702031b070f060e040f0e060603010b0d020d080a12060b091c05120d02090a03050a0203010605010c030203030a0f06171005101406030717240603130b060f040c0203 73
    0x44907029a00041400089144403c407002907840c2c030000c41c1442c07030585824000d05002900507564111041c4800c610780601c0207107541810244c0301506081c0285030940310101c0300d02d4002c0003800480c500584840b481c0c894100c0d0001150f03920384a440001710355014000b600d100009007882d40104405c0c040400410008104880003c00455480e80400d48503401600c080d20341e03001081d00004185e10503000b0b040725510300b2001458801e100c40090052621a0002d8811b80c0c0303e00e81c000d003182002d100c0c15001e0b00007424034046c00289a0703070081daa440000c7c80c04e200c00391102c1700c403030710f0480e40e8020344040d104440046081d810040700c400d6035080c2ca00d180c0305440f070900c0089005648280140c00a032441c1c0c6c00c813080080d0303f45c000d0144690018158204000007015144000a003040384180254141344002054801000c402d12500d070b41c0040c1c99100d01000c005002e00c24040b645503145440c0c0c050341002d1141c0da9080000c000b105070000c2c1c6034009040241d40e861140e408402042203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 304676258 1106 304675152 304675177
    0x30f09120a0c02040617060c09180c0702032503020d05070902040f17060717040f02060a0f03060807050120070308070b0103030f1e0e06040e070203 65
    0xa074044098000098100d01c003800441c0790074000c08008101c480384418421039001035050300c0304005003589800f0100080c000d076139130b294088201c0c54180d0381e030783c003500c1e030310302a20542d80310b07801114201c0c421b000d4020f01c01d001503401610249210800c581107541142036509102d181d81c04600283c8940c0b10302c00c00080c10011600051020340884091048401d2034100f030b1000c51303100042e49816a80002c002c2215182c2e2280954007003080244074140d030380c1ca03941800c081d0300e01c0b0140080c1d00401c4c00900c80c100142c0003603060600440341d0343c1c1005090b6403070707440545400c0c144c02880e001070030b40070500c049055421005405604448181d0f00340950326694040320303034040f85044603213140c5c100040003410b070880c0b000000001942000406420ba05031000e0500080c10162014014a128041460f031960b0303050b234000e043c0c0d10b81000b061381131010001c0e40d2604044c102c4000c = true := by decide +kernel

theorem cover : BRFrame.Cov 304496402 304676258 := by
  have h0 := BRFrame.cov_init 304496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 304496402 ≤ n) (h2 : n < 304676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
