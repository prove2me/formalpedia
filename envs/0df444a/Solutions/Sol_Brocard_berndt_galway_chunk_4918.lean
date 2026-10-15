-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4918
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:09:08.659501+00:00
-- url     : https://prove2.me/submissions/79fd7701-cbd5-4737-8cdc-fb9eb00cc85a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 884352517 ≤ n < 884532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 884353767 1250 884352517 884352559
    0x601060c0f08120603060709080d0f050d06060509120a020a0b07030e0406270209060a1407151b030e0a0b060f03030d05070306080d140d27020a081b 65
    0x840040c8040b40c007081c001e0300c0c542c10b002e4891007030300c054045078201d5072019400c8a4a0301c2511401d401034104c850703501661440740b440036241c0c44c00d070b00782075150220000c00031040394019030056000801c0400e180d0390303910f4102881c1c0400c014210060480c51066000902c0701c0c41148240c92410400141d600b0426000b1010720804080043c020044aa0b5582e8015042402541c401c0c1038100304400d500f4810082d072003603403c3c3c098098101410403d20420039601c500929040034a64003042c400d10740000c54a03110811802c1c0108400324900b200240e851507504007102c85c1205040c1806180101d4510001e1075242c03860300407040341d910791075031004241d07000c1c0ca040480d901070000103008102510107820503800788203d69000c004442e41ea040f15501c5a0710940c0200c00a500707003034200c01c00e01c407010107040d00d0380e0100750000e1130b241ca20004d0407941d080d01802320a031500785d54075207043d8a418590f410040c84010007400b46507155614112a01404583e0309200e00069074048084540076 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 884355017 1250 884353767 884353793
    0x2151015090b12130b070c06051f050603060303270103181101031508030a111b011e0212041805060913081b031308070503031204081b07090c02150105030601060c 71
    0x10605c440b000b4146801c008204a40b007a20a5135441d0414011032003100910008412480501d542462a00e08010802881e9400545500d515200501404d03101040041c1031142450940034144074004955002605882c0c0005108114140315030710760740494600c110b6224816800d03c1d00151014420760010401070703a41c1c02c284403030f10002c6203900a545d00007400b60704010300b0204496040001000c001840051169401c0c00154140c4040000900c0c003603140b46008010b00640d450344c41510088110754001d94840c14801c4c80c00305407801080d445108041d003044094494810928003e00d070501401e081c004000d1009000140c1031244e90350050500c000c0c1e0f007500f001c1d40d0384c8441d500c2c031040040540c1d0289078018014058000b40c0b5240001c00c80c0c1c512208010784d440e4565960320b03201c550780c0140d41d1501440040c294090020745081c03080d02e010b41040e07040010180d410200c001e00e06840130003180c0c500c44601c0c00501c4555000141641151558a020001014189810180840c032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 884356267 1250 884355017 884355023
    0x40c05090103150b01090306020415031409210903191202010e0c01120209040612120203091e190609170a0f1106070b0a020d0e0114070f02151015090b1213 68
    0xc0410040341003106400802f025201d2070f03609212201403003111040103041507039041c6580e03121401d09d4210300000c208000c1da04000c40003043c201200080030a003490051141c44100b076002c2c1e1107910802c07521107201c1202204500c0200140024200b07070700daa51409550f4203041c421700704080c681c150002d40440310b443c100540207110709641d9143c4195140e010700412035240c00d030205125005840002501c0c48900003d05003d440d0380240300018100c9181083d058009180d50a07620404108401c024010304455540390210307442d103140324900e41d5074030303206002d560001c4552001280c946101840d8064016403290440044900018014031a0107401008003200c1020031200e0003c55018044a0b40c61081c140302c18002c1c1ca503203130308032140324100ca10036035201004603400307a1080d01013540061440c01150380c000b500f001034055011003128403a000c0410b070b2400340710840c5003a2603642020b00b20b081072403803d81810780d418494020a44800d078104607500024800c0300c00031a5100013160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 884357517 1250 884356267 884356271
    0x7050708030705121c0b060702100c031d03070e1e04030201090b0a0b010c060b1c051c09030f120912030e01020105070e0d0b04050f03030f040c05090103150b01090306 73
    0x20340c904046840303070440e00d01901e807030040c00541444c1c2050801100c0044030580c1c035040038840c048005500528032107400b503410403000d01c6a880181c841c0340390070040501c00c0d161011b0001092078020315a4181e0400e01030078004981c907040440d01c0c005604000d880290302440c08a6603070b8245000b40c1d041c03104d5010501c0d001d040c2400113064041d03005456190103818001500d60b074580408081d12aa00c21990015040e0303403000c0c02042080d403000040e070000401c459802c0c0c4200d030400c52510303001c14040d1182e0308410b0703007690417140b40c82121101d42b06900f803403d8810b155480b5004581c0c02c80d10060041c800c1c11a90850881c400d4030742c4000b034083c1501c51401c031021401c00800784944030040601561074040400c5609000f074541c03441c40040105124440a11551825480a005001204c092003226410203280b001480a54850040d407080340c42d8038034281c06d040c01c0000959220758003c120348001800441c01c094190b409400318a400451010206801200c038820140d0001d06014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 884358767 1250 884357517 884357519
    0x10216080406020f16120f020a18140421090e070306080c1e120c0a030f021f02062706040302030d23070c1b080c04050c270303070507 59
    0x9000009002a901c9030303402c81d2803d113045007103c4e6032003902c0040d070380010005100400524681c8100d25504520540d50070600403c0380d404504038131070310b400901b000d014030000c42107001b40038442d2044044220209800741d0425444158100c0840500c0300e42d80541540301c0c1c10190702402010000300103404590003940303001180100100080d0090540310301400f4124181d6241c61b40c50f6445644482c501716070b42d401e080c01040408400b140200c0780f54000d040d0004600d540c0c1355050340003035000e911214580c0046104100c0c4480d10644d00751115960f800c40f4003035090303000940503403001d01041c070980c0c00001d000406441e40c8101c20100082c0c45440d080004040c1d01001030403443c11106424030030030b11444894410700c10210012061000c400d00000c120500c6240028403031400741c0000f40e04030400301c00c08a4560740e41c0d0005500c552000b1015600780c2414825a50f020100080c21802c190481d100c0011a490800160003440c9056801c11007a07a018021240c9043e40201250965 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 884360017 1250 884358767 884358773
    0xf0507031509020f19181404050705030f030f09040221090d0914060708031302030a050a12050f0328020a031a040203010b0409090312020a0806210c0d05010216 70
    0x2a150707841c400c9000700340307a400844180c145070300b18040e01c01c0141c0d40081483d046c05840c03a4404070343d4048490072516882d849046c2580580170501403801800607050359400c0c9020f041c038008004072502c0d4140d1040144004200452050780c24228003203c0141c0d9608400c80788030690116194039968403001d00c0188284600c000030050f00341032403501c503c42c2c0c03a9555450220003a0701042c22a401c404100140d1002800090040d5030151150840b4003490840b03401107494004400d0741201c0303980c0b00c000344005100400c3c1080c298102c8600d081458294003410003610340c040542250070142003c0240000705440b4540f001c40036001000864440001600c001c0217800150b61080d1410400c01c44140320f414a402164181d5440c4004e0a00e0185044030500040c81141000d0f42000401c1850b50300d0352615000818200d5210303900e040c0c07281815010800100e240070742c0075103d0851420314040d20007010134076511a00c0c2c01c40712030140074040c2c1171003070180c0304041e60840442100703090b90b420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 884361267 1250 884360017 884360021
    0x909110403080a052d070f1e1410151403010b0405130308011d0402150c03040b031f180908090901080102030f150f09040201051207020606030d0c0c030f05070315 71
    0xe5804417050040e03001982a1001c400f00e052440d03070420121003004000082401038440ca002c01c0c1c07184541440100e2050a040c0303441d07168100888420300002006041c14004101c07547c1d0260354120200300c0c50181034002c420f0789150384201d8101002090340521256002e40c0545071079007000e4811703c20751801c411801410000134004802145100c0300208074440d60040d080714428035940c0300701103900c3c0c5808200c4041031682c145061100e0421a041d040507051024000034000e9607401c0d6200c0c2000c2c7c01d000c00d8141201c2002080c8908802e082020f0590401100300781c81890000199006150030301120500c921a00c49420200e444000103840030b0550040d446441400841e40306611050400300a10b1030b064140c80c0c1c030060b030940450b0741b85005010140c0092050404928000010341c100c40005011200000513030881d0040005504090221415040b010321b0030100c2e01d48a0341c1c1c0c48003800030a002c040c2c030700810200344104100301040803c026540081170140c0c803204448a02e00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 884362517 1250 884361267 884361277
    0x9030b09010e100b2407080c1906060e180d030209060f04030c0501020d08040b0109020a0507061b020f030f1603110304090f06050f03060f060f0a030f210909110403080a05 75
    0x10044034146500c85d075140e4251031000340c1001c48801c6034505200b6441d070001680100418818500803504031080140c5001004006280300d240041001890301000b4452404020900004002020301c0d1701c3d001e100100701c0b120000294100143c60785614804035145010b0b1031b00e46100ca05002601009010507809014100d900036400c0700c0e0715059000c0111480c590507036001308030403131003001445108913036005054a2005c0b46045030411000da00c4003000d48031446a691040341c0c04044800e0800d03414055a0202103076a4021890810044080706a512402c07481d05280c9034a95800000c05100740441c000c15208c0c1c400f101c1d1284c3d2070702c0000008201c00e00d0300e0044107261035800901414001640303000000c001b400303048281d44160004140180c0141075503400b005060b11b82d10542c1d00d0505641c050343c020f4004d00b03080500c03031034135000079005240c9021186c101c07000024002903200d4000c6c0180c070180480403480010008036140c1501464100400c0340d880424081e5205134404c010701 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 884363767 1250 884362517 884362519
    0x1e021213090f0e03190210020d02030f01050306100519050402030705040f0504060e01050420030c1c0513140a06020313060b0405040b0c09030708100c09090c09030b09010e100b 77
    0x1d02c001c50304038041101e02600c40c004083c0c2080c020f421580c1d503490385103102980d150054450a6480840040c126444000d407081481c0e404424460300c2c0101ca10720f00c1c0940029002060203080100980e11081141c0c070400340329410620502c00d408108001318801010041c10564481c209040c010380340ba001802000040c0c1d8002500041e14134141c0215012034410007a94502c0341d0a11050101070b2010b00c51030510050000074009283c410b031001540b00c1c03020101080d0311424032070008899014404082d44109040c20103010700b82101307021a01c4110341c0320068848110910113030a0800c0c181a801401c102d1021040001281940710b020356081e10a8204011071400b1740c00f00401c0b60703c1a1405081c0528076400101e031041150001c081069004080300c8030141c0d2603400e5407400c0f1640c020b80d200705403a08103610700107401224442c0035086100301800038006258000380940700d144406000002007001041000c0402c1d8045103450702d404041c0c4659071005503448000d8004a0042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 884365017 1250 884363767 884363771
    0x18040203070f1707120b060c0a12031524110a030c02100201020712030213050402030915011203081b1605060103122307060204050a030312060b07031e02121309 70
    0x2a02c142c25111091034414001d6032208841410301a40f505c004013141070500b50401400c0107444004041008807500c55441a0381c4d60200e501c1045004055490a2100c0c1c8083c4803910001d01104959440e81803040904508220403070103c1ca40445524041c0360f5250080e014958a0501381940501e071a10a58025922503d0645c0042c40481c00c078031468401a140d41a02c12018191034441d400618800e90340d000c50410302500c0d800028102da0094460310250b5000341e04001314841030440050040442080a07501140b094401815040008012034150080e00803101c484036181d2042c6c034103a501c0045074040e681258503105545040030300080e21003c25981e20a140988103442d001c1c500790541c0c00041181c840800c0d1401c0c1900300700c03070444d491360b028040445c0c2503d41010384801540240d40f401c103c564104a11800c5800301d800000e503101c1c0400c11480880d400071440e03584c403d5510011640300d418988100e00707120116400341c28102c000601502c8000e40390b01c035101560038950007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 884366267 1250 884365017 884365037
    0x18060c030403031b0f02010c03022a0306010915120201030204030b09010b040e010203270a1a15030d05040612090506070c0c1211060309030426150402010905040218040203070f 77
    0x118821103140a1000f0000c04942d085c003030065100e05104000d0500c01d004561107521550000412020a5241d40d9848420400803514515041180740d00400f00b01c001081a07000180402c1d0b04803540380581075824010351940d10441e40300e81d045400641d084011603846081480300c40d40038080080e0030320b100e5400c084c0b510b61000818402c483c0111461001500080c80100554844440c020005525806900d8001022804044900c0c4184c10031454503d103902d01f01903900070701041601107900070f0340590840200306030402e0444099070032604251101c4080074115001400445200030824001c0034140041c06810240300d035400f52240341d1600e0b109848290100d2500c0d60028003400d11010b02c14101200d0404c10001c5130081c3c2c0765000e803442d29854405400c4540224010815004100c05640002030001d00864207120381d41510300e181428140c00007004400300b40200c520950b4000b9415040c4e010350300368086004000351041d5240d240041d8082c0c04403210111003404194034280e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 884367517 1250 884366267 884366297
    0x250312021c081e01210302010e01050f07090b1201121524120209011413090809011103090a0b16020a0b03061f020a290a06060e0105071718060c03040303 67
    0x31140c10b07180b58803000303042202c5005c825041402c0c5004150299542c0d91000544008203000e041e02c4bc021845030380e43c050411000003005401035038000c801d036501c00d10103004010b2901400e80d045034210f030384010030348c2004d0603c14500142c0e0546c1892039880c2c2040e070015200c01c0c210b41842c0b280965024a03490399982c1c4901d00c840700381c0741c000b948a0030000c01445074001c80c3c801c002d000c41c07015100580205140707040c24102e0b860310506641101010420b05441d6902c08007414017141a03001841c14086400c0100e540d608040c01b407403006500102e0f0034001c50500582500006030010a404440c0355100e41500580d802614030a01846a99080c03040e40f0303020011800d1903844940c01000040e003103490b5508184a80f03010540c0010010303a90590b550107600c285400b591080e140028590301c0e000d4042c080c0d4000024003414002e0a00c001004158015851642da4102c0ca0005641d1048400710000300c005c2c0c401013035800b901c04208001340b04400805001030301d11036107482c42d010240c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 884368767 1250 884367517 884367571
    0x14010605040806041e020d05031e040e060d02040f06090203010f0602010608030307051305040509010c0e01020105070c2d0c03050601080109110f01020a0b18250312021c08 75
    0x20045651541c0140c000c10009603070520040200c1205415102032285c0310346c005103454820034000c1c0c2e002d500c00b24084048000c1c0d2007001d000f0b1030080c9400751506291441140340c3d07420051040744148082400ca00c155103458020303501003200002d0801c0007039116810350000b90070030701503058940b8240202203002c50052140100360b070108002142560303201d01c000c0f64103074000940c110038000c02d4000016035440d203000392400b0348200c000120341e0400380400100450030407242a411a0f044c001032145260f0001c0c0300030b0015401c5009002888c0b21000d88440c08031038036202e80d20300781007035040d1000d210841ea03004060320b21500a4031503a1345e032000200d081e90007494002c0c0c00b80e15012940050f602d020840f00d540b80310103006031001c0071a503880e03900040808580442a940b0380031400f651244081c080f03540814040c02c525004c0349200101d0255860048c0802090380d109a580c5860480c02000603990102d91000210b0502d59024802099000b054407802807662124446850442e004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 884370017 1250 884368767 884368769
    0xe0c070302030405060d020904060e0f0a0c0503010515070b04081207031b1b121e1b06200406020a0c060201050615030606160818060313110f0409061401060504 70
    0x641c02182418241020480300e5070240c0240038082d54200302c1107825440d40e010384002019a1280e1040f289070811641e03100360401800004040e00d8404c00480310f0743c202c000e59064900c151824104226075424005880c0300d550000f801c02e1140c002048100941c100003131004264040020506444e1183c0a4050b201c01c0b961801030903541c5496200000d1040391040101c645090107841004483d403101401c0030032003914480019541d00c0d40c00e51040640c11010359040c80d81c030348001d610b9205640003500d90380700440104110f8407440d982080c0c0322410510315142c01c0f1440320307640e0f0b1966004042d5841c001528100e03170620302583c001071818010b104403485030070041c140041c00194a0561000e60f031005164680c4803105004019030000c89000040c0311a00c500303202940c500c8001c0c1c41e42c10380034240030114803c00302001000091001440c45003030302680010060495901c50000a00340141c400d407854000b0f18001038101032114a0700f041224500c0d507403446840c0e0362038039021900b5100d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 884371267 1250 884370017 884370023
    0xa020a0e0a0806070f09270b06070b06060702060c060c0306011d030a02090403120f1a030c13020904140c070204061424070f03090f050a140f12070f0e0c07 68
    0x8880000d201d90300440d018880c2440754902103002d20341b1403085c80c0c0d00d64001000645103044c00c08030404c50680502c06e440390b0302c08c11901241080c1d82c5a44103c82000004c012030b000301c0c0c01003180d03011500d924040d03510070101c41041da070180c6070041c403108544d00308030f48550010703841401ca0f1000c4070524400c105440c0c0060098400215187c003030040384030005d80300b2401c000051181d210052124441c4500700c220400000c180f02200d140540480e29001c60424481c0e004104034001e80c0d40c0707009030381c101040070081c050384034254200000e000380b804404c001040b120403000c10232484194402028501c0c4221001c00a10f51506180060f01000c07000454103c0100300c004505060410b00d168220300c1c0d2103c41d246400381c265501c0c1400e001d08442240401c002001c1880201e005900940c060001a18001c43c0d0604c2d2450120b6220142c04002e4050b8602c003220201980741e20410000b40d08584046683c01c95507855003013202d100510805003080d126001180c060f410039030840303201ca90 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 884372517 1250 884371267 884371273
    0x100e0c0901050a0917250819030c0c03030806040509010501261c090e0a050c0a0302031e09240408071103071502010f110c070303030b06120a020a0e0a08 67
    0x240d503001555503500c0b1070103480602007409000108403003070136159182040203038060005a03201e416949001c21001e40c5c2c480030040444004d00215800191800e40841c540080c891300c2c1099040580342c0c0d4224034400f030580548a0004010305400c010740c64040c03074081d0340800040c3c2d605d0341c40b50300b221828000d006c18141c410044104261440781482c4841c203405007582e44203840c903000d0700c002900c1c00da00c841c00314440401c200100050010309507072180c0c1d1660188060318080c00410510f2140c043c00c58145980800810701885255a40307441c52400c10203000e01a06241c4106030352a83c154507000f0600c5520007049401040d0041414000c6901070a414140400c643d96211044880c07030749182c01d80f00305c1c1d0b00014010702c5d5110500281855800001c0c1410b007605640b01503500341e01c040d1581000400101c000ca1100240e0101141c2e050701d40000c55803022000200c0310300c5640c6440003c030480c601841074851740d5900078142c07a940c580304c05064030030010034440d1009852040501c260 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 884373767 1250 884372517 884372527
    0xc0c0e01060f1b0318050405010e0f06010906020c040c030e010507110706050901050d090f05121806190e0402091003020d0b010801081f020f0a0201090b0108030f0d020f04050a0b03100e0c 82
    0x1034000c02d05074a110b41170b0700c081c6031255110004241201c2090b40598001403200081c00111745041000d180c0244082c60710107525070410f400a541c8101c1c10047c140543c0c0d480b038003060241c3c443d07801a00c9002e5a14002d00c06402d0810004040c0c501c1c1070b0180590f80560b85000030050f01820840f4038108041e116282401c0c0c0380c0510a0040c000544156031480342c6505060010b001400b10f04c42100c1c07603096158031140d11090300c1100900700a1014020942003000d1842c102566000d00200d00440c90100058110700c00414041e0148440058001c2d403d001e00400c8917806801a1103550401d5004020b0052104011515942c00b880b414059401c0700d41440c48061800c0d06003c1400e1100201510304840041310241ca58003540c8584c0c0180d556006180030803400c8040240101411070040d8142942409204098421a104d140d0f07000d40c00241c01510340c0b1220242c4006010050070070380969900c2158255a61080300c80314400c050f007203004140c038041d140344d40d8050003940200d50700340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 884375017 1250 884373767 884373773
    0xf09060f050c03040f03141b010e130603020303132d0b030a0603020a1d070804020a060e1311030f090102120a1109130e0f010506150a0c0c0e01060f1b 66
    0x242d10008040c1080d002c1048040341d464064003481c001184103115403200180c103064114200340c0070080020041900e42c00030003140c5e81c0840f80c0c84841c0401c50319402980000701010380104541d81c8025007601003c5170928841030310070782503070840f019085007018070004020403609081c860182280700344400802809026601d1000d164094074080c070005032240c4980004114407400da000c00c403060200b01030484541320308a0810f401c4249410304400364106540000c0003404107008030010050b030841214040d9440c0240300d581c41c0e032110000c202000288a0b081e100c1c0c1d00803256240c2440d03440b00032550060052088499402200c10240c0329078441024000103445404121038003a4414014070392541e84440c4207000e9217007864000100320040c10891420300340480408040c60340342c00e00b00100381d212210b0345051003101040065690841d09415180e90400d14409000030204840100ea80d07080803000300d060740c1454070303080d09070091200102e0713010900c0d000085486c840c04140c0000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 884376267 1250 884375017 884375027
    0x151d10030e030d0615090603020a140a02010b13020306030106060c0c06120b120106030308130c030f1b030524150108060f10020109110a0e04080c07030f120f09060f 72
    0x702041002030320700c0c18044000c403400351165a080325030381c01c0d440c01c4892803480c1c200f41840002e20f81c60509506040070004040c0040d070740201540b040403000642507070958800c0d4451985c414000b42400082c1c001408181c0007500210b030400e001e58a440000b04416015001c071160043d40700c0d0400a496041c010102c41c070f480038036038034081e140e141c0014950582d2683d005c0a850404040000768891440c10000c040d40009840c1d01885540b00c0000c2001c075509035910802d40341c20180300f00f050381c1d491400c5900c00c84100d22340e6080451440001c020010007054407003081500400b4503100011030270008a01401c01e5455415590500e02d00440ea94003c2c0d804542c070140003841c400400d1082000300368a04044411000142d56542617101004088500c10401d01e2059807420750030341c107104845001142c040c4c0042d00302c1c4070200345442450b004001440156071700c80c801c4d000b10f0703410b0300d00180d26000c100d0060300070513500e080400300302d8403868540040340c00c103507164040040c0440040d15 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 884377517 1250 884376267 884376281
    0x7021c1502070f0b070c0507050105030c12090705060f030103030905010e010504050415080d030c0809030a050901140904090305042310050c011508030408100608030418090c151d1003 80
    0xa14214680d03c1c5801140e0091200c03442030090740c503114100081403030840e0800180c0e0300282e0512409005100b400c105070003e4541030000014000307150388400381c480b45888802c2e400103910503400254110080b8144000e58100d03442511001c818a03212401501c0143c040c0e42c0301030006400344804c004610301a040ba5906c070a0400a8151f450707140c00759203003441d285000c0dc070042522103003124200d0783c1c084d40c19030380001084050740c24203c07003d60081181c441c8200423030412030045c084003030f558030135021200d410000600800c1040c800345005001c80d08075226410003212180040103110101c2ca000c203185900007450000801e10310801659587c0000035030540640d030712550924103100c14500140a05440310013036071202e18080116150604908012100c942054070800c03403004000700382e900f900c01412084002c102e540034450000c0501d008047c001d00682e00c00065100e09280200054801c59514131000e280340c0c2800401c1c061541410a40100c16412048582d5202c2c0c0e00c01c007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 884378767 1250 884377517 884377523
    0x307170f031b09130203100f1a1b030d05041a100603050c070b09070503120c0715170f24030a020d0c0e0c09190602030304060f0e030d0207021c150207 66
    0x2402c009106012614000c4c0d040c00c0100e40a90000500100b50103902c1c1000081007551940d40f00d4500b841440f409806018610504002000c03520403100900031481c60040b1301c1002c200c0361030b1009802c040300035102c1076900351252540030038010350400c540c09520b0310a000d084000300c901c1c0d00d04003044009100040c514040e644c428008400081c0300000241c0c0a00c001030000c0005904100403d41851076082151a11240801031300010b000c0100d410003c5480c00408203c2c0790001100940b00646544c0c245181a401c000403c2411406104054010040202c00500341d00c140d102040c000c4000442f0307a681070340100003003c01481c0c5043e64000480c41244d00251881d500c003001503044500359140e02c400c410200b1264018200000710305a120303912600c180426103000c034065100e02c005040030b801591207404002600256800c0003120442c42001c07641c0c0c401c89011580300135003007060100e00c40d01201907403620442c2d08005500c0c589800100301c2d000078807070450b490000c1d44008021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 884380017 1250 884378767 884378821
    0xa09290c21060a120c03060e030a0915020a060c030f0c031503020d0c080706050c0105160c03050a272309130c1809030206060103060602121b0f0307170f03 68
    0x109004c0000018031802510445135000301600f545882404e0b101c04551502c482e9005202900c26180d04c150000e04a4800210036500c8513043c5c441207040500c1035602800003410090301802e6103502d41e002909600c0b11030000c010903142d0f140200d0994803801c48a1416000c40c540600240c6407a03070306a507100707200319002c441c1c7c80e6498180509041140d40701d0004281c0c08074449201d448203001d802d61000480b00442d1004840c902d0107448209115800b40c10005d012a83c0220503001c0c002100b1005c80c0306101c83c2c0361080c09003c8484566040c01241d4005841c5940240580390b414045c0340d41c0705000304100b2080d962050b0104650149020648442e948001c00240d146280702a244c04000d104102245610807414040d20700400039141d00d0404d0310b01441086143e6021400041d1900c2c440645565000000c10070264252801090b0b0b40d00e006004816010750320010040203050b2041072040c04070a08140d500102e8013801c82c4400f04030300c04000080014802100807420f0349400b2000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 884381267 1250 884380017 884380019
    0x10f0b1b0703080703180815090102310e090d032304110a080d080412021e030a032004050d030504090f05090705030f030702090a09290c21060a 63
    0x20381d2410129510a44480400050741e90906a01ca0990268182c0c424021200b8614100c5030940e100c044802e8020b070000c0013000b040300d1100a40461f0007040001c1b40c01d030030403a8144008525190050b5070050007505e1002d00107485120203040030302c01c00d601c4001c0c095910121405034050b00d0401e0140140c0390003041c51800d80c002e42d16100e40940d00840000903001e1480051240010041e00103400b0b5603c8a0000c0b044241e012600c0c0d0f5104c0c3d442260300303040103a60f040903460420107010107000d0b10400e20300140d139240d000010f001030400a41d400e10101500c01d0b4003d01c19040350320000d040e0700e020401400207003001c80c00503015074481c0c50400c3c501071352810300004440391050705000070b68445040c80a003c108000c1c04010f0b000440190603601d9044a805641340302c6c03183c00078080d1031005c0015190020f2a0300c01c488558019007010050700c0f50710503240c004141d07000c0c0ca190750b04d0355901181100d000a81984d007002006514000c1c0300d455030301c0c0c90804840041c0380d41d9210b404924 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 884382517 1250 884381267 884381317
    0x70c020306100e0703020f0a21061d0c0705120901090906141809070513150e1e01120f06060b040b0421020f0d0c1203080f0609010f0b 59
    0x1001c00c0c410791641002540b41410040007403240c54004c0e01c0300080600500000d001c1200f04011110644503c0c07d09841e40c0c50311480c1c1c6000701c12042d0003a281280780c10b50015421034036038001014580645481d950700e650b02000405039000d000720140440d44924407101c130f03070724201008054402050410100c22959910404240c940541090303185c040030b00720700f0b682402c212000303007105108003103061154600010040d035160514490148198000c4010504c0740e01d69500503a8848100e80c076152074145c461040c0c00c101403084d80c040d01101505c40015008028048695041c1c4440c3c01400b80003000c41d03220840030046017481a1200c55a8400c0011411b89440050004121400c00c00b5119840c109090221902005920700d846000041410069907801140c015030f260845143d078240426040209030071945400001a000005003c0c005040d04414101c0c411503850240c44090350f103001c1440079210007071040e070b00208082c41050003103101d1740f40075040c0e0a400d03501c0c2d006020380c906 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 884383767 1250 884382517 884382523
    0x171002030412020606030d08151503090703210f0509010e030d0908010f020301050a030210110a0309030204050c09030a03030c030908030f010305060c041404090c05130e010b0d1505070c0203 83
    0x6a070484041d28240c01002e400c035018030500f40c1c014012400b8141c04070b0040c5003c0d000070801480a04000c04e0084140c54942d1195084600c59052032011926481c146062035914000380c04156a204d80400b0076505080505444645290042c1c2d1145070005c4c160348180c07020b8100e400260b0500034107040e0388055031030400050f224007a90340e0f611304a0610300b0110500311100c541030b4030300c40c1d4010401401a621003040328421282d05840400103000c41c2038080342ca5042c0300903020300a00400c1d0040040c184d1010390b01056900031a410040e2340c03107405112940e445103444080d0960008804440482d010f0b620184003400c1a080100f1105020b40d501e030301ca54411207031080080511401030081c44410024960701001d81e02c0700318942800e0200c00d03400282d40340304003481079032a1061142003180e907552000060030087d0400e00642c0c849000600038012908401850303610b0030f841d0007402e2426620400c501900b1038a0300f082c0401c07030105c44005d010010200010701200c6944100140c40070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 884385017 1250 884383767 884383771
    0xc1b1a0c0309091b16060b0f0901030f0303021210050f0a0608070309170a0c0c090e1f0b04021603030b0f0d110301060e10080d02120406082e031509080417100203 71
    0x602d008003e0b1101781c2c5040d008848001c29914003a5520310f0241416031909031700d29055a40220098945084c1450304401a1141e484030345040805030341441038142c03c1309a2602900e070226507010400c0031503405d014074000b052040c3c10000ea06074001c901c40d18020350000d0180d901501c040001010030103c40c0c05990b100d8140d050004250348c40c50414821181c40003400340c800b60300c007030025540080c4e95a9071182103211080601e00c2802500074601e0342540702e2a003950000d0029529a940754020305030020302070030258082801c1c456034007814540420948501000141481c500c1030558980f10b520280545060303805640e50cd4010070a01031000f00c040c860495400da0421540c07c01d0a5181400e034400c1204056600499201c503944048405803825103a251038500c07296626181481d201c200389205807184000910400c40c0361041400da0042560700580160380520161604041151244480a0b0140030284001d1020f1020350740a84400d444400842d800030161050b064120703401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 884386267 1250 884385017 884385037
    0x1020c030f150112030c031121030421050a030b042301240c02010323090105070e010c08090f010216091b1d010e010c1b1a0c0309091b 59
    0x2820b00030b8480c0311581480ca0152a029081a004601540d00a00880c0245c00b008081c0844889154580c100812140c03440c42c0c0521a51603110800019080d07055105613002c0c0d0f5801c0b10b00a8040c0000c500c0e04001da08540b040d41e44070301d4807441c44030440080855680c0e050344140c4070440010720340d4450b00003100500c80381c0e0612209514100a4811000752546401500d4a415400801c0c003a0401e82d01c4200c150282804501c030104c00d00a107800c0d402e41603000035801c0d1118107128150304154040d91107a00c40381c03140f0075042d18407001076410b10202c0400500003041040000c4079810088200c0a2828060040b9140003407960807446c02502240c1112100e941d84808100c8458040c0c0012655440681491280b450168003e40f42c46a80403c0c590f061100900000361140d10170486001401d40002c0c0100817040e15203071440115880303104140c4a514610000403420b07c140d821250705039170100c01545401140c6091003401e031001461100c82c1c41d0020700711200c40501c24014064100d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 884387517 1250 884386267 884386273
    0x60f0c0304090605010c1a0c04050913050d02070b070f050f06090109060c05090618032503110303030618090c060429031003150b0406120c0504020304030f030b01020c030f 75
    0x20802c1d00d50411030308039a0040307041101d41c40c4150040b0303502a0701c404e01803003024031001c07180e80e90214442091003607620181c4c0007081282008118072a0704000d1014030320440540b400c01c000102e0490f42e078141802048505981004120001010780b409000c00071312030f10690f82e003c201c1d0140c030740c10200100c4e80c0260300d0b510b819000c1c0802c1164820700e0000000c07030806904014019010070320600a00c24407445001150442a20f1598200060196011410080d1821081400c1c43c4000080d262008803118411103814290360700e404003d4074829100584194420800c00c0b454030807004028111207214006c20b18105810b4540b4001000500b6180d5035802e0440c003005001103124811049a8006103000d109110328070b14180f000500b2a50040310306400da54a20402c1c00041c2114080079501c40c2c98440001510048650a1030140d8000c5600c0c041c0b940e5900c0038001079210881e0014000703100e045840003001c0c084e40c450520950184103c40e410281c80011a1070005089080c4030554 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 884388767 1250 884387517 884387519
    0x50a0b0a0e06010e040f11060301060518060c0303060d0c08030a0305160201060612090303230601020607020d0503042901090506040e030418020a052503030b0607031706060f0c0304 79
    0x500e1030041ca80c41003881401014558900000c8500000d0080e20091005002c0b00e501ea0501640080208407540c009151540c0c9594139a4041c005500c640102003c500800601c01900c1c40c2c040b090b42e41c64002c003401b441c6075585e484100002c200040404980141e6910710205900d101040900502001a1030019440c02c0600c640360400190fa1251011a810107009010481d84208a068031420348c10012a083d0381526013640501013561080340190f15555407241100400c04485014103000c1c1c0a46e01d042c0c481c074500b00d881e11041c1d421a80403407030400105000a0103000c603042c1804002d503140704c1c0307032216004405029900b03a0084c2540c07901c0d0018401d0600e071a00c20640740c404250000c41c42d040c944296039550b66481740000c4042c40d07010070302d800410f000f60122400e4003101c0643c90f0000c0c2003d0303010301030b550803400c007070300000cac90461001941c1c1410300841d2052501503c41845000d01c400e0016481031000380040d0700048140b148861440b014000b03840c00c02c0304c54024644507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 884390017 1250 884388767 884388781
    0x604081e0309031209010b13021317010b2803080901050706150e06030c031005101d04060506010309352b05100603090f0b15040b0907051213050a0b 65
    0xa1a800361054400d43d141607c1010160b42341058000007065001015860b03c3c0d080e50b06015203c2140c1c0a001e211110100d42000414107500c41e0301c1c59031003218080742c92203800d00b8080140d2021041070000c1c143c841c0043c0041003c070300c00b0746808101494001c1c0b40c0100e903a148801e40d0310000508504041440003401407905511032246d20400a8000f0103014040e403000960307a12121800c0303202d030340d0340f1004250000048001c0c0c070040d100c114580107250105068065916604540945040c1d1170200400c5c22980b00e0b000b0214503d40084888000070b42c0480d003410a40c2e800030080d59001c201803640c2c0c0450042e84050030f081c20007021b96020240b560381d20344880054401c203c100f039514010401c003000d4050300705031003542c0d0b0034900001d000d111450a03174059000041d018100d03d44501c100080158411607941c4503000c207580c1404850700b180180401e0440954207000454418003e0094642d041039071a80d001403070000308240003201d41c43d02030404205200686910f4280020402c01e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 884391267 1250 884390017 884390047
    0x1d19020d0c111011180406030503120405011104150f121506120212040f05030423010e04090c053a02091303140309100c050c0c0603010302030604081e030903 69
    0x30f46504080c080c004188203044041c00340c030030940103d1070b2420301c0d12103e0131038850750310900c05550300804a0790303280040b0080707054007a01102c0407a410341c241003124403c6944074050303e04031100c0e088003c03803401c0d64100548049600b05281c60400c1161410300000300c1c005e01844804d400303010035400406080040040c2041200311100c0308480c010044d03409221032103102150b06c2904001c524190500320b26001e401c41c4265802400b81c40303222a112101a0344217100b6198044003601c540e0310740e4401784240010b075a00d0f400d0103040440f20030010001800d001c070412205003180041001189004402e510188100c100c01c186a03881103c540405c5003490544a0b402c645c1c81c02400f01c403485141e4000f0000c85108901024000700800840d80c100380c10410352000c0444214148004410100700a040d5004400d450540d4071800444886904110b81128140c90b0003a015100603580c5846130712540e40000b100703489031084a48000c02c50045130b800785003e555a0b6002d1690384800c40d200b888 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 884392517 1250 884391267 884391283
    0x1015050105130b13090c03020301170a0b040308060d020604091401120c03020d0f0209040308060a09020a35090714040212070e060c070b131d19020d0c11 67
    0xc10301c0400c010900001d10503050000c201d0303a000039199511040e00075000c0c5900382661140c009682483c04001c40680c140e000f5605941c5072100070b008408641c0300b910f650302004900502070144c00320104012a100b128100da1100c400341c80d0b0354901d00c055010075160351099008000f480d648001e49a0b03240000030125004000c46d0507000e00415203a00d071811140400d00c002845125107125a0b0b080200b010030b01514143c000307002418a2500c1d05001e8400102115032a01c5008103500216480500340b003950082e18a41d950020310340d94a41c4c540206004a070140440e1402d0744018040000c8604a90f0303205412290207000114900b0f400310b580c2103112200944030304e006004404544403100003071503002480b46401041c0c100c0b440d010072100d10826900d21842e006844001c64958130003402024411500b101c14090b580e1342d1094054003002c0018207070100fa004101080e080640c000c0d1082d5008180c010051428480300308003011540c419000c100803135401442e01c14081d1051084403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 884393767 1250 884392517 884392519
    0xc0210092c0106052107030906050103060e01060b0f090910032a050a031713090f020901081501020a0f0614010f0611011401180e0703050307140f030904050a020c101505 74
    0x15041c0403900002070741416003100325036003103517440c400124500e200303402c81c22a03d03402507002c0140703503128100b800140c1662450321f0015030800000103078038003222003120107404014042c1801c0540050030170001440245c04002007110811002c00841c0591008070a00300c1c040161684003080c1442410010006078845403041040071020000300b01d408101071500d4427450711265640c2955407051140c0249030300301c030900740d180c0808240031003820b50080410500c00d88426101d681c500b0501c2d41c000302d51120150044e0041e00c220300c00900021031484001d0710a100100d2100d04a04000d00f40700801d92003841e881e103c050301045400c0c2c03c9540d4000000ea484000c0c09985020616080e0703000301072207680d6405030600c0d00000d01030501c3e40400c0c844032030041a0380900da643d040843d0b498000c41801e881c1f11828000024181c2000542c4030742c03082c0b00601960401c03121004000050030010003600d0456003c100d0324110003410301511520070320160700061841c2c0c1d421920804529181c00c0391b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 884395017 1250 884393767 884393777
    0x10060510050c0304090b030a0c0e1905190b121c0e0d050d080a0603080f0406030509030a080a0203040f051f06090e101505030601030609050c040209010c0210092c0106 73
    0x48030460004002c503070176944905000b043e002004004289000c1d0009000382030080d5001c4041249803581035082d000e207424400e90340004125948840c22500180d9030144001c8200d110003801c82480d0700310131503010004103003058094a80d1941c600384081122148040c04903990242c3c000c613001407161010b003806642800d4031503000d5440c10b65401c1a40e401c00c003030009840c00190752040035040703d07010f968050095a12035404d44080d1400d41c109010b80c002182c18140001d211000001c04d43d40c100e51503588024a64584050343c1009600203002a56100100c10400000c103900b004001c1c041c01401020030306681a8200a00c1100c203113400c00e2003c2d900300b281c552240d2100007410b0002c2f5115640000e50f1160001385062178002691040342c16019880c0000180034040d40458041c0e80a002544c046060407001c01089105900ca0903012401c802c401c079025040140c2140c2e190740c103d0502c89000380d103600e5000d0391540151800c92800d010700d881140c900004600c0a40140314038200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 884396267 1250 884395017 884395027
    0x30702100c0b0f0c0409060605040806070c1a190207050c0405071b02210f06070e090403090b091915020f0a020f060a170711010c080c1602040e1006051005 68
    0x585403042c802801c3d040d0300304003038804250a8812001154000c0c944050104101590f0381c2002e4029000b600c501f000502411001034181e03400b520740c41c000b090340140c0b00c40c0c2258031601c41c00e40c028800303403030000034091102d10044087e40c1e03440184580e9018000400355001c040c02080140c03a0000c02c904c08101da0500100c20074404401c0415116604541440190340c408084612100310302d480040740c1d208804104d0001070000c034a560081c00303156500a1106280010300c910308805840c01000111000401c01407a55007001424909500910440f6055000200c10aa074506a040000001d0300c00149101d41d1741c0400140701659450070182602c950700340c0000300880c4100c1d00e5240114000918076407268401c5000c103144210b07900700e05181e4140761a00802a10303109040000030761a03c2c5002e02c0c400e005000b003612030302031002d00520780815440098a10f003d1a80d0890308685c94552040c80401c0030700080326600c6503480300180e02480c200401a041c88415811000e02c441040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 884397517 1250 884396267 884396273
    0x804050915030d030c050910080916060801090507050c15060a081903030209030703120e01090929030c130f0b060301060f0c110d0303140c0c0a1b0314030702100c 71
    0x14510040c48650800060081784407405070340c0d41c4150010184d0152401550010b010780180c0441d000e003400608541010304500822405070001d4050b10000c603504c0001000710741038941002d07901003141d00c2d04c24100800c45010515007131840c40407013543c400c8107041000905210324150f009007510350040c8801040c1d543c0e040259082c1010190801d600080e60024541f020041e11004644c800c0c00e04115a400100003070041540e50705040c002280c000b000180705403640210b040c0b60307103004110201000300d503005c000e41e00707040780c07400c0e40501485024109981c0d0b880848901800040d0000c02c01d80d40010300c0798102c8001028243c411803041c40107010745544010742041103281410240d106a04070f0812109100b81c2c88a40c551007881c441140041541c1900000d004810300c42d40c40c850707030b15480644520360042419401d01644107016560200e4400b644001030b00000c1ea0701100f01944a8660582c0d0b40110000e98550f40d200090400c118100488200b40c032002c0c43c0b41600c43d205080e5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 884398767 1250 884397517 884397523
    0xc01081909080708072303070b0c09220212060f030613020a0f091b080c030f09070e070f02010e06130f0c08060405030414060f0d23070908072c070e0d080405091503 72
    0xa800c12b0100f41c000309400810340c84081946905101c010140c120300c00c0003400b0b403070181d4401080b4034281c01d44140031030214100a460540b041c1c800a0207030801c4c2c2c1d980e01035030812503502581683d102c40c0c040400501402000f940ca00035184100300492403119009107a21010282500c040422808101300146005884190b81e005045000b1a000304d031601741c07845142403a02d810510080c0c0140080c0000150860782c034101c1c05000781c000384a00342d05084d5254031410708440103072580e00096680303800513520001081032148a004254050780d00d5081d00b6103001c604880440d40e41e84001002e002c0320704100d2000c2c40d907610860301c85180000d155180300881c0503802001c480c0c940c6400001c00d18410b507080040d403c1c4000388a18181e03240030304008004421038801c00da01030140a0f40030522501694011a40c080b20740e4101d040315030b00103124860140700604400c10800e40d1424030009545107051506d20b90b0081216039215410102006a140307806054140030455034404510961008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 884400017 1250 884398767 884398771
    0x7080c01050c0102040b130e10050a1e0816030b150618030a02190f08060108060c070507080303010909060b0105181e130e0c01081909080708072303070b 67
    0x386401e41e00c0380440c64406001e40195007005241d2100490100e07200c15180280b0b0044a050b41d40004840d122280340040071500c1e0302a2036008000300000b484205070210310044103001055031110300fa0703030710003645040440c0d229440c1e0072940800402c1090107440841c02da0010381d00381c1020780e10760740f201c009607442c80760400089a10140300481c80c80c40d41c1c24400b0b507507059006001403104600c000c00c0010b18040b03d000d1200ca4a030541400700d2386400c0000c2c41410303200703210010031a60f2260205040140c0210004072128171681002181d0504240084d5000b4418820042941c2d6810b20340038055407040c0200301d041090502014520a0014a02105010040e610a00d80c103110000301103030401280040c5403c09601c40e20088036200a80c800a4203100c504241c81d24441e9000c011100300b4003d40d0b0041c0f01002041000301d514241d0303030240780c0051154120900d0300c2ca05954080980c4c0203604d094800ca0b020b40540101c00d00c40c1e030a1034250b160654003661801d1615a5048044100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 884401267 1250 884400017 884400019
    0x30e1501051504030602160210020708150a02090a0b0a0e0904020d02040c0e150d05011d010314071203020a060506061c05060310060e04030e150a120b090901090b010807080c 76
    0xd0000206060b861001214059500228295030740c03900991868106100070100301d00840c00700809154080c80440c050040d41c00320f00140c2200340380700844c80710303170340f400b5284c07208180c1c0c03c000040c050b03030701c489898000f406134442c015159401d0341800b80c0119035448103540118155001c010046c0e484001c150748480e07049600051280343c203d0708441c036030014000b481e0803003458040d000d214050b1a0141c410381102510501c4a40e032144034924146000400c1c0102e6100b0b01d030014000118401000c01407602010122034000c1e944051681e0081c200200c1a005030308440c00312801c0c418140074403948070000703030740300c030300d840e034522540c00e02001180861200d9540e50404221503039400e0000000107544294284121900e8075143d56155900fa94110301280d4428070b0341c0f82c80d013422032041109000c40907805003403508005c029507409040c0b10001000035a500301e6442e0347c1e0780741461580140e64010000512610514090311049010307044103070280d2181c4420020035a000901003072080c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 884402517 1250 884401267 884401279
    0x10605010e090a200c070f1514070503040e0f0906010b090409023d021903030f0f1d010f020c0307060b0102070b07060b010e010f0822050a060507030e150105 69
    0x83e03603a1011004240c2c3c0c01c0382c5070000041c0340d07041c40400c0c3c00394040c3c1030380c114107019216200c3c0c0e40c0042c01a1041b10748a00402c0c101c0d0b0951500e0064014065980500c1c2c5145586140c00e4007680ca4500b1b5a110350400c902c0100d08a0602c1011960310380d00301e0f80002c111009007403039411700701c9189990007480b42c0390b0722954a418921085440c2d00c0303005803c000e0000480240c40d4140f58200300390340c50004000e001c0c03001010500c00350700c1c8002074001c0320490303040b8a2020040c198030110041c221104100d004280c94801b4582c002c04103100340e40030004a8119111418060354929017076a104817000002c1c80c2c0144034084100c00c0110840b45016030281002072a6068400140e051051315444440d1200700411102c05000f8990045900d03403000340d81c2c03070104000100c01560060003500c40b03400010f81c40c000060704440d0098140c18445040b601741500382003540e680d1458004900d5040380d600b9107440030321110300c2c0c240c040c1d0024801403001400e58002302641600b464181446080e1081d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 884403767 1250 884402517 884402521
    0x1b060a0f020a090e1902031501020f15040314120901062306030121051e070509070818010f090302030d20120a090f05060405070e01060210020f0c010e1e010605010e09 73
    0x1700100140720401c1d100c00c5025903c3e880c1a00002c0303000041000c90758051301900181c0d42c50104041044507543c1c9010340419a20340312074904448200740f403024851000410455080800050813507588240c1d29413002240701800c0041d003610b089050308001c7d50841d0700070084c0d0015626203040d241580d40d0098251900e01881d20400201105000301904601500b040e0003000c1207084030703201e0303940300d14000c2b511455036134814071868510032104480062000400b20707610020009101300da010700c2400101d461041e0904400031642030190860150f480011080000605070190340d04182d4494036007001044101f5003c0741c14400c017400c0c40c8950101b90000b0740c0c400c000d45d00c03c07143c580c0c10540e440d01c3d20045140090ba01d201c10784060307034203215410000850400d9035041078103039915540034002c40c00110011074041d4001c4601e0b5141e21707000b4080e4401d104800d11030b06100807a0369004000c90b1642c076032030650951403288401c940ea410000305011356600140c2c1000108400d507842d0708a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 884405017 1250 884403767 884403781
    0xf090e032a1507050a032003010f030c080c0f0d030e06271c020603100b040b04050127060c0f061422020915041e0605120114011a1b060a0f020a090e 65
    0x200e0b015007c00c41c564100400045010704000c3c1c009000c1c0e81c4100c0700d40108903103030007415959000e2207800e9079000c11000020300c0e4500300040c407644807074403a04100100389140000034016401c01a00203040b0103c20011703100d440030300d0b6a8803000039030a4440c0c5015044000f01c131807055104442c0030f40038034030000208216144100108004102c14458652201e40b0b411080c20b25500074420307a030000302503c45a44a0120500700d40720600352020701901d4591401409540c2c1148510f010754a03207681c130307000002041031402003043c0e1201182c445c546a240090304442c0391822208049002c4082100c1000187c80b8150885e8100c2c01c03000da4003600d40c1c1010001000b82a8450760280c503c1c01094820b5000754070798001e14151507040b5040e00d2003101c0c0c8483d00d0b00300c0740d400c0c0303c0400da110058010000c903600030708035050705282d1020483c0b89c405558110340c1c0600302c000c150101540010108440e1280070710801c00042e88061080d4507210044d84010559200c1d400741501c0c020340b01000c2042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 884406267 1250 884405017 884405051
    0x209040609170409021e181207170307020405010e040512030a060302030a060c030c050f041511070e0103030e1807031523040f060f090e032a1507050a03 67
    0x1030301070301124030350f120748800f40780d4040d400c40d0414440c082c05903c0101c004280c1503085e030b184c01103004e0590360f4403050141000a800100032140c4071038040d003c0701190700d1545403d07810345443c181d0011a0749240502c148004c0740d178142d004d4071200c1e01035000d010000310301040303440781003071190244ed4403520344102540050405500c001d44c5840381604070303020420300c0e8010541d412600c0d2010003505070900800e8481d48104180341c101058200018085080307000910042070b5040d1604d42d40303e10110308c9442c07600020750450440b0003820401001013541c400c080c07008034442a50881e1700c1c54060300100c00404406003652081c50b40710201481000030141d00c07900200130070075144884882c040c24049440c000b880c441e5006504101000c2d0110300ba6029030f40440d0140f0611004583c03820400da002130089e070b24840b982d40010000e950800101480d2908407400410311105010400c031030880ca4125980c242c0c01010002008003d807154000003500d0f01c18445080c04502c2000882603114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 884407517 1250 884406267 884406293
    0x5090a080307170106030c080601050a020304030222110316021902210d0e030606040603030c02061b0303010308030609071d0607020a03051005010f06030501030c06120e0a03050c1005040209040609 86
    0x6a40400c4030000071442e6060700f11821f03120203a203070584241c48002c01107078a803064040080159004000030401030a01300c00d0503401c4818041c0d400404400b4070703e0101929030004902075101004018030456883d4041d0318500f0380b81c14002030841e8140c44005584484046401910503042c10050086020784014580240103000055034960013001c44050010300c01100750314024400c0300001409402c042c89078505981c0c060f1a400b118444030f50810190f9441003443d1000c078650b500041c405141c041010318003079032080e030440c2d0301c0346080000e0cc12a108004c0c20072080001e10480103101110004032000860000c1d22002e594a0031400032a0410104d03a01c004d102d03109035a540c50182c0d41d2980028140c891025020448680d03803081203059400c280000740c8001114032003080158090322440c09000e06080010504101c00303001d150400c100c0300030580101d840001c980c408101c0c184540340010740b04030000c00c284c0c24184c002c1541e40000500046c03c856407040e02006000801c0900c1d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 884408767 1250 884407517 884407547
    0xc0f0409021f2c0d080307140406030c0e0609090115020102210f012306130902070b07090f06020705090705130303090e0f24010e030d0c021305090a080307 68
    0x3082d080c8502d100103004031003e980002403e140810b44036000e120502c62030904040080c103151103c0c0090701c0b90080f07580302801501c01d0042d0342034040715403080703013001e04001c19031501d001440e0f40d04048042d200c200080300840c8100310802c1248416a206096141500c03a10000d07280310144031002680203106019900c4001d080d03c1a0408880c044e19421900c6107813000b000f000603980c0d456080b100090b043c03214078522096800d040c00c5e00d003085c3c0b0141400c00070840081601e203a4542c040c508980c0400010707500d6002e00d100700079540780c011881c0c00052903503444100c08245024002502c4181c24001c0a12400900010505042c411401c0d81d441d40c81d0101c03250192603880c5005041d07040d03070303100d054801d0a050002911f10700b4502c909504c1104d43c2101000d807034040d240000c140c04a0905a00d0601c00c0f105178141c1541c4040140020140300e90b110060340340411700402c40140c030f00b9107000ca0218108410088000e4010580b90040d5504c05005500c0791152501a120300400000d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 884410017 1250 884408767 884408809
    0x30f15100e1618090e0c030c06030402010813020f100e12030c190602070204110c010e21030403090305100f06090513081605151e0c04120c090c200c0f040902 69
    0x4d024000002c11041b1014004804840c4828542e000b8000e09000469020b030109101d800000c0d14207038180100c035103040c8014200403008400e900015000900040907400043c961040d03219039042c104560003039a241d0000a500342440b0a0805903158880c03940480200c4401200d0004c003c040d40560303610550080051003101c000d00c00b010f2a030303008103c2201d142e6080000c02070300d6002c00729410503c0b103180349000b050404180003000c51540050022170070400380000010100320144004403415000400210300140300c1c2c1c1c03284081d9016034015008180c582028040e90001099a03004d4540e0301c1200e4940b142d0350140106050488214082d01d14002d060749842600307585100d840c4108820384101d40c2c404a1000134240300301c0100d61418400d54200300520154800b0380004510310303c28510072407080c0d1500b4180060392501ca000340089100010002003040000100100b1055000000d1140e00030300340c001a9111517a000060096503104845415900e801d01c400312560801480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 884411267 1250 884410017 884410031
    0x180111010e0a030f030203130204020a0c020405100602150f18120708040612021c0b040f1b0801080d0906030906090821010b0903060a0b030f15100e161809 68
    0x2150b0340303400114408500140041d450048200c1c0039209803401400c00401c01d8286040319400d100003584044404000e1000c10320f000c40060b80ca81c043c8901c42c220802894212903c0c1000c0030b40380c2100354246a00c2040c00d03904009002d420300030f01540c462000104803400d080740321601e50404140d080c5505200c00002031a400748a00d10b401002280d090399985503282d40c0d001e08007412070140350303409454206040f0404240d10354a0f041845136820040000441120104000040351451982060940c225449250b800ca420804d4103005100f0500138060f0741143d00c00043c220441402241d0a041e503446501e0184035690780300c0769a080e80010000c0e90b90054040b25880c41195100e14940d10b4070f154008030302c0178000c01c152040c0b2107024009141d10740b01c400c0360001a000300041aa018400c07480710304400f080401080d0045100c2080403044c81c01c1030083c0c10401d45940c0c01c0141030b411168203128100801c079040e010240410301e88441405101840055002c195611180d2183d04041e8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 884412517 1250 884411267 884411291
    0x1c061505120c120f0709050609100f0504051c050c030106050312070302010623040f020a1b020d0b0705180a0612051f080f0f2e0f0906050403030e0a0818011101 70
    0xb00b46008600310307141c0406c080d589901304483d03841074510079600030100031241d2000c540100c0c1d0b1100d12500c01e040450400361a42c01003280e0f82e03802c00f206002c020511042c241403020500c204102684107600a00071f007130920010075030703801d6000d01840e4060344c00110321052520130341c0a1409891070940d206e241012610041600c013400050441c0b04a06d40350f00c5541e604900d01c01c40d101d003506600c0364080341400f01c410306000300034200e05a80048410040070000741e9074801043c4161203607100c1d141c554090702108900400a01d0809000340201c0d041406a80d811115207244000400b101240944d9280103030610100200920002d94040170804920141d011075601c04842d030b09021610800c594000c074550b60341074003030070440e00803691820110310441c4000345164800b41c203502064098140e1099011903008980030380d040303582c47e03040c0800c25516005608403c00e6040042c113002e181615100fa1511a2041c103169451508041240e143d004a0641c041260160001c201c1d842542c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 884413767 1250 884412517 884412541
    0x180a03060c02061602060c070219090212090d080c07060b03010c0e10020102181c0c030c1401020a05060612010603080c0d081008070513020904021c061505120c12 71
    0x100000d800b500502c40004d0091000d49000b0300149043d030300524490301c0e0000d40a19550114a090760011500002d80381c9080c0710b404294000c1084500040e607034030520a0f50946220003130103c481c00d80008880299180e4004441c64002c0030b0a020156240990728000d00103184901ca41c1d5019401e003280d0b0294290800b031101007100003035440100360500060120300301d00c46c1503180010300c0c0c4076030344050b001d0401401c1d0b28441c80041c050628548500d031074540b4202101e42c421100c0d6220400c0a21031510302c05200c1d10408402c0c0002c00d40c00a6603500e00351500c100404050065501e00000502c1160942001e00215041400c142d603450142083c2510f41c281c0c0700c54280815550300c0458003c04109a64504683e0030002401c1503604040c100030b04081c4480303004030b40030f40a100307296003a590741c4010016146003551407192281c44028410030703640c0c99401411610303c060300c0380d04516080b408452100c4000417101700c05955410032002d6a00804100c80a0208880304104460310301e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 884415017 1250 884413767 884413781
    0x320618030604050601050f04060303140903070f08060a0c03020a0e12160306020d0509070f032a120201030509120403060e031917060a06090902090f03100605090105040908070305180a0306 82
    0x3034901f40c020126903400d1206075491444003c0006009400b03403030100c0d00c3c03c2c02800000c10000c05440d1f103250750700c240d403000c0c10043e00000720340e030840c405102c144085481050302000c0541825070515003095400b40c002800360f24042d015200e000c224802c01002840484001002101352854090f200e040c010000d40000c207144014503c3c090116103180c4000540c8000c131801b1911110140c0d00b56950601821100100c44148900034408002006a503082c0303000a054003030002d01801c2054000102030350f83c003030400c030f8a42d00308004000c0c40b50a603000b10340659811807004101c1d6105c1e03d42c020b1851140360320f000c0c00904080310000010703610003030002c01d174218980751b2280d68079103000304607506c1c065115500115a052104001c0c10501c0d402a051041008215140c82d480d02d0010904000c15051000e82180d5500d000b40003034900811344602512040d00c003004001e440f036480a803035114a2402505000c07021031030820502e02c00c0881881c0708800381c4408440740d5a03207001c602070428 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 884416267 1250 884415017 884415019
    0x110a0612050f040506071b06051303022103130302100c110d0801081005090f0a03030f14040c120f0c1d06061603110f0f0732061803060405060105 64
    0x2803074046028005082c003074501690b00200581496240da14040e250102e0244c0701001b94201c00e490440400e015115a074896442d032540c0101814251074002d003021005c40503407046a80c410a08491014184243ca500c803826400300d02c0d45820b07a040c1603260244009884185c0c5060402c40c0e100103a1001340c1459549054085484641c564102600c4010090143d00c070280c1c0012003c1005044d0360f08000e40044804003583c1c030701c510981c289800c0c0310301244d0940200c1d8844000c044074220394400c4440322a0220840c1802e4105680c60861501844c429559a858013918441c2400718000345040c030141c0c0702d0507401aa90f030f1078141c482a01d040e8032101c2028590480068142d06012044882140a0303241024400354159019911441c030b030010010248107002d8840001e08003002888003801001000301445072a1142288181c185503810950382071151545c00080390700c1001c01a0885000c48445031035244118144002c100c00340000ba6040c4134020901061000201c0d201f0305035a4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 884417517 1250 884416267 884416271
    0x81b0409182306070c1a150901080712081b07031407090b0105091e10020109020a05030a0b160210020a0503150a0b120a0921080708040c0b07110a0612 66
    0x3082d00700c040069001c8250300d0101d0f080a40051400c5108000204d0020300c14072071074a001c205040110b891020481d85059180300414803254145010704806004220140003005800d0500411107543c0c502d4902c0100741070008204266100060207002c1901982d04045030016903590070444500c0c00e802050300401e0007001d002040d1441a8020000b0340c1c017061b1501898420020700784081050560300c4a101181001c11340d070b106070394440c00d402038070360282d0001c1244d608a0041210300c5047e81d0000d84294840c005503000103c044480070b41c001111156002c00084803d8240e00788407281d4007441106100281d50150190040d026501031171080742512400c2007140300703104000c1043d019500054605000040c0280480030b00070f503204240d136a01040760340fa182da42d014030340c0469000002100342c03854921100341e4008161a40041103107003414490810f6286d42c004d48040b1f004902000c10002540300920042d90101d100058000c1c150003921135903240c0080400b0a91107441c01c41c94 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 884418767 1250 884417517 884417543
    0xa020d03020906040e13140610050d030e060a051209030325020c0d0807122c06070219060219030503010909210207060207090e0606010302090d060204141807081b040918 74
    0x31500141180c8110000c41d405c9e24194100b20401440c1d80306080b04408001078560416515210400600310046c3ca80c0c88003619a0f20403111503c4503080185441e0f803a920602c200000d41c074007411800003103600582904030908840388120f0a084002e44455080303111701c4803031310802551b0740c020a461341c04cc003602c1c1881ca140e51000c950800b001d40700620518a00014010b03113201c00f41d20014800c8000b4801c901d031940990115015000d901202c008504900700c0401803d6014010655403040722154582001c4165a02a100d070006000740750020344d491843c81c042240f0f41240c9140051a08d401030103044520310b00950780c20690180c180180122500040d41c0b521034010011101400005070159581e0f00c00114000d400558110750310014140140c80842c1040c402000500360f002104804481800e0034482c1d020007815420f500c5400440401086960212042e80c0007044e087c0c25014210808003004079034000c941001c600241741004041416000150301501036108006075141c030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 884420017 1250 884418767 884418803
    0x41401030e011802190515040e07091206150305010213031403040f0b0c0102070804180510050d03120b0319050d020d05040e060d0f03170109020a020d03020906040e13 73
    0xc0c45080403e40c900346407990803000149013101400c3e040e49203031484000c0140d80e440000d4080c1110040c0600c0044001500340104504408520f510203507600304400e010303181c41184120400c4e4494003800c0c030303a61620340d801d03a940d2401c030450055800000a544405201c0f2008101d22240e10003107071031017184034000c100b881c400300079542140e080c0b000d1030060031720f072001044566208040da20620b560801400001558400c040c0020344903182d41c0d002c14401107200c000440e500544012000000e80d04204801d50701c1611007504103502d031070314035100e000404100c1c001d006410340e0705503d40038101c6420b03030741921480b4070b0880e507024404440000010000c1a81c4a6000303074489400554200003d111850282041c190481409401091624410f4072403184404442c00110300040310303020b09260201251508a000d01903080086290140920307004c3d5407180d040c1880c200741600840c081400c4e43d1034105560050604c01098405440d103031002096082102404540d404c012500309815 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 884421267 1250 884420017 884420021
    0x24030610140d0902030c0d0521070c0b0903010b041b031409060103020904030e0a03080a030e0111030105150c07030b090d050403020913080706061806050f09040308060a0b041401030e01 81
    0x2400101d003810b46048480c070480c0303010b008141001c0c0d03014811090030100d00d4030f403071088038000d500480182645401c2e007800740c0c200e413121908204541105100c000003050074280340404803292038850701e03078850010780400d001d4544110341c15480b6150441101100340403180200c00c00a01d50f8040012003c154140c09500760300f0380b281181544064010700041c00c103107080b190003601074200b071082041d080c40001c400321f40a4008443c070b4240803484502c181e4042c00340c4c4d0105407400f0024000707800000c980084a02051182900c40da42400462101003108002c407056809110261004181c0300d080051540341e040d940d03540588500740a1130703c80342c0310300151019291b000f8500201500c942000611610b01c043c0286ca00b40410090940021100c2c4107240081500d402c400c500c1c9000e030b812a00071500e06a0145000d076035030508001a0380d07141100c880d405941800c00310a1038403200081001c041c0303540c1007448598000503000c100003141c281c0b01c20300a1400d0341d0620100c407120f000542 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 884422517 1250 884421267 884421287
    0x4080c0910030210120c03060302040605010203070f06180816020a0b0f19120e1b01050a022104030506090109061a010512220b01030204060b09091524030610 69
    0x81c920044800c00c0c001441d100c1d103160740c11103203458110365070a400b80e4034038210b0300d005a0700400700c0d6030b41d0402c00c02c504060044c40018a02400a1810001c40e1b442d20144900036180050400d545d5032007030031603501900c40e1a60740c243c10038811038840c0600700b0201141c2c1ca00100503441142080400614060040100c2d02800c83d24403140b403c020010b208403c2d0074620600ca141440320405c0c0325030000d03601c2d1080c000300c0300b0b5000c000e10010080b50520300030b00c2003174800f0b1410060b00b00011005a5000141c400c8a21602c0c1018046490010900291802640c00080c1303107000b40c00612028810540162140da801100b08204d9208014004900380103151296030118001348600f030241f00c1249803042d07100ca180c0e02d00900c00a0069862245814106070440d00b10311054014000d500341031140c80060488889011702d001003000c001307000c001000b0b24505030304d40000c8084405450f0200b9260083d0340078403850701c000c940c0c07a81e0261960000c5808034002d4031a01c0c60b41410604c01d60980c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 884423767 1250 884422517 884422531
    0x6260f1807150c2d1118131101141602030705060a050c0c0109050a03150e01020d0204030302150f040206030405011415040b0f010518030111070b1905090c04020d0e010603060204080c09 81
    0x316122100c3c3d61040e2005050198140c0d200d91240040c0d0500c1c001c03c58214401c0c145038210742a0001c0d01e1414100d040603041c8c2c1e1034100401c0c00c24200c00441c0307030750484011030603c400101e8000041c5c03000900d040090f41085400900210303503040c0300c941000141c00315256020039990880c103120011524071031244a1947d1048960740104003182c845045c000b030100030840045006c1d0405074082e03099920035090746054640c000f4080082c15418002000f1103143c01d2400450740c00c00044d000c500a1004d80080d202d100000701040c10404d0941c000c1c0350000759000c48480740e25004080302000c1401160150040d810080101c41502e48102108003144058450904000510000039010000c4601e195010340d13071040b4200940d28010041c1801522400e800025032425030400461000184d05803001c041c00d0005004a02d82c0200d521158001c0030b680c01a00c0e0554a4400e001a0280c0d0020f105030794030f0000b012050111a80080c41910302034001ca5000709811001d201c0144021a003071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 884425017 1250 884423767 884423843
    0x3021f050d0f0207050706050903101406040b01020f060702010605090105100807050a090b040b0301050a081506060d060302040c080402031e12090a0f06260f1807150c 73
    0x9188078184950010340030220300d80b401802d04200e41c2d01c0c14901340ca0f44d000a00801c00c04580a80c4502d0b0800609100c00b001450904c42042c0c4400d01203000200501580d1080f51210070f0303149541d01c01c008006540046000b203a10508040c040a070003001540074041c0184000d5001003542d052500340b00102680716642c0f04119591001c045805400001c2c0b09000c11601ca080041c0c101980750140001c4c0100d10115179036545040c0401070003410b25404401660030148200100001003a000c50b0b1107001500c5483e526148060140c006001580009510500e03152508072003952004915201d41c0c0300340c0855191284c1c00c2c01d00341101c01d4211180d4102e510400c40c202c40424250003800903580041c241c4150640c6401e46212211842d80000002507011100b060110701416041c0d1810844000e45803814106010021440d11009040c070004c11503231201d4101401c020001100208448807814045e91040f820040420181c0c54040d0340a680a580d16900e2503120280c05001141c04030039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 884426267 1250 884425017 884425027
    0x30305250c0305040906030b090f0d05040603090804090507031a01110a1707050d05030a1a010e060304230a0b06100e01180e0c1213021c061b0903021f05 67
    0x100700c0d00100080300c2102000300603c400240e0b800c0e140100c001541c411107545500745002070717544d450709881011f0b0100590004c800e40030b5041d0404220b4050f01d01601d400f250348500760034502c080d440350f640302c0c450141c45d1104101219070f25078003008102c1c11445088a501861200444500c41606040707003a9821941a5800003042068607440905280d41101c0c144407103510345030f007803640c860804c10100d40f0000c2048503041c1d09108403000d00c904200406160801c03540020101d414402e4110302440000000c02c050100a1040610b0350000044022916500002d9241c980c0e40c0705104980071181ca802045c0d0510b40074040340c3c4540220355402d20805096001107800b101030139031001c1a0741c4840c02c042840451070b0902d0303214500030b0420304d0791681d0158160000420081c103d40c09004644501801656403910503424000303948071100010b1071904181c0c004000103800518107038414802c42d645281c00450500450380211840c0e181c80c42c0074088044075000d0340400e00c002403402c0207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 884427517 1250 884426267 884426341
    0x62a0203030a03021c02040e1b0304080f0705010e010923070b0306062809150809062802030f06040b01050c2a130e010f0204180c051c09030305 63
    0x101500508001708541d481140000c4001000c980c0700c2c2d00b140080a00700c901300b0107039992108045110303540300c2000324035600d030640390a0403074059a02540303441c440010301101880000d4101503030049107440200542c0b6424501210f90a1065940002ea580c41030300e00c8100d4900465103804559a480e85546581c3c1d4031010001168041810160101c02d0300c42d02061015003c5003160400e520f54803900f43c4c0b42e0030300408a0741030040c60f0f04041001600010800540c0307002c551103401c18900414101505492008440c1410045283c01d00c807520210410100005401c506405500e0549041100d00000301c01100c003031184902c440a0741d0701a030903200c08070003005481c1d103070040d821601494068034000086d21a9800e1411101280c4d140c43c18030354140800c0c030511041e851003007001c40c44c1524103230904407402d2851084208180c2e071070640c1c400d11801941182d070b03a030030b01c03c403000385810781110f014004140445040e400a8030780000500340c040b400903640307082d1130011010860000841 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 884428767 1250 884427517 884427521
    0x10207030f1118070206060f0d0f03080c1e0919080a0308060a051507050d0305271c020f0106060201050c12060d020405070c02192d0f062a0203030a03 66
    0x342c002e0340150504545102c01c003034159074540140050760141860f400c0601c00c01008800c1ca80c0e0240c425000e007190400001c0c04543c0741800760747c1c103040500303a503604c150929160b80108180641c030b403100045d0300042c1c0c040100081c5440f01e02191401100d1001140941c00d4120900440f02c0c5a0310482101022038060304255900504c020600d0300e00d40c1d12070002c500041141c0118000c044c0e008a83d0100b005820b112400f0300c40720340e1400304484c2c940140001120510441b184001c02283e02c111008110300313001d40a4101599000c40c80200c0c04200000c2da43d8044c040084e0300c5500e03150004c140d9910601829002d100a55145820b0001080c8a0b4030341d0030000e018694840e0890311003000580b214090381d44142a26180d20340700380f9190051180c0c105241300b0300c1007001441c1105004502c2d98400c0307030315400300704a85510584001c0c030030049100c1f5030380c100031000c2140c040005030440d40403c5c1c01441844c0e56852903595105482c19081b02100510300950603082440714443c0e540c842c2e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 884430017 1250 884428767 884428793
    0x60c0312020c0d05250609020f090c09010f111501082b03470607021f11060c0304033c030f0908040e011a12043e010207030f 55
    0x319803d24001c050034182d565021682d0141120754a84603e01c0c7e0302549404a1101c0451100751540c1ca80b524140d404481540f090b130502c581400000d09403500d40c11b21405144000c031100e00c044401d400c51441140003503500912031340303520303205800d00301d8a05a00c284061346607195a602c03001c0d0144202d1001e402800d4441c403844109403030306007110f406002c0e500002c0c0d002d04c4104218101e8190b8841c2071624002c071658128012181000010b0041e26240100b80c5070100598020311028440d20007102c07840c0301400640001d00c504000e0040d80003110005602a520a44aa034501004a8100344010308401e0200c151200c07510407204a804860704442680c1079541350001c0c01031540e004950455520100a4076483d5011800b0701c00b11844500c500c3c05030160032200300511050101c038000510580a10007038a00302c1c0b9001c14200030040044042641290035282c05102c585030a80400020100c00030740d0070a403894800c1d21a5002140100a507a009205201c54000b80d4440403c0c100072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 884431267 1250 884430017 884430037
    0x2070e1302011403070810080c090621120a03060509060f090901060f0b18061606110d0212152d06040b27090112030c11030304060c0312020c0d05 64
    0x244a04480c0f11101440c0210300c14945a103078007100e4201401d0007514100f02d034201903050343c84041307501e6140d560b107a801765200c842140c195200700c0f0604410350b2003000e4444001c0301031090080b0350fa0800b100c0c00240c00c1c02041a5010415203543e0410010f0061098032a030741c202c10301c5180c502044c10170501080e4072019070070010483c10358400c1003104c0b2402c56803000c00b4001011400d1a001c0c000c00c1101042d030082100c126090150280d03800078160795038480101410780d40d112128030581140140c503101164000219141d0410702ca610710144000c8a108032840301010f41042a4500710007084943d0501208100303c50041d003505c4603d0750100c078041c0368070000520001440f9501c00004001141448002e00c0100110340100b4078a14881b105282c800d04e421030040c0108119400c4101c00f194142c50485038a5019061103402d0f43e94200303546805010000f40491840d403c003019103c3c2038401d81d43c0d042400000c4001c0c1081b40200041140c490f00f16220500d0500c1c843c03006080c540346 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 884432517 1250 884431267 884431277
    0x90403020c03070605270901060c15020307030506040e0a11190f090606110d021519053d171203070201050a05070c020a0e0a06031a04050d02070e130201 67
    0x1c49400180c43c00119502001c0025400a44031083c13003d844c030345032152443c20074441406468a40060201d1005002d030f00704100841d00548140075070b0a5864085440c00801150303070742460341c0c0090103803600303d071110700031030402c081c070324404200040c41c02c0e800c3c1e0044e51038404d04907440c08103c1c10b00000001c0c104c080310000404501043e021100b4401003c1ca041d00040b4903140c0382d00a00818041c505690707040e0441c15071002c40503000700b0b896000728003404100706643d503615980742d480f140031b0302c00e2441e103850882044910018002e5807040001c103082102448240020504a5103c0d600703050912815452800c000f2490f581030a030844030340b404151040010328008100180c1c100310b40000050391640709101802d00c0d10701c68590071038440d00d4036240c00d00480d008500d0580c0e0758806c0100742c900c031900041001d511684030a0196910880720320241c000d001011103a42d00076201507510b0b000d130011200b10180009845000c035542100c05030019035400c1c0451580c08003000007607060003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 884433767 1250 884432517 884432533
    0x80312010b031b19080f070203070609140f0d020708030a0e06030403030603050a110118032109080a0308150a050913020f0d0501090b0a02040b0909040f08070302060406050c1809040302 81
    0x4140000941603400301070111100030900c1c51130090602c0b0025000d58901070710281031208966010007151141900301601043d950401e242500b1204403640e800d544e603005030820b14664801c0411905013801d203a608680b0f41e151030700d028039203900c209910440841d58400f00c40329103003810405194424040d00b000a4180e03600e445040c206000c040c011100b080c04100c801c2510768200d02d08041c00566400820411780c02c681e07520b04280f022108000c52446100650b580840c8202d041c00007070301e0024241ca08411891030080c1c5210b2041c0e61b0315006401e4045182c0443c203000c05080c0446400a01c0d55205032038181102002c03400300c0e141640c0008401d03070444d03e15114401c4820540b0300c81d20000524150300d003011602698044c0948581c2c03130041108100840d102e500b030300c2070b08904840341d400079203032072819600c03030510114010030511000c00c945007415004608181300f20300451013408030f0303a00c100c4861000d100707070400c0700710b000b9090b88005081d0a100c8111b9a01c24400c0c012542e1038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 884435017 1250 884433767 884433811
    0x105010203181f05030906070503061320040f03030e03060702031e0708040b04090c030c0e0f0609090a050609071701090b0d051c0e030609070302120304210c080312010b03 75
    0x5481d20403c2501260f800801d00070704c0001003044982c000755501c1c00c1030a40c1800d0000030a804d0480035020829620b41ea511529142030116036100e14919044903591180c0c3d8030050007031000c1d04c0c4800e4000c03031808004800107040102d0428030031215075000c1c41c90f094a0284034015582c80000c090b0700c80009016400c00100c83c14001d02c040c0142035038444d05d4501e401402c1090b100c0290480040504007060880b08035080216105205000c0703c41356200340390000030031814003940510755446040d007402c1c406250540d6200703e0064805444480c440d0340c036050244c4403a404200c3d08502d450b141001042003508540c821640f014006041c0c1910018503280d8a2914000081000c0c614165104082c45150080466035008400b5009443e0500e80aa51503440d01c440384800303030088400c161041c42c0741c003040c404c48004c1c00341c40910400d504144010071042e1020800115016546580b000c00c2e070b194000251083e441c1e152510142c16801c24543e8011500301904103118a452807a40c0400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 884436267 1250 884435017 884435059
    0x140f0304060c060b031b12030d050a0c02210307051c0903110607030614130908041508130803061909021606050c0316080403090f030506060a0e010501020318 69
    0x6007403695800070400c40c14144242101d429101c0b46110307034090080182e00307003131603640307601d0000c1b080380c00c00907003c2402002405c501c2001c221401080c82c01c01009080300c025030240803800900e6003242c1305418100740420301c0400280e05210709403414130003e541e003845800100100c035411218000c001c100c0c0400e03001581d041c2c2d80100c012440c0d100c001c001404003080703003039400106440c0500c03482c0d10741101901100c00ca448243c1c001c40030300d0716502c258151500705100750b56202d0061a52581e45018018080410014030f0b00000c60031004100b0070300c0b10002007505e03260052100c0d85907884500030071104444801d500b14846002c50800181c0c0b0030184040c201120100021011018291500c2412150700038140010f0300418814403a001440d10406290303c80c0504103500142c03100d0500b510b40000560060403981400b1302c0110070400c0c0424000c1c003c07201079510f48031076500e91680c905103003401d0040a0040c0d00070700c041100d061121850007008000070b464500f94a502d003c0450b2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 884437517 1250 884436267 884436269
    0x4020103180b0916290403171b0309010f03051015020f0f030c060c0d090804032d03020d120e060a020301170604030206010501030e15040b09210403140f0304 69
    0x240340b24a40300f04400c01a084c082d0551182d031011420341083e0030b04000e0031458881049004008020400906503540a8030449001e940c00505802a1000344040d80100c3ea00c8440300701e0034280c070300b03042810000700002621001c3c2e005031100b046100c0303100821401020004d040140d100e204c0342001401c0c0c03209010707186100301c507a40600116603ca048541c40d006500c00c0ea60303d41d6008200856982402064080d000b400c240c1d021590340410080200103480c401c00301900f001000900002000b01e48450454400040c1e15107100300e0248411640704890001c80140140e080708007910302d07161040740e042c44580340a280000300190031607460f5151140840380c680f00720741c0c00001488100450003080d4401c5c00e01000401041c64140e5009450f8031046c803c46052640324940c2020708070040c48216124a040b104006281c949400c00180c001406d0750407d02c24041c4a20f24500708c071248100d0740400e2500e0000a01d001d00d15030b520720041100d45185120350140c180010a40803041c40180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 884438767 1250 884437517 884437523
    0x90d0510110c01060608010506040b03060307030c093215040e0a0b100e040c0e04080f1306182108041d04060c0503130f080405101e080103020102150402010318 70
    0x142c03100e480d01451400c407542500001d003400301c1d10004211b150b0303036801102e0540c1c2c006030080f0303120346813a00841d2030080180c0000742580088139003c200d1800f140d200a4260b80707032224058400010a0a0f8103903030508842000001207080300107120355684560040134070202030710024104000444c0706040c190707451000c54004036100d0034824810502040c20000c0c3c503082440c24054100341e139a404541040c0d1040303000c481d0040000605002041d03060742c01c031480741d104c450355030006d041c0b9120303c030341250180f40701056445001100d0750b08910100001d032001074030500c17540d040746c502204c803000800404803415031041002150b03004c0348805100001d0000da1901616040501c0e0030000d82c1c0070940754208114040c401c001c43c461081540148658022414400d8100181406200746c030a5820107608a405030300d00070070b51a804407010b0010451401d5000c1c802c1d40c4102c00310b0320b0030001e100c0640181e20405445018141d1600f40d19000b07441410b0001e40100c1c0101c1d4140d24400011080d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 884440017 1250 884438767 884438801
    0x5030301080111130608070c15020913020a020304210c03141009020915181003060b03190803090109050d0c11010305060105040b0c010f0513170906090d0510 69
    0x41018203401d009034840240c4003510a400d08001494071450840d540c0f01c1d42c010082c0c0751b00402d4405000d2a40d011031190410030380d84006012030070344000380d0701610155008840300e2820410000052003525620041503015500c0c103440e005407894001513200841c10303400c04881020001440d0038076a10300a505c100071202d5401d00a101c0642002200249041010f0a10400000603031302d10180d1584400040d50f144490b0100c0400f0940200011508811a8805502b84641e050312034081e8000c8900c00c6a051005038010018551141781040c0d181c0700700c100440403c000680c0d000c0107180c5c0301c0084000010700b00450b031111443c11481151b1140491502d403c680140484030581c615594820708043c000b500309030340001e200b40300e00e11a49e468071001007804243d1803400c0d009800135a800203814442814022001e10f001c05e03040b50304482912410b03840c103400141c14000d6a000140050086040414603404c1c090f600d22194001c89841c09846c0c01071041400511600000e81181514 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 884441267 1250 884440017 884440019
    0xe07060c03080a0207080a1202071209050a06030608070e311a06130b031e0c0a0e0c0901121e060305010506031f020c011d15180d0305040203031605030301 68
    0x40a0030b804005040c0c0300355240100010360100f0a07681c111002e5211500d852414150300c074041c00000d008600e402080b003031400180780720f0b03654400580c46c2624011a0030441c00740d602d06c1c06604841051203120896001224100100850350035400d500000189074800c4c05244c41d620756103003000014980c0c01341080c003190002401030900c42c1105610480c50900f0341e50174803c0000316039200900011545d96220300d03103210140c40920514405003038503403035041c0d04040c6103699511040704000d414002d106100001901c071541d811001c1c0980c03a00c4c00300c0e5142c200c80390011140020410b03074080119884a801050f0781d000a03082c3d00000b0410000010502d0441c0340c0340d425a9030203054a84a1b07800010520310041a400038821709940309000140e89000d900c21213809400e40781141000b009044264002e81c0d02c0c040761811604042d280010082d0351840e03005100c6511801c40d080040d4800d182624909010f5486980c1107400141200e042400490803080d500500000459a503000400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 884442517 1250 884441267 884441273
    0x30c030f03010e0a060503061501050409090605090105100303090e060a0f090b0a050f010e04021b030712110d051c0e0610211e0809040203040804031b06020616030e07060c 75
    0x884e82000340c4810a1040510b0b0800003682c90074050b2640f868041080d2151a01e0b0f80a281258028401ea01061101940d2030070414018402195020f0695007010000b43c00240003004000a80b039240d20b4450b84a41001d03c507c1c0b003c000208419081140380f80007080d102060300c4d40c00c0003803440580210700d1025041c184076100e582d952000e0f0180c2181444041503030307040b039980c1c80c407401d05640058951a00000482900950101d030314003e0100085a1051000b000701c0311010b5000e5842c4c01719500c41e641023041d82ca4403200d18120026030309204120034a8000c40040301e6030b280e0641d01084905248401074181001650f5161012020780380c00c000034020300008040810f51300380c00210360110340c1c4400788918112200600340441407401107040045250590740542e0026004548034134003890800001e92260006540201078218485601819001c440e8145c0d40c0581c0600a03a88604041c80000280402414280b54a801450320604810061240141003544e28180030305250700f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 884443767 1250 884442517 884442539
    0x10e060a1b0f0905060f1303030903140c09010308030a090c062304080604021207030605040c18051b0d090212030d0b1009142b02010f110a0b09030c030f0301 69
    0x1146401484100c01c4402d03070403a0030031080c2c0121003041c0c0701143d440f4a607051410300ca200d00306140c21103040009020007850750045e05a0240c912034840d40c0645080d0590b40ca03901c1d000e0380c0303c8a5010410074018800101404095504440c1d101c00205518000392350b00c08107e142c5401040009050b4019440310350b101d4800322641c4e280ca4200b09182c941000003454841c0740c0100302070b0262003c2d43c0643e40844082021000131b5410090400040c100f51604100c3c4030118030a1402c1d001080780783c00c890209900c00e4038080c03160b04291400c070601826400e000d68100c8903490b402103686540c0c480141e160040700d140c203900158040c55036941c080c0070000c201c6100071001401403507400504c0703106032740242040ac2540d8502e881901c03c24581000688101c0040195031540d803007020307070301010502c1050b091500b030340700f41c03103900d442d0440240c04c88040c0380d40300c011850365020200190100d07090381440c50b0014451810b50f071806403800b14191840d031140350a0b00d40c0ea41c1c00001040703e10805 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 884445017 1250 884443767 884443811
    0x290d0606051e011413031e0b09010e0c15070609020420271503041e030c1101050913050615360d060510091d0c04061511010e060a 57
    0x4e03020781000c070621452030050000e400018200c04241100300002d11000340d01211a5070301070f1002d139031482d2207241d0740d0203004c40512206552144072103000e0380c4c2c60003000c00c0d51340d51100240142001d0b102d07122034014041c0042c0c1681c0040d560b2942659003400240f842d100c1414043c40305a6440b440e40c170356003503002c2c2c00f0910b0354104480469542c0c990b5940740d0525058103404450b81d12602d46060410705000500042c0c4c40c441d000d00c2d40c2c1001c2642184807940303a17038044c25281105034030210064506100340c0660036401113901c2400c10303808401e40e0201c2d030032800c0a0580700070b0b120020460045030b0f000c41044000c0154501004800450881c1c0c42c1070491031744501110442c00300e00c0400c1c0750780d9988400400b4503441704001811903280e5072850009112101c4e05210f1241c04003602403031407206031541045805a5504541303542480c2c028442200c1c64542d0401484072000e0f4100c42c2c040301d01c0d92210f465521b8000788000c201c41009814040c03064150300007001141403415244899503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 884446267 1250 884445017 884445047
    0x90525080d0903080f0c15041a15060a09050a0303030b090a02120403050306011b0303051605090321041e0f2c07020a05061603290d0606051e01 63
    0x40301c1400107600001800c11a41e2201c0e11a80b05d03502c4400b05c001501a00050642da88941404a000c403e5030600386801f07107004108501940f5403041e0b09811501c01203a0b050103030500c80c0d42700740b20b60038040001d1441c5403062070200c8540d1344480001c1c80c0340046910130717400282c4882c502c42c090702d00820820b410201d040c104600d005102c13000d00040220051000d000d00801000040050340144a000e4403c00380e007800b03030002403ca25001d002424103490401140248140c0d225849000f4000c5501c5018000c0040035040309407050712413034007a001000f5a01420600c80050b1200240c0b2a05200c0081e080f10100c0d00790a0080d41c140f02222035119000c65501d01c806a0000350b6681c8201455585001c1208443da075110410703440d00c9404100103125101e0f00701082442d008086e40b2000f009035554040c800440d80344000d030044c2c00030514010780121000001e050ba4034001002240c4030748a20004034180f80e4450014450341c034422001e18201c9103129005400d036a00820920f05000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 884447517 1250 884446267 884446273
    0xd02031c020d0612030216060207030b01030b09010b0a030f03031a060d09020109050d060506040b0603040305040605030910090b0402031002031b0c0a02041d0724030c0309052508 78
    0x11903091540c980c0018140c009100641c00103069040822640026000d07009101c0400d4201003d864000e645c1c266061114202000c455000700300740d8070110b00c1e841100d4200c040810140d083da2604d18080e50081d140851940d616080e80c60541c486a1003507000b940941880c0030340800e86c3c1806800da8502c090000404079928100241c280d6586d02a18010000c144000550b0314003440107848001094020b1540700710400d100b401008100e41041d48100f0b4151020b100c1d00030300505006190105a0f40200490002c4c841803103610301c65005540e00403c0ea00c1180c944081300e5001c5003c664000d0306c00d54060210408000c1507090400032060b40b896103640462543c50103010640184201500510340c3c15000520540d40c80403c210100059400900402c10a4014241a07116501c81040450a405044000501071503807200d40d50b0f00b550f8800480d2221604850210010001e2146840c14195100c02181c0817800800c840b071080c8008985820f104148016203d00019884d4800c182581c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 884448767 1250 884447517 884447527
    0x618070602030435190c15050f160803180d02070f05010e01050706050a1e09050d0e010c0606080309010905032406010512070915020313050603070201020d050a060501020d0203 77
    0x82c070003001c00500007600ca141038901100911540901410302d4500350300d1031003218010071243c044039000308001d5101e054520300d40d5907604200306808000e04080c0300408d0040c0403141d201c1e2407080c02810f1310175015a092644a1195079402e009400c192400c5952030404060044601010801caa8180780140000c0440c14036000a501c950520741c01005d0400c20a40107250703844e401201038480c0640d00420510007440c214134868002c24550010354100c03c1d507542ca001030543c1f94400d140e03186811401811138034000040558040d0030704000c280c1007060801c0300b1008200680f2480029114003805180d0716070f00180010840c10f49900300da8442c3e040707400c400c00c802c050309c2c0b40c0c2460590980b9140d805680c4020060b205070242d83c0c01210710400c418104002d1507480082a015030341e142c0035448a010b00c1d80d204980c0e90140c0d9100303280c887d00c1401c0600c000d140c20300c00b03140c0c4985640300140c80c00b407140c0034481c1510019110700c072019450b410140031030342e014480314903503200c9840114104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 884450017 1250 884448767 884448779
    0x170703080a12020c03070b0723030402180a050a0615020a110607020d1101090f03120e1306031b0504020708040e10030204020c0604020a1a040b1b06180706020304 71
    0x500424840101011000141421440e0091a0070216003030400c00454955040344122a00c17a88031040c2203a907901c0260018000d20300808540021610b4500a244501841b0040f21003da1014009a9101c210110001c1041c42c8000440c1d1140740744c2180854641007804500c029141c094000030034400110150a8200d03074002010921240c005d200710710034451034808113520348154440070b0741100d51460b0460500841c00c0014036103501c20ba0720010030a40d034000e4400889403600004085070300e0990b10040d00c0744640086c0c9541c20700200b00000042d01c44d02c2e01c00c12541254003c445e0000701a007001030382208513290301d000304019038055140ca1017943d2981c00501c114020003105202c81d01c04101040a005144400b440e07010b00215900c2031640c80c025600c900032501207200310440700d404244440610300c0070403200c409501c010b040c5810112a00d4194010301c21010b545484440101c1a0800402c007031401680c4600000c4460b00c00c280a150611480d41c000d4030a41d03004102c20402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 884451267 1250 884450017 884450023
    0x51003150605161b0518150301050c1b0c09090a06142a0f121f03020906150f130503150405061b120f0108010e16030b090703060c020d080117 62
    0xb10a600c0114440c21302d04803440d842010040c0e4100c2c43d048038803083c142400ca01c011554501a2030b80000d81c130445d50111f0300b05803d0f82c008a0388081281414042102500c05c01451101d4006818007030340d20145d4040d000c42c000f1103048800365565881000c0c5e00050201501c15841c50030791000a0100504d000b800d044c02074020900200645141c1045280d079040301074003a40c501d002ca401c8885c0d41c4140384038142c181d011058404150a0f0030181701d6002500d0f0b011840c0b01101d601505407045c3d41c0d41c50040008044000020b00c2010104201007100c504c1e03c0d400408400030238918401e000d40c1485e0030b2528210782c10750f203003072030000460510003c80c17400541c1540c00700710241644001c00c80c240c01e1141d070340600c417405044015440c041c0103a610038031510506036a0400000c014000c1080307109569010030350741184d51668110014408a1081e0f0001c0e42e0003150002122003c6a4070f40d80c401c100c1d041e803000c3d840181c00c01101c089480d0380c001055801400700303012540c6200030b1b400c0a251 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 884452517 1250 884451267 884451307
    0x706170103110918030a1205010b16030e060d0f0507080f011a0904021c0c02060c43030504141509041e1e0c030203071e0306051003150605 61
    0x48507924050024015100c1d01050030304c80c29070300b03003540d466580b070000190900d00d46501700712030541031200205004040f4004c3c0c8010707800305805494041e10136281500c0403c1c0c14070840350070035802c020407041d2000703600640c8640211a100010b0707500d0540001046600d000d403503151a580e01e41c00420400c0001012007a80f20124040c5596076801500090000d00c1120f42660380c7c14070100307241c3c03043c030407a520541030386c0c0d0703150292091036881000b03401c071600c61020280003e5040103502c034000c80d031f140d8803008131140c4e400d5400d42c030310a422119001d20481c00c0f001c80020703d00142c248064141e0a820100ca000c1c10780d07804900c6800e80c44184500e0083d008154019175613141c241d00306c0c1341602064528020362072010060840c0007691036a4910301549000140d50600c007009000500c80e20849110f404542c1d00c2e80e0191600070110001e8140700741d0b52408150300e9900100d01e0b030b9680031440c20306400a13200001e07078400188072510455050740c001c0c1c1c2401002d103c0d6480b001400c22103a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 884453767 1250 884452517 884452519
    0x50a06080912070c0311190312082d181c090503010b18130c140319020d080a0212030f0117060108070b1c020f070c09060303050412080c0f070617010311 67
    0x4894900c20300100701034087d107010a210318681c031240002804000b2260011a00869840c2c24031640c40c02008204100e541080e210010360001740088038000358030404ccc1c0c000d074000c104124000e50940d4002e1424107201c440152003030480410041454000a801c402420190024000070000c2000103000c00c412000c010038501000c800140064840c619462909910a118910b070301d4540346c0101000100d03150781c90080c07080c5841c02c0410088101c0c240140b6074001c1c00d50104c10003541d1841c0c1c1e5500110100015481042889000c481c03020300a148540074045103a04c50390314043c048840d040034181780e9039442d00300300010300210001042801c152040c180c5031a89e924850313900c240d1051450700c01c40300401d1001c5844014208141d0060914500503400c0c40940c40c1c551591400701d030000d200c0140400da0421040014075203550302180e1460140d4243d909108540f08070314140f2040d986244c00c030380c101c50814042d154004407044c6507072040c8411003c2560542d5200d18040d00150601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 884455017 1250 884453767 884453783
    0x21804060c020f16090f0e16080d0516060e0a05010204030308060a090504031409012d08010509071d010512070c051204062c0303070809270601030e07050a06080912070c03 75
    0x41c0c940101a90088004111031f241260620380302400d04181c441400d026440682c0a4040c00c1d001040c441c40030b840606d21042e081440c4a01d083d580d200c002c290294483c0d50740c0c080c41c4500c3d00070503000e2000d0801180a920f81149a1810070100300f140c910a41040d170402e80340034240030110364010480c0d20f0007100d00007400d9607105044016038a045111400409070902020400035040800c2c0c0d0b1560640401c0d12820110790f00d4108010b003030301c8110b486000240100850012851341c1442d034102954060502c45e240c44840d000541003444103c40c481d0218504171004020480d0420130480101c1198280c6410700303041680003400c42c224090b0540380c80703414264220300c0301a0a560742040003401001c4981c3c0d60303514603280351a41c20040754984201c0308198040203e11074000c01c10803040e0302004061040e0f40328030040d40142401e418200039442044804203031500e4211003107024210a4030740001d203180a0314014600001e0340c030321b20b10242050003080d0020f0882001701d02925440071038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 884456267 1250 884455017 884455031
    0x603050408070f1401020d0605040b01020c060a050a121d0606040501080d0e0a0f08060103060c0201051302010302180634050a020112140429150d021804060c020f1609 73
    0x20801c2180d00b800c85131a529440044c41d0400708501c0c0d403002084401c152070500400c0302c004010380c1c84044142000d50004403c218500206200d1b40052500d4030720703400c01c6012007014401a004451704803000c25212881501641c03e000c80401005900800846060102d90f040c1001e03940c40300c008007014414800444450455540d8800126018162000c4626402560307080c8496952200384400e4400519201c0c00b41c006500c180941481102c081030b18018401c1ca42d40110020360201800003c06282083d1a02c1190f64000003090400815020310340460b2421122401c55810181d12911300a210100c1c680000c5010400150403502400c3c03528040e815900901d01400b1130080c0324038829064020001002003c03207241c051b8580b0301e802d901c2d0b0b00c0380304180c1c0d235000441070b680700740106641c0594150514142c042030756014400381000301c1082c0000804008001d0540e01241c40c00e032190411460300b1381c104018035420b010f40d4014240b0004001c2441031080c004d0080c0d0700401d4403181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 884457517 1250 884456267 884456273
    0x22e0f020a02030a111003091e02030a06050403021006080a0f0803072304150f022d060c0d0b0a0605120612030307020607030509011a0904030905090c0909010603050408070f 76
    0x4006070094000d029a0003103041072601c030002803808200309216400300190034040920910940152681c44280100103030082042c0d40b400d4a0300800403a414071400d003c607c0000e241d8000c0034090707071082d002440c00b4500105400240d036416080280030744c0c4034450700e602040034094807452098100840303a503a516030f90b400310343d5241e200c00c1c051210b03144480704d41129101c4c2c0006000300d0340c101e800d0030f00c11a446601110702a0000681d170340184d01510005801c2204042c1e0807801071440002e8014407421090400c1c24100100e0344010540408a6101c4550380d03039010703030742e03442200700c079890342050600d08080c100c2d0044040c034903140d0b10a800021456100c0c4c060305070380101c2d034000f00c0351a4545200001d55443e4100c9080c000241020042045804140035030b4041c0d4900240c0340d9461002a020b00605c0720700100240d003040800240007880b902d40180c1f4074000d4010424040d5202414000e0010b0203106902240c01c03d8035100420011a008c401a240342641c00010198282c0d20780c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 884458767 1250 884457517 884457523
    0x31503170f030106020d030f0209012322090f0e100203060f2806140403060510240201050f070c2402030921031b0313150603022e0f02 59
    0x722252480400000c004100d440c0c000680c0080059580c0d010b100103280c1d0314801c0142c0c00f51000c024081000042c0b50995000d10040310040c660100b61114103001100c6140f940312111644c0c3e0019600300514140091091801000725466030314a00f0300003401c011041541d1461888022034546501002051040e1307500103100c40b0550340113103880004a04840c0e143d440c516071003446128611001800101c0b640500d00d40d11061614010950030305146858400103080000c11091f180348202c40045620f60200c02c5000c1036541c107848048195a140f60064219607001c0c001d004130035011810081900c1e4440e11394440d055001c503003101440c04001402696490040707804484500202c104400100c0c001103d51522415428071425080241922580c521082d18424079030f09655109411207041c00004682105a01d0402c450f20301c200e4039a103940054511400080d540c4078407041056103071004044500d030702059080284505148000510107000d203a612080c00380080a050001c4e0082c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 884460017 1250 884458767 884458777
    0x14010e04030e1e041b23040b07081303051f1505041d070e0a0b0f0d031b150203072a03030b040b19030309061b0f110409030e090703150317 61
    0xb13001844200c150454a43c0c0540d09070040c10b0002d104541c0e0940700304804614024180d488400e0310349403034100080300b0990340c0300e002d0a03111406d00300142c0d8030071301c60303004620000e5011300041c0103a982c0f880c84506d05041f8603d0700455070b5080180000900980180710000c131501107400180403210f41001072101d2440b90142a0540100d0600160703020f40e41c00f10a200c2c251041c0200014031070141004909081011640d40066003c000352001030f004812012010441200d00182510310350f680c1001c003410314000381002e503000300c140700c212a00104c05000d15550710080b0408030700070482003442a0380340c04001d420151282c80c03d869a8803664070804607601c000e8901003503010030002d0402140064401140003801400300000e0640c858a203000042d00f81640c04034a00c0015111740003c29021607060351560012804010155214400e500c2198840e8803680d2110345c1d508200720b10558000c220784145800c05400008014248e8810019079601103580404100a55000c1c2254064 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 884461267 1250 884460017 884460019
    0x51e0601121e0e0f0a0309030602090f030604111e0904200d031112070c090c02011103041208160c060f0b100215010603180f050c060d14010e04030e1e 66
    0x5040e00706048007007600010450401c41d400c13a10440050409943d0b280e160042c003800144c40a1420300c0007810702d4000780000d80c0000c1c00079100c044048002410002e0230b031801c4404882c0c0d903428800a003403140000400703040120360840091140001b081c48458018401042c0720700482501c02100d43d00040e800b440040544001c00007001860b000c1c00c1020f1011652695125003d1124080e040b48022210321070f034030520101c0441e14020107a80540300c1106650700395525007620102c080354042c01341d4070035030151300d0380d24003c90030380005008900b01070907030701500074200c800e00c8500f40c00c00c075500011030b4005230000d40e0041e01414400141002e19034680c0c49400541ea0301c0b10541d00082001003c0750042074455070340da07200c105604890100c3c0514420200311003948001c11b111740b85803441c441c01402a100706124807030000d102548030040c02c02d032240e03a40e5100e0303646c418001da1040c0940004c0142ca83c050400f5280584070703007401c218092140454100426070030f0b480e19030309111504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 884462517 1250 884461267 884461301
    0xd050f010c090603110315240310090b0103050108061512060103050708101b0c0312150807060c050304030204050615030403030c0f02031806031b0418051e060112 71
    0x201c081e03002001c2180a1140100290620300e50300360800720202101e018441e8000503001ca061100140483c44001c1e6181000d501c0c2920138603081c10103480015131003200000b82e80b80c00750341032a84407802c44038240c1e9810304162500006002c101000210b95401c0005c8910103801d001c0c0e41000964400c80d410a98030b240d0042c2c6000104005000400c0740a94282d003050724200907000240600b2031340003001d40382c020200707a5911990700d0b000311b104400060103442c00f441c100765125028410740d0502d000f03401e01e20300381c100c04002600090041c100500b107185003150415186440f19543c0380240c3c00041c2c40340e40d035000482d04540c2c5d1032240d03040054954100c50786a1030182000b500508a95050f2030200b880d861610740400e20200c100d40090842e0700294002030100340c00d02c00c071900010700742d408425403c640b040119089101034030090000e215910042007249209009a44c00a00381207162450761058240d00c00141c040694800020710b00001441c142c0b18440700508641421400048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 884463767 1250 884462517 884462531
    0x303140705010207050f0f0604030c0813091a010e04060605030f06010905090f0907060809030307270e0901061a03070e01020118060b012304090e010f0203070c0606080a02010903020d050f01 83
    0x1705000c901004804000b01c03d071840d00ba03c1d58074094031800700320341c0100080c0e403001082d0b000410f254007030101051302c8801070312405d45403801c060840c2e919074903458081f404c0d084040e48641e80103d061411481c15141030280501e000009000f0340405051450a54501e00005030b050744210641d07002088014072404284c1031200000c281c42c041512000081d0040c0100030031142d000707190907401a11140000e520355540e107001102d45006040e00741180b400096654000018141442800380119081c10001402d00b81c0549085844503840300d10100700100301c90780500c0001041c3d0f41d000e4081c0c02e007582d00b0242540103e004152a52541070b603020111038120038000540e000b4048d03407100b80c0703a201e401c03c001000c800c102c001c240055034512004010900c51002107400c040c41d02118500082850340e2500414000c0c0d0300301300d44000004109150036010700c0164003d80c001442070780080d00c00c161003900000c044601c0c0d4007020740100b13045c00b60a004c008081140308501024800200110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 884465017 1250 884463767 884463773
    0x3010f0507080405060f010308120604150f0801050f07020c1002030d051501120911040e07050a080c030d03060515090d060e0f0f0c030a0b1e0106081905040c0303140705010207 77
    0x124409443c02d88242c46400700007040e441c070903800f0606883c1c100055a00700300440348100b010380c0004103203d0300b03e5140c0d2003a031111a03103100c082c000b5154030a840c8848a0070403858900315400107186800302080c08050001840c8c001c103c00300160000da90b84048503503400001d0345180300700410510780c0e61030701003040403080103002c2c1d400742441c2c246d962000c01242007510a050314030400010f811440c2145800080b40b900e0b81c0a81042c90303458080d60404c1d5518000a1061411640040301c260484c0305541024641449603c42c0104182000c200b464200008075801d001c02e038002a2203c4000078088969680e448100360496070302031014410b07141414005c0d80c0300e40300705500382c0d90303403250f04c1c05007940304c00100d14007504d11070250051150b0351040d15181401d4001404150751401c500d040c0303582408040c410b990180107251288141400e107150003160002c0d4001041842e10701d02024000052800300e6200201c940626206242001450322401144600d007402442584006000740070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 884466267 1250 884465017 884465027
    0x210314040b25150b130906051b030f0a110c030c0d021e0616050903030403110a060507051b01023d1b0807020c1c0c0f1503090203010f0507 61
    0x3250b10b21641e881c10030590038a0000108845290040c00c1451100809a40900550103244000740c01002195141d0710180304000311403409009841d81d6480310f00704000f507001002d08007458030001d403889245107404581d072000b4410144c01c1c6136032141c0311100d000d581031f65402901c42d5510b00c9001d40ea541d580c050070b050b50780c1c980c018090000d4010b9604920341c0c04001904620501201006400c00d03a407200d6882c01d500c8007401105c024000103122001483c1c80c204050405540724104070348501c14440208840700307007598000b00030400100461000610301050100c2c1038246070040e1354030110300d540141d0400d4178500165200030079560801410f0b05010030641c01006030203040007106074004e885402aa60b2010301000383d551084420306d601c40c8100001680400a481917030126940000090100d1b01c0600c0f840301e054008607038820a0020307081d444001030201d2004140003e00d85000c036545104150704481c24140e4450006055460a400a800680141204108500d00703101c01402d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 884467517 1250 884466267 884466277
    0x2b02060a0c0b0a0b0609090a0609020c0f12070309060e01020a050615040b0f0114030a0905030a0804061a0102120d020d05161206060c02090901020c0f1f06210314040b 73
    0x800322685408207643c61202d100c0c02518203005810985418010800d10400e1140a4084928156107140018205100c4d101074030301e40c28114058031403c0c0b40401450314190402c0e108281e00e0710100565000030b80c209450100303c484c1707418034044900300d080c0180e06000d140f003c090b21501808080144040142e1154000c15400300e4003005070468000c2480300402e055074070a07021498400741c0202000c45040a103038800c00300c82020455001c69a0b417182103410007603082c0040703603e100074401001010f014100f903000d081c0b0402d21b845255000000c0d52601440c208401e00d45002500114941040d012244001c1c5602400c0c401424617408000a40910045803400210000d140c0030211030240038560803034403181d50b00d01c80c08441d40c08101d42100042c09038680c9644c2004550001d00061161000d0903060300d000e04040d0340c4004140c0c20245006d0002030049186c1603041c030130369800a1140c0f410354030031a800da8a500c1d40345003d070b5440343c0565902c1d081d0640400c00082c000c0b0308500410f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 884468767 1250 884467517 884467523
    0x6060602010c0801080a0b090a0f03210b1f02190c03050c09011410051b0106140f03030d02070623060406060f020607180b0412110306062b02060a0c 65
    0x8046010b5400480e4521801e0241480940254444801182800c20080e0300080c1080a442c03081d4541d41e162030342d841c17201d1001c034040303100044007242c0024403417401095850307000020700100100d54006400e1240c1041204038145040310000207852003001503140759040400c0003d030b030310f000d4104900d5856062204031420f201e513000711101c40c1005403189041f909456030724500101c621040080407a10340c004101000400e109162032080c07084580003040c0041e0740000381c041d04004411a616010030511030140042c0701b2000c900d034600004446a104280c040186c41d203a05241641c05041c40340d042d11032695003c0465183c3d4101c040300540200001c8034100403043e0788030030030b45441030401c0e89900940c1210000540a6001c1c4c0049586107250056a100e46911901e54040c2c64100e80c00142c1244080112541001613004142c000380104400502803490600009005000d258188492043c076456000e1400c122804030006031940c01090b1741e8880c81031400c000d04e178500302c0b5000c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 884470017 1250 884468767 884468771
    0x207080306131b1409060a03020c0c15040302011428030e070510050304050a080f1803030f1c062301120504020f04091106071a072a020f09040606060201 67
    0x8852901588034001a4011189090080301030820b42a504e82a00304c00340181460201300718401562048014500c03003265880c0180c56129049030640b400076020500d5000341e10568200c0141c1081600351000c890b0709181841074800c0f514442040350103002c1405070f0485550400601030140c1080600700b0b80c0d00b540d4100000544019060759420280c810140c202c101c0c0741010b68054460401160b019016038101c1e4881001a82d408030103030b20088590103918404100d00f0070040b008036581d01c654100300d008500b4132220b0700104d07445103d902566540760141041103811240c242c1c112000424008903013210740d2042c1ca12026140343e04620007030010b2002c403451080f0004034401d90b0b0046401034031048420a20740c0c180001007000200554a282101c4000354880c0c1d81c034402441614480d810f202500c502d4054440c28404005c0c0400c01400107540c4115081c074a042000c01c40c0b000b09400c500103070800c600202e00c50103104203c00d80c0001d2010100030500065410bc1801c880050b402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 884471267 1250 884470017 884470039
    0x1b070f0626040c09050601050705060108010e0c011106010e040201020708010507170f070c0b191109030d17040f030c05160f05030a11040c110d0f18030302030a0c0302100207080306 79
    0x55015101c80c201c0d002480401202014030400c500e562126501281c18100720b450300b0440c1c5c98541c83c01400f41e0004880e0f0f91207004d521107048090200340d0701c04001307003000d03408038006210181c2c0741e58050041800919103c8006425a03200300007000040c00040002c1085042c1613100814101401c0300c05264040020041001c0c491480100ba1143c0480d03581d40e2042c0101da5512a0204800780005100410b01001c160007000141305e400400302003030807040d44da0a100740602d803d021164900340c06000020340b081040009a0079230a41c0a039100c0354104044240d880d090311917240810b0007411621800c0c123002c88035465004214183c401811006901d1a0380b00105540e40c2d194200003060f00c203402ca50711801c0d0600c1e422801e200100c034140152490440c10b400b40c5890b203040c00d0500001c500e030356504402038020525038841c003012130b0740c43e00142c250b0704c019550f8802c00625404002e004030840040c1442071121050b2800a0f120a55850b1140c0c2480d1005400964031544202c0054071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 884472517 1250 884471267 884471327
    0x40b0105090f0d11030708070302032803121103070507020a0806010612021303060207380402010c0c0e0114030c0301090314030a24090b0f061b070f06 66
    0x65411009004140401c44100c00e010f000d403071107a0560072241c2e2000301811341c000e90340c184090006002002c00900081e4618010180341c0344139080c4c41d1400150341c40e0841850b055030440c08413a43c1d01410300e10071910411400100070114a000052044000b00038401000e134010000c11401d4000c54442c0c0e100342c2c842d0350403502da64007032003080049038090440c4481e000b8282c000d1700b510607100c04030403583e9641307440d61001d07680310801c100c9003000d03000140200b0300044403070306c8100c980c144540344c090608110b400c1ca10380400b40010781072002c018070b90010011402c106001402114152540300e503035a0303c1031000b04806503070140c46801128071540a40c141440740581d15501a070340d061500c0c0b03030042030003080d07031024006500e4140ca0f813881d190541102c111040010181040c00c43c2d80a00c0c114142040b6013000403030a2007144418a680e80c2999124183c50b004910f0284110541064610280c6882c1403035000d10380c0400d014000203402c03a0041d040100d07071441020405541c04040d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 884473767 1250 884472517 884472527
    0x170f070f061e1b0f0c0902041701050103110103110903120c070b1c09080705120d05070203091302161407260706031512050d020c04110403060e0c0603070e040b01 71
    0xa2400c00018034403c55034009201c060392507004060150b600c1c0420503074207440b1502c0f005003d420048071250005070400450408c0a8102c400c03c00404c001c0105506596451440d100b860b019a070406072510000c0807141500000c584240074010101c1d8040d40800c0c0301c103113041c3c0085584200900a50900042c6400c0382008c071244000c040d00f2441640c3c081c11220310040c011941e003501d00c5102844000000f0300100140b04100425240b440d8640c441112100250f41f001040c0d14119002401300c0344142e1a126801d0040c20200d45c40540c41e4150318220b2507209101c0003000d80307022054440f40080800124044054481c0501c503010b00164904240c41d62003641a00c40c1e07403d40c051541040101e05c80c2e441040b01c0300702100340310001540d548200e0300e00c1d80340e07207400d03142c0380c2249034810841501008080d0030268182e5090000ca00c2a40c801003031030140f41b002074500e6844507188281e21740140407440644a008001c2030f101d0808000c014400044550314600462429212101a600038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 884475017 1250 884473767 884473817
    0x91005181f06020a02060d060b030a02041e031e1403070f020907170a0203040303020d060306020c07090c0c1401181a060a05150a20030a0e12030301170f070f06 70
    0x43d00100101c008560034072030140d0107800c0781149140c0d1880d01142950200d0000c601981124401603100c900700001610307901703a0180324580b0b49806810410004801c8860b1044c03240e032110010b07035005031508141503116400d4105203140d0100203840701c00c11a6120101d402140281e07a4190ba5035140001540d1000a40d00000300180d42c0c840050766005240d0000c5a0041c460310b405030405025003180404d49605400c221401074000c1125045150100071182c01400340700710501490700304c00b4010700b4403194604081d019800c000f080400e015404d40005618034038070700307040d103134110301f82007403450385500340c3d0b503400e206180e9030200d038162a01f4003120059a000401150b0650520701683c2d8250388107101c5081070290025600c4841d2110201200701e604819028650710b03417801c14000d01c0038070b004c80b01c00c0c480c902542158040031400415641554103c0f4043c0f20095003c0810f22700d418140b9134100307418481c0301c2000c1091600c0d02c01c000c085900603201c00c03d000e009103d0580d0031040d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 884476267 1250 884475017 884475029
    0x90921090a032003070b0903060a062106060b0a0302031e0702060601110c0a061d19030201140409091109070507050604020415120b070e01140306091005181f 69
    0x1c100034000b00301c0e140340c07103281d41d011050140a41c00105002c41d042c0400c44d03001c24101c4102140280c01030170203011741640104004000c00c000c1741840703100a800b48165036030800342d0740d803c120300040003040d60241001c1d1660b010360545500c80c1301d00040103903004581d007145201801d03050303110034030142c842c1c0c50140405401030001035030748c0401101c04140000710031609104504100b8200e40325443c08401a11b0550380e1103d0000f426500c000080307610f543c145014a9180800c103a44080405000064030ba0901c0c00040c079040782c900807065405280c010620440c601001d1600b0400703540e401d02041d500544000340d1507a80c0060136101e6002d440c4002c1c2082d08036800240061502c0d80c03000076948041000036030410303180c100300c1c440b82001941c1100c401d00d524042c085156000380114108140c2403170854600700300010348290a00029003c0740c01030110401082c0c1402c00400048080c0c60094100403150315180510030581e030060b00d1620211908020301c0c0c0c0c5e1030402d010340d04141c03a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 884477517 1250 884476267 884476279
    0x1713140d230a032304050a020102010506030a0b1815130c06090b1b07090e0322050a03140c1003020a0305010608090703110f030a240507080a0906090209092109 70
    0x14080d0803d4000e030454056454031068918946030301c09480040c410f000314010b03c000e040c0c61a0503c00682103540240034103201e64004410340380090020361005d580201c0c0741051000745403446041601d0103150010350600008180100701006980f0b204400145000d5003861800c143d0320501951441d00500420810000400041102003103841040000464080c125001250303290f04a4003141d4000c0c00040941d000000c0f078908040c0c2c00000c4488001000c01c101603a0b51400340000d004040a1000800500f094503002c0b184c480140101501004054240103600300310b00ca00a000354402c03800007022034a0000046205849410110301c030708a04c4004054290640d01c406c48040306207181c01d540012400b0400b1040e4030244101c40c801d5104060134000803242c0c07020100f005000e0b50f80101d0891904013002801584440015002614850001044070300c1d410400301504030018040d41004450023408090300780024943c4034558030708942d900510080c0c640c0704030352040c05030141d4016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 884478767 1250 884477517 884477527
    0xf0406230106052d0c0106360e0a0c170f100b0303040f091b0f09170c03060412020f011103060f12010c03050403030b01020309011713140d23 62
    0x180204000d082011000c5413440c2503220030103030802618140d000394040d1400118403e240c0040074061f81c1e001c1c0c46c1da2102c401c80c407040700e9503000840709680c118001d45054009907103015007040e0301060950150b201501d0300c0101c1ca061071844540300d031080b0109105c010b0245240e1160200382c0c2000d400700071019150580340c05100201901c48440342d40e40c9400704100000e1040c9090203c03500400258201080d01014442820030300b0180201400603c03410350b00f4842c486610031612803d03200001c860411100c601c030b201901e840ca0540380726415200e0070040c031040c0075520b516168a10915400c460304100c8554085e800d8501c185d820100006042c0040780d0645045048003040030005040e0400c400c00c100d211b075081d15582104c0d180443d540307034140000e1551500542e40c00716001c2c00210728280350000000c0010845000700c580c0c1182c09000b0a5042c1c802d18200315140307800062811040c0010400350b52140c80040700c200202d212004040c80f034014040444500b181e200400034202 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 884480017 1250 884478767 884478779
    0x10801150f050f09091006090b0f040b0f0702060706050a0515131d1603050105130b0a0902041104030507140d030f050a02010603020a03030807030f0e070506070c0e0f04062301 77
    0xb5401110000c0215401800102c01940f039120300c0e24850045c50f050141080c0c03030480090920f8206070084000c02c40200105081c00100e80c044604035455455801e0b238500401050303203400e00800400940c07104000036030310f091001b5a04151b010b000b40410402043c0c44070b500d010389141101e502075400000100d070307001440c2d1030366000060400d0001d8520354061039040f00c0e00c0c00c00c00615515030300b4425100d000e000b881800d2058030b6006e140072141403144407450300c40810032000103141d2003c803503c50101c142191541e8000100b5000001600c0f600d803500ca140103070301c0d01c00d03902802c001103602091609462814502d07a01c1055016120b4041c00d04010108a400d94031555200040d503403a07507000801a1035945000d0011f6000359908062400e002200906844610b603001c500c803070915110380f44800000c52500b00320b4000710349080da10f540c42d140164500304903034480b0248074480010481c3d190102c90065104500c51078041040310900c40e05c0c5906504e403801b900c821322200ae4014021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 884481267 1250 884480017 884480027
    0x20f121213050a120302010f090320250311060a05030f130804090212130201120903120c020312090106060219030314180f011802091314010209010801150f 68
    0x1c0350000ca001074652500d82c1c020407101c0d20154041c0000031107240004060540c2881f92035505002e00301e05014007545518001c0004416824503d17036008080a12074048004100144890100003c04500114207400150060300c1c1ea110035200034103090800c801074545001211000802c0e5140c0c141152034140141000c4140208815800d09000000a0104008101900083c024a400542e80719600c2d42c0315801c248000e0200c0461102070b54003800143c0c1c02100399040079003550000035a84402c1d082c11590b1200190000690701d00c0e117110060f040703a02000520790016555850740590702e0741c2445900706c8940d440f800f00182c06c200a44408400b000038402429806482c0c08035180024854500f540c19064480c03440f00d030300300344103000d400d803050002081a0540700c000700303d584098a000002c6002c0c0240082c8100c011030000380003482e4409440da241a000480081002c0b01f81c41010f0003540080070283c045000d6000010b1001d400301d090080925965803144c2c3c40d05500a41950 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 884482517 1250 884481267 884481277
    0xc011505030120033d060e062a2406040c05070b04240f06140a0b09060f0c100b0406050d2006190203031e090604080711040203040f020f1212 62
    0x14810301000c1c10342245c01c103090003000314100005903080a89403100c0039180150711410203002d05414000500b0001c62613040e00084544c0e0404420841142092142010301e1100c0c1c8280052400760002502c20362101011322440c1c080c2d500708400c0030f5401c801d48040c010110001c0500702c0c0000060000744401040d10b03131102400000b40b1000107600c0041c002c1e00d00700b40200b048280d13100300820030b9941591102c08404025a902400103003046101c581911076880e1941c050000000d05c2c40c0c140290100f200d02406c2e2f24170a85e1805004107502c3e07400b42001044051046040c5540800ea40c03528613400300504e58880501c18980e55101e01c2c3c1c407c00c07485c0311f907081c2c0c0c0103600740300708102c092182c00c0c241203030b01c01075004c0c5540c1d05c3c0c200c0c000c0345980d00c4058010315a00200081100c0700707200165141c0c00c1600b1100d0192600c0b89440c22200d141d201c030f0075054219002005000420005000c007805e01417088861406101224050189009880090b030b115a03004001c02d03084c03007041c035006103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 884483767 1250 884482517 884482561
    0xc0216060c06062c010510020714120313140f06030103030309030c050102162307030807051f02030402011106061011010905030a0c02131406040f020c01150503012003 73
    0x704890741d5503e68580011310640007000c2e01e0040c3d1480c4000c006010391124003414040b900780d01203414a0f00001e41e500300c180982c1451002241d0340164540d501c9601d01940c07a846070840b03a842d00d0742d11120918082e00d2003010700c0052401d10769101490700d02200380400d58094807050031a0300c1c1d1346045000d40300041c0250b0611418035000000b0030002c1c0010924907200340c11031004244940b405000314185904a0010700c50240e8112a001c00045010070031203402c1803505071100d0450400a06043c00202003604800101801c40408801c903005984518001d0b01c50080205109892545401d022115164002c002c100c61a2300540524103082561001e84000292510720f079441515685c0680300c11030120750800d5940086191500550f0324102e00410144038181c0d0080f04440b504102900040c072498481181001082a640c103650712241c002009101c003007803180c4220707100c0e40e40d07000342c80c065401d0008043c41c2c0c180c0310146100a0300048100c0d482e40d40d646d2540c0400c1c2e00d40410345 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 884485017 1250 884483767 884483771
    0x1b0910061706210303071803083103122c04050a150b25110907030212151e0603010302040903030207150213301106070503030405010c0216060c06 64
    0x1400100b08654010f8900c02500b0000c681d030381401d4202800303601e0340d036114610f040e5072400180001f58010b0103554201c91418080c1c540c00c0448600b8a018002c18400401e000c2803c0700c0c008280510701d01000c40356a11078441255000507485824002840035a8000801e964001e03800e001d410240d11040d404000d06000044a0148440b0395071481c6407035100c4020141d02180d000c0c00103080800b0b00c614081e15108901403c0341ea981ea0021017190a45d0240c03061007a5000580c076980207804685181c0340502c0e1411040ca40216162070b180b4840d1600d6015180711740da50303442600c59003e1314410000c0142407034210b82c615400c100180096400c11001c158081c44464000f44122201042c1031818020150b1600516030030b200031103c1c25400741251203070700b0b426410203200b0541203a040303201842d6400c1e248940d90400083d00c042910b0003d410090005048003030290210185000714403c030000c1c014002e40301400c91781d90303407000080340002e00c050b0403c022041c000c10f0b450503054452140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 884486267 1250 884485017 884485039
    0x80f0601171906032003011808070f0b0901050f060f010c1401061a1b031201050918030c01140a0902010e130608070b040e0a09230109051b0910061706 66
    0x4080945600384d108540100424001c030f002c0b0301031610344031200d403c20b40003002425000e0105004111a1100192000d000080e02038103001000b035402d01c032282c0004140065003040c0750350f0f40c02010102c5200b0f0200d0814000b1400900e417407840c03c0c41528050356801d03040400741d141d44421582d120764038040c56603240c2c3c00007843c000c100301654102c5174414007a07072a00e090414492154452118840a60300300700401110501e50040075410345505580070b600a54406c8042407050501c100341c0342583c48003160b40f245200c1e05411444080c2451110317141d00d52034941c03243d000d5038040760009000c502d24001412150402030800c1189c3c2005a0000c02c0047d40e80000398200341658000c68019807000809004101e2040007250b001070401c0820400d42080703449800e0358000c04101168050802941c0e512242c809401041d80349070030034141c0d5610b001c5180c40703a846402079442c483c0680f5a100000364907c1210118004032045500e43c580380080d070100803078500ea00103006070b6208420600e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 884487517 1250 884486267 884486311
    0xf01030f09020319050f010207230307060609240b040b130e07081006020f0606040b18181c0203070f06110a02070e0c0406090b03071b0b07080f060117 66
    0x4820702c1113402c5546440e04d448040c1c1461803c01c110001840207680c010066900000c08110481d400308203406900c4805500d10503100c0e085108091020307050360300348000494020036075442041802080c50515000123110101880d031800700b03100c0c4070341144050100f0070142d6490300090810141080c02c401c2e40a1301c2e040480303654501a200c0800181503101081602c0e14510046d4004d0681800200340340c6100c1070384103940f201c0080c04540100d07110b9000039065181c4800240a0035412070900304c191500060764124500100b46c1c0703c269102d2030150300710300165042c4280c2120a15405149446e6440c1c582038194041c02100b1550303e0b55071200a200c00103c14041d00501c41540d01400c0d406140c041411484180a4840c101060f41000200705103a0003140c50300488070350309552600d80d0b0710b04005655180251151520203803010312a10100f040c12030045100303104075251610300f9141d05940d8000310350b049a0b002c0c045030120450740d404950046006a209500500c03001e0a280300398 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 884488767 1250 884487517 884487523
    0x7110d1706211615050403020907230a0309060b0d0503040b0f0405060705010c030e070b0d1d01020c0307060f06060c0b1003150605041b091e0b0a050d0b010309020f01030f090203 78
    0x2008000303280003520b0082c00031340501c10084541695624015043c41d0950b000180c0200b005007080040c0a90f883c061000c003c48807540c0c41925890803400740d20751482c00e401030b000c1d0001110444819240c4034003413107649410400c150242d0742042c0298103103420312840f0046c0b0340c0043d400a048803801c0c080080d0f1a59050700429200b8490070002c11884071002c8003605496800d04220383d07a810581050000c40507031020344000e01c0007040302090300030010100e22007921408080a08a50000038401007455000000384621440f644003001500d441c4261481151040c8c0102c0c000240b448020b8070214107080041e5400407045111881e20780d9903607440c2c03140e80700403070f900e420802c1c3ca90108001d0707482c00d4410300c01c4484003442000c41c0c030301c40b4140007490b00d021802039420505030350700314603001000010008003800084401554640140c103001d041c44e0000000010420b0505203040d04c0c0f94807074055483d40d1540900320301c90800c8400b0041d4003601c00961800c244690f220f007240d01580e410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 884490017 1250 884488767 884488783
    0x8070f050d020a09030308090c090a1e0e030405240901051809042a05090f102114010c0f05090d06050a050907240305060d020907110d170621 62
    0xf0340c540780e14143c9036160207400e15100410090003a08041c080100503202c1c2c00845034400c0c100740700080d4102c880c0e11034100c01ca00d04032017020480e282c9286060b02d400d00000400941d2021517882d41e100c4a09240416208c104454060480806000d61141540900060404c9074801e003481101e03902c44102084080100b1142941c10118080c14040884944552b10781c0c400380c0c04002c10005401d220100d440400c001d0040902c0c0d2000d40005003503966070345803420140c0254403038803010314010f00e4146810618050140d4900304e02060340c3c103d9034014481c0450242494880c5812582e00c040140ca003500500d8100d0b801900200c03c0b040014803622800f4032403100b034400081e0070f09198050500d054002c1e0088540d00074603141842c134501c0340e0301a00c0042e003c103180105813036070365002040d0705405010f03000750000499410b0011680c0c00c460001c0c1240a806d0888413a00300000f001c8031009007000d240c46404811101103040340c02d02c89201e904011000030700300169010f00445c0c80c941864 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 884491267 1250 884490017 884490037
    0x40b2d040e16060906050c03090d08070503030f1522150b07030908010b090c031909140a021503101a0702030a08120c18010302091315030314030708070f050d02 70
    0x74609222041c2c00c00c14080c0503020306d2600324107204880d00c200e0307541c3c45140c0f0785510480c101035100d8204031468044078445644041a40d8507030030b00e82008005002d0030788000c510419070144803c481d0602d0481080e903620016240842400f600c000c50703005008032161100891903200000c00e1202050f0009d08a251095807407107901d52509002e03908607558181e00a104501400074030406c004a40b091360f40044403064204070100e0104c1080c4010521110018003220b98404031020110707001c100307070310303014000e2320854400c44c1252000d24440c0300444030202107401c80c110502c0703005a43c80603040050340c0600d90780d01e0000a50002480d03c0c2d8035000440c1d41d82c80000e1110204052040341641000e12010828241000944603903e4080b01d401414101a07022030380c01d80940e82e003540c80c200301607508420400c030040c40040704106450760000740d01082c8004030280500081c213040324818007881d80c5000d156142c82c041210b1441146c940802008024080c1c005c000c0c1c510b1000b8404102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 884492517 1250 884491267 884491303
    0xc030d020c09160237080903010c020f0d050a0e0a080d11010501030201140d14040605090f0307110d0302070b040e010f080c0102100c0908060a0902040b2d040e 70
    0x4504104001c40340000c01107520010a4a2a000104c0c1c00040498443ea200403403400f00d981c1c6010110141840e91052844154a812065060080000c010030380050305600034005500d441d20283c4e505c2c14003151141459004030810700196125102814158000e4078025180c81c051000040d940e00150308000748507041113101c40d200c95040030aa580803c10f40000380440e61540d000070b003d891202d078203400d80d0440000c4201c0c1508a5512190b005800300384000c0050819043c0b40c0c2c0245070884c2c1c800d8003442441060f8060640c004143c8080035440704500505054100074068407030340c0540b0450940c41444c40200d032a140030409000500301c4a942c0300b00541c504950342043d0150780d03000045540200c04449000d03607000c01c400d02010170018000c101c50403004011a44840f0329444000c0d0ba00540050001440c490b4000c072898900880d0103102d0b90011204110b2034043c0c901d8044100c0382429001c400010958002ca072071807400400001d06806101141802c00d03070301c0240c80001007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 884493767 1250 884492517 884492533
    0x30f021912151805130b06060304110607031101051b041203111b1009080319050903010903050c150f22020907031509020a050405040e07030606030c06080105041116050c030d02 77
    0x20b82c403420794040703000040745d1411022500ca01019000152000303003e484000001008e203c0383d1028601041d00161041d543c854a40c203004018607607005521301c0b203500b03050100d10340440641c500384d43c06c00e46400041c0381a1512803011500e8210010840034080d031600031080003403061103000901c040c8070551200c0d220350b100c10070801da182c40005c6002e214080c241405144000415a0340485a00b851060200b001400c240c4841c0038103035003294190b080027a202e0405500001410140d5030382c0c4116038148070311f00d100648503202103411341020b075004c100207580c2c10390300500c02c6c0311010034031a10181421070790049040200110703031100c0800c0d102c402c0a503400440302d4070395000b0103041500310b0812141290040c09031069104440c4100d490f070b054103d4044042c80307080d008590011040248503500d01d0b211070041010b100e1a0040703040300700000b40fa4102400384004190380c4403509031400340800c018003421080380c0c9041c0d92078070403890343c0c40041d18200f048850380150b58000744445 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 884495017 1250 884493767 884493809
    0x70f11101514180a09140d03020408070f080a0b1e0c030103030e18180705030321070f0212160210120e0102090a0b1c051501030f02191215 61
    0x1d00049000300f80a0b01d00b00b824580c44140310081113800c880111030214a02c007050070003010b01610301c03183e40c0c454002c500d1070784865038050b8010801c44100c40155803000d03607150350b2100c0d035131100c0c40b03164401c5c0c0042080900107000c0b000303416400390b20b040422030780c4c084501105846890858203e00040360020042c003c0c150080c01c01d61201104407103449044108040508203164003410510701c0400810052010130014466080030b0000038040f80e8680c1c594091030125106204144802e0003a6400130404591003103003003404081c503d800500c0301070a0f1000e1038609510101e25040c04075403072188140141e54107050403403066261b0b42c400108810303441c980802c4440712062400960b2040000300e07101e49507170301c51600302c0d106080159204c07984184101808280e500f6842d4016281004004122820000b2075644000030390b0100704000c024408003040b0700c590701d0b0008000100c02000604188100010710b901e1064010100b07090000d0190100f14418540181100240c2c0f00303540440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 884496267 1250 884495017 884495039
    0xa06030b13020a0e0601021002030f06040b0d08030f0a230f010906080c0f0d0c06081e0405100c090b04031112010c0906121b0c05010e06070f111015 65
    0x124401e11200d0000d4480d5500080301080240f19031444420a04002207041e802841041d482a014074001c0d9a607262850340745006d00c3c0f080b500940700d00d02d405200c03006418101e0401e07000a034000342081c0340d502c4103403541801c10b40c0246981b0350181c40305802070401800c40c40600c82d104c0d4000c40308502e03060490003200541e50581165101c1c0e844c002d0108400c80002608403002401520204644c0d04030801148403151600c13005440405164000540e460740b10040900c14803080130f41d45141506003c4200040c1026503014115500c5078619a0b00c040c3c0701d52140210150505149800558402d42c2c624150040e42c029580c0e4040745060803845d0900e43c00c40d10801c00c022000b000b2401d400240907200103040c2c0581e0013003020b8400c031408504425030012840091201c0442c2c1c000c8641c00340100342445842c42164503508251302c42403400300c0026600d001d42147d0316600300416850100300c5a000c1010f801040510030030f1008a207078140c52049114443c000c40740600c00b50704007507032044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 884497517 1250 884496267 884496271
    0x150801060219030507020301060e0c040305010c0c150e100f0f18030c030503070c080d051e0f1803070c240516031b1505060f0d08091002150a06030b 65
    0x10364000c5008665058514004800403d030f15061958841c051070000ca8010503150300494641400030061020211554010b80202c9110700000d125801030064200c48014070000c00901142101848620800d11794100c3c0c04030f03800301c03002c54080d400a03050302c5080c1d580c1c481d0540391555564440b0041c600c03590141e860407680c1100c036601445040e64004020070101c01002c1d04108010010850640c81646142b04540d000904952150300c00705002e00146415940ca090707000380760601c0f000c0c80b038040381a07500c601075160049205686068409040e90706286921049000821200300040d418400700c00c0070301182600c0d40542007221100c29105214030a1440030f1003012b0111702030300748104183ca41e03090340c146404000810864030403038040c010307950700410203170206404455080c1254841481103000320b40000b0786044030028000740c0041802c01510b1a0310070080d0302d500341003100442c20940d4091040b242c0981c00d0741c040c450407101c25142241d176a601c032a410414088a05a0b850b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 884498767 1250 884497517 884497529
    0xa0f2006090d1b03060e100b010c020d02130b0303040806010f051f1d1e150405090a050408040e070f140405031908040803070f0c14090a0207110a150801 67
    0x74502030351000090b205010b03221008210701c400400030303c0d115214010703030801181d110900f0720141c80e06c02d507480d4484551201002c2a00c0c5001040c01c0b06621032489484840d4025104140c0083d03180c00b0300201036030080c0120351183e00c9011482d01620108020001881c056016180c25414101030380410001580000e00c01d030f080d000250461460f4101c14010030f2407600700000d8034a0000701900c2028001e40c0390b03c5c0d0003052003100480c8070100300d811109901e022502d20400703190f8920000d4103030080780506500401d284000962010071580142e03081400b4071b0300c03a4146559030800844090080718203200049803008103590240d00442440580c0c4c8880e208542494242404a507580055001c6840101c070811089410300665008a40180c501642580e40d01c1ca41810300300d1028050080c210f4800440002c00610061001000c0710990002400d031026901d900c41e60304041d400c02a0191440790041d00304405658520035080018082a003018610b82e03084640a01142c50580c00030f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 884500017 1250 884498767 884498779
    0x1204050715050316020a0c060206090c150702010503130605100e0c073503181e030f031509131e05100911030307140f1516020a0f20 58
    0x8803600e0b003080640b98801286250328040d01e12070355041b481c08030b0035100501110444c0e903012442c2c503400705045200707400c10400c8441d03840410b400d0000c001c0c2a11030b0041054400d03c80301006610860083d40c000d285840d4401c6020410b0721041c08940095400c001c105444070010801ca040c4025406d5011030008003035410324840d610b500c48006403810f26911004d41140055030813002c1480b504003c10070480f0841d0b04ca2504c440740002420061070307288510b00c202c8e030500d19115040702004245910200285043c1150042001051341024100d2500a0f012402c0600b039074580c1c1002c107114188070400d1120010582c14001c0360b400c0a418600307803c008000070b040c0820b5000880308940b44d08000e00184218080c102241ea242c0c0904150350b06000020b40c000511440c3e0104021104041b405c1e120030820001403103580b2151451101d00c80504140060010769801c52000c58080350340c01a10240b404541c1d40568100400e51304403082d910412107107202e80329034203d054400d030041d141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 884501267 1250 884500017 884500049
    0xe030d09020a170709050a090b070e012c06030403051b013e0d0f06080a02091f210501140a05071b1b080a03030911040203060f010e040b0612040507 65
    0x85691521654045e18036119201c00c045032200c40503904c0400a02d42205411940d42081e190007420412404c40c19030005100c0090100200007500040e401e088400119400109001043c0030322604010300075410710500b03000c80b0030805840424a15110324000002885110040100802007005800010345200c0051607461402a840890f0000035148070b0668030790307001140d42009070100350b82114155003030100008950800044101207184221210b423441d0741c5960b03d03000000360013001b200c41403801072070401072044070380041d40a44d1100a051140d00c0280d454483c00d450080403200000010807003048409007661040039008034483c5406480c81f400040c4030700001c11448070140244030f00f21400314011381c1d2910203200510282c070070342d4003010300b41c100a402442c83d17010541e201c41c05010700c04164501442120b12462004241c0c0a800404070011560340d0303c0f102c00d1903000ba98541103c151039468102403e20404c059620010f0b070b00d0a880c01707a040c600c040d03010701c582a2161130 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 884502517 1250 884501267 884501309
    0x91903030e04050a0f0603050f0d0203120f09070e0f0a0b0604050a061407020414090601080109020a0909170f04050114071e060f0903031d120a030f0e030d09020a 71
    0x203120075404208450104164541410b003100801100d60b10100e45403403c40d0010400102103910000c01c022881076900c00201c18078242d84a2154401c144884a0114000f401c5000440451074102280c0c004440b012074488080b101071401c2500d0702d4003030401d00c2c01084607600603401a283d450f203054446904040c644004100601e605010b21401e0000c1c551070f0035804020042684c0c0210f8000b03000f40002c0010020b0100c01d020159814810303030146800204021405008100071903902900ea00842403801d0a1040201018541111084121820140c804006034081d00300064104211360340c551400c3c00141640c1100b482c0c40081c8601484098003042460100658000800f031050050f8441c9240100040844091401c0f02c079141070714400c180340d0305030300038803004000140d80d181c0c210386445440c1d41ca440350103200c02d14410400c94584194400e8101c112482010040840d40b101440d00803070540e00f042d8864041036554124550035031030030f45000001400d2815624001c440410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 884503767 1250 884502517 884502527
    0x106320423040f02091f0207090c1814031b09060409030507081309050c0309060a020d090b01080d0f0f05070f030e180a0501090b06070b0403090f080309190303 70
    0xc0301e81e000d1400c00c0e000c8160a00c1c4003520914038240001d00801150100440b1400203402044815005880b61103807048a400d0150703940e6082c202035002041460b05e4200f85138003515807481c2c1c8100704072501c50740b1030300c413080c0301601da021348110808001148014418145004032400d01d40c00961202d2108040c2c0ea01e60312485a00490261004540c10b800f40c201500d80d88a40d440040024070005603988101401d43e105000381d0b001d40d43c040c0865254000702c650700b4002070301c4994064101001103441448180e0041c003000340030003008503410005403211810070100364016280d94010051740a9155130114052006100c14100307090102c0c044600180140602d450040c030040100d9506d40915005900c0681e2144000703182505201115005040f2514282c4000034060b040ca40045052111806140c44114000c0c220710304000a80c3c84e100da514a000d0310980500c840401c000c15107243c5080194041c0c021180115550004542881104001c0c002d0390302d500342c1c0002e82400040e17402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 884505017 1250 884503767 884503769
    0xd03030b15040f0312020307050304080109120806030c09040611040b0c0105060109080d0f050f0d0f0c0912021509030f0a030801050901150e0301110412050712050d050705100501063204 81
    0x6080e04000441d05c0f042a461885405009040c520000c20b000603190015080707a003070350348612038010300c60004900944500c4010358520368035401c0380720850300da030800b80d407080e600a004003404692034486030302000c0c0781d91003034011800b01c01c0d00042018404509000303685e0803003400e103480110b4900e0010096200c0c0d0203160201c040144460b0341105192050b03040c1c640682d1b5100200e603076a400080e80a00038240d17844840c0c0350604104000000c1401207030303080c048800d00007800c000f4010350340c01c010755203152681c0c54255040902c580203498804002d011540743c907604c000e086004013828082c20360700307059120621440096005110020258001c00a054982c0c1040740007100c00a001901403c0c10b000c050000039800b1800180300c054035520b141e4503a00500a58881603200c002a0103040d0042e0005002c50b80641c60304901c6510450040c04c03014040c6e426a2203108060352a0010b513282030780f141c40003a0010072071030700d02c41c80300d03000c9101c0170b2207024445d00b01410045000054081c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 884506267 1250 884505017 884505023
    0x10e121b0a0f050603040f051608100608120a23070b0c04030206071202010b0904150c020316020d030513080a0c060309020108040204050c0c01020f040603150305060a0504110d03030b15040f03 84
    0xc040007282c2004010311f04000c00070391000c00c0d41c0031080d80581078004c07a0001d00c01c108180c859140704523a00d054910541d42070710303a50300c05802407000c0c1d800e10400550005e0048400c11036244101c2c04440e030440400c101d801c0125604541d2051281001005c812004d0050361744054108002c00050792001308030b984641c0d000283d0550060310103016401001c0412a5540042e01c51041004200c0c1040ca000313800c0307500c44804c10901983d0a0100e99a00078040000c0a4261450402015103003105903407044902c40e06e4000c0c98007041343d0b41c5000c40307852a844503000d170340b003280c110040004003180507001d014035203020403010300d8a4000a241c1e14010f000640507507500d1022481e0407006a0403204800c4004000303640d03071a0391b1202c0f0400b0750312510a0500081c0303466000001c0344803c8080c5802c80b50808010001921504c07821401031001400c02c42d016090004090100d03115665800420303402514001030041c080c1043c05848000c500c0e00d0000700100300814071680000e08620310070350360 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 884507517 1250 884506267 884506279
    0x12070c05060301321002010c031503030801030f080906070614010b09090a0c020304150503090c120601060e042309010f050c0d1d011d0d03060b0414010e121b0a0f05 72
    0x620361320904e00c40075004880300e40040098504040b01501500301c07913044050381d5130400c110364440c07040c030b004031981c4d01004000400300b00040010620b0350540f00304941c00cc05107030f4a005180340c002480c1f80d10013041250800e482d031214829402c0c0d000302960041200462052400ca1440e000840f004801010f41081e9540c42507000710a520820943d400b0f080410b1840d618900740641c081c100750800c44150302e26210b140c42d0103007a800c000d1030311510040040c0c0109416400c202c03080e02e003094805611a0401d5803a040b0a00c2040c406d05e06101e00c048001c80c980d110b0925200c0c0609480d80380c2c0032205000c1c2481c0a0020311125402200d524609850000455014401e501e071a1a00c00c1083e1710615030030181c00100490281040d02c4400c0c0e0098100e502d03517900010141c00f603440910410000c03880c180003c01c070079007001903420f5442c0f20524040d41c894200d400010908007007c00a40c6180e0711442001c0d03144c0c03c0c0300c4075000e0086c0b803c441030b0b1203035803800e9001c2d09001014015a40669 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 884508767 1250 884507517 884507579
    0x70911030601110705031213050a050d0311153402030924120105090106030e0703030c08090316050a211113060b1e070b040803130512070c05060301 65
    0xc060013110090040182611041032000007035103456080a5455070000503440300000e032501c1c00a0344c078400c648001c0d04440355403105481c20384240c60141034011107800340c00032014169030320010461142c21200c0c0c5660040d0310400c0000d041c0d020303079441407400d80c24007900e070400a034000040c0d840740c01044a03580c1c400038034480714181454402c0043c1b0140d190100e82c542094004034101c0c0d042c0c4030306072001360191f81d0701c1038200c01307445441c0c01e4900150002d20302480030034824950140032500130008a440c2030070070b90110740f80200110710380549074814841803217246403d0070207c009142e00ca103051001c0c0090344843c1d910b450340c03440040c41c0c1c8090900b440010740303401c103009c1001c140120080250350f564110b01c98240d44120301c0c2036035000b001c003140503165100006440106402c240d200e0215907559a800d800ca5101901d5040b04c07164201000c17000030b40411501c0d44080801038117548662207858990341c012010781100d0f204400030300060100082814003250b0526094420442d08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 884510017 1250 884508767 884508797
    0x1515020c060403050c09060315010302040b04020408061603240902131203180902070f1101050d020d06030b010f062307020a0e10050916121407020d02070911030601 72
    0x2901010101d411030404035002040c8000425080410301d81510743c0300f4503541d80c004054031000248050341e200c82284d8010300250500d0f5002c07964415002d00014941901d031881c0900e016000c44d02243d259180e0031450581d2985030051019405a11030506504c032240030003140303408a00c0c058406440e074003058904c1c100500600303030401030200310100b0b80c1c2285c048c28018242c004407585209290138804000078441d0b0b441c821a408642c00c41503211a1710016038070a500c0d0780d516541c0354100030301071201d860b101e0040c0c401050a188054000540b8500d586041021100160b10264455004803000c2141e960403803800c07035135900481d1050402180d02c242c070302054003410305c029400100d080e0300400e02440e030180c00d80c0540b03035202920100f9940c40081041001c0e086480080100b4411010429103014000b034200005041c400480d2171007101d01510760a035411911640164030240c403004030160148141000b03041840340500601d000740740c2e800001c2c4000380c81c487c100a0048404082 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 884511267 1250 884510017 884510023
    0x307180510031e0b0705030123030a0b090f0f010b01090e13080a030509100c05090418060e1c0801030507050d02031f0204090b010e0307030f140706030c030f151502 72
    0x91684000c055000c1038150100a43d48052038008039510a21813001c55940e90250056078102c0d0b0510744200c1d1200400c201c0d515102455698068061050312a60000038180341c0700c0600c12041c031401800c038458401e0b0010301d409100d402e441800d07450000c218800b40da200d40c4a0303058481400404070300e92644c0d000040246801e400181503000c0210f81d500005505801c864002c0380c90000303c0c3d00340c1d01c0c4100b43c0c2c0304862888880b40b0101b0010005d46108c1c1c207080d0004030350a215411603804494441d11400143c0d404a000e044890f0442c80e0203c4d00c0f11181e99100714150007034038004d4050348c107540c0e4403555a080390080b14415400c1d2a01e0700c08556040041400c40460001c0340d100c02d04c12460f08101942160040c500c0c3c0c1030500e1280c0103154881c14243d1040301d4001e000b4030000c0c0c034546900d40c181407401016200740c607243d002e00094000800041008000d250380c00181101e13101401003c8039980780c2200203407410848403013024034240000c2d00658516455a220100f40c0400c160310f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 884512517 1250 884511267 884511269
    0x905090f01020a09030c140d0b070207031e121806140f0c0604050d14030c0a030b10080a050a0c1e050d1406030105090c010f0f02030d020417010b0307180510 69
    0x4010742c00095854492940b202c569001c0342d1044201080142e01c0d50341d2020072101e04644650014140d0440c4400300e006101031a400003201d006070b9480c2d03030b02c945030403036042d061150300e501c08170b140010309080190f4285d21410380700704c0b1b25103001101c5035203c1d407200b0f1545500ca03800800403012492849583e01380100e400754914000e13102d07913486031011165241d2808035402e55244c011030100c0c290050103000b00550405510044c14550354450440c003c00b500820500420180d0760a201c080c1511210800b09001016840f56a007a18029000b10183c50004000030101400c008004d044507400c410100360403030070000621417030000740c03c00301d9050044048006079207082004075403c441d07414040380d000c0c08090f8001e01c210b584030080f0960721020800e410340002c242c81050043c1c64414208c40710303002d059105592400c0c000f084030f1402d0360420381040c030f0060b0b04185092888242442010240203058000c3d1135014a0102c4110854183c0301e20341441d03a450b00f0018003d055050342c454 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 884513767 1250 884512517 884512543
    0x50406121401080c150f0921010c11010e160e0615040b07060b190b070615061d0d11011202070f0503030601090918060207051c030e071a04090509 64
    0x6515a524603d50356034201c150011405061206806140c07440d07010101c60a103a0303004900c1d03141c502c48030f0911003032030342594030304a5051101402918030702080c081d4a22451490307030303030881c41c0b001034403428219048843d0000081d4007004480d26440d11840c110000c0303410300c551101c3c1035541d403404140071600300e038905000d026000a0100d03414410002800c0b03207138080d880070042e05441c20240080038500d2072000300008170055041100342d9640c03004092107841024013041400601000303810000064102034042400e0880d0360440b05c48050103c40840c8080b1913007030900b003071520383e1407084e040318680d2810070070b00f4411105198050b030100d40b0203692102084215800c43e0501545907001038803030500080503800300150004d61401490002801200c4002180c88542d070303036000950105200305d40700e004010f030103c0c152404028a61840e245924085402600c0311203041c00c040054001c4050070039144404c81082d45468140d90541c2c0003d00c00040b55210760f43e01c14548400d5820300c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 884515017 1250 884513767 884513801
    0x3020904021e03010f09060b03041212090b01143703050f030406030e1515040b040c0e13060602060402060d0213030804150c0209070806120d05040e010b040605040612 73
    0x31019281c10b03401541215450351402002540352038031181540c00d50f100f1100010014004540070550441d28200707000c203582010f8028074004101d20040d41c11a1005841d500c0110004009101c840f101181c0c101c0400c64441e000f492158400c1000fa0f181c242c8d181000283c08400001d40220828080300030319041405c5442d110000d8280030350340c0c0d011340964000a0308080c00c070301d0080b10001c0c0e110f10b030f844114285466580c1c1c03040c1c01070f012600f8421496100d911840148401d4542d841082127410840e41c602c120b40c542502031102c9011440f00c0d08088a1038078504004035680810320541044e41240d00c60750b0340420003060006409001c8040c424044a00c000000b00804480103100f11080d0036415015200301c80c1c41520840180d00c8040c3d0045d09d2540042ca1680c811041d290b4401d10090408248440b99803815142c00020713240c05001c50700001d810b1040124050285004101261201c0e1900342400402000e45c041c80c46218180080c12958400c0140182c2140441032181400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 884516267 1250 884515017 884515057
    0x9070c140708030c0c1504140d0212010c0e09150d1a0112110a120327140f120d0809010b060d0603030f030501060926030a050720030a030302090402 65
    0x50b143d00c80c2d004141541c0786100e011801160b6003880584860f04c50750f024070181c02d00e03290000034003900340201c02d1598004135031500240117a40b040842d1128031040740001860701c0074400090302c4080080da10510601d0701d801040307900d2101007684285060155900c03032141c00300d490140c0620451290785008001071030004912070301027171001c205841c051103070b806020780554180408081d03d17014131124204410b25141c0440c1c050319a0300031000485002d8a0244030704961440221002e411011040d455021000070600d001d40131072428400490b50703071a1005013a01003c0da6021820404030038001c45400203000f00304290b00c000132154029040031b03540da901008607801440580007c80100d0300074032075102101d1080c030416050741c81c50b0703e03040a00740c1004040c03164001480300041d01d141c100c80007a42900d80c188003500c1c0080d49500d03140c0d1103005a00c2d10030490858001900400411400e2500e195030740051011040344e014200182e4a441510204010341318070080d9102001e001d010b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 884517517 1250 884516267 884516279
    0xc080705010507031506050a14030403021f02130b0f04120201110a0302150108031303110a03080f09030c030a0510050411090916140f0f010516050d031a09070c1407 72
    0x1101c13100000507000300c9405522818150390314019440390800027803002c81c003807031040070000046802c14001d004860003402c024a062181038801894550069008955500050b003002d00c203c01401c2404566802c1918006600310700303008072310480c0b440e00c03903100d08801503902500012601c400110240c5101030f1340d07400c001e5691003841c00d200c0070b014146000090070840110680b811400c04410403002140f8680b00c18400740e54003112181d0094101c0300000000764000020206130803820000c40c0ca0b404203008041c1403039117114a5600079048180d1110004a000c00e0b074034110f41341c3c05000981900c850600b40c2040080e60305050b088031080d418400d08a8001601950b90940c44280c12130140c5c41c0d0740b64062a542e40f40f400764001881c0c049032507041c50081d942d036460034818034200342002c0b00451103140d0403044410030342c0c041e0845484401000d500d40900c502813084107030003440e540407400218100c00030050414013009121000d1030700308141e00d0020320f0040340800c00c441400303441c1c2c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 884518767 1250 884517517 884517521
    0x403050424020c010831020a090207020d060905033006030d0e09222001020703080f07050c1201020a0e031204060f030608030406050306030d1106070c08070501050703 73
    0x100031000014560401c40207803080c07911601e500203989601034580c0b64803600c019245401c2c041e001a034071a4056000081000b11a401004201c4120b01d1841c0148542c0c0107101342010300c0d4110242e0503004002c03850158070341c0040c20302c40c26400b80001074034007050309041e070030342c060400c6082c591118044520940c1c10252440001122604050a0036444901c01c141c1d40d00003070094000400c3d94004a59442d00d4100c8001ea405011442420300a0480b041031000b241543c00c421035110b49510800440e05a03107401c0d80e42100404e000500700103007075840381c05080c01460b60040d1100000141c5c0c03c10000d05000c81c03aa00c182c00f0b0b140b80c5480310802c2004c1d02139082007210b100001c00340b1540c01618a00040c01c51050b40741c00802920f030500f0024100d03058020010b08000b45170300c1d01030008a4000800041005100d555501130b107034240241010b04007500b000b0701c4000c00c4144141c213800c1a01c04900540c01a00300c3c104141140c13080e280c0281230340100d04000d07146528082c10001440e07019 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 884520017 1250 884518767 884518769
    0xd1d120309011d1522060806010f0207030b1e0a0c0813082a101a010e1c150b03210d140118050c070b0105010f09030203011a0a08010b0312070c05030604030504 70
    0x10001007030a8035188250305c0102962007004002401000440d009501481d4224403480c03140c030580d5661616600c40c0306003900c05580d100074808921007001c641c021b0001d13085811401c180c81c14402140000002841202c0c058622150034401d4440f190403c01d03d50101c494121640709001c0d0b0703504015816002d06941e080c0048014040c03038025220710146480741d00c08911010b8000b4985c8821900111035403041e21200f80d070060300701c03000150021307070f80c0041c8600036110301c1c0841c0e00c0030302001a400075a203044a00070b0003503028241074041c0144e103074001038806c0040012a1f840d000c580f0410380c064088901a215180110000480c500107144107222034850304641c240426220704007200070921820601a0100b51900f0051007150b204080104491410340b0304070007015100e40011303007102d8590030f0b58080e40c91000300401681c106a055400203011841c001c0200d0b107c08808240c80d0804100070000700c0c1800203005c0d080083e01090768010705006801c45d4004d14091501501070b601c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 884521267 1250 884520017 884520037
    0xa030207080106081018020904081c0522170d0b27150a0905090a020315010f0e0a0e0703050303071d150a030b030d1d120309011d15 58
    0x640c80d0115071250140255412203003150300078202540c0340400000207204012008048030103000d1104050390301d5220090040c2d000c0c00b041360f42c601e51178040b118442c07500c411481d10759007403100b04003986104402801c07008080810301d0400d800c50749420b080900720f401b4039054109010901300c00785d19403075100001070718040e01c0d184600c01d0040103100300840c180c00c2030b103203081e080d000040644284804000c26140c02401c041075003601c42c1131031800e40f003048a074481c45a12090f4503a007545410440710040f000c040c000300856505001c00841c90358402d0190f960b14288130400b20300400481d505c03041c0c100ba00340c42515071640d103c0c03510a8981c1c0c01510b065000410070201b48104518a040e083e03d051001001a50f0080811811008c1030b082030b000c90041c5a5100c0942203d0349080c400140c1c1d8614555800520344015041202031003074022580c2c1c0904100700401072808400000c8401d688000d0800400c8082c48200840510544580040c1c114441421201850402c007000d4915004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 884522517 1250 884521267 884521273
    0x303090b150111030f07081308010614030606180a020a0c020306040305030709142b170301090f050906130212010903020c0103051501021b04061d01170307120503100e090a0302 77
    0x141d40f0881a40d80c051116007000d46541003000400058018000306910070f51984d034003112aa0b50301e501800c56409600004e0791010b80403030402c4500e42404802e51108088448034408a460544011554401444c004410740c1c00a46005510f0196030b000d00740390360041c211041c81c54a850010000d800944940e801319500d114081010359090a00e0814620301805075003241080c114200751000b424072082045c601154624070210b942075a00e2486581040c8402e60b40354502a0010100d54030841c0f042910361030071050102c0070b4008204180c000b21034800c20b00d509401030001032500d1110381d090a20395803801d00788408064021a240310faa860980703007041142e45107003403641090a034501c440c0c01a0001681040381c02c407060820599024082e00c001407503030702d41504000001942c101400c010130148c0041092503c0018001c2500d01100060b500380b078240d98803264841340c80c0608074148000440050f446482418500c0e00400c90035a01180e00c1c03e040012548680c0c0b01a002d60040c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 884523767 1250 884522517 884522537
    0xc0c01080601021c2102070606031506050a0902092b1a07020a14190501090501270305094203070504090f060806091501120314070303090b1501 63
    0x2d030000c1060941d46a20b520140c0310440100011984c00311004480700c0078580c4000800105240d030b2000d05130061090800042040c1142480c0c4250480d41e5000d10360b96042c0f10040c00251038a40b00d120460704445405a1268102800108210b1300d0b403003c69004130000c019050042c008503041c200302405214450b08503046000a1624440110341c542c0c00340e40500241d10026451004920780112201c041d07a109003206403c3c5002c80c20055003d540b2a9168041e09050040030700c070b500d01400102c451034145c5205000c0f20100075401c124003070240710780824200700507110000d0790001e48084903501059007419440e520000103139600c41c290305429800300e06140503148821240034010949940d42028500064030001e0314240907000c0046031203113130000381208100303da64024078000010345140740d400080f5082440341603004d50030501a008107503021079041400180074203040c24080303517181c0c041d0500350003412502c0703002491040c0f5601000350f0f03400c4070100b00368001c03800d0340d40d04049 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 884525017 1250 884523767 884523769
    0xc060510051018080706090e090105130807080d091410050c0910050904060306050118020f1603032306100305060f06160b090105371503080c0c010806 66
    0x500a00e00501c0d400c900007026a100d024050b03550b500701100d80d440d07400c0099884030500c030308107201075000c80007113441340c10240a682428428564841c61087c02000f443ca48a0340542440c15450005042082d0025150303080c0020203080b0307210078041e00400d100c89031040c54440c5030300c0309591540c81a4002c1140c034094905142c00340d00d00902c1140301050810070034404000501031469070300810b025040080301520780b19401008000c41c005c96000840c0e40c5044090150862110841d042e50b600c100b00c001001081c071030a443c220300c480e80060065280c00c2c03030254002c0c8441545410000d810f0706580c50369031142003009101d030345c0541e041185d01a180400ba4155442134844690080740f078400c11405003407200282c10881495680e8035500940c5454020b403082003518140081d035151804c20148280700c1006a1950342480c250104608242c00d440c0a2038480109102e151500c0711001404907008050401c003651b00072406566400b0100307000b81d5601c90510201c4c0c0415a11400a042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 884526267 1250 884525017 884525041
    0xc0c040509030319021b16030c0b040803120606160606090b12070b07020316080609070515180402130605090420120c070b0f06043806040302100c0605 66
    0x240312490031184402e9001304880040d4200c48591510078020700c00780d00b0f19401c00c10904078800c03071402c1d28414a0b4218105800e1700c3c0c0c03860b0040701600004000401649000102f101c803044c000c0010300c1d080342c079018005149441081d00c40c4200c084484881414400a13a1000d0110b03806900c1c100031000c005420310040c200100101f6484c0e802020707080100c6400b5100a00c48103100901740c2d410142100c14845494000d81c002d4002030340b1100070449000c8041150307502070101190320704584001030f501011a0721804400011103001d5140c0400d80e9112034050f2078026103c0100b42c0c0b252925554001d200d90030290066100780d04021141100c03030709109001040941c040580c9151031150000c946420002070f1041c0c2401340c040101001040301035000c1c81c0203e0304004a8421070501c1c800300030a03600c078030200d03198003850315242d0011510b000d03424040400c3c10101d0f9000c08400702000a400f40965400031f50410030504d00503403250b5000400d000303442e20541d81023115448a20700000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 884527517 1250 884526267 884526271
    0x10e07051509061806120103050f01050c071e02150d050115020703031b120503042a2c100612050907030f1b060e2704080f0c030c0c0405090303 63
    0x18a08108000b010b40c1400d02030020040b0008607241c4903030340b0f82d00d9008110b160303004807044000102c2a078014020004c0502070407400f1240d100c020700c440e040516001d41e040c8142503006080c42c045071002500e585029001842c096001400c41f0312801102e101307082c150703010a49079000c5510b400d001084c206640b4040f0612084c040e4000c00c14281550f4081d80c5018009010728483c03034118a0745d40010302080004400ba00c0c882d0390345034903401c0034034250b031140f44070b210301c06400e440804e1030780c1e41c02184e04514021100c1c44031507600c00007941c0f103045001c400c00051050782000008108900981c078210700720115101580c0c1e43d03c6514210460400b00d402c180c0740403072540c000080410100342001200b802d410302403c00f914401c82103480c1103480252551152021481da0b440c0c00003507141c8a0403036040380c26440ca00c034010081d001d060180708040101300034855503001c10808800c141c02c0007900d03200c030205000c0300e07620941309202d903560722a11014a03105908103000140c00c0040842039074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 884528767 1250 884527517 884527549
    0x110a030917070e1f1509031101032306060d02070c060e181b0408061504110c060402060a09030b0702070828030e0f0604060c170301080a110d0b09010e0705 68
    0x82c540384e10807162140e00c080100c480441110300408035840c440e1404400d4421615141e401c0317114554070300b01c01c032000c03110035050615140500d1040b1644608409180b5182c1c6407000c04410794a00c0002a0140129400d904a251020814008010483c0700300c1082c0d0b9600c2c0c03681100c5401e12402c2000e02801900340f205400548008100d507940300342c0d600781000d030349070440c581807a072a111144d00d071980498055070f40342c025100c80032003414140301d29105038948018683c17070905410005a5120000340c0020301490f400075600a64600c1405054091170b4044429503440c01d007250700079a60002805101058060515080b0a5a00c20030358840d08040d11858004082c019840546006103884862500881d004000001ca551400b0041c80502481d498a034280030603420092070700302d02c1c03038880c5c21220002c00041c0b00506c00000c0391204141d2002c040c0d6007440d260b070046210f0129410000f4844c05011061048418040d00304e2038515101904855166981700308000902251356200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 884530017 1250 884528767 884528789
    0x7090b03070e040c0308070b0708091b15090d14010c02010510060f120606030c110a0c030f1a01120516050108010b0f0c100c02100515090403110a03091707 68
    0x40050b16030300841070394014015081c0c01c04259991700c1e12001644903440480d807040c003113010401100c1c0c000c5010740d00403428400501880a4040c00449140b0700101141e1003681c804809a441200b01d10440e4842c1c000600810307181080c03403601c1c020048042c00f60303105d99402e108c1c6000c1d48920500c2001d104046144140348140e20b015019200bc01c00d0240344003c00c45511068004280d02d801b6840040c107040e540000c0c940c400c01382c02007035080c410100e015590429103c620105640d00301c000140c0c2e4211a4611149081c0e01c2c00003900e04000e00304040740969800001003641102141d42074040c0a44251500c45040d10b03c5103080c0d9a160258501040010005000f08201e039030280c9142d1108451482c601089545c12510700b812198040120725203540a808101e0b5043c85202031460781c10710240494106401952000c804e903000d1180140e0007240094140f40c03144c0100862152390742c0559405072400d040c020041d44440c016250300d407070901c0c03140004400c0000c041c4c046510036004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 884531267 1250 884530017 884530019
    0x11a03120322030509030a0b07262d090709060506090102100209010e0306090705150c07050409020406091d0f030c03031602011d010510060801050f010804151d07090b0307 75
    0xb80150552402000e6040140c1402184080c3e102007108070100e034001c450480e42881d1070040180b0266014000e19500000b10360781182c10700e103040c0000c0c4c000248518601c0d030240d0140303405c0c50aa4609014070b0300c98400f64180142d803031010641b44261041800107101164a442c00d011440c03095102c2140140e11032125196101c0d46580900701413038051410090300200700300003a20b000400d031076015031a00603420422062a11520f08603281c2c2e0540c90781d5007452414684551078092601c6403500a0352107006143c219902d9a0200000c1d00d0040000c000450b8201c40e1551510405142003800e031203020340e240740468000040c0c90b1403040d4200114515030752060003d0402c800d810001c0107543d01c4a072902c102c40c0844407003240340e0748900c0001400d49040d56170880c0741c40341980500203100e41c510044c441510389801c1c52039101c6081c2445210b607180c5103488184050401e40e041d0002e498008c150300c60050440c080c85554040380200c0d00741e591203003008030441e84103043c1d0503855400070308 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 884532374 1107 884531267 884531311
    0x406090519060503151f060c110a050d08211806070807050306270106050702150f03061c0b07090e091606050d0e011a031203 55
    0x2d0181d00c0c0703484007083d01c81300c00401e0101d07024600710002d40c0103e441d0341004c109080c900011003d107592110001e28017469400300702e0f0300f15841402c020303051030603005030f1003540d00c010003402c507a0166980340c4007241d1000148000c002e000c448480c802e0043c0c00c3d2094801c500641c80b080103111000021411310f2001000f20303050282000502c542e1680c02400e907603214201f5103406450400c01c000000d01305015a02c24010310201200100d00d20380e20101a18055100780c40f0180085400040c240b210300034100342660f841c2040c40002d14a1038019a48020b041d411010900c03201d0b00707601c800d03150070002c850701008144404004c2003050100c030000f6511450000c041c0c200c120600d0511409aa51407248404102011410360040111540080c1c1c081940c1c1e4004c100d440da5040a580801e803419651034403a0180400c1001110714800840348541e120704004400340322206 = true := by decide +kernel

theorem cover : BRFrame.Cov 884352517 884532374 := by
  have h0 := BRFrame.cov_init 884352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 884352517 ≤ n) (h2 : n < 884532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
