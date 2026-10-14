-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2795
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:46:07.953774+00:00
-- url     : https://prove2.me/submissions/baedb22e-3c12-4ed1-a160-e7fc1fed15df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 502517985 ≤ n < 502697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 502519235 1250 502517985 502517987
    0x1c0216150e0c011103130803191128050a0f12020a0f02040c031409010c08010605280302090d0b0a0e01090f0303050403021002031e010503030c0703060b13020406020d020c0a0303 78
    0x78050782c0702c42480d06158128141111920310302038426030154540c5804000a260000007000f481d190b1003901010505002060050341c154141d03001182c1c1d0303074001280b8000f20301405103800c900c030f8107800d1081c6202110780d126030b0b11f444418001200c1d10700250201c070081c80440382c00070840700014401001c401075903942e800845408110001d02864503540305180381c80c060f400078100c44400c2c40c420b92486c503280b807085020705042070290011418034000860f11500c40e50459040c00031604615070346100a0031f20740740408140464804155080c40f5190385551182403c2d2082406201c1c0c44405080400c0018110391159001381c10311381c94560020002580080740d15141d81e010305000801b544d40313003010390403d040142a0071409100000b0403030900b0305400104c02c205a04a04100d45a0302d9200303150740c80c421085a0541d5034092070040001407100c1d04820249003014081808061034102c010003680c00c10f4102c0400744e0032510641110303070350420520380c0100c03086079841e5441d495614 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 502520485 1250 502519235 502519243
    0x606030c090f08120309030f0c0a0c05010906170405070e0703060e150a030b0a0906360203060a020d020702030a0b061306030c0501270f080c04201c0216150e 69
    0x40204404c1d003010002903280a014401d981c2c1c503000c0350644a0380c0d1700c00142d1702c40e154600e403001110700040303201c408140ca5206104c400d00391140c1c1e44035110101c0c1c049008444010004008407202d1091410100700d000f401d4030b505010386003903240441d050b030808100c5400000d0040c003011090a001e140002035a490803140720449030050a03e08942d00d4a20b2a14040c190307107000544140d09040c1c0c1b540301200d001038407142c02528902c0c1002c1800b2101e00e80e2240827400300c1c010f58035510040c04220102d00513802800c114400200061400c051a0b0200781801407498003030f209007d149040107140d0408103010704605000d104c1c1008490705694618580d07103100e0040d1410801e180360184a80891220340250130480101045003a5960301d035040244c010f64080c000c994050100103101e00d05003409003110b00080c0782100030b4910f00010480340c041c0c103c19401e004405112103411508640c602c01065170f04400120340c2c810006500300444000d00704801170403964600803c001103800042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 502521735 1250 502520485 502520503
    0x203160201181a040302041d0d050901030b03120703230a0302030c0f0c06162a020307030c06050c010c0c050d12021b010f0e150103080a09090606030c090f08 69
    0x10910401090080b01074211040458109442c008814403800d414a0188070140c402c803803084600b405800701c001d00c010382449007080d00c102194401c02510303912074020000380c201d5030010b01d0001805402100001e03d0300c0030000664000e42000aa89000c0c103620600c1c400030300b2144000030441c01c46074a00d0017094170503500c200041590100103c6c50b4110404211100c10440c446800d4580304a0107226403260030a5800d051041c6840b5600e05100380105100e00c0201c95240c08104034842142000c46075810224080b640341c050741002000180301d0105410281150f41c4e11326032940400429542141c80e119406014403100500d44d40003e00b000540020b180140d01d000c00030f03110f518000c800a0b008000079440b00389120400c0c0f0340075210550041e4055000c4500601407010304918050712081d442c80c46820f40150940140b01255007100249110b40e00703454418940c503034135414182110b04135040500069251103400715402d50003001c90f4041d140051a4071481d80c030f000c1c82c00c0d654003150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 502522985 1250 502521735 502521737
    0x601020a051c09051201150801060f030609061d03070b0108070f060e01030b10030b0f0607080f0705030706091406060405101202120706030b090a0e030d180c0b03160203160201 77
    0xa040d090082e80310f04107100040034098600c4400814150415019105c1800620301c881035902d00021a4001401b03242c1c106c40f0003800010075641551200c0c0054200c0140551ba0592075016210800148040c60b00401c4a160003468072403d0301e00d00600280030603408400258840701040c00240d000c49240d00840d425410000d4060711001d0060f0094410b40006540c410340f603800c85039001d9015000303002030010403030380b442c5814141c0040002c1402212400b03801c141c01404401040101480101042d90051049030704040381d5a58007001c0d600715001c12540c00c01840005002d000c01004030a8000804480074001860210280e8003018041e10580c18081200c16680c425503d484401c843c08540710b80a56004036201c0743c000d0302400145108a01500c0b80c000000c130100c0083c0714101504040074082c51400c500b00e40342d400940300e14036010a82c01c840900100010750700002003002400d91800c19501c0340b9204405040c0c810f0f24000d14425900304100c03500c45840709283c8950103982c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 502524235 1250 502522985 502523023
    0xf0a030228050322050f070f0e1e040317100e0f072304090603050105071b030f050a11010c1e03090b13080c150a0b0d0209180c0604030f0b0601020a05 66
    0x1040d030b10042c2c04c081640094800c1c040d01c80152914800804c0301c1007a101b20292190403030350356600b0f240c500c110031954a440701002c00c9008903045034410304076422602a1910516032444074559a8140074117881e02c0c060785110000c101304000100c0a0961703c80541425030070907282c180400340041003512a06440038900c503a002c600407131200242c402034955820b0410010b40c480c5007141c004d01040c1d50783c03008035200310700c144221014400d540c44001c0d4950380301103a0310b001e803d09545070b801502c284010f0003c1c0c080114515082486801c071030105a070703a401460f4040b0400031b45600d40c0607403036004140c2443c1e900c40101e01c94246240e0444100a02e4014210050505404901510f03003212442d00801c030300404544014058135001d030641d090108003511041e02000912150003100a41103485100002d0360f060038506e85502e0f48105070700f0f88403800b0030000010200e03031040c0c008035418010f0401e21401d001455403140c0e0300001c28001859240c00301d0315008ea1311200f40040c2d01e00724031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 502525485 1250 502524235 502524271
    0x30c04090f020d05281b06021e0316050c0429150f16150615080a0f0f0f11030106090302060f091008010e1b0901050706020f0a0302280503 61
    0x244c2040703c0200420a00c40700ba14501100c2c0c0b40c0e491800d04050161004078018110100310480c0c132604404480c4ca6800400710307502e1043d40290084090411107072180408d0004250004801020041c100e11500107085588a044100422a82500d039603602c540c15000d80c041000c040c3c10b0511150450403210b00c00380710181034940565116403c5d03140b4004001007480a135104003401c901d00784a04c5210b01c01112201a040903044514030b1040c0f19a51459048024415000b5030129400841c901c901051f20032400c45982d09a5260715080c8005942e00c032110048250070788982426001034a441d140346501d0014000c120300024080030313100300000550540d962645000f01d50381e07254060020f85215240102c0070300f54001c244a12a41545c0b0000000c00e01c20180104c8984800d05045a45c20301c080d4100448070750b0800c4200315680796080250b4003c140314040a4644551107035405079650014848002c0b42e48044d00041c5106121500e458004903001000d8036400180d486c1400e40d000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 502526735 1250 502525485 502525493
    0x6010b04081c1b111f0212070506070c050f0a05030a09060e090105190807120308090a020108040b0a06032a05060c0a030e041d25050d0b09070803030901060302030c04090f020d 77
    0x402c0d900361319400144c480c0d0071880c08201c6003140701420825000c1e031382103480891045080d0b200317561b0020a640c20840c006180366000d0440510760034040d500300c42880030700401c001e2503c1c0c820401600d40d0341c0089011003507035512440d81c00c0034148900d015842c0c010f0500c0401c1e0030507010b0107034600c245110308441c069425503c02c1e50b0003d2503450201d6130950358908004030b100e103845205800040c81d05000588001d40013400000e45a4103a407104016034850315800e04e50361001c1e2000c0380703003615610008085000c0109448070300d0b80f100342c0304044840d2030703c0c411000b220035440507008170821b20100410301d50101c0c0400d00c0c00e4041c02c000d9010182440010000c0003401c001500817000300d00c1340c16400030000756403129007001c800344034175256000c42c0003428040305105540d0b0249000751907200040406102c260011000b0084031003558880d0790450964008031075480441e0341d912030802c00d41c9001c1000c82d10100e0180d408000c076002075217070402142502040a13000e120189812030401c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 502527985 1250 502526735 502526753
    0x12301090b030a080f0301060e2e031104030c14100f0e0406150305060a050f0d031803020306090607031b0c02121203070c0b0105102c0306010b04081c1b 67
    0x10307034130081199444141c150700c1c1450b1703082800b0300300002d02c0501054049041105002c150880011a12030080100b0f18823041880313a55600030003016140d10b007444410040802510186203d40c0a450a10341418a44000a480c3e810401d208100c107800e035041c1950081c035620440074039450720035850702120011030b002d801c203540a200e601000c5044084119490f600040c0640401c5030040445c5581d50100510301c0c000c00d03122035010750200c4841000a010340903912100f0300c00320b030506070b003030784e030307000a41042411110b841207a0401c2d0200320055a05215101440046107041c4442d560060001040e001030141e0080c0101107018000020040800440b081440302049903a44c0e0710b0143c20082c030094030b00c5001c550041041c000441d0900c0c01184c024203e0350704d65503084494012100004c2412200078801341c0d00c2006240c0c00f102d60701d05110b85406050b035144015036443c41d290116280c11f0681c1d104a09400340f2011040400b54460b0740ca40280003071285e56106030015040440d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 502529235 1250 502527985 502528003
    0xc030210030b01020c01030e030f2209050103120809070b0a1707090602010c0206041203050606070c1e050f09010b030a06050307030f030f0203120606070c0e18012301090b03 76
    0x40080c0c000030982000da4107070084844110207900356031685400200540c00d4414034001c4424a8005000d49140b502208004d0b04004500c0504400395580380e200e006c0780121a504072500040d00e580041c400c0c40403a07100c90144c8680e900d4140c829207000c100349a164100b6009441d90240c001a01c280d8880c4134121244d40700000483d0710185050440b00941610381921601015500b03094416910600110b0b165200e0341e00580649074148080408400030320303005100d1a8001014020403001c24207144004002e0041080280b0010142c01e041e106802d08640c89140300311410034000e0501c2c1c80b4a90124110f4820f0700d200c6450382c440581c500b0103849560005d039010700c90040f00000f84410300f40000c1c1010b010351102a100b0344003d0040b61244618600240960003100c0821118107294000304002801010416000d5840380d1591103c40002e4407580d200b8150b02e81c0300e0b10101c0082c400d81034204492000c600d001c2c0302c05115041050700510a03002069540e22000d00203440a12040807 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 502530485 1250 502529235 502529239
    0x6090f0b0a0507050f0a050706050a0806040509031909030c090615180503120d05071404120f020603010e15040501050d03080907121a131509020301240503100b0d030c0c0302 76
    0x5251400746034010791303406405405444074408d010000400c2c0307009508a0303032200c0480d139600c4000e50b28541400080d0901034a100c0c81d510040000c1a148104440c50b584404c6095640c6c0030b00e00c1c51418072041070100d40c1c001608061411a04124482c455142200c190b10396040003401105034621420980500c2da0001c0e0f01030080309100d244d1a0204c0b40140060b0138408010049615a40700c202d442c030b000301c00d500701c201d041008244404601c03260110040d030320891849181c664240d0208d0826002a8806071061212009001d510803403c00c101104820640303081140f90325000015000c7e80e0410320207400c0c8651480800c0d00c40e0b0051250002074aa0206180e072200c06070300d0004181e140b9100d1508034800c0710030100380001c0c2416851180950840d442d000035507954442d502c010428505c1c101d03850341d40e0740c0c04840200040041801880240302e510004540b8007070605080c503c260701c681c6c5000380b900c01c880c542d82e51001c0302041c00580600e000c82c654040b510b41081c292440c0e0300065 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 502531735 1250 502530485 502530493
    0x10050307060e0114070b06060d091a0103120c03050f0903100e0f0f06070804080f16060b040c0c0803010308070201170903090a0806060109032a080f060106090f0b0a050705 75
    0x10030301c5a007104880a0b040c0007030740e5004002d03e8401c1d420115000e1248001c00c102c01a1004c6070043c50200e000d001007091170070f4001680d844590750030090b040468105695030b80540f0041050061141204441da411f50a2030714545030155401080f5200b001c118045c2a10041045c0001d81c4007000250442082c1080400c0041d54508181e81c4d03840c09210500c60500c03807080c3c0103402d018007180701d80c0218901e840358129615542d581141e541c000c016440c20f42c10090281440313101d5030702806400f4a018040000d440c0d6541c00a0100b980c1100c0101c0c8107012801035000c00054018003180c1c1102e80005101c2d0721865184012540c600312003200c690280400001d004402d40d000c00181040c900403103030001c2c00380c2d443c04045d8498108030752681c086954900c0400c00708000d0000e03c49000d940500394032240181801d80300c584220342d00242001e5001c20b881d140c0d015000c006460241c0351504004241502e040c070302c0405180f65015040100b200451580e100328090025115103a901100350b03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 502532985 1250 502531735 502531739
    0x702070902040f290d020d180c0905070e030a080a030e030703081e01050607030807030b030a050604060b0604080d03231e150607062408060a0b0402180910050307 71
    0x20f0801200d9801440345041d41c0e54440166a141e01600241442d0160381d80f609291684240d04000d40020142d0000f282d00c412202500285209108521500c0f17520900596801c2140100460320014403035414022008217070075280e80e00003484d45116500c010050344d110400e0b10b00301c018081d1050300c441907100c0424038004042e006481244110301c01a144620742c07640400b0860720560a00c24260446800c002d40c40c0072902c41c503201e0b84e0000190402203031070b0a814000c6071800344a020151910703000070b814001008a0340c01243c40310312040720300a0800d814242400c1c0c581050512210034590b0b82c403a07148a03a520041100081440010210790030f241402c1c011071000f42000d5102c0c007602910000a08280001191030501080503100500f001102d0381d031640204100074041e000c290700802c10750032440c41c0a81c03101c041c4c80f21030058149030401b12403d800307561001004034801c40c0113015a090030090301d4a121010300301140c0715402501d420782c0345501c80c185500955010b0086440c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 502534235 1250 502532985 502532999
    0x6220222051303020d02030f0d0f2009030f071410030f0504030903060b01020604170d140a060f17030a0e3d08011412030d0c020105010311180f070207090204 69
    0x210102c41d802a0259410360b40007903000c90302d0340300300202d841e5042403d010925254421b580402031410711904009400101420124000030346015001d450006c00600d01156080a12102d01c0d00c01261008084c641e0818501c40e041e420246165401002e174840d14500007132080e0001c0e05800a00202008241450b080c024034001d407501003a075440c0e08080c0105201d5100103105446250080d0b40c06150b00441080c0f58000e6010703404a51400340c0315654102082091201d072409041d103808001451841e0032080c516000440e0300980e00302c90030b001c043d010080c02104a8010000c03c0c58208a500440400139040800a840906c0c6804000090000e0804075086455050403280c11020b00c00c0800c8008650071542402940f10b2500d1a40d032003003c0d420800310f01c2c03a803200b84006903402c3c5560a00b003542200c10700c41d40342c80146e446034010414070a0030ba604010700721017500d9480c42c0c641240e0901d0102d070300240c0212801d0540c00006103050b4030a1005801400c25104150742c0d55980d084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 502535485 1250 502534235 502534261
    0x306150906060403061a042d1e050a0f050c040b0f091c12091e0513090b0f2221020718140604020a091401031506110622022205 56
    0x120780c50143c0e11b4541403900001c282c0526070740c510f48000c825000c11a80c3c0890f071016100c20241d0400c071010034850030a840b980ae0080e54451b2241060014421b452a0401d13030564502038000c42c44960100320503c25030750080110703240281203010460355030034888081901e030440c2208500d680405801c841301040b008600110512620b03580e0305a9554940c003600401c04904905001c1800500c1010441410080d1820755004a0a03200061400300c60311003000015040707440820100040c0208645405a0300126103074940c1d1110001e0b42c2d64030f076075500d070829070080440f000c2c03900d050b203010124030f1003001500043e000284201d103028000c0244407024110508883c2d02416070000000c05c07d0410f80f00f51103031300b0110380d00d41d40c400d403410001d0ba04820118503880d04041d1550b549507103000700d0440b04001001710b9034513504c07006224041c4908100b800303801c455a80015a4400708a03000342040410240e4040301d9083c241003c0c001e00c54905100c40303c80d030800900308000c001d100b5180013 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 502536735 1250 502535485 502535531
    0x2040905060603010e1204090f0e010c051209061b03060d050d02101103091c03060510050309010c0c0206041a0c0703030822030207090506060702030f0c010e030615090606040306 78
    0x5002402174070301015100c0d807500c2c1119070f20400e580043c4030400c68600d441e0010150780003c50b030b000807804090412982501c0b64145110081000003402601f0383c50000b0640b46d10007030110240c0000e0a00c2510320b94000507042108050300c0c00440400c20303a03078440d0348008203664050700300e07419130791182d4000c1d4a07620240200b00f016487d01002262034828a01103900c5441c1240203869041c0c01000ca0b031001e402c2c0c0c50040c00801d0f54400300861240c17111650b0700c07074841c0d444d00c1fa00d440340f5082ca500c1e400c1d16500c01c0d9010070001c110800c500142c0710803050720281c0c0d00340f0a58005509000e80b1202c21801079542e4034502e41b08501000044c9900301000314010f00c2d1b444203590100010070141c09442c11312550007030060f170054200300110101c55120130b4101000070312407444d150342600000c1c6446103800d0803208a4000c2001c030001c960b00002c044100103030603005405c040c604080014145074000d845613003c1c02d04500003e0301680e0751811100a0b40d03020b20100504100c46180c1e100c000c0101c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 502537985 1250 502536735 502536739
    0x30501050319061b1e02030301080613051203010e150d15110f0403060f0c05120a05100b120114030d02060a02030a1e020301051005030f1504150602100612030921020409050606 77
    0x100c0a1704164800306c01c503416244400020329198540070f0109000340b035035007026140e90042c0718105490807100741c0118000c00d209142e80d03c860416801e4000d228001582c3d8074415600c28506100060880300c0044984040400c00907415503034410f24a903078451140c0440301240006804030801106500100e100e50310280c042240d11042101650688581d0031803080490702c00001035000c141a0b0000d41d44030804103100080b0590311140c189240d0881600c20000b1007076a001842a00f00f03502e680d40302c0c1c4004600070419030420100203900e0f02406003125986030b1300040082c0d0180d8880e04120b0480c6070181e42d4640c18420b082c058130003900207015851092502c480d42290091003502980d020b11140c0f01d400075940c803401c2c02c44413082e050445240d000754840b070000704c050742d070f1000c0f94005090300c1d00036024a0803810300b04401c0b2000d07074105080c41414802200b0129a1040300c507016500110701c002c1c01c00101d1036585001032480e1754001d602905007148030080000208000313010b0182 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 502539235 1250 502537985 502538027
    0xc0f01050a0902130e10021605010b01080c040b0906040314060405011406100e030a0804080c01122307020a060f020a1d130b0d30030501050319061b 65
    0x16680400d802d94580786800b0b94044c100c40c006448480040c0d0124054142604c22151503401440f521801c1e80c002c207060b2000c0c42072400242c000c1c45020f0050542010003480e000340d003032601c1c4402c0b51080c0554054905140b001013600203031a203510301114061600300140010b4021300c134000b1356880c8021070382100c003942015901e50903820480c1c082c5014142c000c111044032910400215811807040314a964103100d000c41c80c50102d0f4118000b000645003007806040092649400948406049051740c0036040c81c0011405001c44800005403000750314000c0b805498403192000c91a010f298171000e0640d5140c8a0703100e102e1501c6034020203070300c40261a85421204403d000c9000280320014003500222540c03901004100c42e548015186d1200a250b001034640d40d0311007802c1060259200d0f600070b5a8010341803601d80000d400312258080b1440c003404190705260210361a84081820740c0c1c0c280200200c0b110130810160041540c18180c200404441d10800c2c400600604c04807011281003c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 502540485 1250 502539235 502539241
    0xc0a0f02030f0703111005180c150d150b0a021c03020a0f03050a06171b0904032a05031201050f010309031407020609031902180f0a1a0301020c0f0105 66
    0x4008000d680000204010460400c42c3c00d403000d4a03030003010900400305000c0c0601d900c0c4020000e00c00c8a00803086c980d4081c0300c0c5071500c800f0078070b04002e006d201e07446242960080c0d07a0494115007150020044c0641c08600700000c8000c058030555250000050003201103000c001c0e46500080c812b00702144040e40c20031145088606a04074030801402e403000802d14a0410a441c1c02600490741060702c803180001d485907506040105459517200101c102d0304110109001902001040455420201c8031007042c3d061968004c1e101d0074402740404448254805040001955030030008100d80c1c005003601c1e51a240c0030798209108009003e124850380c45100402a0b43d4824482d0300a400c0e0325441c0c640c039000d8491508081030300100710890b4014010030101945803001d100c00040740c2c07a112419002045144100424007030305052886000e4178240070040702e507550302c0030300d87c01101402001074407620060510010852864001360198000039260050541c00140d540080311140d0080005813 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 502541735 1250 502540485 502540487
    0x60f060f06070308040b0c04120302060105100801240c02090f190614130b0d121101020f0f0a091e1a0a050702060a0e180442140c0a0f 59
    0x1010ba00307406000925424002000541203980d10340c1c000000280c1d240c10b01e40c0d42e12201003400b5140504a0060308030700010095402c1040c503c0310b84014034184100690b041880788210880da1000c3c240152740103401962045000303185480340750780c0151a004242c0b400c605001582c92040e43c82039002c0e0381c2d81034000c0c1515290311582c0299220320b00f114240c2103c079010040034880441d07174034034850342d80d908102d030356603607525049091446200442d100c03624000d000760016568800c0314460b1f9004001c482108060b10003150010300403000700d0780e2551007007207084a2045003504622000000f02c5650f485951242001c0da040300c60403046007102c5a201d14040300b0502071740341c0200104c1c03c1808180300520703040c400b50509900303134030b0003114007002c840c0001c2003103201c10503410310f0802c410103110602c081280c0717204194a102820099070490401c8038481e0000b240da4000f059a01c12010001c0e284094020314079203545030044194904003801c984406600105861000c01d28540055a0003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 502542985 1250 502541735 502541737
    0x70b04050f15011a09040608330103020112021c060911070c0b0903150c07020f0316091a0d110a15020309060f0f030702010e0f01060b1902030c060f060f06 68
    0x1440d222584091991a02c3c0151004c10102e40d188200c550b001d1110603581e48540c42100020000f8000a0140c030780011142000028113860480c445440349007c0101c1d440000401411240e080c40d00b00e1010403214412402409600880301844110012010960a003a00030344203654091000300041200c030b4040c40031901c18100c0092806c1f020420804c1200c110070080c145201010b019501034801c0c0050381c281c80101200d030891882c0000c5041019810040039060450703030306500510889984280c84406800c492154040d0b043d01c842200500c8001c407001201c0024010744110007003c1903140030036940300717a200301c54002c4a4244000500c2c01022140320301e481015000346151a034100305000c41d55005074060060300c4810001a126514002c005520623400f590001611a0035580840d041540914000565178100310341400000c40c100100d400780c104c64030301e41c071a445404000b03a00314040c0c0c0074450154000c0c03a00308031080a100d00c10910a00044400d03c006c206078804100031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 502544235 1250 502542985 502543003
    0x7080d090c050f030c060702041d0f0c0409050312040c0b07080315030106030b010b030403050403170a20070603020d0e06040f0c0603020a0c030513030507060512010b04150507110402070b04050f 85
    0x4150700c221894172090801000030601d0794005040031400c40c044100421810400c0c82d4404001c0e80070140d4030440701014024900050030071107083c4440c03443d50320743c00d80d680102c42c08e41d031441d00d40c040418200060103035604001c10482541a40740c40c01c50504255a4200300c038200c04030780c0e2070685c2d40540d01c1c061003801d0550307621403060240740c2d08145220040d608024411401d0150800c0003101082c0d411034030604010b5060615a80d50100900081030020701142125609800303c15201d04281c010550300c2c2681c001e403a0050f21841c10f5880b4030054800700c05010362034022101400300f404058560761070bd00e4000e520101400d5500e80040301244610f1080200040e004058100028400c4008000503030059148140e503e40b6a00c4050030010350b5030190002c1240003603103a2081c00c07190740d0140145000b0070070340d040626009105200c04040c0c40c00b02c0411400003100c0c030800044100040b04024003810464444082e4174044804290980d400da40500c100d00c640c43d50030400050340c200c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 502545485 1250 502544235 502544239
    0xd0203180d0f150905011406040b0901060e13020d0f020c070b0711130e01052401020601050d12091502070614091305090a08070f03030e030705030304080f07080d090c050f 75
    0x140c03032400b94980c601c105012031404401c05456a89941c0818000d002d8841ea083c262500e010322401d01104020449103032241041c003030084030004000e1550019243c0f0007101007501c110700c42014000c8008004d03c1441d0b82500540d2928800040c0210a9405002a104618100c804440c0c0703401d03003005140645040100540c0c865030881040c0c0c10210400c129001801ca80450340f6407641000c0360a5401c2110010178046403000014908a4803403103d00082d42d0a00103044c040d4100310100b03406643c01c190242c42c03210009800007440d841060084010259424000041d104a20000391903403e1841450b0000c0d00c42c005042c104c1c5414022548282c40050100c50f0068180a040c405418002c100b07441d20b000c1c90744540c4c0825903490040070034510400000002142c1403801404413500c3e007130040390540c03060080a000a000208a80d0003940225950f070b120710707203803e64401c43e201d60b4600511503007003c500751000310b40540026207014800e0b08070490682d2a0302c1030081c0d601d90490256 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 502546735 1250 502545485 502545503
    0x21b160f06031109040f3201091805070b0901090e0105010e12030d020403080903060108070e0a02030405070f03080a1709030405090406020d050903040e160509010f110d0203180d 78
    0x1c0000d000340d002d050500059180e85080a044d2030003d030403118000d402c030303041c1502d40c5204092580240c03080c54001e41501c503840b55000d003050013401c01001c140102c803000d80d50703040c000c030000e00c0c030b4211000e985900074200e410541c1c541d10086803540002c0c0700e15011482d01d0034007007900c1c108120180e040c4d8806070741c2e90b580d0615840411469031030800c0014001d00003048070141010540c001003010b140030ba41216500c004003428546000780585c4000d9607074001400c10f000405464503215080201e11501603100c0d00c2e030741401418a042c030f51142003042c03102c10b00001005410000f500409902e81c03154000c1d9001c04101c5000c2600c1101c140d0800e8008000a00142c503040e42c81a4102c1d000300c0f001070500d0442f0401d4400c039030b820345680c0d490354000318080144902e0300700001e81c8811325035000c2e40c0042e10541e0180043c0581030549060000400788403900e2842042280b1f0701a140800325400040550406500c1f0f52001c0c590158100342030543d8405420030440355440540c0c416219 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 502547985 1250 502546735 502546739
    0xa090e0a051b130b03011509090207030503060d0606052e020f100e15040309050a1202061801020307021009081e0d05280210050708061302090112021b160f 68
    0x648290710501c20008291450f03035020905070001405035000c1d0103032003007400481d80c111401402280e0254444007919004100550010b41c0c8602038942110090341d046035420301c5031800401401e07150704070785d80002c840714031001080c01c02002498002001c00702d03010704201c032020032070b19492004c1006413144e100d00140ba8560009a2190303075095610000d4441e041c052500c002c030011425501500020034051080c050342c644900d0fa2002454a0803d0441c8030866a0100c1c80f1340c058603070b80d1640c516800c424a0310b164028030494500c20740c007e11500c11a8946000a03103180d00c45c0c003034001036104113540e103900186140240f260f0713400380c0d00041501c4031103040111030562150150003a140040f4001d001d050400c10b90b600002070b005d030040c003007074401e0707400d071204407680180044d081007802d509004030303515806040e2144051a01c40540d0310710f04000145c507403000b44040421078901c0080c100c600b00e06624202000c03c2500300076215489024000c0d9498440c40380624926080c0039101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 502549235 1250 502547985 502548031
    0x7060c2c030a0209071b110a15020a03050a120903090f1a18010201110a0f030507030203040f0f0201020c21060c07150507090e0109050a060504060f05041a04020a090e0a05 75
    0x4034070741c00a8181b520411000c2c94180b803041c1c0425084089414601542035840d01c0c0c07030702d2aa10805442c00d00510b002c2180300032002981c1d510748050103002e0081c00588010033342d100d0600000c408202c0b0a05004201c0f25140c0103000c2e08251017102300c10344441101298500000f00704c3c0715001d400240301c41c100012864038000c3d207e5504902410740d941d80b211829025034450142019049907282e40e4a11001900d003d419503000070f004500301481001084001130002142102c45030301300082d03070980082480140d20301242d628500b94043c91f1070000740241c2c0c1d50403c0503505c0504e0301041e01d0b419250715007141654015100010300f840c520300c100e6402141c855014640c000040e18020710701c50303920b1a880b41510002c0e0444600203841c0c9041003260402401580018041500e0401015160955660f458140b03401b4092089854280d40302e01401602c0f203010001d0b400510865898100d58030261007020503100c0c01e07202e440c001d00050310b981d8181c41164400c60710540300341026200464 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 502550485 1250 502549235 502549249
    0x240b03060604050a18050106030606171902030a06080c0a03031b0f02061303020108090616030b030a0203030c0607080703090b01090c0203160606050315010b0a1407060c2c030a02 78
    0x40641e8205405100000ea66951050180000c1035500304842510009400311416035605030040c40030306040c060308000c6240e210024070841003498480d0a86500c81d80e002400717810114480ea900c160003c41408010107d59110000b00c0740322200f128007446111050050754141840080d01103407815243c95030381e10122825481c220320442c1515030502e082d40c001009070300050024464a450300109104551300484043c1d00590300c04020721251401d0310420041c0c040c01d0043c10105a00c0300f0b03007030000e40c404000d010912135004043c5d075143c920440c140c0d071303440404581000018500da80071a00030b501a00c00c1411150700300440f104039070308103680000600084001c2d803045110420405181005449203045130034400d141c00b1500a24000400d0721f0041001004551b02c401d00f4010003400304900111100d0441c0fa040480000103a03410352503941c00303103447c041d20103804c044220b074030180d00c8800c0101c948000c00b08145940d44d0200320303080c3c6040450780aa01988040c140c0c10240c58000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 502551735 1250 502550485 502550491
    0x50604050d030c1a0a0e031c0209120303160f0f02121321060e030a0203030417040506030c0a091706070c06020c0118050d05090a0308030901021b0d0201240b03 70
    0x100300b0b8110030525546040b40c2680c8103400704001c4d207101c014409041c000b40907001e00100782c2d1009504100d0400034594801040529009826074000717400c00980d00d0300480c2081c4000701e40256074583ca041c041c8010516100401c3c1e00014103280003540445018410084012030284d00520010248015010f4990f001f4010620000c2555034005516040000c203840131440c40c000711102e4112525110051b1800816003502c2a00280595001d595001041c0da03446a00105140c50800600d501c0c85440e1003560000d039004000001044048405a030040c000e0090300d03940e400312965500445512440002941e8490341c011b0030100350300c10711408503e00c02c0d9008002c01071404644c00011400c64450f0f84030449080a5003840c2020310005105100c4410428144540703013000c1200060511941740c040180148000320100d07103e08400d60586c1c400e40b0210102c04101840020116980c00400e81308000540c20f24502e040300c80d6030400c0d110703524040125201012414000002d03040d070802 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 502552985 1250 502551735 502551737
    0x40f0503040b0d0f06050109060c1106070821070c1a0907081009110d050a08070501180b091c050f07021c03050702150f0d0203071106010b130906050604050d03 70
    0x5200c0030401c668030078003c0c00080040f480015144242400c8603051301c50b10ba000e80d040c010f488000304200307500080b407441210340c4858a10a4504a03000280044c003441d14040c002000100c1c040341840d070b22000e80ca240302c4240d600410540e9130000304658030400c0d000000d2912400180001a400d0345082c0e51b0340202c0703408251031440340ca0340b060a00c3c016146c1c14281c01d90b0346070010b00040c000002c0110210040c00e540c000b000740c0158070f0300c582d91805000000d040361000587c010a100007944405102240d142d0044801d1031242401000741000b66282e02850103a59180e0300150448400c6110081064407424140300501c0c030b00000541205109a810900c1d400301243c0303042c002d440180c100d41c4281c8903540c40d07442900502c505d0802c1190b0150f0031003010460000c00010000540e8210700080b103000d6500d0382c41020446041c20304604880e060b00c200000424501d803000003074603a82100314a5410a180e83d150340e1003d594441c0b28131744d0802c104000034442800e103c07034004005800f03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 502554235 1250 502552985 502552987
    0xd09030c02090702061008012906130906170c0d200d05060106110304030b041e08030703050406050c04030f12020a140f010f1406010315050a03030201020910030501080303040f0503 79
    0x200741c010802166045a80800680185c010046920b10560006001d006010002c010070119505469180441e07640c00341402c54220841e0344441d03894504a03000706170342c0c014109074181c0d20088200a0122401400c0001154950344444d0700030010701000703448002461082c0c0c030451138440c40500c29900d01400c42c04c003900f901410964403400d00c884202d6114500a0115600d00140202551070200e45030300c0c250020030040000c102130303006c8250442c0d00101d055503680a0f03c1c2d030748110350000e807070010552803000c020440d0083c0c05900051080d0b000306030522084ea43d87c03160403203511940c0001014190038240710008981454815078010b551030048640403d00340d225175400c05002c400ca150682d10179820a502100c1c03c1c041d41c4003100c80000140800c10841c00c05034413850005022504155a9050908941070805800310042001a0030246030a40701c3c14001d0107075100d022500c6c021913070903804c10700e403c1c86889200d04880c901c2d4040d50450b1150b41c0c80755150b011455007600c01d444 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 502555485 1250 502554235 502554257
    0x121501030e010c080105040b060c0319020c0a06050702032e110f04080610121509060b0a0b120108060106080402150c120c1e060105150408060430050d0903 68
    0x1400f481007403092101925110309940c0f40030200820fa4083c00c0c50036009503010301643c640b4040000a4038030b4003081020b147da81c0b84c00b00c8400c078584450340f8030503540180164400640c080d0000d00400504d40240c00355001041180605220f01d11120ba1112485004080340300e0892065880814102d0042a43c6481c14079004412145070304603811070002a080501849850303200c02d10700c40c0050407403083c4e80c000c160030340d164219030680c220405840b031502c56883c4070801501d91304c41030303070204024880c80103d91500c1035004150021144818a500c00d50000b06949200180b070f01d040301c2c080e0341d50342000e079540ea081c800f200b0b160903046001e9900c144004000c80a041c0907081142d030381e03140407540ba6810000586e142c07039a0410744075a904000c40110100243c00700e50305065450581e00300d80c580106d422410a20320071507101d54a10300aa01c2480100128030014203180381c140155091203440c0400c0442480701109020008a20704016840c040d07421500074007d00b9001e4146080c900f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 502556735 1250 502555485 502555511
    0x1008031e1201080114130b0726010b0408010b010908120a09030f03050306130e07170f030c01020304260a03110c0f0d0306080c060403080304060612030e1512150103 72
    0x81c03401e0304080640d94507039000101001000040e640c2c0204c801d100d000a24525032500c10711248058400000c210520003680d031510010060f80d040001c4000b410300896071740d201050425009402949030650905201103030f44d40c41024540203840074403014050f091804004041d041d44205034030310038081910700000200b03c2694403d85800d000e0749031f1170742c0c1c0c0c40c000f81048040600401d0703419a103498900701d0700c2c42c003a00080704400d9440800da111102110f140d10246080111002100729110000740300013000010f402440c0103520510b40e901500448080d03206418034202c900b0412540c0a000f88100c10b8401d0300310003c440142ea405a10701061154014104042c00c092030245522004581c80110340c54499030000b09090b01c003400049007010005886031169101c05000c01c1004070100d011702003154031070002066603d103124040800c83c64060618601407800038468020849058070800d50101100c94803030605100036a1035071250300e008800d03090107503100e040503542e00e41111b401c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 502557985 1250 502556735 502556767
    0x705400603090b06121506010219111305042411070f020a0b0c0c010c05010b0306100602010606022b0c121d0402070b06060c1908121008031e 62
    0x1030511039501144000a40c1414102901e010380414001e8192002c00044a540441c659052031098862201c0700e4850600403880c01e0150051400258624458442008602c541245ca21401941e02420b9000c42c81c0ca0142280c40071207000d028028004801d055046c0e01039500104010101d000080840c1c0c3c0c0210300325507403c1418103d074582419071000d82940703418442e24005000200844c0d1509500008075900c030b01c01025450705100c00203100343e08006080d04070b80c1500740e0145c200c44041c50110040b82c0d15410611498000d07510740600030810901c049980e05000302079140f03181031a000e100000744d85070f15079413a0000300030980a5201c00580115044401c250540d41c68140f85003926100b00c0f0340100010300c1a100728410081103000a00c281009540f00a041b24210b440d103400b4000c041c10807040701c00001c0040030304034408003005403000141405d050071035510360050b83c0340e200d0301d49050540c1c084c042c240c1e402032104540d95115240034a1880c0042a4668104044100000c0704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 502559235 1250 502557985 502557989
    0x20712020901060809100615030b030a0503090d06020d021602100203070c0b03040614180706030614040506030a050601090207060e0a030e062109030a0e0109061e030b1201050906070540 81
    0x31550f61034041e2300c0c1a07140c082d420164000300c0141c52404040d0342d4803079030b0744a03101e4914041c0105444007001c2c00b00660540380502400002595900e2038a03540c180404100e04007244150346070024909110304c0041541d4400783c2c4480400b41181c2058480226500000c104032407298844440704480c464940f2035900440d0b00341e01303840341c0c500d20245407414002a03410500425240480801008400e0740072081450815600007846480303002c0401e040600d81c00010b801c0f445100000190015594020003415006400400c007141070810070390303210070345000c000e8002890505809a03614141c03005200c4e4520907405081e44080084001c52000c00460b10b002003a0000300300e03100d02d180c00c0320f003102c0c2d090006d203401c0c018a4284203015068107032200f880f103081102c80605441442c02030384942030420b002003051590003661100305000c0c0c102142d010340a405420301186d00c03e40a174094401d038400c000030320003001490000003109884c0001c02c59440c940c0741c285000341158071400c0200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 502560485 1250 502559235 502559249
    0x6090218010f33080709120b01050907051204110f0907081906090c022b1e02150c130503010c0e04051b0a02071505070c0302120109080301150207120209010608091006 73
    0x1456152100e0003801350781003a4071602d440c0007c05070140018040c0300f403990558000710b0752200e59032203901c2e00f204c0342d015031010300914840325801d0009000000c005a40020801c599440300c010050040c41744200050301d010f03000c2002c442c0440c460b241500c1d00c401e4100201c8100180d0300303030780d5003030603080c1c44000c0e000311b0240c0c000c0024101c40c0030300d243c1c401d0290400c070003884030204459400200424000d07440c030b0000c42d00740d64025142a2080c09454108019403a800166040c100081c10050f400301c501408136202c18400021103060600682204148507140e004900d90f026042c04040e0200500442c08445401d10700d20904680d200039045031a0b007035000b86449802c044d41070f0a02440003518000303019081c0042d00004d8000b440d407109480d81540c4e003d40240951030001c2c0500789601004003007520110000c1841080f4016403403400040da821102d01580c0c4c1e40c1d00612086131400060b400040940041c0f2503d0300800040340c010740b1120444d100c620b02d00d05a202110f615402440e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 502561735 1250 502560485 502560497
    0x7090623010e0301020d020d0e0f060106050d110d020a0e12031605010b060a0201050603151302280b0c0709060b040e04021210050615032a0c070306090218010f33 71
    0x8110442e03235104401c00c0300303242d900a1603500c8003520700c035940300130512075101004000a400050600a6040710520b000405200c54403041444a400d010707420034080d120014600200d0200310f480c000171180e0303040301d03d00c01071031820718680c040a004000103a416034081d9280c041644460f1035060007095088d07103a0303000258906040b01054140310041d24641001280c5005000c94001c0351020603800e075504498040c000403601e20700c82840240c0c035107040d10f902d1184070005880c0c48040010540085240192110300c1d84074418841224000d010341811700031706002c2402805d280a0220340c101d40002c10025024488901051600c0c0f000d29040819540340e4060140f01e0500382c0004283c940c060305070500314070f08003031244141c40e984088051a030f48003018442c070900f01c10046403c04503050b41607441494903424060003805052400300d0150b40d00c5407040e21881700c0003c1c0c507816a08049a202c00c0540303000c2d0001300c0812552036245490082d4900d62151f60f00e003500c50311403061540c80b98 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 502562985 1250 502561735 502561747
    0xe090c030601090b03040b01180b03060736050f010306030803150a060f05090118050d03020a0c0603060302180714030f0403090509070c030c1104110c07090623010e0301020d02 77
    0x107100795225030009134140700078010b000004060081c51815100c20b4104080349140c41c145c054080d1400102c0c3c00c0d0540900c0042c0302c040c640c4840c0a000c41d410444002d510440070107960040c0040e03020004584682d002c1c1c09101e6460624000149110140340201d20b41d0b480352036540c043d40c019110a0110a04646402168180151090000d00c450b0500c00c45641c28240c000c0c0151003200c0b0729034108281403000040010702442c600000d00400341010101d8640b514000e0354440e5114002c2e2208a50600300151082c0f181c082c500550354041d01c0e4461011140900e1450900050100c105009960380901070306481c4070b018502c103101003030360400036041604002d0b0101d41280c0016010f82150020807160b1b681000800d92b00650610782490a01ca890600d0742d44440714280c00786d4018241074400444101e6000600700c0ea503c0c00c401d50305d51540d20b20420044866601c9141c80f5000b1003c03c0c0700c5044415044085c848106061203440c4d007550900003402c9034840000036481c29408504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 502564235 1250 502562985 502562987
    0x70807030e24042f040b0409030e090c190f030b19120f020d050c030d0e0112110d15060f1809020c0a0f0609210e01030c0e090c030601 59
    0x8420701d07844941c010780840c284050508041421440403490420342c0d07140850200a01c0084441044e1665404500c3d494010120741c950200002c00c0f4520031814130645003a113207050700c503003108035905031545c1d06450b072501c090007000c0000800c031404211003407040031001034544400c1c0b2a04005940c5001c1605224000a41101d0101080034003805040480e44d648a0212000c4002d544803101c243c480e40743c8602c2d040c0d0007079007206402504141007012843c108000050003102105046058600c50101d0318001ca40820075007103a6400544d01d654481c41b001840e07403001401c140c400b1490b80c90030350100e501400f600d10001d40c0d03110380c000d03213081044400d0f40f00100301c1c82a101c2d0321740181000c56842401a1001c0c9900441803801e50006219410a0040001d401e101b980a020301c40c5200d443d040650061038400d9084d1050382d0390b8947e0070280410300c0340b01000c629854440c64044048440110000c041d40340d4807006001909040860039603542021030301c26550090b50590b02d02c1c040d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 502565485 1250 502564235 502564241
    0x201608121f080c03070303110309041104030b01080a0803071817100e031e13050a0f0e0a0203040201050711030c03030d1a0f0a09020a031b20030301062102070b07080703 74
    0x1021024542043e010000d03142d4001c6181d2084035054588032a240003011602411441141d140a900500e088114400080080702410849000d040068110303a640c40d10941c0341e90a060300240812010070000d000b040c0507401e03440a4601080411900c9611034600e040810340c80050320009500107101006030b40c500340500901c500c1000d0185040040700805c000c0f80240b250b91074540c1050100b88d0841c68040c064280f4000d060050013001c0304c2c3d0f50344402c030045102a0050000510700000000c26107015802120f001e9a411303902c0c1031400880351654020b9922800d1495410b00901030301000b03d540400c00b50103c0001500c0c0052020506450102c034501c40801d110301401101c10455a1035132041d43c0102103445040d4056984c1804450441c0113084640e00780c543c100d0703082a8100543d5102141c150403c0d20910442092000701120964074002481108d000410304400348880c1d240f013038020800d03400c40d12009424400300d40d50709174980004413084030019024400700b0060070b40c140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 502566735 1250 502565485 502565489
    0x50a020907030c09050112141905010605490b030c030d050f13180b0102101109010c05010b1f02070e011d19091104201608121f 56
    0x20800f004200c50000e4003a003150824801c650511040841524803980703141c10003001d100302d45480380d60303d1908001c640a040207504200c072400746007400200d03005005008a51304a10a49c125004c40e02440800c001c010300c6801c05040705254203070088007421040170b510f890503520018045030a42030002451300e00030b5a54416842030b400b04001a400c0c0d41c00204581501c5082046150b0b01c4404440d503154011a13540030b1040c2c101078440600306514503910801294409038203031107030b06140000250030754042c41030400000c1d1081282115560041416a011314490310012451411650000b0b4020800c2c550120701842d9000189010fa035040c059030380a414151108030b09541002040c0c09035458480e902e891410407403020540f0713030410314111200070b106000144905001442c2c840d204211641a090150381040e003160089100a840c0c28203529000a07603606203100d003d21401c60000d95074040d16604001c10014003211120030020313201d8644811076004c20590040340b06203a045903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 502567985 1250 502566735 502566737
    0x5120c181b070b04060903140406080703050c090f0405090a060911040b190e1503010504060e010c05070f06022b0608061006230c0f1f0506090714070b04050a020907 72
    0x41245400060180f14840e07086501321a0008440302d0701d03c0d058801049040b02181035050104000030115400150305118408640d4203010725118420700311018041d440c1ca1b41d500444003240c0d0380082c2841ea10142d030282130182221400b4101c2e0b119002124042c4000381c03031030300502c040e1084909090045084020040d101c0041d9405050000c182c940098020f04a00c0c0181c54045060400d02d20414140034500400030000c82c10185450b4000700414104601c0b00c0d400c110784a100b007400b6006880c00507401c04d9042c043c1e0380c103a540c1c0714029031016440c030601408100c0043d40c41c0340c95845484051a000c0310000e241800e00041c03d02c5c04400034600000186c44a50900c001548100406514845204104030506203000401058010000c3c400850b2080e02440070f0f42010004042101c40d400c00b200d602018003e104c0e10096590840b44190801400d60114540910031841c24080c072000402c814140b08641d030b5070342d441d000c00b41c031b0940d455071005241c60301350300d440c040c56a003003042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 502569235 1250 502567985 502567987
    0x13170d1109040e1f090c0e0f04060606050c1e01090524220204050a090506160e03030a0203031605070b0112140a020a06030e0a1703041b0f05120c181b 66
    0x8a64204620046134070f0b14010360381c0c13601d02c80c10410108000d040702038820307204d9440840c9009540b080b18407404541c16104c450804000103141030185c412140d00c001d201014002040d140328000141c13802281841c00a0341da10043e9402082043c0418034000ca0011946404441c00310500c3d042a10041c0032004040403401040d04540f907080f0200c074089a06403000718440d07842018210007041c1c9240c024040740507840400c00d0701c000290b03042c0700301e1490340c60700010443d1840a040d5070303019203d00b210140c1d00420204210340c00c40c40c0104110a400e10b811071801c513076076840d107000000030303401070218449407185c4070101702c424451460703440f5205005041500040c0c0024552810030b22402c41450394030b009855014105004203500950408a105980084007400105651040341c055880101c4205158a510140c8200d801100c40100c2d4070700f0703010705040811010800e03640803044503210310f400c100301e00c1d150000495007542ca1961600c0d210315110342142c80c0d040f02c0b0341c0300e00c171800d43c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 502570485 1250 502569235 502569253
    0x1203040606030b011410080702010906090b1608150108090708120a0f020c0d0818300a0f1509050105090606040608070503210405030a0f030f0813170d1109040e 70
    0x1e03190380540007070800380f07004881502e440c5230503401409070760030282080c2c0c01c3c1003400052003201c03078120f4060314032180a0131044021000844010000b0b5810718580c0e218280c1d080e040c0e40c440c00c50240c0107141c820540c0d00303490343d60510700d24108801c250540c0c0041e021402143e1239800c180c1c4040a1b28503800a0f04444400340005181c140389c101005050710004500c3d100311a510310410701c8003030300113403500040120b112240800c0e8002c034007403c0106a0840584100705402040144040398864a85c0005840d5941da44664400c0c0f1003010b85002c0da00c502c103001040003401030b40e0152944001901d1203040c40028002614000d0700120b0241c1d0140380700300180d440010300c2191505c2c0950040100280c0c00d15100080d20459002c0c56051203480745c0103090150b2510444400d42c03207502c80e513003a40703500e032000d46031000110f50402d02c0783e44c0d85850360089921001c0481c040c2c080010054503140e501c0c16107408031034090098041005010841c010142440d1240e9001c00b5503103402450011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 502571735 1250 502570485 502570489
    0x1e080f0c03060612070225080705010912030f030b061b07080706120b0607021512060d0804090228020d11011109061c0507030509100903050f0c1203040606030b0114 72
    0x1105001c081013200041a00180704548244030407140740c81c1054000321540b400d11010f0f1041c18642c00b45034128007030041c0000c2c1643c0501c0451084800080b040c280799041c1e901e055900b100240080402e0645404001125999000061444425a13805203248035100c008580c50200c031038100c02c0e200d40c403c000034044217400120300840100c201e20080754200013000805c0c0d40d4000d415000390040905142008129480e00c080c04808860010713418860f942c41c0100410718403c603030042e0100104004c02d01c0300942507001440f50183d000c9481ea0003090307080d10100030382c0c182c0310000d0051300070800d1812415400861003c01c2c02c44a0001c1c46400d258000300b02a83c445d03116043d100350341c0041d04510000840900a000e030f00c684508005616000d0400740142c40101d0324640380d4040c00b003003152048000d225201c0d115416589a80c00c1c4104c101800080b9807110800c139086100f03107040c2540c844201c0e4000c5100c3c40c0f0070744c00850800e26518010b4620340041c0c000c04104c40180030007107115 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 502572985 1250 502571735 502571737
    0x18030503062b0503091009030837021e06150904020a030501020a090f0e0906150307080609010c0f23031b0a030c14070f020f011e080f0c030606 63
    0x200078210750300c000a1200c031982e03180c0c260000c9401c0c0055820001040e0502001001a0a100d5000c1c0e40c0d1500903003030920304035180b521074007008045c85d4051005000704a00110207082c2c1d01d002d030040094461500c3d001000002040100364016131241cbd12846d01621604208100c1c2030380440104441d081580700420940c0741c140300c0c6401203505070005001d6585280c1640025074001000319911410f4101c001c05000e62401021150f554031381d400560800c0c041013043c45080c2d03001c0500100d81b0303408186110342c0a00c0d07107404e505124543c00800c01a0b4180301e0640201c0710b0b800000f80f50409030001800302c43c0740b440300c0c4003403003a00075001e0407240b035100c0e000c0f26980305843c0c5182e803a690140c8030780c00c00034a03074250384860b0008107083d40ea4503015800a0050010f07a202c4007194041c854081115100359040180079050042c621001410030551900010784141040701d81c20301040c9900d401c0c00c01220142001403021003d200c4050100e0f0a030030342003c0905100f528510740741c0085100c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 502574235 1250 502572985 502572991
    0x71e21140411012c361006020c040e0102040503030c0304050a1221020a0c06170a02090f06070c151709070311190f0b040f080f0d050a0903080310080118030503 70
    0xb506500450307a498507a269800a40f00c09280040c0c2c0e40d8100507180d040b2104a61843d01c2c40c10581585c01090740b2105a440200456070268002c21040105d501400040c1c42c5d800320070b42c3c031503400f8440801c0b65074003400a0104110524015502d9030b2a00c020000c2c0703000386500155103c0082419880852441820107200840d100c8a98409410700e403c01c81c038207244054054014a0b8504000c20695404101002e0200011004002c0d0780c47d1407407070000f24401c020703056074012610800d558050a00d1805000098001e000c54807060342d0712400201e030383c0b1852540c2c00024482d1010b254a058400d10119041200c080080a4aa08555908091008c92040c0c02d216203e8243c4a0450102482d00c51028141e03112407040c0055903240990700b44d40050050458041040d42d001c1502003000030041a601c418600810b5080703000302c41696035502c004e50103c1040a452400b0000c1082200110b00990b110740e2050b031010310348003a1901712643c003000c0d030030801202d80003440469030110540750 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 502575485 1250 502574235 502574297
    0x2060112120c110303030403050304050c0f03071a0c032d0403050d140912010c022109061e070f0c2c09030d0509070905071e2114041101 60
    0xd03082d21142010001c0d2024440784583c1480000100400c15038000b0145001d2885281100c0242440c002004003a89110b0103c0e50594081c1100304640c0000a1034100c40e82e406c080043c3c0303003820b0718100741d00310f505c208002d4540c1202450070004103d03402e1034060b000c2110142c00d13410a82180d59050303c072801080c0440402850804400340000a80211381c104000104900e405407465a01070340a80018200c88003d4066844040d1001c00201d10304264100c03581030317641c60100c84404000082e00700c000038108084450717000d1356102c104440103200550061801c00605403003031030403410038205038104000d0030403059400044010301810803a8529648900b4180650340c803a262461809141440800541080b051042c88100401c020040c0e480c2d140d014000f59807580002da51682890400710700307000300c40d54861b0025114084d1040c444410010000c00303c81c4030a14201514141c80c0c14081e8030003660b05110810022824011980500303003803000e01340c58449240d90174140d040314140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 502576735 1250 502575485 502575497
    0x90709050a1d0a1704050f040903260a0c050f071502090402040f03050c0405061309020a0b0d0c200703020111011d07030c090227011e0f0206011212 65
    0xc02040d90707070b0412814540c05040da00784040104101076541c03580c404056800c0004080c0303d075000f00080d01200d00342d40c00035103003111411807042800004c04a440c0c0c140c0400c20b0a26a491080c1c40300c160711402d803c0c101c42000143d0400d20880412604003004250034404108a008071421940083e24126900a0941070400408941a0001c0e01c81d003207080b40e0041c400540032a848207010403040c15240640e0854442038510303814030045450940d1819805032101c018400b081c000341e00210301641c40030f404c00300344690b180541404c540004500c000c82c00d0301c40038144401c03644001040360003140110b05d0b0380e100c075110b035006889402d00e0201a04104855080001100380ad400c030b05410004d1000c0c65444104c9003401c03a4458003540400c9903001e0021400050180030341c000d581d600d0860200816194901c28805003200d160307600c6440c1840100c000440078043da1a02a20b0407e0058640c40321010441100030b0405005811102695248440000106e0011920f444031011541085 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 502577985 1250 502576735 502576741
    0x60609050105130905090d0207050307060806090c160f03320c15100f0b0304021f0e04050a0b01030c090803030c03071803060b040b0103020705151b0d09170309070905 73
    0x990030003002600800e41e04c50400c03060096000c000521000d400e04558241c03490243c5802c100340d1103500d40e101e004001000c0da000b14000d40303080740d00d9941005158407214a0301ca410f070700403508031800160a4482200002e808003e041d004003260f0a4160840e11030544d0400e0319516a00d80d41c2001d101405c00503011990801e000c1c004c002c00e205c4042c902000500e5494400354a41c00c0304250b015070740e00e000315000b000035001c0d03122050328000d6500401c125241c51004040315517a107450605c2d0303820131041403c0f80b48940c5a5104481c028410b112f00401d1209881c40003506444406031968104009000d00300f0030164084141c4c2c1d04140d00c0007200d9540e0b01c07100402c41d801c81c3d4a4110081c4c69413480800000c103c07250b40412541704040c1c238148040101d01c40103404900602138040d146401c04200c50500c0c20501200300c0e440010714041c2c594107490034210215071303000100e801a2190340c07003040d00c060240c110102142400001d602503d546052502079171102242e106d107007031480e115008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 502579235 1250 502577985 502578007
    0x4080a0504050a0e0a0e0d020304030f060b090403170c09061204060618020d0621020d06020d0603050f25090c1b15061e0e0402060403050a030c050c0103060609050105 73
    0x11680102001495442210381340c0110640244080d500410114030b424400064240d0101c1c0301078010242c0d4014500346440c40d1540001080c2c9030404a607841d03507030010b0790742c01e568007a44a0700030760181d543c8801198401000e80c0234640080c0c103494030f041040c403560f240d03580c0308000ca50081d1a407601640340b50f116071a0400150002d5040b07460042940780080142408503030141032100d092400031310503580c5d95482c000c580103040117aa80002481c90f125400350501e50b41442039103218240041c034100c03507041803000b160700301e80044072640c103d1250307094140420007a400b82e0829589a080c2144d12290303000100d0040c83c4a201c4045482e0b00c6010307005030203069644982942150a104800c000307150044215504000d5405402c0c902701d40420b0b01d600c0c8000545c407a805040d0038121750350034080180b010210003001241d00100800c001701c0001c03000c0c4444c00c0c0452003611891404c00551420364204414511468101403408004211280d1300c09400c10071501e081c28020381d01c02504031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 502580485 1250 502579235 502579237
    0x1615050405010e120d09110307030f031e0e090415020c030a12050f0402090405011103040b0402011808070603020d09080f031e0c03130609050f0c0111060f0106030c0519030603150c020604080a05 85
    0x122081d80f6000740907002051210210f6000c0b0380910036561200c1d80a045801048200f1444e4517040020300100c84442e20fd080c900c102d03c0e0040d0042c00804d001c0120005408241d0f403124224282d26080401c6595403103401890005400700000d109001d40d181020701400004c500510281c481e101e0768000c1400e009080d80003052000708103040c0c540d245001d0501303003151f034420341e4220b0008642c80c0c840d010b2b90a102000c001034403407820151120350303d480e40c03c401030b42000060b8030445075202c11807000035201c50014a11710860701c91786504ea142000740700102078a4070f405031700034100200c03c01401140c0c0b03800300c07980a80d0303200310b5102040060821500401c0301c40d0700188144608904090240c034002000281214241e07100c084112800410646541c0306039002c410754114040144141c1d4003c4e008107105050b2460307d1030a00c6d402e100c10703005c0e001c403520b02c1c030020a130303107110910602c11104000d503104c1000c10400d0196001c28840295255401000500740304404117031081881e2044e8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 502581735 1250 502580485 502580513
    0xf0d1805120909160f030e1504050703110d2406090218030c04090506060411070b1008070b040605030f060f03030703080a1406151615050405010e120d09 67
    0x2004894100702095800401c9a001030b1003203115510003c0000c1c0c11801c0b424801d0104041a42c960703400c101d100405a015000c01074081c420790207080010340d40e0f0020300652038861030080b4000d00d4000e155040054a200515815038054050604c608002c18441071030308610544610390404085c0c403210441c0010455074004c046c0090000411048601d28620940a1490101c0607124903950410800040316040000140a80c119000140003460f0940c000d41550303d010400c80d141450355a21070510401c1102d0b516501d5104540501400504000400240c51208102c51510f0b0902d4005016800014020a802c0c5002e000080701134903010042804203001804603074407004039140180c11100c08907110a402c0303141c0384940210845520341203020350340c082c01c85403031007130142c042c003110340d2290043c10b00c80569000d40e400019455070f01d4000003100000c0005503070602e8030780309003520400040601d03254011040c01c00901e03000421034604010242c03000070407200c4c61404810490b020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 502582985 1250 502581735 502581743
    0x5100603030f02010b1c06020f0708070b0106021203060a2603041d0a091e03021609141e060609010e030a0c0501080a02030106050f070609050a05210f0d18 68
    0x106100008054204015001007801c640080c480b02c04080c0c00c0c000e03000706200d28070b04015480305940c40070039910360040c0a45040040e00d14501500c0741c543c161164050081142c18001640042240b43d5050003803a42c05414030808615500740100010344000c041e001d0140d03903101403c11f44075445141090565107004000c10740740c40790303900c1540481e0751401009107001100d40038000f40326195030703105441d1a00d034807890807505034259401c005440401038a0440952240d440b20302d0385603105400d2140140601c0c080481c910910991182c602ca0000d4070002641d03021081446080c100721071207950010042d1042516000000c0c0100d50f0152145100e44e054001c020b080390612030214005410b995003038882c030b07a90351034084810040348002d10900002030300500000125001c08001440c456005039004108a07090b91161400e10f0f080e020121031070b910000308850400b01006d0f91803000880355400d54185500324011042600c10440c0e04407103a543c821084030f260f102c0c04c3c0c00040740e13608 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 502584235 1250 502582985 502582991
    0x15040e060702030307020705010905031009170705010f0b060901020607260f0f011211040207080702130507030b0406060c02060f1201090c0207173f09040b030111160510 74
    0x70060183d220303031041da00d0100500845801280b99402400e6020403960060000c014039154240035070020b10304810b04450300d1511105009030205c1440190550034081c00000800c0d00751100e44104680c00c0c00185030041d10140030118403a80c01041090b80a0020b080080103141c0c1600c2e441c030350003039000035144400300301c500744407038165180540d40c42840c040c50210196600c2d1902580c060507054001444900c4552000000742055001703042c04d00d04c502002400d000580e4000f4005000318031000d1502070740c03402001003071136060042c12800b11058130200200780c20000300a04040c02107402a02943e8000703040082040c401080b141d004206071074040c01035845498040140c600b05440030014400d042c0042440e6112600369120510070100618504506600983c5040c00c80b5429818810505d01c1642c200403107040c101d400094001c000d190365880300b40401044074032030324610340203a142003002001422048100c0e0b0161400c40440b1503001341915046140c5030b5545451101c00d41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 502585485 1250 502584235 502584241
    0x60a02060108060f0f3709051506061206060d1815290a0305010507021e01050705091327021f050d0c0e0a03080301080d050901020615040e06 62
    0x5408503845040c1d401400603038005846888800d90000000c0d0790003040b401419010840308041020401c6031503140b4080054a40c06518920034194030425040c1d40031501c4405810030801d0a2000504103408100d80c1942801c140300420807a001e903405412560034103c01103441a038601064a840900e141800e000180c807403802003901520410007150041c100640a980803582400380e40d00c108581240d5603200d5000341480c069141004c840c0ca034010070022400300c0070900078020b4501c548159001406111a81811040c03141080c0340004c1e504d901d02018801125404012280150000c803901e45010701c0ea5039400e0010440d91040e038401510110741e0f03021100c05058241070701c0b4021150000380c00101110503c96617444c10804c800200200003544485d081c41d0301504410703031703186421064420b41e80041031000c5181d4201360740d440000300040017035450800042c401401c2510f0000d003407804840c0003035a20000174200c1c04030b00218042000054030307560b00c0701c5440302c0407008484e5541 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 502586735 1250 502585485 502585487
    0x612040501020918191d01050115090506091003050408120a1b030c1e03150e010f0b04080316021f030c02061014040c0e060f0d1b0e040911060a 63
    0x36101024032130084030070000d54608803139240c0d0030512030900d10583d0841103004c0b6480c240140501c0e0303016410403015010094800300244102030113088205100e80c5c406010000c0600400c0d01c079400365124400c01c200403482a1516180d0b02403424141c100412652154a00f8142d81c0c096254048848442841000380b14082c94116031003d1016801541d41e1000107030b4214291881100028040340c1d407000d001c000d040321200820884101c520300003034447e00c184179040c0c12400c00e0340301401050f1040c00511210341d8029204009042410113b464a03181101c4180c807406209281655100081099810f648501d00a03401021114000009119901d1f4028000f03190f084403040042c8034040000d400602c0d1809070300107a030450402528443d0204040002070040c202400e000c00a036250041c14a4903414090102c2003002e122043e20703030f03c400000e81c04490460b0303001c1d100e4140318884a0503c0d40c02c81010004020150b50208500010782495880000a0003049821560000f2415100e03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 502587985 1250 502586735 502586737
    0x12080903070519050a09020316080603010f0e06060907020a030801090903050702060c010c181a030a02041e033309020a050a0b1c050702031902010b1801080f010c120902061204050102 80
    0x6134404554000b0000d07100c81e0010100d0104903504004071441003400d0050501404200c2d030300510040c004071340c1c4100f04200030159022809200550791207801880028030786a4212540220344d031005000c81011a10010b000c004180708641100f070303849013a07109042c410407c441081e034002e0091641c92524595090080100041807400984a106020b040c102203040740001c03140494000b04d00d043c0740309030100d129840586040c2130a982040700203804007840e0040c6031011031405550481601e58189031701030030120f4000342c102039428015501a5009100c906405c0c00714190002050380c40782c40400d80748040394101e0341d40450400d0340000e101816400400c5d8041740074a091190440940121f8252601034a0103c0541c00901c8007514040d21050020180d21091001080001070350010640d40f803002c0b451807580604100060207051802c00841c0c541d58055030081200e00d03e072000c010040c0408407c86010f5580341c44504065545075010b84060040300160b2040e5800d040c60540e0003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 502589235 1250 502587985 502587989
    0x26010e0712110901020c04090209151f03090b0907031a090a050f0106140406050a0b250b0411030c010e040c02070b040b1308060f010306021e0a0806150412080903070519 74
    0x180701b42c000c0c0032050305082c019022469805049840740f61038404d0129143c8072107848194000107420000140304008041804a0403aa0b440001d040310302d504100380d0060005142004a074040c41d030400004072003051700450000001d00403111501e421103080d0804480c4403000d000313849100c1641d00440410f6202408485041984117034541c025010300040c1c274124070a141e0f201c080ba440400040d0040d01c028002940e0000f003840d1228105004e81080001d545010fa45551451080004116002401c5501008210028803488150000080808140e000001c0c00b91380c892903e02c01c168000c02c14100544186003516031565100d82c412105a000949041094800041c00040c80e050204407103020314021500c40c1071982c256188c410282d40101038510301000c1a44031451007008100c080c1c00c0840850b620340d003960030103404001a40c110f00410328080310082000b0040d06038010002c10f80280e000324281c0d11500054002424868903911664101d10480e5042c45111b41c22000300c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 502590485 1250 502589235 502589237
    0x60207080309012a0e040c020a0f060c090f0311040b060d0614190e011418070c200d021c08130312140f0705070515090126010e0712110901 61
    0x1c44506032130001501d04140308100e4013040c41201300d8403440c14076401c40381e50081a07004403076481c034441c0c0c0c444100701070090094070303526961791a4122640d40008480003c2400fa03a5030300199055444969160711a042c80e18071980d0790b101e15a8640d1a6132041e00d202e01d504980800ca5641d880403646000c5110111307885c0308815103680495114030082c902c00566090800130a216803c1c00c080704400400711820030750250101041c0101d03000f12648072441901540d03650074240c610b914100301c1c8256081e1802e2255001c108404007240c030741031540c03c10f03150112008504c03c40d15102140c0744651480c40034000a0300000c41000302ca00e000c0412080f28032a40d411442d80b04e10300011120b88500c1400d01031001030030805505010700c22000307000f0301c0b8061010340303085a0b914000905582c10001c8440e451340c8004c580c0c0703062581c01010400c4c0d002c030340e0303103030f4801d2406540004043c83c103050003140707480d207890300128010707912401140281c05e414440030000086104045040c54012051170341c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 502591735 1250 502590485 502590521
    0x50f15130e10210b0402091008031b0d030e0d05070c031709010207060306030c1517010602100e06040b060d03091208040f050315160327030320041206020708030901 72
    0x1100d4050800a00c20400e40c100043d80c01c130380c40b1070f03080260341000506907440002c4030000100c4c1d000014001008400c40c00400fa0304500c00c038074492800c10590803011400d0605d40504d0707250191010034285101140c52810039520001e924101850b29103941014003503415135450304000102c00c400034400c1000076000c03500040d44c0c403a811802d840c3c0b6400001e0220a90032010403400801c0010011284200e08214500001e00c400030905490f09910240c0140d0100c8242c0b05c0b40b194038401e0742842c113050300241202c5d207816110201000c00282c9040d003d014000c41c52420306200355000c0000e45103e1031480b10350030722418084400e170040e00406021030700c0704030300180c06c2c5000115144280140d001c03418803a46c0b2910004401d40084c54643e05040e2104240006807800b034058258111600d01c940c5c60701c80d15030400a08992480100c3e043c2620803d062201c49030a40c020b0301c0807101c0480d0a0903001c009488d000d000ba0184120051503158080700340002c4c498190404000384040c4140e407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 502592985 1250 502591735 502591769
    0x714120114030307030c08070f120206040b0901062301030605060703170736050316210201051605030405040e0c01030e030f070b13050d0f09050f15130e10 68
    0x10380300e03c100304c8020041541003012800185000c40900704040c001c20130b21000d0b010503251400722064030811080143c102604120801680d0105150410b00920007007040d1418509443d01c0002001340e8680041020b00c90005141c1c0300c0d8210101070031014050903101c0f040c6150242a0840360031f583c040d0702405c07900040102e40310f150300d80c00b07641060207000c0381482d1400d1880040220036402c000d03a003040308400320300b03510b04010081101f0f0503100b1400c400c40c503200900c2c8003401490094001c020303402d0401c0d00542c0e4008140c6e04840b6070041c80e5983d000ca5450403610b14421648481d40113414002c1903268040c01240308000c0c01e20a1304c041c89000500c00c0700d82d440341b2507c203100705054410700a80e008a00030b69403036584948440307850850703102c27103488040c90019800000400a034102c079a645807103501c6944030303000705015030311245652540c1002a02500c00d4441604440402090822580250304040001062040129441c030306040c040b94210905070300400030a42400404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 502594235 1250 502592985 502592989
    0x12070602130e1012150b2b110907051b03040e0a0912030b06271302071a07021c0302090a15030b15030c070302030c030406030606121a06030714120114 66
    0x503961200e9200b280207420141e000c5082c5d008106481d1199000003006030700d00c0400300c2c002c080318440703144241409200003642c54040420034142400d680580f6240040c040c03815044020b9504044100c801680440288501146940500d9001c1102c048698083c40000f0300c050303000c3c5c4169405040124001c9540f00020350075100d8800149800040c1000f0280b01c600890842d540b240e03101c0303a84140094040000550050072130b516040385540e0001c0d802c410401d9030054003008100d4040c8047e12441c2c280c01c040e4a90199010310301ea42402800d114880d144203504407042440e005058010030f54481440148040810390403101007450010084018a82504201c0081030542b10741450340e511074502c2c3d0720942100700c085081d0b20040c4148030702c1050900c0500050407070b990b400245546041070062801c001813410740e18051a00c03a50040c40740003420703000c02140c0e050750103654989904030f0445000c49041007010062001050303c01d8405521203030107040343d41d42020f00403c0084441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 502595485 1250 502594235 502594259
    0x6070f1109160f1d04060f2628150c11010905071e260106060509130515040f06090e0d23090406080d1206060212070602130e10 56
    0x2e0480114090340c1160350f60a1061030030300e13221004610401a00b440b558003240959005410104d2003119001c03041c08007451421a5040e96070104019031020741c1420446c5844003400281a03070010720300108181c40e001d604005000d51035201ca20700c0d22113205a00184024004149460009050090710780b100081c1405a02000c039000317005004110728010b043c000591004032620280e1100407000511228001030344804014100080d038143d0141014003400c584c41ca40011041c00810300c00606503884000c462150003c2044000540c0d441d03210b01005001c01c007101165005e0304202d401a0f40b441c25400c010102d07841e03c94280190b03100d0040d0603480e100315400c8100041c2c426100380103801c14805000c2a00c102c55251180b41c0440c10010074180c400d260400d203416032000d2540a042c66020340e44621340e0008070750803c0410305000f0000d464030109240c002c20148082102414400b41d80d04444904c00c440c083e02a0142da102c01e500241c81046607507000e82002c2c0c100005104002d44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 502596735 1250 502595485 502595521
    0x913030e220e0105010f050a0b3708090727090b0a060f05030303160f03020906131d01241707080906070c0c0504050405160e0105040b0301020403050709050606070f1109 74
    0x400c05040a4200159800ba80d04056a4003d2b4003041100801d85074500184020070261100c000a2060501c000042e024840242a4030283c1d8003020042000380e40c4506182020030884890400b0906032035411400f50103031107409004540d00c071090014064040d40f1680072640101103481010340e44030700309502c0e0702040324026080800309044668040c03040600510907a200d060040c00d2050a10118a407500400745c1340d0222605d2860138005a500c802c2030b20f4500407030b81d46025007581000e00051064242034112545061410020700545005201d048049031400031000303000d00e0542c074001c00d410760655400e0b80500420021038210746c49400c43e52103ca80000352010164600004c2c88014000188103031518010051200071207106030b2910001014030031420b198035410501000119075644108a01c268410041080040d2002c1141c0c01159100710001840340d544601290703041c4a42d100040540c03210348008030411a80f0190f40c14405000c2d80c2c44005a0f4401c180c0d28440c0d2421 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 502597985 1250 502596735 502596739
    0x605070206090402070519080a140a09061b080d02030f07050c030306091302100905030106090b030c09040611030108030c010c03050106021506041b02070302030c0913030e220e0105010f05 82
    0xb045804803505140c0c0040a4051248045a41500c0c9207861400f0032400c0440403120803000013240a002903111000c120820520540503107031240c00c250292020700b41d0704c6041c0c2803101210109605203000110140d41681100c1919603515888060f000290700445e0300c031030860280004500c9807480340302510542645040110310b0f64503501d082080c4000001d2000d0019091100c02c000142c407a0300d0300701040392803a10f4143c095814a000c043c05e44001e500015040740c07810f486540d1a9400003500355102509032013460300703a122414190050502202003213003103070000000042c1120000018110560408001c10040130701b03c030120241d580a01c43c4400581c401655103070000d24030021590003c8000f000011038401d034410208001020440c070b5809038100c41d8081095090a00c2147d8061004a0f40d901d02e038a080741d254556120007020290411164069250380e03921070740b841088046004004041040306c616000c1c0c098861441040304650074140000354510080c0c1280c0700f65540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 502599235 1250 502597985 502597987
    0x120f111317070f0e06031009050d020705120307060e010e160e010b03040209190e0601060f08090a0c21020a0306090204201602040b0d0305070c0b09010801050111010e1e070605070206 80
    0x15096413034140103000342890383c0c18055584020340321946445400280c9116038003500b18849400d2010f414130002d43e011600407580c0d00e1909442039008000c807081b00350720038030009085440342d45090040c600b0010030384191080e03c0140416094804621701181e480c0000c1e02c1141e07883d403002100701d010594000b90040a40400300d803040901c0300b0005078140169900041c40d03421513030807518004084c1e00c0ba0002c00d030008040d1614660100f00c840e40012190001c0801d040b1b40c0c0e0700c05158200c248140d1030b650002d50150300c829002c2030703440014250010001c40314aa100e082400040c00030103c00c80c841c40c5400c00030161034210300c0701d00d034800318403481041c1401c0d80080c41442000f0400000c030ba0082e03682291028998465441c1c1d800c5500070340e41c440e00d845103072500d001c0d6022035400001844e541400b000d076250781e0002d4464113564007031818041490120401d00e0141c5941c08000903a070044c003c0c2c1010304034154840a0380004103008554000780d903045d0550707a034800c0e65006504840 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 502600485 1250 502599235 502599239
    0xb01020d0503040305160605010f060c11040e03040b0310091b0807050a11030c0303062b11010903081c0621020909191a0a0b01120f111317070f 63
    0x4080c00c09164002e01170b05005242103030320554540320251249080700c2c82644c640050000c0510001680e001d0541401c254500d0340403925a41d0825401c0d94011b842161202c81c40311102e602481920010b0001341d48141d12800c1c0300700e0382c0303040001074012011064900004540c1c0440481c0d9111005281a05c40c0002c540b1100c104940d02e82c08511420207015030030038000140c40e01040240441300d9440d0146481e4102a002c0141400400b40d02c251596000300380c0c4100001c0d01c0144a501a610039841c00c156103c220060712501c030300e9400a000008003117400800b0500c020351840f48284207001c00c01040d81c4400e00e40e43c0d038140902c401070b4540d1541070010014100200b5440e0402611300c11907442e40103a145080c842c51078002d080b070301414085d0311030301c400c1c04001844d40c22100002d4144a0782c0501400202280b0561001c0000c80c0d03180e010710514070901d980804640b030a60101c4030796403c0040a5001c40c0c4075903215031681d0301c010031100174a07004c000c2160703004d5a12038030060a1941c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 502601735 1250 502600485 502600487
    0x5120a080a0f110c1f060305030324060403060c0801050a0f060e0f0603010f03060b09130f03121104060923011101020c0118140f25080609150a0b01020d 67
    0x3080d0740000030a59680c0c0c0910300c070000c803100f020b42252424032004084500c81c0901242c410300700c020b4419000e81c140002800000c0c03020055952080040129510114620030f00b00a940c0100b140c40ba08140d00041c01b1080c00740ea0b401c0000681c446423503e81c4d41c3e03641ea0051068422080c81200e09a00801000344030107407190034035208010004003050192802040090620383c020380c4090020030f070a00c42001005010b0050303010700e00702203420100500d03024040c140c0980b80b00704010500000e5504140c00c25008406900040f51006000c2101c07060103a14010f00d43d005000c4c3c940494803086c0c0008076004071584071003400101c074080b1700140728003c0040d10990188c44441056540034424080031070024443c2a084040720180750701c03015820b0a101c2d058a02c44a0300d161300e9082071941c80d5800c3c800113102d8000d44140c41100303060011902065510300f200341c10244ca20b01400007440203840c40000c3c1c56142c4610290300d821140c9504405108a81403103030001d000d60082640c4140f51 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 502602985 1250 502601735 502601741
    0x1030204180b01231e1f09060f0516050303011e120212030c2a0f01081801020702120609072306280c14010b13020708040b0703050705120a080a 63
    0x2440300300360305413100320805001410840d08042e620346600140c464000040c41c0000b4104001d000c015100840304d1301b04440281403407a01c0c016101801510310810528510540840f030943d0070703a552050194107280b07485a01ca40c030078401d4443d0190380d6a2404001403040001408650384510842030500a0ba400c2c026140c07050700031100140001d01ca0045400810b120507910102e1301e000b002440c4050040d001121078440e00c4440c01a00144100c0c4803d980004240d500152007021060f403250000040c18068030070000002e40200c0c0c550900c0340143c00010700d0070300135800303d400d9402564507070b81000300701d01546403500c4c1e04980c50a030701280d5042000080c100c01000b4000b0480e2016440440410715015002d01c40000360041202d00605c44441c1c036007041f40c1d40b240f009000e0501c0c0800001d03a201114907408104540c0040c00404108100049400900c40c1e1401e0ba40ca422407403d019140e0703001128103031424040c92070040c802c2034620040341c200905503164070440b91254042d510003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 502604235 1250 502602985 502603019
    0x1f1a060409050705071a04150c0509010c0204061a2502131e05010308070203010516021239010608150c031503030f0403050f01020301120b1302040501090501030204180b01 75
    0x91120401252006c68403000c0203202030360844194400780e040074074210804020342901054050304d000c0070003c0480d401300803605802000d28000003080d886000250040c0304680c4410b100a0240d000760000040400140040c0c2c0c900c81c0b0804800250520013241c90b1064500095000990012001a241e01c41e4004060f985541520491180031014048100c0340281c1003510751407004104102140b4003400380950084000003a080800c01c00072010303581d9603d0844042803a4004a48094110754110154503880b2035600c82100e4558a0403100b1010400441003102c0780d4200341c80400c95150005a0700c0c3c148100d6004900280c0c0c40b5004801e8640002e0401c159203074a03080d040c90956810806800c201c0d600c2074019039212301c0c618095290010f440c59644069005100420625030041225013181ea0401002011a1794800c198440c10782282d078000d51181c07404c000403401707071116400340e4140c0b84251001c0120401200c1c0c41b9a040c80440001460703617030400010b01c1752003942d00e59810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 502605485 1250 502604235 502604237
    0x303040f0c1509210203060610110706050703020f0f031206060d11131d0105010f050d0204060c0b0c03040f1403090904050d0201051806070810081f1a0604090507 71
    0x5065107444072804900010b4400800184030144184003104007008518010400000300314507031402580403a4403084000c126074419100b01340b11840741d41c0039a010040542400050b200520b0312040c01600540040740c040e0018451981c2c007646002e0001402002c000c1144021400c0c441105150680010300400c52604110203001c0c11410705482c0c010001e18200040e5056103031901840e49048450031a8820392100342d040c2c0200c0800e40050000381e041d40c0c028070b8a03100c2400c40060580d5244103c10992000f01d02c00900080c45551081c000c99032039110381183d12054491441c1e1000500094401400c1d405094100400090300305c011000c0c5c1e02c10100a903420250480300041642c9411641511181c001e0440045101d0303081c0705680d40064603865031007881131806001c82e07860000a0841d01480303044c5001c51156440303040303a240109550030445102000b0b4041c44920500c0c6840c40001c02410990344440c0d43c15010041c1d40c0108002c2d0056041c1881e00c003000000d40b2010b045c00c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 502606735 1250 502605485 502605503
    0x1050a050f0a0e040c2a03090e0606070209040c06120b1e031006060c12081605090312040b070b0f070507060f060506040b0c060106170105010804020102101b0e0609030303040f 77
    0x60f050303c6a0050b4445002251a0b601000740540200ca0510003900b440c01e00e4440000d00c8000003c0d0014106016242028075440e55991648080b503101d105a1340b0103507002038040104000c1110000f042e106890580d5501030640c581c10000d1001c0c2d0352102419540000c58140d070740840c1001c2d1190744280300c0000c084034841017000721000d04445240c0c20280c001542210b9000c2480549828045070400301c2c60880081c1c0303030414005040440d000500070821100051404090390100800c8119100c18036600303903219070715400c0200c15440740d0403c450381c3c04d04000040340d0454074000c0d14482d00355611483d203032600300c1c0e0701c81e80100000074902050658520713010409450b4000640040c00041090707982c5e45910b8610685405416803113101004401201c002109103a520342504484017070030301c103c9544a520041c3c0c18601245c21100704d031490100020b00401026403206540c9089440d40c40e04600f00c0d805000c0030340300d4024030a4050b8000c001043c0000c00c0d100380600303041d004030388071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 502607985 1250 502606735 502606757
    0x151906020c1917210c072405030c190c050f0a020609060d020c10020a02100203060d02060f120c03060f060306090408030606071502030103020108060402120a0b01210504050c01050a050f0a 82
    0x100c0d404d0390403120554201c00302048249188408100080140409130700240f00d85109144611a00e411224224100500403010a680e03a1b2a0015914484a100f40905460285450052207844101c1d0142d03802d11a800c0e05580a903400324a4a04185e0043c118514292030201440015800020345041c076030340c00c0142d1080301c2001d008142e28040030b1007016070707544035004c0024034201164400e010400d20402c02d105071565024003480200b503042d02d0a580b00c0042c0034105a15024442425401c6001a42046007008818000314810041100d26146d1041d5a4040c00914001210303001e4100c4208804100032072200300140d68810740c02044946071501d66561725140c8203a01440c80081038000c00188115a040300155034005002d4504500b84102107010301160740000e803005001e03e03030311000c515059110f95401e000c400b480400c540350b0500f84044480041804450a407504d0080c50b41403035140d03104004490003071301c00d55281400e00041c00b16114040c1c2c86046070b541400108005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 502609235 1250 502607985 502608013
    0x20901030b090f12091017041b050d030e0a08010c080f1f030c08010b041118032a130c02101e0608010c020607050f12151906020c1917 59
    0x64003440a030a8111662170308464014407401c40c80f84444a0700703010002d54110513075841a600f07203600903040b081c01031810b8154107010420000c4e542229411a02200240c001e00d500301e080c28050660680c5d86031411a900c002284c02c880903081c50000151545c0041200d84d4102403000d03400906c043c2c560019041c2d04494148501c08a60046401d40000c00040100c001c080c03040750204a825a0240700e4900c00d5040c10700c02d8424840300807483c2c4244070740f8040d903440400c0b1506403420520b03103880c004040c082c0c08503410689000098840c484030072800708005504d00413603202e60580c5c0c00074000c11032104440400340071080c89603240c0c0da40309084d5002d91000d500603040104540e00000500c0040c00000038140b0303200070030300c030f042c488100203164103030704018210341e0035040c80c0554580f0f90302c07105030909044000c40101c56001c02c25189075101c0c03031100360b80c050440c0e0f42d6800716240107405d1010712681c03010b807030140b00c403e1032208010030803518170421801194402c00306542020001e60a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 502610485 1250 502609235 502609243
    0x916120b1b04170d0f0503130c09060909060b100527090f060f0a05060406030f020d090305040509070c050604020904080d0524180a0c020a151e0504020901030b090f 72
    0x8801c0c0c541e0f03603204a10044005050088140c030b9002881e0404840e0701030381002d1300c0b5100140c901d0101d804134952007810300040715007041c051704500106000e260340d038031101b001a0202c20303010786419292070401c03109440c200854413032948942e142c8504180c10104c0c101100e00d42100c3e514a50401090382c00038551305c0c40c40740b0340305020f2039881c4511804d01100380601b15000004850146682210078442569603074260350440d02d061402150b4070400306400000703401451607010009080070070110805800c20080c0c019120181c58008003580c604804552940c40021701034003907082a8040760140c2060030b140c030b07032050140b44401d10340001d10607002c0441d441218070100070801c841c008606042221845541c0340011900c01c481c03860301c40441b50040b207002d001e40d1881c0d41d40c3c10380c1c814a203000740402d5142c0c0f45c120459203101c0038203000100140103401c90000400302d5a02081540c0442845814000c98000d0903521a43c0c0c01c1d0340c0c3c2da0690000203000c0300d009205000c802c1e00b511000300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 502611735 1250 502610485 502610489
    0x5040e0f0a0507032d0e0a151b1d01091d0105040c0c0308130507180204051302070302030a030b01050409060b0702030f0a1a061302120916120b1b04 65
    0x4100d2161800d030070740c1021260082c0c155000c250070140c1d0101141c0e100150143e8124081179010464039903c465a03004140141c80030400740a9803c0503014401d24200a0b5981078203c4424010210a943c40300c54260340e5441004c00b10b40480714090850f1b040040c00c02410740181801220140c50300c840070680c00c07110240800f511074107801072009040c0b034043d01c28100c1d080d0801c07a4600c0c1c49642c0262481070001c01c8180c118a4962503101031000800071140100a8840020121100c2204c010b002e907000740aa140100e000041610507140b0601c00c0302c825580540c02f550030a6a80b01084014081051105042000910011a803188507109a000408104040c030790b0b01d1103d8411b240c1844281e695000d0a40c0088841002003408540780c058118081c00074441d10703545480002d000c1c05210f10340340c00101d101040c1c502e0105031a001032030081a4001c21140800d41e202920085086e803800b450700020b0074452290006642c050656400145001d00484948989880030b00c1640082e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 502612985 1250 502611735 502611751
    0x10061a2b020a02010e1207020613120822060903061802030f0c040f0e06010e1905010f0806060a0311060a0318080403020109140d14150f01150503060a05010f05040e 72
    0xa0b44120b00e80c3c0911803842a44145009800348100d945004603042c01500ca01074011040000c560054031141540f45014111060341e0034646a500d003460089078100b00940048440d0140102c0445814400039400b124220b1740c40b002450300707681c0c8800291024001002e4a80030141d07015005980510516442c1c1d0f82ca4070003400b4040088003000309903218a40b41e925810702c0d1040b5030b0000c4a0214070b80d415101c520725600c9568450b48500040002e1140107200c1c06450f050002c503120f00314040b0071040751b05d14000c0300c03035076202c00313003084a006803c2c84001c0c01c5900e0030901490b103003404405082c010a20b810001210702002020040c600f007040000c0300c0072480014203004560b08540d040d009403ca90008645554100300410803e0b20031039000341c08081c0c01d18001c50500f0040007441180980c0031002c2d031320380c1000c80c4280202c0700b0030f020f01900100c41102080d610781c81881680d205150003070121317441c68940380040d2a580d40c20303011042040f00400010908000a00f00a4051030701 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 502614235 1250 502612985 502612987
    0x6220f080a090e1005100909061410030218011b05070b0a1806080f131a0105040c050703020715090803040e0420060306221d10061a2b02 60
    0x5408801000d000003504143c140390080350601ca100d00a0000a03016030300700392581520880c4904080e200f11040307510490016050171004030300d40c000c1c0c1d0411400854161018074501540c8081502640180004a042036038403e04040c1d10398418046104a00c181c40e4010715404416100e05040916075004002d0440300003540c0300d1182e5100d0036041c41010004200c9800c1c90502000900c0000d001e452410081041d5010500048020340404081c2d0b5000c41c411401e2440c02009000c0c43c0000d1040500c114500041ca88105009600f251303141a41640070703080c028281801c803000386203410b100344100408008041040e140400040c400340c0a00845100203142516001d0309008070382552202d01110310001fa582600c83c4402d881c0c02070000c41e081410b080c03a03580e114050591100c1180d510b941443c5a01803180241c040c02c04d400142d000966040c25205001c04e0b098a24501c202450288021642e005414000b4003800101312904004000c5d9441540040e2007403a010300c111082d40c0d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 502615485 1250 502614235 502614247
    0x30b03010c051306021516030204120f02150c0304030b1b0a021e0102120106050a140d0c110a02010e0112020d050c0a170603030a20011805060106020f06220f08 70
    0x5883d4520300050406200505084403580c0400c81050005000118804100d100c0b2405060080d01564080c09503401c410090750150308040b0b8125480700c40c160f00070140a26509482c014006c00c0324200c031002c10085241134038581d12403110450041841041c1e02c0c60b0303092000e0101281c0000c10300c01e0300580c02040c1d10b8204000191001040304414512a0310411a00d01c200e00030320301070f070b045502d54242103031654270b03401c401d4400080b901700d0000c400350f000980250842d0341d039002100c1168160b0300c00c1183c24030744503c40d55035544043d010380401d03254003c281d4251b1041000000c01c0400d94030260030f0591440302c3d1400e6807000e44036a5001440428003c003082e5218500203003040003a107601030305d4100311002c81d0301c0b840790702100410451111a086c4054442e1030041c02c60443c146d0081069020901001403c9004800b04442e180652000065181d20005a501c0081e2044001d401103807280344050002c4010349880c220241140940c076000f2070a10341d507007581c05000e05805a9101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 502616735 1250 502615485 502615507
    0xb04140a06081005010305070e0d03022a0a0e270102030403080f04021e120601090507091505030a050a0902040207030804260910090b0c15070801060503060d0201030b03010c05 77
    0x3040d5a0401c904001c400d01c1008500f50030802d81c102204c03020700b80000c181d2181441100c99480103003484c1d0304407001c10507410815a001500201800580810302c0018804096541000410240859000b18506820f1000d1000490115001b240210701d10b140344801c10381003910342842c041540080d035408400c0009140e0441e856a600010180701e45045250550008010f0500e0345066200022000310282d46d9440e100580a4826421407c0341c640307695401a06001d01700483c2c000000034120039000421440380585204905055180e25065940e0600c0110040000400319000d00d9190303008000541c5270380c4020301d030b0f540c002e80e0340815900d0a8204004610792509402a410401081c0001c100c203000c810f40f00044021075030b51240c070440042c00c480701c24543d040001e290000041e4500c0d81d120025043c1c402d4006101001d00540c0c3d1b4450503501d114092140303001060701000019074514156258070040f07481410001010b02c040707404a800c68404440140c0420f0000510035401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 502617985 1250 502616735 502616749
    0x61701061a030105030615040f0204030c031703070f0806060d0c0f080108030307020a020603090f0d350a020903210702040501080705030307260a05120703090c140103060b0414 77
    0x581d800791038461a551410011940da02c00003440c0e0081d01a1544501c0e809649580140300c443c40f0581d03080d500c0f03980707909110b0800e055500c4111070f40d80810540305610061007040e64850001519031700318007403241e201600c460000a043c50342c064010000300050103528800c0c40c02d403809550703031501e80300c201d40f5000d84403041c1a00030140551050080024143e80003401107600d50303068650070784a46810904528044400b120382200340510010442400d5103e054000b2002c044106010030201082400040c94000748030390b10042c00c41c8002030030980442d0000d01d03a01c1c00103011500d0050300480400000c00320b10b10316000c079030800200e2034150f2815010303244c00740075140040c03c0c02c81d103004002075807032065440c0101120860b520300082c01c1450304000e42504142e14209580380c01ca030800500036800222021170300000000400c000c0380c443e100303081005901c120800c40e070b40d0070611140c0d05604c0a1603058109501c0703041c04201f02c0c1a0102401c01480004000d1002d070801008101035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 502619235 1250 502617985 502618019
    0x12170f190e060115090806091f0603020d02152101060905041404030c0c030b130308091c050f091c03030501080d080a020a091d0a0606022d0106170106 66
    0x4090401c0220003081c0d00101d045411105005090264000c500805a90511840d07011813514000e0208001700c40c1c0d000308600c030416004100c00c02c181c0c02030207058011600d182c00040d41141000444900506051801644406160206900701030121203c50011908031294400002c900d900402c001d80e001010304000c0e25080ba428801449152009580703060000e0010b81084104a0b0b00414404880e020b03601550b0408181e424030b15009050078801c1c0c0d08440c0c201c000680c2000001c40c4000c1c0030440302081c24025500c2444061900c000b1100b0340c000c0b075002d007010038040040140300da45200313945d0f078801528450ba2a41c4091803c005e030480300d05030311008003900000039128519070b01002ea168410040070005844039243d20084409001c503812038a08181c0b403c4002e035505842c82c81061007000c021009204058070780c8412a25016469134030003d4042c1640701c64220040c1c13001125031040d0500000a882d80d540c1941644001c8071810800d03243d5468070103011200312074004c416 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 502620485 1250 502619235 502619281
    0x1b07140307060e0d0c05060c030304290f0403091e170c030607232107090513021605250504060303090504090c1a04081902010c12170f 59
    0x10310145002d4000e08250895040b03503100f569000200d0040141c2c0041280107010b0240c411604e4550060801c0d43e40d03071082d030f000c3d1025910390f010320351058001010814000303100ca100b0315180c3c5483c2c1c981c58080304054401ca061000d5014003245c03c284110190540061104006180500d014000510402c0c4602d144a450704070407200310743c64070005026608581c1d40d140125004034007545a07c034000c1030036994520181b001512900703520b103c2918100d07848040421b00c030151151a07040e10807000318070034580c00140c80d40d841c00c464611035001d4148010302c00c0c4e40700c4600c14140d03180303410a000944d00320740001c601203840c4034501d196482d000140c81d0a07507042014034255100a80703020400d20808c4d01c51a12600c68030208101d44d02441e000f0070801810b200110414410615160000e02565425101f0000c0c481072004000e04020201d0f41c060312181003215940d182d180ba4421a07c4940060101800b6844803c11025400c3c0d4403560a0303191004c51414084243c56201c562051521 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 502621735 1250 502620485 502620493
    0x100b1303020f041b0c060e3415030f02090909030714070b03011a13061d04050420030a0f05010606260c18060d0203090c0a1206020d021b071403 63
    0x19019441c04d200d241c0c3d0001c1982002d4a0011181c540440940900d1041c05a00d001d00c4010f001203000d89060f0f0b201c0c0380340c802c0c05521a0301000348446450622441000c5ca80460038a00080741b84c0264880160703e0640e1101510b82401c03c400300307001e80e4041c0c079540c40c103070f02c00100303070042c0705905c4410104c408031200545501c0b13103804c80d00003041c003060107140150302541c0d11902860301da0000f250003101c0903c0c0111201969148041e0801c5c104031603014560015120070320030b42c41c05201d010300c220751100072a07805806824142c11080d501c0c0c001d103505071041100c0385000c102c01104005510784144004600a0b003031503001050045080c6250710074050403003480640c041c140702d1150b8000d090001242d00c0c2c070740c0c109640c40d040080c0e1203006d410a00002d0b408541c000203400561080c0319503003c41d150f00c0307480c00a000300800184601041d500596007040001a0302760020711071298004405801d0000305810204000d41514026800d540030000410030803491001000724030b94101c01038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 502622985 1250 502621735 502621751
    0x21c03110318040f0609051906060f0c12170a060315111c18050105150303040b12040201030603060f0f0e12071403040305150f0a090c050603100b1303020f04 69
    0x111400030305030300e80520039500c40b4101c8440b49132a40c0003600400500c0c40501850414001003200a000782243c8003880381480004102c080c0070b01da40354401001c1e81e4850b80c031162203071984d0f40c60071102e24000301000b4104081205c1d5003202203004d409001407240008000f40795140100d07009010038102041d007414040030032814031904090340c4c801c0303402035003c1201a00350b4205c0d40003070219501c402101300f1442842818418154041807040050300058620644494205540ea010714803c281c40040c1c00c2003000813007210710b84050381007807040c1800318450b03849036182d0b0151152124540d4900f907490b20303440c044010b94020b00c540b4191210207410030f01001c07100c10609120301c007405070400407242d04c080420701081049400440d01300c802d40f070001e0b4164030580301ca880300340c4284e038882010101080c4e880c0114852020425800f8244042c140c1c42d02040c024203030001000f2110007010301400288001c544001084410700b49410384805034110701c108110741200208280c09203143c201d103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 502624235 1250 502622985 502623007
    0xe01090c020c0d02040b03010908030c0703121506050a02070801090f060b100503150102340e0106051912110c010606050909060904080c0a0309241205070507021c031103 74
    0x880f1604036019038004c9000c40c850f40c0881d01401070319800800b403580000c2044807030404031018018a510990310403d0704841c0c80540c070203a404440c185074284019220400c207180c043e000070040c806441c0103035007080d96030f10020707801c5600010060b190b41850b8411a4200909407003205a141000c540c480f003241c68200700180300d400b004100c86070314590041c1c5c41c40c03140e0003000320258001c0c04c2820303d8400003d44c0312203441c031240090042500d04054102180081c1501032240c141d640380d503121800e203108021080e03148624410300a051120314144000c5229040c00341002c40428500d00300d6480204c4001b00b42150119480b03102000780900c9a10f441c0e98906903260f4101f00103c0d00d50403d9115070401c80307614442c0041ca20214403410881c20700700350b00300355000700f241c207801a110343c0d00d01100030751007400700c60001100010344010004083e03001c10341e00481c0c02c580386142039401c084c0c2a5010030b00c042c1d4084001d85400b901e10808004040e030104511100b50b1561014505100600341 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 502625485 1250 502624235 502624249
    0x506190608061302131509061401080c0a0e210601030516080a0f170d050f0a0c0c0209090c060703020102091207030c03060515090703390c02030a06060e01090c020c 72
    0xc5c81440041c44920030182c007038000b841d003141140000500903076102085001428288100c5804012070442c0194a40c0a41030483c400c14003015060b1510890b10001c0f1004803021100a61010029030035002a9400d40050440420603200a180950460410900e00206200006043e4660b03600c14044620003160101e9195400300160b06031410a1030807410403034400c0d428580d0360b4408902210507140940141d4081c81c1000c10301405915100401000e58410341001c5000c2a40e41c120032006040900c00950701c40d0304c002c2900d0504100d00d000410550000c2c0307050b00140e4005c02d00000030728000c561401c400300302000511055117540e9403402c9017030b502c0c0300203003699a40b03e0001e5920140e004034000d5000d0001c1c02c04080d890403400103002400e04078900c400e95186065050000c4110745121312961611145a102d410241241102d094001301c80032078041c020600d448001402900030b000140c2a04000403145d90705102d100f00c1210702c00107607182158402010700350076484102c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 502626735 1250 502625485 502625521
    0x90c02011e0c0e040f0f05091c03110316030906151406070b07110a0c090f050609010b030a0e0307050a0302060402030f070311040504020301021204060f0b12030406030507020a050619060806 83
    0x40d0340405c0d46410001101c004207001011400c0c407030b0800041000c83e1801044240f220341c00802521256003590301c08904444010600e520f002c0340400c00310b400c000d82c044040c800d8031128500440c040c8c2041c2e580c1e00c20b850000d00540d030104036051741406001408c0c00501441081940e10506100141e101e005000c0409480c190500649458000203403c0a010f03031007135150842c1414940c203540d008050002e0082000402d141460140405c500746044041c0034102c44402420b1810340d00e6040c60480109000c00c120100740c48200300520001e039040c820a002c01d030081e000b0701400e03d0a0300600d0306002c600b01d00010703543c0002c802800007910390050498681d0054030300250382d40d11840401c6c02807059040c00d0700038001c842c08100822015400199254000c902e00b880a06080720a020203802c0c0c141880185170001e020a00400740709500c000d9001604e48100caa11203c2901e43c0c5060a006907100801e08010f021040c0042c9030034080d00c0010150040144000d150034014010b507d0020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 502627985 1250 502626735 502626739
    0xb03010216080717220902090f01080606131707060c05061303111f0605010e130b0a1208031e0403020a030c050f010c0302130e0408160606090c02011e0c0e 68
    0x40f410800b88046a618540010146001c0b03030350750001483d1021030300d1520b5045ca510a00c40d0702001c11845502d009503038400b10090a8030345038048040041d9008000200040e4000740244124401c2d080030320450002004050641c0120405600045080102a810140a128100c052840044d40000c0d406a1011a010038241508003c1c03904590504010300c20b06000d01c500220b824019105000d5091078029080c0c007000080d9030344006540715a4a900241d82c420742c503202030f41c1d1800c2a074003e501d00c40c600820b4030083d503441c2c851504442c0d42d1050281c403002c101004200b09007103500625006070901a21a603814903080c2d070001d542d1880d540b030044c20840000c5101c410080300304124030510318808002c3c0009550350784010000c0d04079400c260220b20030380d01d0000301c0e269040c800c80d000d203810559442c41c040100311003481c0a40c911400321221a41c0c0c0c803001402407194400d114040001e9400801d010f1a9032801c2c00341001d1024000040c50f1914024280468000a81e85402041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 502629235 1250 502627985 502627987
    0xf0f01140411190809060712020d020d02120103030207060c21020c04020a0e031e120a0e060a030f231306061d07180f0302040902030c1e040b0301021608 67
    0xa6200454081c0c00c91540000c074092012560200c940602d42150704003c0580ea500c12869480d00341081da1600152046000f02d106822007400c0b107007843d00100048006140d0140c6007160b011130a8007240d21041c266000e506070310005104250b8140881070050440b0b00d02112440f04a031034104020354032200c2c811050a00c040c10924143c0203000d082040640100115120000284003502c40552414030710701c030340114040e02d2a9000c07080d041035440c08280c00240310140da05603101074140e0107001c504c0144808200080110343d100c1008001360051942c02141502ea503406420540300b8249140c101c14030b41e40040c00000c0d6000c16107a60010b044a003c10700d86071642440002420b0a41180200441ea0108100000c0c4c910102c1c6000704901e0742c03602c04d880c01c041100c80d08840c2501500c02e024030106c2c801c001602d01600503100340307400201580e4038026544002420440e00e9034027141ca05d8008109410a45414410100700c3c003020b400a6241c544000300780c92890240040041200e0300c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 502630485 1250 502629235 502629269
    0x100902040917030603010b0d050309210111090906040209010e040b01111b090f010e060d02130216060b030102131a0f0c0a0b01060c02030604061d07031401050f0f01 72
    0xa200d80241030456008095480c40c070b04002054080c41c3d0085070031900940c02c0540c1c0841904206174601e1711560440d01450514a1900c100442d000b0300040400c14102480080a0281020b01c1610500609100b4099650310502e050103080003008001c0c511841c410700500c22180d070051a02c4410b03403411940041c42042200040e03031015048801c0207101d1241c108e800c0503000807002e2000c20a1812221340e652503032500c01c1000080e609001d00340d0003003d010089407050070060010a007051004086128a43d4070150030360407078108001c807481c1d03200c103080c3c40c1d01408003500c52a280104250005d51900c01084902c401e0b440451040580340000b600a8011206028060705c418440920350f1a075035010381c80c01c00b540c5120b805000c1d543c2ca0031007000014010b014a203504211a8043c000d025160744135118000207104030348048907202c54040e00c124043c8802c0c051100558890020b422007000d410110908646000f403105040c82001c03000d00c0084000308400e981181c40e00c44005034200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 502631735 1250 502630485 502630489
    0xa0308060118030f02030606060403020d080702040f0c03051506310e070c03080f16030203041a0711010609060501020304230603010b1c0506010e01120e060a090b090a05100902 77
    0x10250000322070300e03030203000c0100c10000f00c0c41c2541c4141e8021400c41f401b50b01e4110402600748900d1200a500c108600c0e005800128000e010b0500140001c20020700c00d10f00c0b0001034107449081104000081d0b541040220100b9913101d030080c100402e95a090409600c998031820001c116800e5031141008000104492004080070340041c2960441020b00da04080307401416210f0b01610880124215000150035018441c03103452041040c03e407685024441c02d1400e400950002d00266170b480031207200640000e1a134240b040c080c07049940d95105001c4c24412150031100c494010601c02c0d400c1c18802c2116030b03400000da800b0f641d41c5600a44805e4480c030300400980b00c8010005400c40c2d0084000244403200301d0140102c000d24005a02008054147c44401c0b01d01c200c814501203601c1203900c01c25548a504000789441c400d4000098541080e0280c2d40780c0001102d58002c41074848a85104002000240c02c0e007000c9035a00403c0031034015941d4903103442141160980c0e103950340304114159 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 502632985 1250 502631735 502631747
    0x40b0a0b0f0402070302030a0f0302160f030c02030a0311251413050f060f09090a06050c0c06040f1b08060f07050906190908120301030807170a080105010905060c0a03080601 76
    0x40704010011540c40c809072030080d46a400090001020819840c01c03003445500034002c279400743d24054505807095a959403986030201a201080d400c0043d03000c0003000507103023002410f05050082c2c03940d20000020f003466614195800e80c0548021000005542595600410020580e006195441202856900440c49800c802815141014103050a0201201e404a21203002d00030075102d03500381a0b80c0c0300c18400030a000f0b5582d486550300a22400010480755400503811904824046282480030071005241c850140e40030b0f983c0040401290301006a07000c07205182ea2462034039540814a402a065191080108012100040c450009101a1198084070640900101501c1d181d40c050894004945000e217580740c0400c2e64403801040903400000c100140f000c2c25054640703181c1c00e6568030b000681081c84200c1d5040281c0b45141210450b41000c0c05040701540d40b80c81c425031401c00010469507a580c0100e024403010080011034036004580051041c0e050304003e442078403050012100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 502634235 1250 502632985 502633009
    0xc030b07361202092e030b0417030c09040b13022715041205010f1a010810050d031b0f152f070f021f090902210403050702060d0c1205040b0a0b 63
    0x41e40465400401000010340da41f41c05207024108a00e2000508088200248026600681d0001081c030044085181640000401d24000f901505960404025071002d982002c601c40c4521250614103240d582c1898450102d4042c084801c41002a545445e2100500c6140246502051503286039000d000003508468003e0032800804c010b4400201c4144044c0b020107403001d800106840701055116554442803400e5490081c040401e890440c1e0301070b9582d14480c0000c1540c1c0b0f085481c0340000c1071180c115001101d0180b04515206100141200b089a0365550f509581c0011050450b11070081c204400c105030ba050409590740355414144000c410b102ca03000258090340c0303003641407070240004400e01800f040c0d0b515040d002c02c0c0c582c10b4400c164002c0c4012145a0f02c010000203a403101c9030300c2d0790741d0418040d0501d03901c0c02160f9004204550300c011140b40b201c0352650720a88440b58000b200364090100f10394100200e040a6484848040c0c002e04403156194803240341f217056680d40811030702 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 502635485 1250 502634235 502634311
    0xb06091e060d23041e02031c030203010510090b03072111090102071208070201050a110f03040609120215180d050f06010e040c030b0736120209 63
    0x41c642c580314010710050045510031880d0814032200680180c0048000e050160740d00445a041c1c0b0b4255000130451005107842c00d0364980301d01002c40c183c0c4d00762919030042e00300140d034000d40d0301d40c1400180030414200148900030400301c10b2042000b001c03000192a000300280c9171851101003041d00c610855440c0011030601c1610384407990b00a070001100820001030b081c0c0a07a02c1465442c207403a05209041c0c48c010302070070320401045005601c0703000107050f441e050341803c03458a2000c4036140d1421a1400c03a07a550707503000003804e00400e0b8001e44103500920104003c07100000c0507902203441d09000031500500110045036104420f00b04020030340c070345000500340e400290032608240b551042c10b034204400902601d000030550000100703807244940c0c1c0101c0f804130803c3c0703955943c1d4080b910040c031b004c04128108450740d000044140c3c20400c0705014186e4940c3ca6404812546041d05a03035100ca00c07240c2d0207a80d20b40068844d0314106070300806a00000c0603a5803a20408020881703c00340b141 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 502636735 1250 502635485 502635487
    0x31a0a021207020703020405010909051b0613080a03021203070f03090314131505071205182101110406020706081504110307090e04150506150a1d040b06091e06 70
    0x1c20b40a50010715102200c0c000c840503c5a6640e0b00d641c002242c00030b801c01391113500885201c0d10b070848050a104c1035802c020b00740500d08002c802e3308005141094100c0c11079600a01095814151304100004080c003910000515500703041d04098400c544111006003032644508034101410f01860150600384002c40c6a21381e00c420207403c21b021001d507402481509460a00016031181c810300581c4d0090340d0203810801d09040f440030694075604100c042d44a090019102c2240e252201e10903106480c03100300303112050742408160142520303c014100c0e00c090100b40002c01440c0c1e07000500e17404032010f03403c2000c2691038a04800c1103010a900645400c1828181d400a44c0c610500080d48100d06c5903685c0000d480d210541d032000b150064074042c2500541c2d030b1142071480b085501c41500914020b050001c104d00e01d01040c0c10f20381015071b907103011404420801e00e400b0740340d5840c81540c000c120340c1000240042c8001400d20700944004a0042040016802c5690404900d0b40c9240f10000d0407a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 502637985 1250 502636735 502636741
    0x140a030611090a090603080901051e0403060b04050601140d091505070e010f141e070209090f0c010503040f060c05040b04180605011e050f09060301090c0807020304031a0a0212 77
    0x400869118142d814050500303680000307001c42043c443d6005a950000c14240780041440044926400201d12680c0c10081c800c120120000400010b10045104040201d82130810070b0070001115030040c1020b0521030143e0000450050440c00c0340e240212100e00056000401e040c220000c0b40d014280d002c0540c5030005205505801445402c492002641c44500c0c240c02243d00311041e910400c01032030b19070000c1c010502d038211128500000389240582c05403d10020341c0004000c0c40041d1000252a0820309585800c144c4c1480100000310f400c0c2852803840c101a9192101c042c000180500140d60301d0400e034814502c41c2e0200d030024892400819212526410b0040e8074690070341c02c03c041c0b51324000002074594084d8055032032118114100e800d246020302c5060351580d102d04506805224108400072039952288081d40c068100c0110000d0708410030b00303014096503400742c070101c1554400e00c400c00004824031551a903c29001c03108511071344442c2116400780c0a140c1600c201010440c0c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 502639235 1250 502637985 502638011
    0xc12020f0601330801140f040c0903140d080621070303020f01050609090c0f0a1d04020915130e03040f090510060e03030412231005060a0609140a0306 66
    0x941000b19451120345194044460320110301c01614086980c08240c1e44401007141c4002d00341104a07804e8054187c00780c01720f007040042c0480c0c2d006100180400d08200083c0144941d081c180480b10050350000c050324141d5440282c9241c000400355031250740f030801c400c808030011070948008800354204440b40aa160319003e52140c0740e03400c0408942d031034440050340501d48034039014040d0354030780080e1001045080522a20b055610342c00c0d034108000d054000303110025928a01494207004e01085079a05013441000141c800191070049946100501104c017560342e18032209840c0038480c03001552095203002c0e181903010700e074806030b419035071228002095525604820300c280c0c1a0f041d0003808940b20340c0160741c240202182d150701980284402e001c1250b05000d0201994022100c020f6024144540306021490b007000c81d231007940203480504c800302c80c14061103400003001c48640306058180200102000002d00c503005e006030385109007418179192103142501858101006000414460f14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 502640485 1250 502639235 502639259
    0x90b0d060203090a06050f0c0301060c21030f0608060411060c0a02090a060302040e0607080a020a0c140d120207020d080a030222051008040c0e0615120a05010b030402010c12020f0601 80
    0x2a05079401e80c2032000051403c0008504148142304106000c3c0c01c69003040e05c1119040c5000070100d404121020382d0b03400310321800d071040d60f0391941075401080d4090b00b00041d100f91031260340550702d0740c3d108030300b03101c000ba8400c21035030f0400e281a690540ca17200c24207641072500b0ba5107400a504042e140c0705000c40401580c0081041da80240d03824000c000c8c410380400e9690600300d80c2200003d0550000c1148001c0c1c540007807120130302904c0c1c0004c514000c3d80b60541007041195101f035160f03000f0350141012940108040b00401d58441b0110f0030210340b500415160716050600401001e0002501200702d4080d03030541d642c0d100c0082d1401006000414070024050540c000d152080188141080c0c00c24825040c552203070b0381c0050307080e10141c41c010020000d01c10240c459a0f02007031114044e200d006121025003003410302c807200b0580d10300705209072004907070b41a0001d03052100c042040001603608035810701c051951003c5480004455404200d0038002c145010750704234080c0c540001400c2d20606 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 502641735 1250 502640485 502640503
    0x180606090b090c03060906121e06010608070801060e0d031b1407081f0c170a020307090f050f0d030516150b0307121b0f120c0501020106050a090b0d06020309 69
    0x902e54040319158440e09030510f003c12100c50b9400301808000401e5814016140380d003820303000e01101d803d1030104042425960515100d482e50f42d128034010030103694048101d64202003103060600031541004002000d148286030f00070f0151901a01f404109482564055a070080c600900c0d07040c0301007403401011444814035401054031031803001064000000c2218003824104a413040740d102d03041c111803409060780c404400d043c00b8080c519207520380c2d07200681e0703449915503000050f41c0e85401c2070050400080d942040e10607001e07108040c00551900800d184040d4401c41d0418050645032034100c1d054415074044800419007a40004100400910070411483c007042c4280a120408014943d03562447d1080d140b00c5007c448190307000c50b0390015420b120414410f000e50040f51641140030908510750b202c0380340f070000035561809029910049001402007480280302c15890240000e4070b03032a0502a1001c0319688031880c04141d501d0803030000348107074420015522490002541038840583c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 502642985 1250 502641735 502641739
    0xb030705070b0622270c06110a03050a0815030d0201020904110f09120c030724170c1305040c020c1c0c0603020903032a0f1609180606090b 61
    0x700c0c00300d0303c2440e240001296a905a5007005844003404075941c02420004040302800c81e400c003c107205503968407091101c1e80e40036035805108985409401813107003c200c0a2804640c01c5260b09800080e400300447e0031001903803030f041e901900c1d03090441320569000240c40d940361040385640d4940d1a0107401404001808441c2040502180e42c02c0c03080c644107076107200103840c000300f25182c441c0c07070701881e03040c0510404400c032030860761a00c0c0420b14081c05e0f504840f4007401c80b28a0b088624032000f0540038100244c0c904410203140c61018004600c5000c0c5c1850890000800c1c0c030107003150104403040041100403c280064420302d600a9201c6140c1022030380542c400034800d60f4031072001c0410000080c0e00100e5892050703c2e11508070025040000c181340e05000402c10300309251501c10b00c06600001d50f081c04081c480b14a2031540c980703880d003800b41c030858010320900043d11204501c03080803502c1071100410b0300301290340c4811285145881c020400d901d8003c0c00310f8002d10940c08880b949200f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 502644235 1250 502642985 502643003
    0x4150b0325170c0103110f03241c02010e121218060c15070c060903020f0609012c0327100305090d0c02190e06030607030504080708030c040b03070507 66
    0x22080740240011002064565a5000d0300707003075032154406da0209104004181c0d000d07041a1010340701042c1680305699400d00ba10007480d02501c00181110300b400100012900b400103030a94015503881d02a03881c1c4045d0503c12480d03203000e0103403169035103204610380360000e94034111000c1250001356040400e00031801c000c54604d5035140e091000844112200540007444602106001801a40380040c800360810002c415410002000da002d43c00d041d9200750050121003008000440c07034008010851000f603814a81b032000c02d200c186a01640b1418042d045010756000c0c01012403031032250369000003006180f8403201300141c02d007904019050b04100c0301c60003115002c810407001da401c259019400368110794650205103000703a03203280f0030b648050200710590803990301c0c4803043c5a03154803944a0013085d10401200d481e060040b51391103000e5007001c1003581080d890f8803105028000e0b0040c500346001010a01481000702600c1c020806c02c03540a03524505480000c00640100000300d8284d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 502645485 1250 502644235 502644239
    0x20d1404110901030f06020a0207030f1a07140f0d0b0907020d1b21020c060c011e0606020c10090f12150501050619141602100c020904150b0325 63
    0x90b0500380c0c030381201c0c1c00c040c880c615060035440c0c01009500c02150101035220701000080001e203040d900d030103250b005015160415400e00000000c034030b001007184081204055019540e200301c9000e5801d6440b6114425071a212044400c000400c0c16604090b40508070403300b2000a42c00124901d403260b00365908500303514161004c400c0c600025000908004603002004e290400001d084060750031203104591410b2281d0000c00c005a21407521404030381d444c0c01c0180726170101e44d0a80241002100c00801c859450000003e449200c00000240b04d9003400c02d42e001c07280e10034000c00c0301400c052003041e601c050392510002010060144202e400d41003007404569840340030301c1100d04841d4080c3c0708070318002045080660176210b02c003464051009022600540c01d06403809000700c81c20703401d0701400d41412801002502c102071040c250403c03240ba9901001038a40d114841d82280e03102a00c1e00c1800c071001d507050b01818801100e80d030503118808a01035485227001040000c54000001c0102090b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 502646735 1250 502645485 502645489
    0x60e010609060c0804050915180709080c10030c17010806040213020a17060a090608031e0703120908070b04030c0209090a020924090406090308060a061e03020d140411 73
    0x3000840000d88158400d000402847c20300f0005e90741d01180c2c50709403840c034000c8140042c90142c0051020308401c18410200204e164000b04030300003902c3c82e68010000b03013542c0c8001030070f8503008100100c10140c44002807a5601c0c0a0200602a0300900010019542c0c5611449a54100c00c540980c4a125048120b44a0090030b2085030781208656854410258030700088003012000a081c264000000031800030340000c551103420045c00000c1d01a5564800141080c0f200307844614010030b20030380803c03c40001035003040200495414180c404583ca001b9410000e21501844001a01d407295400c200001c06510401440c1e141d03100310782103c0e03140c079620007c40d07445ea50200001d40000503580407070b800d050300440445101640104000340755503000f0208090402c140c40031200592070720024406c158000d010035a0000c02510b010404c0c51910700002d002d000d410503008012000c4406001206100b901198039011150fa0203022070b01d1100301e6105800301c211000d407041c3c50f01d00c01c0c0054034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 502647985 1250 502646735 502646747
    0x30605040e060402011119110a0504050108030a031112070804060f0501140f030307170316031806091a100e090102040812181c03030b030604051915060e01060906 71
    0x200d03803920090000b079803254015607040900f2461b031600e92152000c02c4440c081c88680d00300e1614428079100b91075256007410712080c12040e4010034426403c050060103a0f820000036140300c0c5125103400300351909091280c206500c1004e1012400002000400000c1ca41100f8154041d52040d88101710b000701104243c82180d80a00584041410300081400285000f151003060808000c0503170380350000c655280c0041c07420300314641c00d14280110821003400080034407250b0194503400e0a00c0f10745212072080a13030800d0320034000d01c070b0b65451440c402400000115241110024241c04a09050001800280b080288079010b40419910002001a9010b000b610100d03003108009040f40c009004590805030007262044007001462100549a079944d4000000c0100610b8103641cde00340902d090040c04e032900f40e411180031741e2004091000054000400f1290000207260032030a0401901d00340144002268008412906200700402d083d00315884981c100d49481c2c45480b0110b5a6510949035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 502649235 1250 502647985 502648001
    0x40b030106171f142701030308071704020108090307151e0204030c120f080a08160c030c02011808030417010b090f01030b0c07050f0601031e050303013302030a03060504 74
    0xe0120703110010014800c0480c0fa040b81604000c5c5a212003c030800c0140d1500300101100c0c040344076410300104181a0030819a90f080034980c40d003181e011914800c2c800002c000070780b00034100034060b0001500542c0520543d04503507405220968008802071521015051018010031a0042a00b8000303458038075108560499a011b02e00b038080c00d00c2e150ba000081014541c090768820003000b828000101a0b10041c0025a07690711010100d04054075841e4958005141000510000c40ca0b5070000c2908000b00a4203140e0900c1d240420354403010800340d0907001944513890f40d20012401240f00d5140c0450b0388507202d900e80082114501903000c100245030281e5106032042040c8006002061050100c075500601041c059881c003101590f8581c5000203074004074030b181e0007007070050003084070300c0004050029041d28040c2c14024240c840310380700e100600c40c3c48003003140740f41040303900000424a411150080012079030096841040030303490350303c90303c0b04c2c00020780fa00c8030214180c60140b040c182 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 502650485 1250 502649235 502649281
    0x1060f020c0904050309130207031803030e0d0201110f030d110a0903031d060318060f071b06060b040308040306050703050106050403060b0d0c0803040e0a05060f090c040b03010617 79
    0x19000401c040c00714800c006001a00c90707000c20443c0c0000d5849031040000d4107089100b0060785d501035803e00a103103000704240e16408045103441040482d0384880740c503030280c2046540801103030b15403005a41003004800408a5402000038000b50101d001c0064202007602c2c0c0c7d030502140030310740d42103c0a8850381c10080b0214240c0c10003400801c2c81048003a000341803280c10414600c114000082c4a40c00403200080340100241c079140908a0038880141c105a040444800318240081c0103401c6005054070240764441002c860014070840d40c200d000180341698034540d856449082080c0503a026000070f40d007040c00c00f004259a5403180c4101412941580d40d082d04203802c690341c01c0301800b100040303541e008002010400c08039501d03405400050884500569a46141001d40084500c004102407042403410b000c104103915007501105600c4070454180c2d01075a0f51500301410750045070480078000b0300101c00803400d90340100c400300742d451b030003503d20715680d4440582840000d107808000c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 502651735 1250 502650485 502650493
    0x1110080705030406111803010b040e031804021b061012050a0210120c0504140103060e0112140a05010501090b190b090f150a08070809190812130b01060f02 68
    0xd02058400c5000e9500240f1540c00490a41108095640260040d8091030040d0744403280c0480180760910030302e580c243c03040e20f00303202c410700c207040136070300da0080c1c03aa02140d5000f0020b40b0b41c1141e6035541100e6180c1000080b1b805010400c8164954911040300c2c0100305100514001c682402105000f04456911074001c003200940c3c0e60034843c3d614a400116824804000000f0159a1700c41c0a02d0a401d041a95441e0700c1e64641b0402c0b07a03441e010403107201c4c140f41c42d00344144528051402c0701810b541c1000742101d800002841e0403507200a80010b007050078018040513404002c010340080d0b048515221003848030011100400c10400514201e101390f0a250320b1040140400202c0030b80f2104600414105218401d140819170012035032004054000f40021300c0307850142c101d26542d8000f045443d0122052500c03450050361800b0002e0240401a862800c00c02007082c0b0904440286c107890001075600c0c18116940c01d6203070f40200084482c1c010765400824003e1040f01c4003000c10391103034014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 502652985 1250 502651735 502651741
    0x1e0601030e162c040b0712390311071b0f09020c0c0a060c03270305010603061803090b1608041d010e09031b19120e01030204061d0d050609030403111008 67
    0x36504a11f184140c2d0341c401d510b5034104101c643c0780760001c064201c1030001c0d010058448250000307011040070000301c103161400000b8003c0a542030181d5668a80c0040f11084038007802038030300c0c200a01c2d0346c46800560449140400c2c10002074021301414902c080480b13840420100400c2400c88031400303240d000800c00d03000d09010904c00c0c1e580314105880120600c2009607200300350580c0150350740040d586a9100c1208100304003151282820315041120300e01300c0c400c0c1c04d981c01822601e003072003040700e0143c0114411000010941002c210554446002a0b0711aa18504040c00300700310002d035000c0080f88000040e15440300c0c049184104050b41c040d502e00003158a0ba2529400790b4034496896204415107600752a10644441000078001c1d0202c102c0e08010b010014001d000710400300d410180180710800083d074000101c121074850035500144c6006803a008640440e002c03501c00340040c800d110900441000200041043d070340038000000c03501e182c6106000380c082440300c082000805113000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 502654235 1250 502652985 502652987
    0xc1503190603151d060f0402130605100c141b040207060204080105040323130e0601110106030303051b03011401140f0711091e0601030e162c040b07 65
    0x515800100303404002030258498580d03031401c041c01184000c0c6165980c9000303800900c040c1c10499050790207001802640381050001c1007041000e08001d000302c00c00740c0310061818031900300c400646409003407003944c2c2414990003000e0320b07a480d000352580d0f80381140151041d0701c00f041c400c124940704650454034030070150900c8000d40c03100340d0984a5a40c20710020849100a000303803405a400b0f075450300e80d000040702d0024225001c00442401b8498204104500307048030b440d10608943d400913140322a0b540b0040141c481c240e40d54000701031946003440110030150564040b60140c81000740f2892841e86550008001e0700c0b0078042d1150400c00b04444060139071103004140110825880c103182000001044554280c0240200b21159290f140020b01c490502803900d035845117648a44805601c150b9403c01110f1501420050416859070030380c220a00b010411045240110382100151940d955481201180300d07003d41c2410010040600780d141c0d207a000c001c0d010303907002041200c8588134214 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 502655485 1250 502654235 502654261
    0xb01020703081606140604060e04170a0c080a08100f050303160206070b01230d1203150f080f0607051207030b0109091e050702190f0c080601080f0c1503 67
    0x5400740041182803030f000051003a000d0810040c4000851002504055042200b40d0301c49400c012400f134980c804005c0890310040310507020307207201c40046640323410f2604116240c9500e5075010348071540000701566607075403280410341328040c090203841c040e603152002650040c14034850183d040d4003e10808180c000f117811802600c0d4402011203182441c1a43d410421800907400344656902810035058401c01d507032810071501c001260005c00d840025987d001c019140c0703145910800d0791b50002601010000302180019004141700000700568410243c0c0e9140084e9a44004c1c03802044046003100c1d004d1015185001c00000c60702070765503a50b0703404400500f1201d001c2c5041045c2180c0004041c9403138469000902c1d185078900d40203031104410300c1c0640d100a800b550466002d9084520105d43d40319030b20605584c400d010a82510050034041818942c0744c0100e00e560107010000602d40c0c0c8005100c2800358000fa06980301c54010404001100c1c104c100c4684c2d1110f0204006400398510103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 502656735 1250 502655485 502655497
    0x80f010b070b10090c05040806070503100b0d0624141603080907150c1a01050307090c0507020a060801050a091112131b05040f11040303050313050d02030901080702010b0102070308 79
    0x54003091382c1c800d980800d40d0905171400d800f0910006042c851280244100d90388500c260800c00d141d0b0030001040b4140414500c0b03200480200491000c002450b43c4d04480d0050084030117502080d0321800000c0e4103100000007010100e40c2d010001054002480c00b07581c140c080e10460100c0b000c000d91001d4401a1004001101e54041c0d00004501c1c154001407121904407a95100c0d090740e140c030328101210242c3d804140c1c0e00c4800c0c070760040000b65000120a01540c01111011400200240b002d035087d008040b00250301ca481a90b000c00e80310b41c01680c05d412174104440d40001942da642e0402e01f12040e00201c40302d440806c0015080e024109400b01c4d40122040c0c0404010400f00e8560070440007264402c0082800c100000300b140345007034052900607090b00300c1c041141c0c101c41884420548030f50f00c030090520401100081556443c95040030650fa0040c0603204822100300c1e0003503ea40c01301c02c1280c0814034a4001c00e82061052107441001c180607001030811506685420246030460 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 502657985 1250 502656735 502656751
    0x1b08010902060904021318140f0907090209041404140705150d0b0607020d0b06090a0209180406020c030c0102030402012c01143604050c0a0c08070204060312080f010b070b 75
    0xc00510745104c9600d520b03800c1e20250340095201c8c100511040310702400381c07000c45401c0c43d5406018078007002040d44411103400110040c3e440e006180414080c0c40e12a5121004200050030042841001c908d61000600088265056240c440c001c112441c00365200c614041d600500c58445400340c9507002034501c01009054500700a5144e000030a15010f00c4811a00b08004070180001410100001500000140030540c200309100010a0941413504203101e0240603071800720b07040c4486641250103081060084c1d07665030091b07842040c043c2d07000b941c049000030b9000c1040c4180100001d118917031156405103c080c105103c000440701c15010201000800e94208000e4207940c2030496a207070160031a00ca00e080400794540c65402580141da026400b80d400e2004205d100a1030504503195940d60b81020100358200c0d00348076225010b0000020341040c50410003100303100b01589202035440307083c3d40305940756450321902d4150f02028802c2001e0108280003035000940d01c80d101c10b50000b00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 502659235 1250 502657985 502658017
    0x106091503110315040507050405030a24060303050703021b060901031a030609280302190606030204050f1f08060601030c0309020415080708010b011e0509030a1b0801090206090402 79
    0x36030700b0020b10507402580c4504404205040048140c00c1c6802216808030302c9040c00f070708007854a00841d07141c404020004001c8182c0b00c5205d01d0122107104000001c501c000010030003540c503480c0c003070082c0c0e020031800c0d809485108081d0795940005801c010401e02c01611145c01c0545000c010b40103408004488417400c042d040095058ad102086013500c51101c480003003000c1e05880c03001c000c40d5601c03180c1111200348440d0f100310101c3d8002498141070003821282d003416a03034500f0410010100c40d04001d60007410b04040c481c8132400302a0060080014000e4828031441e00c0350707441d00c1848a4802e0ba03c01d60011000243e8070340c040e90081c0010401400c000c0f595200c1030340000e00700d940e1104000c2840c00421001d000c441c00410549000d0042d000c0204103203644000003900303040250382c50100024142024029032071240e070a13075a000c980079040700c045099500d441c5081c007818020351803a00320401000100d00c101409840a2703a500501040d182244150901c0041d5000340701044071612 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 502660485 1250 502659235 502659251
    0x1080702010236120a0212030d0c050414010f080601030b0406030602030c0711031b09130503030708040201020c0a0f05040902240306030c0114031906090905240106091503 75
    0x100412044040b4485140f42d04201d0b280f00800000d00a182401e5401018000b08440364080c00140e04141290104c1780980a60303c0060124918803650701134040840c100429030765200c0d0040060010785284c50b42d404c016010340001100c40640c40040c0ca0700103462100030a07619406540f105018440140010803030b2901c0361110f03800d036402035800300c694900c0001c0307800c1800190340d0b100c3c0300fa4000b10301034850301480c800b046040450008459104004001c04140d0700c5910014203840550302070b094036202d03e0015009069403004907002e0f0b0160081c0d0890305070702c2c9003001005080d5032010031460001c1c0e003008281b0000b0444540b00302c0c2c1081200344c4006030381400121a04944c00c200e07507080e65902e001800d050800c42c400311001d06000c40400e05690a18038002903130340c0895400318805103416003910103000350030340760310601e5081d00d061003034801c6c00008680d440d04022a40c6e0080311030000c030741e41e05286900920170f41c0000740b2141c03810720a00c1881598580da001c801e14011030020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 502661735 1250 502660485 502660507
    0xb16021b0a0b0726040f03060e030706090302010b01080a05090706050310080f06041403030f1f03061a0a080c0102030a121104090902031c020d050d18080408070803090f010807020102 80
    0x35010283c2640c00c011102010395401002c1c41d20300305005400c00c10541000e03d04020681034481a001c0180556220f0980d6018a9070030401d0b20f00f2036410071010f0210701e03200d0a019000704801088540001c1c0c010b800030b2280d156600a0038000c003140c5004160b11440c005089a5541000d0101286540129000501c002e0108042c81400010b030020308a1070a1520b00181140c4c04642504000d8100344204061720001800050f400001500c4520101c0780f4040b003440710b800c15400c001c24942c9068000c6207925140a01003040700d405460080d64203850300415030340c1e22108403110b030042e171040100792001032007603c0c1131051840c02c60000c1080d403404c503441211504a60440d01d0140e070b81384482001d600d41000240303100090303501030500e00e00c05000c00a48a215130304030320051080000b02401140c0441d4807285030fa102110080007082050b28000100d13038058070034031650703104081000c1890308020084503002c18004082420021600f801559800c1c0d00810581c195517003070050f8501e00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 502662985 1250 502661735 502661737
    0x803160c020a060f0912320d050316020a0c1a07140c011b030906080903090402030f0612071d0c270a0f060806060d0207140a0b16021b0a0b 61
    0x500b0f81e070745800c1c0d4868280400103100e0102036010031481d01c102d44407000421039943c0a592400343c04562001c0440240300d02164010007220b01b03101c1e40c13055501e22100c0a0307111011350f005074102552800d6103401402c0890b41c9030000b050140001c2e42210342001040300390220501405600115a4246078640d1507401c4000d01300307071045690350880d2070b4514442d81d100b1440d0b08a00c00503800411a81c56544004007003003018010350b82403051420224101c40301c10425103c00e07840081c010756503890603a031641400d91058441d01e00621000c0080f0306840c0c80841c01c001629030204482d000c220143c4141301c0110409401d100c4891002c02021041c035905465150440f42d0a49407490005800000d10040c114580e2000030070240800b4140011a80280c0c510341203002201c0c0251150142407202c0b0080c85040e0000f400c0500c0800d441ca030540c00401c41c10070b00e5002c0e00100e2200d540b100b9404c1304031113031110940b0058001101da12222110341600b0040d00310040d01040c03000d520b80e1240002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 502664235 1250 502662985 502662989
    0x11b021806012d091508070e01030e0d05070c090e060411011715190b04120204140f090106121113112205040b011407030507020607150b0405040803160c020a 69
    0x540e100f0081141502d42008001c40180101703403030003280941340580209400c002500c2c41c1d080041d050075040203070f8400c1d00205031802c154400e80e509448035020241240d401a00c0407202400601e000013100a0305100320642c0c072605d10041c100b06e0355642c0c0c2c0c0704a40700c80c20500303c0c1805005005c04132a1003146242ca0700ca80c9150b81c1200300309c840001048901100310301c8044201e02c0d98802800064050f000b5101250507017096450061342910006028101d150192100c540d10481004803403103c0c400001d0080b403203000200009600e4100c90400c0c0c03500440e01421400001da040106402c04002862448150b03050010398036490701c0d503146141e030040b820304049811030100d00b95180031402701c100c002c05040300d0800c500c086000001c2c10101c620b000381403042401003100414580504101d4548035801050265039560520b042100e441e405106140305524110f0300300c2040c03e00c0c1c031425004641121050341507a4441e441da07004001c522042c035041113005500c10006844207080100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 502665485 1250 502664235 502664297
    0x319020706140f090601060e0d05150c03011805060a051201020d0c051b01060806041217040501091101020d0e1009052106061903030f141206011b02180601 68
    0x71400c20314814080e150011303060008a0b0003d0700100512600001d070204200310544018002d8130710ba050041c10000d140c8034000412489108002204100030002c0d81620241858607180e609840c9950049507000c9842582042802c07606000314074140b040920b46401400015240c10720140660b41a90780140c4503501081010461003040715610005134010030b06180200300c4240340c0085103070744540c0070f00302803c000354201d001290b0078030071001e11032041d945d03880b1103c10303080a11741580242040001130301c80c4040ba180003401c0d5880030580c00c499900036520085690840020043e003ca407600da18014440f1984000909448401c5520041da2400b80001d0b0a0440f0541541c20090000c9c07189100341135454061160440e15601001665014541074401041851040e40d000e05080a200910103021501c1444003580c54204d520625003030740c4441181c8024140c030758540c440401d00070f511201c0310080c01c40705e03074032055510b0788001e0526060b041c11607249003107003155140ca0303c104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 502666735 1250 502665485 502665521
    0x2060c1005060f04020c070905040219030804180209060304031818020d0b061c020a0c0c1203030e0105150d05011104150224070c020f090a06060806030703080319020706 74
    0x1010615140f20b050f03404103003c1d50254507040030300070300035210005c6008003844c140e610b1004c40c0654035101001058481001c42e1003508586178141a40c454201e441040d1100701598004002e03e0120b000b55961000003400341815500c0350750341607030040b840b030f0504501030403201c000198029815004010206541c64016a02e101c10108013040c0c49540e0200c03402410100003950400109001d2408d00070021240181c46903800c600885810001b546d01034100350115501180c0e17441156480381e85180329850400030824421005402d881b8100c41180240d4112414a103403400d02064a60900c4d1040b00006071442e4024100b034900c0c1c00c81d420003207a5501e405d2080c800300790100514210710503218001e80078400090450007001b440240900300b0442004694011515450103103405040024101c064a14003402038100511040c89118001448200800c103d400e000c85c0c1e0344156604a101285035a4038181010100f0f0702d4000780d1400e45074200080000701e41c0398400c415140740c54207950 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 502667985 1250 502666735 502666741
    0x150f061c06140301140105010e01120e030d02030718030c1703160302070510080114061b100b10090806040605060a12060609111c0506010c1407050307230d02060c1005 73
    0x81401c440103030540318545d040d00c100511407aa0040701d072402c080c509280002519141e0301d102d07005171850b108456543d100c0072915800c40c2010360040c5110301c034903a96043d1585c03510014610410028070000e4000034034164107220a5450f150404901140601100d15002e801b0b01503082000c02400c065005130840c19042c805c170702e880744010280303a003940740006071541400000100d0840c441c08540c45040c00203038030018078101042d0109807c9045003950403409084c00e4601c003401307442440d10b102d0100041d5109a2500405600c802c0e9140e2034010030043e81d6555400e001401c001c1c0c0015800a0007480014000480b022003030b541b40c0c0700c0c4601040751458240620250342c249032049088800512031200064480c0c1542e400c40700705c0340300200b0151600001a01e000080d0200034040d1896070001000f1010300042c004112241038013214403455a0b203960710b461807010407207000500310701e0035550001d2902403c00421140018425440c11030407503003061501072442c401100c216203807020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 502669235 1250 502667985 502667989
    0x23010f0317040e07120902040507080405010e1504021309020907030f0b0105040b120a15030f1716140c2106150a0509040804080304060503010e150f061c0614 69
    0x9019080e24100c00228240780c10168244030380e0700020204130030811641a100c0c4031190603040640e01c0c5802038001c000c942030600b0010020b20044509523119802c1c071581c4044940001040f0092111520380074505840d0744d42000349404180c0440146035880c0e00e0100b025a48165506000e5080e5840c0040d900c40b00c21102c80960701e580700d078907051240034041004400041c408845641120042508559941002c4040180308501852149120000c004170811114010705410302c0c0c06810180748402e036500c440300d0140b0800c181c0c5200c5001c6100c60b040050003488442010309008000d6406041200c0041200300200f80c00c80c5946020124100700a40014044c3c19000000e54001c0084000315101107090002d070f52055900852040c1c00150602400e0010790b0064041c40099036942d03a52414000c040781c02c280075540c071408a41c80480c0c1040d8600d50440348440014100d4000e40d540d0340300700402e58010204d080300d42074034008403080c45041c911808015004015070030800c3c030000f40c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 502670485 1250 502669235 502669253
    0xa0905041d060c190c08030109051906171204030816050c040c080f1003032a02040c080702150f0a0504020d02040920010201140a0c110102072d030c0623010f03 70
    0x141031014094003203d0311700442c1419007101d044d500100400b14082d1605d100c988880817001050f8440f01d441c0441c0070481d22440f614030400146801c04480241c112481449500d1260388402030504104001070344002c0c4030310011140d510b0260307007640e1000103040c0c0424151228154080009002c200410800c076140c07001e9941c0040c000c0b00c054030081d055075006420780028440d890f02e444510204d00e0716805180f00446003503a03001d8802d2116000080014105050a44040016016a00400c1f1100e10040c8149100d240035014080322525007468580040102070000d80e08401e4076030042c0003507211030080d42e03401c42c814440c0002050541080d0030240c2c1c0000896030459050181014800504001c0d054225001100001d100c0781c002d003058941050400d9005407030350012550400740030020048015004000c444201e80d100e003400c4007040a4080303a4014080348031800398030302195240c1e03c100d15400300d410710703402c0c0c14015404541d01e001003640200503040d2005e0003801000650b003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 502671735 1250 502670485 502670527
    0x120702010f1413150c022808030705030408070608090a02061e07050c0307150801032a06080703110703020303070c15090c1a030402010906050903152a0a0905041d060c 73
    0x100d1701c1d501c0405e569000a03c0c558501c0c980094402c20320004040c54522941d01500511208040780c0d80d90b0304c58581b141d00d9070010300c1070282e14001c0d14000107075103001c1d000403880344050310090840300c4502d40c200240b6400c40f014054195400c881d4589103080450000c1070840e00030401013a0b10b401400030186440307401e41082c002d1001d0015040b0302203410609a90640b503020000750f202501d4115103000114204120441d9100303c2c90002400a80056005020310080e07a402d01910050002c0f1a000d032091600040c01070344108000b4281c1481490941f10403445000c440380c0d804440c40b941400c2e100000e4040d25062003c043c100a200e4109155001702d00c400c0a030700c0c0c19803600f900060000c850301e01c15a0140107000400e01d0341581e080c0211202e0040b03902c002521410301242c445410554000d2100c41b80c44520b0085c684800c1000c2501c0f103104071552618203060521040c88050700d200d0303d11171035160b03120030141c07001340040c0405c500ca074000c040090344440e00e0f415000741c001484 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 502672985 1250 502671735 502671737
    0x409020a1e0c140c1c020301110f030406060e1b09010201090c06120b040b0a0509070e0916080702060c090103021b03041e141309030216060e040e120702010f141315 72
    0x41590013140e844814001040ca800802201c03091009800841c0c007505401c103012609810002d15019a43e14800207035009274010072080169540703c140e220421102503941c440211131f22510405514a4240244038903c1d041c030000c10060642d64500c1500300d0300381c1003040800c1e035114400d462034115120300f1702c1125003158203102150f580000b1800f01405d0740901030044400c0400100600c1c083d01c0b00200a40c0c01070308080b41c5180c050681c1d140b455414810f500001c070068041a04140f0000d041405000c0100f442858030f80c926005400940c850103d440000050b2804050610380c18000b4000419001d2002e0440c0b030318140b48607441c0d4083d5009146140d10b580d00d0900544c9031303d044038101d070900140c0050303144142c0c1426031030100030042e0802c1200c2c00040201c0c80c590721000348011160306540a000484918031000d40302c00b01c000014101c4803042c00041d000d0740c0b2038071000c01c200840f810214034150995a1004181d071100700e00b1176084081000c200060010004284101012 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 502674235 1250 502672985 502672993
    0x7030f020f04150917061509061f020a0f0c08061006050901031104080f0705090703180b04060e0607020319090303120f06050a0306150602120409020a1e0c14 69
    0x284181d521081c040e50003032200740600c0d00004944140a8500c84002d014202500e11a4030459211155108011554210071b5003052240007400c0c18290502402090024006107150307100e0042c803088407480b06100c108511a13801e008010a05a86c0c00300101c1d4010000e01c0e481c2c608050450749400400b8040101e4407800c840c081103525440000e40c3c80c0200f0910700800e10000c481403a6000303016903044580e55000b01d00b000c40c0c1940002804008540007900c007016513903680c01080d0101c40c00f0400318002c840032281c02200049c0401a0f01e68400d10400f4002000c80c00c005800d86018002c940807405039000203490700801c0380e0710602d07482d410b9051500a407183e0450b0f4000300140002d404009050342c41c2c000c000c19211103508490007901d006884101e06a5503070420344041c01904080308200b00a18401003605480824624800041902d41380c1c58207180c848610000d41c00319201c041086020305074200c0704019850840c1e0340038200d5840c2034241c003403410403260329003004003195041c1d84 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 502675485 1250 502674235 502674247
    0x307080a081c0902100807021b03070b030402031006031a01050619050c0a060f230c1c0204050d0b040605091c030b12070617131707110d0b07030f02 65
    0x11900100c8100100c8a11400100c40440e1902c8019100c1d5201c029030003140d1810380e1446641c00408288111a65400c0f146000000e11031054190100340d555601900440c8040c00b0b147c85000c000c54000b0f01c040c040318070102000c40e105084480a4000700ca51115110700d1f42c03100c8000006043c090401185c3e090b152022141090610b090b0483d070030740c1030010100703000c056088180051400660001d1081c0030150b8150400401001229140c4103040c99903045503001d9445111440c1c418580c0708400c6260180b542c100303010842e0ba1001d400d0071190204000b00309a1240e180c1c20ac20135201c1c9a80708918106031070440140c0704020b0a5420580c0030f052990101d96004441480c241c225040000e0018080c0020071601380f50140030f080c480c4243c0c00c0000e0842c7d80016003010460128504180c10b07110030b0100b01c908410385101415224041c0741c1c0000c0807000000802c034552080040e001c03141700c1c4901041242d00b00103020b07101c00594904004d404c94060085458007929aa02145840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 502676735 1250 502675485 502675493
    0x3060a0602162303060c09040c0507051b120a150e0109020f0f040207240c180905180607020f010b0301060b0d2304080405040b04050f0a090c0b07030207050307080a 72
    0x190702e9100b4a4100d16102d0f2003680460350380c080c0c40320100d002030107440062508440c0c1c0341d00d81d441451114080c919016078180d22a1040007542d25065003c40170300980c51503441c038180c01c0340360741c140968810700074403804062150410114840714451000141c03011050030080d8100d800500e0240c2159040503c42401a5180700c040c0358020300031118550880c1303001d00890001d01841d280200841c1e4405101c80e505070560806440100c02e0070010301004240f460b04803290744840c0440c102102c9600803d000c4079420350041c59010038011036480c00b60580c01006440c0800685150780036030800e00e01c01c0c034069800e00036260350007000c0d0006d00c40145844d170503081502c24682c11410032a55070104190442c001e200708940107070002c825410504080c10082000d602034440ca6102e50714160031814241070a0080902c240000c1c0783d03115880d602c680000c0050b150001007155200c11401000c900c0c22466005031802e03a00a0703008007542070810742458903100c01500042007950241a01c80006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 502677985 1250 502676735 502676773
    0xb040504080a0c110604061106010504110a14070c0311011707091206020904050f0f0f0c0406050c011b170108010212040807050a150504050d080106140f0d0603060203060a0602 77
    0x2042c440c504158044501d06254082e1128010090380c02000007a0026a041d4030158111385843e1103416100540d0742c0d00100000c450000005007080300040c810404454011040c3c801300d128408041840c00e00c17581d466030074043c41508100c40c1b07130500007454106c55074040c00000300c82441d41240755042c00c1000d806401120742d4420300030414001484401004170b190146d035440500030b4010300241c140300580705900d010480b1101c82a400b640006001d80780e030b803070f2500e00079140100424a40390401004070780c180d120011b00036040d074a5682c2c1c240449241e84082d00d07100c540c0d40e11850446041e10b514011507034103a001e505242e0051203070000f486541d12409412641c00300b0785070780d614103d1400720b003050306489014008820000d000d485016940d000144958801d209542c0b042042000a1341c00f10b20a0040c500052600c10880c8080107481c8000c00d005075400c464181800c0c0130b810b003142595580e0304102d802d1034021040c0113260600d810114082c0c01c460020340100c40e20a0108105 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 502679235 1250 502677985 502677997
    0x11b11160b0708120f010626010b1b0d030203070212030108070b09031606020a02012d0302030c0c0303130302011401031a0c0d0e0a02010207050a030b0a0c1e02010b0102010b04050408 80
    0x78103400240000420404104880f800d580d0800c0b0000146410558000c040d5024030441000c10200c0394500550104080001b1080c000c40036000e280307900b800185680d40d0070412100d6601102c2d405600d54111040000c03500404c0c580c0c0e40560780340389c0008000d04084407029411007485062005000001000c91f440e0143c2d03000102060700c420f0302c800083d14003001c608111180f00b0b002c0c81d0100e041c0d680400d020300c0e024000c0c1c903240c60220034243c2a401c0500c010845501404058409900e1184290010364000c1c0d40661200d00300ba8500c160303641103500507620400510341000d5075008054082c040c00100490202d07803082c00398515150b07860711860101861101c41c0d481d00005644c540340030b0640c2c0e800c200401c01045000c3c0004e058a40d200711440c0164050f00c03d400d00041e0130b2400c4404482500e6002104000a8449130f0100020b8002c11103c4c1c42440002c5424030746078114940c841204800f07a900106030314441e20000780c2100c00403820b050207182088104800700d0508011204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 502680485 1250 502679235 502679249
    0x30406020c151c0906110a05120903190c1709010828021c1104081b04061707090c080c12040c03240b092214011b1116 52
    0x1140e80c0300240203640c0c0329180100f4040e41103007640c0009151940e02240203248124030400480348a00c81c1e418050142c0301e0320303100181e401c0181000b403a12440d451900904444212401d0142c0440c510181c082003000e2800003840a80e854001e11180f91520700016034400866440e000c0c080e40000d1454400811800100c5005071003041400ca100c89200c8503074a4030482192900003001740130480c8202c4c8011080c10904004011044610b03d400b25021644002c0c000c001d000c04c001100807501800c094031540c0255900e5001400103903109501c0c040c161042c000d00500f6081200d010f00b11000300740300008000d1306908001c8246200c8044511116aa2041034071942c0c6610b003d10250219070001449a02180120102100b074a210750380e0078003609070305014a0241500f44641c0303500480d00500e1190380e484050181d40c2d40002078104c11070050b81c012080d003402c500035500b501e081495032440e41624020801b283c0d54468110440c4002c418050b000c5989411051004040c00780980e00b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 502681735 1250 502680485 502680499
    0x2062202011407051204031103070509062404060f0801060207030b0609220c0617040206120c070602120103020f090714090d150b011808030f0307210e0f030406020c 72
    0x150000c070761040c0d6200d02d600004690b5007403c6408451110f4200c1e102c2203460b52010404c40508d40f07404038008040c0d0b0703000f51003500c0c1a80d800040201036000f8040041200404500602d10400840000c0c4050045034039800c1840b2903001000f407000005a00c6101190007506045c070005441c1c1e5501500300a086a03000020348610002d118080c0d008410580607500c1031b4054020007491700c6400e4100d032010f4558002c140e1000005001241c8100e400030361010081260400d000b814402c1035400c28070203c2005d0400b003c07580d03030343e0803030340600340001e05910f141004008501c1c2440b145104410140e9400500d41440349020b13003820120b0391284075003140460407864075100d4aa41140f0305400180780302c03611000f034018200401c100542c040c0080e0030140403e01d13100010442d6400c40f04078000551401210440c0c81c481030304043e240800300503030420100502814861a8126900d520400056140c40061100e150030001c0c00058441d80082c881004041d0300401d031240303140d409840c11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 502682985 1250 502681735 502681757
    0x51c0807031b0302070806090f03041e0b030703090b01050d050318010324030606150906030b01030f06030809120c010e15090d080309160b030109090204060302040c0f0206220201 78
    0x94841800402c0340c1c0810030b214038950b6082c10360000b40ca2080b143e001040d1152600c606130243c0c1c50b00c02074010588030398001c100400c01111211007400c00c0c3c801c120165250140c80d809401c03415441070350500f0000b170b2104051014400d40c4014035005000c200c03041002001c9031ba40e100d49038007480c5400c500c4412100c3d41700c600380e40290498144c0700c036001c40742011a91089102051000140010b0340c0e0146802070108007030000c01041181080b040d00e9010303402e403818004501601341509410304064980004030701c4a4114000d44c000f451141030b149403541907690070b2101d0228886410703443d96000000c840d0159800c1302c3c46802c510300541d100551807051001b04030075131149066064118501e840300006000e0786c0406503001300c000100b582c8000c105000b900c1014200380c012008201c80070001044607040e030707500607070100d44080c1012444a58070740019041703074010382425010a88a40e500a02240d05100c01ca502c0511019116284000aa00a40303900360f4000f00030b06224240e545 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 502684235 1250 502682985 502682987
    0x9241302031203011203170c1204030926160e01170705031204030c0605040608270a050c0a0501050c0303010909020303190315090504050d0806040608060406090c051c080703 76
    0x100b01d0650107010040d0781e0703503901e0072242641d425010081d0005070207004500e01d41e1030005103441c02150a140c0e968140803440d550703003400c20005082203080c490358a000250792046100020104103001d8082c81100c6541d84046040c00072600300ba00c05800790010510401c10b55020300e0781580c81c640030507207280300e000c4541c502e031039200c1d000107525101d090800e54948041000038016644142d48003a03401c5e0b0360341c3c419035542c0030394000c603408540f040000940100c420040041081044030f69000f14031241d404060400400e2141a80ea9800601c4140310a003042140c1100514007071a0240c0b5180444112503128041800307100f40d11a110f5260800355503041055415140c00c6000e11103600320000c2002e4014207143c1d400c0ae40b2203011520001e03448120b44641d512071500207020b050541148101110011001010b040d4400c0d9220000f04144400308011886a44905da0000e02120a4200608101401c1d40984d1050b6010740c00f440303130080ca14102c007002d1031340411940d84500c49494 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 502685485 1250 502684235 502684243
    0x130506010b0a120b09071b021e10050a020309040513120221090a140609151207030b011205190c08010e061f14251a070c0b0907080102120924130203 65
    0x65801615072041a820031040c1c0c9c500718800200f10f51400c1c04401c41c003400e880c58016000080c0160b0000d00441d002d6060940086500400041008503c071030182c1c3c91140708a080308860006a000548294003500105600ca805601c0840e407241424880d00c000b40030008030703000780015200182c1c5056003d07203c0005031003e07401300501601100401d070035200e902c1d4000c80710780008032110302d0208080078000d02c15012034030f4041c0d480c010701d20164481c01002c0c002c054484003a41440c45148690071304a44036800d4030003a80d540305541945050142e6041184c080c1c14a44607110310307408071100061108032000c20741c446060071142c070071004920131081d00412032601076500311240c0002040184c80600000a40700f800c0740c1420b000c00840381a8105400c80c0c007600400d03051440003000c200e0300300078280d220082c5802c44c2c4080c2d40300d0b22001c0c00da8000300b5081c0041c00b401c07000c3c05a0b04100f032090041d060300403250301031000446034044000c9140a4221142c00a01c26411810364034240 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 502686735 1250 502685485 502685537
    0x714010b0f040e1e03070611070b01030f03110607030c02120406090e0c070818010206070315122d050f121b010209090c040f140f09130506010b0a120b0907 68
    0x3490b40001c60741c154034050326030f070206c0700484299180003015680700d01c0c10826580f0007038004840030b2981c1e0850b954250540550f0109400b8046d0840c012551078104114440c845c0c221580c0c0402c40208051004e407130300003d0005003480400c14801485865031103920f00c8101d03804484000740d65120801d9249051007001c60280400380b00150f400317154082800c480390005001c0e8222510356844907402c90446a8440f000008100c00040411055030a0030019030341e070703014507102a240074059034903001403c4205022001d070100c04805409100f018000d03d900e0600031000f03003641540da86000e070420b205081036182c60303c80803802d070100c400c025810703202a0800540302400504280a016140341c101c2e00c01c2ca034280c030320020049000070030401d568a825501901148020b2103140802008000003451100c0c083c0d0785920b6500803500c1044944e000301218045565079001c0c1e618001d00d02801042e080003e1401c00781400381648881d2055507000007103281c08500700e00f8400f04200102541c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 502687985 1250 502686735 502686763
    0x1b12110415081f0602010501060f020f070b030702010b1309030e011106040b040c030501020304030221040b0322080703080702120306310f06051207051003230901020714010b0f040e 79
    0xb048002c04e82d59015403000303042e1281d54031842d205002c1c0c041c0c1240d5542c54090098010340150404009a11a07200596042091400046807031004000481c0c0f81803400100b0000080d22540b8803818140c11015240c5c665a0a00e030461008500c0c611071992210064401004049804005400c0c07203003030305d542c0010790350110080d035680c289424004e54880840f50206410b80d065681c140d0003003408811181128032104680d801d40d55142240c10f4480018950a04110440904800090790b400020030700a44661075902071410011002460300d08290050108240c04006000091761980342c6030705481015030842c620844c0003044031451403000c40140000d03034107049101218070040c1d007207103040d80c10a45844041612640002d9641c01030341c81029040709440c00c03078180031807007500490396445a2030021320f00212124130340c0e03002c020100d80001e01d80c0d40c00311b0341000300808a058603200303404101c001d12212601900042c040b18141c1d42c40c0784610f50701c0c80d24003484a01440b204181c4528 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 502689235 1250 502687985 502688041
    0x6050d031b052109030609031e03060307080f1b010c0b0c0306010c060f140c0a08060105031312090306050a0608030a2a050601081005130201030209041b1211041508 72
    0x40010101ea550041d44410f8882e0040c1d800241f0b000c0d00000590703400c0c0081f404018040d00d44203507090000c1c7d2000c2c100c9509070103008000f08404904020b025407034806900104010040305a0742c40142d03003405101410010142040710105200e041210f40004140d04915039a0716540c00507100804100001009d05013083d04411180080c0e501000740705201803150502d6039500c4034410054465040510007090781507001c140c6552041020315030240020384500a48505a240d114007041706000500019401740406d004200c0f0900607250001c4a01c4404d0001c0b9080c6001e00740c0740c1c02a50000d10810074041023800030078404540c0400035458024800c0001c03281401d1054941d4004d008146152040c8080901c00040c0c80c03041510451b031030702d100140c10400e6401100694007401c40d01780c0c080e0f11a6400450348117041000c044c6005070780c40e0090008000100903050380c1882d154403400050502041105200c1c940d0401480f82d10340c80e00901c1a924241321422001041c0581c13580ea4034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 502690485 1250 502689235 502689283
    0x3060b06071704060909270f14010204180b030706121d0a0b0601090e0c0f120a0504022d0d020301020f030705070209152101270606050d031b05 63
    0xc0700401002079035800c0d42c1762800c141e1120b188005841841e00700441c4403039104400c01c8464505440d0f440150702c1012100f0502400341c0300e04403040e08642078469541d40c0010204040505404490381903040054103024038110b241c006500c48030306100d500103020024075440c52408655000c4d60540032012001c00d04010700b543c0b610b94859407244111031002403c404503400f03600840500e4125045034005441315035174019050155080110702c0d240e07002081c49034a400149400020f0b20603103280000169501c4c050041220031000002843d1040104000300c1700c10800042d50644042d40c1907440c07803448055440464024403c0d01c2031001c011102105001d80140e100000b0700c0118000c89402d00181c6480000c240501c50440405903c1000c070100303099076800c0d141494a0f03010c8003000000e5500644d5400c40c0105030f640261514010750844250204017007407040e1000b811007520902d6507a007143e9400342065022200d00303800c4080c280251000c000d000c104c01c0c2e068000d00d045583d0024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 502691735 1250 502690485 502690523
    0x180a200a050909010b0705070311060d050f09102007020307030606030b1e06010801120c0305120c0f0303091e100218130c0f030f060503150f01081603060b0607 70
    0x2402c003102a81c4035414000c000a4401075080903500f0f000d80144c00f820000b45596a001007200040d00c1041d0001c50600c03c0700703032051161151038890703182d01e50018010300c2d003149800d0611011810580d03200f4500700c400c542d140107009404070301c44075040203180d540c030980c00040d00d016203980c402007085003412004000c01003203060b100d01901d01290301070b040d2000b01c4001d000104040301c4050000e40d031f00c0010806024120396403917100b80100c4000140395283c1d02d4007070802030110822070201500180c40816038a0070014030079100d42c4400a036065080864040b80c94501d6191840110905a07a11450070310040c80400e00c10014268115074440354000304010400304850014032481001910050a82d03050055000c1e4603800d42e1154200010001c2c15070081603041c2e60010307171a81d629404141614108044001c2d040d02ea46110401d1400600c83c1c0002081608103262541000716900c444c03400006102050726481000070032500250000b10b040c6000311000500014800710880d810300d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 502692985 1250 502691735 502691737
    0x801060602030903061608060f0f040501080102041703070b011203050c0706180803030415051f0e04061b0e0904110d03030f0c0c0201140313050d0305090c180a200a05 73
    0x100043d41503442583d10b86c07a0462800c40c100c0c803a40d002c15811400104140f42c02a00b00250850060500c540492040045170444000b40c100e04c1e4141c0d40010280104031b840e000061071541100001c51070202d56580e4008800818131030204c401054880301420140242c0948482e81500400c03188181e6540000400e400c040030503028114140c4800440c810402104491285402c200b88101001064a0120080c000100805502e0383e400c00c00300c0326261a04c3e0040c2c02050700358005c07001d50400d0308143c0c0c221141e603450032a0800351035500060540c2c00c140940481c800440c0c0200c081e594078100040401ca51014055012003070b02040002c054155103e0710f0a220700103010046450707040010f44888803c0800a400704540e030013543d2106000000440d03012103613a50000e02002f00365a454a807400d19065100840d40311400c0080710541006400f4003032108980882e496116443c84110451002d040420042e4480200321070333414018151510031101c0c00c1c40385940f503100807001411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 502694235 1250 502692985 502692997
    0xd020d021306030b100b1c0e010c0201050a0f06050d030305060402090409080715022d131d091203040f1106030108281101180b03040b4c080106060203 66
    0x3619104c6012450f03400200c00310405840450115624098000300441eaa601d403807042d03000104e031550441d0000031004e00a0035200c0a00307130000700b001c1c03c003c0d00c602c064500142500e0480d61800d103040103250746810340758444541504000983c0d03115074011502a00c102024aa00b140c2800401f10811402c040100b01c1382e40103000040844800304000d80036803013440c1645c1611400e10044501009002a41494440e11110f503e803400c6240f030403070781303103526550302142164a50520510388007034605080f0b80d0100c0032001604024581c080f45440301e000240001e062103200344c041504105c900e00d582109140010059900c0c2d40c2e5840d10140c2e501e08060420190181150585025058205021901c280e000348000903d2800e18011240d2004801c1d00490b030020b183c50000c4c0c40001440258050340c040c110710521440d04007007d49940719084100d0b007801c0d0840b01074148480410a4100341040313075042640400450208181180d13840382c120160b50b51230001c0002d06a9000030080c00303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 502695485 1250 502694235 502694243
    0x7030f030e150108190302120c010905072409030b040609060e0105392d040b09010318030903150b03030c03070203010c020a0c06180305151918020d020d02130603 71
    0x3246440c21802c0c1105c07140d41200041c0964004241c0b6805829054054121990310314000103940150307032116490407100d80d01c40d145101460519100c2024a0110342070400c8135404d060002c070345160307204000700760010000381100c8d650745c0f00c000c200301035500402036050100c0c001340201d08141e00e0007008001040045540f035000022211000d030101000c0a8190b0300ca9012603052502a00880346118034500707010200010024805007801480006007020304881140b141d1101004400501140c0550380d40316800c00300c4c000100d000aa00071120030640e82d00c0b03202088840c8a43c0c8460024001800000e0750500001c41c1d00078040c6070010103001000c0c0214028084104213020130381c1c039114202400b03440c00b41c0b05441406028000c40840c40080c0c015100346c1291540c2e500c0f85800d0a4000045201c1c0700102004d204002502002e01c000200382e4520400c60040c3e44050001d1101c0340000007030155a6001a0401b555115802d0020158001e081c00d1074007a50030b09a0001405640412a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 502696735 1250 502695485 502695493
    0xf140a0506030f030714030c060705041508090a03030c02010f1a032e150f030303090302120310060e030c0d0f050f0309010512270c041d0307030f030e150108 69
    0x70124900001c150010010702c40c0070b1450200d5948032595807910200c1041d50611082040c1da00104040185070f02c90348581d5a1251141c0c1410861b0355240f040c50350140800ca8001c06100369600045810f000d400c1d410300780011400401e10050b40500314003e0410038a51800480c14444803044100b40d84201d812400d40b0080803100c0941c5142d02a000030007045c03480c14101c8c0342c01d450040d90040c82ca5035101001155490341e5011280b08004807078000f100029105c82541c010142c04104130026a280304c07181a00f145003112407404501d107a0f01ca60020400700100000741070310180030301c4600410180c2800805042400c4ca041c113043c0e21202102c90340f0a05040c044d5015002c401c0d079013810380580d0b0702480c1c0080c0100300d507031103000074200c2145071900c04100c1c032484244583e505d214803410009059034918080030002110f8a100d600c04189209160340700e101d00000c002c9802c016450b0400e500c840d080b504044000340301218101c074503841000701e09a07065211a42950480700044115 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 502697841 1106 502696735 502696741
    0x30906040b0a0e0f03062a040b07151413080c0a03230306130e0708030f07021509100815090f070206181207060f140a05 53
    0x41078001e000011619103581d0002d012000c040d20840c1c4c8113001c45100d0f00803c2c0c0700d5a008020324020b5000c0035117085034044a00707200300c3c17020302c3c4850b0316261615942442015132150340280e407040740c400c0e08111990308601031007100c514049121003080e214081d150842d42064481140c00003800c0c401411149804c001c84130a041c0680c1c5ea510301519114000a1582982c406012162900304200441c0c2c0c0c0301d4812440c024407c5103c00503c10364220212414107941c0d4205d030916010000e5492440c0900c10054403034507008032029003901080d464072202e41d1040c0c0d010282c00040e1040a11000c500034401d440d402000104010481c22240c0c00140c418203044403220314450000040c40f00c440c5c1e04001d0180d0000c004000c2c50518480340800540d65035802c81070018109002507518100300b03150b0000859030040c0c000074014030b418800d003079031740c8403084899600f0f440c85c3c01c0c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 502517985 502697841 := by
  have h0 := BRFrame.cov_init 502517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 502517985 ≤ n) (h2 : n < 502697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
