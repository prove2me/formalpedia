-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4972
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:19:33.09269+00:00
-- url     : https://prove2.me/submissions/729a135f-10f0-40d1-8dd5-10144a29c31a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 894064748 ≤ n < 894244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 894065998 1250 894064748 894064771
    0x80309010903022a0d05030f072001030e1002030402010314070c02090a0b0a0635010314030a1704050a020405150a0e13030c050c04050c09090708011404020f070209 72
    0x200306103402413400324070b041d100404521031104038405011031110001d40840840c0c0d038072030200c02802c2ca42c0c15480307840c11003580c007040054184100400b044080400302002c402c0541d80d240e5030f00056040d5a01040b04c844203804c800404410b0303852982c0515005030041c9800503128040041054440744281d8180000c900518158000c510344498160f5021200d040180848100b5070041100c42810740200c50a00603c0b10406100360000c2c0d50900018100e007020518100d180a5100c03003001082c0820341d030309911003518082000c000001c0b1081d0448555540140800b550100c1c402d245003c0e108842501402c0180030250b52a801654020900050081210240c420400842c0c0c4520b80c0200314a080c01000c01c0721100d9249504404280c06040010700598146089800e22060341065035000e4644428040340e081000081c4c040500c080e2141d403495114084199034150007407080556504581024400608280d005090090031000f2240c6c10036035a6400a07642800480d890300b07244 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 894067248 1250 894065998 894066011
    0x15050717030a0c11120a0c0209041101090b0315120a02040507080613150b031801090305130915150c081b01060e01060c0b182b031514030a08030901 65
    0x1100c107108841d90010300381000001c01ca9804150394a905e20140000c12030b06000c10b143c10228000d00c89141e4141c2e00510000061801d880d00c0e10302d020760008040d00140250b14007040c100101d40460703000e20a0394802c4d4600300501000c02c9020701d186040d0b680907000d06c950b01401170b01e0b2809441d0050b81107071075860701450030906004942041d0a0030480590031700c150f0030180702c082540079040c1e48820890380d9583e07072094144c62044520b040d0103201c0350f203816020001e159004003c1c014002054421200e143c1d5030b80c61710740c2581c60407010600100888a0100840e00741210700c085403c0d5075041035200001c2584881c01d45402c103071621fa004039032040d8501b550b92402e1140201411103084901e400b5414041c004058010000d40102141c40c00b0b00440c0c4141401c410060800454604130f445000b159801c8070b20110301c40c9041814120410360415825029004513404070020080d6602103a15240001c0e480c0303076601c000c482d018043c00e074502c00420704000c000e51180d00b8030340010914 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 894068498 1250 894067248 894067261
    0x4080c1c080907030b01090906230901110304021f090b04080c040e0106061202070206071203020d050a05070f0507080906070f05070f03020d02090a060b0a020a0219060203041505071703 81
    0x700d40005018000a4202080a00000300c05200e031030f041d104652400504494140741800003000304001e0520701c24900c1b125480c0340c030380c01000148030303603940d000138809007801200b030a40f14041610002d601508032210410505512600108208114a000c405041c2d503003070f10843e5a4455003103036440360010b5450700d505091a000c0e51841e001c0b00350003003040c0c07807400c08014588015005200781c0a500010707d24250350f1480700344c4e1511038001c0c0d100640d902c04d0400140c001e501818a07581900d0070b01d40081e0221041d80b003064414415500c41120440100800701d46a40c003072002140c0899090202d030075140ca5150181c80468810300070400102c4050802a02c3c00c40294443c10314040b40340301c14070042c0c0311030142c001210fa055038560303496101c5600041c007824080c7c0040166090102d40b20b4410f6500092004143e4029a103e80800940103060070003000540980f2025900411040000311150402c0000c00718040c90300909040003030391500c01180b41d65501d203100c007401005101c1d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 894069748 1250 894068498 894068507
    0x3160e1905090906070f0f12020a0c1505010302060d0b06160b01030525060f02100c05090a1d180f0307050601030b010801051e06031510240c0b04080c1c 67
    0x400405050044c00c261a0074100103203041c04481c000390400000150030131441d401400804070388000c200043d901c170000c1080082c4542c0d103000d015030b0000b5203a00600c9003034200380315440c10780b134020302854507001005035598050304901b000c0359003246041114440114040c2c40b415020b41c4215480c1c04954510306060f032030417007a00d074025881d0b4880a5150310400f50325690100f140c00c91308102c42c00c814400020390806203614003902c0d280d400c100c40000714aa00c080100200c000885400c0e280d161506030440c0081900c5100140300200e4202040385440c0b007841e00c101700140c0c141121140001c840041d815034119000890345a40a0b0700103000f040b8100e0101805001c0b103000030002c619001074500c80364408079a00384075144024020842c01c1e10140000b540e030f5202ca088001060420f003060b500385407054401e02c031182c0c3c003689445c100c07011020103104e5a11401d03650004508030340d440b081e90006010f0002c5a07160b108012070380101e1014045801202c003600031810000c2e00c240f8000c1c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 894070998 1250 894069748 894069751
    0x10516080c0f0d020a2405150a090204080a0b06030106170d021b18070e12030d050601020c01081f03020418030f080c1b0f0304080304030c0509040803160e190509 71
    0x82c1e1a00045400d444499000500003541504001c1181d074072031100d0752412000d90004101c00c039040c1400300300300b4000038503105444200410350b0780f221305582c2c0d02d1641e001c0b402076001c5e022403a0003207594000480d1550b140700350030010080c000240f89a0310140b186000c481c5107080d5020783c00044c0030007403194042c0a20408540070006010b80707080c0300300024801488080d000300c00c80201c100403581c10340c0b0032440780140d07030005032000c3c514041000c4200e07529085213445450050414000511551000c42c1080040700c040e140d0b501c2c141c4411202d0b40d04401e82e20715480780c0192a0b800040565107030300850f81d080c5c54807a070710b10303034038105090041800030b84001441c2030111203010711503d800307094101d4941c0c03840c9050426101503d8408107080207034254200c5014800410040b038401c00c040000d02c122445105008070b515a0380301800442c800031030300135040010900000300c0c040c0181c0e000c589600f4aa2800660036010311000a10b21030000400301c1e1301d11617404042c8424100300101a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 894072248 1250 894070998 894071023
    0x12090e1939090b0f0a030c180b070204052a0706140a0b041808091002070312080f01080604030e06030910063809010c020303070f0308270601060e010516080c 69
    0x83c075015042420300031910032034120705d0800da40c81a0f2076220a200d214031445112548000c554000c3e510303040c042d03d80c1c0210300141d2250b0f1070180421340043d10219a080e6180300c00d8001f1111204981040703000d908190416565940c4071121070300b8004544804500c1003828074000aa80302103507041c007044607001c05140340c1c064501a508000f1410300c0c01540c0c1074800071200c40300c0202c49800200e00304061980014002c00548250044968002c6030036032103040b8150520740d143e80c0c7e4110f040c1d59503601b5100a004102d80c04070744000b0341003002c0115030028150049400b0b00071101703191000c440182d4089012941c86100714100300c15442801c13440d00d6400d1690b690030b4514002d440704a13219001295041c042a00c80450854500703005940e40c0c1e0341c1102d06818210b89504014111a1040b5050f00040c2c09171015113174011300114042010300744071001420b0684c2040004c4e2018103800ca08a4180301050019007d16202032440104082c441c440042e00c908064011a1070650f008401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 894073498 1250 894072248 894072269
    0x40309060c03080612010902040608010207110d120c11091e0a020a0e0f030a020319111c06051005060c010e0c060405063412090e193909 60
    0x40c00309600483d500e4018000302c5080040d11581e40e0841e004005c0b0070002904181040000542c0e16819400f4180141c014200703400d1507044507040082c5050b20600040c0a13000354140780b12942c3c42038443d200703407a1040d044810000e02c400c0004621079411039101805441d0b6a0803440c0c01480c650801c0d0300038034060815418001d440c00e000d450f03600688034030b07405100112640c1c0c3c0240d81c10400000b4403130b005000ea43d10b07000d00d01200d10719050035200c260364144082c0428145404c00310800d240c40746680407890040c00c00790b03a5090140002400c4e4025016054401241a699500050042c500c0e804000070382d040c02c001c51103003401554a001807180000388400c0282c3d0b1104400c445031651042820b08460810080e80c40041d11000e00318180ae000f140010070400c000c00c26060110000e94843c032584664452900c068002e04540b031824440f1210817041a01806401001d8491400f15000545450400b510803070100c1c42040209074408d6200419400740c0c0181d4654041d0150b042e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 894074748 1250 894073498 894073517
    0x5070e090d020d14040501050c01140c070507060f120902041b03060905060904050a0807030c0b0103060507020616020d0f09051305061203090f0d0201030216050105090c0415210501021204030906 85
    0x1300c5001c140034a20543d418000009551441c41c442035100d5038102031202010901400d240c8030091468015203021641c510900070007013000d9016500840d01c3c80c03050b5554a050701c121902201c003415a21074203c5e003040e00c810031807100000d800b00502008201d82d8001070304d5460500c0c0f0710152400606858000c0120600b8080451310100302d24146540200e180c0740d031400380c0e00c1d04980d4001302281c090001d00360240044101329164102500582480c2e0031200a9201e82c825141030f00c4051180c0b00260b4014270303080d5106070095500d461b24440c0c5080540c1c00030340e00e001240c04a468821070252042c0d0300d41c20000030f4901003042e03d5550510000071800c0800c80d4000c205580c1220b28894451030410b0036000440e0320a80490721810290411180442c071b01e032030420f018100984007811203018441c009600d6091920078400442107a0031072a84040c50301a88051421920004101000c1024039031400304109000034035505102002c2020545000c1c07c000b404503810350407410821001c0503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 894075998 1250 894074748 894074777
    0x301050319140f1f0b103903121503110402120c070204050702032b090503070309090b04140606090d2906010804030f081906091d01050702071205070e090d020d 70
    0x801c4c860111b18200302400003a0203070411503092401e20300242c480d190140c0c41280356140003081c4800c0d0b1094075003410101d01800319606070f031001c40301e0881c00440348600b0408601d00441d04007030341002070310061810554910001c1c1c0000115000d2000810003e1000118103151041c1588500c00b440654201000d2040200700c10110746081d101c0303511015051180789000e80d01040341070358400b00f107a54031070039031401616801c001e1081c4510103107801e0441d091410503000e0412141c03001c4660807903694903401000880e41046039a00e40000a0b03da1000c00503c40c41400301f014024a1840788602c0c0001001e40018140101390300c0c100610745042c040001d412145a44c40700794103080151780e682d40e184140402c1c04028080703002042c1041000500842d840e8048081c80107266281d0b408040c1c02144103003a22070503a000401030740100313401c0181c1c03448041c14000151240c029034010965400c013410209400b907803096030ba03400000e20390100c503404001c40075040c048e50401c0304a50403402c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 894077248 1250 894075998 894076009
    0x270804081902060a11150712050907050114070503040902040b04140409030905040b031f0c080a02040302032e020f090906010905150703050f030108030a020d050301050319140f1f0b 79
    0xc6013480207000c01c882140800440a010990340b03140e09042e000c64514220030010107507074400b1b02038443da0f40307807201082c44d540000c6038400949006031958040f120707035020000d03015405400261400d0109000215070020b03503000402c02011103141603500da60521445141e101e56652415100340d1500013502d001a030003060b0741c01102c00c12540020225410000f02c0d0a00149207131020051032a90038a000e406035542c000c8060000e95035444506941d1401800c0403485140406503242e40b1900340c86d2071188031203040c40b00d550004a11701c640008844012001c1c0d80044654a40004000c81c070000581402c004e9160b2181003460015141d5142c8408030b40c401010b10101c0c0d10129000460f80305050140c41210032200003811303801e59a43c1e68407030a07520b03a0803040c1150014050141d001902d18070850030351f4140c0d20014050000123500556140c0e20a02c4200101d45188900440d605080d2090080d440c03020306040c090584156a000c40c48070030282424804003151410400300043c3e100c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 894078498 1250 894077248 894077257
    0x3090501141606090807150e12090a151b06050402010e04092319060902210c01030c030e0a030e04110a0207050904060e07060f0206070809030d27080408190206 70
    0xc03e0700055003401030b04210660340300d9040090956441c40c44004201803541e80210381c0c080044003a12900c405d44c4103007072602c1c859410229840101200c0a00a0154410704004520f245041c103200081c0030780c19418003030348101e5013500e14036038550806c400d65801002c444801402240e041202da00e6030764610b2101d40520401e0702c580f000301c520500c4000070800c41e0010814144c00fa122a1310700074680140a005a280100e0082141503036103250401e41400309202408107a0140c40c41a10174801180103105c0c2e0041c0804068541c0c0d00d5402040050000c02d52440c002c1e9260b115540d0302d4020b00041d55082c0c144409062020401308c003450303602107101000e549041740c0c864000c0c1c5807030a2640140100488242d02c5000340440014825042145410601555000e943d20341d40c2e01c0a0035076807150304640100c0c40b6081081503e45110680d4800d0740a484d0100321001e1382c41d14400380402d001503054003207461540000e0305005150041000f00b045101201c10490448012303404606913026 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 894079748 1250 894078498 894078503
    0xf06060f060311070b1005120a02030c03010203040c0e09150f060108180a0602030a02090307060801060806100806061e0c01020901120c090b0304060b10082a16140a030905011416 78
    0xf10000815241c004a0306c0c1e100c01800d0007080521010031400c0220340319107000300201d100b4401d024084040303007018001c0d40e00c40c64000c000290403030700c3c02041c0601508002c004c0c08050040d140e031608608108030721140500c2c90009803440c10320785000050900c10b0003820740300b2881251802c1400591000072070f223074500d501c02005078480d1640020f20019008034216258103000d030362000f10300d556129070610f0488910703a446d4501034481c0300c04c2c02480707050101147c2c001a5424000b801c0c60500074000d01d503c610300415a8400a1000ca03200d21a0300691940c05a5940020303801d0351940c0d1144e46043c891648500800c281003120344080e006454a00c1000f07917070100413001800b408220340c402d8581600c0544031a0844400c8203004190074001c903401c552010044081a400355001065284031500b404419484c0c211a40f00400003400c06070001c94051403103a600d50000602070250b0384400f4440c3d240d0804440c28440003400c03006941e0340e5200d0f003900c18440b003818500c002c07114103046ca4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 894080998 1250 894079748 894079763
    0x308040902090604050a06020c1503010815040f1b14011713150608061008030702150f04031a0906011706010303030b01030e0d0e030f0705030a060e01090f06060f06031107 75
    0x240c6150100e43c150040740d201e41d601411610f0700003005900401d103400500b00803a140000280000a18401e43c0401e02030b00945501c140c1d04048418582c0081c250081c1c001c68490704119070f55503507403d80c0f03102110b803050103042c0082d08001240c1072120f10880020309082180381c0c00791461440716001c10041c9150400030014840d0824132150400380e00c050242c80b4414802c190315000d5070313540c981c0260f409043c0008041000190440c0203c2070381d110f160700030004012001590414141e40e0445862081d0211b0200302c0000090072414402809081e80485129036192950240b421b244059000d0740100345000d007501508403003c50014152641414009551803412004034005c00640402c0013142c8122980c64100c00c2e0010010b80c45407400310304075041d020602c49407548440c542c1c464107400d0f500000c02d940000e42c00340c1052800c95098000000d000d041503d8000c1c54404281040d81d045680d5441031202e90200c00d03c9001908103420240103525101482000b1841014000740201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 894082248 1250 894080998 894081007
    0x1c06060c2a0302030a3c06090c050a1d1509010312030f0606020c0f0102120a2a0b0a140105010e121006080f01150308040b0a0905130506090702070308040902 69
    0x10764800350400140d9006001c03545a0404d07454210144042e1501303582d981061800c802a4040b007090640316105802120f17000c8584450361081c0c0500343c008021151410542000708983e2141c08003400100114003a10240255800310180c594801600b191b0445040b004880f4854403901000d40c11640e0042e20001044103080003140103002401d1042c0b602c80c18600f001075076a6000070b02800034003088030386c0844112358800580c0d4a000784041256080b4050040540d07681c01a00c000c441d07041801c0c00c1c1d01200d1503805010b01031075001c030001c50300c8135000ca05100700f0b00300c148110300075425a41c401c0076403941840c0c0060f0142c0070200350b481c8120122143c4105001007400903540e40b2084c00d40501c58551030304156038507140320f43d110b80300540c40d2464114001113900c08000c00c40e0b03008100d075440e007414086810790b0b590100b0702050610030714682c00500d540320200080b02d24140d600000400c3c0c105081040f0030084c014025004540c00b031001800803403103036030440d000c840e014600182d85 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 894083498 1250 894082248 894082313
    0x1b06112d0a0807050906070f030e0907020d0509030304080303072f06040809011e050301230f040207021f08010e0606030423010e071205070f060516020607081c06060c 73
    0x9106411744a030b04288017180313200030000b0b00b04020003803038443c0e00d503201071150340c509200303520500300c41d9030300181e0103410740d0034115000340014a6901c401500f6645050786510340946140e1080c3c0301f14001a40108a242100e1411610ba00c01c604244104d40c291034a0036088940e1024080c1020b046480c0000b9140b205a000c3c0e05880280302001d1056860082c43c204058550b41007441881c0203020000411403505d80f11080760311a4000007440e5070110b0464400703000003508107003002c0780c0040d146441925181c2d0303403110444080e81c5a6842e98030799030401d03224003401c180280c000d80c010f240500611000400c488005109100507a0b003e1030b0301203920301014090038044e208078004d4050324401090030400e8408040c6841e01600403224003c5d070340c60f040c0d64040200c0c0301c0c6500281e0207000c056040151420f088120500007882d060510f00700341c403007011942c4010703081f050340c059042c88050606424020100100304a042c48030410a8607110303c6107120b10110011055442d19221051 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 894084748 1250 894083498 894083507
    0x30206090d020405160f030212040b060d0b09030a2c0103090c170307120c050a08030c0d0516030f06180b030120180a12031b06112d0a0807 61
    0x1c1c0250000d0091100303090074070b0301424811800300b00d000007407080c01e51565014000d008580a00c010126840d910f640d4039180c610f6a008090900c0d503018035481050008140d940707088902032401c800c05143c2d40c44034498050b1010305494011442010320822404105140048036240c0c130f107083c00d000c2204611464250001c0000b60050342c12804031901c00545001c1c00005009514461800901d001d50142e000703803072242800c0c0b40104598824621503002414402c060368000350706108442c14000082c40041c1a40c10440300b0381c4400d4400c01c220305240b0b506000d00c00344402000010044681000c0c55203a00500018000c1880c1e42c07211000045d81e01c095000c400d441c1a00c0c00c100500d02440703040f00c20181d00589049081404171b158a51040c2b4204210b402125010030030000300c1400d0f03603010340340030100041c07080280d9084a0810041816401000c0400d040380218036990040b031442004071010407089028139503119080548480e450404440c154103503810024036941e15182c0484 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 894085998 1250 894084748 894084769
    0x115090305030d09030e0306040f081809070f2d0c0206040909030c12140327100c022a2b0501141f06030e0316050c1504080703020609 59
    0x9046102c0054100e910315080e07400030148070f00c41c0c0c1c0c820910421900c01c02d0b5030b404013940c1c080d00340c6044801a0000905840092200c50842c003496041e4015003800150031030011100000840c2d0165900006c0a50010080c501c0c680d1216240c0c1c5821100380c0c08001001e010b04c0a1000d05c03024a05403425903030741d10159030041c00010000d002e001d10360301d4010400005440104c8990b481240101803c2d40240180c4c2080c1c10743c0000942181d894020f41801c00c007040c600100208411441c02e0980803090040f4802402d4070140800ca00d075240c0300007450b0208804540035050029a011004007145401c1c001d0b00d150200c5620b0084001c410140c41041912040e1045180e000e0510a0800406402480d540c04150070a880e40d541c1d03035421031845c0d015240c400040f603441c014050080c640243d00c02581154404100d07400d12a14004d0282c1c05401e48a080da220303404960403a04610341a0005028003400b14455810503251103020b80d9244124080248120780c0881d140c80355454021448 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 894087248 1250 894085998 894086003
    0xf061906170106090608070308070303180203100b030f010e1002030a1d010606020c0616060f18030818030901051219060603020a0305011410111203040b0f010e07050301150903 77
    0x74140d0120000060300810b0207116494402d0708000c80001c0f03407880410342508990b080800701d49807a116940441c002e01980c00a2403264124042080241c0c404000098548050b004006502e00005003018500022300300103450b50b81c18001605440ca4000c105510348c003400ca4405601c0c0c1c0c641002d20401b40c1100081c1080340503003c0c03000031132a0015008001201c5040e02691000b15402052007030324031410440140800c0f80403141c00015280794094004034400540002d045a6007407014500010601c005a000403626024070608000c09039442000d815100011407426080780000b80042c010042001d5510203001c000615001070408203440c03416100c24104070f07564540002238003d42080c10720304006840c2400100d41b9000b98284490445c000419800440f450502c00f250030707405070400e100e0b050141078140c850900241004d14044c40c0702e0341c2c503c40c8a14010703224100c000f00580c0030100c0c40d03108206000c043d6422008607415625801d20006010350b180c101940c0061030350303100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 894088498 1250 894087248 894087269
    0xb0a020c0906130c02160b03070e0d05072d0f1a0a2601091805030f0a0e21100216030c1112010510050303040f090213031b03030f020f061906 62
    0x8138003c0d16070108401c010001d481c0f8885160755201c034841d00b060300040b5280d00c04500d2446452a0500c0c004119003c16480f0b01d04a46100707407242d0b520b00026001c0000048180602e0300100c014191100079070010f8200b440305400c507580782544001c041a600420400706880000b0f194a54510805c9034240300003540000d00048610900c882c251803109201c1c0320800c51400926241740001014204022900040103500300703030200100b4007960740041410000c1c07107000300e07461103e03442d906264030700b02561403529925024000d80550424041e500c5600903e8030401221a105800c0c404001410750186010b082d060714a1419010319181c0f040320f103a10006e540480ca0400405401803885040e185464160b01030342d0300181542c1c0c0c040c5001741510301002520034810100ca0b980070300515045400c240c0f0300b1590341c1d150300000c0300382917005486440c00f440051041c107800c001e101c1c0965030144018251412800051520b803c000382c800c3e59a1000301c2c1d07101e2002026600218041c0865444 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 894089748 1250 894088498 894088511
    0x2090c091819061d06131d0a050607050a1e050c0a05070302101106010e060f0d03020604060b06090d02040e011b02010e0d02070605030121080409150b0a020c090613 72
    0x81e002040c1d032006004404541440e201080704d524400304107103010080080001c0f1511418200700c0205d000038425000c481e41c130f807075030b00c401c03800d4608030f60b21200d0304000341080012600380366040c0000205600c0600400f08508180d0592040000301c10a01108401054448814049480344a0b01c40d003401103105050045090050200c1d44104a034801c8540e41701c425101c00090301d44003c20340307a8130030342d03003148004000428064a003558084401800b80048030500300c0015020341131481c0542c0103030b001c0410402009118810b002040600b100c15038140280440011030300604e480000f03014540b503141c8480c50311025006900541c4030600c0d42144c84c00e100400074002c251800d200070040c41071303074084562940049620350585440c1e517911480d5a09207118040764030a802c070704801202d186280e50300400d00d000c0190014202100e004601d007080b4482c45010503215400001440c4000c001e8108481e800080b03d01a141040da692445a510040020300d220286087c540540741000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 894090998 1250 894089748 894089761
    0x370e0102030a0e011806050d1a030c0d0c0312110706090315090c0e090a02033f131502010c0e0a12031e0e130504020a121b061d0d02090c0918 62
    0x7c000c4c081c0340c0d80100c800c001c03104c0060001c00006a500080c55015003010b030710308200d810f001004104080c00f400841c24010b40d03d81d1001c40c29040011402e002030046240c9086a240500a820050044c1d282820800d03007180caa9000c1407150b03024581d000c6595003074940400c504100e80100a0103c000b1045051030841445030b10394690040c101d110340108102c20b09001d0690400301844500d003520411031003e400344065518003042c24100001009025400400b0f14405010300505460105460117010350500a0f084d6020320750280c050182c800c88240281c2c5034005007c04580750644080c00078051400c0607240200050003a0040c0005c0d0380c01800da6581103200251f004105440414030102d190022100321403050340c2c000d43c0402441010060760b40303500411040180036681c80c03100724a0515241800b01c010740e0004020510b6505e4500c03206ca810703014800d1000080d01c11014145c10b0b68000340e403026005060082c00303440400c0300461a25031035028582038002c19819070b194204a07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 894092248 1250 894090998 894091007
    0x714100b0f09150d02030a0b10060306141e0d0602040e09162103120f060f0603020c030409230103050c1e0303030402010c0602370e0102030a0e011806 66
    0x4005907008556508600c48107050528a080c802c121400d41e50343c00c0c01948040041c00121000183d0f8184100000000132030880103440d4000e0456000c0406083e10303020001d819581140d0160729041c0c1e03403400c0391955440d6080113410a020b19191503404e28100c00c00030700814900d4401400300e030310208010400c99683c90b500c0e401180b046d41110f01e00c120900001454204d0b9000b18001c82d02440224507a547c000124503a0051182c2000740360940202d0491007281c0c000c083d81c003240e40d124a410041c950b4159400806020189015850034020b83d4043d17a8900c9584100710a00e0303a20284142c00c1c4191500a501142da45520f07014256075034146652b640b900910f00c07a101e107284500740b441c0d4809030358040c12954030140c00785040d03696540055039880e89480d02030350342c10380030003c105005000d030100c10303040c2e640c001e40d00340c200014100b81d0301c0d20742c0703140410800c2c0889000444640e03a000405ea03040d80946107001160ba81c00d0381e004917007010025070341b0340308003035090030218129801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 894093498 1250 894092248 894092261
    0x1150b0408100b0f010c0303060b130f1205101806050a020714030f25051c091e210c0f1d010303022119031e1509111c1d0105010515071410 61
    0x224001c40320201d460b44d1400c00437014aa070001e240fa80301c028181210480c5070031807054440c40b03003080000c1c200c0d0350f25100c0c203462044411090140d800907030314007000402da81701c0b000e1002d4840114240380c0a203040302c40d41d10035081d0200c109500d0f1500014509021005000040d900000742c51040707402101c4a000b04503800961004203540078070100d03082d1020413680704003039a82409140c40c1c41c0f8010503041c090580201110700d8640d030141c2600441d4042141d800100400000380f02154904900e412816192100590008501c84010008a680010214101a80e0200700078095111900c190320b00e12410440340b02e022006950854029015841005146012403140720290f00350b90090003200c0c04240c1c00341d000c10120030706005802281c1e20402c07401d140004107038a4020003000225145440080141c03050b034507508562401e20500e0340d003900d4410030000a000550424000401500c0003041d144500340000c540b010500000386c601044404845d000d5982d59048003031800090b048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 894094748 1250 894093498 894093509
    0x90f030813031e030f06240908150c0d0903090630021308190204060b040602030301030b04081b0d08011509090b0301150b0408100b0f010c0303060b13 66
    0x5000000680c81401246407120907a410b40d01c0703289000d10b04004800260090050200301961801d09480d041a0384c403881c000381100b10180c0e2004190040880f1400c1000e00c0b83d0020048001020001c12074000b07000c01070745841303407002c255941c1d1781c008180e01c501510030415216030034103518006060300214110306031000769840e41c0b012400340005c400c0030241b40542891011101c200c0003441c14407a80034110082d200d0303035102102c540c0c441d0003e25001c02d0b483c11081c0002881c4d001000c510f801e1040500804440141c0f40c20326141603000380d205d000c1448003400d21220320f8001003c001410040720000700c1d0380054440c5000014080540c0d8190105080313001c54070b010000316840004150080008155540c0d11100c0c5003006032250182c40822425a05076413292211003181b02a4003560000c1c00300c000e003481e122480e00e550145460310500d034580683c4c2c501200c10009488000d1a03409016003820598010200b502c0d08400800d043d40c082401090b000c20119022554070412004594 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 894095998 1250 894094748 894094757
    0x20f0d15060309050607080408041710050709030b1918030206090f06100b0903011d0a030e040203131e06020a020307030314010f052e2006010b03060402091201090f03 73
    0x940380d4800303504480c1c3c00c1d41c0190842e4015000962210321400c41550310a104405050405584040b4039085003011520000c058102d12a000204c0300f507481400e42c40b070400c2c6002c00c40285191901140250b0103800070040c113681180005183c403060f000784061a810b82002d03000750140342402911004199070001e050301406104070401d80000440d03601038112503601c44070441c07411029004075481403913007541554032820301c40a9000c01c54414884141c0b55070291800c4600c0d40b40c010050540c0740390241c440c41c810b00522451008040c0340310b181036808a281804001c60f419000c0780815072150061050f0f000055000406601101800e03007644aa01c040c0100c0e00341d844110b0b08410240200640c020105008000604e026401c400d040070400000c401c40350841e00505081c1c00307809071884081010b01095100b503490344103005466044220150400d94100700011100e407001800312880b4540200d0002403e6580c010119858002403008010300b5800d4070346503160495818099000c903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 894097248 1250 894095998 894096041
    0x703051902011e1b03060503030405010e010e13090507120c0b0c0f06160e06030c03060613030c030c03020a0b0c07050f030f011e05060909030a080a0605180901050604060f0e070201020f0d 82
    0x1031700902507201528002000345042a041200445c5c1449280c1c507950304028200380b9400941d1241101042d040000120215881b10181021890026a0b0340184200d004000035480481c1ca00c0403e0010b0302c0c21619802d80d250b400e540442d00e410300c03a0707100000a00442c0140071346002a1404c59105c0341c03480d1180b5520410f01c2d01000307100e00080761080d810034400c00c0007503524917001c00100445440140315803119a00c03501c50f0481000c99800485200302046024019450041c4032030000b0030700c1031200c5140007507007504540c444286105076030048101c044041c14035a02440300028007400038000b00528004030540c3c0402c03910640040c10200e02d0100800d8403818185601c611a00d14007009503c0d062104408aa8454000b080004119503551000c503882e42c8000a1050b488a8920058204e0411490b41800c407040604100d110b681b0740403041083d204030006d00d00c120790000007032031015658140c00b640640f04c0e085030840e00d00d20000703e45003042c07003a500c0b2080042040c6140c0104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 894098498 1250 894097248 894097301
    0x5070908062403010b01170403110708011a0405091e0f010f061403070501020601120503040306230105040b0d1b091112150d0609060615120e030703051902011e 70
    0x5c84180b06115400074442c006003a950100c08258160028400d191000c4c4045000040b5030801105800401c440e075100c42a00307a82e01c0d032480b03400366101000c950030445400d0544450707503140a42c0e052000c0301542c03000b8290142005015848022883c1c000910150b04840300010041405000e004412800103404a286080020703006d0305881044e00101010b90030f10b0901080e0700900002162948020080071000806a0140403440400031709444540c80c450f6213801070212050300004e01035803030074030000720513544d0006401d25503802c600e58102141c3c0540030b203040041d040c2c2054021a0070200301ca40503000b408010150802d560180d07648548a101004903a500007055180d40484801042001325035258404051240700c5e007000a00f5641e02d03050240e02d4007184802038081000d00304041c03002059409a81e03030008104019502e482c585542c080c200307014102180010810589100c07503018000d601c800140180080c071004c400b03680c80700c1300c07000d000c100f122852303040c0c1e080d5052200d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 894099748 1250 894098498 894098501
    0x11011b02150a060803040b0309011806052202012a02090108061e090a02010f0507020301140a0c0c080f0306190b19050309070e0604060504050a060302031207030f030507090806240301 80
    0x51307070b506070701440c0307010314050004285070000b1b0202c08180d581c84207103030036540c000707210074503294821200030841d4540021815560b20665100440658002c504080140c0c1e01424940414807286000c40c1030f090200754101840e10484002500a0072903c0041019000000e072180300d04008440d42485072100080048020700941c0d81c03035402d41c4595611001503014140500b80385100e40341890800e40a5000242036034440300a5200d00d40343d01003803140200843c007801e090000181001204a955039407004a2489150064903c000c0f01001041a6907070314044507050100c0d00720030701303c0e85031158103030b140e15407100503080d4400c140e41043c17281ca68011030035203208000581c00f4114841c5000003461100d24020201d6070f0041c1e481c5408101d83c0d5403845010300900e028240060854158410305191541811011045000a1020b90000303584610840c040210310324001c2030903204c941d02500d0302901500128140e0240c0000c0100c0644124601c408156000308070003141c0003007000707050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 894100998 1250 894099748 894099761
    0x30703060f0b0d0c0e180303270c0f040f02040f08010e0105060a05090402010f032417010b0901091104051f0201050106090b0406030509210d0f050c090111011b02150a 73
    0x80079018403034800c00c03100705100c010030b80c007402c042c00080c0800e0701c0b1041242550308c100c91400315481d2403035803036921001c003006458200e41444000c010b403070083c0002941d0074100c810303443d01c500d40b0b4440c0c41c0342043e42901500e00910341000101903441e21040454041d280402d8102038661078500002d49500c0c3c804007400407544040c0c442d07205038075107400469000352001c0000003816150b1a500d0030360b02204103c04d40d40111120012100c2e4103100b0401202200400000140c1e070508a1249145e600e4040700740c11134901200008a011425407014180d0096901c41507000c1c2005084414a50180505203046511980204074a80e281d00c003e0b12524038a0044c0304045106003c1070001c10f000323611568100003a9011221070f80d8010b440c9602c514081081c110258a0100707400742401200d00802c0540007020b401440030345401502014070f8043c22560724108840c0c940902040e0340c081d840f43e004030440c01c80f084251520400e01035944c00f40080980c000d14401000540030b641248520b8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 894102248 1250 894100998 894101003
    0x901050a06181a1b120a050c1203010308220305120c01061e0303170c1804020d050c04051201091a06120109050c04060504140f070e030703060f0b0d 65
    0x241665070915000319402180c03880074003844a644100414036100c001220607001c90080a0541d4601c200340c01400646284042c445440e8400c500403544c404410302a25102e44ea40d29201752201005c41c45245011002241c2560502c2d0000010051007400e000070942c1c81c41860b03007555207840001820425042e81d01c0080c20742d8000302810408140000d0041c4a501c903088004540903403512400b1f07000d00700707050200c1d1044000308410810107030010310700d18030096456507501c41c42c0740150b20215280325507a0782615210502150501560300e03079055840000c3d104204010a1401000c0c010145d442401307510701c990444405000c10300b10500500301940c0c2d00001180220301c81e04181440400003900503a4066408100c50800340c6c03092192000842c000d07170081c1165a0043c041c0300c200c0e840c40c0c0205005a0034130150b004018000d0b80740e9034007d051804551740f1030391085011200c62004820141e4940294040041804899040150040c0c02482c080110462013000c12440c0000318000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 894103498 1250 894102248 894102259
    0x300a020f01180611010204270b0d08071209090504060c1d0604031704030b071e0e1806120a05070906060305100b03041502030403020f0606010201050907050f040612030815090105 78
    0x51110900c6080044c4070303184840005400c0a440708841020022910900a052038410841d4503810782217008138440d4070029180100c4590303181d100c2a49903c5010b90251040b800b4810030789842d48034201800c002c0c48291020011828940780446c041d100c40c0500200062180c44e03806a054010140e410780c2a9006115501d054a50340d82c4103812603074001c1e083e20b0f60f01c06200c000701190f06c1c0c014042c4a21015560b03c2c2c1e424207820241e01d42c1120740ca00003001c1040b02008500152247c110401101813541c03200c030f03010799030744000850380e1440746402d01702806000e0540040050007d42407080c0c42100105122540d280c2408504940f1f04544544085201844c204111040300f00119081390040c00c4d240740351101172030980300340d0b0300c240c03400c40040c0e014021210000c0d1040c0001608160309200078000c07400c107032200c90b40e20070141c080e45210303619444403900340e0741d0b0f00d80c04540107101c0c41c03000d04c1c1c0b007040c641809041024112001d6000d411028540101c0380380c603250403410303600300a06 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 894104748 1250 894103498 894103547
    0x160503031611030a2f060a0804020301090c1503050a020705070b030a0204351b10110105010f1e2115090809011b0b0402300a020f01 58
    0xc0c140320a00c0c5941070b5506035141400c081151818081e0b44403a40c00f48604d5084003c0c001e040e8036001400e42a003091005003001d2038900741d503800e000c845070702d4010300d8000615101d6000080c0100080000101900085200022410b240e00e000140a01036510304226603a2010000803d91044040041c05500401030500501074950003070740d0044000080182415120490406030843c4440020044601030030b03514841070490600078040c01220000c2c10058500407151091420b40c14989485042e02c41c00c0c1c5411540f0900d01094481a9800288200c0d41d480e141003400e04101e024540070310510030905c1c0200d0600e41085012241404106410410242074030000000c84d030100700d407000e051801414403901140142052523010f030f40102c0c1d807424480000b4024003521072039214640800c090803804220000740150344150152201e41300301c40100707003a4104024005075125000310f5410004081d020002d1500e0500d44240e40000001041200550300312404442c07441c0c0c41002000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 894105998 1250 894104748 894104767
    0x102070305030723010c02070317090906060a0e030303180c03030a020d051e13090501060c0b04060902040908030f09101109010c02210a20090a0507090f080a020316050303 75
    0x404003100c242c000242080030140c089883d6095943c00d0f4002c90041c0d024900a105001c05001112b40c4600743c120f94525050312000803d28107840241141d01c501e80204400c0110750150a40408011000707041e240d89141c180c1b231903202034250032030007605881450509030090a00000b22030255100b600107024241c1c214004440d164001c2c4a1800c1929040b0ba000d40d0091514010304102090301e50002e00b01400d120b0048111074059100c0010001420040d9001c41c80c5440c10941058000c840401d0002d81800810050310401600600828000080010f249201c0f0815400b5007040c506a804480540d010170301601c1c0d4aa00301032060b18200304803505580204c2c0d2208095101078200580c4a8044601d00951001e00000070041d800c0303100342c001004038103190303085413118141441c00e0401082001c41e11424005041248490b590703c04550b400f802a00f000004109046a010495440b92a01602c410f800e4500328000d1140c540c0d030111040d82508030324241c0e02d0190046003802c0b440c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 894107248 1250 894105998 894106013
    0x8030f0702071a0d0c02062806030b18010c030b090a05192904090302030415030204030f0f1209240306080106091e0506030d0518040c0806030c01020703050307 70
    0x5814201580b0030b5200008902e002501d01c0c64000d00002002d80c0c440c810f800e2400e003a518503800341000c64010fa000c10045240451403411031104142015a0001c40016520014580340d003010740301152020030406084030342004100300c0d1903014000e21091015030415800da0390740003543d50340007440b0000550070040560080380c4c8501d00340064200c1145a21501046400c02d080d40b0020004411038001507945060b210842c2900036141080781b11050b0320b00035103e004a00611300302d40c0000c0b800c0182e4601c26019100555045100b581d812421803078544501009280c048034801030001d07060a0250040718008219041c1240c0390000c0b5203101c424540301b0808100110905a44600108806201341314040152203440d83c00940355804400030201c0040031031481503268241400c0103001d85000c1100120049141032503901c84011070030349000c801d0b421f001181c005180c0034030489050351088041d400742c42d064055403441002140126156009808080c0c09503008100917000607a46 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 894108498 1250 894107248 894107251
    0x3021005061e06070209070f0e010e03100e030705030408060a050114030a0605130b010905040c0f1a0f1c0504020108010b0c1207020f0d0c05090c04150f030b030106031a100308030f 79
    0x40095103840c00a6002640103c0151024400514258084416142c002c0d141c00c500c400f00342003075a2050902f100080e526901782c81118103c544549124905160030400c0e90b000a1b408419261540e03103c14100707a03030380005c40b01c035030429082c0000003543e03502c41c2a84000904c80034000d80110222034881c80c1c060500a03002c8030300401d05021a602150841400c64080c10a42c200882c1031f0400741003040f41d0308071940201800201a40701000015030b0301d01181041015000116100e0142e03488002d01c5000e0119140d41d4000800b088411000850303200901c10792003621881c05a98030340350b07101c1d100c2c0141064200c55a014003824000900801d0107090074510042102e41e0440300b40002c1151300781c03441c0d011a07414041d070005004600e0920805035204041d0700025040519240220945200e0040403805003e01500b5048203984a904001c514180c050020b222082c2e6902d4440c60703c031110b02c12401f54034204000319400b4101840c982080700d422050b0a8115241c40c030010072480710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 894109748 1250 894108498 894108559
    0x14030a08011211010c110a0801050f07030b011706060f18131e09060902030304080601091107120818070b0d18082208010c0f0216081e0c040e0102070302100506 70
    0x25081c050016a650a03403107c040d1a82c01c002041c1818542c0301c4000a10000e4001000d040c2032840c88462660300000a000c030302440000b0140c0c0d500c0b10344c08149284a20420003542d2880090804a0310011484224000c1d02c191550085111100d000a046403c8042201415500041052000f180350741203840d20b80d0103175000140c0d8040950010b4550751055100e40d00c81d400400042210030395a100313143c400c4e00600d20181c5041042d1fa1610b003031004a00b8a081030240071804141e01e404407040c1d910700240040300b1540c00b80d4462107200303115081080f04a14003410301c101c1c02440701c0c424240140540d0710500480c00e0000c1c1c04c20035001c001c080031481701a03641100c0c0019260703c2c24065194200301b141c44540d10803649900090402c400565030000ca0100c04608011920002034440300f15000b03895042050414644d41c2400d005a1068140d4094209030465844600c190300400b110361090302103411100441c04001c05444084818a600c20713a0001e102d03403c0c21800a52001104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 894110998 1250 894109748 894109763
    0x60f160e0409050105060310110a030921030605190b04060509030a060207080a080a0b0906060d06033216030204090809041e150305030708070f14030a08011211010c 72
    0x3001034011404444482009880302da450b50144101c40c1024404d411030030b810341d8030034403480c061132240e4240783c03169242000c100b580d91b03a06e5030140100580000000b602e00d00c220b01200f10900e070001c2c054507140c01035a11802142548a82800c0c9240c81c04007100c4070301141e14141403074014140da039038000b80085a0503001780703011500015110b06c02841c40b54451014991a1041c041009004030002804810020310385409400700d41d541a000640c41902101d040356160000c5240801420083c3c4c0000d21880c844000009800030106071548048201c4000c06140400425016620707544171280c944500304c044024405820103401c070820740c134045d00c150f5240130594008201141c011303840b00d03043c0c40c80c005401ea04200c954060300e000e44200000c0c00c50a2401c6840c0c864032403040f41c400401c080d00002c1e02800300300701c0b41000e0300300f5a000342c01818503440c0c20039501e1302c90340409449800034160030f0011607002c0c02c000798039030300c16040360300c20b02e00030346038001501d0b8074a44200550740c28 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 894112248 1250 894110998 894111017
    0x40209090f030a050a0f17060f060f0a03060302040c081e1003120806100807090608060a0801180501050106030513060c090e070c030e0f1c08070611070b09060f16 71
    0x41204100408403560f0507038801c0d0b91981c801074002c284458a00622041101507000040300580c101061a04100e017241e0060b255698940003030042d100703c1c4403101c01c1d0800882c030850000d07010b9226004813402500c0500107280030351f44c00c6a100a08803408103801e20041d400308440181154066400300d0441d401c3c1018503203c0d26007008980e20b40d1400303030000da0a803003013010b14101038000000074803c1d81000c9046041401e07014040000700e0085070100320304400028050340d0388150910052020303000030442e061507034091100400c82c5d40b0b010784040d0b003413000000e1518803a10507a44198074a0b9110f025940480d5220406003100701a602c0400c0203007800460b100002402c0d25004205546901b51896103d190240080c01d000803102e225156100c441029510703003070444a50390f913201001d509040c0151a140199014040c03015090a03c1d050340704c0306121440d0000c1580c00e0058800c1c01550351990301244d0390b10002c03501c04e9a11440300012610602041ca02030113451120b08114150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 894113498 1250 894112248 894112273
    0x21081b030414011e091203020a0206040902070c14060f030a0207020307080313060203030f0a020f07050d08101202031b121c090506040609050d06022521020604020909 73
    0x1035412a41014030000340c01503403000150780101e4028001c0700c3d0104e0404005001d02d40280405800703110b8921190302036001d1100b098400d00080340c0030f5078001c208a4075183c0b40c1c503a00b0300075040030004a4811442110104068130b03045008000004000c150514002659a14200541000c0c02c00b060841d02070100c400141d80511211014000000065031107050004401ca00c05074550f0104055400400030b108981e0301c420340d00d985c054920040965265800681e80d10544209400a8064040d801d40b03842c2c00c41d0302c200c915000c2c030751b44610359205a49401010110401045000354142d101c0580d6050002d0502200b001c1c1d44402050309104100701c04040d41000040c0e01d07006500d00c141562141915006001c00c40a040141d1703c0605085c280000609810714500482e41300d016240049000c10009804451000311400040c2c032000400004108400e40c03040012130300c2c1d1082000c44031004501082d00e46001d50f0a82c014035050310b4603001d2000003031014103111010f010b070030100d550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 894114748 1250 894113498 894113503
    0xa0206211603240302090709030818100305010b0d090c050a2607080619110a1101050c0a17060a030b04030503070e03060601211d150121081b 62
    0x20401805120041d00e41603058001d00322404200c00041c102d080030442c419404501c61004103032541910201d92079103c601c016103440d03003990300c014000e06000a61403800305c6041440120040290fa142c0284440500180c042e0f840034040c810840c0710074002e030036110140750001001240100e905c160050b803030300089240035144d60808030410000141c4100404c50154005c1c140303800d94400340c040310782000401622000041c04a52540140b080c084000100c140d12525582d1040042c460307844403260400b4240c45002c82c2c03d44099460000010180d0010350f0844804102565502e0031848806000244000300a040c890304002548004400140d61106c3c0324081c80c081c3c2c84068481c900b80d180100703000c0c0d1904005029400000510005903000900844036020b901620310071002d00707424400040501501c001d903024110303501100c11000c08512940c038521a901d030040240c1c1ca03070581700482c1c0d0200e40c0000c040d401d68101100441e0742c190140c0500f120039100701502c2c68801e0181072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 894115998 1250 894114748 894114751
    0x80421090302100c0308010512060711030909040b0117061b0a0201110d09021e0303190c020307032102190b090304030609061b0804020d0b07050c0304140f0307080a020621 75
    0x49201c4403500000d16802044503801044111028004040c0b0394080542b85d40b000707050001442041105158142000d200750384003002c0c080d01004851809042c4000e0541c0288900b451418580180014103070022403090311034040b0010a0a105440244810203940408912000c5540c0c481d419508151070360024428060107100204040810f801008200300b00031606440398900072004042030780380401520b0741301e003070f4803003100401072268400e032060451014000d516015030170011041200f9502d0042c1003c0c1060b00c0c10703281842c0003070180ea80d055446940c1c070780410001c050700001540303401c4103940001c0c1801581e0900b0b58035920081a1006604100c034055191080e41070450340041c0d0a00600e107203840c1814290030580c001c22020054100040c141d125070314001040580510211140f120b09201120b40c4c3d02d5035a1500b209600e00c602126101b0710031080d451310540b800050000644407501c001d800d0a801607802c1080a034040451030004113107090304440c4010700e509425 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 894117248 1250 894115998 894116029
    0x15031f090606081c110d0507020f0306071205010909020f1e0d1a0a050c180a08030f0c010c08041a0a0f0c120f2c1204030f0c06080421090302 62
    0xc0900c0e280e6010071034911444859261308000c010b90085099640000341100c007078001e400c045541d8121800401d1540e460303001c2031170301881648140403aa9078441c40e09070f8120140d410130880c603601e030513000d8103558240340003035800040320151072103510b084011038034411840003c00342807404078000300c5d0414031940e10075100e160342d80194a44170071062075810781c094100c02c0100142c0c50140c1d80e01407103014a00b86442d000001c40340b10501034480880c420b0280c0703038002c2242e84444129a201c00c5541c0721401d0b000b030f00d508000410301540d024030000c50081c0c0e03204940850180c0403200044185c180107003c07400054a82c4c8540c55120f44c54804c00c20940740307543d10444501d076822400000d0341c00110710304603a140351855880c480d05c1c0d034000108003000008030114500801400251401c6880c482511054000103000010040040c1c011504644202d0204055556821054030041d6045070040d01c405120142085c0d06250605804000c0c4080c0c20456800e070b4a94020a60044246608 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 894118498 1250 894117248 894117253
    0xa020c0f0d020d0206100b07110406091a030303040f021207030807060204140901061d0a030b0f011703120601030b130e06091002130905180105070801060815031f09060608 75
    0x341940c1c0c0d040c841040d4a03900c0c4e000a12140c104803028180a503018416851071400c00b140e590100301c0d89a1030030100300e41c010401d1146079103d4001c24002c080d521985504c400032810800101e04000c01030320700c00d603084004904070240d650240044012207030030084c03580c040c50902100003078080c40074089850180c400180c9481c01c0800740c0301d600385d4404981c1e1164814800411204d40d001d903c1031010306006100700207a41881010550790b00403034000422401c1140704102264480f082d429040318644200004a0400e0000c4c0175100c2c401c0a426840030024140040e41c6540203802503e100340014003103030700c2681041684400c8641e21a20b206590304000c0a0046c810300821078102c0391401c000045107800c543c54180500011284121a0403c0c0c40c0c400240903400100c030140d810018040090045107001380c40105640070034003810001c04c0104020401080e10b811101030700000140c0200710b5a8a00c0220f0300c0b01e80541240300540310b48951102e00010140c0c0a03190041581000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 894119748 1250 894118498 894118513
    0x308030112020901051c021302040905011d060108191109030f060403030b0609030721020d1a1008030a0c02041d011508160909020a0b120601141e030a020c0f 69
    0x4012280c0030690005215040d903110700c0130001006a40c4c50041d075811235011500080b694800c07800303070046070301134004145404c0001407900302400c10300b19019420010030406075500f80040d07441d003006a84160403000d40c02814000c4103000c0d40701c1d11903074440c202c1320b0f4141000c00c0d0003c2c3c60000c210b811032190b034010105201c201509800b901c0e80400d0121040350902600300c0220f65104824030a401c0000c141c900015102054a10200310440e0040e000c004014202d00705030b0031003501001e0985403403010300006424060408510ba00f559240e01c069844d0103070b5514121007003111400705980c080c0d524038141c0015000c1d900d810a400840c0000401c480700e450311914118030701580680c07465040444601164042c404a10080c1d03400c10400003907085580c000710712000302503003000380c0009000030300c0c91482c82410f00244c441c480c00d0382c1c0e560715410b4114100f0554000c80e109407103001c044041c0711350210121400740d640004c00100040c10040000025490402e11880ca81080c2d00440d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 894120998 1250 894119748 894119753
    0x1a150a0504140307031502121b090d1e03020615060f07030809070902130504180206040e04050c0904060516020f06010527040f051006050919150b0901020c12100b03070308030112 78
    0x64081e0344100d928010030362070015108440d49c1071041c50352607803040d5403094901c41044103041c02d10600c007003126540c4006032100e26001c0e40c1da1070700f51056914500b8010003041e452410b00d040b81d5880d52500c41544c1060075540e000d9171107501c0504113000310b014083c808100028248007034004150501107000f400c1d4078000901045401c001000408070030004104400350712090100d8007140e048005401c0d0031b556506101e0f09141c03a1031000381d8050500300c180b00c10700025810840c0102441d00c02a81007171209042640d890031101c10100303098006800401c007a18001a42e0701040310180c1102c51500321000704820020b004503802c48401203002c07150740c180301d4100407490b40790b07201c00d0b0100545828400000d88000b070041001007840c40506851502c40b6850b08103080f01c0b94841c01c051200c85c0c6499518550790030a41000c1d00521a00c46e1102d1a880d20034000d40c0c030444104090990702d45800003900140008011803a0544565440040042c0110009500a081c85800309848a0a51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 894122248 1250 894120998 894121027
    0x20d290103060503030322020a09110918040c210812011a040b04051e030f0607080a1a04020a110610030204151511101a150a0504140307031502 63
    0x160860f0b40a0741c404d00070000588400d41c1c0c201010a481001880044120f2000501924803070b0400c03a0403a0500889080300507800d000342a10000440c0d081d04014034500d0340361f148030310840b0040d20b4080c10f88010064400121042d47c140001c0262650610502c1e4880c0300c1c2581c040f80c031186408100000400602d010310407002c21070359a1300551442e00c2d00d029000d0761240a030b402014400d006400c030180705983c4d82c2000d0400c588000e8255881881c80803080b94650f40d041300c0b03400224950b5000600c1d0040e99101702640700c421204c11444420722581404004d4100701c2c14407051182c401440c1c40000c0302040030342d2149102030702420415045206200991f4900000e0800d6401c00000602c80c1a48980c0800c0c2c0c01c010714034099281d8030380c41a14030715200e07105008242a134a401da61515082c4162880c0400d200c0a0381e4101c41006604415000341c8a00404000060341c180420f0054455040c92440301d000d0003000c444c0100d44a490341040c20000d804032005041d80086c0684596250303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 894123498 1250 894122248 894122261
    0xf082509080c030703080708180d0609020f03060c1b030405030f0313080312010e060d02060a0c0303142e03050d0915031e02070c241205060a09020d290103 68
    0x1a0f001d40522881c6541c0c500b46401140d800505001000c52405903464a8030031031602200c0081100c203000c5c2e003600b041303c01000c5100059004443c044200c0466060000d8038034000c0002200c001c0c070b80710240180990500303152404000a0104010003d41603604001d010750751010540611798488075290f00f1030004006600c0808140c1090010f240e1005c6c03480c24250444480007004a8540c1e20040054203140111000070342c045804120254000e45c070110b000c0035240300f03460401045010540311415000115411107000c1d10303001d2200c4407103544038240150342189520303140540d031703c03582d600e41800c442d0320b100800580704180802044560400c4443c8061860a08000b81400140ca10f181c0030a0014091000ca8000a0080402c5441526030008149003801d45031402e01031054515444002c1c6140800582c10101d01d9400c0304c650301c26140151801003000240310702e841c8445010b5000a00d0b6100513a40c0c440c4010722082c81d2140c0c480900d103610f0704441100e0780741e40c0007404541e035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 894124748 1250 894123498 894123523
    0x1e020c060609160504030303020f3708010b0a03090201110a061a0108150603070203131401081e1302010e0306070206040b28020d0b0d08031501050a0f08250908 70
    0x3d800c1e04509600c1e411108a07030a6035050724015030354014000400040d84600b5190511603680441c0194158083c1301d2004480c0080341214100408441c0003103c01c2070080c0124035000c402000042c038114005c1c0e00120100384103051401400940c05641820145a0f480989000b038498031290040d144800114034441405d0030b01e4402401d01344d1048040c45c41d40360400d4012400000424260790081068a00411000c03115801c1d0a444400780d40901054280e1a4082505540482c1141c0310000114104c421402c141004594440d003104100c03c001120523418040d00303600c04c42a035102031058501c00c00042d0000e020b54142131600e6902c241c0010540e000303460427400250321030464000e5001c00e240c04104050384038003850301d0440003400b0407100079901c56a50805a002c100351500034500c503840b2819000c1e000550100156140d12801031010006484502c00c40031281c05280c00380d0b08280545100ba85410307a01d00e408000d40302d9011110049100044100302d08401089040340964 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 894125998 1250 894124748 894124771
    0x70819112110050c03070e03030d02040605130b09150904140c0c0d0f0c0b0414070f17190201120f020d09060510030809120328021c09091e020c060609 66
    0x40c1c850944c0c215400060301503810085000c456010300c0d42c0800c00e03280031a032480005c550f2183d43d0440a00964051a5110b12101c015030000800500d40c00513117480c03400251840c40b1640316004502900c5d132105d00000d512503560300c142d40404070350701d80c25441a44100314481c0c1d105929425075142080c00e0321000c0801c03021103080a00e0301c3e84061a058484d901c055809031640321403400c505004140f03214580319104800002410040110001040f13070302544001840400003191a9220102010484402d02c494820f43d00194400e203e0003840c01c040940000342c610140c81030405a0340b001075004441038403170524805020b41032080030b40003619070f819075521a00d107684000c858010044040d21070082240620000201801140d01c017000c02d0031101040403058114054540181061200502c116032805e803414507154080501c01c407860b00d55116984c58000700a01070440020224294540740004245c1085140081d100010310313803001d00382c81c0c544081403200104004085941c41d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 894127248 1250 894125998 894126001
    0xc030201030f0e0c061c2a0906021207061503050705040e031303030c0f240f0e0615040608060c03041109150d231005060307081911211005 61
    0xf00c2c00040c03490032206090300c1d10368560070b0a02d50b007152200f00d82c0011101508000c1445224400010007030b040411442001d00203000c0c41c902110307240c8a5001b500d0140c3c0c02420041f103c0d6401c80040c144661003036401103140d606007000f032032049c109035008039883e1b03005020a1066203403070b0041082c42c00403500158101032480403500300c0501207100180030701040c1c2d0303100c000340590341c00b032860301d0b680102c40c44010121011500104101e20700e00c03512503a07d00600400c90040d5401080b40308412400180340c582c5910f520310410280003410258007656a480005014000b4481b00344104500c001c007584a140c181020100c01c003c081202c0d02c0703019203c042100041030300c2d01c55901c05400b0f6400950352902071030000da98103102903202012040c044043c50b40c0c0000002d4030445900080800e0017030752902c805265a81000c0c1c094102c103500300780102440c84140c2c4800001c032601400c0400c03658000c48001c28522480da00c11900000100500003803074850412114809000d880e408100c036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 894128498 1250 894127248 894127271
    0x2213009030a02040515120d120c081f0f060504140901030804180908040801020c0d03113009030c06070504030b061c06020d0213330504080102070c030201030f 70
    0x49400b0036000900c01d56883c0d01082980003c8482912007840c040c0904480c402a8a51076a4030401070481c400090090f0000b0342d0303000044d006080002c5601e40b00c285103902c0d854003a0041803615166001a8085100c0c00500d00280c16101402481c0320f0301c1c1d0366039460412001962801e400368200b030203452441d00400c0085e0340342e4100d0f011940384815004100e8004c07094000540754002d005444040041070200d04120103500910815150100322a0f00290968058094601001c214403040101340803203590029851885265101c03228110840210115400e10b0603410545413016940d2010030f850400035000c1011540020240c02c1007400c0610310703510314020302c1c801414180190101d81c6000f06010300a000d0b58646540200c3c1923443d40141075590000750840c0407007041a088a020001d8011429103100e41100a02c0e81a0189148048003109440040445070810000e04000000307840c107003840035200940c401d00e110f005491441c0001000d07200c4400c44d50081c9841c0010100b00b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 894129748 1250 894128498 894128503
    0x5030705042a02030f1207030b090c0a0c020d020406031a07050301140d050118082709060904031b0813080c011e0207120503120916030221300903 64
    0x41c20200c020a04149800840100e04501541170000080b0b1000300713403944200409009079200c2e1500d0b54003004003c10707000070084a00010355040c82c107560104054000c0ca4460141c16410a0010308004000d5070a42d000c601100d2081d8000d03140300d90000880f2034003104290b810703500701c03071185082c0e801c55040208100c450142084210300c202400005001080b41c00e421290b40c1c180500c241e00100a82414a03024562001580a009081c2e85036038102e01d8464200000f01864003906020b0b42eaa02e0100b88035042002400079820301014491441e2441c180c1e8000c0c52049101d010001d480d500800f4024207040300c43d030003500003030700620400c40c130a91b404140e4001d00304c0718000030f85925029080990800b4155040310007000d03404070a000512100200400b141c088201d1101c02a544012059444002c0000b010121140c40b2030208090701e0034000081c0b0b820f800d0001c0d0038203014040003186c82c00f20752100000b151101c41d044504d28a007003c1c0074049031608060481d2034881aa0006034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 894130998 1250 894129748 894129791
    0x6010f021902130c03050103030e010f08130501090f1104050f070813031103180f040203040818031e0d0e01020d27031e061107080301061b08130503070504 68
    0x400410311801c0c04081d562105070b15299503d07126020001c0355500b540c0140600824003040c0c0104418001ca5880c41d44940c0e81407915034480c3d9190702813521135074121000030000080c01d030f4041d034072271641c0e80210760707080104081144114400c4d0814914042480190388004103280d4003841c001e010400c0860700b06440c0c3e580482e14402c044039080c2039203010713600a001c1044503145440302042c5007050b0700703a44040245031101282c44041410120041000381d21046400904521041c404801c10f04e4411100c10b92190004080c1c60040082031000126229004c6240e49d442c0d0000101040705600700030700940141303080c80602040a070314000949007100c401121b480c0350496140c41ca0f02c0300d48161408019652011903217028540c0e19000b80c076500c940407416103040e483c12000945042c941411600c1c001c0e444000c15080da86014070981e1058200a0301d045450340300c5001d000000c03804c10040c07000c41005840b0300d081d1400c2c507050619140c0d4a030851030040c0c1c035000c11000805003158108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 894132248 1250 894130998 894131023
    0x10e01030b06010c0309031b0518090a08070606030b0f01091b081f0f0618120c0b03090102071407140d050a060b01020313030c05150a08042319060506010f02 69
    0x20760a4284601c1c04a41000365680090180c030784079440940f012320810741c8481100c5e000c0381d00d10400326184003c10f43c454000e0303944000d5940494010780000e000d4201405881d03019404c0000c0c406c4e566100d40080100c11103024141195820043c465490240301d4480071b4100031401009002a4860103400900094004800e100245001c840c1c00b50043d0701d40009080340c0800180c803039907900300280803110300d040200e45800c0100e6020a210800b150445107141d004081080c50601c1d020184040d40d001508242403550200b05150110b102d1500d0f10300d03007160b80c07001003a40314500002126030141b0400c1003403103207031070300b042c0400309400003180040940c100030000760314490000181c0c5140703d071081900010841203400000d00601256540032210140c60b000ba80c440700b046100b4843c402c0203606800b05120030041008620084241481410701011010214800b03501081c0307010401d6002004000010244d0010080320f4010a5008182800c0c2121032003682180032f52143e200c005d40c0e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 894133498 1250 894132248 894132257
    0x1106061315091109031c020316032c090114060d05091c0503090d080402011e021f360b0a090b010914011e14040e0d080708010e01030b0601 61
    0x114603048100c0742030800245034290003004452900b00c0010300c0f50b0011076000b44207002d03c820b20000c9510418801210320b0450b4080c519118403848020518995030070150108104050340f400c3c010b40d00c8041400f60050292a00b500350001010010b907805c05030454440f01694007092001a1500c2c815203036082c00254002c5003642e9a21189442e10382c04081100d40d0b01c1909091418081e0007100031800f90030b484098483c10880e003601520580800d0b50b0090002e10007209003500c060240800344071a24441c415174600400904520311108000380c8104009503495000b81d0b0310821084015648942c1d90141c180c400700c0d840c907805005458210040c02c4501458001a540d140c4d030b500c0440e5803a030104821a1558696803010020003a120030380c000e9403038010020801803000e0035086021810011560b020b01d003802420646802d2b0741c0c0e10304d41c000e0307150889101000c40070b1140300240b40b030795501c1c01603030325100b1001404004181d0100c1e01e00d407910340051000c584044850303a88400300303090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 894134748 1250 894133498 894133511
    0x606050a1b0f0b130c050406050d020907031407091e08031b101a01030c030e210405090c120a0603080a030c170f240d030c0309080d08060111060613 65
    0x20400b501c0000a0340003045240c02c202040421070490224581c0c8501400288400035152404e20044a0490088a42c418064064003006242c5035141031303030042c16860003203050002082d0041316010250703403904c041903841d00e01703100d80500110b41240021891100e0440149000c910a4503031203455034100110f90500c0c001d07040341004010800c4c490000480c1085040800c980301c2000401d80c0080c940024102030702c0100c141d11038080c0705510700031070000d030655540c0440003c00d0a800e909451404241c2840005031135070301c171041d192180a280402c15a6010341d1400d00d140b540009001d1021145405411b0001c2100a0181e80408da154140025a12011002a2004501c94440f223141c1ca04800c2007102c1f41c402403c545026480b41c0429400c0e825560075080c03500c0f030781e840d45582c2000660b603241010920a0180020701802807d129080d140c840c040c00303051007c42c80340b04000c100c0c41c00901c545d035640582106600002c09001c1e02641c01d0031000034680d14800e0f41d03907503a5a5100d42 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 894135998 1250 894134748 894134753
    0x1502030405070f12110d0b1501020a0b09030706150b041a0d09150f0e0a060f090c080a0b0f070203090f040f0f1a060703080f0c16030e040606050a1b 65
    0x1100281c2410380070f4192440c1c0d1440302000050180301e08551100c44000c00f40035500306440580700301c6a110b1540101951540c0840d07603805003080340541144510a040c0b4081401d59038424020a2070b040655500e10f46400d100040e0b50301110a4030f52081152410401c040b00070041d6400c3d1a5400401c42d001e15011419601d140641407421840514191801c400c003d0314038100c09461504807810b1184404402d00306040b0f4401d0b480c510f1440d04003902840c005006036100001740240ca04001803190581d4581c40c011500c0b0b908002c0c850341c4a0709600d400d000240035010b512071005a0010300d43d20301540c1c020b403030340540d0419602070705c0f10002d600259500d5810500c00198480004c003c0500a0b0800c4000707410b40690206809414510741a1a030900b4000c41f4400d80e01500d40700d6003a206c550b03a0f80303003101008015030b0078403c0c14822212041e1002c102102d20a00950b41e1400d420314020400c021941c990f400bc106001040110307007101e82d004407500151600070b40d04901c1c50388490 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 894137248 1250 894135998 894136003
    0x907030209090a0b1503030d0b0a12050a030801150f0e010e060d0b120a0309360605040c09050a1203051c050115020604020120151915031502030405 65
    0x640009601425a004218015a0004454502600070320310701802e51100d014107810318500c0e4407034581680081062854800e20350300711003c01c1501030021460030b69a46001540584542c0040b600b942000140d035080c5580080781c40d02402c01c0c035000c0540642e02c2d00000c1c2580c89148150000d0001101c0c503500160b00070700c000b0705542e0000d054503950f4004141c1c1030006000c43c1180d54440c84030301d0301e81c91143c0000540c0e0300c20103a150b1104251941804014012100903103061151074a86068210b154242d9410030b881e4a2070301c50b00841c20b03601b040c04101c180c0d00003c0d8114200310541c0c50411056948000800840f500d116010f02244201d007002c5540384103c40b580300c200000b2413010180e03502c0302d80c0014100c40c480d401c0ca85070f5113400e450480e2544e4065401900040c2c00d208010304056041c0d84d0728129000310780440b8810354140481008540045402c0d00207507110780c03580304000c03200c1d000f1022080c503a9a0048041030556586881100004052864166003c0002010000c08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 894138498 1250 894137248 894137263
    0x90b0d09050a05010e030c150606032a0a02210c1018050313050102070503070e0f07170f0a0b0a030b1b160b33280b07051501030f030809 60
    0x4030f8002e200100c0c0100301c04d9604c0c0d21001c0407504612850b42051718028a0003445405a64010505491903e5060807540121124a0300072a410111002c000d85004103400800307202d02c441d005440302c0541c681c1c8101402c4a00c0e82c00c484650810003e90100c0701c0d01140d600001c041c0000c0c006102401900c11700410321041d81c00a0231440300103210b4802035500312106088643c01d0f82141d4150791144245603c030849403180b0150f10801c2000302e1906c001c006d01055001609203030182c2c0d8959003d08403000d040c010303101c01c50342c0c251006c10b1207641d6446025191000c001940c29015032851580d03070304c46049004140d2080071807010b42841582180358211031959040d0488030705446500d0800d0b4031960b0040d50303130751100728048198090040d01001d04ac0c201035000302d0341c0302d4080e00c0802841a080c03400e5100750103c00c01421a07600c070079102903445000e000354800d1551100c2103807910902c1c11080c00c13041e04041d00150010000207000041c4426a698145045e40541d1110244070745404031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 894139748 1250 894138498 894138503
    0x20102090a0b090405331c0311250e18010603050f0c030c0a0b031315020a1404270f0203040b1e0c0904020721090e0106090b0d09050a 59
    0x40781d034002403038080d40b03000d0010000c088504100d00d8807400310442d852860030141144922032100c81071229480700c0054602d0141c05098042d440e140c121201c401c0b031030b1151044020404400c8001c0d41e800080007040188a50510f12040e4803030b20030030a103022003283c404d5140b40760f0710304002022118000c400c07c1824984400910000b52039107041915600c0040e0a902280b1548404600d036140c0002d20002801000c3c00b060507250030f02e030070703110154002024209100b03d540c0c07913040000e440121411911030041001a114410f0f1000140180340d403a50700d1a030140203000502004140702c08005030401002c1030f0b1100c60040d9128172000d00541d940240d04584044104407d2044081d1080e101e169100645100c000908280700301d4041c003954203502516041c0300d49900350503d07038024510a40124554035000100750030100c1c5410300c80e054400010f100c6c000401654040f041010b001d846a4208071241e141807400c20190350040082c80100f640c1c40b17540b10720030f110051080404498 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 894140998 1250 894139748 894139759
    0x603110a1a1b070602030307080a020f120c07020d050601051302040b030606031003200a05030316031d09041101080c2503140a1d0103060812030601261f03031205040302010209 77
    0x16503551300a0744a800448207400441c00240001c0d480014600c00c81d1071200110741d2181c00c00c140010a42128640101a405080000c111010140c2d854410b07243c0d03000c1c4101c0040c155076050070103000301e076019400640820b034010b00c01400091101420340342c0c003079415240a03459580d803440e500c0c8101215031020f4111502400b140071041c2140171114103140082d01c000f1b580075620010315642c2d02c20b0400809101c540710042d00b000903c582910080034101d44110003d48408000140071150140c1d0201c071122104a003c020550b0400302d10b81e8480030241000d0300f40182d0345268500300c0440c40f1011011107052924108040c00b45101071035118290384c81c030752156000c0b00080d0000080c1c202d241c5240ea228142c5034030700d40c8a0b0140c9400d489290001e00441100716007490031303c0e000a4551414000991001c1c10250602240a50014038040c0e024038541485580b00e01a5409105000c88941e407000083c0042a003001c11120844988200015241d555007001c0b0300a00507200d0032607100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 894142248 1250 894140998 894141013
    0x2100903080f0c06070e010206070f09090f02041502060f04030c050709050a050a0b060306010c0204091a241e09041109010f170d21060504050a0603110a1a1b 69
    0x280b4185001d80711401c80e0700100e40c260b444490054440003064a00c0383d0043e03001d400001c2220348140500c0d2106402c03230800c0740515846265501c00d803501040c407582003650200c0c3c03c000c09101d03581100b103500700c54005421641812000c1030201e5100400140901c4141a010b03010418104009130040031003580c10800382c04c1c10030180001e004141e980040050429144c0d045c80c5c40c00004480c01818140c60b00c495917401035003840054a00d03031109540980701001384800341c25541d5105445190500c0c0090b03940300c0441858a14107601c0004140948000504014032010540c40441e222004444902150b0f44524201c5610100072106030b8200e40310500006030a40c7c11075a090648000c120102c1c0c051501c2c0c880c0564500406809800068501b50681c40c15400000441c110461803e00881c0991b01c40010a05803602510010002035403454100700384080d402c0d0501c0c0800d401c44039000d0042c41d200704284019170802c2204442c02d8000340080a490140b000b040b10160302c101600c001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 894143498 1250 894142248 894142267
    0x70308190606030501030b180d0e04111201031707111210061523090607050709110d0f0c140309070e0903190c05030706110708160c120c030210090308 66
    0x4e0002840300320381c0e08102d00013003a90700f4404010103540c00c2c810f20082c2440c82024030120381d000340c0381d048250840d69034a83c0d0310035080304900078010195424808000742d40f440c500000c504411404007100d2040602403030000544194045000c280f044460400054001400d1401c000e143e8a08080c0c56152003c001010030207983c0719905514103864484101c3c2000d015101c03801500303058546c03603000801c40c044107441c0c01c1010300ba029000c1d60843d440140c58a80c2c0000315521032200d880c55010204440f0200101802140c0300312170700710800e0102e10105540501038a11b40c00b0b20042e4210702000140b0f4441c3d08120040041c0003290700c404a9080000000d9280d034009690004c0044c0c0c45107218a0950182d00a1080281d011005501d000b20940b1440010542c01c071400d18281820070038000486c541074040c140e00c41d03000100501002852404042080c010f0344458542548040700a0205078155244002c030794055488004040130143c0840c0c404020381c01c004e2030090085080c004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 894144748 1250 894143498 894143501
    0x9090405010c0f0504032612010f0f05040c052a01020703120507030b060a03090c050a0627120f110306090703060b090c03150a05060415081b07030819060603 69
    0x4020040d446050754071000ca40c04455501c03580c000a0002401c01d0048150034811f03400081000c142c400d6903a040c07613840988211528000c0e802084e94007000607003030002c003425190210040104850402070300328410401b070014003480380c3c01c010030075840000c1950300483c40328000d0707052a868021076a4a0b0180340c00707440d504420005a4407589000d000903140f90092145d5900300300014615820076403030750b400310044c2c01c040104551402009000040e6a00d600c039800010b0700c03140c1c50344010300340d00c03c2400409c040c0351a482100d81c4800341c0d04102e5030300d1031603480c5141c540003454124800e9141c1419070425281e1620150184103074010099100b07408115082074901c108002e10508d07401b10200850050140c8000d02a2a820000700d01d0b24000d03117000c600303c00d201410000c45c0c6a0b403200050207940050744079411401c50100b40c0e0030240e0b403100710554480d941c580a05402c14a100510b000ca0045603801400d04c60384501190410307890300c61203281881d8404040c40307055280c000090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 894145998 1250 894144748 894144761
    0x117010b0a12060503120304050a02040c09031b0e0604270602030f09010905060c0d15031410061404020f0409020301030606141e150403050105160224040305030402060909040501 78
    0x80c0000d6060340c2c1ca6002c12014062141111001001401002080100082641c3c0003404c02c8410b4440c608052006888c0d502810013444040e071110b07a0b09910b5424441401c4400c660481e01320540d07510b09200380e800b1031480d2600401c040d200000d0300303a06640007ca0750340810084444e0352524800c01c000b003100a4000303601ca10001d5011196a0315060605403d89058800040942c0c01040000d409040c44001070443d5848282c004205070340c100000840204442c0c1043d2030784800011560740768402007064107641084a4020000300d441c24040070f0490342004110391184e600000c0c01c02900724601d060314050458190115925656841e000c0010000361186520441c070243c0c90b011940341c503031516080320024411481540402710100251140c10285070401007c0500c07001c00401c0c024440c40c4d200303150700e00c21141011180c2c180a4a00ba040140311a0240940d003e544004441480925042945400c010791030703465600c009a66801150441038100c3c50b840200406d1010541011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 894147248 1250 894145998 894146017
    0x3121b190501240902090f0d061a030d0801031709060d0c020111040b0d05180f060105041506020a0305090102210315010806030a0b151801060e0315150117010b 70
    0x7000391410100c0340600085103083c800f80da40c40304100c200402c0500c1d40013099541d400400ca010090180d0002880316400c1100070740d10560340d1554000e4103030302002c0e445514101203005240485941d40c00501c2004140070080c500d00907005401202000c00e07040d90030031034005161a4441c0459414040141849119400103601b042c0b824200707020040200c400b0b40d80c007144410700d0072401000d10405400d0240540720104003c90200e140c0f40340501511200744081d0780588001e515103001c0106950280400741d5115800c5001004513940028100310025407600b0055100c00c00200140d0a1180b91490701e04102d401c4040600a203044e007000350321a4101740e8020f030301e00054000443c0e2020088840980507840a43c414002c104180b540380d84c4164219400b19501a10b603002c51003500324a03c450240503007910040c880140c00528603900300d0b40581c01442c400d00340f190403203040c040150070b051b1036054180681c101c0b40d00c22421900c03170418483c0390035420350b03480341100150b92000340c0c007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 894148498 1250 894147248 894147251
    0x70b010605181c080d0906050c030601020a0312060b030c030115030905190c0302061908071403070e1f05090102010f1107290403031d010b03121b190501 67
    0x40380003030241003603903441551100d0150701c0d581600c1c00d2140c01011402c9100c8000408008880040d00b44c0c0001c0030001144100803c00710304501d4800c0c160384010700f9050003c48184200304442c0d0740080d04002d000d406140c040c8056159034440d000500c50780d0400304440c40c0000401043d10304d20342c001d5040345c07c00542440c0d200c075903030300880444468150060140d00304902d0101d214a44d540350b0301c241d601616160100d50717aa5400110b00394000d0a400c44220707240c025080b1110342182d00180c1c440141d0920141c4942040000170003480b00801c00d01c18040704481c0c10800c3e444a520103024000c000701c4d0a140000342c01e074040d0858016071001c9006600740401e50f03600348990300440740c02c0c00b0400115810406140c1e01ca02041130010540685950031a00050300e010203060500e0085003e91000145620ac0510074940540c030424620310b142e050505144e09514000707400480c80c7c02c20b2104c0d40c0c6856403410105803a0003400c101203007910440091608041c41e5544040c42203105100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 894149748 1250 894148498 894148501
    0xf03070905040c0906030c1b1209081908180409060b0406060908150606090315010602070b0403111201320a061d0a060f060507021e0a050d0606080111070b 68
    0x2080140d8600400f50000640700c8a03040040900076007080318584440d0900d400c4d080d18503110a40f003020015400d60702141d0750108c4200c7c56411141060242100001924600003c000e1380c54140005140082c0240340002e040c40000d180c201690380402c500400a00c5070000f0350400c040501414540a0b10441c03030100b0019000d400380580300b00f110310707040182420b502640150341d06c2403001030545400100812426500c0c3e90b00f48030301800c040031000011095410118003c1c94500d150308140400e1804000c188003194158000355424401140c0521841c0042441036014220880714004211499900303101d0100d07545c04c107243d42c15000068103120b582e03081000401d940f814840c0414184500040104c00d2440b155107a0b403114010801040080ea6040300101103181a800000042c1d00810410214034000c034a048079004070307041d6440d03181d0041c00016040b0816200d1076124441c503d0791141003113030a170003620040c1301c05030007080b103052000007004860f40400310445000c902d240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 894150998 1250 894149748 894149759
    0x403020a120b161b14030a120b010504061409030709020f071e0c0e1b04060e0301180209060609120a05010507121a0d0201051e0903190b1b0706020f030709 68
    0x800e80f03003082d40568504071941d8180c2081c0c80d0f10786444400795a040e20701d411104110004100404051081d035444903114260f004140b000c4a00307814446040110802040084551141d4101d1002c040b030140309980704455400213140144581c000c070806400400d00d284403000720006041ca82e4000e12003200c003101d0103072822080d4039044800a0006001400074800203032481d0541d0380c0100440c0032000050100b124003900c80e0400c1d8021070015540300380410a508007802000348091400c03082c00c034444c4aa900085a04000510203801032002058922a50742e030060407094603e0014144c85c8041c5c00c0d4144240602030403194140864543c5641c1c130300c1c4206900c41ca4409130560843c260740084007400b008132002030888203038100314080c05034a1006040084060107040000e050903582c914400a25090054003007071500e2020100e01c0807004916000b0025602c1042c00c4065400c80302c4440c1070700d64602032050003604003440480c00782440414940114014540c50302c0e03110310240e4a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 894152248 1250 894150998 894151021
    0x7050d051f1a040b16050636100e071d0f061f0e130c09030b1b0306090406021e0403020906040b0609100504081f0c08060607030c020102030403020a120b 67
    0x3000100040c41080100a0501d00d400170741850f8803211400c2085c0d2044d03031650707481d0031b50564030a403412541100d810f0b030001c601c105144a40a103214031500384400ba09003103071603e20f1020b403024690f0b15100f02e8421460140440d0380035080c04030030b488101a10b4440c540700110201e0340c030040b0f0031003000031421910b48440050700c44007000d8004070b203070442c10800f1140d103d810118107401c0402c0104298030042d10f402030744203280c202d40d40c60421034514100445400740c05000c1442502100311001d81500341d0004480e40450295500302c60741d02c031ba2030804024400c0302820103004031a1034132000d031900900004c1c0f044a00840304401662100f0303080004943c0b02c0c010680c0d100100300701101c9a81071220150070b101848bc10440e040550350000a800c4c0804004010f08515010b60034606229140c401c87ca815241340c90300d0b62041c50000d002c246980300701c00020f01405950500c0301d00b1684200704860186a016240c801c1041c1e480c0415401002c026400725583e04118002803004100b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 894153498 1250 894152248 894152279
    0x1050c0a03050d09060219090b0f07061104080106081b030d21140a0b1c030903080c0313140112110406050919060c0201171003020907050d051f 63
    0x106000340804010558041d189903001001422403943c95001c910b02154940c40070744018020016a01c0c5902c41d6100b00604100e000e030050f0070006001d0184c22005c2c004030007981c0107151301c1070780041c1208203260118058061036010707100c0381d030a182c40424500004181044036400868144400c03542480c10142c5801c851400040012420050386070040b10317841007400b402511035000515030101c5164240d8122080300d032180340a482d42c40354138140c2041c80e0484a039010303806020350100c4030b60354010001034940c40701425030380d000300e400002d400050040b00c244074407032500003400300e540b500b101c01d006042c41d41c468041901d8100c002010b5106000e45034443d11107071019842e0034244801071314280c00109207540c01002ca42c0c070403004061b05102900140c41c20340c954680e03200103840014110b400c0500704018240f40074050011000c02104d1840c1a6a8120388000999951039421612401070242050000d41880240046250005540c0e05081e002c094006a41da80343c444880d4034050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 894154748 1250 894153498 894153517
    0x30b12030412030f110a0b15040908040504020a1202030f1b03040c0519050607050c04110a1715031e0f0718110c0304060e03060f190b03160f140105 65
    0x200e15001000903c14000b80e9203881d02805c1c8141c1100c56408200d00e081c124500456406488100303010501c45040123541600008031800c0c81111415600e0020f90b010764071070140102d401040381421706000705a88044000d40100840d180e2a014424404030201529110b982c0c01d04014034410700d0300010120303485542c2020340d407090359140a043c00704102090444241c500012807020a0310b980381c2c5c006020842c0244010002c0003040001c11003242e0342c28281e0b08440d5010061314070f615400850840581c0c3c6011210900b0360303686080c3c0c101d419401d018241d450700802540c0034200c0f100e0104403141c002903804890854508002c0940d17208441c0c0900d04040d104c0c9804405042041c0d007280c02c0c071821070304816081145c4420b2180ca540c016800400c081921510300c858542801c010f02d84d44102c1031f010b016010300303007000700e007524a05003a0074141c80c0d038640104c50701c03640b4100b01d0003035680c03c0c4800c0101d0322a5150401c040c400c80c0341c01490103068440a81420940c800c03400c2c0c480140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 894155998 1250 894154748 894154769
    0xb0d1509020d0f030f1b11060c150a060602010903120203100e0712050a180f020d0b01081b0a0b04052701091410150c0302010e01050408040314060c0f090f03030307030b120304 77
    0x506c0e4841340c980303554001d078240e4440c00030003099040c240d003442200030041c1c00c3c000502042c1040b8143d9003d860040d0482e40445e0b140030000404641c0c0701c0050700c01e0f0611002c005980e0744138050300028409039500055140d9401c0400d1251046d402180051071f5041584100810f84902c0856020394160102c40030780d0341000200000400c0700050b80d410060b07c0205103401c2e400c00b0340d45007201c50009909c6507039590400540e841c080e03507032b81c1c0c112090040c044a00102c000d0a00f07a1003403843c000c50142600490304605496450700c1ba03404e11080c04d1249128241c103130360f580d0010038040e0010842d4042280b40d01c00110306480500c12543c0107032250349c2c0000d9222141804101c82600c0429826403c42d900c8a83c1d1201e100028491035000741d01407030013103a032241181080070814583c0b540003519540603408000e00744844106035080c00c07600070342c0e02c1e5940840340001890201214009039050000005001000c2c0c0c060b80203180d0713224155603682800780d41181e09602c0e40140e11030200e295 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 894157248 1250 894155998 894156047
    0x3060a150902090f0901080706020d0c03081305010b120303071101061503020c190b07170609150307031e02180702190f080705011409010b0d1509020d0f030f 69
    0x1840075401030041c012020b0020341c0544d0700071000400b4200c003a8045000c030707000307000140441d07076040c0402100583c6609080504240d00e54006154210060007230343d03c050100b082404202003900106107072800148050703d4040300e0080141c80e0f62064443c0c0000c80d00c00c00d04168800018010b40e800c0707075a201074181400d01d4408096010303510900d60481107004194112010054030346046010a0133403941c2d042500d8960300140101c06008565410452220100622a6102e100990b8821031022002c040016101e0200e8981082608020000c00700c0f1200c1c2a080c0115804041e60303035000715140c840e065003140344500101c0b000d81e51040160040c15000070700c400c80040039a82903110303c14039000c10310f0070349034211641c000e10300c00c5031646d440b07481213000341003408011a00408080000c01c072036003c000000b455034040d800014000e0100d40d8820440881541c00000c8194006d0000c9411a081e440c2c5400061480c00080300841d000707042c5806210300c0350711203008005070f18420300140b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 894158498 1250 894157248 894157259
    0x9080309060a1103130e07030501080a1106190320090a0b07020f0a0b0c060711030a031a0d12110d1d030f10060e01050306070c1502041203050903060a15 67
    0x1a640100ba15409200580011080b001c03010402030030701036181400e84014904189100c486031030040c0888007018205001400070420201e0702103182d41d80034503511540e05222000c640140038405034094200c0d884440d04545a4054100003110316030010541920042e0380c1124100c1e00956007040d400888040c014400d0264440003403001750f0004101a14121840d0002500060160081d283c0c9200101c2c801848050130402980c2080942c140030040c004540c00290303a0b4022000640201034803150400d9840034103104804103004050811110b40e03825050001010402000c6140002e200740d00401d213540c0c5c007007148004200301d0356442e603070840340071016443c2084404050b5494015030041e944c15040c20000e00c0c10034152b01e1030205840746003068040070540160710650003070700305e0020400240d9000c13540808441c0e1258243c01d55545201001d002401540c000740382c0951450030f08800c0c99007120103400700c03d20440444560340d50303042000d02550b01004552070b03092403c1c0000d210 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 894159748 1250 894158498 894158509
    0x10050c03130c0513020703030b03072d030609050303060a0b04051026010f08010b0109030f020607050f0f06010906060c11010f030b0402030f01060905060f040320040e061609080309 79
    0x80c41c1e02960b0001215501d400005407020300880110103c5507002449404040c4c060061218030007048014050f00c030300c2e018007000c90b4454200b460050302d102422944100301071081c80c001541c0c0100c010030220340c15107051981c981c800e41e070a03840f81c1c1c2c0031322000810520302801c0303605843d0058084011100002070903a108103226068070151080015000c8403a2181c00480e40248004070001c007490f071800342001c1c00c5404040980d030402003500010302c045100c60b080e017180d40707a050f102a82d444a2070b080c03141c11300c00409800001406410f00c4400341391800580b00d03050700e4104c2e10401c0040c0c1e42c4c10095030900c17074042c0c0040031315072403402003203071036000e9000d49103840d00a050116145007410006000c0340d00442d88512a078040707400510030103034007008080c09410f050795028500000c14001c4901400345110041c000d688524502c41a20071440c42c07003514440c040c1c801d01070000d403041100e4450900f2141e24120a103011100f5039028824690103040ba04c0d240b0155243c084100140035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 894160998 1250 894159748 894159781
    0x607080c0303040b2d06040221042a03142404050d0e030d0c1e08131203050415020a080a1e02060c07060e010204050a1d01090b06040605030a091b050310050c03 70
    0x90784150b081c40b070911240644c4800d04018420454009800e00cad0603c1c0040c0003900d00b0383d014045402d03014680760010b0150902d4410303a6080250100c0c113004420001e8507194002944072691145174622141d10740c0c642600c02d025612500684018841c1c4100c22105499003204266042d070103802140c408500404010444034014481840ba06202035002c54a5038511401111342e820002038103903046410f030260501510400300307200074071841610001c0242c05180101c08030744294050380d562881c002c001c960390709903014001d1501c49026800180c01c04100b207400030b40c6400301144a02c4100d1011038458440e015141c0243c0c01c00000340c44400040c041071101107150b40d400c20001c03407140e58501b001d070000c02c400815400d0890444146e80031011040e444035000506201d00c030305496981105440c1910f005140c0651659103014000c07003e8440c11001070998000801c800b4100c04001a85400380c030415801c480d03480c42465001c40445908a0b000c052030741c006d001140b01c0015000498 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 894162248 1250 894160998 894161011
    0xa020906090a0e010c110111130611030717041401111b010905030303040c170a02011b0501140c0406030c08040804030620030c12090a020f0105090607080c0303040b2d 73
    0x5543d0350b00d5001282180e02000e10340000c0b4400e600d80221680c004d003c1c01d5440703031440050a0401c0003040302c481c0d00c02e080340034450074084c0500080880d018200280d070510b58110440d030001c0c5620414885440c2d01c64080c0501200000c02c51421039405400300d01d4000c01c00390002c0c4244901000c12003c400b484118890400c566540000341d160f03000c1000d140a24040d07554090841e150110b01d110b44403000321403800d140c200440c02000b51fa004241d41000318a2204420300c203d0503458080d0040c0007420410000084038014008800c4a0801900030b480d144d84040050302342140c1d00303483d01d04088600810980c0300300700900005620b40c0000d4007100c80c440301c1a5150741e80e1991340b12103400444681c0c6102c0c0000c6149940c6081c40c2062541000b8410040e010301e03170b0507402151050082502d8103042c424005042491926410100e41c070694110104544440201e5483d64030b03907005950a40d803082345500400d0082400c0016140542202024a0071303000c54510021030703021006054 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 894163498 1250 894162248 894162251
    0x10020a11060702040525020a0f0201180801020d0903020c031203010b090117070309032003310e061801050907120b0d0b04120311040504020903070816030c05030a020906090a 76
    0x4160040e04c460040358055a9022042c8100700318103500e0104968000b00124115400360985c4070110b90031030100c90340b941e020720303150240c004522200748001c422035000c01071540c030000b14102e00100381e40c806100c040c480d600362003e46c04241c04050f5907840c601c10a030506070041004202a064401c024020750300b0604203c1125882e140806010705001c0781c4080c0800d899102c0343e4109544401d441038150000a407404180b98842074032030303680c0944915400c0300c0c03030b40061600201003c01c040100159500149604054071800030392108201515206c0c0074203c01140c0e00c41399480010498103803403014040c5019035442c0c0724100c2c0d54107808500390903183d54514540c40a51509844a00c50602903600d400c817605240c0b503c01c1b12984100c0c4c440040514202c0713030403c8610b144045500b194011540980c4860135040020304149071b40c0e01990040c801c0070141c20302da055900c81941120300681c100452984d4070001d140d1141e0700300200943c8900ea041c0060114604081c0094000707150010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 894164748 1250 894163498 894163507
    0xf0938040510210203070c05060f040f060e1c02011409011116030e0d080307081605030109151502070e090a020a060f0c0507140f1c0210020313060305010302040b10020a1106 76
    0x83d028100d920640c0d0200c0004d80c0c0046401c144402040510740080340c09070f0440c001c1c44c158484e40080311010070010045911100b01c401a1102000405942c200982500d0100501c1443c0680240b45092004059095400014503104030600c191144a014050028980a0a40c8901d00750030030102c0300f141803000a200c10002a1036038898464958810019941e8a003405c00015141a400034030440724070800001c40001030350b104c3c00b039a044684034100410019010b0f001d0741040320762034105000030204819040c80c81030340010404200c40c0c15640e0039503103889031803c0a8840034900c07030107900003082100c20010b07039215000b06103500b1903602c2c1c8040c1700c072402d5580c2c50402056601c4124041c145002006640c6032480b000b0f41e680c001100c1020310706106400f00d03140b07111120030292092013501c40c083d4107507009108503454941a840c0c800342860311014064010b03c02804141c0c0240e21380409001c090070080110303813011680e500108004131060703854a060104400403990082010710 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 894165998 1250 894164748 894164807
    0x906040905031210140607031211070203060c250803010b090a120f050c060c070b0a030b09040b010f0b0a0e09070905062b0c09060f0938040510 63
    0x103c07003030148070002e6074440000d00d440c00c2c19031040400c1c5506031088108004900000c3c2d00101600403c000511010442605c1040e007059180601da1740a034140c020740007048584084003006018181c0c140c420020003a001501c0000717025004e203001400c5a0080006003d4140e20354060106400024040005035032108580d82d404034007030008441c3d41c00010441800c002c0148040c1201d0082031705c02c42d0414140b080403555a0b0807a11070701e240a2000030300c4c040c00034401e030030900c41d010026140c028903080610b0004640d0f40240314002015079049000f0a0028103141103500c4041c10799185c0641e000210100103540e54050a058180850208002100e407a10005130541c4404840086514800c0020140c43c040704018a44805031518054290302900441e2450a444181c60601d40d00c00f40454140d901601070b810400d43c415103050030f803620300349261501d6130200c1d115101cfc0b849810042a401882c1c0503074040d01b54490144010807802c54400e00340c103c600b010340112800c1c25070064 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 894167248 1250 894165998 894166027
    0x2181b0d0905010f0c020c150f0f13150c030e130c020c0102010609020405030304031e06140a0c0e1c060f051510020303040f0602220b0a170105090604090503 69
    0x61022000c4544a11404042c80401c2c4a129185005848144685c83d0700880003520741070251070003071007000082c4032212004d858000b0780715421140d1420a60365074100000460726002903207465560500d503040410041c0c0740c56502c82c0c80704965101c00951040a60f425241d00103c07002d02c64002e9468425401c101029005020b140e03a140e0700139104030301030080020309580a94004030690f6004100c00c002980740041160110307034000f115115000c2c413081c400c40c0000e1061074090251030410511442122207840c02500031444c0d10010000803e1481003503e00c05010010181e01101d0000445607200300c110030000110b108481c0003501c000d95041080c04c4030401d0f10010f01001a071102c0204a040071350f4920002c0e20240000e41c1107280540e5500c1a9000300e0b800240304580108150f507a1450b10b6081011691220004030621074440c0c0b1222501c4e00514070342c000050341d6100c51142401c0c96142641682c030040c111080130b03502d01c0284000b9000f04c01d41216148002c0211030506080c4c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 894168498 1250 894167248 894167257
    0xb13020708040504021c1a1005070f0b0903070f08030609130c091109060412050609060c03010b0a051c0b090a0b0102030304020607020319050c0a0f120335010312030902181b 76
    0xf00c7c0b10800b0303d98050410300a44919805001040c04810048500400d440d081803207184d40d8094200d580990761215890304501803460010488400c25120000300903100001d1440f1300c0003550030910701d07503916443d2026051410700c081e022510401080c0540302c01c0342c101d4500c030402d1480241c0f800f2001d10103c0c038681e200390301580080c41c1110245040000c14011103810080000c020125820408441c050780d00c070605c600d10b00700c0d100080100c001c0e4000c0342900c0700c40a984081c402c41c2c042c0e1122200140c24120400c034401c000344800a07241000318410b000801d0b0040e4025419991aa828000142c0c06824142d0b818441c21841c0070707042c6484044150380c01c0c425009480c00145074414032000c0d00c4650411401507640b50010321551400856000c0181d0701440c10720042c025525025a480d48012051100c44c50486160030840c3c80007400281201c0c8200701c1d041c3c0c1d080c03d100007181202d46800d00254441021860080d496200d02d07026500001c1192004002d2001c109010030107601 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 894169748 1250 894168498 894168521
    0x40f03110a05031216022e02011b020d0c081b03040e0915160908071509080c0102061b090306040605150904031e110d030b13020708040504021c 63
    0x6884204032180d0401030501002060300b0b8000381089100b18960420314002c008228405110301d00e6684107540d15141289400c0d11b07001201e004c54120101600b04010403050b41602643c20600c0a000400248801c01c926160f150301600140d0f0b03038681c08807888040320800341c440711024044d078840070506180060b80805c3c00802580c0d210f03d031400c0280850002090313400190810141162005c1c1c0c0906010361000685807030030b0440940400584030310840782c112100034841c6000200d00001c0c001a00f62100c0c0040d1110201c0990b00c004465a0300c402d030784541c1c01078000c032011480800c04c80c0c840e451726103006610785e810321200c20007003403a110040303806642d0251220f080c00b0311741010307440c0b400c0c1041003692341c0c2c0034034685501d016114002d00005517009d4040c0003c40013240b8400d41c42007084180c101c044ea5840c3d1120400280907214244403640300308150480181180c00a201301c40702c5a0f440540b05007444c0c23070326080100a4008421206401e41d07907203944042c146241c0b14080181c034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 894170998 1250 894169748 894169763
    0x71202130906060f11120703020a0b0901151707060f0207090e060604061e06050901021608030717131e0302030102070b090c0a0e06040c020c0607031d270c040f03 71
    0x189003040080c40002c035104100300303105c81213071803c3d1803070742c003155034000410b9294000f591192a494200d16140308044041c02c40040d4a0601a5415040d04040d80c09920780c0d203d1307001e95407121807003000c9150032201d405440d406040c4c100495030003100b00c44c1d0702c05140d0066035099559240302c0010741c0e0010440e060b40f500708608001683c90984104006045482c0780c12062503421070403000d00c0a49070080e00709000b00030642210682c400c12080300c3d11749109205804c05691b9010903556900f12a6080720040520700300c400c9044422415500401c51046101603414600351101da02c0b2400b00f810900000b0346c250740400961001d0000b000d04602c2a003051019103441703030490f82051a9101d440e84100c44441041107403100041c641508100c0450300018a5021404203920f00340c1ca2001d408e4001c4c502094130000e050b00030740c4c01036104119002c000c0d1115010420000105d4000342c60451700490f008441c401d50030211f041c154001d0030a56494a002d40310170112108141c107601c11510036 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 894172248 1250 894170998 894171011
    0x2060d06180c020a0213150f03050f0309030a0308040302033924060406050a030f051c0906050a211e0614091306050a09110a030206030712021309 64
    0x40010140d40010070000754001c01210550b40710084d192444114041e20818040314254035800c0c5581c0035540fa505c44001d01e900d481c2e035400c44041c09111610083c0c07624001d1040340e0b0311607840401280c41150307006020f00f54a8146a90a8402c018040c0c002d07030445c4400d1050303210300e14821b13245191340064095013202040310041c0801001e001d046c0740c00000e030490f802c0b2050040410340544500240c4001c4541a139841c0004113009001c258403282d0300c002a01ca0000c10300075528001480030340100c0641c2c0400400c421030000901c0044110b80009840a0082040307500c20009480d070340e405441d02802c021920040c86040341c5101c4001e280050340d400d904070040800388500500448401c2c4148a501c0c9420505007034051100c190f64010411070380022100d130615011020440ea0140c0d0400890812884840c010143c1c81411501d00020010b20f10486c0350140f120401c4a46c002c100514503642d00708210341180d42c0314005003030035400b480340703030001e6691031001c84c043c0091450024a5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 894173498 1250 894172248 894172259
    0x6190c031e0c1e0b07030b0607050a060203040b161b03260a060f05100f0224061e100e010207081e0d050a05042306031e010605210c0702060d06 63
    0x3070f107907070030080c45000c061803402e0ba0000d16803080a1740c1c0400e060070b00086035190700c4003184241c41940c2c0014118018200d8040400c1065400756004034061510b2150b41e59543e00c00241100c40d46103410007090402c14503036007084400e0389181d6142d00c07e14021026510030300307100d41080304003600c445820190340200400c610080c41180c000700384003000703d294146454040703840c4001d00c481e008100410408040000c600810040000b0000880c0000d81c034400f107100c08035200015203407d0712408a000d610301e0084102c01c5612b2242c04000d05240c0021003104080d21280d1244085a041d40503650700040c0a400c14420178248a40d02400745044405920029007000102500c4100f403201c10301c4200e01a95120080d82c00741c410041010b0074030501e12001116481c845140070354004000010030011807158401034440f4011070f0b83c0c056644e40c0700c1c0c0702503610f80102c940741810130f2a10268035400d28882d0420a400000b000200ca1038200c01c3d030040323107441d40309a034070f40c034225104d1404100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 894174748 1250 894173498 894173513
    0x60507020d1101021e0c1507111506100806030708011a100f0801090207170408030d0608012003060a0801020a08040506060603041a15040216030e06190c031e0c 70
    0x207003a01544002c520f1711450305840032030101c401510003403e0304081803841c240d000400080d03020010302c0c100e00442d407038039440041003204c5012121500b805980d64040c449518040c011f070044100900c01c1105602513002103a119500130030103641442146800150101c1c207101e1100000c214201240504100340148818072180004000c03c1180e82511200350a0b0b20101c4541903d141c0400940d851600d0304000030680303001010f416071080006400542d0b40e000000414081d083c1c20801e0019582e18074020b403c0b200d4011312500e080312a2700800160148010045501c110020100403503e03071240e0980382280c00915030000070071418824002449020098070364800d500b06c039594510300d0645c2d544071131065239003051083c00c1005804a59200d618207140709842d0341c06003013151102400c00040d202599030640c241c0118000030b109840c2c0d03080c07040440307a00c0030710036000c0710365850310030740c05c640c2c0d03c0e000502070301001a0510807020310354100740d250040c50358950341c41c000c0608a080c81d04c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 894175998 1250 894174748 894174767
    0x71a0a18060f09230d030306031e05150705090402090109091a031903021c030b100534030807090b0d06030308060607030c06051003150203070206061e090c0403060507020d 75
    0x3032401d0f84100c2c00260003a0001e8691104082d181d1210304405c0d49025405002c1c2130308000c140c40d00391251041c003c052102008120b500840407140405002003c00980c2d500c16100d60000400411843c0b0450526400910000006161180002c0e6848021808403601d11018000032001281104614a000c121001540781c10038100d07100030391140d40c007959401e6100c0000e010305207003006410803103020340d0140c16103a1029007560f0032005100d0340105107610502914440514541001014070300345808840bc040300c03e41800036100d00ca40701a1030182e00204641d0801018100100300c2c1e15103580030305080c0400d80b030041a041d0840c13901411003540200007500481c028456100402d51140c1c95040c1e02d07411800001d01501d41047d151141400c580010f401e0b4800e45104c0f18003000e8940c029403141c84c0035400d540381a100c1e941000340a5015210b100c50410f0b0040843c201c502d0b184205540120303800103007514040c0d0325529442901d038102d400c6009a080041c1242c0743c0d940160100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 894177248 1250 894175998 894176009
    0x4170307141506012613020a06090b1b0328141245070510080114040f091b06050913051905010f031202071a0a18060f09 53
    0x2011401c210345a041448500180443d04020003104c01400f1703060301c03501d18070014110903030396200361030501000039003500c414a00b20301079001e42800044071482000701c1d5080c1d0b42e00300285440d040f810b44000031300d034030901d0981605000800c850020040d40c0940d0040c1d0480c0300040c0b03070444205c1c40e00601889200000340303441c15020006503400703085900006601a00f03080200111428444c401c108a080e4503030361040c070b08442c2800c0d050010701c1302040d0030b81c00d034150216103842e03441d03005009051540d0381119002c00c490318018031400300c0c5011b8400014601030400140041545482015640c40060a80e54540d82001d610100b88440c26444040c100900340076280c284070b440815448903411400480560b6594003040000e0701d0f041c841903450407443d006100a50b1500100e01000425200443d5001101c0e001242540e0022030244100c500f540315084ac002100d2071000604e82c0041c19803420418000c040c658821144400c000c040c01042c4c0d030752040d800245401508840044c0c000c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 894178498 1250 894177248 894177253
    0xc1519050a1a04230c0c160e0c1b120a11060910090f0c090203010e07030b060d051e07030b030708070f060f11070303020120032a0417030714 62
    0x90180152044444414402d4103480028040b60b00031042d15002d003900d03040b40c0c8004092414040d0f00c10107400981464030b9407000b5100d981102440d58090039250348101e000e0020741c2c1c030025a95184480250000c1f100c56160000100d480c3c0b007400381001000b4100359804039010903a242c0301c9510242013085641e5840c0105064102140d04690b203800c10240c041e03859031604090000c11000e40da05400c920f80c4035a03045200c0d9226076680010390000d028010710031072201c00054840340700c0e0140741008200a0b240e030346084508403040e00a00001000028048244460742d0440700704280705500c9040c541c1d40010380d13424104100b605000c0b15520003c15644036000501019040d411704000321125820600c21040b00094243d6105a51400880460180035000014150103401c80701c42130358581c0e00460061891611024103020a9400d0854558143c26000280740d400415680404040032450704041d0b683e000c5032070000342c1c136444401d95040454040c0030401c12800f0709198491341c002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 894179748 1250 894178498 894178511
    0xa0c0b090f0616170a33030809040e030706050603120c0714041d010614010c0f060f02090a060914090103080d02160f06090218011404020c1519050a 65
    0x410303548042c0544602106418200e00151003800f501c0d2031030341c82c00c02d030790300ca442441d050206000806d4845503035010307009807142e004608285030704880d81c405030000181c41c5813070960311000c40030340101c0003aa03006543d4550304440c1090820140032440d00c1900c0110f203e00d4004149420920000348a6640c20b0003884048079514000c42c040c0300742c03040902012001c81102e80000c000d048a14400f203007804080300702c074500d002c040d000203042d00e2841548002c9c034004c10004540301407640c40042e10b180b900032040400548070340c00210080b1400709015081808803400100725003030b150f200c10003149000204105144100c0403500c1500e20031a4440000c0d0300d191100e404621070fa13100901d066500089030701c0ca001c4108a0881880d812045015078040781e881c101c4014800883d00743d21440c680207040c84444501299141654000f054549122007018180406900505010081c078019501021201001711288a22179060740407000c0d014407080c501082107a801400440320355040c00c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 894180998 1250 894179748 894179773
    0x140109080304200102120d0f06050901031202010c0503070e060c0106030c0f0e0c0a020d08220c14040b030c150903030d09120801060207060827010b040b0306040f1b0801020a0c0b09 79
    0x1405c0d03e07c8081910b1010904042a00d8038000601b040d4109070743c44489480040103100000c946000c09012540007000081009182907401d0f00040725000c1c00100c01030356083c084e05144d400b40000080f400004580151a03135a45101060247c110250081d00c6810811551083e0060140c215100d090803e240442110000351a09402c0809405004422000c103494a00400d1198440e0100d098444c0d0020300d54a01201043c0151140081070246803481c042980740c40d20510b0b8071610010000d02c031280815083c05141da04141c1d004120320000e01600c040ea489c14001080c0c1522807001c00500441030f840d000d441c03140b460700f6500810102d5401032052030b800090600c02e603074203414600300550700c0404d4420010419414004101c1e045840044012415007003050070801c2100d06201040c0c134103051580d41d10003241c2c054901244003821001140a000d03130a401080c0550384486c043e601c544014cc03e907400138a1460000308100300100c01c0c00b10070500300303811218100203811008070300c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 894182248 1250 894180998 894181033
    0x108341b03350114031c030203070806060c0622170c12190e06160f050f01090302072d030503030604050105040c05190306050a0b09100206010e04140109080304200102 73
    0x14060800f00600c0700301301244c1035604111140400300d15040282141034003000060207508280da8010206140d8000b14002d07240030b006982c00000140f00502042e660800341c0480c140140c1c014074980d140c0f0003000d9010504d01030302403484400d4a84842c2c0d41d29000310005103003040070702c41d022403030009011a824050b180ca46600b8080704520700038141451504c0050034134132416a941400c02c510001e0182006490390032554428010020340e042c50204100e690300b82c3d0480b00d80240141c21004050110810040e9000c0704415088241c4030080402409145181c4032a001a61527600200400c0031900d458013449002d002c00369410b022505050001510034024071450341c0302c403002c07a051074010b103200364000d1004102c018500c104d055642e505000040c0d03c05850240a0440041ca6941d010b00019842d8100c80f014407400d111075856440d040f82040c540840b41b80d0329503d950022002c00e0400d1301850145000d0034501030307410440e99610308803140089070f05040d90071032480ca00300d180b801c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 894183498 1250 894182248 894182251
    0xe0712050717010b062a190311070f0f090c021203070c0213110d0e0a0f0311030d0203070306050f0f010909021e07050109020108341b0335 61
    0x1805010b01206035012019030140c800903020303d403c1800458044c01101c85902c91102580e181c01d03000030380901005207103803101d183c40b44141c213152151011704000f91244401070041c1040e039040d61607240d141c00380b803031081d2440ea00100070054002c5003444980458481d80c50200450300003030007261088a01641c907800001d01c65824401c0f400847d10941d26490716041d00040201800c200041c000026a1216001407440f4590350740b0300712550b03541c00c100060701a50aa000701001841e0009960708032036040205000d0000b2b070009201a030407890640c0040c43c0507401585010606900300810301146607070402c00300c0e106028408245203541d0b000b8550a05881c0741120143e0380c0c00510070700d101350440120744c4200d1254001860b0f41482010360244030304502c00d80e50b014068842d19070b1660380f0741404004002d204000800200024403264211503179003081e040421411501074607448040f001980280c0200e400001c840c0c40e41c05080031004000c031010316071043d1030050440320400b81c00c030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 894184748 1250 894183498 894183509
    0x12080609010b07120f021905061006030203090303131716110405100510111b191d130f0507090e12030105040c05090306071214040312050601030b12010e07120507 71
    0x1c00b00c0c1322103541c510030321200c0305d413401c7c2e604a01c2c40010940307005651920b0494503100130078002500031404504c640200d82c0249070303040c001d6055454000c4058048100d00c05e080710030030200c0052682d03244059001d810841103042da18402542c090408920001e545030030070b8420303403a103810800c02c1890f500700c0209441c0240c03111090b400c21900180c0d00d903003030350409841c80e00c00c2c2c0504102c41100d450b2011030b890310540382001951b003003410300b581c010fa42d8021502c440c05100360910301ca8101c1d0b454a13078003109035881680306810b1510b070f0302036041c41d400060f0b8040d007014a086c44a070040e4042c007912000ca200003030481c0c0055084c0c50b13000d40410b0190701d10851f1250344660703400b40714900b0f41d020364600906441c154140300c40090312080c0504649407c945c06c0441c1444600300e0490464400c5415440d00700300441181500d42c014100201110305241e80c80710108041d4658005108010f08110300000d182d80c1661001ca2030040c8590104a202100802c22000510042400c070100c54 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 894185998 1250 894184748 894184757
    0x14010c0b070212041707050301060b030a090201050d090803040b090c011d060d05091c2313080304090e060906040c03200607110418020f13060312080609010b0712 71
    0x8031000700c100d060070301d03250070f2180354a00410041252185c41c0c0c4036018500b0080101c40c0c0340b6a48900385070a8911511030710300150310901c0000c05850345a04001481c510501d0003030700c0c0120044030041183c109400c25107154101004000030001c2e15a8100e804c204040001c0c641d60013400700003888040c11590032000300203000080c81c5540c90345000d0329101c00c0d09003c140f004c0c0c40d203120865552407815140341e902c0c1034540790320107099025202c60b00c4444c005a114050810380c40c040d411095100c0c8a425602c00d658040005481c0000d001401c0a42412100070a03046407140103903140010240400d0038582101040c000011a4403407480216580440c55854441c07992214102d80d103240b0b41c0480c2c004e54002100c0c01008100001e80c0c0a42d00200d404104d01d21a500071410240388015000f90441d581c0c001c82d469600e003540d2600028600301401007006a180d90390700714501400c40e41d02001c90344880074001c407498041e8030a0f01416950005505104007511075003001402c002c006410b11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 894187248 1250 894185998 894186001
    0x30b060d020a1a0c01050f1902040b160f0c0f090608031204030c020a0806040318062c030109080f09040b01111b150307080f0709060212032e06080114010c0b 69
    0x83d0720081d611000101c000800c580e20308003e840021340d6044500b0341c04115110030002022680d4070a41381030b10200405103007071500940c890580c140600c5020340b0314104e5607440700c0006008188107400b6240d40b0051260701442c20349101e003564403a4100242da50000c2c442192124001600d50398010780614250441c0303062800401c11b5a0b6481d0426080f0340940c4d4108418075030405038423442c0c0010940b100800d144d58860071500c965110006140f80d02a9031402243c1c88000a5281084600100002280026a2380e012280d80c010800c400800c54085903007481c910f0184544150481d007800c1c030105200c0b09602032901d41840c42c246105102488076045202d4480f00e6100c6d0700124600c00c8141d03203003402e04003d00300a6084425802152100c1c0004004512031180081141c90f241c004020048024028000c0c6410080c45400b0154803009542010b8084032644226000c3c0729000c403015134100324008000707090580000850301c041e002e41c80b04c0b50f40e1140300d5038502900440c2d440520b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 894188498 1250 894187248 894187289
    0x3080a1a03030705010b011805010206040f050f01020a08060406120503121f0603020702210c060304052b030b011d10021f020405041d061602030910050301030b060d020a 74
    0x44400c08151990548808524802044070541c40b41e010014242c8078950307040001e0107a03422905240c0180f6005030882c4010030000b50b07603440c907140b5191040303094410f14015040e500342242c0101040c0d20015884005000181c1080c0c451000680903811001000c1e1a40782c8485a491080801210a03200c1c0310b4009450010000c1c89542c5c0c00500b80d800e410389540d0f440700200a5000400c0c00d030710602211005124940c0000001d118000c0340002528884103031404008180d04000c2c000d0f1028051584c070b03c07840341380c0e1040300c5141d41e01e040400343c80f07112000350041c2256100380406041c010f80710032602214115817040581c1c0d141c02c8a0320a07181d003a2010483c2410a010701008503001501036001c141c041035006801541d8040e41c0070450348000c8800040c0340300e849103507242940c100d0002f0800c1d10819100c00030b5440b2150040701d00e00301d000e401180890744031184040c00940c01000620401582864160300030800701c40c0c801000c401c54002842c203080314450401600180103d5210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 894189748 1250 894188498 894188531
    0x12301306110c0402070602040914240a05040905030703020f010509060a0b130c030f0e01050f07080405070e010b040e01090b10080901060e0408070b06091005012a1412040303080a 78
    0xb6099001e8410b5480b42040e10303000300a50403500520300200d040240c81e841d4200d48008845c403c60094064000100000301c01e00e42010030766141c0d9820081e5402e010034a512203005002002c0c0c4510000e5507600c590f410000e09201c81940e0f004c40690401040c001c2844001820940098000b240003415250b4800040c204444220a500469003841c40318210306405602c80680400303074403814002404c07800c000a08844040300c242e4440b048100100d03555a10880c0d64652091084085130002d90300c4803420718038800242d0202059040015051003a6020500b555004180342442403040583c0b4000145c0c001180c8100c0e001004041c00000e4907420003504048010310400d0b9850702c803030620b410078141b0f552202c0c00588030364000c10081212400e044402c10701c6058a130100b41d1526083c400115030410340c3c0d000e110403003100030102a5090085d50402d040c1d641c4244140d03051602d00c05802410304980210640e411003040c80100086500301c0f200691129070401c00090840035155100d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 894190998 1250 894189748 894189763
    0x3060c0f08360d090609030c1404021c0905010606090803090415051320091c0f0b070f021b0102071e0801290402070f0308061230130611 60
    0x44400d07002c540a003512020105140340c1d035580310340e10342c1500c684036141a20358203082c1c40014001c054003130007041888104080500c078400014005807401c520318506a1035501c015036142202680c3d0003451040250134401c190041100e4103000760403528016810f516401407078500c0d4080c03506c4820340901d0311148100100501001400280886080500c00b8000c158508400600c41c550b443e003422441595000d4941909006190010f01c2005503e0584220903001040f02d1000d180090100055103140c0040c0c4180110303540d404074204c50080c001d2416180071400035203500e1031002405140d03800306a640903141084903174900c003103907a2080351015500e540038a502d03500e094200c0c1d6110020006100c0b5070032000846d0980941c1080c1041304030b118480e0010801d0045c280440d0009003d14040b40d4400c000401562520b02e161031703031505080700c0300e80644000c8403d520460560490820704020a0412000541800300303485031040d480c01c403070007040d061106050300300b505841c04001c40c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 894192248 1250 894190998 894191071
    0x601030513121214060d150204030203030d1b0c02060307200f011b0207060509040902010e0d1407170c01110708010606080105090c0a14030a020405180103060c0f08 72
    0x102c1c000044038801080020340c010540412420200c1001102c40c0341028240a61001070440e04840225500c3c501c081354249203442000340c0038040040036940078000f40c41800c4030340078049002a181008003a1a5a0140d01c900520140900841c0580c68100030b499112550303080c5024070798511380741c441030210021034080b0984141c100a2642003010742240704004003441c1c18003020940d82c0320a0f40c40c0d5009021b000d000a209200d1189149400d4000c2041c050041c10500c01c0380401401084840c40856019a07074150308914007205401d0401200b00180003c0c03402c01e240003c2198080d81301c040c1401d07682d0402c1380000030800e0442052002e5001021920020000d11760f4905002d03102110921a461203141800009107100107a44c0440f04006495076a195000c900c4900d8001c09400c064404008241d003407201243e9600c9408034090a894600e00020881d0f1462411506a80c000408030040000d445c007200100c41d000800c154024030310380143d2030b040c0d0220301d00350b103c0a16034020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 894193498 1250 894192248 894192263
    0x3030403050a110d0f060518010c0e2809050a020c0316020f01111e0f011109090703090f0f020f0907080f01060f0e0603061507121d01080601030513 65
    0x40000008000700003d2050402c4240300c0010030401c40800504000601250039803130082001480c107a0101c5d602421680100c0e000e098080381040c2180d501071104004554140072000251402c240540a840310604001d141120030305142039040fa41c6118249a480c3c41c5c10118114910b150107907a40046204126500c9032854041c281216040113000d81c02000340355200a03103540310380d100b51100614200141110403021001051080030021840d03040d02410501c640408420302442142d85056141c0c20740b94140c1408022050f48040c2c4100c1c00e2610346044940010342840717400c0302d82c6400c00c0040390005180d0000c62000034111306801e60007840701080009503900512094029483c0904540b102da032070310f50603100d203410484030002003610700740c500d2914641b10000f0369000c08050003a1b82146900319000c600d03a0804c901c00c8900e40c40c0641d941000592100440041d07541084a201c907a0b107240c1c002801c0c2c840d0140040703040640300c03000512070303000800780c16500f25071103650b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 894194748 1250 894193498 894193507
    0x40312080a0e0c0130022a031801051803030c1510050d0219091d010c020a0503040918062a020d080403080a1b090501021009020a0608060a18090c0905040c0308180303 73
    0x10401f03001d00300980000740c800720b0020800b03100100002038a002c81c81c11034011444401c3e0100545c1d10380c01c04200b80148014040c103040075520148094101b0031580e900410320542046e0078900300260042000c0c100d0510444100300e81d0b0744030aa26111544c041c3c4a8061001c5084681466140107403c202e03401820300d007007282e42545441080b1052910300d0001c1203460000481261607801d81500541160300c140070031300039a0031543c80040d082e0001c0c0d20318008403c190340d42c48160b85d00030251003e03802c9642c00201c0b00c40071001458030041003e10282c102c1844110001e000e804d0090b101808001401000994002040c1e0007951000e940b040c554100ca070390820010b2228000d070203414014081c010005519110b140626004140e000b00409211800e140c000c662074140105020381c00160604001400b500038038078146070041480d00072440107014140110b00600304d40c0071450045c501001c00c001310705101c00700e8050b240c1c400103242c0e440c1080301840194011030040e10707505000019 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 894195998 1250 894194748 894194767
    0x50103021b06150a0e0f0f07030b13021809011505090a0b0d05010801150b1206030c06371725030506040f020f03180102040312080a0e0c013002 63
    0xc0e194004880c100c49180313600c1d80702c180c1306004403002c2e540305d0008031040c00400c2c8500300c0c2c54135003035121f4507a140028000308000300003541c840e01c000c0200031040d0700103484103c0003520303010b41902881c02d40309052194035000602060300602202d6000f04a00030450f81b4031a80c1e03440c43d03c0c000304801007800d41ca071b900259900c0000c0100380700d040c0c500c0d842c02521400c4414003440d15405c56096002440c00c1010307a0301b00642e01040140b038a5850700400d128240c0c141d23580b2019100f0068501d82030f502c0c10003221201c0500d4420460288031185000d06071340c3c03407281c0c04a0402d8101c5030b401d100d4066500c8601403108105803299050b0b0303030b5041ca0380440d4140b503403552040d481100121020b1180401c507820300c000301e2058154000081e07000b0400250f28100356a14911244c24101c001032803e5601c0d100c0c02610b0b070902c030a00e00012510b20520601001038001c1511140500d005494080000c1002900c441403d001e0703d0308030b030111a0403a0284c05900d218107801f411410083d950740d010303403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 894197248 1250 894195998 894196021
    0x1b0d060f06030c0f020c0a0512071a04030605011d060f0d020a0b120109060b03070c0305040513091109010602190f060e010b19451a0118050103021b06 66
    0x10f8610004001d02d0750388200d140b0001c2c01c081c55080182c41414041d04010034031118071075443d010301c1030740300384000010039000c01e25060140e4484100300c25210350951074440150741060380000d9640414078086006c07810a50346690300800c1c00c4a5100d10f10410f40301142d0142030107803000e9480440f8000000e085241140141a4a410842c0740b401a0303884190700011a070650148805940d014030014009900070162001003074003030704002c3c3c1016580d40000d9001c520341503e550840e91111070210030040c601641640340e40082300e40c07220560610b04025070b112010544006001e00c001078041c248100072205886094210105119101c411101a0f01a10203094410301501024208071101b1300000004016142803004207c0c04941503400300c40202000300340340141c420308a0b1402c5034505264130380700203080c4804000c03038500c1002c92070b42c3c00f0460060002d814030904080d101611145c10400314152102400c0041e12051080c048250311a0711019264503440f4043c10300c02c103003025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 894198498 1250 894197248 894197261
    0x20a170907060e0109030f060518030f04150806030c040c111509060105010c0308010509100905040b04020108060f0a12081e040305010f110a030b0402130f0305010c05031b0d060f0603 80
    0xb80d00c61841c0320600300011102e00d9550300c0054102d080b404403100020f025034101c160401c1d500000c541c4048603c0840c00e0540e400401c459000b03070310025040104d100c0240301800c0100031403d00c03440a280070070100340c407800070107010380c8942d540f007820b0100c940c060500e540c2c0743c0c08104100c460592400c40c4e04052410140c0380000c4030300c10700c00002581e6114902c0300036400d500d0398505641e646814240b0046c0103000c0e00c5840125800072011841041d188203080c4070b60b00481401000b400c0a00003d059000042e000714010546070004a030f803502d600b25504111441d82c51a858141400d0421181a0103011041c0700c09450791715043c0e10f4a10000003a00c180e81c000c000800c00c0020000c40031003100c124403c00c901c034050a20200b0301042c000c0e80403100040c1c0190000d880c040401c00301d0a000103035500154a039042454090081c1700c0c0901c0390301c460f89000d080882c91801c00203031420060360609021200e02e0400203c01c0401b10664100e00000c1100c28031560505444e444090060881d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 894199748 1250 894198498 894198509
    0xf0c010b0406090c0c120c080309160503160e100504090507030614070e061c0608010606031a01140706090b0103150c0e090a0c0509030a030221040f0504020a170907 72
    0x400340d020409070402c0c4260780880c41180c4031103041c6006076442c00c45006400b04091b0521441c100c90b00080f0b162140114032401c9010040c15000103140e00e948e0346016245c100720300079800444040da1100b001c6010b20240e0b80d412403104139540d00d50141f1540003201d0b0700440e4105050094100c01c0100014101050724440c01042c84814100c0700b00d100554421121b010005685010710911410801c5c0201092000c004c100c841c0902250010340c00c1ea2801d5010b1000b6030340d0b03910104134003640b502c0703001345103480c07018444040e00010000810301e0040c00410b420320640000d00304100050f0b81d02403910103a2040900c411503035a030600709440700800f1541c61089041040314003002d4418800226407450052002040743c0b07070200810001c1c42c01a40c0801032004c06c00400c0c5d8960f5040001f600c0c15880b9500419141140542018160031290a00282c805050005010307a0402041d240d040da803050354016164140020203c0c0c445e0509450100282c00c00c01c01c2c003000c44008a4504159074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 894200998 1250 894199748 894199751
    0x1e12020c0712200f09090f070608150406150503100e01030602210613050606090a0f05030f03161e06090c030605060109180203040f0b010e070e04090f03080406020f0c010b04 76
    0x40010002001601c0b008840c1daa001c00b400c1191280c070b151580045c3e40164602007101c0328045240a1185082c209410100101d00c1c002e042141801100050030030100c1c01355002d01c43d00385402c1c511184142034181c4002808004000143c0d0503007202542170081c800b45061200f1940e6038200704d0001c0d0310410148040203152100741602e449511182409042e016210445503003580c03034100014000605160b901660800540072f2503070341e01b0381003c003a0054240c001d02d8a03180c00101071402c00143d80c00c0b440c60b002404110040c1c801e42000d411340cdc5410040751010101002800b0410000f60031006180ca0300d007103a481c043c02035084584007a031b0f11586c0200900d4480c0401034500107598410100004405040101100b0460700035503009031007070300706100c451100c0d981c007046200260406405840058100100681d01c4610303d900e6450a0b1000c004403403041c0c403428a469460030f4081e0070301540ba408074041000690458941c1c2c0107001c181e0340c44240b01c4030028083d20f58040705074400c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 894202248 1250 894200998 894201023
    0x60d260d0b06040b2a030a080618040b0c0702010203040e0f0618010b0703050c10180312090209010302010315050301020a0e03060606122404020304211e12020c0712 72
    0x1828040e00722026107104d05811420000401107242c0108145900d02001a2203500b22010041003040136080c40c4c0141c1e00c0341e085502e0484240001009501140500745d0241e80611000c0b4130186142c5811403240e81c03c00d50b581b2010f00060f4038600c216440500e8641e044410071060303e0364100468081c8408031880a03030141d0100440114281c01c0c05011940740b400c00c65200024021001010074100050a540c90381c61400501030488600d5281c003540400581c1c400d8041503400999140c078007107041420050a441500461445a8140002814540d4640881c0c200c07190a040081c02448002e0003955540d42d0b4036402031a001c1080340580c064414035000c1400340c980103056030050007100b0340300c01c07960b03884000e0b01205030f41428080703250140c0b00303c40b030040391250f00046105a0050750012b040c0102480e804c071034100002c07441c0c000c0041060036040500c2c132044008a240b0058a060201c0b11008201007000788141f0030301c0607051041420001d684412541c4a60b0010300030003010195 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 894203498 1250 894202248 894202271
    0x21040606061211040b0d0912051b031903050a09060606020c031e03072301090305130b120621031b1e1c0c0f050a0203190308060d260d 59
    0x283d41c44015040450441400240202c00c0507001511031503508240c00300b801d01203030f150034012500070072031400007480c0010fa000c121400340460000100015000714585800048600c2c01c02115058200415071240e000c504804016000020000c0d0003000422075640e83c0c0a0203942c03150680c158900a0142444c00f428251031030800d4804410120003862a003401591000841603491040802d0503207041c881081d042c00034400d40032214465140c0b41d41d10031000c2000d0348200c407580c0c0214030403441006125104c0c000d80c03140302d8000405603001d480000c0da00b000c3d82401c1c941400e00d011540300120b040038811100004080c403000325801903400c460542440f216007814a0340000805a01c05004540400da841d10700141c600700506e0600c11040481eaa40f840b46c01d00603030f0070303141584041928400d5103002d00403005201c000789444034402c110b035a0050181c86009040ca48107899201d800300601801e5004041c502400321140d40c0460508454809079421484840d40c8591030306030352540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 894204748 1250 894203498 894203501
    0x503011e0b04020435030310031e03020a0320030a170a0921051204060903030b101218050307080309070e0606040902090301090c0906081603080f210406060612 70
    0x291101c00c4405503070319514843d41000070700c0c2804000029170011240e14a0b081003400a103008150035170440502c04d1840c01c00c41e202900d282c1c102408110040b0789640080e8000a400105640c54101a0b40d40b500e40110103450703030741410604400b40400500114225400048010941c81c42c0000300d84507214281864102d401900300107026450031803110102c140098100c05000380e06190481c13904030410340590325808c0640b02101c0098441102074100b41d01801007080d00c070015a5054204a81100010034800051032110040da43d42c000d0301500040181603004680d8200342100e6079004145400f201d03070742c000c46288c10a80a030032004544800003002c0d050061710004e080500346410800854000e40c40059441d502d0365903514a840000c031594840001401d18140006006181c01901803c01540140139042c0d103404081c01d200240c048004e0328142c0710542100d644944901004400c28400750030403609507004907040108010f02038105c84183c8010f565032290340418070441c0d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 894205998 1250 894204748 894204757
    0x30209090f04032c0d08030403110105060312070503040e040807020a15050a2a061e0207050d03110d060b0403060f0207030903120219060b04050108030c0c060a03060503011e0b0402 79
    0x600107480c107a005810300d440c00784410680b10304c1d00309008a00050303d00280c403000003980201c851030790120030041810381080307090b817100400718001e000d00d00c0e1110000c0c4c3c1b20f80e500361f042c0080b800046102820b1000070070954010b01030303850030402c2070700341800c007030031b09410460089220703440352040801c0c08800002811004030307440d183c2d1400d18000d07030310648646941000e0b10204008200c403001d81c806046041205080c01030310001481c84c400540c02000281140e05c4015203801041014000f6400282040c0506c43d1440e00040e01e40820b610729105206060302c502c1513508156000c10308000c210700400841c0c1c400c002c01c00513406010038110603405000c2e07000d0302081e104041040424001d504007070780701c41948141c2d100c101d4111074641401c06041001c4da81c6654810100c401c500301403080030302509903080210304140415032800c0d41ea05480001c5801042c000c24900c2d0317403a002e40c0241c0d01800d4000c000307210109004840c2030700494000040c07640682001d031103d0aa007001d20031903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 894207248 1250 894205998 894206003
    0x10e0a0f030305190f0b0306070e0f090c1902160609050915010908031b070501140304080a0915050c010605042705030c03120106080906010609050f01031b030209090f04 74
    0x161106111074506900428009240001d0440040405082d07201c05100d001e440c05600880080e2048601c001e040c90b02d00d00804000500c40c0d20521340c00319507145400b0411201382144d88a01c0c5694080d541c1c1c401d401101041140c8800c80303800d1840003600403c803900740020818501c3d0245689080c100c90a5030180300d00c40e001a0f0083c0440d080303040c020812282542c06040c0b8820180e6140101403665014165404002d4592147e8181000d01404064020309003460801011240c000078044d4510003e400104078090004004131700c0d5008140c0308000300b044010307540c10624016005400c2d0341c00340071b00780c0d01c0e540b82c920007142d2864688500706407500c40c41901100c0480044c0030f0240e10040f00d400303070b13402e00c018410080903d404100808417448545011080b0354036100c0003420781017002e040b501480d040100144421035000707441c0c00480b50101c400c2205d074158a00164002c00f0280b5088000800390201c00c0144e83d0903800901d20340302d003550382100d42e580e0000a06421601038a00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 894208498 1250 894207248 894207263
    0x120306090406180c090204030b0606030c0a0804060e03030a06170610090e250e09011a01030b06210601090f140f061605060604051f0303081902040801050603010e0a 72
    0x4100418080c1d8000494000c080c0410396603018107441d802e26130051a407007100d05d1600080c0a0040100100c469a0046016a02c060560501c040800c030300d4064000e40004000082c0300060034803005800543d24840464217a90303031b0b424010385160140c0b90600402600000c01c2180302c1c448403000030524803030001c1d600d07442c01007030030038070001c000d0118080602410310484052500d001c1d80c2c820901615440003aa03010710314a45004028115002010414a64580744402c0c20841170745c1900300560409180001c1c0c90100030700000d810b4082c0108900c0342e032a280103040c038602c03e008000390140400741c071410400c543c0c402c05051156160b0150000c11b00c8035502c80c84e400c1c10503500c2c144081c00001c00c114240180406516110b55440c0e0382611994090802c2c8200b0341014458240c102c4060303942c941b40316500c21208805007155210040410000b600058a00409009841211180d2041c10f5560f0b5585840d040d0180c8820360b4841d11a52801c81075441181c1c0c0010b568080680c030466 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 894209748 1250 894208498 894208501
    0x7030e0a020d080a090906080c03070f1a09011e0216052e1b030f1706030c011d0307030b1506040e16020c041b0305010e1306270f0512030609 62
    0x2903c0300541c002d56880c00c14070140803400b16501603103000e580c010304184001404031088607010103142c00d00f50341c0540e0404030074110901241c030303801012501414101000f00c0d0740e50044070040302e40014800380c042004207031881d1880540d070b0200303289441d4203094002000290b03d550401108a000c1c0203005400c0b00f40c2c41d45c0d5400880000d0041c2d59030307145800c0800151160f2050f040e81e03100d6038401240020780142c801c1d4484c80d08a000d0a003100315102000c980c41c9003a6002c25601d402c00c801c0d0b1814010040c588a00040f00308800303051003203000d02612159581c13407034140c4003100e00355882d40c01d00c0310142003c10203080600030341d01221640c100004081e10b4a00700e010351020100942030450180d205854050b440382d001d03100c89540d11071201c0070b540703020303040007001c0302c0d0f068000e85144442c000620040d00c0d0708208140c25150048000600c10194005450485006415941c0a02a020071705410300c03006080c200010790196041e1009420030114040003488200c5502da442100b010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 894210998 1250 894209748 894209753
    0x10513030c0507150503010e0112080409020309100e0706110102090907081905040b0106030b010914060a170c0403121701030b07030e070f0f0b071509080f0304060507030e0a020d 78
    0x10a2503101c10302820644008644800242e0741142e02602c4801c04520f0020041000c0807859850fa8010202d0ba19a0208a05a55509841841244160310500c6d40100103d02d4015003403244024031215401d0130411004202001d0380c461035188a10400700b078a070541422620418001c480c0c1c5034500515407480c0d13564804050b10001c9026151030810b55085020341150401c0d0300c00c49000b64001c3d11081c00c01d6141650003015628075211b07050400248203000c001c11070710620441c20200c0100c403025110340c6040c0046442040342c2003a100300540750b41c240540c80c103802c230040c030503a07004c1d803041075070b0103082082a1540c02c00340f4805242c081c009401000840c101028540c1c1000c018500464002c00d15015246803180a402a03110404250020420036100800101c01881c01c0601107013040ad0a8540b00340109601031803100c07464641007904200681c03001103851807a4000c82041c0c69003414245080100b4040b100d407800303e4540958074065441c0051140720721035009028404414069 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 894212248 1250 894210998 894211007
    0x70924051c08071707111c060e03130311030c1909020a0519030615030c0203030a0b0a05060d020d06050a0b09010f0203090d080c2b2607030b03060901051303 69
    0xc24141c0b103000c018808000001c2c98010a2074041001d00000c0c0d44888a5007002c1a0342c10841c00032610820940e40305a50170f405517030034914043d0b040346000030070b1941066424154842d074000c1003a0580704010120404c442d100041c94820f000354112404042002d007801402e6035407140d0300b210321110700010010142950000d202284203031400b0783c103112007c08502c2964040704224804641c5408003403000307078141d20800c07240d03100c1c038a0107101c0c600301458065124840944009a040d031192160711441d2145640c410041002500182e6280c8110942c1002908003203000203a250400038001a0343c174083c0c80c2003054030701c0070b84040d14045a400054030700d421009500b4080d40824403d50400c3ea940400052006014421150740d40081c482900e040c9410311008039002080c0c1e48090b02e42c6051010050320a01c51410b22445d07442075484c4200c3c14000c4040740c90700f03a41004040080c1d07a41e250704076880c4400c0680c00c031841901d420780c005003643d80c01c80f42003121081e20002e00001c00c0c480c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 894213498 1250 894212248 894212299
    0x20a0611250602040e0109050708071d01080421110706020106050604050607060902030601270c0215090102040f0b0c1603030f0c1106030a0207020a060206090a140f07092405 76
    0x4080040c90f25580d145da04141e20360903840610318680d00d2042110241c0c000105503800030351440d00f01c200b201500d4002001940d50a413130f60400c060800050100085510049030081201061007400000c00c0740041c004c04410041030300900400f080081c416005000301c000345e5200800305400c090030081800465044040c0a4940b10b842e40744000258409100080c040c101c204000340b0a10115032004c06d880d55540300305680b40b86001003203094568003062840011403035000c4050386031039550070507000e400380d50000140100fa0001c0002c020701c1c68002050381459001c00d4608241900d40048c0c00c080321848054041410100c50490780d0344600841d0083c1481011b1a80480207000c0100381c0b00c1e0001c41d070707400b5003a034009540e000f540b80480c9541c00403d207920050074940b500001441c0c540e00003000c000c01c81c407035061780009510320a20000030540d202c00c2c21500e0382e540e280c1c80341004c0c00140541d09064404828500050002213011038103580010301802c000c0c803802040503114240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 894214748 1250 894213498 894213503
    0x206070e130c0302180a050603040609030c061a0a380417070509090f030418060519060f03060e04020f030102041508040c05040e1903020c030d020a061125 68
    0x1910203200e1696840c1d4800c01400c1542a038006803101e46504804018411030b5400700c2c030900281008112130740d580400c80303600c10351040700031400b10010301e01503c1402c5070580040003142402005604422031000c14224008200c44660b125952a10f003083d032103918461221002241031000c4810b20b8418a00046440544050358942036031220300348110302c400dd41091464000344003c00c020300d44401c005401c000703858050520710184454040c1c6d80e104502c180f00a40d41c400b904402d07800a6a80014014000030300b600c07114040301e2900c2e000e1038113580140c40106601035401981d01d0310a2003100c00b540c40b40300101c04207440341c2d0200710310030010780e000550640d001c22000c1845103e810700ba0300506010748403203409040c10300d0400ca49111a80016001e00c0c5001450351a414002403240c240101d0400003842c0780855003070403403c182c20780ca0866094450309508e1520941d00040c181c482c1c50065604001744000640e2100c1c0f075202e070b402c00712040b01c40c0203c070704041c00b01511012903191 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 894215998 1250 894214748 894214759
    0x3090c05030f060a050a1104060f091505030405010c031803121d0318090c070813030c18050912300414010509011118062203050d050306010206070e 65
    0x26a124006490060b00a2007440769800040031300038103184070300034542c200c10210403d0080400d00a21004107005600c191010404078030000303000c144c050568000946112200400084c0341c1181c0a07000e42e1043c0c030101c03030a600c0c0402904060748648200c0c1e6000c119200d44a01000d49600c08540000c0c81c8c25060f042c899031000304d03404540c112801503442041940141d03840d2000307000308219640c2c0d41d150303660149240300700300006a41c042d0116800c0e55032001c0c40d26254034202e40d100d07220110b84d400090550402c1f280204100e112220074203850100c04001f40946c3c2d50342c002c1e840d200d00e44034500b681c45e041c041c0000c0481808424200c50700c50840103056070301403941c41c403541e080101901d00ba15800c40054041c40c039881c2c2030041680c4640c1d010300038401d0f43da964805103000e2140518000414004030308020059403044200c2d80e6020401813001c080e182400e15421000c1d0b0940700031180d520901030342040087c01481520720617030051300035000e50359442c5001e40391003039240b800304e5008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 894217248 1250 894215998 894216023
    0x4020c06010801060302090a060602072d080304180209100f020f010c080a29060d02070f0602090a0e160507060b0306040302100b0a081b0303070b01080303060a0b12070309 75
    0x6010004280201000000030031290f00c1e60041c030008450107803495a4260610328140003854001440c0400c80324400f101070441c400a10030b40d400c2440050350310444110307616001682040003c09403040e00e10f4120f0780c0e0014a16010010102e200780340c0c210b50003846190441c00c2c158007800c08001a1041070042e1524511010b0f5003500b142c40d94800c0c00c000c42e8a003428010030104921070b00c11480c01d81c000301071807051003031080306210300484a264458040041c2185444105d0340585144551203403000401c9516441e045011750070140c1524002c0003144400644104c4048101c3c2c0200040100040711071400c001c1142c0c9a8404481503504603264260800c00341c0b0100080d9104602036805070083d00e550007007180645041101891007608031a50a00c000351010171090f858841c11006034150404d00d602182c2180503881010b40010340500c0000f42010000c80254890b01c41150301c0342002d82c54000407000ca00034004807090324079036500040c910a001e907000b94540c1c0e029080a0541 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 894218498 1250 894217248 894217267
    0x714120d02010509060709060c0b060103230a11041a030406021303231c181215050703020703140c070b4b1b030a05030103022106070309020402 63
    0xd0151003210140141e65900c20080007200c00c0c407400d0380000c503600d05602d80600d0448014170208610b8009000480054003040c0b05a00030b5000185a5500456106092080c41000c195010044840315211814040c544c12105038181c221030544840b640300781c0c08c0d000d541800303600c2904028011143c0f10b6003008010700e061302a4950b03a0007144103108105900415011181190900c0d11802091307910100b00a5411150344a0b9200020300c1c61601c002101c040803e250720030040f55120b42010215000c81c007052100c00c0701c0401c0f5201d054030091100761030b0184101d04034031548401600041514071408a40031104000b040c1c4460080c040350000e5441d0201c1486d2540f290003800b50040c5c80c51b410103039116040040c0c044011207941046400b41400c2e45000c18640a81e62040c08410009800001003049201500100e0541c2040704c1d112441180041c0c0194401c0c00141d1180c103481003840c418402c44004400384145074005860241c4a4003000d0f0041d0440705800c0703134495001d100c0e0040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 894219748 1250 894218498 894218503
    0x51203070803220b2806050312072d0b1b1c0b0310050610080105100f1e0c11191509050d050a1217060904020105090d03200f071412 58
    0x78a541200d05d80880040d41580408852100d0980d030302c0d05e0400320304000c69500491038465003070b281a05607990703018a180072880080034a0049000522a51045000d9801000c0c0340c3d010620a42d68410507440b41c0388400310031202d0041401c1c0ca52810401d50140c2101c0c044034030481c0206203800300d031401c0103d000905001182c031805000e19650410001c141c54100745004a1344140d0602c44507550400021442c00030083c4440c0b803e1043c101000c0c10982e101e0502c2443c415010403640341c100d20b82c190010300c10312040d141910602800300e02c01e011342c541076456804009aa401ca0008070b0700c0c01e20810750107981d881e4418107200b10b49400244a0302c803038031040c002c18801c070090001c4594500d480625140440360700020030207071141480c801100031042075000301086840c880a9513075480102c1d01ea2143c0d11a564020000117082d10425030010035029051180825000c140844410515603503c40b00400e0f40481d80848400c10243d50308424080f400c003000343c80c0440c2c40c0e41480001c0d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 894220998 1250 894219748 894219751
    0xc270d080c0c0a060c020a05090c120114030705090c07030c2102010b0a06030506150d1e0e0106150903151104060909061d0a020313050d09051203070803220b 69
    0xe0a4200910b149401d280101d809806040c00342000d20314000d698000c50501a09802031601584540001c84c2e805248041592a03840d17445600b000c4968441e0403901404002e0342d1601d01038800c0c074001140e64a01904c0e59441045850080c82c10101180c40403946140b0030b040542e481441c02d81c000700300c0442d82c1a09660389480e0303000462a00f85020520038030340740790341c059010146047c00b402000c1e5039130400348aa03885c100b0003507915980c02d0301741d410090400c08168001c00100301418003580700c0c55040032290405690007002300680c0e030000603080141d282030300c0000a012103020700000740040c01c0400e001d900d090000078141202a500210755000740c100c0070200b10009401c015120950180c1001307066020000c80001d908000340091000b00a8402180142c0200008283c0f46da107005000007580c0040403107442c86000e0901905000c22405120f0082c4114024030b24050070020448003495800132a051455503450104900000011640484aa064014800424415180355 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 894222248 1250 894220998 894221017
    0x9040b04020d120903030809061005060f04081b041503020f010309140307230d0c03080426041805090714361f052202070b010305060c270d08 62
    0x2000545c01c501b0f02a114610042880c407040e0301403401c02c081240c8108020045070005d45207651606c0030b04180c81c9040c080c6d604070503494840e840c11500405816507804086c003405440c1008894400180900e10550a000107904082c4080006150f948a039121413050b1740214100050740080c4400181507910885040e030715055201c01e00c0d210b801c00004020300500611008284a08200744054250700c0d540201805200340c480c0000c0c14828180341c0070381070425181c000200c0007021401274030150424040c0b19020070821203070700d180720a107108250103001080000c12600380f810141c1206c1d0714440c0ca1064200c90210f58a485034002e418000c6042c513616804142958200311005d1f4013031a00074284411114082544488601d041f40d603d81641c1064600302115101a409504c220034080701e01c1d000b4038400a804000e01c0311a0181e17606032031042c0151750b0f094490032000c40c1c050091841001d008454400325846180701525040080f9001401c010742c080c03150f8441c40e40541008040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 894223498 1250 894222248 894222257
    0x302060c0312090a170d0f023636090a1e030c03030c030e0d0503151207060e01020a0b09010e070e010b0a1206050916080c070209040b04020d12 63
    0x21084809041d445030b9000104000030078030000b95032218522640004d03940000d2003c0051b03403181640321500311004108060740305543e40d0208050120650341888124104000180440c1079905564000c15602c442d00511300c030102c444801039041c01600e89040c108107620103280710607a48000504603482303860288043c2c44004000c0c207011150007590030141d0042201c80a200001030307001038948118a0700b40ca00020400e602607415401440c40100032201c521590601d115003d50003c0110b1140078030300c0d01c146804e0122014401e41c02032444681000740c00a100c00e100541c40744a0f0741d00c08220500c100c3e4082d22054407011200c3c001514400c550b0707512055120007903001042400010503283e08000c1d1198980301c0211450300a0031019030800803214245220000306070400d8000d0718000f080d42205007030080511070b08200b500e8280000c50f070b40c9030000342d201350b80703000b1350b2181c5402500c1d0082954a0350780c0c040300f044005004a034001040000039004c101d01480070002132840d91035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 894224748 1250 894223498 894223507
    0x31908070b0a020708030406051e100f0906060c020d050c0a03060e06070804021c0f08040b03010608010f050901030326070e011103072d050102180f090405061b040302060c03 76
    0x1407031408448010400981103004201e0b03c1c001450704802c495210b078101100040700e49458000c240304480c11400b00c611110b40303a040c030000d00c0b25600d00344100c44d0944c0040401568a003025015204544101d8021410659407007000d41800c1c0000341d001d52081007600ca550040000060041c14250015030721540d40d03141c42800120100700703c580000050a11020500d00303640054002001d80c140540e0780300301e004100c1c041001815134135801a51091b50140c8072a02c0d0030b03800490303800074454000000c01c0100006010042e00d580d41e010358a003e800c00310641c0c210380b070584101d0b5103d400c060801c212144880380d160700c044e800da03004140c1551098000720300d100005180518001c8040543c2c0c00400645002842c941d000c000c028036170299905681200008490019440c4200544154000144485400c913001d8164000f20812610303004505802000d00020120803034004040d81d00220200b40c00e85a010f8a079010707260341d480e029260940b40d50200e5072a40020746c0108981d0b20216 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 894225998 1250 894224748 894224753
    0x10b0f04230411181905030307211e050a120915050c090f041d060106080105031504080d0b060903010c021f09050703060509071d0f0702072303190807 66
    0x1a0f19450b0050304400c50500070384100510880440058691007a0317403c00d45a40c1c803d03072400d40480100001020340f0381f50101800c0114101003003124a0b00c038001d0580307100544a0298103c0d00d607200208503526010b0413070f003009503015030040720329805100b08032100c03e00e443ca4500602150501c684071058234040b030081108280c0d08054000c080c02c0500344010005902d9249ca0542019021200071480d92a242c0c408524003c55031080e072010300800c400440d110f900310304001c1c1207a0095040700c03510080c84000c4684000c05035001080e5200c200414034990646070080440104000e0026181c0f40c84100002d003116505c100b0080941c00c00c40011640710b002c91402c3d004064203d071b0074001e44501d45e840c1034580ca4a0b000040500b0b94503400719a5200080001c040035040d03101140a1149c0744d400ba02403100c03401c9802c001c601da885400100420301c0440d080c0120b03001100007040b40a1742d400e01c02103002c0c0082d42d0680521072006620101049015000d00700d50245001c165140b0b500d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 894227248 1250 894225998 894226001
    0x1808190302030108030a05031005060c060f0a0908070f1401050108010c0e0303040602031603180f090b030d0206150d050d0e180903042c0106180501080609010b0f042304 74
    0x40004600303140c41800100240d5030007204694400106207042503490755400c10b010108807030303500540d400400100e007885142c900055401c0c0118194003008015558000324542942e44d021401800705a086c071482c400074107012201203810f4400d04041070008512840d86085940c07d922191a87e074440c0b50722200103400941c6035071858400c0d0042c510b0b05003041c401a569105400204268441c18844901814861840d00440a000f10300c0b00503850358490001c810800c80e402050340c2549070081682140c44c0004800d094009960050a0280d45a4020528890b01da0b2840c0307130810300050300900000c4060180031081051511842650844d403020311080d5400a0081c85030034141400f405000c007400803c0c0c40480301d0516145405900011498240c803c2180380140300c02500d01c000710b000b41d041411641d01511050021240507078902c011070302408150b07030581e00450010014080341030503000410700740055207951803600d940c40c0307807080e003001200d0344820410002060405461605 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 894228498 1250 894227248 894227287
    0x120d0e010f051603140403060608030414010302090a0302040b060d0e150f010605090907030b120a11041e02090a15050d06090b0f10030609090803040501060e07051c1808 74
    0x9440c2070b6007000300c404040008810281c9025052141603c2c1031001101c82104960182d94401c5c0c040c0015641c0310740e1160b8a40003030140325441080e421000549501ca80f00342c0d801c6080041210300d00c14516000e00c0014000001c0040d080301c2c0c00c2001c41c28000e02030098410751590040104048840040b1851907c5000342c03030058a204240010805281c0c00310a485510074105c0341c0a001e61106241a0001c0c247c0582007500700042d5040410b110380b0103e008180140a03041c407000c138405000400c012241080d100280482b44003c074078100e44007590240c020024050882c81240c2d803599101400e0044031a1404002100080e80c240c04ca0710901a040040156220030700c000350320200011150006206641d000c0c000e004000b0101d82c6c0b0a800070001852010400c10000c0c00c0c034141071000c0d030300445003600d480d82040800900d180e080039403284036007150381d2414106840c001d9030442c1c4003d00800d80d051242c0720019004a44c20700e07003908125501c21aa400c0d0b8420100c00c0c640315681a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 894229748 1250 894228498 894228527
    0x210f05010204210c0806190b031f150812070609081e1908071d04110f04051908070b18040219020105060409020f121006080a0510090f060b120d0e01 65
    0x1004060000c2421f00380c006802d90704031010007144a804281c0420700d03119005503110203442c040703504aa580101644025000c4054910306a14507403141d840c160b07204294010000064803c00108000c140b41d680a1400107120708030b180c6c03405d070049000d05103020f00c04028414408000424540300500a104040011210300f8840c05a2030880b602130316030150360803e80c0d044510f6848100c3d40341e546034040000c0808909041e070315501204000443c0360080e014050107000c801000f102d160880154030340858072103070014000b1500300110817006400c07540114500c40c0c0c802c144142141e40d5170001c2e21940d0441c40002d030401148410003400c1d5000031f00164051890205410b0242e1102982c1c607001d55002e0301c80a60a07c41d08000343d02c1c0044501c2041c8156282c504080390020300440c1c00d041c00da00490440c0c00da62410a8050100c40c000c91004144800005503200010b480750842d0540f00c9c2c000f0302c1540030310341c48400c050500d1a8401c0020008048250b0f1283d550303005245072071f1601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 894230998 1250 894229748 894229753
    0x602180117060334032003060903190207030f030f031406031213080a0f061506091a07051509010501060c150b0a0b0f0a0306210f05010204210c08 64
    0x1042c070b0100307850341c09030340124a0b0035001d00d10301a60340d02807840c0c18035802880c2d106105110381ea07040141e224082c2c101c840b28103150806064106242c000b03a1070f03020301035140c080c3d4a41440f40c010903401100440c0307184203502844170000040380f04d000b10031408600a4558a50304103220400504072038020b4201d42c01c00b43d0f00400c2c0089600d00003081c54560400100702d907510f0401500319001800c00d94040e00152051100c4441000b411880d1282e20070302c11001800f01a1800010061140840c0074100000d00344040401c100015440791401070360340307980190b140c4041c0d6117542e81003856402c0d45001c018a42014060500c0c400d1103010b00400d150319103161050b07016034907040c00034441c20911445548070380c1d8105c902e0f030710401d592009109a103407040e9690b1004010801c250014140240801d250001c0002c0800840380f000080ca54040100c0440304401c1e5a24000341041040c2507a40d50750a000c00710303480d1200207002c494410401c11801000c180c1d4a0310380180e40517608103450700d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 894232248 1250 894230998 894231001
    0x21204060e0409020609030a0606150521100b1909091503151409150a06031e1b1707090c140a140a05120714040b0a0306030602180117 59
    0x599118070036294401040310003189609140c0001002070040c40107159241c09603a0300f07603041207615840001183c3c0320860322007004504003010358290042c00381a041c00d44401502e4031083c0d15281c4419408203408120f90b0915484101c0810282c02c510b444950515950310207a0400d82c1288a050050903416410b10144008803074440803240180b00c01009140c20107100c865440036904102140e4801d01c1e4143d4591401c1d07540c05558804041c103c8000b0220070000c540c03c2801c034000c94041e03d800503000300b9a10740062441300340843d070306026107801c03c400c810052410000c015400041000162840d1400d03c0c1040550a002c0c180d440b000c201841d0450f41140f040d000707445407515004c2140d0b2291161202c3c03100351054941d800440b03682e29000543d00780310b5500000034020b801d161200319803007603a41031016214101c03e00c00074007050406000c1040400050340041980c0c3c290345c81c011907515583d40d2410242e070007014440c045242c820840d110310b964801a20100c0c480009601c003030742e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 894233498 1250 894232248 894232259
    0x5060f0907060f022a150c060705030601030902120c010306140f06070206220e0a0e1e07081231050114270109120201090905060d02060a0203040501021204 68
    0x2600154401c800a20407403c0740111807500034000789020f43c520613000b5040700c811143c00e50055152616140c8100c44e00d051014118624105407020082d2050050030079413a6503505580c42c4e000100f130360f8109911a812200107803994001e00040760118402001c544404400160a5504c80c0e000600c6001d241860408950385e4070360900c9007010155082662194a400403612901c500c02c503806c0301c1040c1c0641074801000c82000b10040300c480000c1e465113921400000c0040d81c03002003601400b03034002c1b41c10164640913900d40d40c114811010449100035544d01110f8141605210311400c0e0000200e0a45103442046405071400102419009041d00c81c1c0e00c454802d00c80c003070148070304201c804080c9005210400048580030340794800205105101070205503031751505102410b0010760000360015450b070784200302c45101c55058481c810b2203424480803500a000040c106588019252000c1000da19030000509581401d940a15031721401c002c006481d002c02e4001d14400c005080104012 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 894234748 1250 894233498 894233503
    0xa0305010e0d03360303110a0c020a090204060206151c050a15060501050406030c0207091a15031302131113090501120b0106110c03030a11010501210b09250305060f09 73
    0xc81000b5213424020915142070032802414220441071042000003503003024a908008007585161003262040c00d941d440c0c0d0082000ea01642c400c2d880942d00032004aa1308004100300913008400141c68268186454018951101c80c541d5059425400820405050001035080e11000d200c0300c820a02c421440d20000170003074442d501c102d40070540c1d192025807015109005403802040b0541d07040c0084e001d141c40e40c10f550841504440d110300b10f001c407100c10503042c12080c1c074442c5140f640d0340365800c2040e40912108d43d80d22041650303a190f64200440000030b20001034500b40c0c1c0c6410741ca07000a4203105506085a8041e00314440c00e0300240e004073300260b0302c410300c141920540c0c5072482403030071a581c0c2c1914008d807440000343d141c040407540c1000340350f100892003900020480240243d9907150309500c00c6800c0d02803840d030303031487c9980c1440200308172418164100301d013070341116811807403205609075424443e0b081801307400481804105000c0108280c0b03070042006c3c00d1040c0c981c280b002c0001e9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 894235998 1250 894234748 894234821
    0xa0b0a0b01020114100513140c070809030d050901020f16090902010504050306010902120702060f070302070218040501021909030f0305160b0f060f0910030201180302060304060e190305070602090a0305010e0d03 92
    0x110322803c0052b2190404c090a410307107240d51405001c550314a0000e42d009001c0d030300030300092801846404032040c1e03c100000f40f0007011200c142c0d072020000d4101400e4a0103408828000e03030503c03504100014040d10200b28943c001c1c0106140181c0b03418071445000b4540300040c181000f10360201c401c1c410700d58200c40246170003403030f64140180e80e54603620100d041451130344041014500c150080209101d81034000700701c40e105022801c5604284a00140d8801509000c040c0c990300101112800107030044d0001d1103600d290340150305400d820780c1e48000b1000310031500100c3d04490700d024441542015511000d07200c5040b42c0002d030903c0e06441e6140c504c8090322000c0d0411600b00d1f90181c140d491901404040c64025100c1903403854a814548081c00b0070482840441c81b60b0400031804500031143c0e028516410355030f0034034001d07071500c0300c002a402910030b059110901442c00400600248295815408003038060b24081070144170180c202c070300c1c00c2d040000005e454069204030184000c03e00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 894237248 1250 894235998 894236011
    0x1060501050c0d0c061b02100507170c13080a06060e0a140f040303020415030506031b01090e09030910030903020610271103040f0c080a0b0a0b0102011410051314 71
    0x290400c0700071742460000303801c00d0030020011441028070480715aa000c60100b0b01010700f0041401a511404c108566100100080d0400c10304648085180c0c00708090003040314a002455903c101a11800c01e01d00704804500f00715040c65075160100301000c0125080c0741d02113200c0d0707410001e04800c044030604800004010600080c904000101054000d81c195800b800c0311450101040d100460090010801910014881e1142c1000d038402e8076070803407036001c0350f5006075a031085880c5000c0140d045e011008d4030981c428003090050754031546aa525a01050300d060391302056004042c1030113030401d84090501001000a03603030903c1904122012040301280468550042089000e903080c0249242108140103650000600051000f03515101d0031040c041c190306061580d60300c3d0203560b95020001e0040c2071420100014503801010b42c82740b40481c00600021816900d02c3c0b803051460715080300c103848811603851050000f4101240e1400d1a0441c5007400c002d00c2000044401707170800e005101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 894238498 1250 894237248 894237257
    0x5011113031209090c0909060e010305031b0109120804060b03010b01020723130507020f0309010f2a0c080f030702030303040b04033b0319030f051308030c01060501050c0d 75
    0x30b180a1082601000401c44410104290354203560300400400c0b540c422584881d0821001096074407200200504a0754001c0c0110700d49103010400754103107203050050800c103540c0e8040344008250800e0441c82010303016590011507103090314001c02140d00241145000c0d070302d801c10800140e60005400c401f5100b05c59019070301c0c41e050000010b08600c41c007031981d420088440300404242e007540c004074000c007069020307039455104401c51503a0301d002d001c030801d00003510000702c2c00145010b54802c04541c00c3c401200c50000d02c0c07040017040702d1600040d00701c0b440c075194681082020f03400d000c04801d464558002c0c601e000c40079000280e9a02001c4c0018101c0503840000c50209400f07603035840310540c4150a01a03580201811300040c401c00c203141c803040380c0041e000c0d04e0101c0c40c011641500e050070b0040100c8a0300c00f203807400c582d0110b4207009241404410405024001c240310355110081145000540c0c2d215000d6007501e0030741c0c05990101d414050140001444a000400c1c100d980c565980f41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 894239748 1250 894238498 894238523
    0x902120f151f080304061106130b100b0a0806090c070b041202030714030316030209060a0e040b04151806081b0103020d06031b050a0503070b0706270501111303 70
    0x100c0e201060320000000610325080b00014500801002030b10858030780d91609042e5420a140c0d40361110000c480303a188444000e0b00c1d150016000390a01c81d04840708180b0032002c0c50302c4002c044280d500c00d03098140480e90350001c00290389440341c81654049000840103040c06126684d00d82440b10141000f011110010500c11031903200b001134413603140d044a81e099030343e141b0348102600c070750058400d55800c94035030303008603060341c0240202c4405e0000a0041441c14000d85400c803912a14204d410f607015845080445440c0d0303c81c0034031184c0203100a600d402c0c40307140884000c00443da07030f0302070385010b414401d0410031648042460241b030b51110b0307144500b0144002c0120001d10820301d68030078043c50040007105010030a400710165a040c5016030b580a5240c500704500f40380e032441115410b074411202802807100e22406850f0a0388580000f080701c20405070320200f02105241e03c2459503003031085100c14080240540802d0380c003008040761402400e40100c181001085c00058484038a110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 894240998 1250 894239748 894239761
    0x1008010e0a350c07060306050f0d032f010612080412030903020316061d15090402040f29070b040b04081912060608010b090111120d0902120f15 63
    0x409440111000e02c420720031403682c5981140c2d070494403401c110b07442039403404540d00c0d000e841803005980d001009080780050650800c6105c0310101004c400308400d41c141c21588010b5000e180000e032890b201c1d0034101c10350110031282120000d610101111440304840340c0481d0f07101c2c049800752403880188001072030b03113428260f03000000f83c1d1000750548103040300e1a10b02900601c4200a8415170ba41b200012002c4010140b08005902c05981d4011900b120381c1002144001c010f001c4644081c20142c1041d9890030802c400807601d40c01611154102031a44030710150a1f0130503a5040c261000581c10468981c0b2100c0d03178151f0040005003c2201b6501150511070017605484074245000c400d581102c42201d030003011013026a02c010310480c01d1800220f803140c09680c241c0e043c0c507003035242107052850000c011605009007100780200f034010340d820300c0311444281c001031203168036500300883d07003600030302c184110500f4008e0001c120740c004420a42c3c04200c0852034004507407070b1781b00c407501946806 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 894242248 1250 894240998 894241043
    0x30f0b06030a080a02100b0f1503130c0305030c070f03121b051b0f04270309050303030f06010e0402042d08010c020a06050a020901050a260f1008010e0a 67
    0x103400f070040410030a8603280d00140107880041e00070f400344010500101440030100c0420304003680401c0072040076101c4821070000d0b591002c0006040c03001c0700721984030030340184e0058005403055040092444c481c0d4604100301402000005100303445249191541141250180b01200070080358480c2c10b01e24010b03490307070205801e801c00140c80d03104c003a045052040d1800d0210035405091015240c10b031615083c42142c11891000d442030507202d07620403161111689501c000c8090026041020440391010800f66224150300d02c82100e090030102d001410684a550000f031203240100024052216a41140c000c2801409011001101c01c00c2001903026415000400f10f0f61070080d010792034030350000701035252a01414040026403204029041a0700ca401e8613240400c1081081c80070061184160568920100143d003504481881500425404c1a28030110642c0a80306000b02c5c0301c000740c1070b8001045c13070800070408181883c101070f85415aa21018210f00405005016801e860 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 894243498 1250 894242248 894242263
    0x30302090f121b120c0906060c010c11070b070c06052b06090e0703050a1e15020c0d081605090406170303071e1e121a0f0109030f0b0603 60
    0x30a2101c0b80710841c1c0720b8a958106010b0160042102d0320a81607007070816020600c800e05510b40a005201d0030302060010590000c0d04442e0488410000101541800e10400460407400d90703e0040c0105c28100e21807502c00250811036000350300f002600000b03048140101b040f41c1c41410116128000000c000e4515014070b441403000d0032994143c503051907020761100302a2620104100019200c602c0c09d55038556890000521079400007401401103511482c5905104d01034a82c440c100000076940d035081045c10007401043c1c1c90300400d4040c10603100b80f2006010704800d142c900300b245002d14903003418080c400c42e070340c00317000001903940b801d9280c07038000f04007500800c4096080c540c0c45080c0c16a0b00c1c5c1c02295104002610703100360940b6102e0004c200c030a280c149641d10100b513042842000010308205810b0403e12003a14519441c03180c05009a00702c101e0341145014625410500b400715290340e4142d075504100f407002061001800818840d090075030825030401140c1d40e0080400d00d090304 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 894244604 1106 894243498 894243529
    0x3060109140d1112010c0f08130b07030515030f0703021c0804050103050a09050d17090d050f0f04030b0a06080c010305040f12020c10090306060f060c03030209 70
    0x14520301c50105004000d0048080c11a6404d50380d00716031011080c0004120300e0506103c2094000b8001c40c0e009140c103120107801812039490101d00f4400070840802d055403080483c4404800c415400d48042c0050215204003504460a568a00c002e200484c030403610741030742d0700907009420800748006074459241030900c1d007402c0041d03014120042034034201c40c0e51000500080b500410044a0f100001c0d1120310522040008143c25010001c01100d4568080d10540301c03c650300108940c07514510103e40ca4803405c0404801e8003070700c9980e00140025100c5414002c10b2001d6505c20004c03503205104552000e0106401902503e40850300608005081c14141c004140602040c011310780f01c038415900d0700007001001903080d000c82c07604880040c40c807041c01c3c020800640b10f21170250005501901c48140780c510002c5c00303d84107c00040405401080381040c42d224107034408402c25 = true := by decide +kernel

theorem cover : BRFrame.Cov 894064748 894244604 := by
  have h0 := BRFrame.cov_init 894064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 894064748 ≤ n) (h2 : n < 894244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
