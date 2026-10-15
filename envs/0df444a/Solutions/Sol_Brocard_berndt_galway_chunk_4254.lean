-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4254
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:01:22.427151+00:00
-- url     : https://prove2.me/submissions/8bb82e65-8ad8-4dc2-9f07-38693e547b3f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 764928057 ≤ n < 765107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 764929307 1250 764928057 764928071
    0x304020d0c0305060a0207020a1d0c030414100c1b050c0d0c05120a120c08090d080c0a0c05011202041a07020d2120070302090a0906020f07030e01091503 67
    0xc5441c05803a401c010014041d841c144420f150541d0042c0040907c215030086405131503801103040f03814404182e480402a410101c0c3d00c000c622402190414000c100c0e14103091100503615180c110080300032082e944d03468034188000c50348155183d410000d645100f0304041e1050b15065904e50803070480358428008145a1000c11000c91b10b01002860040c105114101c08058010340307a402500e0184d400300311002609010a10840514001d81c2c0d01c40340740340c205400c41d0203100203c02034440c100d820090030006442d03038410410881d04154415203030a02c2d100d04001c0014402000c07082110043c90040c0000e020000300b100e00f81410040304110207403103004c01c3c00080d10350a84048045c104c0d0040001c85d05950003070302c0e440000000740d900d641d150030611101c501030440108503d540c680d00451400e04c0185400c03803095401481d0801d0102c0c0f40744090310b450003240d1020141d03034103201002480c0010103422410404e01d80070b003400c5c0616050f1030b048600180105031509a030405541c0e0701 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 764930557 1250 764929307 764929313
    0x10e06030712110903060717221e061b05040315180303140709030203100b031614100f090608040206071406040b250e040221180d050304020d 62
    0x907206075016040e0300c0903c00380540b40e01c07400ea6940100e005600a000d0b60000850302030285600b6840c0400302e100d00c0b40c2c0c56688070030341802c41446041c0d800381801c507640707100007007046400c07100c4442c042100401083c50071854140110b0340e00d0a414022001c00606646007240c012040da02125005401504041101c0b103a010040604002c40304004100390f00304014164540e100f812a0040c20b185c0010716251404152a041c82c40c0c44000c1d4142e00507512210b84551903080b880b0303d480090304036214404c100c0500240a62a50800130000710b030a0004001c40c81c03c02c81c2c155118565080c04088080070b5400105401000d01903001401034040124085403603400440d10540d0304401350701140074a00141c1a01d480301502c0568040c0140b00200d0804c88121110340c003220000184001c541d5960310b010741d400a60351200d1035020b942446000d0741030b2080d1092511403802d200c54a641440c01c0444d10148100c2100c61014560000e0040c610f00ca42060444c0e03009501110300300c080084c64a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 764931807 1250 764930557 764930567
    0x210f0c030b07080103060b011d0111120c150109020313120905060304060608100e030a0e010302040e0f04021030020c0708031b03070c030326010308030a0b0f010e060307 74
    0x1a2008042040c03070802c00a0083c1e00c181d2160689124240501118603e040119101706244e12019880f680e1400c6a99048d8081d000e4071409901c02c40603201d501c5031840c8152040d0700702c2a0a180140c201005028200050790f0b4040e000d071101440850440c20700e14a10700826015007002056500110801100c0c0e502402c9004000c020091007599070b8a40b924120025103014803c0550b680705041d04248240750300e0060022903210300b00150f041410f590022102c0d62211084103040c198204008246000c41059a034840c206206c405412810940305000d01b100070f022001d07003045922000704441000d5505100c40072501c0140000742c0d00308410381940248900031350382800348182c4100052103140840503040e00300c00d08500d209050800051b00c2d44a2040017001046420780810520001303004140e00c07443d000e841440490080e0764619403080102083c0c200783c5400c2c41c080100030718540140030364004903c0560341d401820440ca40040c1500c600d0300c001c144110800310006101030311030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 764933057 1250 764931807 764931809
    0x90411120a06090e030a08070e0d060e0c2b0809010e061611031f15120827010512070e0301150e01080610031b030c09020c07210f0c 58
    0xe504500c16508211032004000c00742440b54410103802d042440c0400b040100c1030301d81004007520b4802d40e1b5954800c0458007041c01d00019a03000303400130310307003008121140301d9054079800c080001c0100c80e148800700000d010058011424114150310f685880c0074201c640300d4100c0c0c1e0b03c240944e80f500c20080c0142c42c0803103003104954102c00040380711240114181d050309070450003401c840c0b00300c08a140078545c56246000c50f0b00200906080c02c44085501030b132214142004c088002248607445024108503052458002d07540084041090040f40c120340d00c3c1042520140c00101d5815030325100083c0041c002e220044030010380550024010502452020541d106d0060007002624202070002c451000070b40240845180d400b00045402400000c16a0040110444204a1a1950391448de100041e10b42c0900300c107000c00d03400030005c0c4040a04201500030004050789075002101100c0c500030080d44140c05940d11115107000300d9034000590207195030000c803070506030740650401c00760311282 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 764934307 1250 764933057 764933077
    0x150b03100908030714030717191d0607020a0c030b0709090510081002090d0b091204180b1e04020c070f0306021b060f0c0d140403030b0a06090b090411 66
    0x702888502009015002184034424a86540407400490301c1c6072180e5000407152000400c207100320009a0340360203007030954016008941e030740300244a014074500751080c41c42c0c92206080d8000c8034070902941440100e6210285200910600304541c840305513048091001030300b488018400704803110320922020009c1c01e8042d409008609010112580d0a5818415000b09008801441c1082c4c482070084421030300e4002c204406100c00f5440e5401d103500042c094440c2d611501c00040c40c0c010718103011b0001800720112203100b017048001460280c40108210304d00c0381c1100030320000c044040702c460b500340007001d8800507214000c0201241c074100d100c1c3c02c00e8501c00e610754000020031089800402ca0305218209110380303041c5c80500e0941d1010f00341c8210140d03c4070b80002030303101c80311030003d041480d40d0608003180340c10520749254400784041c2e80c242c001070740340c0780d81000070f007440d2284000414007440c25610041c076203080080c190007180000c5200d075446030569041126070000340c4a007450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 764935557 1250 764934307 764934311
    0xc0a0e01020133050d0b0f06130c020a020f0613060305070c020a080109060e070e070f030b0d0c03030f05090603040f0302070b040e0105030120071b120305030a1503150b0310 76
    0x52180003581c0c00300da03280d0680b0140030144408150707400c0442c205e8010313607408103407810b4a8480d01c5910400c08001880d458001c00018000040c0d948a801920148807181c0c010b0501e00415005020200100c3c6400e81e005a004205c49611045181c808104887c03040c500040c95403078480d411542d034000b615029500003d108008506c180301980181c01d0f1903c504401c0120390310380c1d2112a103408152280e020320005a1000400d000d0090402900740c41980c80c0004c0e40100304000510501c110078000d450480103602c0610030190000c04514680d12182005810009580b000600ea4800100300502c511505a100d00406001700302e110f014100448200f91100c1d115002c042c144442407007014841e6007050f4040c411320b0440c0042500400b06072126030f25001142d20358155102c0008013041d000040d20390005100000700d0701030541180300740d549582d0ba05000103d0b0080c1e03800060304401e20401d540b003c00c00108401e00c510039042a02c0030220750b1114a20002e400c2c00520f074201c582080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 764936807 1250 764935557 764935601
    0x1e150a0f0e10150503150109050603070e1315060c02030703061d010b06400602010b1305010501170405010b0306070512090a08030a181b0314060c0a0e010201 69
    0x1500d01d01d210340c429801d15859050007903603070031090302d110508003100c03002c1802000420852010b200c000145014103050190403580e84802084007648100c5040c00000c6142892144a10303100031702c1e200d100c1503000b0910425400c400080030b0326440740715400600c1780e8141604110348041c800a8011a0409410800d000400c0b40079418140a10310115081d441c0880c01c1030945008000c0d110300182c5060358484416010012084078804101d910702d1194104d80410498048100d0303c501808a5900219421450b1028080100d09071100014814180b0300140450390703000f80c00300e004c1e1000c10782c1a441e944407406c001780103019030001c09825000346000c00499540010040c09007540b410a0b418482da10010302544410310240c005201100c1000031402c122107a03005500d60304550000e640000001da91010420105003101d401c0310f00e0701100130400d010b81050006400c90800c0064861460300740c0e0810a507205440d400414400c014452400302c0e4800d5001ea21000c0c5000b13a5101d0380 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 764938057 1250 764936807 764936819
    0x507090f0b040207111f0e15120412030b0402030f0a180c033e010302181e0405130b0420090708010305070801020901090b0a02030f04030f05061e150a0f 67
    0x70201100c1680038a90040b00c45021440640319100c1c2c1006e1980c601120414840030402d03401e190710722007071080ca024020344004407600144140141d21030506c020b09150b1445000d02581e001201d02d03889584140100250781d10060300081c0e001e4a89100040c540401c40301c0d000200760002d5016190b802c180d03d010040128a02c0d40b08048002c0c0c0c012248103070031194904100c440600002c030403140300705007484000d50298000e13200c8080014501c40c0c1e500b2a2601040c0751060340a00c180d40343e1500c0400803281d0901e8440d0580000f0308204075401c201050300c0315000c01d00701510041c6401e100419a19105591a103410301c000001400d4404d00e060190005110480030b00007941c1500030344d1030010b07100005200302e81e840b1106844803407805141082d01032080d0055107002003940001c00800b1404c408440060001e107202e82c000700c944d103441d401c2031880c0510041007c5c1404506014901001740401700c400c0c1e00140e07100000c241d80305601d0102c1c006d00c86990181040101444002c901 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 764939307 1250 764938057 764938073
    0x6120621170d140609010302010c02130e012a0302070201021b0418060911011d040e0309030610030501060602070e220203190b0c0708041e0b070b150406030507090f0b040207 76
    0x1030454041e0243c1c85540f603000400414903020321000b4003260700070074400010300300210170b400c003440c04850001304002d1103940300342591421003841c0c1610b0620000106c2c00710450084990a03400d0b82740c118100007595002035590400c540c008607034101c0c650001d01c219500c9402c81d0500145e85062000695510324001c0e0103060400d804603a6018041c440000d594131401c0d40c8041c1c10084094050f4405405080c44002e0482d0b91030404240001c001e14070060320108030103401501d101040e030754402c2c61410070701d00311101900010304542100c903041107003c0a80c1062031300809210075080c20743c07404e141941101d004a4400a41501605414030300c0c0b40040c070003900c2c517640110b41c0b580715a96450442802c1d48070b043c5004001c904140700602000c2907d80c04490300700040b800541c1034035140d000c0802140c0141c0010ac40b035241080030080034800044000001d00810b490603c425410346d40e6440d1581c5860149480700c03962650b000d0100f41d00fa8014101c55240603108664640700c50030012a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 764940557 1250 764939307 764939321
    0x3011802040807060c112b0c090501060c0c0e0c09150d0f0f06060309020612040c0803040902070c08011a10030603080c0a050d110c2709060106120621170d 68
    0x81c010302541b2040742d180c1441504444100c1264800c41e1045555806108003030704510030070b40f40341845800c0030815040310300c1042c1c043c08041e1a48039900c140d80c50181c10b003400f160031004462007208184641c160104042d01c40284048401c020800741c01601c040241c080e005c40301108a0802c05000c0d004107159100304e08002180300180300c901c2c5c441c0010f609a4015210094001c0e00c1080714a14180c0c800b04a280c0003481203042045036541d480fa61032071900680c100b119496800246034007000180d07203106008194240007408403100a840000350481e650f410039018020001905a00034486c3e441900550340c05400f45860701c02c018412542e601c00940102c81500c1525001d00c85170307020304141000350000350004c2483e11030300018400d01d0040d1040055581d821401c1e1800c9003904002154810f4000d50000d000343d42c0340100007000042c2000200250b24075243c814041c0594050b914403010f09200007c0204070094074004c441d51005545404141da00440e03041c40315042c07034003c0c00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 764941807 1250 764940557 764940563
    0x60e2b0e060f220503190f0c1802030a18030e010f020c03011d071202150a050415080628170c0a08150c040e0117010b040c180f030803011802040807060c 67
    0xc1455403900d051540d2040c0b00c0f0704040d00c850144840c0300019207c80d00402c6003505c210980e07181c056481d4150312250840c007070000c110503008070070820784d105180301d04800707440b9400030405442ca03652805445911051001c41c1000140894001c51a00030840704a803030304050300030003000b0258a0503211110f840321182d80f2500030040d000807281e410742d012000e0340d50000c1c400001d01040100490199104004c610140301080c04001110090048038001c4400241c6540c0064039205080000c00b80c01400c00305602c4540c8251b400000c65100d2168095030b4a0049902c5180600d2a0031131070320a00c0441e00b54840d980d820041180c402c00b00d5401c807445003081c2d1380402c2b600c1304002c1044900550040c07440d405031010041104d007040514100141c0008800041c121200701c2c0071905407090b00080d0800318030011a5803c105ca0304c0c422120061484880c81c080303985c1182c1c1c540d40c1310310045c402c001e500582c4040c1010010780303550403600181907420846a5030f956031034010b0000030100c4419 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 764943057 1250 764941807 764941867
    0x80f150903030c0a0f03090c0f1403060c0a030b0d051207120f0f031817030106020c040504120c080f03011503050109020a0c060c030b030a060e2b0e060f 67
    0x1059011030000242c078082c0c01c2152140c0c2c2003050080c01140c440b4401c00c130b40b02c00c0644941c5400003268201e00303402c000d003144160000d01d0504001c0e00840303544202c45110b0003540302c02c0c01c00184540f440241c542154141c03501240c0c4400703e10010f600140406009401d90281c214002c009441c404001c14119100c4c45409080c400c4170101620b00840c00c40800c008602c10b01032060301213100e944814450101c0d0301301d07140c03031100c40d840d90b01001e441003001040300a00000107224058041241a03002881150103003c06d1030140d407007036240c000d041c8001c0d041c03010714010ba02c100420034051f00c0a04141c44c44454485d03a440075803e21107414010307904e01081c40c01e00045104401402140d0307007005607488014192030503a440d03800030004009003e08050351812018881c3d90288a035961560103800c000c200804100703502402d0039507540c5003d281061140ea1010002443e08403003050342e80c1070500c4000d0640c81d50103e14684101c1500300f20706100007a50440324002c458841a07584515641 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 764944307 1250 764943057 764943061
    0x151302120907061e050d0504051605040c052a06040503030f0601050301120b0c0903010c09050310200702042307080c03010f0513140c03180106050a1e080f15 69
    0x12076460b8a05406600001281c003000c0300c1001c201c1d403a0402028950b40b42035844c0c511001c4000b800c0b92002c2e94120703055041071190b104a200e10888040243c0700c1142c08200030011f1079005409032083e0281c2034015621001c402c00344140800340b000001507000c040d11340302e16151915585a0744100e9191040c415240f01150381544a103050300d050b988640b80c0c058540e11281c40704100c0403401400703581f008004200c00d2595407004e0003030600d0b6600c151a420141403c04c0101820141001407500c0709900d003001c2c420080c0d4182101050141c644000030303560f048a8004500039040c0344030800182d414a250002081f03880107180792040c01682d4a0803030a895045951203588801c1c401c0000441c10700c54284290300e03014010707031454000c8040002c2c04003d00e0502d00c0c50002c04544046075240040100884900482c03000c1c9a441d07020002088524106000501149100d002d590700c0f000c12210344100c00c8101020b810003815400301140e82c407048154039603a0b41c403007451428100381d0381000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 764945557 1250 764944307 764944321
    0x61d160314150703020c2e061a0423060301030f030f020f06011a0d060e01050108150603011a1b011a0301090b0f06010203120709260601030201050315130212 69
    0x203140c0c1c1c812650740640c09002e031035884084001c0d4014102e0744c000b5002e03410f140902c2520909202640100d084407c03c14605000c40400480e0900d078002050b0341040042c0c82d400c401c2d2101214255020401c000c0c000f000d045200300146d10b005482590000f00c000004028414128030700b0511a00c60742d50f0030362010401c40704036190449000c10354125805035005011324030141c3d07400040c000e40900d100d81040100765040090301e01e0782d070107020224101401030200707580c85071400e81c0c407030b9a205403c040ca12a200110301c0320b100512840313510000030003003210b4880144007210090f1501081e201035000d40100c0b583d0091180b00110040101301d0710b08043c46080600a529000d03402103540e44043d41e95a40c56141c10a00600c03044c110f020030000e01d5924400040c5950007100d5a942daa015141400b0000c54061126038120f06031003800c405417035002100003400ca06499080c030b8002e4481c0c4440003c407401076103200c2e8040c2d1041101c128101e9460b81c40c1e001e011403036000c241002c1039807101c032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 764946807 1250 764945557 764945563
    0x16091b140c03090303070f12021207031b02040f05160c020d0807020d0812010f050603010b0d0f0204180515092716060c05150c0403061d160314 63
    0x6404140414032640e400c10094803600050104400e00e2816645042c428000107411a4441041102d22600c084612000e21440007003211000c42180000d004401e04110601424000c05400800f0010481051008210180d2080f031230b0650140003800300340200b428202c06017908560020201411140006107580319421609801e5006029141500107a4071805d2059000c0141660042d001044000004035104006c10440b0701c00c0c0304560392175061401c0c61000011990080f84a121b06000600c21620b09400720745103e0f0300c0550011b0b072041d89280d05406400307682d002d240003a100340001c401c00c1082c0d0300040d111302c00c441042042c1010840c02c200c182002a00c150f8168002161114031518805401c0e84001c8403440c05ca40039000720707820300c842c00c40030340e0400c2d400031710501c5000702086410000040f00e180040b588541a00c1c21611005140c0a030f448040d00440d1035090942d9505402c5414041038400507099a15184003940c0890b0828035610040350341d2120040c801007441804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 764948057 1250 764946807 764946851
    0xd15021c05010b0f1e070c17010b09070e01120507050a020f0d050909070e0405180c010c050c1014032502030415050306040b130b03010c08220804081609 67
    0x841100d08040394169066666080020101802c000305c54803660201003c9000d49003040c454a800c0c1042400c0078078000a00c54207080d000c0700c0d81c0c103000740d01800c0e03034690418603071000b842e2030049440c090402c0101c07005480210082141843c04040c06801a440710040c1b01d00c10311902281c030645e4204122580e1008034005980001e10140f11078480741c6032007c2c202d50403200f0707494101452101c03030300040e0450b9000e0f2401c40c0c0000a0a010f9035100d0720034400c00b4091002400c2541440c201a1251515407405070503152190103810024010356018004124298600d48042a240c0c40c00c0444a00116401caa900c2840e078415041410711074400022102642d040540302c0b140f880b86200c0a07a090f41003e01400d5000b521074a50b00c80030f48408030345a2700c03043c14600c00301d2218042800e16003101e403964181d004004201082140a040c4400f0141e25581400914503c80c02a8205805d0602075504481000d001c6e40c00300341e000b0180d031030b980d000b9110f68003400c10410680d200c00940c0e410714 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 764949307 1250 764948057 764948069
    0x3021510060e01210216200114030f07030b0301091a07090b070c05060708090d0f0204060f060905060d0b120c1504060e040905010e03070804180e0316020d15021c0501 73
    0x3d4200c1000d0034491075006004030001360440c0444c0b80082c3c1c2e480d6014081520449061406201047d0402d581e00420089032035112440d600c0c51405c160380380340f0718420028140c105158a904071946c00f51000d512213119a6041807160071400410725605850007002ea407200002184043c0c0400c0003403040c0100e83c40070740e01c05c40d00c00d051880c000902c00c0c640c00442041c3c034251410300c070110054031030025012016106428860180205104000488540d90803402055001c10801e21000760410507032820b4420840300151182c01da420302c2c2018000149045030050b9010301c020489600020780700010309002c0b00c0f0005401d410a0313160440c0c1c001d601ca14000200000700316106400e0943c03240300a84c0c040c80c000f01e100c5608000c000d14551190703004584284c000502040140d01400310192052481503050152040b0250100d03501d008030107000c2030014002060100b15954894181c500781c2d807000390300403101034040e0b001d0025084000c03408070f848200801e100c51004e0b2403081d00d0603070b52 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 764950557 1250 764949307 764949347
    0x101406040e040230010c03020c1f020c03071a0906060d080304032003180f010804031809051602060901090c090e100905010207021c0b04020d03021510060e01 69
    0x3241c0805072a40e518050700070f076040322800045507103001e8a02550901411141500980c1950155426007110303441e003191b004251040c82240f00c4a80042548400342d00102100d0020f160001604002403181f900306241c1403100103090f2080004000c7c020750185640e4000c4010341e601c5841641d1540d03012507502d07900c03512071084440020844406560000d0003031030a41e5a2005d0024506170355074840d40444442c0c0c0c00440e05000f61403000c6240300d4408801d80c1c1c200358646811001800c5554007a00080178044000d00700002c64141e0000d92004206a01003444941452400000e001400b616084014043c0b1400038404203014010201800d52240150075554900200c10000700500150159139004445800e21040360500031604500d0117000010382d200f40e81d00c10080e003040c192a108210100c1609401c006c101c1001980b03602603015100c10554964901e0f0481c1041c550181110120990307105210042e42850060030aa800a8413145409044a4019a00d50200c111108400c00e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 764951807 1250 764950557 764950559
    0xe0d1d03160b300426120403051b0106050f12120702061303060209040b100206040201140d2a080106020d120605130b1c110609040b030f060a110316080919080310140604 74
    0x103005186181d031f005009142c40d03801c29025040a500600412403900c403180e4644c1c0c014401450264280c0450300021a00c16102c2e0114aa416866241c860f41c1d0780081e00700400c0c00410354940500719110810307004c800b450b10701c4c0c0303a2510070000e41109071600e0082c0d00d00b04800c240c9081840200d8110f129540050080b60f56660044070901015054019502c0c02408240c8400305540518a464445108a00320041d0442c4201c4c0f05501841c400c1c03c1001800e1004018641e0003055604403004c2a1a10000c12035000c0c00d00c202401d05580f04980003504500085100d0032107038000307450880221030203544018200e0417040c0071020900040c0c0203aa220400000b04d00d000f00003402c1011002d03101080e1004424006130500c48800c030791552640100041024481c0e05120341101c01000706c075000d05504200c207003031a050500b038200000b406026408100c005004014425240e803242c1d004d0207417102d0b20716040b501608207403400807140720580c0d40401d450030300341070042040e00c0182200f402c003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 764953057 1250 764951807 764951827
    0x9120f020d08090a0b18030d0f0c0c0f091b0f050f0d0e01020304080a08090105010f03060203091c1724130e0d1d03160b300426 56
    0x1030720030020464103080200034038001ca4583e41005401810f107011116114a0707034004030a041080388540394030075000703180301c10082c9401180485080c0719a1034000c8000e140f510f000000c3d43c809800c203004526203030000150164140c1c000c2000d5490005524461841c9582c003038414458107403603030010543c140004158409808054102c4088112001c07504400700300c002e5003240d20030707182036520b03034000191080c45c1e54103c2d9080307400c8240d90000f0011076250050104403080c140c00002e04c2035400101180f07000c00c0c10041314101d508180b84942c500313001c2c00c401901405400c00800b141814075000100306c119000e0b282012020b8407003416038442e150504028100c20501182e010981d0b85000d0003010b0350040240c2201c941d410303200c14035424104001c902040325030740120f0b8030035030001d030080459042c0c8080031070840d080d443c25941c03160714056001c030740c44801c3e28504404010f80780c40c0c044460030142d040e502590152040004480d80380c94488030401540c2c0c452031240c1c608020071a02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 764954307 1250 764953057 764953069
    0xc082104050d0317011d010b030903070605060103090c08060703111e0a1e17090102030402011218083c16061d0d02190b01120c1206020a09120f02 64
    0x68442c3c40c0c80d204c00035030244c01803152403007030304140c207036203c0040d62503859044460854050050209400e095107018900385036a88a00703000103003115111404200564041d0f04a003000e290b02511011400c0d0301c07862204d03030307907441103505100181c18104100000c01080c011074044e0040c4103503a0b218458070726802141c65000c0340e03020042141e00031070303024150f00385500e0140c019032540d1222800403501c000c1c00346c412005000101542d20400c2407100603a080303640610311445c009804240c038001c0428954000c070121202501442c0d001801e80b000e445019012450038903041c2007580420104282e08040c681825a5280c030b160707042010f04011844424079503512071254030003040794000c0a601c6c20000343d40204900803a440560071942068050190702121503440703000f605c80d00001e84074219411030600c034020200400a201c50300380654071103001c0260a03c0314244c29444030702d00d0080001c0d840140304074006816031031701080c5900701c0e202d03040060360480001100c19400e0703020044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 764955557 1250 764954307 764954329
    0xb0d0b0705210105010e040c0509190f0305060402100c17031b0d090302010b01051c0b0d0b1003050706090f151110150b03060a170a0602070c08210405 66
    0x1400002e2140c98500700c411440410344141d10000405554940760014148000b0001451310645c2004000e00e032855109054400e43c4408a5900072000b186410300b03100c56586800c6410080c4e140c034004800d102c400182e142c0905d100351445000c2c402e03440400c032245d9208400041075800c002005800c00c10f41d007006942c02c2a4030f6401000c8118108120b041c09601c40340300e4181c8a43c482640d4000c3c180c0a110b4445401c00a091881c60724110781d203190086224049200c841d143d82d800070751100d031203e50320f1040541e880f0058003180c1c00c01c05480000b648103440203c54502c0351842c0425079501c01c0c41240100c035446260743c1602400d20411440490100000d54104044000b00780e030031074010812403012103441203001030a404d280907661240390850300321005900c802c000340b1103d030326190304240c2100c0013510044940d0b41501c81260801d0318110f03002d4041400070854400784624903200c40100d036072001c12644003ca0f0804000343c0e80d1a00c102020201c0000d100401c80d03800d246200003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 764956807 1250 764955557 764955571
    0x80c10080c0d0c0f3c020f0706090e09010b010f0806040e101e0207051018060f0c030b09161805060408010c0e0105120109090807080d1e0b0d0b 63
    0xa820b1520a18410044500d90842007000076010f4540440b05600144240903085010324803050001c041050849200c81200f200c80c035209020307248010b158400e1051a05050390001a100030340c0d9190b4000341075614502a000002058102081c018001407003544241101038540c0a0030000c802c009982d810130081c02141c1050310780302e007482c0718003062050114160105400040c0505d048102000c54021032a59196180c41000702c00d01198000890100d0300360000e20101d140ea83c0140c024a800035600b100401c1d003810070b1400b940d490b82c01c0c2c100d4a0f0110050b9410491a460071041101481d82520012680055102c80380c032414403450301c01050049a540c445c084a5176640814042da000ea4403c07019039560712800100981c2c88892102c1010382413070040c2c14400c1580c42c2a030803240600c2a90002d90340c80c1264401c000e80801680d0f000740d008595a622010720160f040301030074101e5110058980011800c0c11810300740e114200c01d115024000d203d9900d140d940351150040060200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 764958057 1250 764956807 764956831
    0x1030807110303070605070201051609030206130f14100f3e031e0906030109020c01062310050c0c04023412020a0312090204061a070c080c1008 63
    0x80c01a50310b0800081c0142c1e44215000100742c50300c4c0900a0846002800c4c64007903035045e4440140d074541c41800f0905681d0120360440c0d0b5900c141c0c11504c510b03406503020032940000500c000412404400981102d000240c840700011034001404031800c12b07040020201041521328001c1e6054810140311080c0d264000380b11030a5264501c1d0700364001c01c0b19140301d0640c6c1c0b00040254a5a00744c11544000800b0f5901c214102121a0001943c9000501480100950100785500c02e81000d40001004000740070302d0603801004071702405000080031140310300446820704003084140c404c2d07049696030b0710100094a0b82c248214208006584013034050415466494000e80c441245527507699426288400103925100310761408a140700e010f000190295049114144080b07504548400c003015040f6400049214041c070009008066a0300b00e8640201c10040c810b51001071040200460313409174010114080e9107a01306582d5070442882c0c80d411244001003664450300079988150440030404103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 764959307 1250 764958057 764958083
    0xb040e04390311032103100f030b011d0103031209050c04060e1b070203100506031c0509010306090204050f01030b1210060608060d020a1511010e030706150e01030807 73
    0x5000c121540301c01c0c0481001c1041c0300c10001c0042e981c00e0b00b200458160040c010500e1131004c450920703e5900c10541c800d110000000707100c414820000005055804080d5000b583c60741841c0c7c0c8850303001d00400030060f0384120303a0071110f80ba00056034122581603a5440850010790300c04005489004800c58640c81800e2011080b941c403809035001a000141031010549800b03509008403d070000d045030708041d820010400961400b107100ca64160303110300045007a440d2100030a18000c00a0031082e5452200f10b011955103078805e00500d101102603030207120071505d94041c03001700d200d6403046503488418100032001e0380d4001d40100c1c15000005020010180d040c0003038a040c00b64141c82c4607440b90340d5070414403285070031484140d0080f809403001d10610f2096400314011480d58029031000c04600307c00040118894602c1464800b1500c00070f0140e01404003450741c0c5c0340c11610080310b40343d05001003510b0040c01392000e078044502c642403108040c0d20b551130b1603413a0f6020300c50941f940707080b2800d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 764960557 1250 764959307 764959373
    0x50904020f27011e15050711060903010c11010606050412061a03070807030314040503030304030c14030a020c090901051b0304260a030f1a06090402040510090f0b040e04 74
    0x90001d00070300d010341039100130a0741c2e100c0c12800407020344c00661180780d140e2100c0d0b1416a204c1c040c0d60f490760340031014248401d160000100d050103203030f410320390640c20046407202c00c0d03900003075004284c80610024003041d612030b50140c0302d500842c00b4558000c48203c04a1001c00d80c0d94108d4054240844188800c101c0c0d650301081c2400c181c3c2c3c100c00c0c1c50b540014020004c06501c200c004680140381013485082608040010341c40c0d1102800c00740411900d5040d003824810f1801410181000540031250780d0b038240d0101a48a10600038014461307140400040d2000c6c206010f030a00c643c0c8000402000000c5d01e540f2141141c002510075100354601c00d007504020f5000509075103900c0902c17080641c079010b02c01c8000b0700707460003003640804460400c22840c007800a945200500c051040f607910741c0300d4100a022400900855000c151b0202c45d6091003244c40fa081a054070503900080f410b148141d803140d008100500c514840d0041480d209000940030680c1011040010b02e840c204404800711541d13 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 764961807 1250 764960557 764960629
    0x509030606041a0d0c2c0a060b041203090b1b1b030717100603062a1e0c0c0e090d08010609121401060807170703080a03020702060c0712020a050904020f 67
    0x1c04800c0c5128107111b01c900021203400840360f1040416105000e17a80c01c1048800482c00b50703110390f01e07d000e1922006c100309402800c0540180c02c0042e80340d51110b541e0146032020040007030301c22403c6e0242c0d40c0184605400c00e4040d008082015000b003030118542010464a04412544920306001c0c900320400500024080c4000440c00b070074000c20304420418035038100d80140450000241d00e00707216040442e8100310360381040d48a10104024040e41c1800682c1c1d08008150000d003114003200c00480d00c0300340e01141c0c0d80140100c0302214074500c418401520806000c1c080c1d40c0c0032844254040011300525044c4007040ca00c258050180703143c0f0301e9940303400d450064101040359080184140200c4204400c2044182d154000420580c3d2441e00c518034240301e10b502c8401010b40000701d80c0c0564032844105ca443c4012401242c60841ea1840d4a80b13606ca00200206d1141c55420000102803901400e0580540c0d00144645007503a0039000700518080c02d504100074038074202c80b44c41038983c2c141c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 764963057 1250 764961807 764961839
    0xd090308041e020108010603110c070b070b0f15040f09140a032309040203060a0e040f020103050a050402311107060c050c03181504060509030606041a0d0c 68
    0x2921850500d04040c40e0940c24402100c0b401001d500c5010007410240c0c4e80107181d1030450305142800143e14010300e40d5075507244160707a550b90310341c4a004000183c00b010f1400625030baa010710b40744080c0b0380f550605104040d50a4424020200403410702c680c10f0314081c4d12099206242403000a1821113580e90750303655410800a1002940261610500f4950003210b043c80084100c0403440c100c0b10035094458540c041e00010034001c6034080f0006a15488030500034002c3c01c00001d41131560f241c03919142c041c0401954049001a0520380819000056801a1405103900910101092a2406014032190140c0944203180000c10481003452015885510aa01c0003000081d54807030070b0341000415103001045400030800101700c507001c07961000c0f09448a4030b05507000c114030003110074001010301500c01c0032052400400100080c90541000c014070320000164103444040d40d8403030400080b03641c61044d91621440808100700c0918110702c2d6010840c3c1302c7d010740701c40103480d03500d101049101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 764964307 1250 764963057 764963063
    0x1e0d08310606091b0302031009091103070807062a0b0a091721060907050d0e06070903020f03010b1e04140f04030930050309030a03120e0a020d02150d09 67
    0x941c0f0782c007000a80000c41d410b00c607604d003420190b01d50b050031600641e02844038450620380981d201c0e840020801d81c01460050348400a0886201c261030380880d58940d003d91140f00040340d60760980808518410b050700b66481040f40606a104240d0f4440020300c5d100148800411959024442c0008503015541c8041d2001c0381d24264580f0750394161010070445044181344060000d600b00074440c1e66402c2a1584030b60f051501e1521095000c0088028000c11712441401e0b004000400209a034403c1c81c00c0d085a00032900b120344039045c2d00900d0708a0b034001d1082508400701503482c10002c0c0c13031800c1d40c9007803c602030070004200c600c5418a841132003040e18a805505c10a405000600d94441c20341c0c0060540c03045200b801a45a41c00202d465001020f500f6090b03a07810740c6c54091240510a9801e40113000d803e8484240081c07078001d05506201c2030324146140f0304075491140c47c00004042622507405440754010070780075020001c04d4500440e08619842040200c2c2c880410580103005000348 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 764965557 1250 764964307 764964311
    0x3060507020f0a1416050a0311271b03040c06050307140301141203031012020103090614070f0e0102060c0912070b071115030601201e0d0831060609 65
    0x1200c003078490605e8000c0340100556640017009001c665262450301c0d0450390720010380d1b01705401e208081a41000d901203803503140c1c410407200341c0591a8610703200d40704560003069103001040001155027140416035025140d40344420702031098502410040d600240c05041c43c003058520b041c07000241d6802600085070790a0760a01d01360b002e0410203c1407000c00301d41c4000e07508519002802100f51103441c454602001001444c0d01c055901030b40c88543c41c0d50700710100b80103c0369a40e0096031905415071b4200c00045140c0ca18028162065860a201034816405800262503040c0009c0b0545c00090200ea0b000d0503c50b070441c0c40840410801c0c009122080e0328030b4031524542081c9295005044a4900561518004520b1030408508490f0300c124242480000c044040803074554450000c0f080054904c00c0c1307010802030420901061a6091003002201c00450030010100c40e20403090f0350f0703800302c4a255906441c0c1d100742600d0a551448841c240c41203400f100ba00c8140580f06158000d0441c55 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 764966807 1250 764965557 764965583
    0x6040b1207090305030706091b09020a0e0901050a060c060e19150c05041e1502100501080d02060f2e050102010b03070e060d150207060c021b060403060507020f0a 71
    0xc28164041d440600d07400e10030156441c503101c960701d0f031040300d00c000c3c015079640400204128901d001c1000c000319001c1e01800107a120383e4048006e503c0750030a00d0200380f0811505055182c02c1900c9030590300c01030104406546088000e070744000925404440503500c0d000005a1060104690703400582082c09102800c103407070802c80450859000d6200000f800c10203400780d03250f0000c04075412207081a40c00b400340380a04000d45407050f500c1e0080c01074188030440d00689071781d0004100c142c2041941c01000340740d80c0c5140070360380d03294028030300e0025030040790004040c0c181c601c0c1003070b40c094030710001e0071100224010281d00b00c4a865842e4054160082030a000c55642481403108500095000f021070301e08148100140f840b0040c9181e1040d00030301c3c644420000e01304020010200101001d40d250306080c81d140b805402d9076400301d0014030800320b4600d031200c00c1c0155a0400407001d0405840c041c110b88503180a02070007003505c01035100c4c8070740d03004a0000802c00302ca882d0340140d030000d80315 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 764968057 1250 764966807 764966827
    0xd050339011416030e2e0608060a1e050903070b070e1e031002070b0108010b01020a0812060d050a03030f060b1c05150a090b03060a02070506040605040c0506040b 71
    0x2840016040c041503030b15002c2c1032940700b8110701c1025003040e002e1030f00e114801d103030b08003c50240003040c3c0c0c0c2c0b00060248040c04482400081840c41a928140d540601201d04e03404008048410b640b003441c08513070040d008035504e0303040355101c0c8510b001100001c4440b84450a80c460a0711000d8446525a600006407001031040b503001c04e50708111a440c1c04070f448841c3c00000341803c4041d030000c2c03545228110b461500d5035001c102100c1c071352907104019915442103081c00a05a6400d1040040355420401a0040340d84040741050b0100da01005c040e0500001740714502c00c940d00144120740000c1e0001c1c010780826030810499102c14866034000c070b80440d0119a0740250b500c940e002c942c0b1200140040244198200700b06c4045050b214400600b0b9a82c900c8850710787c0690000050300b02550010200e140f51403504142600f52068003102c10780e849070940e1900320701c124040909260404804140094100e8010741e8005020700d11052443e030b02c40001814a501550080d204640001521404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 764969307 1250 764968057 764968147
    0xf1503160206130f0219080706030b13060e04110301060b030f0415110d05040501020d0603052109010921020405090c03060f0601080415060b04090621020604050d0503 73
    0x3c44209040c440c02d00c28500d0f41c44076110240081c1c000e100c1ca107850340b11107245110b00c401c08028070071402201c9841da6110743c0070b0010140d0640481c0209064180f010754010301d405520112aa000c00d1810785544540b40c0c0f0311091101424140c0c15521b030319000804010010145000f40203041d0301c460ba0b824240b41003100e00d20701000c100746080c201030466400205020996250340141c920210b400d03521890325500911801c11405461498040d01209001001880354a2151710541c401005140c5400c1040d10303000f0b004007240014516001031140c494510302c40c1008110320848002c85500d41c0c3d0014050703d20440d00e4650b160b021011124040c94100003450b0464407010003001181002800242124401440030340800750f11014101d2941d003c1d4040d41c0240f4009806035103a585a2003500050021481031203071100c5044443e8140100308981405c101d03500401c11031030245044203200000204501c250f036140001c1c40802c1800c40600b007103c0c500e0205111403c1c2d0340c01040c03d0582 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 764970557 1250 764969307 764969311
    0x103150f0506090a020904091b0617010503070306020a170106050c1204080a1214040806011d06011205070918050a0606020d020a110f0315060123090f1503160206 71
    0x30581c204000c2c00341c2911240070064100030710030005641c409402c8003040281030030007002040329090055404500241980d0102581e086964070983d095180c0b40090845a00b03000300c0c1d40c0740c1c215010400004041d90300070010082d0a041242c0020150044009400f400340d00c40e5002c40d40015244d815442c3c14008071a0004001030722604050400a00954074103050074000c2111042c00c51203020103000d00d204102d1603215a000d2070352140c444036a683c03140030a20800900d980e24002041c0d00c80c082400d514815001070b56507404091424000340701030f0001030440f0702845072481300814002244101400040444040802e02c0d09050810508407644c5a100e01c0c11500000400c07654a0340c0451890007007900180d8040f035950800001404482d0b800c0388032907061103200340c40200d6441e00d80384180b00e16000d8907440c6201844086c2110300c005d048018050f005002c006c59015841c013580c0000c0038480241c2405404d22100304070a642d83c0c0155406500c07604500704c000c0000381d042211507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 764971807 1250 764970557 764970581
    0x50924340e1503060402071109090d080106031b180b13030210080f0c0c01060521012a12060b3c070b090a0804090c08010b04060203040605160506010315 67
    0x101e180d01807103002c90725010150526111341d400185500901041104041c054000108083c403681401081c469595404020000115180d203000248540c041d20502d0174401c00d00d00c1c1000c00210b8400110b84603040300f1101c0001140042c0040b41103076091010349401032851461a40082c29401041100c0e110821f1000801c5969010440c551101c01c207075540001849408c1c035144c074030100985024040d2604260307000805050000381c0d440102c058421180f00c280300800ca9860f07480046400400d02c2102507802111450318000914402d41904450031014840081c0385ea480d1012100b083e80003440100741c00039404a001129048110b4021101c5000894015001c00c2581d926402e802120009000034214000050402400748072030303440554460f80d101ea5441e203681d000070082c1450201d50002803030203c008502e8201510844064132200c4d001181450b107060000c41c1c0355071141050b0b01d40c040140c03001c4400903030100145400f07140b0030b94043c0d40610501440c401100d816503019 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 764973057 1250 764971807 764971819
    0x8031b06090703080c01140a02090f04110306011b141f050712020d020702120624030604110a030501091a09370507031104050924340e 59
    0x101808110016802d4110b0303600c05005500e650903011104c0c014110440408281005c01c4100300c541c803115401400c80e10350441f130380d00561040405220454480c1707c00d98200c1001080401e5441d03014010001070104105809201e149050361742201c0754114031203508541c0e1100c1c03c0c6a130000b02400b41080f40c20030070b8604111915200e0300007406000010b4256a00590005409040003007540480b03001c26005441c2ca00c0d041102050381c0c0e80d400c800c88a01c46440e441060703260070f0b00c103580c90be0030b40031300018018000d0392076036124060300c1070515038140d0784221814400030000380280903130603001c0c1c040c0d50804918121500740524882c402030044005810000c00b840301d01c48140134200b454844500785280100e11200d41c1c0f2103480c2e042d1405011032160300400410801c448000302410702003510144899200c07500d076140e4402c5409141250224051178916140d600003e5543e409014a040c0c114070030f03000080c8400c812540c2c0080714191244804e65600d542d0000701100200c3e03000d44071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 764974307 1250 764973057 764973061
    0x106080109121e270e10060206070f05040b030601020106180c17061e0301020c01020d0204090c0e03100209010c020d0b060307050307060f030207050c03121e0a05070b190608031b06 79
    0x90160704800349800c040415507262404144100741d41d01e001e41030171100031940342440d10810051014130b124000c0148138280c0040c040d50b118140001040758144c403040d00b02410034010102ca40c2008100a0466585010018000303040036501d103c2d981c01090b000411140c1d10314010442c1c0171820754000152840001c3c01610b0b2940c84001d485098662480500340b2544400680a8803543c2c3c07080e00c2d0b540c00407075542c005000070350082c001c44152010820000e20107140c01d581110342802d9030b41d41901310004202040e14590010841594145820841c1540c10350014610000400d402d0303c0d4003807005c0c10071803141010000c40c0e0181004078010565180303410801010b01d0154040d803c00c0640100d0200c0400c0000c01c541268508002d082d5400c0c0c5005a4100d0500d42201103441c070159214130070603022890610454050b50001e58a5a141030034540b24503041c810060495510110500c4405054010341c0c41030f074000d420600051503440f124058003071940c402110000105420082c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 764975557 1250 764974307 764974367
    0x418150506030c030714040f080f1b060d06031a0a05090604050c1909020325090e010303050a0c0c080601140a080c120f0f0604060e030c1e010608010912 67
    0x949030302c03002450f40ba640c1c0f5680c4080483c0c414400c001171400070100490041394080014564505a030220b00c111394070301c2d500c05002079590b0045580801c0400c625024901c072401d1080c010403003442110b02c04140c2c280d0380d684204c2da035008605070039030301d0140205000c50b4490600610b50090035001c010016418903481d40d607190202c03007040d14465082e00c0d000145403a00c0b0a20035005010300c000840d1030f13160031555501c095401c10040c8002d00540d01c810b4a0b0f003402010300800f940c1c92240c401905030f080da175003641e031640704504503001c0c4100d149080000900e20035209005d4054000500704551400c040c00c8044090414410b100ba04400400d0080a5000902c03851032442115280d40c403c6e27920044c58104144880c00c4030042c0603c414004110350005643e6006500c1560100641314049040640368042d2034071003803064111060b4460b841c10310003441085072016500016249641d98089421100c80300340842c0d145808080b281030703040d001004100b180000c040040000001d0708 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 764976807 1250 764975557 764975569
    0x100204140303071a10090f090519030909180f120210020c0604020f12030703090311150d0b010509060a1206140a06050a0c021002031b19240204181505 66
    0xc0c214101d044c10032000a880350901d80d56100060901800c201b0010b020701c140107018184040c0c050f01d651169103407072801c9840e500c0c800c40380643c2541d1404045400c0100345c101600f10b0020900120b04001040d0000c150950140b0f02c4180c46140ca00c1c1c0d080d4803045c400380c144280301c0140c011b014418000c140f40d08101056a1f82c0c8580c2c1210f040c401000c001002400d061440802c02e8503070710000c00d82c1e000705600086564140c900402040c14144c1042080000e00500ca02d0b940035100020b201c0d05c0840342860f0042440120141015410302e44079001199543d004101d42c8070020b00000301e045200419449520081d2412110b00c000004251022990603a0309204110800c03c1c0040c0c0d60542a2141d0512140254020040d043c141d24041c4000d5403030b0050039031520360b020459040e4691690000302c0c51400450880004200150307500d5010b40c01d00251101248806c18029064190b25548018405414600c1d410000c40000c0080c0b02c0807a89040240e0022901c0d24005000da80c1d160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 764978057 1250 764976807 764976833
    0x90606010801140607020a17030c0705030321060a051f0305060328081e0403020414060f0105210112030f0f020703081b0d0f031a090408030702070810020414030307 72
    0x44c0c40320741d5110050b05c04200000d11130307444030700d0300c01380005889a040d0000c401000105600030445003d25112001c15460b80308102c0c3e00b8159600d003050490404500140c4160312210060550301d9403039859010441800340015001101c012006140c42d01e40d406121301d42c7c100a0940041c5000e181c42d40610880e000800380301407490000519980810500800320345505458444070352681d2881c110b440303016009070000b24441c3e401c0c00d0090300d6510382c80d0340003440303440d006040144008030b090055505074041d0072081b140f9007200165844848225003458020304000790202e2803181a404d00802440f600042d00040000444054a105900050502c252034200c1802caa84200c40c5108007181c800e14030985083d805141a074286076504038403200e00340401502c00b0310590500a11640c48800680c00066104c3c0307021011502086401c009581c1c407034000e0040f00d14140e110303091280340c20061070814251640015090046020010009032130103815401942405190313502c1c12006546 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 764979307 1250 764978057 764978059
    0xe040905010c1106160e12030a051312112403090a1b06050a08071209050a0c270b0301060317131a16020a051017010b070f0f1703090609060601080114 66
    0x2c01b4016040da03403249505402d55503008104c6e503481320750540c042c02ca9004410440d00d400481c0c41d00040c0901c0e541039216503a9880018081600045820001c54500b41510315003103104042c03501107032044010040d4041ca25000c0208030f1448a0310340407040425103481e408030010002c004101e01c0e50130030700f611504074690a21420540c0c03560000c46164000d01c038080703407050070720301d92005101002c07400450702802030740e03000c0c1d18a07101d6005074201c80e44210714040703d03a1402c02825486c03021f94040102c004000f0f0001c01d4440d625110003104002c0700d54540340381c00c00000c013600325156074105900201020f2080e4084000c00e900000303080c3c011403000071400001e0b044003004541d01d0703100c2170001d090700424401d256401c008000700142d20101050303480458180001c0745403e400e1055500700303640060314040300100341d540c0f0418103904001c00c5441d54903608072010303104001c50140d44142c1341030000700860b01e06094003a250001c007900c05c41c1401000c0300103000c0e44052000311100c0c514 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 764980557 1250 764979307 764979317
    0xa080a030506060d06150f050408030409050c0c0a080c0c090f060108091e010605120307050a171606050f0a15060c051c0509091e04060b010e040905010c110616 70
    0x24403940490500c4c45041d0300f0280691400c1e0380413039a481100480c170401829599000001c071034801e800c0c2da00748228012500141d0081c0010810100b2641000d54810300d0285001c0c01c4c104c0010400c0c2c641007100c0401c0b180080085000c0084c54410000c51081c8042100c11201da13080c50086403605480241116040140c1303600080d003100390802201c005070414031401d410070f504d1002418000c00e42401083c2c8240f0400205102100c0004191802d00f50450040c1000f070310a59114446140c3d01c04a8003c060014810f02040700ca000c411841180e004840100702d91800d41044031203000d000300020300c0180781c01d0117002d8214044c4800c2d0241ea40300d007020240310b030382410800d04c0e01c00854148440c18034098094840a98088003912501d0010380b40300d80192030300c041111300d40342c1902070104000030b040c0001d0040f0f492a000400900300604040d40d19001d4a0041030075030703001290a5a55030b444020b44414207500046500135001e45134040c02e154244031103840b041800280c410000c100f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 764981807 1250 764980557 764980561
    0x806030102070210030c0e240c0a080703030c080c030f0103122a061b080406090309031b030c14010c080304030e030312070207060c050d031a0a12020a080a080a0305 72
    0x618258100c4505903001800d0184d00070101038014080c3c0110400c0600168050300d084005041481d0001182180d0000e841000000c006000c0c5003a00f14600300b0603544150f60481d000702d48000001e0a102c2e00a68011401b010804406088080e02070080038801740c0030020080043e001e41d04c4641526404510641e1403280c0441c102d40e0740d2040310f205102d2440312840307441010204214182d4113441250306000c01c1003c00300080c845014009d20401040c61040040d00041da1648a0201c1901c241819040141c480d00ca0100000702080d03c05a06d45170a00144140051411840004d000c00c415100c200010800001c004402c4a40004e21080000c004103041500840b0421406840079040382d44900c01c6111242501c4402c0d102200540164200070450300e00c41c11442400603003000003811105224070f0121700510301030310400820000c00700710410a6495a259500030207805d150014169064010007031b0342115540071107030940c0051000e40000e0b8482c7c00781c9440300c80c0341c24001815 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 764983057 1250 764981807 764981809
    0xf0304060b0f010509061804110c0c1302030603061f1805040c0b040602100915020c1f0b0a0b0c0c04111c020a14070606030519060b030f100e03040510210207020901060806 75
    0x1500068279881d0741c103030780422203200e503510000703840c075200e601140c014025500e1040844101c0c8400d4580d180c141d08a40e0004280780010b009000d9075031a50b040d09140c0c070381d6500044580178541c0880d0749081e83c5420a001c18044081d441b880501140a0124a42880c12101070f554444d528a0340000e40d031191030782418801075607a0b01402c903502100565070b4001403404503803140d02c60041c594460a42c20544070080405104201c4002d4001d400c4000303483c01d11150310410340003181c0418891003000c240003101e445500032020429070034229a501e8204000400418080c581c0d092000f0f18814890b6a4005610071201c1102e40110b0380340f41d40d80d00d02810504041c0c0703450741001d040351203140540040a02072003081e612142c0168400c00505481e8410192141124044107000398082c0c84013100407019903000c2c5000301b1185003200c0c50181e80c2c00101e00c1e03541e003850161011030354030324140c4035500c0c20760264401040844001c501d02407403540001c0b1118410301640b030030071881800141c49 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 764984307 1250 764983057 764983061
    0xa1203050c0d0c0b31051024080d050405040e01090210050301090c1704030f1b030e15070b0402010810030b0c0d0507110d08070903140601152f030f0304060b0f010509061804 76
    0x81c0c1c0620349024003184070031880e01400502d500c2c0705408d0841e14403a001481d0310000c0f07550201b1484c41c0d03a4132882d2a00e000d00300300191982e020100c02c0e555a410b24500142e542404026a011042d11925201d40c544107612003111884080b803400d00c0300f01e200303030707992240310445003076100b549414806d890000300901202d01c503200c1d00708200318522049111080c16000041c80c41160000c07250400b104401841140d1240908140103020350350180100d401036000b00f00f02540b00d180c01141030150703a070365125003908010644079a0104000024007044400d1140659684004181064241d4244800382c50707690b000c8a03c410340420030088003098165102e01c40c1100255001044d0110101c20000d2240c0c490b0340a03c2030000031b0005501d29000c8070b0243d54044034602c032104a2042141e10303414100319585404002110501040182e158000b0751a0701450049004140c00504100c00e82d040c40180c8460034003203411b205043c0803aa2940d03a4580c202c030504410750115030700566410b4003080c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 764985557 1250 764984307 764984323
    0x60715050915010b1e030a0e1b060901030902150a0c02040f1b030504150606020d0201050108011e1107230c0d02060418090215090414060a1203050c0d0c0b3105 70
    0x1091440006c21f018800302180c004803505400807060381d02501c400301000500c0c000c03490041d41c20803001e010300b044940c01780c0d002500b187d001801138081507440c0d00c070b03c1e44d480c0c0c4147c2c2003c001c28401c1180f8820750926108a4a80c40d018610400030100c4006043c500c0c000004039030700815032143c00140c00c010003500c010b459000c11010502480e5203c060181d2580c0350001013070019880d040001840010500401008001e00b01c42181c500381d80c0700c4207030081d10750050301c0c0d080503030200b08550010313241a0b00211001c150006201603100840203090910301120113035889410301d241c0c080051b9481000312801c442240001ca185460f071480305102902d20000045d500c550003071a00e11042e03200b40002d11070301d001101e082050042000092112203010380e00b40e41c111203501c0741448000e0620141001503230090030300741e051072003144203a89040c0d6142a624002020226100704200c091440320740c05c401410800e070007a20b03130151182c45080102e007109400340040e01d04101480800d218a003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 764986807 1250 764985557 764985607
    0xa150212010f0e101401031d101d0705031c0c02090702032d0906030408070b10050111010506013015050901050105190c0809060715050915010b 63
    0x1034180d07039505800c6003080d8a0b40314042044039600c1c001a00f030300100f0680c5081d101411004084051107900440080c8036128183c04084660061000b20281c05c0041c0d25908201020100302444086501000007501800360801544101e0090015680100d02a42d51085026136024440c1408000701c2d140700540001941080e40c00050251143d40407000305680032404c0c2031903040503140516010700d900001d0394540941c40c01d110000a501d41103000b10303080790045010905081041e11031400c0c240090f035107854a8a0440360411295070850f00007641c00022100800183c944000041c25900812495250404505443c040445840b599040e00b040041504008030340681c80c0650620030980111803040074070200020701e540c030030012195410200e2540b50344904c1e64003021f0f81d040c803404030116180b0314140000301b901d2715008054042a40107403080120031048460080850310060b000e00100d030068807a281ca0030b0311391240141140c8081809580d14407007420380300e0050902007451 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 764988057 1250 764986807 764986837
    0x30807030309020f300f0709020c0c060f0702040b0d0206090409050718060f2405180d0503120a021603080411060c15010501210b0d0501290901080a1502 67
    0x10b001c820565a02400b030030036681c4070b11100c42071022a50b80d81e82d0400d0146c0400303510800d410f1040300c86e9600545922031110040301d0000003070b540021025001400205c06420380442c0c80402c1d45054013034035050321300960b00d2300201c0c4d00d1500800c80911400740464050340d1541500001c01104200010041404d03001d8401ea001c0c40c883c500e40038049a02c100a180301015030042402c034404107603907007180c1c4400d01e126495008e042080c3c179281c00012401110704210442413109840d00c3c120303042c840f1b101c1c00181d0f82e9000c5401185110f1207000d40401030725403062002843d01e403100c10040e40d616815080c200d030a60388515201e03190b40d440000c1180c21160100f0481301c04840000e0507a84034003c500d908805a072500e004441c165a502c140d4800301c640448510303020792869224020300701d400742c8410081030f440d4807001d00f5030b80d103050101c040134450543c56040e1041091181c6942100721a48289949440c501c9a540c00103488c0140c0b03040c00c1f20b8101e0036410301950442c6c110b59030400031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 764989307 1250 764988057 764988079
    0x302120a0e040e21070b01090c1b030c05150403020d0306050f011107090207060b090901110d050414121c15030303021b0a0308250c110a0911180307030807030309020f 73
    0x10131025044200e0441d29030762000000308022186005040d00000300b907903600b40c200c071606010070700000c600c00c4c01e0b010f2040d2203040501041042c02183e4030902014680704c81f6081c0b40c9402032070003289090700b03810580342c00010301c0f45903500007030b410131510240703800c80031b156030031800b20308055559000700c0d115440000c10000b0030041d50421484034000311455080381d0342d0900ca41d400c2c3c4403902c08040340c0901c10000c2198025542d4440c43d042805080520300341010b81500300d01d803619503407003841c056030085280b08002c40b9002c9581410822041e060002d9031a4101111741c0003541e010050600d40c0201e98103200c0040003002c00388901c600402c41c0c1e0242d910f410003804000c420380e4500b044802081e805021805083e0407071041c809150f032010402112903d481c40303269550b1000607400350354840c002662080a0082116203080000c0943e603803e11403548230845120441480c0c02074001c600300b040800c081d081541c5120341c0500f030200d42c0000c140300282c01103020b8082c183c0d0011922034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 764990557 1250 764989307 764989363
    0xd0b0f0a021c09050c090f190e060403020f0106050d02010206040b0c0c0d050901090b071a04051c020609070801060f0e0703060f0306150f0807121b030b040302120a0e040e 75
    0xa1940078041c0c800d80c1c00c241c05440038040e01038022120100607d80241c08180600c28034459040da401240100003440380f413100e101800c01d0025070342500140d200155010381000284101c000409007120781d54507600a60340041c0d01e0346402040509000308010003c0c501003812402c44070300744004410307503200d80c6034408060b0144d00040c0c200303400140300034808252000541c046510681d04900d041d00c604600d2411520364490040c0112841e000300c80784103c40c50000d28000320b0b070441e140c0150904e450004a0b6a00d410380c4c03580141240da050000800c0301900c3c10007081c0075a0207142b880030050783c62150580c003a105075440000f914185940001c1400100c0d0700c480c0b800f074482c43c2c20442c20341d0354241c0d00c0070141ea64080c00060382c018030410040d0b507500320050406503228004042c20710a412095019503044c41e4001d982143c0020208010143c0c1406080e440100d5128142d0506c40b01990050034440e80b012040c5c01a0740d50003d280001d40d0410500078040d0b0f100c2c041c1905900c0d811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 764991807 1250 764990557 764990561
    0x70e1e0d0b0703150b07140114131e020f0123130e0603010911190317071b0f260f0f0c01080108031e160302031201050d0b0f0a021c 58
    0x100c2c0c0342d000074540846440450030030010402180c000c020010300300242c0c0c0d00d44040390001440070110641d1303181e03c0b001e1300941c2048003521074440303a0940782c514807503030424042a00112841030014004c0780c11410040c0e0f00d0308032401001c1000c1c6040849502c1450046401e05c045001c699400b410118400581072022890f030010360f55120f5554041c0e440e040b052509907401c0c524018142020b0f051000310030f060016040743c41480300d00f00c00700020760b6915000422496241c003c11810000241c642c01c2c000e0380080c03603514020501c11108480c1c1b030304280c810380e51454020090032406030b8a8441d444081d00c0a111001d444000682d81c0c02d401d2a1036050f03940d0308151401046004048480c8119070040c0b181c5030480e0001c070061460b01c0f002031664044180300c8000d910501c041030040100308040c0c01c405925140c401d400940e990561050b40d0300c1d41c150305030705c010302c9000c28003a0080001c080d00701c41600031468031041c603020b4a501882d40041d0080c00780780c000c40c10300c44c46420850f103156 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 764993057 1250 764991807 764991811
    0x70614040309080613080d0b1c06060501050f0901030b0d0b0f16170f0703020412050106050a0b090f151605030d2301120501021c09020f09070e1e0d0b 66
    0x90700c41c5240e0303641e40c3c06100c0c2c40e42000c940c40d10711904031810403c04120300c50024003404a08010000c2c0000c02c20000444010200020740b43c00c0c1e1885600d40304000c1c0c24818000508070074242a4104030004900141610500030f00d0b40c10103131694000380c4e00b40c450100b840016079002ea6202100d1820107801800c1880031280080c0d03048a4100d000d1030355001d0070008104400c0011000519036a1070300e0000400005820a0201039003044002a0800f54480c5d01c0c0896100304004541c15180500304202e40d02660000d6070700c0c40040040c0042941e494903612000038040ea680008480c1030114a212401004070402550b09110130840400c24003000501002080e0401040b80c07000700e408030007091044440b041003281103200107000001c11481200c400d9403244002614000c1000c0c0c0d00078920f13240007400f600043d180c880d841c0840c0340c4685c0381800c90406a880000c01d1400c0d5400420b8045184160f5016160020704680c407120070303103480d10603010040c0281c8500b070000c0c40c0640f600307041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 764994307 1250 764993057 764993063
    0x80a15140c07020406051c170417031206030c0a0e101701061a0a080601050714070f0810291908060405060a0e0601091109030706050415051309090807061404 69
    0x5c1c1140105503494030203c13110002501400302d1040b031020f80e4942d134070500c80340d88106a040060100080d904050050b180e006403209001d107440d07855003030801281d840007600140c480d400401c644500c0c0d03150300381100112a66130248044c543c982040310030404650f0303001034030402c0000d81c29600400c8150400e804803034400b045d01d4188034002d034a411490244001140000700d007a40800c3c40c5621078005400a14066183d525041107029151440e00820380e1100120411541081000d203105001c0c103101603503c0b240c14405400080ca030042c4030001480508020401170781904890380ba0441c040d420301c1c45466090340c055854180003503803414121800c560134820324000406c584158010b1190b0502c1120050007140d00340744960001c6d00780c01400300c4031340000f40912145a40c00f00b01403030041c1826120113640e00d044c442e01001c07207c0c5011100081c01020001441c515504240c60700884800b8080040d10503014607001c1024406c01030f010701291300341a03030940302200040207503001d684 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 764995557 1250 764994307 764994311
    0xc0c021e03240606090118030f02011e0905060f04050402040315050c16121e32070213021303060501080c0108010e0a0b01020f070603021e0301080a15140c070204 71
    0x7500111031428000d641c0840c199030908000f04900f0b01302040603020a80c41418809101080c45c2512988008664030940300343c4107400c080829542c011451000340c01c1c43c0c00964421a15240000d00b03880c165102d03160041c1070025140d50030121003c155806403000800c25550b1783c0e0b403400e0980070b102035a421141c4852404000c1840325054408940c100011115044c02080e4240c864040d0604500d0b80321003880203401800f100d410b0001000c0383c041440b61280e4940c444141960f041c100d070f03100442280203c100140404c0401850b098540896040340e401540c1400c001d040c001038050183e80e0410b070788400102100300045901b14034162070f00e0b01e0440d081320600e000110b420000038451111901c001e4004100102416040300700300303003418011224240d1041701032a14003c92503018000195000c5541e00c4071030943c1d41c84031081d0445405e403078110350415000030703102e05980704010b049007800f0102d40001c030000d03001304103507450580e041e042d986800348002c00560f20407181244958 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 764996807 1250 764995557 764995573
    0xd0605060f04140f0c0412030f030e010b010c0f0203010f02030903041403010903140d060b0a0302070507091103131703070c120c080306100924090f0b0a030c0c021e03 73
    0x3040c280714103c1c050a48480300b41141c0c980c0c2140e07000100010b00350030f20f005010440419100c00c1522003503484c3d4403da0f2101c900c1ca050180060171200d01c030003290050b034108540000140c0e4051043c28500c1e400c075507051100100c52000900600041c40740c14200750010040021b8802d002c00980215140703601c1c00c08003010350b0810035088554062004010034211817200c00804c2c2c000c4058012803090100003d001ca445403040071403030700100f0744400043e800003085000c102044c003211005060003441849803050030103490042e404020400c0c001c2d4040410340070140500f40c0c40b101e00300700c071920980790b89040148004214031a03000d0b0a6503d42d110800e89079001d8400d80c1203807041c90b00b1450b940c0c25034455500700090300d15035025420070044070210220700201c10700030100d680740c0c0145040820505190b40604402c00c036500c2074242e6404d041c0c04001e020103a10880d0a1b01c14545000541017108403001d60b4480380c1e50714082d400030782c04040004050590030000181d13000490459a0b0f40b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 764998057 1250 764996807 764996809
    0x305090705010f050d1803020609010e071205100e010515240c0a0c0b09090115021e0312100504140403021b041103181213030f26120a02070b1308090d0605060f 70
    0x60b0b03103040cd958a00d035020303c40403c01c110040712a540c060303100b0025650341104842015054944294a41009035034601c10700420100b0000c0741011ba04c4c080c1c0e12280e803101c194110102c02c58514254070480e4000140303080c4a07580034821069440d0784078150a21050701c82808100d26000380b00b0986c010201e0b40c001203080031800030708201481c1c2d03da0061070000038901c102003044804030341c1e10996100c10302c404d24500450b00b04e180d11503100c0c1c04d0341001962030f0000b08000e5560905c2e44400300b07004402070001003640420701c401528152000fa0000307415441c0814014000041105000b103800300c1408050100541c10040d003481800480710075001c200c031440c11500c1415121a50150b009204000040c0041035040c1d411740100c4006580c80e2060b060f103007407007595804482c2d16080c005144540d40c0c400171112a00228180402c6051251558445c58020b5001d01040149494000064200308040c001c981003044040c01001402c0700701e02e4100003515041c1d503114400c1c5120055040c00e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 764999307 1250 764998057 764998061
    0xc05060f0a200a11011809090501060e0603100b03030d0504030f0e0a15031d010c1205090c09061e03012903060705030f0702010905190506070305090705010f050d180302060901 77
    0x210302115806040741002642d140e5041820b44c1d18014113101e40459a03802020718406000000c0483c039402081403645858202d08503820f40d00045040c80085050100d1030b2000035001c0e6034603e443c0320001d140340300380c80000c1c6940122000424010b080c44100401c00d0340c0a0341806603940b0903150903118000c02d0040010760815400307140f000310450100e00c4002d900c66000000146da50640e03500c05400310704141420754260865031004200308a030b43d42007210441c46580d40c080048409010f8101036030000a03501207019007000d11500958002c52003074400014028000d40c1c00030000c000030b0000e44415100c5408046c444075800035460780084180c11301040540c0302e000075035111869550340ba01c00703c24400d405030040701150340e00c441d8078000502c1042034854091403150b09050f002c640745081860100300070312903c1010b00b40780c1844052800002d070f00c403d403502420051201090b17240110395138055450084550381c10080441200c90b0400c0d10015000c3c00b9500340d8156a50750f030b980c0e0342 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 765000557 1250 764999307 764999357
    0xb0d06030b16030b032107020d0c03030e03160b0306040e010e0a030e0a06030605030c0127080102030a111813090215040f0501140406031107050f0c040501050102071208070c05060f0a 80
    0x46c000c10044803411000d20008018842c41e4401001100001c0c200e80358005045143d0700214045005003034407009600e820000074080c030b034400082c540c2e00d5042152101e16800003805003402075469220070415a070081d005813040301d41c4074040340c0124445090090420007008541e0340910075860000c03034401d00c240240701c00d0b994090000d0000e8400003004403143c0d9403840c4030020300d07080b290013007205084c4003030480f000380f21040002d6100c3c200317540441c040380c00142e650b0b80440010401c040c1c0c2d21807000d44003400c0d013500f00d031080c000a654003009805008000002540702c0841030001c00d0b6aa60300c000740059448484000c511662102c00544813402d2151045050110900c41000103900c6900800103070140d1046160803e080d990b6050301d0b00300c1d032411648060f00201001e0642d801c00f0300c50f03140100400d03c0104078003890808810ba040c0c3d040721000c3d1201000241c1141403296400c0c6042c014100500403070fa480800721038107407a6402140c00080010b110300742c00f07582c6000103081c0c41 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 765001807 1250 765000557 765000583
    0x9051c060f060f170c09042105091309023d1106010807051e0102011d010b0f030c060703030b060708130f060e0a050d170d0c020f0f070b0d06030b16030b03 68
    0x3007007660b0300700104000100f0081041700c031608d500c1800b08516410f4400e21250001c0b035141e0310388441c2034504120540c03c640c40300401d001c0c07034186140007681e50309840301c00e01c01c0f0001400c991200000c1c851100303203142c888100e200083c18224000096403104403074000800303240540c0c01c0c40c1d8903444031507290441882169400036010a00000302034ac482c85000e6070020500002034180600d1107400000c43e14096182d001e40d54034088015941420910061080821405080300384c05000000d903490103540c8000c0c0405945103c1f400741511440b084038a80c68008007481e803520580c0c000424011820f0181052002400e040010068000d882103c2c6400700200614516401c001c28030644140300401504c0c50000e141c10313a020042040d0060510350007100012888810f8400c1c043d14007810740c45480415440104d40e101c2106000c9264026075200b1000c1503900c20b8015903180c00f4080a0704080e1920101e13405001c2c207140544000320500c03940d510184019034400d8101515190144214 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 765003057 1250 765001807 765001813
    0x120201030b4b1003061203030902030f0c010f050a090b0c061e04151806090c14091302040c09080303070207061b0f17120f04031e09051c060f060f17 65
    0x400e05141640c1d102c490001d0130700c2c0004080d9a602d0314148070000000e41940403da070380700810250306040c02031071415199040100006200c0000081982c141e4841c4d0030200480807805920072440380b001600141015644641c0f0741c414480f00310b4454900751980502000d0000e1414940306200401601c01c541100800e034002c40004443c00c06012600403018443c414203000d03800040c3c0b2889014540342c0268a565481400c00b0454403500e049070f108103109051000c00c00c4400c1c0f41c0349030305c21015581905d01007100c6000c50000c3d50700080030b411181890001208119001c2c0d40003c40008480c0c05503902d0720f85041e65040c0d00400b40100b00081c214032001058030000c500c0d011120388080000440e01450b0440c0b184108000c1c04080e50120890045003044c4002d05600109148001c825080349080c070314103003a0060045e042d2440344a000310448004c8018003516250103454460b0800000c1c014901c0e40441c0c80d0041c5180c1c018480090b00c00312000c600700100d4540484811561801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 765004307 1250 765003057 765003199
    0xe0903040303051305030604060b010801050604030f0f0f05101a0109150f090f060e0f12060a05041514041b140105090d02150d06080604030504120201030b 68
    0x400c4456038007803200400c05413640180000c0302d4608025040c400e170700408000620806130b03030004240d110180e01c40751086506200c00c0c004900f0911170b41e588160f10038075030144602d0b039113040307001880540383c09011801809041d1181c0c03607051b00300c44011a8a2814603140301d1485005407500306040c0140e070703900d001d11000f9250403402040a04018200c600f05140802d40c4c64040380418403440d0030050000b5103000c001100c0c0e0800350b620700d0a40030111542c020303640340b40034115500c0c0c8004104200464442c0c003c1804e1101000e04100f90b041c0400041c8849020301c40701c0c03101e600085da0103c602800c44011100443c80148407035050752259249942042c0c01c000044030f89422500801e544000e41c800d0700001a903420032111411207807881c04076241c0315200686011590030364003428503904184104000681c0c02011501035500d84403c401e014101e600041f402403a5035142150840300c40480802694410203000d1f0b00c08001d085281c09040030741c07900c110079040015002a007811f140310 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 765005557 1250 765004307 765004313
    0x1005070c030f020c03070f0602011103040f030f0e090c030412020f0601050f0a050603010906051f1403190f0506030f2b050d0f0510050607030807050c10050c0c070e09030403 76
    0x11a10125040c91040341c804a00300300005c1d050045170740c400c107014400c0e02010000b4680a01070140d0b0a0380c0034001d00d040d0b213496160354143c4248100000e0811408802482406015600e0034003a400082c03d4120b043c83c004140b65159401a101668101d4015400502a910005401c1000701d070072005488580d1070f1a042c450000004000700b82e1050b070301175000c58107880303140145000f40680d10b00810b80a2805040c0010b00f5116120b81307003016202003000c01410b0300609004802805410b005649988003400c060418110940c1c00c0011802c201060f49c82080a40040340940001c17002c0c2c81d103e41484c00c5e419600d05010040c0c50702d01e0054081c044000301d07180d061488081c03860515615141c0310b10070403811101c0707550948a02d91358942c00e1100b55030901400002622094070014a0200103890140120100400700000c009000400b90f400d0f1100340108500350ba240c1d1020311050604080704030054000001c0c2d24203500c502c4200181280008181d103001e101c0300c002952420381942c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 765006807 1250 765005557 765005567
    0x80f0a11190e10081005010603110c1c0c050f1006140a0902030942070e150c1506090604110414010e2e020d0f051602060a0504081005070c03 62
    0x2400702c543c3d20b5000714001441c490074052800c082d444240e0000300d56051100143c101d030b0f44504040140130301444401000100021804480c1000072890280005090012501c60680c507030000c049014607004020b0450700012140b40d401d000200074401c458542641104a03010119802c0d44150382d200d08100c2d00301658003e540040800003940e5030b0003441c001d50980d0a07010107102c04034142845c640120001039403403040e03604120b03000c2a01c0c9801c0900700180103044042a041c803a842c8044580c2d110803a03003007143ca54103821000d503401410039400450f0032040454a00c3c0c0107650702c0300001c2c05490544540056070b290500000d003003500702103010100501079a80e090500c000704d2496206551151400130060613010045000d040b00981840c0720440d00c190700708103550203a4040700d4030381c1d081125143d02e01401d1400c1502c900d83d91a42502e43c03e00c0031006500090001125910154441d000344183d8950b0f000b2a0510266203c00da02280d00890703211000461205603070001070310030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 765008057 1250 765006807 765006811
    0x100c030806040207020402070506160503040206030601110a050f0c01020c040207050303010b0d0905010515030c010c050d0c0f08120402030f0d0806060f07020a0b0918090a1b080f0a11190e 82
    0x940700605090a45e40820100d0348a03007410350315948080d00b0420b8510a9410b01c15a012080c90241e0540c14241e02080709400084d0440341440360681003011881010001c1411141c3c2110844108480303080c0c209031034400300030096006018620000d0b001c0e0401e4000c035621650710200842c5960700e401c000d1480c58101c80040e804960701c40c0041d102080090040ba800303400ca60781120180c440c560100740c904040702e101030341400354194050001c15404901000c250100e8144034112220b54074001c80d0071004518004d104d20000300c1d01a04a840180041c2e00c520310940440d1000502d600b010742d075840c2440d10117000202e0540005400d410301c0e10150210341d0092904078240f10341c1e076000076000445500402400b05d00401c5054481c5011801120301400c44880c2003010f0500c3e42072940c8039140450094045103400340e000036041d0102020200611318902030321038400c104403406854501e41c0134287d48100025003c020302c1d161001007580703c0d21042c4040ca0f015031804400072805040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 765009307 1250 765008057 765008059
    0x5060301182408070e2202150d06150906080421050d14070e040b0a09110702180708011d06100302041a0304050706020c1e2b060506100c030806 63
    0x85a580315070b40354120034100042c0030341e00e0240008a05004400c80001402004035451004400040450034290114040640c1e01035442d11803103031f6190541d400e5403241e424400304240c504040000c000090400045a01e0340383d641d01e190781c60b80c07200c0440d00342e40203030b5014103070701482d0b1016140c00c00e41040f0888840103604000e420038482580010407200714403801e503a6003903a04200141140c1c0442485682c0c1c2045070208101c81c0140041600e0400324001c94401603502c0180b070580d6190703941070f1180b882d4000d018401c26528601007000c01c82080d04c1e00030106040000200b100c2c2d120b07860020203042100d1091940ea07880d2010030a2880c91895110203155013008040707107200552610070340140c61180d0480c0c1c0c0f030601c1d10700149000d425601803021034102212944d603554034901030300c11800c140001c2c088881078110004452810b046407808941a14003109081d48074003595000c41a4001d04080016590b00420b11500300203420728200025030030030051780001e0090800b603401c644 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 765010557 1250 765009307 765009341
    0xf0c0b040b1809070503071b150c0306060921060f0c230711060306040f0e0a0309090c1715130e06090607020705011404080102030c09030708030f040b0304030210050a0b0a0506030118 80
    0x5540e201d180c00000386142034103c80e82c8590840d0ac4140c1c05004082c000c05070380c501584010b18003007202c0c000e0f200e0b0403580302c000b12100f401e071024018141c200c10042d80007e81c08001580d401100a070a05d4083c01142c10880452041160b02d0b542c1001516011b81c2c00040c03507080419074200f006074541c0010601580160380742d0704200c0041c201e01c41d00360008218ad00a196214a030305000c1c0603240940d200b07419107818a40060a825409000312082d01e10710242c40380306499480140c41e108a1451032260002c40001c414229042c0f25008841c00c22114400d40350507407a4945200e440d400220740820160748604800c000d113503c00c0307801001102d4402000b600f003030303141c80c0c0050a90b8016101c641940c500402c0000321407905000c9400248400c400441c582400007a0011090040e8841c041c121f00c00840050b0505000340480354100e1100340c030400562424149043c001c3c2051100300c1d01907200808041640e0401c0012203050314802ca401c0a0000525051040503140801c11a24251 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 765011807 1250 765010557 765010607
    0x170604020a02150109051905090706030b0a150509040f090506061002070324141506091c0b190b060d0e160e010614030c070f0c0b040b180907050307 65
    0x3c12003410b14040d00c103050012410b814070302c200e001440c2500000c240781d41c0c42c180920050f40070004882080343c0c0c03103050114038909504005045500941d1101c13246152100b00154007507888801002c0c00c1d40b045030208071615298038150103c40d0b510f88010090341c01980802c402d45441c194440d00e400452046880355600c0781da5500c501020700c220320803103981c40402804e05081c9070180b090310716415400110240340034040d00412042c0c50506601840c2e00150b540341d00e440d01c115401c40c40a8100d884034680a04d8034149469031411a040c240e13030300d80400c2210300410345009042001d0001030081d800c0c200034003582030060000515680c546d10484145038030100840737845c032000301a1710221215541c035000f80070f040d5408011000000620400030401501c40801c155500142c01454951030382034030b071504036074158143c1c101e1107500b000450002109070290300280040a204041e5008503d0241c080c002c8000c41907d0382c50105000b88000788400b4030a40303080c0c4000344212500d078841 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 765013057 1250 765011807 765011833
    0x11d0a0911041a0c06130204090803010e040201020f0d0f0e120a030c03030606020105040803041b0e09031c05011202060304050a080310060e0a24020a050f06070f170604020a02 77
    0x884050703888840c580808501082801c03204120b072450103070300c1e18510f85440c2c01d100c189070311044000c041c0c508190080141800f9500d07241c2c00030000580c00307220280e49503118082c0841c00d0b041218124014803076050602e00c031001c08100755101d000c440e12028001501c0b030b03000740d550100011603160001591503054034004000c0250220070750094980700405a170609000741918883c0e00100290381c14442804002509107003201e503c07542049644155030b4100040768070003200d540c044e050140310141407190200c001b00041c981030110300d001c8403417039840c9030014098660901c6800d84486d80500c106000d82014001540e006210b502070311918601652840755035001a165854a8542c2d00001d110f1540c129400407074041d0101c4241011500e0240e81c44a588180451061a0701802100c420b00c54020040450039030f40c05010350709944008840559240c00442c0c4000001d0810001d40031000d000c0c100c0c009070951114914003640d030703a02c81444085c4d440b0410001c2148114004c00d940 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 765014307 1250 765013057 765013061
    0x30c141b01111f0c180e01050f01122c12160c03061e052a130f0b0d050105060a1b082505070503010c05041401050f0f0c01061202011d0a09 61
    0x50000c010006000d040711070010610942c0340350701d0407003441250b010301c5110229031b0441c1c1105c8003101d0700300300100c0c6040102c42c0712001c1c240343c098503410300c88103035001410100c0d1b40422100c00f0010700554100c220006a0f614003450307130007959120800c03241d9a81002014200d2065002d0b0010306c2002e80c0c0e95485000b162000d120244603403d80c00c1c035034003c041060003640d42240b1000105800350901d4403210040030644900d4802c000700c0000c2110b00e0340440c07542d0303d006144914880b140c455807800b0b880c0c05940700000302d450700c61402c80040359520b019410b40750f1181d80756071181c81c49000d0349e14010529802944c10303210500240008518954040e45000e50f400b40c1000740000b2603040e00d0030f10328200d00d41d00482c0c842c2e414005181e040c2035100080c1d0341142c0c203c07103d200d69200c449006076550301c078600340c0424251000030b07400300100601d0010210284184002c0091540d2070620740e40710114008020300152a0705071082c002035800e40050f4405800034980034180d40e6518070a01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 765015557 1250 765014307 765014353
    0xf05060d0227181608041e03031a0d0c06210e0c10020d17130203030723030306280f0f060e0916080c090607030c141b0111 54
    0x155500311109107800d0306042c41c0035607201d486403e0740c0304507060454040140d44d0035000c9104c02c000c00c800c009020700c540060001181b10b1843c0c0740c1022003180342002009881200031000a08901d00c00680c170381e050480010b105150000c02d10314003107007844000c4071a40401c41c0d140307160304c40803600604841024803c1c4c8140900707460080c1031180c0b045040c8616039200764510400d541007205241c0d40c4580280780c0a0b03500051414400e11640c0301d194110081a0000d03020b90184008126001084109401c0807080025170342183c400841081c1d255540b4801228025008004058100da0605c001c01c0130000401903004802c1d0b010340c9842c00314480d004113a2050942001766201000543d42145200c1e08a0000356041c00140c5008400d00e80c1048021034094100600c0c0e50004542c8104101030350709020380104166a105a242401442c11801c018140d550782800d420b9000c10301400a035483c1100c16103207240c1000c9850500649070400c0540c0c500150380900c403c0e00031284800c49000b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 765016807 1250 765015557 765015607
    0x30b04060b071214040b0f040f031412031e04020102010b09090303010609090207020f012f031c05040317150301050f0714070f0213090f03080402030f070f05060d02 72
    0x16100c1c40719082044850f001607100000740304040d80f840d4550b074580b0046509842d0700e0441c099881300103100e20f00700381c86503034004480303103908032808800c00070802204a026090f00e400c8842503c00f4100d00042071105480f0602044100c0c03010004000c0400b11060f4440d0050000040303c4124a0100b405180100c500441c0c50b040000140502908401e482000d040007880c00c500300016580441c4180d0318090b003050501020810401c07901c0e0b41c182e208007491b20741d40c040c2c9906008080d01d6a5994001c12080001c4000d0403003030072458034451144510850b050ba0303484080081c4c032800c04c4024100a860003400d0442c446104c40161070034044c0d0f501414600c5012500c1e0b242442e0010304501c40300f420700752558801c012101c0071414440d000070400d50112040c40901c40d480c0c0b410001440340080080c00716410f61940340c24581c12000c1d59114034003d90030b07201120440b80b0403540380c1441d0300450074810303400030040c0080c0c01c2100107490281004880107117400720030201c04590038a280c0f940 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 765018057 1250 765016807 765016829
    0x180b0711041d0a08071704030c06030c030513020f04020918090114160f091a0c120f0406030b0f1c031115160c080c011d030c031207030b0406 62
    0x902070405100301c0c07101c0148020314500c040c0341c040e50b041d01c80d1145003000d8043d44001c2100000e218400c80d101c5030b558042d48006030307296600d180000c040485413103084046444d14110700031243c002e000e400d218070300e0f2180e0b42d44514510750070480400903000304150016424010f203402911801840c151100c82c00c12118403525000040a081d0307402c03a90b140313010030604800e0081807000d0f40c000c0141c544c2e050600030445c9400e00303421140600141e004040195140e48a403480784074000052262203289030584c1c0b1401a0b400003041d45220356100709039402c4040004000841c402c0e80030358600c0074020419941800300c880000c513807017000e080183c1c0294003128076604154102000c2c17503e00c100e00014003405050001a030304101801040c18840d25910701145003098800d41c40303000401e500001c4030744c852800d001a0381c0285854036690351003010965032821082c40001c02c1da2a00b105c0a4011441d291242c050303400c040401514030030034581c030b6a5170910b083d42d481c050a07014225034916 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 765019307 1250 765018057 765018083
    0x803070507110303070305120901150e191a0f1903050f2e0b0f040c2c0603012c0103031d0103020307080609060a0803030c0a030b010809030a180b07 65
    0xb01c1100d00300340e1160b038403da00401c040c800080e000015244101e900200d11810340c0e66201e0ba450141c52401310300c06490a442d000802c0c2c4402000303456000d0714100280701076100b4128114030842c0c0c502d980c160f030440d5010112820914003070800b0034104170041c1044150f448910088a011141d0b80c0084075281c000715020320070b62000b0408081e5010040c442503034100d071070006040000b58420004410592103c030440c0441d12400913203054801c02600030400092107500040505041c130407440d0318034104104504d080e09801c0707480c03200480000d002c0345c5980d2034180a0018004003400c0000307100300401100002070207100507075000314029180ca1069881000360b141e00507004120040c18144107109008007244d00c4001c0c1070f8044426155545103444000014000340d0299010710306a100020402c182000c1034409050451380503201884025941c1006645942d411162402d403903000f407080d0f825161155206075442030006851a070030360b40710b00061078560301c2030030709488041c1c044070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 765020557 1250 765019307 765019313
    0x170c03070242100509130b0f07080105030703020102031c1107061b0908150c0d090606051507120c0f12080f06040e100209060408070f030515010e0c07050a0803070507 73
    0x9003001609580c0d00c02c15480c05040b46014401c05029072030188200c0701c0054207120000800b95440394000b03030001020304c0d10504d035203a4014100d0360750002500e030070000159030900240210940798141c000c1d42c100b401c216400c07400000050502c5001545422441c8000b414200040c001d5034007458003c1116910464004040c10b4105080020040e030381804004642e0b0220341000c880c119041d81c2c503060344030080410480d00440700c007001440c0c54020a1b00402140b54464411074806503520f45100d0b5500c008440d190007040c401620038611420903104c018492030380c0101d07080c1305651885424a030764aa8804d07120302c0e1845500401d000d8010b001c40005400401540010112400d008400d51201501e848103059640700c90305a80118400380150703a6075041c3c034060104c2d4401c0b258100e55542c1601c2c0155150711003a1514028640291106d00c3c1c850101410b0710215455118647c80d045590381e450f0740000e034151030b00d00901c10280b001508000003180501d9455880c552a154241 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 765021807 1250 765020557 765020653
    0x15060a1a1305060310050108040f2109090b0d0311210a120603022d091e090102031302010c030309150618060315090503040b0c1b01170c030702 63
    0x1400691103040c0c280304100c1341c2d1030110340ca48180c40c4223207030445c2e55840740d00d031903400d040302e09000901c0c01c0ca5081d4444801e814001450000b0a07451799050001c0755191801400c079007801000350340080e180d00d00d04020038003c2d80b03d14150f04420080343c10122101081e40c003c994000e0030390000920000fa03d50322182d10a81003100980003190401a942c9103074001042c00c5940b030b10b02c4e41c1c2a01c01580e105445a05d03041044101078004e00341c94450f01e4040740a0401c084c005041e100c0080a2602188407400140300340c0748160280746442032000615001552b00c034000d20011400c144c4c5031465400025844684282400e0a00c00b01092131410141038140040035104c8031300c1c10300e10f00030f0100086030718403007050b20804000c0b100007608403141c18080d0551040f50446008040e00080d0010000000604011034041e03803411500da0b40169801180d070610a112044e0a484140010588041ea51402144c00c000540101c5030703d01080e407414182c200345001850541000a0b0000c4c2c6074507026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 765023057 1250 765021807 765021809
    0x251b03170c0703140106050d0f02090c190e040f020d06080607020a1a070905030d02030d150e1f120c0906060306060801030f0318120c08030301050315060a1a13 70
    0x9920041c1850242281203640365150310018280d0700c42421284c84101c0300703500c044040c03d409004107905010700c0c245401c156150792001c03805070070400009220340c03c2c2d81050700c0b002e11020b0003100203100341c0c0d581120b016007007072143d44d400f0341e031100101d403800c0980c40245480c418820011072041c1c42c255815048c058000c01380e2055400420034000017440802000980c03ca00e4520485030b501c4c2c1c064112030710001c1c0d41002ea0188100d410320104243c0010140001080200d010f01c54111001c1460545c2505482041010361407031010400042000681c80c5941c0c0207040080981030345c03801500d40c01c2c2e034005801c0d91503541c0003809001c8200d103809031401030001400c06101607071801000604c2d8140520002e030550081450700d800300761243c5c504500d81f401c1c50700040f80e0369454a0b001005800c0300c28044a542601c1100090041c402005403412158000c010380354404038118901b000d180020b0425600402c0504081420241c101c000015091071007801501c80c08c02e250601000807031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 765024307 1250 765023057 765023093
    0x90114010207060809280206030106110f031303060b010c0605010b0702090f060a05010c06200306010e09010e010b070f06020a0804151b120f0609020d0b06030c251b03 73
    0xc04005c100d01d5910004e100101010707206506c1070121148907031183c090b80720f1304c0000e50003540000002861640562a034202d02200300585001d087e200042a0f40c0f80304e01420320131070703820708034080001c180117500080d4034510604241052002e01d580715030455109800c80c408141003c18110b00307500f4190051940201161400c50b100d041150008103a01c02510801d4108414180c40e80d04112070740d00140b0307648000d41080001c15a84480b54034407030b002114504d001580000c0d08409510380805210304850b02c8590341521079080c11509503556011003015a0500f94202d40ad00c0080c00c50310080603840c41e507070b503507540ca41854504282c00a24806005542c1c0e170402070701c0400042049500b03055a206030400b507503c00003014000015010b00c40350b42e40d80d02e10345040001c40200c04c0e00140400b155242042050000b83d6040041e180030644440c130801d50305202c41c00c900c1c00709000d20001c030036503801000300c440c1e80380d41d8000324a0298030740c800e54600881d10400c100074404c02600300740e090b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 765025557 1250 765024307 765024317
    0xe03120a0e36090303010e071106161e0e060a031118150c1903111504021201020f0d1d0313091503080901030b22050414011116060b09011401020706 65
    0xd100c1071084d660b01040c007414a450b0b00f07101c00704846901075000707141400c60360700981e202443c040b4007005203100a0a81c510208109403c060360810b0301d206000002c5481d6151140c01e80c4d0b1381d00038400c8079042440c03400140b698a03640c100110754500090140d880721200e0b03640a403a00c8030284100052450001b80703130410140000341e1407e1020400e08036407042da466994103854a4103040700d07122030103400c0d1000c0d402a408001c254440001c1058410341c026100d07400b6804800704480e080340b0851404000c0240305203c100e00300c1c0c080c3e81084589021014072200c080d03840e80c06407810742d0301010800c9045031052030b00b000341c01c07243d0081e005100b1100d10700f1050146181c03540301c0c0c2b40c49640e14140c101581e560429180c0e41e070b560341f41180550030402809000d05007610700001418240c5050310a50007500000c0803181c414000d290480203403e545900f440700e19580b1030f607036000308502128604e03102c004007030306920744840c050f000381250074403005244200000641822950b410000402c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 765026807 1250 765025557 765025561
    0x50105010915060c03030c0e090c07051e070b0d020421030207060302130308030907090e0f07120210051b03270406030b06100509030307060c0f0e03120a0e36 69
    0x1500180c0f0300c4d10454041c1400326003070040c060100d814a1070440095804030082d000d0003071280894001e0f0070584d204404890102c0b00085512450003822603407455280e1003a6003c0c4905074004014018100010300054180b41e00c80f41804441c11984040310744854038080f0740802c0c076504200c0c220040c05541011803422051941c80c40d40e941d000c1c0005054442c001000c00c8400608100c42c2c8000d241c0d96204005d0300165085054464010454034801881100c0001c902114821380d20040c040d401001c104075940c0c10b203416592500301441c2622a049605064800c03020240024071358100702d4600101d044800012140314000d402600c0342c021850308034140300240e996001c4c250004800c89040c15030040c100003c80e11172150f00d1005402d400046004d07400c0000c542c00003140c101d425142e42c0c0c180304a200d4122945005001803030341c15130200c40102a4001114010030320380c80140340042d002440c210109aa1071031400c488120404500024403006030305088111612441120011082c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 765028057 1250 765026807 765026819
    0x130c020d0507080d0b0303120108010b0a090203010b030a0e030c1b010305070e0a090209030132010602211333021902130902150d1b0c1b050d050105010915 68
    0x507014440b0440703809599022400c1c4265001c1084e641d11540e0122074023100c1da1140c0e2030a01900765050007034026000201c0c00710b41000c043c02034078140c41c1d8952446055036180c00c50400540241c082d03142160000f042a07417003000d01403003c010303e1403004c224694001300c500300040c01c80301d0040840b01042030891151015070f582000c00411a2013500015880d0b046d00000240100004c4905140c1c1c065000020748800032603840e40500c0030600d503100462680e0b500c02c00c0e601e800340e000c001400500d109210f210860806005031691645081802000a481d4840000b01c5280220791148043c11010b182d050707640400320a0b880c07812075101428121003007220f08284c0001613200284a0075006500e03048051041d400b0640e12030f00205044002c1020350b01810b01a4060f0314031111242c241a40d044162100e404030004240c040c1d80c510124024903120904511001103291641c18046440091603a41d4110344451490184000203000d500d420341c00c00484041030410503d0f20300c0c00d5010401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 765029307 1250 765028057 765028073
    0x90e0c040e16021218120d0203070b0411100c120201060617041403130806011415030a290108010f0f0618030210030e06060406080c130b130c020d0507 66
    0x2c076580d90040d151070741c41481e090781400e01c490885449100041030801c0c140606201c1c0441c1000c05941018400555440c05901c40703080d1b2101501503442004040001081d04518943c0304e809801c0030400c40b03650800140035001c0c03151801c2c00107621100500c081c0050448990082c1203940001c0051a18001c0c001c2c0880f802d5188000400104400050a0102c0e5080c04c0c203100700e003c010b490751021180580e69410001c0d0140a0061103014000302d4150a64004104107070741c028000f03040d5654003c810161607000801c0b00c2807842e166078440c42c80f6072542d03403403a0104000249a036201021040014810141680100a2500f088104103c214a05101c2c002500ea1920301184103644984500202c00c407103500c001c0d003114400e001d000703609030b00d68050070315540800150369103500d03100d00300820794400340100812500598511001868460f450700d01d065804040450714207a450006101c040b4400c3c0b00d8400700e501d0300c1402c00307100d5042c002c111082890b803d09506003441503d800003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 765030557 1250 765029307 765029311
    0xf080603070315020919030804182c0a020405040804050f010e09071803210e060c15071b080a0e0d030f0c17280c020303030c0313080703090e0c040e 65
    0x40c020b61300145140203510b0703001c241c94001d0031401c0c000301400d560780380060059100d4411140903448158070000301c5c5105014030311032140803840d0030181100c00445a0b82840c0c0d4911428594803c02d5504001070b211405002d104a0084600c6616135140405000d81c155484140d6030400c40300d4800a0391554070071341c00e10340147c0c1500d0700c04640d0310410001481e4854941000d4000018040101e030941070507041030405040c40d9503181440c00d01041406854051403092588582040c010f40701403165a0001582c002100c0c50094888105a0451000301004040603a00f80600142503540590010001c02d82c8078001c1e110084c0030300440c0c50007001c020080840380308005aa01400382401848046000d007411810107017952076055104c000101003039004504011050f0580742c0c0b00c010301034400d0b105980c0e0054090b40c03966131403840c0160254001040c450001e1484800030000c2380444000e825820300c40d4503420200c604001503007034405001440051100420401070003000351151480d9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 765031807 1250 765030557 765030593
    0x2010c06050a06030209161805091b0f0409090b070e060706091a090a02040506151c092f0406050d03030c020f0607030b18091e031204030f0806030703 66
    0x1d4652910038001c40a000258000382d80b10352440248403c0d1301d400769150000700c1a40c0c56420b0003018a9101e0030044a41c7d01c1942c1d8002c10070340002e802560f9406203090460103030044981ba200b005903c45203160410340010741441d80d103031001810889442c030100e80000590130311000030103840d8001005440744040007001c0a403502c1c0e90208001c10240308000095410092441c18030b4a0001c8580d180b41080c0140d1060f27051a0102d50f090600c1c3d0010038000e082003580b02e00c0e0200c41e05011000400c3e86d0303c0c0c0700f0600d503124050404a00b0340300d010311050038403403221019010000e8280488801c08500b6034403851401c0004c110320340c1c07018403078220213605082c04500c21030481d5083c1c2c00c100490051180d1030281e40d04222040398560b2100181c1e102c2150315441c03a40d11051a800039160494a4640f6903005071012042c06140c81a10040f481c411011a8600781e804404404140b000751070440103d2056003a90004903000360849901c92403d50003822030a140d41c41d14480ca01a590041d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 765033057 1250 765031807 765031811
    0xa02031506281208192a0f05060c0a120623041815180c27020721170c0d1805030a0e100819140901050a06050d02010c06 53
    0x290030160b00803095440100101200b104000d009810311180a0744580310100c00c030115203c1c501050b030f014905650b030200e02c44200d2200441450540744650303000d4141500c00110320441c2e03100103882000300c9440380404682190301c402d10300030007034030180b6104d807007009041c02c03e10180814406002490b010081c2c1c51a105030790b00414000c100284040e0620f800f600e1054507159060100c01c581000526001e00b4041000002e070344559005024140300c01001c2d00368bc60310410507440711412800124070a82036421500c0d000100110490384542c81c203c881c034078a10810111320309181c6400f5459002428900014010340c42c00ea1204000101f0008221a01080c02c06451210307038044a40c5102c0c55001081d400c0203414090317583c0c0c10019010703001076000300104207141003141c0310900c0d4030a5030f01e580c90b56489104040750081080300603007814990750714483c00c000a407502d069010703192540c00002c50782031140b0300e001542c07910780060b4003c040440e10f080050741e10900388410981c200c480 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 765034307 1250 765033057 765033109
    0x4020904140a050703022b0b10080d020a0c120312050c0d0c03140703060e0406020c15042003030a050f030c070501061509090c09140109050a06020a02031506 69
    0x80d0039001440300140191040390450b40421800007080000d40340200c81c2c1c68401441503034868042a0042d8041d020ba41002d2064400031b0010349040c0c0d0829805208119040c0d1240c5940d4504907698200e080140c0c00760340801c06200f40c1e80b0b24180070303050b0f84120158031009600c0181404080c681142c85442c0d0307580000300b004c010b520954544c511451410300c01006900c20080103404502c2150b103010710703140e0204d0401c50091080300b0844495408030245583c2e02d0700c03503100940000b100f91102d40503080340c0b00ca00c155041c201e01c3c8103500c41c10014070407a25040c0e249000d00310313900805010703901c100105901c01d83c000c0d0a0b10b104200b80c68200343d407a40d52864142441c040d8000092044d801c0020105942d0034119102c203040c030460342c0b4100140c0da101d440c14103840780064020081016114144001800b640c0c100b920400181001c600c0d5558620100f51074208941c03007640183c125800b224210300d01405194150810ba000049003400c0600008801c42101c1008030300380c030f448140c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 765035557 1250 765034307 765034313
    0x4020d14010e030c0f0c0a060f110109060504150506030a0b0624070302070e0a0209010f03050604021309050106020f0a020f0108062817030307020703030302030603030d0f0902032404020904 83
    0x4000481c0705100c05481c1c4074240000c284c0c0d039030040e41540703440600480d0890201400d00750180401c543c015070704e4000c0303007040302c401783c90040903583c505409540b51180f460101e0068003686008900c6616000800030111030658121341001c0d1465220350400d03030143c004500149030040c2c00c00e004a80120fa000c0088070803018480c1900401100031a002c035190b02455000f249a4045611840e03604081e583c400e0350382c2c4102d10a80072200c1c0440c01e0b502e851800203220fa8002540a5000b800040c500301104502200521f2250f210003a100d88640c010320207180e051005c040015042001400d0014440c1c0c001440500c185220b00c2c10009141c0006042c1c0d0342d1054601e60800e0101c044500e00f110b006a072840189950040c444001714246800c88483c0000007128880c0d81f55070b010b8051141541d80880181d800682440c2e40345c0300c14000c61050700014461050302b0305412000103240700c0c40e0b205160512160b446044201c411400a90801204280311658802da04481c0201c0580d10b910b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 765036807 1250 765035557 765035561
    0x201110c0f0910080f010911010908101508150610050702090c09011b0308041a0f19241e0501020601060f050d050c03070311190c06020705160e06010804020d1401 71
    0x340c0842100c0c0f1405514261300c2c017040d07014034001401980c40743d0100b10958010346942e6028030031400c00364042c00340c11a224241e0780c09076080c0c2d44082d40100324590364a035a00d141c4a9020030030390801024038280400341c1380c00414101050340c0780c00c0c40b03400c140050700001c481410050492102100000d2a5515030b882400e580080b0340500d00407284e05105814001c2402c2c504503422542301c1c0203600e00c5205143c01a20191180e6208111403185035103070385018800b4006040c0c1d003202603032100c110489035080c0208620420035408200caa009140c4441451500e281c052800d504050680060055036408600a030546004c0d08020500c50580c1d042101c040c850803140c8022036103810180802c06804800440c010040c5a4051041d000e41b81c2c42e0384283d00c120340078100e085443d018003401035402402498981c1340500310042c203007005034030344504142c0040c103070340071020b4107130f00038400c020709a0305168100400780703003003441450281e0214006d840d1100001d000e0b004003051202004100b5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 765038057 1250 765036807 765036809
    0xd0509031002030c1e091e030a050f1b0409120c03050408030f0406030b09220503040320130b0306060111031b03030a1a060406051e03130201110c0f0910 67
    0x2150740b49082d5804d040d082c0c02100344514101d120101400590b2000310950790984801440c61808050700b031161b001d0900f41d6032009805010302d00b01d90300401c2e800d21100119846000c041c002d0740070000e5840c1c3c0c080c504841803030720542c41c040d000c0010400040c03c400404a20f4180740070221602d04090b00c00740103039400340006100000300050103481c9607000d042211656101401601204000c0190a90049424020003901c80b0b03820001d2115040040b14003034000c0080e03900c0c0c65102d03240d05200d40040000d1580c100f054980118060610300131607070110401d1241000f0094103040025241c00c0054160741c10815140b401c000000f00910858000100409001c3e24040000440740d031030782c00880f1030800140c40c155440b20411000030180541d02001001c0c03500d841c0c140300b0305503055000b030b0b000349c00c0c01c124002c3c00b03460502412009500610041c0124010044248001840301880201c140c015801a58000c00c0b00d48861100300902c22044400c44c400d95202810f848105410b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 765039307 1250 765038057 765038083
    0x120a1808060f0606040918060b090417090d02030609011d0307150f0e030a0e1509031c2a0b01141e030102091305040c0b0928051f0e0405090d050903 65
    0xd07045003c0f0a00900a42d4550010710440089c090340141104020f500d0b07508890150a4683d4004800e580003108001000540c04c000d189550032421500400e14141c0111007901041e9500d92100d0f801241c0308002a400e101078000861400c0e0780382d0743e04200eaa00300c0d603002c641291209102040b0090f02c1d00411100505a01225125043c2d4440103080b284142d01a42c0507250350300404000310170a0049030210800a0000c01d0602d040000050021000c3c0e030952040000009442d0320309803400c4a16240703200300c1c0804607101a50b501348425101c0040c1c3c851060f0b499280402405515180c00d00080402c0d0320040110891440010a029100f144030340b6911400c41d10103200018540d41c0842c0c081c500440710480380c0e030385407903900450744500b4628031382c041002c0c02a480c100c1d0518100711000141c08014002190303964000c1980040580e64115029070b0443c000d0211991150f0b00031001203044600744802e0401e07000e104d480c0c0100041030420007400040d07540654804000240c84400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 765040557 1250 765039307 765039311
    0x50411032a06161a01050f0a0506030429090d050406170604060f06050d0e011103040b09010e0111030403030e0a0209011503020903061006110303010f0e0403020f120a1808060f06060409 81
    0x1881c50044484c04880c0c1584444603103407400442c5500302042d90100161020705200e10301800d1508104442e0801807046503080c4000041c19069400d180b1258008590060000c1207402c0000c00705050544550209003041010301c4204180d41c2e00c010088906901c06030400d50f549c44801c042805441c880c0c001800400d0640400107546030b00c04010140c8450106c4200103100c3c80320f401038203980d21106000b05902c010310120300032544980341c0d550864010340c000102500411449820b65104403240c603802d8902104104c1815058010190b89d080d141c03024040c1c50b07440c0d40c00280e807103030706009880741c050113000c0e2148018081c0d81100e000c410b000b01220200d02d04652030f444098014003400f030015005d01c0808958135000015070381070301d001603448040d99041c031002d0102072000910680c02c5224403048019050800e1284411003034003145001d0392101400409042081c171061020902ea280500802031268042903441d0400490b810700c852940b01d04000848034041e9401c01c400140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 765041807 1250 765040557 765040597
    0x1804020d0c110c010201090c140a08120301030b0610020a061e090c0302150a09142701030209090318040c090e01090c02010f05010501120509010f02040801050411032a06 74
    0x90307080030701100c807200b0000c120341c040c81c02d0100490070703035148100c001e2240c0715900f000e10480d086185000310202c0040c2c441030f080b560740d9a04a140906c2ca200b0603440310700010061080c40707138070404158440402c0d11840315210b00e402c0002d55949102401402113642e1b55000f0000da000e161642e40003e130700d00010310801200d0305080c81c2c902000e06c0101d201e0300303141c600b22021286030002e40d40e0b4042c054a40340310a42c54680c420760031500601c2d03a2030340130074400d55022850b0305d00c40c00c040c003904201681e89003035810351050020196018059425941c402d004001c41c244d0003620020f55803c2c02c0e240815102029002990360f2950b40e00403814000c4000f0002c68111341e90b6205000c9581e25a0007848010795402c20f64049038020f01445002500303603142d0071852034454008542181c00d002c00080c820071785040040890300160846819651120240310510150b4420349403825000c401a001c41071840381d403902050242080b0242140359209180d200d0303603481040e104805044c20f0322094131 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 765043057 1250 765041807 765041831
    0x20f0a0f141314010806030a0305030912030f041203020c0703030318080a11010c081509100512100b0301050c0913062c0f070210020f040b040602070302180c1804020d 73
    0x550183d00815042e60b404040c039031001d41c821000d8071701a40b4040e0141010111584048542e40d0005010030000d104204030070300c2c001d40c00e0004602c6014091403103101400c040c03a00f540550000e40c1020300b00740c0103010381508101d0110b00e90003201e82c0340c240020340124920138001d10841d003c101500141d804a0310011258010b041c801800400300f00030000282122400d44000505a44440c5503081040d08180c075030810f0b02070180c0014209104480069941f4006101214030003400c083c25000031400903013055140c0640b00820380e08500903c042d00e001404503a0500652182c42d20440c540c408280c502032555100001402000f20b034844800031060b408511000084455501c8445840006116101c00303022a03014442d06e901408600d0324134003159010703410121940007034010400c400140b49062070001d00080c241a0040d10a591543c010032001110303500b003c1000200c0c2804000b0300d0880c41c0c0450700b201c00aa00c55107110409070340400d0080c05510080046185010084904 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 765044307 1250 765043057 765043087
    0x3090f0b10170a0f030e0303130803191409010f35060f1302031506120f090303041707030903080d05161713030e0a030305030a0f020f0a0f14 62
    0xe442103008001030b111821101c041c1e40d045090f20280401070214a0b940002e8494a840500c8041c001e0071a414540b000000d00c4d0744c030455500950940d800000d01c016401089140c006082165041500c0c406080000412403403242e90fa240e410040500340440360107009101c031001a01507101944070313501d42440d004800d50301c5251500e002d0a0740c0300005021340b4069101490340a400f910ba14208481000c000020350005401506004408171281e14a5200d0002901d0200c1e200c2c4610782c11803c200302c0d0310f01341e010b000e82145280e4004104010207c0c40701c03070305d414400c0084000c055540c6043c0c14101c3d14201a500004c000003c0042c1080d09030043d50003c034020110103c000c40f2a01403800203a81d898500d21807000304070000790000d450210360b01034000380c0c02c0c0a401c128400f0105840020061852608101c011440210070b012440b036061060011404a01804600c1d0051295890105024000c2003d0401801c040040c4085105a0b150241007034940d48590701d4130f0018038043c074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 765045557 1250 765044307 765044309
    0x15020106031a0103150203130b04020a0503031c0e07060207180204091a100f090e04061b26010f23120706030b06040b0307140913140601090f050103090f0b10 69
    0x40d10ba89120b010b128048461b1003260300808400029480c196940d0380d070346504580040c41a41d102842d81d4001465407001d100401a950044441032a120380c80e402e14070890f006209140103c1d84a0401444802e130001121001e4510546a00c2080030007071070400003030320a54006c0c841007070034403122036104100580e50740340c4080d044803244a07184011104480d000d988076034030000104081d0341088050380e131240c45a00309000e41d4001c030b108884010000c0f01c42142d144141c0010341041210748061408810039041d02a60082c1e5041c1949464441c8607142018000c0141002240f1103010148241002d1505200b07400f5200c0310440900b41006920740c0da540c42004042401e20808500b0382c584207003251b054078030750100141181c540d004100d5409100d0220039000c03000810001c4510303500d02c14a105e50249015002c204800c0d2070701e0178242c0910203000b0f01d040c840e1040003401074000d1122000c094401c20719000515054509101000c032841c10005014a040f203c01e2060701041e00d10000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 765046807 1250 765045557 765045563
    0x310e0105030d020f0d030c14040e1e0103020f1c020a0305010c090501052503170c210702060612031e0a02010612081602010e060c010608010509030c0715020106031a0103 74
    0x190712070a102d20241d869000034004070b81c49030042c01c00441e90074043e5000020249480c40c244c000c0985e5440c41c410294400d400c2000c3d1103a07003104000d03c06d0400c80c0303c09211141140c003450954034550224202032405803649106101c9820f0403c0c402000d480c100c20480d8004228104241e03803810301070b000b000155000400070740344107004143d80d40545c00303d62041c202c2242203500c0501142101c18904058141101040142407185070b42e4003030a60000e001c0c0c0000310100d0fa80c0c0c0030403404000d4002040d8094507988400c641003259040d00030070341da0391101d03060324080c107038a4103000b40500b14428100d00ca103040016070f1400105058041c050101c0c4440380e0020070142c1e884603028441e50703485850090454104204058034030042d20229080380e4810304103001703000c10b41e000255080c1c0180a0032240381e0340d1040f040003849801d0040941101c50303240994a422504d401c1d607600e039401c134041e10f940210800070411809200354414001543c12140d030450084001d10080c1d030743c440a220076 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 765048057 1250 765046807 765046813
    0xc0a0f020f040e0c09091e0304090c0903081e0f0d0203040c14060712030f02040e0a0606030501080c040e030f0403050d110633030304080a06110403020105310e010503 73
    0x20503850b041c01d1184600e01c40c190001015090020420000a00c50003031031114107008290040d0b1508511100926044e5000005103480b6410186440103d0310071034414400c1003125002000400c80c00070865020b80038110a8403600c1c24010003c0580d8440e010365820600400200024581d10ba07a0146d8022480340c0b400d0411185c2e110504049a00020070055100b0010018100054142c03a2910300c00281c07402c0204d00c00360403c810400700d03001039001c1c03c1410720300c2d0100041d45840e8030604001c0c0c000ca040410407541006900359072503003180200382c00b8694440031b100d480607041003520500e140c440c1115681e03507202d10389540c4541c0300d0750841c40412400b100302e10210401042082c801d1001c441d450190000f444800c0103d560340101c10029002880b0540c0c03240d840600c0200003414400c001071441c188645000d6045440200700b500c0002c00c03d02c41400142ea00c181120340c0c80040004003644045844014030313600442d9000c10601480003c0d0000d00700d648400c2c458101e503811070507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 765049307 1250 765048057 765048079
    0x91a10030b090c0c032a0d0809010b1207120f082b0504080a0c080d06140111150a05190c0c03110a020a1511010e0a021512070c02060c0a0f02 62
    0x180d0042070190001140c2190403d00545804809074141e58540a5540e4580154a41d440c0801c0341007440c0101107c1c0001c01c10020005018424000d840000d0710540b1061050741a000c1415169140c2c1c0c001c110000340c22440355810300c101c401410310b4003078009034841ea0720704580c614001249581d400c44d80b403000035900b0940c483c00562180501c40c82d00840d10f1441c0000280003241c070b03501848070494034030f001444000b504101d03078480d2201804c440f100c180c940702403e50000d0494013100740044030302e9100f034902000001c60310f00c9058118201400200b0581c072014890002070030001081c00f030051800200c042c825034060300800a19021703854544808210300d00c0140c5070b12a0310b101035008800c8907401c0161022590300307c00c000f03020749804c000c00680c407110a403d4503a107052190590348034403901802c1d03141c0b01140c0c5140500409041c1d02e00704032403da0700300c44500181000140480d40040700d081d03440b103404490300c82904005503141c0300f80c5458000d0428268a44c2680100420b0813 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 765050557 1250 765049307 765049321
    0x80a1106040b0304020420070b040302011a01120c0c0212030306040b06181003150e010e010503011e02090d0602040603050f0a05130f0609050d09060f020705060301091a10030b09 78
    0x2100c060307a01c0081e802e455541d40380c0902016140c6030b0300d41c0003036000c104625660503250b40080e0550611400c4100340c0380c105400c0003429a160042c0d1920442c444540141050780c010100195040307004001040d010f52070001919040d040e1702c0041e400c0702841072012040da80100080d403103400210340030005884144103001035801f0302000616010300340c0d200360300e16180c540d88451000e003e074940407496416200484c135000419500c0610803c64190050060151804030280988000d500812aa03550040c6440d9254011000c00c505980e002aa004031074070340c604022096a0494030555507240c0e00c1d540200100f00c103c0b0240400b02c94600030400110850090a00501041c425220b00040b66141c04030300c060560402c46029a03a150502c0001c0e81c03d2001c500048065168861a503207072030b4020780742140a249e8481150031401c401e103c1680d4441c141c0741510601d080000b0482240b549180f020700e1402c044a9005901030b00d050501d80e45600400d401642c2541c0c0309206440f025 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 765051807 1250 765050557 765050569
    0x60b040b07080c0a0c1401031808121b1206030c0307150f0302041e0e0f010f0b030403050715021305060f09270a0b0405070f02070302010f03060e01080a11 68
    0x4059680c050034100031410100c2d02030740c00380110700c0c807a1003a40c0e141c1c5103540d01c01e02500400ea00084a01e0b030440400c45440da00b501c200303643d56828010044540703180390707200351843c0b28080c21003003070895800203c0c144480a40204103440d4540b182c0d2955050100003990a40c101282e42520a110348012041d607810041641c0c000c44205410240c05080380180c159441501c15912408269090200103044448a42d540a070b007a48031903440305003400c21040a25140006009114418140340104143c0300029140d2046079406103280e6100d4581e450308464134410018007401e203004e00f000c40d00c1c00c428140c0c02010303a0903990b540e9a00b031555500a0140c0d900824650309002041071081d01e4843c10004000b005030010142c84a06505414421180c414001e8236a20384680d50ba60b14008141054441d0302e80090b04c0707092400e05d07043c80841c02561000d941c08028100f040070000070811902075049070b00500004a10110380c1d60f15180042d6a40c803668005685098510351200c103282010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 765053057 1250 765051807 765051809
    0x2060405150c150a061d1b0d020f0415090f06050d240e130b060907090e010b0304030e0a03150b0307050a060206040203151902090d020907030e070506030112111f09030303060b04 78
    0x540c072140d80d265030b48403c09451001161403c21a12002c00041903694142d100820b0b6001040e01c02e42d03115805c0cc940018004902c0310352405000380d0000510405401542103400c540d010700d01940d44541c02c541c01400703440d8030902d600040510300545100c15417036905010550394a07841c0006113540e201000009103118040280003030040c0c10209030542021a2400d51200c007a0030407440035541c4440741884a9401d9004040c207075400b0060104040d0302200700c204d400c0045410000d05070851b00d0700f00da0b02c05100c4031400303129900d03098600541c8044c41028001c0100825400f4000c4e55050040d440382011602203200e4001c18140104440307201c82080d000701030710031460519011400d68080254002c54841d580000b0740940e00c1c0050740c031603d00f42d2180070030fa600442da102c555941c40380f5150290300040d2203000103000510445080c0350000309000e80090f8a0752800e28004c0104100408130b8070080c10300b04110402e040d415400810490031281309903420003100390351304127914081c015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 765054307 1250 765053057 765053099
    0xc1808010209012c01080421050a020111040b0906030601030e03030106110111040323010e01060f05120114070c020a0504090f030906030509030a0309030509030f1b0303030402060405150c150a06 85
    0x10076400070704d40e540f1039000164032604c5183d0b4580401c800d80c0f014a11005140400b078001113001400090700f03982030180c080000d40a0050509090801000803e0360240e43c1e8140d001d00f02c0400051090303842604400c0000c820a81901d42d01d5841d200020504081910600505d60a1040006100d01381387c4c00c40341140d07044094440b5810001203095504c011400d0822469903c4505405010000b0b2164070003d05050b15242110303403a21080c45410310190400ca203445c2d14142e19a1850031001074075645c00b2400d80f60042c02c1441c41c1c40040c1c200900703a00115000b0307103041d0521003000040002401128040d4895420185d0703034140c102c090b076a04803040343e1036410900285401310301940103024203912a007005030801075403074017181ca04122880311034031035480480d08880031680f407801c1c1c010040080d00918954901a00440e204d40300f0743c07103075502940d01d05809002c05d00400381581c00d80c04141c03041d1001d40b070b030154000c7c400e0751055403070401880c9452000646458142c0b85410801c1c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 765055557 1250 765054307 765054377
    0xf05150310060f111b09060915090601090e0115030b090403021218090403081b09032d0d170a05090d08040309120c0807060e0607060c180801020901 65
    0x2c100714045450034039000035a814880c4000e18040141002d0090101040003074249542507400c40c41008050340f40908003900404e00d042c140304c01e00401a9030013507503210903a0040100d0705c40c0001250054039070360010300d0449a0100205000002a601c04903220322940c0601c5844210020854400c2003580d00801580c4a4001030030109000406481082c40310000d00f007824444070046009060200c0b030850000f4070303203400c2162a6551140e10340004200085290414403500042a0303546251a518140c14580c0043c1200310914000d02100d032021280c01c1d183c92003656407002d070002000500d0500c88040007070000320030404134802c007446001d4240c014046010840b10a0369500005482a4100b00114901144418600c480030f10041d10902c845009280340c004000d00701143c0f600280c04010040c0c2011130f141c0ea5200990b69440d40203c0c0c0015051248041942ca605890524000031814480c00041650040d03010b0609044282c840c00c44801c003551503840340456440000503085 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 765056807 1250 765055557 765055559
    0x303030f040204090f080307020115050319052803120b130213050307060f0206090a03080612030904050c0d0f0b0a230d0f120507030c060e01150f05150310 68
    0x98100d0812542060001d0000181c1c511603444240258801080949031342d1000400e21010301c5e424411124400e5448040d064007a08100000761114bc0c11010349410001c078a01c4a01401401d011500862000311440d03500e034421b42c4015110601800c0064000c07803a040c0da4401c60396142e0180f08103200c00109500c070940400c0140320002e4001403265010101b05c05000b06064500304580c8016000d5030700e03045001d03e0120ba00a00e010401411291030340c2280400303500081e04031688076006281125a0041c04072078030641880c500500992035031140c20402800401e044001c018000c44080744018050344131141045800e40381c406002640110683c0300c01c00030440300050120981c1540e0044c1c0765000522000039540c9402c0010640d03103841303001801010803420b054400600030003821724900309031860301c016100a210075005004151202e4104044207000e50001c544110a1070b01c0c0246240c03170b103000d0742d282c8440e070194502800c420480a541d09000300c0c1078a02c0b5040c2c00c0e180519203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 765058057 1250 765056807 765056821
    0x1409012703170408130b131409040807140d08100608060a09020d1e0609151a0a0e060705060919020d020d020319080702040b0108060102101505102309030303 69
    0xb040144140c85014061103594600c14013608841d004080c8903181a40b240380c1041d469284201da54410b03428503000c2441d0750380503141c0020b4981c1c003a4001885a4035149541070207190310a0020554241c1d0040b851903c0d10180c12500e0389004010341e040529140e81c81d10401c0d90390640c1a1440b07030340010703060010081c1e44070540041c40b0500d221070f0b022400741e4007450842c2160103018000028176480d641d05100d030381e04a10039030300d200c0d6a50030059551440c00e0703152070000203242c41580111030005110801e40d40104d10030a00b08030064410303555110941001d42d03c4d08800d445400041c00b0384e1418041100e5400030070244180c0042c02c0d0b2110382d01a90800000402d01d00c0100d80600a5200c81800e801d108440c440d0381e180500100d90b6a21003e00c104800c81e08506143d905110000e03040c88902d99001500000b43c18030b00c20700041c4a81020300404281c03880e540402c0e40310f00512030041200354004050300c7e0a40c01a0b900b2801e40008510350b030303401c2c00342c1c039a865050341c800c0c00001d2407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 765059307 1250 765058057 765058097
    0x903020d12200a02042a050705070b070501020702120f1e0c0d030f08090102030c0f03060409080c01060905060f030a1205130303030203013f02041409012703 69
    0x11941260501590760400310040080500c0502188542d5400000080d0158101400791a01a9128a02d10340382da4440e041104141c0340c03143c1904013000004a0010100071041004074003034030031045e00f20340b10101d0b4613083d4043e5012600c01c900916040e40340c80d0360a000001d031b140301002500c0142110034420341081144c9100003680c2c00440c82041d40700300280d180c05a04442c142c2c001d5591a40c4103912080107410910050400c88080e0710401c104030b440440d00c0c0544400903241e0084903a251942400074000c0e001d000c001a082000000e10400c84041c1503200e04110780840005001c580c4e07038001007011184010a10030f0f010342000d01841c00041e410761044500880904090b401d00c140c003000314040080540040b0086a400030052103141114058510250391701320481c103c800c0300801128140005055000015240c403140e1411076503603401221255101080e101164035008603175078080c100301140e1103a062030291207007e502464005540c0d4190b0551607009e0705006064400007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 765060557 1250 765059307 765059333
    0x506090310060611070f050a03110103090b0c090a0605090303070206031305061f09020c0a032f0d03050708070f08041e060506010e0102240c1e0a08070903020d 70
    0x503040c081c1e0107951800041c0e621880020782010742d40c0090f13002c6400d006a1520550b0303041050054079110b01000f4542e00c200e64041130b2540200c012815829900043e409486189401800c1040d000200400c01142c03802400c04c0e0318044880c410103030b0707a03500d0903126072240440c1c860705500100124005030138038200458100102010300020301c5505e85a460600750151100d80c1a0103068210501a034030f03003441c030b40141031460011842d056408022640c1e842104d00c0090a001501c1c000000b0402c1c80d40b40326424481d5130340c00d808660401138113603813650560b02c00c03040801d02e0b000115a0061051441510410381522a08050001c40c403040d2001a0024000ca51058081487c140c2034000c400302000014030a81300450f860900d003002410072403038120543c0c115800700c0d4186056603910580b5000c1800302444ca514503071140c005044052244081d0500010448468241c1e140f04d00e00051044907820760301c554030341c6c03505503003114200120310010758070907a040904004500c428540e80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 765061807 1250 765060557 765060559
    0x1206160917061305120f0d06060f0806010c030203090d080c010e01090f08070f060207150b0306062211131a090609041802040c0c0b010f0b0f0c010905010f05060f040c09050609 77
    0x20750350130805c405401c100e60291801c0010144c0115000d40040309500030003015208a04204101041c0032a0051101000800c800c0c10800ca201d00001494000d001300c458000000d84001c600e0055801c00d460142e0101700052099845c140c61020070240601c200e10006a100307404c0905c42078507450b0101030740c01942003034410280c0d0501f0712002803000e01c002c0003018401e20b400c5034143e40d4005500115200d4010b5580650444810017813643d8588207440c202c849407040d00c4080c5586400c0c200700420b00e00142421700100000d184c010075242c031a0b00e1086422034800090b95860786280140c081c040d440007680c000c0300900240b081481c00340c000c070b07903542401010041d25a44039000101681e5000d040354000c154405010814091268000c03405000c001440ba18500d14040d189070f498882d208a00c0c940c2c02007c41d91708142c88003900f11444150700040244440021490200020101500c03403d101e1040106103880351700b00750140500314019074881207503e0b172401d0107001c3c51707902c804441 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 765063057 1250 765061807 765061813
    0x1302030f0d1e170a1d06041718060309070e09070513020a030f0906020c0114190c02190b161106062403100e07110c0f1206160917061305 60
    0x83c2d49940c03c0000040d1040240c030341c0200d0404a04c03441803039590f18007240c20407143c220780d0401c0f000c6403001303d0340c0ea0041a508643c9584610030610701810001c60040310358043c000000b0300800800006030001694002107402125842e0307405030036540c2045205080c0c108a00e04025081c589160f400345c4800c40a0741408500d01c0341884820b0201c0e90004411951598041004c1127100b800341708500300c500b060084240542004400c3e41104181800300b680b4158480c0440d1502034420700c4002c0c910614442c8517000c05c841e61800300780074202140c220030010b2514000070007207440f50f0100e10540035002c002e000350391200c40500c445c0f420050000d001d080200460381c80580e1000340114411040c00c64810003860074492400000c00c0054258010802240540402194042036400014000710f41840601c1100360100d40721526000c0c648072030b0f0041c44200a592402c0340707407400500e08280c0c1c801641588504501c882c0440c0142c01d00340e0b41d400000000c919a03402645511070314050411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 765064307 1250 765063057 765063077
    0xc0309080f0109030e0406062a121d0105041203030b01110d0206010509060a0b04060c060915150b1c020306030a02060a120501050f09070c11091302030f0d1e 69
    0x1016240c00748060360545141e54612408003815071000001e200c0400440d400e1200524007400146080820780b82e2098000c502114020104020025148815400089400702c80e100f03640c0907203805074002c5101c03000b64049032110324540c8180700312801d07552503064036603182400340c03000c80003000d01c1d45100303051103040904c800740c20408000d0790344800000c0e801841958142001d102e265600580100e01586040303109010031024101594141e0b040c624080307801444904208000e01a00d1402130207644060a00c3c241002840d00300403601d0103c03900c0c0309100c2e0303074880782040d0511500d60300886411002040d6000d5042035002150800402004c4410040807500050b40312f80c0a41450004204061002c40c10080c013400303aa4010801140c0da011f400001d800400c02c001d030f0080102c001c215920001000300a030a20707191900810182c904034443c80e1a0324215142c580c2620244c2c4284500105030140110014000030000c0b000c5e942d05d07810888030480008108502c031195070520a02e000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 765065557 1250 765064307 765064319
    0x30c060c0c08030c130906060507080304110405040b060301230612030d0507082409010e060111120a1b0f08070f050609101803090b030c1b0f070806070c030c0309 71
    0xf070750180381c010000c0e65407038445e4072041c040304030780d940030000107810300b130040003e2500f00003541d0105400c200119603a40d20f0b441c042d1408000352a02d90352080c40e110602003400102a5a40d2107800164004c10040403508480d451540210040c007028142e600002110742c10314040c0301803a03035000750440341082046415034059440451300744000035807150070440c5010310703040c65600104245004180740e01c0d440000c5102117505001d0000130360490800b041c281d91180300703119aa141c1c0d500c10b55040404c05010702d125a4080c902020001d002c0311804000c04611001060703420354807444100d0f044ca16580c40326038540240741d0580e08850404985000700304280510381c460025600074259042d1148809401c503815204400254003054854500190f08055620181c1d401450380d03a440399105854403000740b00704810441c8601080e0f81d0139004200014400c500c400a071400c4c0c855013600d1f40b0000740c0e5800c0850751b0b0000120b400d44442c020070300400900c0f040e14005d00d0300801c041e407035007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 765066807 1250 765065557 765065573
    0x20a02040219030b220c1e020604050c1905040b030c190602100606080f09010b0d030810090e030409020a0216031118280615080a0b0d030c060c0c 64
    0x1000e4080500350021100c0c10751520412507814800c0b5034520383c0324900000c84e21104a00170400082c150340c0c2841c0509140a0300c10201e04514203400200100300f1107400a450302000d88003122148074500410b1a90f10f0181c3c2041c01c0e800c042031603500118a0401000007410040c140d442c1c260042d03680c180119110381d55010842e011000c410907015107000402454000b040d841c00010314500a01844800ea2202144e504828214901505500c1c7c80e2280b500500c00110b125070301411103500c1104054010360315910035480d01c900607110a030759610f180f090768001001c014440d08100024088004164044d2155162500c12600d007c01d00d0440344000c2e40690700140c0300c000841303220641a140400c0d5215600c811003191110310300348080b600e3320840c407500551660020460300c5072400802ca60000c0c00801410720386403500241044003400011098038820961070030140e070307040b0364140001940b0b80e595140e40e030180710000b40d46800d0b000345500c0031500100308142c481c20010811007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 765068057 1250 765066807 765066817
    0x240509030a0302070c0e01031b120f0b06120318040501090614060a050c030a210605030c0d0822051804170711100e04060e1b0f190207090c081b0a020a020402 69
    0x1a01e00180c134500b540140c010400b27250741c810740709001d91203035400002d140241d00610182d031001d40102e058480b4000120b0b210710000300c1001610001c103100b2010035080f601401c040c90184d03010030481e41c80ba40703000160f80640c0a00c01000c020484102800c1c00c000008043e144102d00c1c00e0b50802052034070450031940700a00e0700000640b201d8000300e584440101c003801700b60014004000d668684004079488484101c003c5100d41040031203003090048003000c840045200351241060124203141014404001d8003450b4003c00d200074022150400340c010765402140c00c80c07280303071381030800d01112260f0354054402141d51f0084041580080c0d04e0324403003401c2590940e101c02c0011207502040c40111405030780b00744842c1c0454028054496481e9419160304a02a00300ba542c480103081034007a0780c814040c0c80604a000b00042c941215808680310701528140035051102c0940f44a0498005805681c5c2c0c008240003070f04050704010902c0e008008020007801643d120502c10b4001a04a81103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 765069307 1250 765068057 765068063
    0x2409030309020406140d02040f0f054803040305120406050a11040b041701200909010b0f03160e130203060306090d140a030b060403240509030a0302070c0e0103 70
    0x1c40c880801145418003401015200a1040c00e200040e0600002d00340c104000000e4040c960f40c0308000006165600200e15092002200741301d2400d1186a10300d421100b00340c1c03440c1c2d030302812010005140707040c0c411341005024841c0742034480d540d400040d0403d90005d04110240710080212407a40780c88403824a02c074a01800c2e0029152400d1607401c07041c0c0d500c0700c0340440360310401c00050004090000031b813010355000c1002c1c19aa1962001a54010009400b01800740034854100c02e00d0303403c09070b000f0302004c0029640c03103201340d036500582c0d042802143c100c0050f50206100003030081c03c0341030403000048800e01d0206400d41d560300100b00b402000b400c5415046800004008131820301f007000941107402d4a0080c124100b507524020001c42869401c10106040000c0b0b02c000341d4820740011070109401000300d5a00d903564070b44401d5040083c2c1c00e0340c0d40c3c003a19215905462041c0c8c861a485405d01d10081c61414440800450081d480044222040c10003560003049140d006680b160203144 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 765070557 1250 765069307 765069311
    0x3c0b0111071a160b0f06240f0408061303021605100806130203090c03070506030105010c0b0a090c0b0a021b0a0504270804050a0e130b0408090d03030b01260424090303 73
    0x10171003000130240d100103040314080d203000d480000480b11880898600f8100c3d10f09515282d1100340e002010506c9150700c664854405c0d14180019071011010f1642c0082c032039000c9038103d072020350300000341100c140b150a600804d00481400e00320f009151541d40f16100801e00c03800000d40824000880c0c006503008445035101e007030100c1c06420200040d44c040c00382116018150b41c07600d00000c10303131140804024540c1c40d802001c610000d59903000002520740c84911024616150071911100d034002c01104801072140c8248001804114044001c0701c0001818090113a8100390a000103001488801003400c29444030900e41e9282080ca2038640920415409540d5445e0404020130103074181c010303003022003d10040c400da8800904241420a0f070100700403905603280d06025500740030f804882608100d4148a1008140d8541d00c9504c956500343ca42c007500c0088004c4051001007030222182c9810480310104022038014104204000c0282c4010110805503008803800c0d0b820171901140401c0e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 765071807 1250 765070557 765070561
    0xb1605070f033204060c05070f0b1309091a060d0203150105040509490c05070605120f0a0905100e010506040e030d3c0b0111071a160b 59
    0x410540e90461072860b00300c100f9000c000c041c0900c181031040344500000d005102030701004103c01845001d0040100e103c51402c241c0c1d5408103070720558441032030669419120480419803d9041c030030104c4290304201440000b90801c8080d20500b60003070041c5500016080c4564016501045100308220701000a000c0951400082c0302c1981c070007401c110090342001e80740c41c0100526070540801c040303580300c484284070f122107011001c0c0400506c04961141c240c0d40c3c0707500465000614086918410000c03210003a03500c00c1c0071251070140c6ca60301050052040d004c50341c1c046a0303441c0e01d6000b010710040040c0d07940d8940d44191600b02e404001c0180e4903140c841000b01900f00b07100d40783c1e00c0b0b48180c405100051642e12019242e10500080380555030752000300541c83d12003d0102080120b004001c40020341d000000e101c1040f4510070045001c604100344480c1e554403800d0400c407a8107100004000032420042c1195860245080022000d58180b2810450340c01c49503004802701d00906041c5214 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 765073057 1250 765071807 765071837
    0xb060d0e010f1a011b020a0911070212030c0705010e0a0b0408061807030b2e12051b0604030f03051e0a180302030d180f03060b100c0b1605070f03 64
    0x103598074059520000c00f03028141000790743c20400a10114111751041ca8505c4050f10025010f200c1c40d41169081d01e1900c0065040104541c0050503014000c891141130101107420340e554a10800180c3d14540d00702c41d6080043e94090101c2c000c00c01001800314120300c0d2121884600da0f08103a00074581c591198043c0509100000001240c99408002410b1440d045840e001810074014010351040f0010101c000200e4178010324981e0300090600720500c5d031560b14082400b1251606e5000d0ba058020300100341c0444a40380406140b0b403001a05c0641040c0c0745464404d4101642d001c00e90901c43e0400c00854165441c001c072008082039034a0107a210709844500920408040c1800011807000c6038003407002d6035002031142e840300c10a140c40e00c0c0381428404214620001c40c0d11201d21201d50708004010840550071050001006030303003c6e80e55003104102151000d00401004e4100c500307160110300f264122a800f8050410241816450082150303030f500d605002a8009070b0010b0070b51a07209004d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 765074307 1250 765073057 765073061
    0xa020718020306030a0f030e100e0a0b0909011a0c0d1d01021b04051b0712020105062e0c02060d0c020f0d08010e06030a02060d0b1f0e01030b060d0e010f 67
    0x5450300c569030450070361074074030080b0b680c2c0c80c0303540e002902040c0c204d5a401c0425109022104514002130b051115800034410003510700d02000c40d00c1c0e4880c0701051000710b0f02601d840c0c00c0d03641201d030007070000d079140c2d2a01080e601d001103408040d40508008015035a0074203020030504a101c030b290303507a0102c5800210341005800081c540151f046405c61000d8403580900c1c1c5901c4100143c0487c1c1c0050716407501d072840315584070200d2442d1007c1d00089650424450016203030702d040d002c0342d0000c3c42a980c4101c00c00c4040010070310a65800201607452003e07641440f603010f91044160b0601011441140e000a001604081c1441c0c1a883d20b46514403141a81800307548a01e0b401c91000308642d03000c000024080c200140100d03400c610704140061303a00e03902040b510300560340251002e42d56103130300785001c0040d046c2c1c4048940034040110f070b0503110034440b00520400708030703541d2110075010f6a40011001380031130720b03046540303d41c0902203103605113540d1182d40b500200180000800480741600081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 765075557 1250 765074307 765074339
    0xc0a02010c0c081c0605030d0201050a0b0306010303120e03161110030203070507020d08090909060a0c0504240c12020d02060f0402100c050a510906110a0207 69
    0x10810030b003010301c000081c2140065540894110f24146241c10020610100402c4071380d200036814881c0b00707620301030560194403441c000e0041d030800380010407403403051503038616081c40000c0014071700300080181c40286a02c00100540c00c00c094a10b41584902d2a9030101c0705903030240d8084281042e0b00b500342c5410f0075604d00d055002c0c241503043d86031507100980307540500b407400383c01110344c3e100850812801404035091260000c1020001c2d040031042c2e80d5680314200c0f24045450300d804c00e0500910b0055050710304840e21700445a003112280e169060b0f009042c0e024500510190070410400540d000017500150100380d8018225040d5400000b4640903002d8644154020007409010150720398002c0000074080300c0c1014440c141031403600301c0c5820910f440c05407a062626140d05400c059441104204528410f2a0112648d41d2002e84549641a004420b00e0102c0e1640d00c0d29032041c03903009145c1850050100181e40c2088150075000c0740d11941c98100140c11801084c0034502900111003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 765076807 1250 765075557 765075581
    0x30818030d0504061701180c0905090103080415020a08030c2109010f0c03200f0d020309010c080603010b0102060103171204080c060c0f27031c030f020c06180708060c0a0201 76
    0x4170580d490110150441110103a1401d02940c541104401c80c0d8003800d0300074020035000c1d10312000c82da500d0030181c42c55001405079603144d5030000d4180c1c1c10346200040325800b0307d070803220070303461501c0f0680050f61030f0f445400904104c0e100144488841d109070f0010034403c80002d00085140c9207400c1e0314070116441a805802410300d80090345c4140b5201001d808050a145c102403030303039100d5440000030103004a0142c3c05c121800041000741104064015600207000c50311850190b40320b820815007a9452440c915005074403810041001c0f850100c1d20420040c54a802107242061004503010102c0c81200c055811080004d80b83c00005c1081148039441450640040e082c0440100360b0402c51040c0e440e1102e440d0000c841880d03405c4c810720200c10014100030120360400c580c0144008000c021404030800bc24a85003681c2c0004e5890f0003110000c55038034020700800d41d102030f0303990001e0140c604601e00c1e601c0f83da0808035040d01d041004900521a640380603444044580f0002d003900c0c4442035107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 765078057 1250 765076807 765076847
    0x315190b061b070909150e032505060f071e05160b01170303071709010204050414070210020412030302071b0617060a1a0903010b04020d0903090b0702010504030818030d050406 77
    0x201c0484c0300f0207206c0901001c005404100c101070020110700d0b501661101d64072003100583c0008604c240c5183d840e040c24400c8098861039510101003480302c401c120703541004190044095406410305a030056000c3c00b96040041c28008120507860088058081c101c078590100c800601c000c002070114005071105c0140254170314903102074014104091010707400e03050404130b404115034000070f40540d0050700d0041e00402051918003859014400e095440d44054043c0020400ca12400c0d4009c07a010b856242c4803082c0030780755941c0d08070000d6110110a0341c1c200c0750441c4c88806107103000034010041801f66280a0307101c044c4210601c0050000d4042d41c4100c507040313010040740012001e15a8a1f11621505e192569150030100303001d40720085140e1390080c0f00046c525a900070755844641c07018000e40d6134460654803001503000714460b6100c06400303e6410300040000500c03920080600c40c22004119615000180c00300349840310146010f400b0031000305003846410f612401d042c907005010404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 765079307 1250 765078057 765078071
    0x90c0c070b131d0103030c0305030405010b181602010e03250b090c03070909150e160f150903110f0a1e030b13020108010612020f0f07110315190b061b0709 68
    0xc0130f40b105007c42c0004060040c04000613050000130b500000c0c061101800c0c1076803812032500c1030101c000c07048a100710380c0051481045842441441099214003d0800071460100b201601c01c0c040d8085604c030031016001251581c1c00600b51184440c017800ea4100100416407001c0101400e144c0950041c0600b2440c0c41c04204c007213030014540946103801e010000802070540b0710a0341c02d1207403d03850303501c2d09604c8440004080c02034055002c11500d882d18251020100743c40b00b00c941d1003452001030f1020540504880d454a401548099184402490340207220703544c862030a8140f03450702c80207441d108000410418407511101c1250b04c0040d14900c0f00c0070040c9940042d09001042c014181080301241c0840c002d1a07081e8100d03071580d00e030034082c0d944a030070150b41d84010743d200b000100d600e4880f04800c50641d0900050000984844070301c40e8a240d0703222401c0254140c0c0b40b440301000c1f1615449510242c2c0c031098010505603a25050006d240708000c045940f4001103603020780149454425 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 765080557 1250 765079307 765079313
    0xb0c0c0102043c1404021603020a110319060c0e03070603020a020c04060b0d05061306080c13020a0206152d0f03070b0913061e08060106030b090c0c070b131d0103 71
    0xc003060581d880081504c400c0c030f2104011a00900454052504111038403481400b0300d0340005e40802900c0c49001d113a01d903400500e0505890381900c8220811241801d04800c5c0040e50b00d0300045040013072450f00803041c941080c0001e140070f040d0781c04a40803036400135840780701d96810300140c15005404d90f02800402d14002010140380b18444100f85496038070f402007800396594000c440d00b106d030101c41c18041d9688807031019443d1000071030401c0c811070860094040550f50ba0098424030300280d0007a12169460800300320810300707002c41c100d911150700084084058005181d141c0401e034000d001360140c400071014410036014020030140321764044001040041c107034004564141d0740030303241155100d81e4151000058152074220041040403994540015889200b2480894003040100d5485036030703a0718103400b12184c00c005142c01c2030103080015005040c0ca40140542100b06007114900c9a48940503105034005094079002c94100400800104803980150300000314080c02e40f02c1903526580e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 765081807 1250 765080557 765080669
    0x100c261e07030903140a150c0206060409020a050d0c0b07060218030f03160219141c020a050f1305010b030105030d0e060a0c170a0314150109030b0c0c010204 69
    0x2100007410b264051703000100421082c482c80d070389142e00194403684550b10300b1681001d01090000c020051086c0e40014403503240034010f01c40503503000307843c4011007800d02041c80b2044650b580d0680325100742ca00009414991040242065806140016240c020010203040c1251031011018070035404850201d5030004080100c3d00a8611b0702c012848568083c13000c21000800300f46140ba00204c81e11001544e5814030b4600d051011088840c1203407120941c1c61728146002c0103401075000b0800c81c4007403060b42091581040c0103072000307091209417140040c032402650f20907007024615110100041000e81801c102e0a01e4040d41030925040c0c51074603401246150107294081000c1000440b000401d1110b00300c500728031040850101541e629800201070064030b0700400c4001968080000a8080c1070071042e8a0881c0e00143c1d69058618a113407030b1080f42c4807000d041e4080407170b003c00041c214000244000c1005045080c0c40d40302e00412800c90a60900b4400e082c5480c0d8206c0509a0300110700c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 765083057 1250 765081807 765081809
    0xc1d041a07020708010e060f07050324040e060702010b0909011e0203100e09070f0e06010e120f07080f15090a03030905070509040b04061505100c261e070309 69
    0x503440c9402103699240c8101c2c03604102d42d018884039441c2a640c50000003012480718419404041601d001da1503808049840d4801100c1c08910810b10603c8441d008652202905102d00014400318070081c0d070040b00c40c20490103643c0c00015070355511490085003420481d50340d210721240005c0004020080d010f0380902c0c1d2080320080000d5000002910510315070220001500010701c004145140c50412295140010700641d904401842c0c00000c405042010091055074180d40b00030400319580141324401c1e10203000409240284d9041d035141402c1000510002c0090200800d80e003106601024244120910201d0441c1c00344401c01c4800c000c001510340e080fa41c0743c07600040c42803290400b2414019507400c125803003110002070105106009a16a0169009810400002c98400d8924034001040d21429800605c0c200a140310140a19000d085081c084c0d05210000071203041000340508090b00d012a0950000c145d80c4010b140381c0c8901c103c00c1c180300c1007603440d000f0251405095070303c10f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 765084307 1250 765083057 765083093
    0x108061e0c07052a040c1704060b03010c03020a0e04151511070605180d0b0109090812010b13060e210f0d05090315150d030212070c1d04 60
    0x140802089040c000c0030219407205400100b40e42000c03071003500f14584d003500400407690030550f00a00c0c0000345071601c211402d03a10a03881e10b403400184560380114201005000f80c4005503a00c0740d90140c1d071000e01840c1b040c40900ea500603500d40300254041c0c901041038107118002d270b181c4003007402a204c480c4400c1302650200c0c03406e011a001c201008a601c10050415041140505800082c4c0d003038000c0060030000709074810307440340d8041c002c062102c0503238810710150085c80c4810040009010b81d44c02240c01c02e0068040d14940140b81800740d0303020b074007a405520390f9200051a0002100540000e4020302400d280c0907500c6501d000000c1e112801901c3c038210112698814101c11075001c00c0001e8540782150103032400754401049c0a03010750840749189019006020710015854100b011003442144280c4888501d44001c0042c000b610749884801c409520846403a020362401003070191852600c01c020030400c1c0d500381221498070f00b0704254200740c07010592080c800000c0f081001440e00c121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 765085557 1250 765084307 765084361
    0xc050c070e0a2a23040f1401020f2524080105030a1113060e0403090302030d0e0105040b0f07080301030f0204060e160c0204202a0d0f0e040513050105010806 69
    0x54a031100031044500b100c130555441400140060018585007440003100e0703031440010f82010f00303100103a803142d10180341010b06070400304014205024141000007805035401d880d1760303190b40711000d600001d5580d0b0300415003541c0d42c003411204c03554081c40960240000390007401250100750745500e404126940540e100380119507220407091141d80c0180e0041596640450030b41c1000e0070040c05555a90100b41d000f03006201c200c0010902819100c02c40403810f030744541c0b80c1490b12080c1d01c201d400c903079007403490032400300002408190180c010354041c5000e0005c071989540244100012282c590f446841d04400784010003107280d480c81001108502e40d420600c815074260f2000030010141002c8180002e2038810505940c8030300c040140210f0302946024030180b264596071020351a2010f102d01c90154069564a81c1c154403490740003480114a0030140c0340381c1400800281555401c40c3d280107900082030751202406400d014082c0148414000350019051140c9604d105155900e14000400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 765086807 1250 765085557 765085577
    0x30c03120f06030b09011104082d0708062d13052a040608070e0103080d060b19120c0806100c140309031204180c050c070e0a2a 56
    0x1504a41020700010301c0c5810802089860703160035032143c03c2c1684d042820350302e003000302d401140c90f40c001c07030b015140214001c1074035811903606850070300041440104600002d440512503001c080142da0f000e4610350b0060b00d07043c80c0c40542c0400e04a0014500c0885140641c1c440800380d103004604c0e604140d2540e505c1c1d0415855003002c0349031036400140300420303c0f02c0d40311240b1071a0f205c45845240500440d07090041690b5900c5881e070b80c0d00c031406448202c0030444010400a01e8890040400c00a81c00c0c020580c640e840c1040172180e046090850480a001416030009a074080c0d00b07458004280e541c02c109000e400300e0b0003001d02e2802820755008411580e580c0c10760341d01942d031040d07030030b507114481041c40e501c03000c82241c90341c00c04165a406403080c004160091103c410550f0240c46000c42005400c0210508200c00307041a0705040c001d00004104000400c0b200303000320000741c82c0804140017030b4204640d002080b07650850030a00b140000d03a001007401c4140701c0d030700b451140a601c0d101da521 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 765088057 1250 765086807 765086837
    0x108071d0603062206090e0c131805011104050a09021303060e03040305161509030807030513031e14070302031207081605060103060b060f0a11160608150a03030c03 72
    0x880c1201001450304e00c0102001c0d441ca81c1e85402510036100c120205108400d00c8400c1103907104108140303a503102c0004180241203c0c1d4540c4501c404030f0a1180c01202981e10f41c403100e0840c1c0c0228a07080e0f081000007030510860038001048001007804445c2185032141c0d4402541c004041c50000401030ba480f480301c0c54000d038080003a80c0241d17400070142c84440d24401d01400403201c280c8203000300d2900003da044c036024001c1c83e640084039000484c40340381191550b400c0700c1640c48030034440c41c2d4014010340403010a0120354042e902000c841d201044041d0b550902581c0000c000d540c1c0c603151f520642c0b007400161400f0403400e2103080c1d040c00c480c0e121451407821010305d00461892920174600e62418005114000907494100c074050b1038204848400142400202d21030035108a40b460010803240b50510f1141c900a200d44001c1c1c425511050b5903070700100c1a82d604e1b40d108400180e002c1d4103010a004d4503110310001c041c0c0032119004036510350754015107181c100080203014008019182010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 765089307 1250 765088057 765088069
    0x90618070c0c0b0408010504060f02090102060a0213090e010903082d1801052712180d05060901090506061002120a020f0d030e010506042009040f18020108071d060306 73
    0x30300354070480c03e520399440e01d5243e80203080c11507003075030310506210314820814514401c86400b8081a4040c0407243c3c2c42201c1100607602018503580c1d40782d50b4400004401c01d1034800c4040d0300d8140400420340c03030071a040c000c003048805081c1c103107410038080040f040310300d0902d02c41c002c54000040070f490300c0d0740c0c0c5901d003041d50203086c8004d46c82c0e500b000104100300144030009803800e00f541080161840000309030320368607504081e680036507100400c4410000c1840e10500000003800400da9080c1202590700c42e81020002c0d20b00e0445030391204400d00410105025641d4414130540e91003200c8001420003d5039951800f04a82c680c0400040c0843c000d17200b48806600b003544081182e4205d114000c00800620180c0c0084005520f0200483c282d80380034080c04185202c0192010b1101c0550b82c9842d03d2940081c4c0000d50080d0390700c02e529881d6410380210881c0403a961401c103504801400090040341000386003204004035010118601e440b44144c840080c582650b1054680d03944e407000ca89 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 765090557 1250 765089307 765089309
    0x60a0b03073c020d0801060c080d020d1a2704030e15120a0c030b0f01180906080c01080105010c08030f070e0d210509010806060315100509090618070c0c 67
    0xc8000000454488802031031060a4070140c0b80d82d0072a2060301c8104411140d06100307028050016000b550a50b01103804400035040d03c0b44070020045c0b42c8003c10701c0d82ca0449072a042d1071000c400102c07031700b44c1d1180f0303040400e44020341f0f01032170700d024140d941d40c2000d46070b60006000800b8084d088501c190141c50350102207501c41a030000c160b07a900b110b81f04000040500f2a2a8014035040098542c501c3c0c1c4203000f041000b1101405400e20f0800040c01914030240c40190046a02000e0800181100b000d01030742c0001c05188000e0600d07089514001841c0c07100580006050140102d11080003070f820b68100d9a0122154200001a880b500310480304410720012840d4415a8201480701b44010000802d10442c1c0e82a607643c00219010300c265824000d800465010550700400500c1c182002070040d40e10951620743c1c1c0411a01e24400282031810360300c602c1b0009400401d2200349401d080304229001300d002c0300c030342c03004003000c0b0b41781039080e400207040d030b0104200d0502e21001c200c10701000c08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 765091807 1250 765090557 765090617
    0x509130e0a0c0914010918030f0203090a0306091b030b0f06060904020c010227061c0209060c030703080109090c0312020f100e1501152105040317060a0b0307 69
    0x507000742e9a4008642c013806580514026103040c070400019081d01c1440341140d0322203118000001181107807170030b0f15159000c560083c15800704000b89611982ca04502101842c41800006500001800c000614464400100600c9140300d6018000306d05a044002d03407084181905240c01d030340f070740d0202d0f409014162055402c1400030400304007848041d0041c20010172044801220b01824104007003d400071000b8094203c0c80400c01c078520148000f042000700800c90402510b0038074610f011807032a038080102d04804e60000306400d41090362004a040c010300c220304c824096081c2d19194070081041c140b2004224021485003072240600900c43c541c0ba407180344040d54140c4400b4903000c0040c024001b800c09050040c03621121200300c0320190581a60030a54900c10800d107001015182510150100780094455000129414001c1d00402d445284603665040c540c1407a00600505034001800c460320400d0f405400740300e060b404030141c030380c41a5a13103085a01100103003400b808002401e0208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 765093057 1250 765091807 765091823
    0x3061a09130e0a290f1f0305070e1b0703050a30060609050111030405101e050915070b04020402250c06020f060f04030804171303120509130e0a 63
    0x26014002c0c014848420035000d4115444e0a150201e07407051407100c22996034020300781e400d01150291209000328965014002085d80f1019181d854080c41c00c003041d4018003590024408004000b1000c1860503960030416440600f0040241d5002e011400b882c03034200100f0031030101005500229400d080e46101c8144859800104040d0485014029600030603021801c00540003500d54401e030031801200301c0d03110180d810641003000304031010031903a0585c0c0400080a0350301c65416001168a2013030304094851690310130600702484848401c400005844407418000000464400f480041c0c2c4283d0403500184c0d200121447da5401e80d8201403c0b02a4a2810316850204135880d10b0800075100c0c59021265101c851090307082c0d82e0f00d001c54941040110780e00200300064060740c0600d03009032048800c2d000d4410008044042c94021640700064002a41d03410000e100e222605508183c540345840d0b440e0031a4800401d003654080482c524003141d82d902d5501549000303104001c2c944c2d03800014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 765094307 1250 765093057 765093073
    0x181802090405090a020a1a031501090b030a051e0402010203070b0612011505030c04020304080403060c050d0c020d0906050307020c120a05010504032d09030b04210c0303061a09130e 79
    0x1a030360b964513070036004a000b2110581c1c08a01501506800c010b000c1c203590413146596a0100c800710240040800709051001c0da150102c0c065020b030001c1c6214103480c940c0003819141140c50607411224803420203507040340040901025076408404c9132002030301b07e03408a000d900d803103003c2110200484181c2600c2c0d460842e0341080090740c0c2328003a040391001c5040b9440c03c1e0710703141040304078807090b03030000d00c2190200f0003007000401e16000f502e84403c4c03030b052046c24440c060408205641d4614426030058008003d145a02034010050030b01906280c54810f046107810180655904e0030b10750003030301c624111142c18000881c10401801d460750300800900582c245490044c004000d402590400400103c1d80c462032400b100407a0609040c8507130300ca500040c42c0d070307c0b468400400503000356285410805d029028120300e4a41071881350b8540d8030171344c54112a04009046910940100383c0c1c00752582004543d041292040d1490702808840484030500c44240c040c3c0180448142a03206009042c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 765095557 1250 765094307 765094321
    0x918060602060f06030a031803060609050702011d100b03070b070309080f1b06030c0d05040803090f060103120806120708060105040f1b050906072f01181802090405 72
    0x41110156002c403181a21003000380c0042220031102c0c581c055200000480c0800e10881c1d110003400405900c6050701b54480d01c1e15000d442041c1c00c04240b050300c035014010030301c0d4244140080000034090106011240d52042074450040ca4114624103880c0e5507100c1d62603800f4440305004125040c1c0c1d4698803c25407030046c010b0481c6c5c0c89150440d028035004d009442201050080c082c0b191b21807403400d400c54034400c0242580001d02220746902d018000d00d02e4a10451144900940c0180445034403480c001d60814078003100704891301d0040e0405401000000c1d11200c80d403c21906905003500c203692100085210004c0395040b16059104508002403c5440802c2280c10b83e4010354003804501c10a0b0608002e0382c070405907220300e81e54a1504180c07600d101d00301820700c1950080004d881e0254a44500040c080c4050300d004501c0300d01150000e0018104002101000d02030074030543c40301102d44003408801781482134100c0c0d405071004610006000394115100c258000b88100300904040c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 765096807 1250 765095557 765095561
    0xb0408010c170f150604080f0601060201060b190f0507081c050604020702090a020a050c070306051005010926010e070b1c0c02150402040902092502010506100e04020d021c061d160918 80
    0x7100cbc040140d480c201011594035140f000319601180380780d401c41c0b00c640036920211414600c4c000c4000400005015a5000801c0ca00043c43c628010715000a07501c1c0c4a0504002110006030090340b0507481000911b0050320344118096000040700c10040e2982c0004100343c42a204401000300c4500905101008000c940e038410f034040c0d1031b1070103009034080e140c01c019154010175018171840c040441d0080f00344580e2036445019140351075000407070b40c01032000388189017802a4202c010f000001142e1520072011113506c00c03204d5181c406d0240702034021003002039190740780680401e170340000b01e03400507040d51555044510900d501400c1c0302e036245485400c0210031421480e108c2289096884040c6c01c4520502900340a01d9000302143c4d000b8400760419651408408160740e0041d800f0300c12a0005036544c4040d151105c6861280000b030107010300840e0840d0701c142c000d64103c04001c00401519805264041d900440687c1c180c10600200301e0242c03045805540618000d80d40346246048001c056 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 765098057 1250 765096807 765096809
    0x5011a070f1b03030e15041403070b0c031b0106051f0302040b0d05070e01020a050c010e040608060114180106140c0c041d190503030705130b0408010c170f150604080f0601 75
    0x30b90f03c10217001031640400c24940e1400020051500091005000c100c404010360495404014200c4401c20f03614006602d454000803181e203040d0b0804940c840c41291550b922001444004001304030180c1400d0005004608654641c2d07a02180c1044002c07645001e641150060031035441407a0f110400c00300201c0140100320741040000f0b84501196070a54000200b0a610170703440700141840c82c1b10400110703000c200f61408140d02c16240c080006001c08107111550103409032103001c0c0044550842440062810103010200c0c900c22100104442c99101320000764910184030400d941c0c400c005140d601e4041d40c000c112b035005242402d00600700c9040300d40b50001550401c1074505110000401035000d220402000d0030a03001000007503c01481031000b4090415819840c00b60ba9441d030407035569640041d080070440360f41d61460000c00540020301064104000711100d499441c2c815a40701500c007014186800071a24201a080c2c1c03541e800050368090913603001202c11001c1c03d041d005940c2c4100f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 765099307 1250 765098057 765098063
    0x70902130f0501030e0a140a02130b011e05040b03040c181406060c0a0b06031c1710150309030221130b04030b310b04050106050405011a070f1b03 64
    0x316107001419500034040c52420b0708800e0054403014100c1d40702d45131420602808410a4080c1f108514016580c10304070b5401d50312030f840000707180b4040b1000584800e00c1c030b42c0c04140d014440090b007502142d108c002ca80075111281c3c3e00030340300c1d02c403032510300807118280c1c0007200344c403140300001c1400c00f4080d4880003441340d0103815161035455540038055507214110050215030003004002000c1110002c0050b041500a42207074440480007040300c11000c94600381d500014034204802c3c071900d0300403812907040292480030705d840a1400701030602e80d000d4011074809042d101c81040c000c2c54000d000010700c3c00404d0680e08011160712003000000d90003015036404203251031002241d0b00c4c0d9250b0941c1d087e25445011002c164641140c101109031401507005400320700b107841403001060202180740214400c0d941c401183c00d00d07250081c25a00103812540c01680b0307280c010054903407107410f058100008034070400d0b40c0708100c0c1001d919400713504a02401d411321254020410000d9285054201e0340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 765100557 1250 765099307 765099329
    0x3090c041a0604050d0c030b2a180108040609120507030210020301050d031202090d06020d0b090907180f0c050415030903080610030209030d0e120c0303070b060307090213 75
    0x1010038007a5254041603016190032030b0080c401444941405518280180c0c0210801004582d9a54a21107079410844801e0207402d110a01203842202c8641c00c6081c1240e14200755080440c1c600c4180c046190000d0040d04210340280400c01303004d00c40d4880d4401d24bc03c15181d01544204160290035a40000c2c011030043c82140c401c3d910b00045403080da81078034002400e0718000c036095181201c16414046600944550802003e0301c2c0d650f40b00031040c1314602c14000541c40301003000c20102103c4540c40b84a0045207420200091035901003034100c15921284040300401070b0014140b0010540c400d40c4200c8245400d10310031106030400d0245c012248081d4411a00440f1004d0803010b4400d4004000d01041844002c0b40c0140351001c0c480160b60418076006092454100000e440c0105c103043c50004501806d40013203560501ca42040700c00343e00c103c01480021a0036001ca69641314101e40a81010310320f5003c01c005075400d000c1d150041a400700155114040c1c01503c01c192100340c410426001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 765101807 1250 765100557 765100571
    0xd02043b070812070804080d080a050604050601090e0a0605041d0f0d021216050105040309050a12030e0f010311070b010801270f080d1508240103030e011403090c04 72
    0x15200240d04801c2e1a107000c007a1829141810441c841d0f504105012610031000740004030721501d041002030b201c11a690303250f241038181030300300408994000e098503002d1030801c0108526660030219810446030f081120b240c0640d1480c100c0d4008040c070342c0003254081d041c68144500311350480a02c9461008250942e40c5940882c00401d981e00c09540460b000358105210a0100c601003101070f0030342405514481158440a5a8140c21150300b103804030302142901400340104e052441c0c44001824007566000c500f08030700d403005030032200c007000201c0c400c1e9074038003405405074407035000042c00c18806a20140c4800a42c0340001554038240079601c000e6103008032000c0501502e00315100d410b00c5943e190400c017903142d280c0d10102005200d003030310200e00c1085800124400c2c5d2048101c0c03195842020302d5510704112001d0304101c20705609000c1c180443c503801c41700c0c00c84060340c9411a641340c207181a8942c013440040e00c0305c0500727140a0044000101c10030100c9000494811a03220003107030200801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 765103057 1250 765101807 765101921
    0x30c01020a0c03110604031205070c06140d05060612040b0702010b0d030804030f020c131d0615061b062d090601090c0311070606061b020f0d0204 64
    0x340700c00200107000201401010000b040e00c00e400300c02c103100c000d07060074601910b0340c8981301c4144505820710001400003480c00c003400300380071001c40501518500340b030a249080070955101c2c06650311640302181c0d52004500950b603048101d07200a100e1a0216021b40341c242081c0030050411102040554200440900107142000c2074003480c0741c2c541c0350450640c076182c07821100d01c0c40e049420b006510030461465082d03942d1031040c40703030845c5010020604603480c0e01c80c040459400c0d803a60f4003030751011040c00b4003c030302101003210f07102003542d040383c6032404850f00710844405a4042040c0d03003c2c1200344100284130000c008196400d20342c202d24130a041c0c8012801203882104c0c034041982040700180010303440e50b040b28000d1134880c90045801c2d002d070f0040d00442d9100300c0003150302d190f5681d4100801908100c809251450720150700c0f40170005900852105002c244086120b22050358540045503102d40c231000d0b1141d00d070200c0c0085039520218041d00f048092100754942ca0388003070003041d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 765104307 1250 765103057 765103063
    0x8030405010906050d0f1b120501051c0c030b0703020702042d0f091e21050d021e0c0d1b080409200d0f18030203070f110409050a02030c0102 62
    0x11180d0603541e886210f840c00c08200d07a5074102d001d040c41d42a480c0c20321050800740d070303008101990141d40740542d0965950400074244e079000542c029003140c18440100b05503a110340c4800040140c0505420204600d490030000d10760a43c0c0000709101107180a01c400151315034087d1030094401e982c104001d240c02108054010040918000300d0040700e4069035038181c071a009070800f542c5910000c1683c0030243d452110701110a0500c0129412408240d01802125201003020006c2002c280740000c1d40e004000f0310600c60041c00e001d081e0340000305005045466000d000c902c0302100040e036203e080140c81142c8a6040c0040100000c5d00803a0b088440f40c0c140c0440d40380c803544405524a814a4284400c0252030024809003a40d0b484001c0f5071440c0c03508000134001149002e00c0018100250b40000003258050a01149010f00748165403002940001c1150401d070381190500700803c4c80391500980000c0d440e0050ba40141c00d088018082081c00a071480c0c41a2003101a5600080c41c00c0049a0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 765105557 1250 765104307 765104309
    0x1c02060c0723311b0804020f0109030503040902130f090c0809010b0a05040e0c0603090f0607050a0c08031003081b1905060f1504090c03051905060a0e0f01050903030f01080304 77
    0x160f1082c182c5400c507540e078055099030b0750300340c0c0040002c5000000c18816100e0b60031000000c8000c14442c0d0200021460300030040e0030405400d0901c50225821030b1034603a41c0c2d0055000300c0e116030303500140f5080100c0c1d090304407100601403240760305e2283e83c03111103900c05410b694600368081b8000c8000310f9841c0384103001c0c600f42001c1c040c007042c440c0c61919041002030320903054140503070302170340224204503100c2c200118482c94249000f00300c001d141804540c58020b000313084908000c1d090045c5e0348402c1d40b100d8050307519a0000c1000e5140c0c0c668000c0800e03520074540c8003d20701c00002404c00e0084400c0721000c2c02c0c80440c50152160f41200ca80f201d29101d0b400d8038001c010781c1108000800503076500c00c865401070020b400949211003820045811110303804426514004014401c00c1040320421260000c0ca404401c90030109249640d0140d85800140001c1403071501e030341d070420114400304410114442c2600003842542080c12080361258070585504012011140012a0340c2c0000407c41d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 765106807 1250 765105557 765105589
    0x120c0e0303090f0411180312030c0d0e150124020c0307151704050703061d15060f190e22020907052205120c1c02060c0723 54
    0x54900b41d4084104a0f40045214480764410780d40c0d0002c02510640102034060850b1041440100b6101c030341c2007500d0001100001300e00e001c1d08008115008542906461541103200f5000c1640c144041d030107800c0c0124a503400c018003110600000f84038034441460141885002d100320004c196100040741c952440359031080e0964040385c800c0254041c0b41410f10045d0b0700501e4482043c040b03c421007405030030b0541f001e80b11540f20240500038044140b00c0d00303010040c9442614200044841300907124060319050320381e404810400140030f511224020702c02010000c040072486408141d60400141250280c0c00b1601b0380d03400000c0c2c642001d00c41103003043c0714035050682c0c2843c03079030700304007000c0c000800c43d00401405101c1d441e122214840301e440f015403903052160f0030906000600c10349262200502034954003030600c50304203803a44105030500c101c6200002e0004100c6c0d0010a1142c400c0d00c03000d028500c1800c030000b8840b90f400c1540412849101d07410003800c03880904100060032101d20391 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 765107913 1106 765106807 765106813
    0x9011232060f0f04020906040f09030302030f070905061c231e060f2106130b060904120c0302010b0909160b07050c060703090e0106120c0e03 62
    0x507031002252900c08043d140081102d00d40480240c40030740102c00c840d020440545840d044140d02820030303001880500010319005000b03510440f035504c0384030b100e1000704403941d110703049140c12158028406401d103a85440d01c14003285812503045178203036070740f403910700b000c00ca03250a48420000210308040358a4205e6920b862940c61048440703950700154108001a0b403070002350140c004040e81c581ca00c1d03410340001410b0820140c0359042052042034100315014103c01040004030388140210700c00c5484107418401c100b501130364010040407044500b5181d240c8540e0403841305a009100204441c00c603000031507c1d00034150765103241794104441c443e840c103108001c1a00100414054607140c82c00c2d0b904d07516203e66032046e030184201000201c07041418440c1c2d00d2000a0054409040034559403000d002e0295080b0741050302041d800c0181200041d400f03900d00041480014000d = true := by decide +kernel

theorem cover : BRFrame.Cov 764928057 765107913 := by
  have h0 := BRFrame.cov_init 764928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 764928057 ≤ n) (h2 : n < 765107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
