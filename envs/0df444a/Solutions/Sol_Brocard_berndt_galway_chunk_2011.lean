-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2011
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:26:55.94902+00:00
-- url     : https://prove2.me/submissions/23f55ffb-c0be-4703-9486-1d63368d048a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 361510791 ≤ n < 361690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 361512041 1250 361510791 361510829
    0xd1103010b0702040e07061205040206070f0b0415060b030a0e0102120411030c0f06070b040c0519090c0509011b020f040203160e010f050409051005060f0307020606010201090f02010e0409020a0906 86
    0x440c1080849030141c0780c8d14402421029080300401c0c0c010400c0368420302c144031034004602c0000c0750000c2c940c402d6600505a0400d4104010040c04620703040300c0d02400d00c1c000b84060034488003600d40044006801068200181481c0c0f800390203404200d9038072403d048100024042000c4081c401d0f0b89040d400d45010f01007900c24070101c0031401c0c05964206000300a4070300041d50f01081164410b01480b025100c0c80d850f84002590501d2490b140c9800200445040c0200c002d00e2044000754070003810541d01d4210600006010700100c9a200d6844500e031030007400554484117140c800c0b2080c0100115642c0c600380e8040c00f2070b900d10f8041f240000e51071f6003104041c0d50084c103001e4100c0740b080c0c03500d9080c6803801400d0001342c40c0c0140640003034a51104001910344a00c006440820481c407811920b914000ca002450240d005102030304580c14400200045281000405113947e0280b17000748151121102180240c00f0400c8000d4001e8078800c00001c201025500c540705032a8280e170214120900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 361513291 1250 361512041 361512043
    0x80a050711061314030a02030d0f084f080705100c1e050c01050915150d12050c0d080105040b01030e03090f1504080d090605031006050d1103010b0702040e 68
    0x14000303103c00c82508001040c0600d00220a00c0900f110000b400c4a079140b042e540440c0c1840c0340e190411010031125030468681c40e4100301c580c0d0340110040c15041c10103d0050401010080100c1c0c038143e0f0b40000c200150002982000300301c86207c5c2b000e420321085c2058a00300c0503a6200003425181401001d01c480150621400360000000d61550b031403048028074443d032130403816005105424400304020780600c0032400e007d028410b040c954060802c50681050720300c001d1600414100500f080074211035240d6641482c10785096402169402980f0401c1100751454815501c1c400081c0c404c0c400504500c13503002411505a40d4261404d0000182041c01502601c6a664040001d600b00703000c8040c441c2040750074551101d40c01040144004080d01008900d907100b900b000c8143d802c001c01c103207616904000b900c80203100b1468014a14904080303503110b454442e0258600f0000001054034181c4030640003c3d40125015150035600d5940e405845044c1e03201000c22802541016030040f94030340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 361514541 1250 361513291 361513297
    0x321131d060f030a1502070b010501020706120c0e09040c03060b0102010c1d0103060b030406020406030c05210402240910180b2b020a0345080a05071106 67
    0x100405140319240c494008201154100ca0345260701481030368003035000320304401c900b9a0309202d510401030b03aa40950901403105a016041103043d903000c000d080112907802800803846030b00034400000e10b01c00c00c04003258112800c8503e142d0141e1090284400c0c050015110021a0700c00c103c00c0000080d130784016402c1c0e54040302d00102103007038102c00c08a440300303542540d031580205160004e4131640301c1c8103111054000765400d54449502003000e0080765050321031511005240e0801d01d0510138a0310700c0540f81e07103010a09581148400c4081811500c5101e03050003240001c5e01e0003180303d4030150200a641d0090994248561020400082000c0c0110108044401d04904e50031020f400c0c426060110b6020308840400c10b122880070b02d464100403500786c084060003000140c1c0da808503c0c1c004007915000784030300101da400407a01481a40c014a062100e40c0c403a00700160081942d450301e0128008807400292600350000340c1e448440e6448070050248a00c00d44169000e0030000d0103001d90340c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 361515791 1250 361514541 361514579
    0x52209020909010e1605030912030106170f10050f0d080a260402061215040207030f18050913032007150203030f01060309060207060e0105010f081f0b032113 69
    0xb00e14050811030ba40305600441c0c0c07016080c0c040b52101112038100c0001507209334450301c00115104044100030018504003a00206050280d90701030030300080402000526200380303840b03030410041a03101074480c1e2103100384690f00800c845440e0140702402400383c0341c4070818511500a00300c240014041c0c2c600040c0d02858004d8141403c2c15034804071402e00607005480640d04050f00c5012002c950380e540000e18695102e555075600d103120680c8050007000c240c20501034601c9c1c1241060040352640c942c610382c1312481200030b244000c06414107071071440013581c07075145680201156000d42040051840100d41c0700b003161140c07802c105081241c89000546024400082c40c4004109032803190b0803803101103000721001440d14038942d6032142100c012000e07410050751910010009078107001814401445902c003e0010030100d0001a03002c1c990b08440000801d07a0b41002101c1510200711440085c0e0000c6000ca101d00007030040c400039a0072000c0321011034652448007156010b04881c00352454 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 361517041 1250 361515791 361515811
    0x1b051e0108060a0b0d090b090604030f030b0f121b0d050706030b06190810050f06031902121005090703140610180e1504090203030a052209020909010e 66
    0xa1900100440d01d516018015580c0f020b0843d0340490500c840500400c0c0d8401c0b0890005070000031490800403801004100400b250002000c01000c260030545446c01441c15140c0029820345060005112032819110590840400c003030000c280d5000064055030113080314450303120500140100032508070030a40040c00b41e0030040040000d2406504004403ea41c0141100d0a049075054503c005220300d01c488000100f001090182e41e02c86500c03034801801041d60000b81c0e0440c2c800100344640300c003a00010030710100e208841c00741d0007a036042d242c140c1d105142018081c24030600a0f11224854010709200f01982030101e02c4031070080c810401203d600301d10040760755076210200b00390034604280c05410f002507501e83c81040c00c07818031288003800000710030540c1381c18850032030130301f4102c50750b000c9010368032b03000d41e17100980d9001098540282480c500156500c0e035100825100c0c61500a00803c4090311007400701c4e42e4803c0c0c0d005010a800159240751481e81e84205045ca0840c05031821960 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 361518291 1250 361517041 361517089
    0x180207060f02070807110109090212060405060f060a11010902060703091a130e0702010e07091e050c0f070c050411070b150f060f21011a03090c040b0301090507031b05 73
    0x200c00000700c981451b014100400504c1d61400c005c41070364449107809590381c5440c0c0800032985010320859030000d00585000750030302c800c0c2000c00d40c41e1043c00014018425003200d0b01560b6042500942c00081e400fa00d1951161810702d400360142c10903002d102c903842c03d540d1180260000c03d17020b445039410003a20b402d00c10b40c039003c07040031142801303070106045548480c803004504e00108980801002c1000c400200c01c81a1054280749180e511101c0c083c0314103190174030411900b18803d80b040700c0000001d00e0f0380c0b03490502c0d110103130311440c1e405a40c100e0f0908141a504104a41c003511540340503c03000c050680d6100d01e504110700b58002540d5104030303d00d074043d01504008000c1c204641012041d1313490a02e900c20004441c8100740c4c0da51100008040061040283c0c11700039494000c5064160b50441c10f240e00459203030618070f85101c1c01566038803000e4109603001d410141032290004251021180c072800d10200b460750315240260b54907651400007801c6d080c9070384029410b060000840038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 361519541 1250 361518291 361518293
    0x7030c090501030908131e080303060306060913170d0c02240a020c030315030f1c0f0c1a0403030605010e031203150603011d1e0402120106180207060f02070807 70
    0x404c1030b00d2054843d9070741445444640990124004094400b1800c0380d00c2c44000d20382541c4141a81c1e0b04904080d40043c41030105c1501c0014080d908900c0403a8043c2282e510301c640485480c03001680075103c403142d0307940c85240392441001464481e60084050149400224041e6518840c10720303003c8411341000c648450090401d0305107034122224100c003620303005070124240e107582c00903502400405c10807018500581b40400002503020810b901400302000c82c0d04003404160000345188080c07190303d03001c030140c4c60b20038442c2121241c0d12880264009000380c100080100d011101100407a1800b0f41c04100388d03008049212403000000c0082011031802c41064445800180c0743c602c010348508a4511141d9440303000d075020f007084660803034146590003404288000c0180005852140c034900d58402000b04d40409540300d0b0301940c501c1c415050305242c05004095a920400d6070140518040c85403001a4005150280c058003042c440b84200c0e0328003504a205003c00103124400420800b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 361520791 1250 361519541 361519547
    0x11820220c020f0d0503060301150302060301060c030203130801092a05010c210f1b030507080304022d0102011a0609130e011d06090c0609010302090f030d09080607030c090501 77
    0x70341c1c00829031042d0348201148007000b614200c1c42800360300103d400482003020b503040900c01d248040840000c88180310b481c5402003955440180114403c02c40000f04240034107008000311104d501e4214041012665641c005c42d00910402e4800c03540303800c0402183c1c40040c10703400c0400d00c3c0d80301404c03040d0000b45001c00546000d0481e00040300c038203554441c2c24100c032521003920503081203681c030b0b824820060080024003400d0241c03403900700040e046481e5000301e94004141c425030b07030b84081c0a03a941e03180d50000511203140c01b140005401e049110804c1c040808a20264150a080e002403121610940044464404407640c29821110601140796180341c5903031000042440c1c4040001d281281100a500b0348030107501e4005201d0604a0006640404021140c3c1c001a410003178100d1402000018441e40b180b41309045c10503402003000102d50b95400c8060101d00402000c42c0c1015940700c0c4050120386440c8601140c60044800051303a0034000e00514480d0561541c4084107181484015 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 361522041 1250 361520791 361520801
    0x8070c0f020405070305071b081c020702090a0b100314070813080a033c0e07080304080a0c05030a0b060904171308060703090f0605070201182022 64
    0x1924122010501180540c50b00c0c07080c00d0085a01c0d54000c40c2c14601058050212900c640c2d02c43c8014407800e243d038020507655020b031103ea402440048a0007280b5a0500c8003034021504003940c40107004062108040341c60788148140b0300192040d00d00340d045940150100e8403500c0d01422282e03c04000240c00c24410340001b40d02005400d169440c81c0136031344541140d50002107810010a55580c2c05200e41d11a03540201c8608018070a40711002c0b42460381e8202810a40342007030202c03601d900c820f4510354002d00c41c000251107000300303e0b43c0f22940ca080441da42c281801050f600d082c050500464603080c0440e949800f9034024070714031440d8884400344640c502c1c2c001d200742c4580c0c00d241803840e402c00401004200ca0700001c0f0180030154204141a8202000a4420380515182084500019221111704403c030f90708100d002805a03104101a405080c3c205000c2d1549441004074000300262030010b000e0062a00d030b040c4a4150740741060001440050050552182105190f11b01058242d003107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 361523291 1250 361522041 361522043
    0x60f060103150e04110a140d0c1e051203030f07050a02070f181419090206040302040204180b060f0306060705010b100c05060a020306010c12091d04020f030d08070c 72
    0x44040045080e0b440b080800e400c212021902ca600340814002d03543c0320103020000841e080d00207a4641601141c5104c1c05000e0107000d9682c050a8000b40440c110340f0700c009217907003d81c103809081040b12803020750003035005491050768800d0214015100c00429a4860800103152414580b07171240c0030340d03494000b0100c031404c46c41880c0e03010403002a01c81c450002021145014000080c1d01ca07000e406a4284000c4140d80713003642810040d203510f4840303103102d6011060400003411440303400031541d42d214540000e0b41090002400040206030200c0100008590400070005c041e914020400b462240700c0e000c54612a007800807801d070307113003490003802e1141c4110000a141d084d01000b080e00b04107807140315008034114031099030030310500b481150342c40006802c0440c0382d441c1500c0080c0071011428405031210070481d41014403c1c0c010111000070b401181c1e0368802c0d030b242d00c115142940108031800c9000b5140c00380501010304001403600075080c01c42d01c2c3e4460340e035a421021129500411304c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 361524541 1250 361523291 361523297
    0x301050c1e131208030702060f0f0106050f0d02030c04050307150503040311010b030a050105091006080715051b010903110102070201120f240501021e030406030b04020d020a0f020601060908060f0601 87
    0x25000903d800c54624040d000d82c40741c400c203a00ca00d40000040c0c10810001e181e000e44824070010051030420703801a19054950f103080854942010072443e003a54080c00aa8000702480001401a04040e80c00a44201c480440454039056103480700d039027400e20313100060310214105001180029024641c2040c1c200c4082000180b038800c124000b034541190030b0b00542d240e9643d60280101e810083c8885070084400d01030a0100310320300001ca41d510403541c0304a188082d0326099a075000741c424821201612004688019180b03840c0d0b0080f402018450700460110300f00d05115a8240018002d4401168058540030001c8c0d08005d044409025400c9a090a40d0365035142142000061104c510140c030740340c03405900d401c2c2040000380c6000001d401001000030a401144400c0600004690503500f040c40d0100e49648907001180107409202c07012143c0a002054101286901c6110b40004a50320783c00c490232640e80c2e910964850280d0b005d403890b01e0b000800081c00101556030656005a010301d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 361525791 1250 361524541 361524577
    0x30d02090d061803030f0e07031101021e03190905030a030c020319030e0f0604031502220306020a1403090703080c0c0a030b0f0a0c08180c0405070e0301050c1e 70
    0x107502c81040710980c00300415051019a561400d041c0d0501c50404940901002040003001d401800b80c0c0c2c0e03008038440100304a030401b21a02c3c569200344401040b01c1c000314800e81d443c20300300040700d49941102d20900329522186512201d946c0c403031f00b0321004844000c4c0217015041e600e40c804a94107948040140d07090311507034038501303400c40620200c0c14201e03000b65140030401c903004007003002a03040f05880354480c16044c001400401c90119054103000020030005a46070440c20f190384004040b00e10402032689201000014070186400800b41c07802c01c4c1e561400c124880f03142c550402c3c00f0541d071500150784a1030050000500701001003107030707400351401ca4040620070310016944000320b030822156506241c050180343c02c1c0900105401120400003402115240c0c0070080000c01c0c010001000c8800c1d0364200c454801c2c092001b4041d0000180082c0080d00d00010041e0000c02071280c1940607600e00400910b520220106440f8031003201182c821341020b81085040f42a0009007040c00100100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 361527041 1250 361525791 361525793
    0x20d03081f0902070c0905040c06050705070509012301171803040e0a06060207060f0507080a12050703022a03120c04150815010e130c0203160b012402030d02090d 71
    0x9070500c40c028500214003598508291910421813a03250384400d10480c00c060510000528000c200e00a0340c40a28003662a0340e0303a030030141e16021003540440d4001034004004039070401110881848465440d05246a07060400011500b00700c443e902044040e480c1c0c808110740741b80040c4c4c040340c082c0060003140d0805456145920000e0400da0704030880d5a96034008019013a014041000100102d081c14920740224a00c05010792151b400e00070801007001503180c249501440001c1014050400c08100c18a802c890150003548003503030b034004207000c540500c803481c859904866034407481d0601441c00c1c04c481007036074803c03918043d10802d50b01e40d082c0004030740808101c420f40d000c1c484a41d03c280607401c1110281000c004010780c0207041003001141503e0703980b5610030084a80d40800360002c3c0050181108030305501851920700400c080c103643d060148100701500c0e81c1a903039036140d03114a0340414007610f200841d00c0c42c0b00501580041c030004221a03007550282c09408800340c074840f010b03952 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 361528291 1250 361527041 361527091
    0x4050306010b0c0708121804061d01090b10021005070e100206100e04020f15090418170310030609050a060501060210051609050f0411030f0f060d020d0308 68
    0x241c008070b80b96034010400b092401c404009800c02000d010000e0180d03650f13484444042403151200080030003184207035082080d141c41c1e224000a161082c1702d00c1004000700a5000c99100a2080301101820070303840d603102e440c02411442d003080701a00241680d004042d44003019102c001c00c0c080500c02c5c2e5070300700074564583c2c1500340c840c00340981c0604241d00d4260048000030b41a23401001040041108000041e203602100202d0001c0c200d50440000382111240d0b0800d108400595070440c2c02c000c012a80b03090900c0101d544180f09104030000c68120841c400d24a01007154008400d0321844010004161940e0004230424007990903940103005903150740060394000c3e480034005900c108608848000644607046d04a4103d420483c1802807184c4014107040a13406103a00c0762030101c13250015a41e5661014000e41d1924110940324a0040342c0c64509040444400c0d0a14100da00080c1079441c01d081100c00c9241e00a010208120346900c0031140545c0003070000100d1011007444c6405401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 361529541 1250 361528291 361528303
    0x608060726160302130911040608090a021f020f0d050307020d080f01060e010c1712010b03010e01060c050a0204061412071802070201050f0301030f060522060c05040503 74
    0x80e60701c0da14503404400d901c148401d04000d5990808150100c00c2c807600c070500021248424415207405030701c0e13102c075440d11007007900c0036841601540e1802c0e1010340d084031180003a008031034a68481240507551044c4140d181c1c0e601800c02035201c0c80c40d910900404080412040c880c640300d2048071301c08552104201e00c0d01403a00d1035072012038804010400c9440e4108255140f60040303240050a9042100b500445080103004030414070051581010180e44500300301513595800400380c5252100411081800b03900c200d080070710f01d140031800802d11554031002c99048a13542e1307056002503840c01004980200c40040102d806000702003405025a031280641070142040240407294800d1000401c5046403140d40c010303a1903005180100210147c003d01c0042140c3e80c0d45004d0303a14406440100e07158860381e040d0800590000c400401880440e82030b1600d624810701003080300d622001c450411080e6a000ea5103008030803454203000041d10368100010f8824103081c0300781031584510019050072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 361530791 1250 361529541 361529551
    0x711010605030601032a06171503060403030f1e091208040c03031b0813180c17070203070206040801140a0e0303070f09080307060221011d06060d050906092a04050a060806 75
    0x1403501c46540c003243d0440d00103141c000490a6409c1c000041d03030400b103500ca0000903c09401d16540c1c0d00c2d40e54808c60f00790403904e244003940402d410365a8070110140018403a60300280d60030480309140c04409801a80382502494001c5d900041c224950b0782d04844150640700804081d4540b0b080311400201c0d490064614455503902a40000d4200381d130b410b10110400c4802100710f0300340410440c0490300900214880454081800c599a6072017800368035510820000941000c0005800030b0340c80010f5004c3c441c105802ca4500586494a90350b00c015134428271900c092540007000855441c90140e142c0e40c0ca95000d904141c054640c1c0d030745074141183c0280c481981e0141d000540810991542060160f011345d121015020f10b50500c035003404003003003e0b810302240743c00d5600880c15540d07a1205440720741d04007440511640c5444a109516070b0002e0303179101d645100d6020121041c0b98035071079601a4039a0f11000c084e05040300002c00020b000701a0460742503503901d98004c26105424081d00c3e11072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 361532041 1250 361530791 361530797
    0x204120f05010c02010b0a050402070807050a1211070501050f030907180204030318030c030209130830010608191d070302150307020c060c1606080711010605030601032a06 75
    0x514441d080c901d007500e003140141c00c00c5900d41b428150081d40d0360075859060310310903140144c4030b13506464002018421440e01910512481c050402005000d90011810a03101d540311001d01540b0010790703070307104002d0060070b0200c0c80030b006912003101315001555200d02401c0807240c1c125500e02840d104020b02d0301810451760340010307080c000d154114075481e0604010a600502252450311604504030903404001e220345040e4002c5200104d80d100343d07150903900300142c907a03100d40b480c1c0d0400510b011000301108005d01100404281040c00c22414121303030494407084180e1351201d448510304c0c407411100204a0317070380706100070544101c0050071251421283c010f000c003a00314010403440d00014249901145010000c10070181e6000c105a003104005890003500c0d1406485650f04025003121100c0c104140340c10300152465015044d940281ca150300c8065045591064450980b0007d0103400d802d0340c0560010000117030b5a500294180451601d01502c00705030005070342c0c5d0704c016a4004400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 361533291 1250 361532041 361532063
    0x1c0c2309041e1202070f050307050d03140c060105010f020c0f090603031204080901080c07051002160b090106170d08012c0f04060f050613051b04030302032a0307060f020412 76
    0x3c015010064040605000c2d10504070251a01d0002542e42e55103000d00c9000300700703140004c0c0c101405200b8140c2c1c0703038501c0c604107620344503040310590355184248285070001341c0031900311b140e041c00812004014003002d010030b11408004400e02012140290140b90584401c100007940340c218070342c3c15401036114814a603641e500b0035000400d1880041d080060301e013800c209100c0002d81c00200f51500b0200480050b884030088045984004001c01011300003002c55020000e003000d043d03001c1400d64103d516590348041910a1580da07980081084070701242404005009184103c8600506005d800d02051f40313481e40316103600c2040300190340070500001200284403c2101c180920051507500c08810010f43c549100000c0c2402d11001803100e02a0340c80c80460b000801d091003242c1070a0941411070782e00c607540d1400039925030001e10b000c150020f03444609444c600030030a1584414055400460508465480341002041c0004607031411650802001908170b1610f50a4002d09020b81d4480039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 361534541 1250 361533291 361533323
    0x31c0507020f010f0207061404030210050903010f020f090906060f0a0c260a0305061807090f05090103050703030f02071d061017160e1c0c2309041e 65
    0xb08603549280c8641441350b000025190b00d980080c0a81c21601c4038906221100340000d200b540724420350700080d40044040510700800c03500240107068640058000300100980c002444080703020f1441882c403c484200302994052414402158001400405d0030b46031081405000c4115400000f240c2d0114110040c1070f41803064610079508040c882c10004055000c24803200c2d0b40707920030b03544403406140ea60404152942c4409105801744000e0600380101070401010140030b1140620906d11400310403103010900d070414241080c1200e0344031001b065140d04503501a10312900c5801d9450031413055100004146001004050392041c120395005100e003492401d00c504043c07140641410322440705078100c44201ba104000380e2043e01c002c01558032228000b4101c62040f0304c00034642e1b01400707040c2d030600354003408401060340c98821200041119902d202c20b85811003205000380e04000138600c900914202012000ea000c2e208601071000d8040f0140b04030300070010b88130151221104462581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 361535791 1250 361534541 361534549
    0x20108010905062d090f100b0711010516060218010e0f100e01030f050c250f082a0a0618151515050901020c0405010b0711031c050702 59
    0x1601505240d5020b20091802c0740224980e41c82020072142039600741000310b58100c15041140c0b20001000307008600a04001c220122040d000341c6454084200983e40014083c81f04c3c5e00303da000c035a00c4601c84007407402820040d901d5070000e580500d000d12094034072000140d00c40c07000782041840c8504641c06032104400041c81400d000c07045901862114441140c180c1e2810300c254400c45651034541c86a00611004802501c042c82d0035800080c00c1205110407800c505002d0200c85105400c00784c2d0011860703800c0039a11602c5000600449403041c03401e0007045020000f03281c0c50f5203682c0e041002400d27801200d4065080c41e800328006410601800b01004035074003450b0310b44c83c0000034088050116450341c110100c660b01c103c101c03007650b860030701e042c01c0724031403146005020001c00f1210a4171f442c000038103251b001c03400aa0040c007c03869400700510b404c0c410039040c1c03654160444c0c100b26043d82c030514405080168030380c1c14845c1600b08001010103540c40031038030440c0d94a036a00c50603184184 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 361537041 1250 361535791 361535807
    0x1181505060913060c030209061602030d09030b07031802100518030c06090f030c0411040e0106050a0e01180e0a0917031612180605010e10150309150609090201 70
    0x140e0b20404602090011408800341d034680b0b00b6070450340000c0c456070400802e030300a208042c1903070b4100701d01007800c0600c0c1000c6e0590110040c002c0e0155070004c86c03030010440b10302440f40001081d4018240100d02070600c20350249110300da811015035061141b41d000076000300210707140e00c0c00185000035410b2400c49002803008100c0d106070000c002038900c1c000016903074061902d07124014442c00d00c251241c0e030341c101311910800380e0140c010000c0404000c0f81c0001036001e805514140c2402d84000202c0c9031081c0b040301d400c10300035a100d2441e400480d0044841c0181403500d24a00d600c109000300f260b1912101e514001e00e520480091090150314000f21030b80600c1030342001140d4107008005a050301864801c10444141c0740000e9210703a1100d035500208111040a0052403514003148204125540800d069400318040700d0312945c0d0340d0600c1c01021105d1701615030100304446480444e207000b40c101c5001d4130320841a180020340050842c50403594140e2200400c240c58541348019540c0011403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 361538291 1250 361537041 361537051
    0xd0204050f0103060807050609060904141b032202060d050c0414120a080c0a0506090d1e210e01090507031712060607030c1b0509090d140c01181505 65
    0x500c9031a00e01002141c6a1b501c03031090ba40030744400684548190b40304011079841540c02802000b1145a02580c9641c0400071510382c42c41070318ad68109288084181c0540c3e21600c0d5461038600201c00c00c0315404010321000c40200d8228000f1b000001c10f002690145510808442c01d6064507285042403003e0780701420b412441c0035050074050150719a002044880c03019412070481942c400c00400c8003440d102c40d0351030150031402602c3c1800b4401901003515402c150480d6551004107001c800200500c02e8080111408074059052214a0036a084403d4031082d00c1030f4130001e5500b050b810218251a941402240d03290042c034420310402944503e0106410144e559090610703c10301302c041e2007a5009000f1601c00c00000c214002090300c140d000a80e80d40d0f1044012040320150013201c241e00031306015041c4558800b4001031402c490008141404031102c1d070301d030b8010b802d500344442966400007001c06034a5481f4a06400c581c45d1007005510002d100754030f0000054040c03d000c204850700034003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 361539541 1250 361538291 361538297
    0xa05150a030512030c1b010f060b030c070f0303150810050903090a0314031c0203040b071b0213061502060f0603060103020d020f011809021305090403090e0711030d0204050f01 77
    0x3041c00440d0b000281d520315550f03100b1003181e60351907074802500075006000c0700c020841e40481e5007a00750740301074221054644031042c2c248015519011301403668002140c0282c4055400d010101c08221000e80c5444001d000703060000343c00420080c200c84000c4c850b00f114401e680303c494080c078810320320700c102980711442e68091400c2155190015031440c000c0c0c8406000c40b201c00000c2e04072540700b44221091094a00d80e82400c1c1030f814020200a50403c54080d00e0044101d00055051400b50445a0f002c0425124003000348089608101c41d800c203080a08410726541c82c000b095500c80b0307403e964040340503500180381c3c61404081c00d1000e02002001c0c0750003a0010b40040006882da56095851a0341c111484021030303490f0300040f24884c04c00c00a8000030344a02c000020070030443e0340200181c125000401440c070303031030b40c0074400443c200751070084c0018981c003000c100d071a008014051b04041c103441c140001551003511107180d6001908204022640000c1c01c100314a06510b00f5180740d00282 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 361540791 1250 361539541 361539559
    0x90e06090a0201080117120307270b0301090213050d0501090519020307090f020c1c020115050d0803073615020601090e0708100e07050a12030e12060a0515 68
    0x2c2e0000f000c5240610134000380c103480e00606001c040d401e004601800204080d03544e00c80c07801d000300a041181c1c0340180041c98084040c0607080d1003c00170706e070341603c61f080300b04d9166174a041c006600035401106094000c4003048008110707540e51010180885009000100f400003460802c503050102c0049041e02c2c06400c0e640260042e00c2c0469454202d805644001032010980c2842501a1103402040d945601481028159031140010005a62000c50707008100301e00c00e814260007400d640740175a42e4400e004201403c00608000b000b075910161902e050901c00c00058011000350300fa00c0e1070840100c844000d00b100440510740c014000f400484000700c035038a1080f2004e9250001030181c00e10341c60b21482c10071350103041041a2002003500c00100c03080d807801e20911400a1138002007081e1a409965000551458104130340030546540c0d80c00f516840500f60b5040d1103c60091071060b0308840a00c02402d00b00c0003d00500d84203200000d03000c81c0c207250030105030845120210050384504080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 361542041 1250 361540791 361540793
    0x503100e060d061404170a0c0f060609180606080f0303010b0a110a06020d1b0e040905190303060306150503070603151d16260606130303050c0c1804080307090807090e06090a 76
    0x80203083c023049400c02d0441d04101134600b80743e0301a044541040e084e540c20318240c0d087c82d0b4a810a1010080d0188000b0040d01d919079540c641c40d070f04080c0207280c07a035000b44010b010f802c00c0e0b0030080c165034078203080c0350014000d00588a410040e91a40076903a10703501045940e21110341c4e000b1030041c04080008013402001040008d0044214040d8030382c0640d81d00c0c0f8800b810020b08000c031800c03a0664a140b008444400c4c41e00401501c3c0c036010443da040c2c14031070804918034548040e003094400c0140544052402d2081c110004c3c1b200c9401040646c0e40c62100081c3d81400b0311070540701e00070050440000c1d2130f00703103120a003245894080404100300c000141204007602c082c8111413001640303c0c2d00e0701c1e40303d580010b0003901400b0111820880078003800010550400c008012019083e019101a4003a41c5d0801c000020b020004040508040340010700003040c1400440e444421400c008000c01e03200c1c5603540ca080c02c00d8220f080c00e1607690b040b002e00c00e07204100300d81e0302400000040c081c04210b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 361543291 1250 361542041 361542047
    0x7060e030a03120b0429121b010f05041a120609061309031707020a12080f0c0a031523091e0910050a0501050f010503100e060d061404170a 61
    0x80f00165001881c4c0d1100400260f644682081010809007203030071128130306803001c0d5200b91003003486451052400016a240b4035001140b4010301c40d8121a24941e489401c40064540d111300c00343c0c49041240070440460548400861400705682c00c502c00c030340741c4102910504401402409051007402c0400c01c00c40341d6540c4103000031089211480115003c51545801d0740c0c850b07020a14040c0c2998500100801140d0021b0343c03200d618003800c16464410039120b0155071004080e00c024080f210034100090013000c500009101a501d6031500003200e41c20401e1507000e240d103c5e00301c6643c00d1031041c84000341c10040d24100b00324240850b41c40802c2d090010310012030152445c4824413201c01234001070125042480041e42c408081802030100d40391004e49280100400d0090f00c2c45582e42160411065100340c058a10503c6c071070240c1400c19040060040304110300900c126403150241c5200030001d40c0c01d00a400e0992416107083d011410907140c00302c014501013511141c101b000348824540351354 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 361544541 1250 361543291 361543307
    0x50a0b0c100b13051e1e1501110a060507020d090b12150a03052a01050d050c0903070303020309090601020c091902040923071107050f041d07060e030a03 67
    0x4201c0c40056203440c25004030300d41d4204808031582161401040000a1440480c80c9204409034a19211180e450704a40044d20044c80040514400350500140c102c1015007505144040141000708405c032940c4803892400d02d5444046807515140d6040c402c0c01501000716a41d000c0707042c02c007510071608050710560b05000f81c0c02c1c14400c40c4c40e04400705020841550021403843c0000e8044103103640c43e07041c20350ba41c01c00d28441102900c0f550b131202e407a08841c00d000504c202c1050750360318940642e4075400f0b809004068038550900708200900e0b20280d0b41000500003c51094002e141c88039400c5c400c1009ea16002054141590401c54007500309650301d28032181d20000354100c0200c0d8003d904841d100a0080fa0003034078000780303410304045e481403509500c4540c2e4101503c0b603e000707a550320380403500001c184040c20703411f600c40e50701072141e841c3c50014444250740203040043c8030080100100d40500440c040400a50400d901c04d00003254006091030800d0001e60092200010582e00200240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 361545791 1250 361544541 361544563
    0xf0c030a02091b160c1e0e04150c020a06061212200a0b01030203190c14030a0f0308070f02210307050c01050106090f08060c07060c050706050c04050a0b0c 68
    0xe41c07001c0014070320384444442e00c49a8219100841d07100c5100d00d19082c4c0c404001c1106640c4143c1d42c0400003041d008029100c0354002e1400e001d105040c1ca80300c8201c1011001420864180f000000b10303804502da03522800d291900594001e2203070444500702102290000e800c401c0003201d4904200001c02c41c00c500800c1d80079140e1401900038200480104000481c00d2400c403003074041e0b41d4403c4240510319103014140e90080f410350300c0c6291080303600c0707500c55540540103202049100303080104000601a07401d5001000e03096607160010f5646401c1c8007000c400c000c4001c2001d102c1403000303440e485030750100340100a000401d10041215800d2031703a407010f1940c28a0b00d400010014400d648900152466444a0b000070310855841e103901501c9103115010310b45c421501e030107000400b1034001900703d01031026012414540500c07515204080c0c10312420b0780d0b06010041041c0400200f10f031042c02e100f12103046220362120708013410800d0000040d4084000b17500c05001d80203211401088401f440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 361547041 1250 361545791 361545799
    0x20708060c130b1306030b01020a02030c010e2e11060c09091504050a06060806060a051204020a0b070c0302030613051c030e151603020f0a050904110a030e0f0c030a02 73
    0x1502c0a00e050200c081d2a0b508400021140402c001251000310302e400300542d88592418420f4012003401280d45030300303441d07000c0c0d41a17208801d480400d5001c0c08002d0b00304c981c064003a0410784403180300303c01c00506091001c00036103411a964900740364407095100c1c4408145000c0e000508002070354043c41d020750000c2038807416003080801ea40c0301c0301d800c030400ba140f4090014801c610301308030148010032140c410030010030050380020308149011800c4540c11009034403446d0405245080d440c440c0311008004903004684850041810020400038003000d41c42104503c0c000c600310310525080c540c02511b0041401640c41285001480106600c40d414001124041c03441100c040d0031009001510418119400b40c54071050f85032148502c120701c60319090803a20000f048a100890032840b441c50000c14400e07091104603039403132198009010503100140301050041000654040d11340c0403e1860700425503520349840d0404c2d080c0000c2c454a040f11024001940500e0086500c80e20007060080c03003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 361548291 1250 361547041 361547047
    0x1204050a060f050d050c04030b0403030504020315130303020c07120b0a0c0306030c060c051e010905070b04030b060d06020702062703070e270601170f03040501050702011101140c1306020708060c 85
    0x204001b00d2080c0c60045800090070b021905047c10064002c200507202607020340140b100000011000042e198051914010340b090300180c80d071000c400039088a121050701d8012200700103400c04c0490701360400d0302e010703001c5494582400c1d43c80f42d0844110085c0303032041c1418000100040b602d9041c042e000c4506608003440c400e1060700d1f0031030914091000c2100c400041896516207044158003e003d040d1060b0200c403481901e41480302c0303d5000b9480010100001900051590b086c035042c90f045ca80e02c02c070f40142c1002c420f42c0c0010a0340c1c0240c00c5802070210310851003200900003c802c078400210540140a0950418109601040c8003c0480090985000d61400d205890b00c005d030100d514000e046d00d2041d612651600940074124070041c91610a10344090007a00c03020048904403803050719031526144080d0b0055902640b1002d07425015548e0305944404040083c40705407140850b4684d0300c0d55020b0500c212042c598894010200f15800710b9410b00c203916002460503005903a82d411192 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 361549541 1250 361548291 361548301
    0x160210060f0902030402131e1d19030c05010507120f0b181308070c0e0c0a1d010c1203050108120c030304060e1906153507081204050a060f050d05 64
    0x600724141f030092883c240c43c0402c91502c0134585501e055030b8150400342840280741c20401c00140309881042001c90f5008034040306002501d5044070400c1d14401c0c20010440e08460311420308541080b5035103004544000040140d0881c0c80c4a0400c4100700e46104020300104080403a91701802d050410030080c2c445000300300b01c500c03201004480568417102040d83c40d421450014101c0c20207200d808000f91b07514011500b844454810b44100c00d2041e920409045040a0344080400860513080d05020b202c40c0c004c00481c40e0002c0c8562000516107010805e0751502c0040391a00107424400c034078210040c0601c2002c02d0000c07003125002904080041407207031160032050f0405c04090041d04005041ea20725604008040c2c00c1990015815030308440403a45c0c40d41c90300d0403140e24240d1020074440f0700c895410755100c1c01506168512801048591264803403d4192a080c4210180c60031402d01007820481440e10036180c402808080c50b00f011100c407500805011030040480d02d0b1585915200010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 361550791 1250 361549541 361549549
    0x60105030c1b0c0402040f030b0708060303030406090314120403020c030706090e09010209030a0308011403070b04030201110f011505041b05160303020c0706030f0e2d070806160210060f0902030402 86
    0x8410f507600400855407035503036910b1420032500503c0200d502010742070000d032110f07004129143c810301e000340c06140355030b03101c1c0e441400030081c2c0c24049047c00904982000c00d12001000380c0809000400504d00c58141070074040d19101724000042c0c0700b45d00501b01400344c140d01c0510b003022034484e1450307103400d5100c0b43d1681c2d003e8041c0c824610340620170751140500303055001021074101c404c031000841d410940c1505254880e405401040300110003000100010351140d4a5048207590540590300d50f061401103050070340f000113016600f900c540c00003d100d145018400d400c0e441400214004625542d420050a123008103080c3d2006200700c0354490081c140a50110b0b03c0031541c1d88103407030380140c8603200600284810200000c500703103000029a520840022400c00740c0350343e520302400404440c0e010b200f014140040d088044d010741c81d4000b0b038021041040c2c60040b04040051407151400d950021714100e01400c4011026040982c01c100508a800700319054135001880507940f0780d0356001003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 361552041 1250 361550791 361550803
    0x60a0911040b060d09080405190501021902041d0606030d08042118092702180a0b060408030c0d0c0803010302041109062b060605040905041109041a060105030c1b 71
    0x5040c0c51810507044da0304105c03030040141f00b610012101c604031890104903c00c5c4a20390780c0550f0b4096480540723002c64403400ea030703041948903200900210340800d40582ca01c0030041024203030115a8004001e004861806002d190010481458135000780e1401e0340f1401e01240c2c54010030641660304030303000c0591510905040b0450000b010043c100c0d55035a0b41060024002c9100342d02c2d401800c2054030b4a825002a80d058007540c004181000d558429401001c0440021b00f40d003180a0341c0304d0040c007240d22018050070040503d2401795480d03294030f50f0100d060101e05840d140c2004070310608800041c5200c41940d040d61f406030390000d18010711407040d00507440780036130040d4030031400f08244a84002a202c6d0081c0c4610342000e0000360708000312904182c51150290340701091040c0414401d40425901c030503801405046500100b036005000329103000760595059850400004441070304d4800540c005802442c06e1030824614546450103841034003a040c80c6460700355034149000c82c503440800023 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 361553291 1250 361552041 361552057
    0x402160807030c0b0708010602100515030708010b0406080a03090e040515150102100203012909151b0607050a030b0117010b0c060a0209030a0b130f110102060a0911040b06 75
    0x440d9207011909000d45202200f55003103412422500004580c1442441054100e50580e001010301441105840001e02002440107455507101c03544900207640411656009203825800050b410a06006020540324140c020b0212507004601520019600c801074004444000711110300c180c440d4a00f00c1c0c2010744020003c51343c054940244035241c0030648110070002e41c240c0855000490a0110200340c0c00244a242410403101d0022600448001105900141034030388030f91410a0200c0050110640c0301020816850701007038a0514a81a0a0403a504594a8010440e500c0e004000604030311820f98801d08041e00d0342400c4089902406034407030114100c0201303007110f41e100d9180d000325401a18113200c0510443c2e0201303041941038401c490140fa00a4090f04640041381c5079510504405400c032106810080920300204100b06080750318944202c0202d0b000b03c4c13086000900d08038004e04150300c134624100320540002c102003210090b110080d1b801003030100005000414500510740 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 361554541 1250 361553291 361553303
    0x30f07090e0f011d090616020a0606080a021801050d11030f1507022404030807120c030f0b03032b0b060c0705030f06010f0e0a06150e01090b0f09040216 67
    0x280040038541203401d41c11382e201004203d0210900103490034051405592a40064000e08041490025150104504101b0500442e6440802555000100c0315035500441711078001544480840c505040443c0c1c4036000d10f032059915504000009103038658900005119100500c0e200c2c07142e0300c041c0109030b02d45451000f9035041030386035008411210360884114005000300f01e449070f00c0c103407910303105c0048207018010060a0f039119501a1011503024080e10b0900c020404402d0415005000d8500108410b5401064070480140940706a45021404038400c2d0401c0c440699021030468040800d1600181620707500300042c010301000346a03414100d5044003002607914003880b000204101201c0098044403407607184913042984804081c0600038a181030101c04210181d00c560000380c001c0421200003072230950340c600c0b030076030100d500f4050b1020522800b0580d08a607081100d001c0100b40381c5110603e802c210058100c07444c484d6040141c8680d40c0803e00343c0903018103820320881241e00c02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 361555791 1250 361554541 361554569
    0xc09070f0e0402251518170c03072307360209030a060e060106050901020a111503040b1f050f011b02060301081501060302070b013303020c0f0111030f0709 68
    0x1041c2480c22485103401710034601d00300340b01800040510341e620f01800390010668040d0a44094808520b0340c0810070342ca441e0301c0144800d6001c9414221000d000c2d08a0740101103101c041c1d845144d041030b02580c0300040c11400c0c0045071440142d81034a0b02c180707440c0e1300e0413100708603218442a80240103c000782c40c0c00d4400c0044403000c2003801c0c2e011003140c91038001151605c1e0390380d00041303659120381c0c2c005500507040070560000040610606119507a40101000d80c92164200180080d4100319002d80d043e50700e00c810b000900420001c0e00d410542ca21001d605110308081c045094101c1c2825050304000c04241035010550440464080031940146169135a5130f603141101c0c1d45a0100c448140a030014000000d601802442241c0c4180d50040984903e686406149940c458070000c40e1118844040100c0e80307808000344030b6410101c52902c0050f00c507810000344038035110714802540140e0b031400100d075a00f550b00c0402e40b070f400008011150556540c10380d00704c81c00d58165010102c000420303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 361557041 1250 361555791 361555793
    0xd0f050a08190210020705120f0c01090812070804170c12030405030705070b120604020903190302010c031a130203130602280c120f0c020306090c09070f0e040225 71
    0x1100c1d66a440740740580c00c880c0320300c3c4541c051350103d1080c40300c020920390260304c1c440c0c1020315080103003900d05d00c1c04000c203080c51503407801c0500b5a6000c2c002200d01c0a400242200c40d8142e001005800504624080e0310314505580c4a04100030f000315207051200c0d011441e06489142080b2300c001d4620707034503200b9440742028502290740e6000030604607a10700580ad008500d620341001a1005c14854a40f400c2040d2030b5602440008d600c81a500d40d058040e1074030706485584141403442e02c0358884e9000141580611000400711044c0e407030b04145640840c0b8201d5416650400000c2d100070840c2c80046e60303921230405a100e44005902c005040301c1c000309407410020401c1400200c2c100c0303030042c1020100300c1c03004110381581d06808001c004078031750ba0a420b003051084500079603181850601444015568000a10b0000102c03802c1140340e00081032091709050a48500e0741000711414a1108110800c0e0050400305817254070902840d0f01050392030381c508414402c0d44a03000d16206d0f0700c49038410707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 361558291 1250 361557041 361557067
    0x81b15010906060f0e010318020405070e0f060403241503050a03170c0a0f031e0e0f1204120f020904050c0a060513030209060604030b07020a0501050702010b0d0f050a08 74
    0x20074818001e407646494800110940206242c50580340e6130766400c80c80680c03080040d0014801420310120000c02c050040380107865600c80d80b80103501589a03800c40042c5181006002204d90051a0042e41c00384800c0002855010065400744501e104441038070601c5c074101c0300144468065965001c203403001c00000e10501180c0880c0c458000d50b6140085810b000a005040030103988000c41c881d420805c6c0076506100c0c245418100c4514900400d2a83d0440c0c0c00c8d0880312000ca0307040c080c0c1c0340c4e44d003c441c0214004018102c000b22005000e0010500c20b1401e000050040b8420981c845000c0e424001c1040710b04d805010949500518001c2142842e080c4070ba524507a800025001c0d040200010580c14050402d4528240d501c4603c221034504648c284181450043d00543c2c0092051201000040000c07013001e102e00b40d55401801d8941450802034250b680203403041066902d4515002400e1302c81c900240c2c204c6821402060855180c9e281032450401c242401074100e910215501d921109 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 361559541 1250 361558291 361558333
    0xd0f050702120a2d080313060605100216150804150e010507030603033e0c0303041e1409010b031305060a0c0909060b03061c080a020610080613081b 65
    0x805207200d400c2c00c080ca0800030340ea0201c810340117002c4d100b040c000030302d01030590f282c0425194410079010511581e00c401084001d0302034107101026070081401c050078170f80d0202c041d01c02401220342144c400c3c2c8114002420000000d000540594406050310000d580c651300180032881c03101000304170b24641200c0c002d004102c64001200002c0c50043c460300c0340d03180c880c803200405001320700b42c0c442c00c54004143c002d1014945114545401451604180c44d50300340080d00007440d0445041c16a49a4842d071458154107541003803a0078003a05120040a444404500c2c1c156249820600d50b680c8920025120b40d41d001031001b01148100800c2161108031608040150000c603102ca900c0280c44650701e00c240c90450064445440e420310010301280790407000f2243d80010998010940040e40d01c990849601107840700015034042004d1041e00e20750040030700e00401c030500140280c0d0411001c00c0300c44451402015000c48000b24030540c5080300d28560700c2044100000f220b0076192b0945018031000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 361560791 1250 361559541 361559573
    0x201303151a01030c080c16020d0c080f0f0d0c0c0504050a1d1207171c0e0607091404090311030d05011403071a0c100c110c030d0f050702120a 62
    0x840640340741c070324650281c080e0000c4019140c4a000540d9104c00210300350750800c2001104044c0350308030307040140e00c4601c0c0d01c00d8114000c840d498035290400501c07070b183c442d0341c2401c005507500410f5004929203001c512110741c01031a240180c152003045c140016101c585811040e0b009240206101600c05503502503106906010304903485214640307841522610603180d1040141020802c00002945048044240301c01d8040317607600741100b000082c160080301324480020f48d540c466500074080d1040114540c040c1c10381c5400c00641e03051214803c82c2ca10070300f02d614000d5498040040405000d40c0c03125940340304041c00c40b5160a00580e14602400c030a104803040c1501703444c418001c6040206207001a11448a46441c2c000b50b8000c01120030f5205140c45442e60041c0135083c0504c0d8418003030185040015620310418920354000a070401d021949010700c03030f81c440d0303800c102c0490b000048400c41c0e0015040042d00c03030f43c55001240b80c51655000080250094041d0b0f50b04204241d1246c072005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 361562041 1250 361560791 361560821
    0x1e0606220b041d0f01050604030605040213090c0801141b1c02180a05120c3106050f01030c120903090f0b0301031a10030b040302030c0d08160320130315 67
    0x50340f544488a00404c0c428011940c201c3d074100020700c0804c1151308404c1e005440a08010176449003134003600207c500012088403010380143c0c040004200c2400341c1c0382c50b0b4815184100990519848000e058030010b0304c174120142e004503880b80b0440300f072180c90a1031140038005650310300305440e01d4000400039950441c880c00c0400c8022070607061241100c010101c03d503000708002c550b00360800100c28016101c20403004a0000c00c0c0c4105040d60500c54041c0044030310109506040c8810404240c02b0242090b040600d003480c07a5088607130010075036903080201500059809180c0c00d0817911405941c02000881c082c44070001902000c4000441c101c03030098a01c42c18140345084070880c445420788603c2242c07a8481402d2011400d000305c081d07001071090049a1510841408081c104145040c0c20404aa004410442c1d442c00307203004002410321914040003071080c1304440007491068a0500c5030010404500f049010000306460700145421444081098601030784010190140800214030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 361563291 1250 361562041 361562099
    0x60901031d2d1b0d08070609060204031101020a1101030e0309061207111501090f0f050702010603020306060a05010c0b0403170a020c1002030405030a110309040906051e0606220b04 79
    0x140e50049618561015240c00c503d4100348020204030752800003100580e1111020000d40b40021003500c9101c0040303224500c0541c0311407030760400f40074150030110b40b42d0642d00301100003000207001030440d020706c0c0024200003e85c48801c3c40d0591450040c0c0e4845500000b0005000301515102030441d4402d141030340d650102c0002905045071138545010140402c3c4a0400040c000c07182c0d41d4004500b0143d0141001440002e520000f805440e410750f86000940d6640c5814400d45c2000c2c00b2041d40700006452420708940340400080c555502144c01811b9401c2000c04901018428008881d01000c078510007403050802000100096001c000d203008184a101c47c810102c1050307009a03841203411a002d18240b00e15047d050b6135510040b0300a01c101c1c00100400c03580c50f621841501c032650301030f000019462500600d01004605064094110340c1001e00c02c006850f0340e010202c43c0680c18070f00e810a80132508003289004840c440d0070a080da140b0114020500c06041d03c1c90340f074200410700702064 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 361564541 1250 361563291 361563373
    0x408040b0705060411060c0d0509030c0402040306020a170c0d050a021b06010f060201091e050f06160801050d0c060c1a04140115050901060f02030904020d050f09010b060901031d 78
    0x111f00c15181403400c85d420901000b550580204090b28811401400b55001000d002e000075049a0054104403051a404250140700300d034403d8407a4640040c40602c02010300780440c0e280180c0c003c20320352000c1d181c2c80d40300254039481c590f0180e0300b090400005403000c00d000341180503140c030000d00907400d16031050140000c03006e1050081c11407250f00f1000c18226804030100100808014003000d4655104d03102401c0d9200c0010492a44200a07400c4450701e0f17410540c000400215041e40024800c01d00700f901c0b040420070300c0000c201143d00c3c4d1f05040829030703d507280c20710241c243c0c042e0051030120303040b0401007801500da00c0760b45000c030480300030480f09134006140c8082001500031541c020100100502c0304038040c10510f43c204001780112820100e80c2d40000d016644200c5128031055210818040901c01751004640c000100b60000c0c07110801601c00f0031401c1c000c4a20b81c43c1099200c009001030b90795401c0481c03030504100c4090b201c2e0100f15100e0030500d0079480400c000c0154070303108031135 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 361565791 1250 361564541 361564549
    0x1107021f02060c0f18030f070306020309120414040b12010203190c03022b0e0105090c03012904020702060d091a06010318061112100608100308120408040b0705060411 73
    0xd90403000100045050075040002c1645d1858110f0030990144101e100d180d0003044100401d00c001c5105007005a900e240c0b101c511810042c08000e1105000c20900052004408020b0248110301c6c2c02c2d54006451102900044d241410f000504042c6500c00402c1c007038100c0782c2d00c2242c090f084c54030505004109549100b10221321841c2e00000c41244c10f504144404060780400c0c400740d070b05444020401c2d4400301c15060071944140c0f980100d517032004191408609082c0211407a92000c18540700c5c00c0c04400e0f4601740b01640e480c008903c16580000c41d0001c56130341030207a481140340c400782000b004009141881174280044084ca980c10414000515198802e0043c0070140c6003a800d42c0b021880c07242d4030600986040900c00a2503c402c2c4068030b82902140b07402880f50301405c0030704802503d03042018083d000c014140008c80481c0e804280081099001201c500011560701c03280941da480c1415400d81c01b807a041105071542c00074544050007800a46203001e0750144514110700302c0007900708 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 361567041 1250 361565791 361565797
    0x8010303090b0f03040b0903250b0105030102041a03192903010c0203070b04060f090b040b1e070e040905011802090a09020f270414160311041107021f02060c 69
    0x55003c81104000060010702c40041c00c603008040c100c03c882c240180d20030a250002a03409801c21003504003624a000d1010248906004040a0b00210300d400d04286011819039072165402401c05800004504c54244d081309260b98240041c0e01000490900301e1800c1c0b40d600c0304004260060245066454285418404d49409114540040d8034202050361031030040040180306844283e07450740c0c07000c5521100d008080e08030b03208220010007440e2602c4d154ad44200d0107040d040140f002d84405c004242e030f00c1200035401c0701c414240354800c8812040068003030005920000c1080d400c20304214020100d49014200304d503c00ca85640d41ca664940006040b03c00410340a54009001f180705c4604c0d0610803e0001f040d03903420f00c6040c08003130314489140d03100000d0307a00b114034030440745000c040d1042c00d01003480c082c89a805550009851620b07005050f012580e0b05612555a80403281001c41c80401191405175002d800c107128040c0351000b04c8441c1504400000250141d500020000c240786411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 361568291 1250 361567041 361567057
    0x1170616050a182309250509030f1f06090b06120603070806040f0c05090402152b0e060105010c0c030b0a0e0303090d0306060507051005071e08010303090b 68
    0x203090600d8500d4800b1250f11101c000100d80300286440042000c51100c103a14400c40140c00845210840000c107110f010071009090881c0384404905402c488042c04140c0a0684c1c0346207032013515111500006401c048480d1202c69075441901c0b610000c0c5190012200302031300c4904810080340c3d589440c20025200c1c5014040d9020703034100002c1c811403c0d20100c16420804c003500b181e480c1501d4080d42c92030940c0c142c90a0310400a000c40300d200b04800d5508110140006035004100350425501050441d84500c1c0c200240b28004200709102d6111442d00d42a00c1c89485162903c1012030034030003005280c1d0200a40c120b02502c80042040e5014012503014950320059905100d450754075842340300f0601501e00c41c006501d40044c041a03500800103180141200000340041c0d403403403040a03003120660360091040c410140802404101d003c0346030304480c80c13030303981c00b103071590b10100c0850740e4a280030740b610101d9100c0120740010315481981c103810303203100c0e8688000361a00c0380c0d18910180101c171a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 361569541 1250 361568291 361568297
    0x30c09020408100207050c0d050c19060f1215060c02090a1808070821061002010e100522031206080303160c030c02040501120618030c020d140601170616 67
    0x507046a0f081c9154000c2c4202c9008105494030520f04000140c82042c04c0301c82601c2c551f00100a0071810324140d41c58560001d4014400c0011038584100503000c0700c8840384401c103001e43c01509981c03680064010006050003130240031440d40d01c4580107031581e11034150503806229140005030f1801194810349952001c14810681d02c3c040035a55131900b54070011045601550600c9843c0034401e051020401000c00e000800d112450400180440410001005411a814415840c0301d501012a001c584aa0351200219042d0740300c101d0900701c14400c0c1074005641100400742400c1c1a4840130b10340041d8000d41c014040c0c2ca68400d11903030f507800151004645050303084208200d903406000104c450724483e040c002025900d54000401b1940c0036400b400001c001d0000900c100981d03413080e0900c0000c0800c0d00c0303401a05945008008494001c00240910401c1e424801030154407951800012038007002c035101580c44410b008810410740c5480902846100081160038148070f00122100f00142d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 361570791 1250 361569541 361569553
    0x71112042c16050d05010b030a3b012009010f0908121b0105070e10021b060f04090905010c1b02030607050307050403060e01020408190b01030201050711030f07030c09020408 76
    0x1006000d00c004080340c91003e000c8104500300c00388065000da580285405040d203a00d130318120301c2810940b40340c0300030341070075038904120b0132040f00d0b0600b07a075148540c08d001e4004401d05081f0140740140f03100c4039414581d4025041411001c1c8143d002812200d101707a942590840d20b8080c1511300840702e00880c26940c00501000c05035004000141c008144081c045501e11481d040c60302d803c507072060300c10f000003552003848540d16052800190384544110710003440071980340c91011410313040d4200041d01c91400012186071079000282602c001d0304084004010603190b0786001402409100d418102062103a984070208144410601e54150b4014025002643e02c6840803200c0f030f44003c1c84441480014400800458242d2007803000366540321000603699800c2c08050b6152401581e074800c4541c0100360a040020012400310341125420708002c0c2e2200400c0c079154202c900452810380d014415425100c00c00c400016106003101e0045482c215090748814607501a4030070781c004c03510198844 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 361572041 1250 361570791 361570801
    0x1030618030e10201c17011403010e100209041811040b04180f11030f07181103150907031b0806030a0203060c04090f090c030308071112042c 62
    0x9200c03c001d80705868501200d0669124100305400c07500d90640b02c0032680891120740c1001e00e1128030303c054184c1803e0450f010f8000d501d80c02005d61050007045040c05a10501c400c464609402c0704519a4400d17094855643d40074001c0d50081d000500080e2082e800c1c29140350840f58501414481c0d80d03080b081001c84164640f00703000146c000581020380003540c0d45000105281090010081c0358841d8480f02c40e501d080d0300b02220307680f0b40803d0f280c2c0f09411404859811207000543c5804440c40d200d54103081300000e66041004050110100c0c0124100204004920f11300004c1316034281000c507940b0300b40351614002181180c001104411002e4441e102c140442c500984020364880d100504450011945030702080c2048030545100200c44d10208060000c5200d40c05151300040c402c0404005d0300006031034014030703001e00b07101c060300740080040491100d9100302c00a1659040c6002160744170a4002c44004041d40184542d0904c00c2d2484461a040a1352148142c038000400006212640769 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 361573291 1250 361572041 361572049
    0x182108010506160c0605071104180b0a110a090504051e1321030905060106080405030301270903111009081b0312040b04030909050702060c0f040b0403050601030618030e 74
    0x9007a0b024030f0f010341c180e0483c006001c450640001c2c240655806485890398a4170090695003044250f110b6800c00501d0452805a000355501c440d408c00003002c51a100e001d011002015003200702c4144131400a00c60350340d1034100480d0390881d50203960410461b40d90b100d003902c00d00301d180000b555141701300b4080303029012184002100113000b00c80b5220b1501002c00c0b00c0303130032010b0900004080b9448494200500c4028406c0c2d0b0300402040c00e140f4018134299032501c1c1c80384414044c112800b080d8140052400f0b6407180f01d40044074151000b000308a516040180040030100c4690b0218441c002c6015070702d003101d01030150a150702103d5542000c02c100704d0b00e031f0a10310300c101404180c071060220f5020282240388150169026100e26407460905040007401e2031041e4001c0360320b503414070f02030082c010350010b40c2c254041180940c06803110034a002c85902ea10031a40441c14420001c5408000e000c0d012800d58100c070b105600400c1001c503040c1c07200703800050180001e00850130440c02c00a81e0700b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 361574541 1250 361573291 361573297
    0xc0103020a050d1e06050109120b130f1b05040240120204050a090506060103092103020d0b010c05030d020d090606030f14010b0307050121182108010506 67
    0x749a04003281000801c04140003182c204405403500200d40ca80c8042840400f88528005001c0c00c0c40d080444030304002e058041c950f140e03a4014482083c2c000050402c0f000f403031016000c10360100422003402d0203030600600841d10340c05101124643c0110000e001c3ca0b03d80708070f42c0c0c1000c51001c14120f20400807160070040940a03804240d0160350200d10211044100c00c0e03201920380e00350700046007180344c0180300848500800c3e810165150082210100310000340c06680700d2002d107030200c2c0003543c528001c84003086182913603000c4100d00740818401f0f5015006008090161841040901888401107607258803500c000b0303003190801c102400084c0800e40003004503940c01040071030100200d42d50103085414650054034402c0c603d80c025010460342c1c003000c40e0001c0251000b4404222107800184e2500e032148a0b803030500410110740c26000c10321120380800302a031410200304140d80b481048080c03400010040750706c1220703480c2d000e01400701c440160441c00c8003582d41801c56820f1400740710301c170740c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 361575791 1250 361574541 361574557
    0x3050307050607031a062a0a030908010218060a090b0d090512040302060a080c0c0d0f030c030510091a030703060b010f02030301081005090a050607030b0103140f0a090206040e160f020f0c010302 85
    0x301281a00843d021803a5041403032104801d0018516032380c15060041c40500759401040e1181d00421000420051006490300700d154121040d503a42c2c2d00080d01a00d101da13103603114074001c20001c151000c42802c16804035054a005100b55100c064110031b000040340700d50301009501940502054902ea88030b003113942e82c40307101898403501d40328034604a107207030003003003021040000d80d6503881c0032100b6454000c1000e40c02c2d1030b003414015810981e6412200362800d000d5800665903035001c4004000c0310400c1040b0b20300f0040c099a00aa0b140e090000182810306811404604582c580541c8103100104481c1200c0341400a03000d0b8041075602c20700a4100680045003d110301c0c103030140403c000f070004074010411071700c0c00101e15090340c002405903803000c140c0480c1d0410802c10402e20100030603445a100307400c0c00001a00c1045c92001030a10f0003103802505c081901d50040054000c0207049020214880341c81d400800c0c12070300c9080b07a45800d0b804600320b840e081645013040c254040d80103002d40e5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 361577041 1250 361575791 361575817
    0x30b130b010207030c08160510140901050f04030b040501050609040506010311060712030b12010e030f1e030f06030c06070317100b1317070302010203030106050c01060302090103050307050607031a06 87
    0x4594036200c4000700100707030700101943e800100040d00f41c00360f24450315004120a035034801400080d40d60152000c0e00e1401c882840c008001050035240c0e01c544115460a454ec4842b9912291641000c09100c541160111807039031802c0f010842500c0c1c02d18285125650020090030b0580c00d41da076010b500821448001c1e00000c1c144003d20003d05500c2d4803107004c2a0039a000900c030804841000070507070089100360000d0349095100e01024a000c0100c991341007012031915902c40075020303125900c1c4112680e902c0240804801c0c004000c0c3d4601220303001c0c04084044440c00440801002858803500750010081b580004410b050b1004040d0429803010081d1640344050750382e103014601584c81054010000c1520190030310200a00360012003840003d8402131440a0445e40040d41da8403040c0900003e1040c046507408101000b50071410141d0b03805002c040307403941e40b890aa036880c1c05c0b80c4812202030040d0400594036901c00d103e00c401050702c840410717070710718a07100501205500407410030800d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 361578291 1250 361577041 361577053
    0x23030d080f1602210910050901050f0306031c1d060301050a03060515091e0108070308030f040f0204060b0414090c18030f010c020c03060a020a0c11030a06050106050408010c030b130b0102 82
    0x1390413a01c18090b41e00100c0030602c19600c040d16070030000080d001c0d00c0000d0510605111a0180346d0381b040c20b0780c0c51800b104640a65989401700000d18045602c481403401d04408111f00c000c40d41d00c603000720342d2090b95498240c841248c0608001140c00300740600f6401808680c0100040b8801d03400864000140d03c510b482d064010301d000c0340c46d4400c00c5034a50342d24410020001e008004100740c4500401680c13000d800700a0959403152483d100103003116442180c040082010310044115200981ea030003002081070326501c49071007503607400c05d00c0f809c40258401c140b2003816080c00001c040c41803c4c1445d0f44c5284c008004c01c2c0350007181034014400d03014841d0400359980c0d07131003d200e1401d07590340c1c1c1c1d0002c06602e820039040600c4d040700208100e60090044c8814128550040c02d50b10113603620858002c05620072070003180c5401d0110002510660405000042c00c0303410000400545000000a1001c540c02c000b0940c242c03a40a101150484004a024442e0214035442031401100c144141c0704 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 361579541 1250 361578291 361578313
    0x1806031f031103190b0402010c05121c0b03010e0d031e0203010803040911040e0601080c0c0d1d0a1d06040e0d030b0f0108010605030703090302010623030d080f1602 72
    0x30640355608219002c01d4100b040d84194501080f007031010710b4a81c1c4d00d0280b50081580e606110307400140000341808000205201000390a100c010504500164400c0d1142e90028100100300c2e00c45003461201c5180104010b0513041c1070094090084218006201c04c04030360400714020045120400120800d4801c8166552010300007140282600401182c440d410165000101d03035519100c0d5541e41c4007000100203100c09480300e03690100c0d003402c121003269906464002c1074403903040c43e0f04550150f00c40d030044460b0003140b4803642c10410700e013541d4840344400610000c00560f01a0075265508104541000d01d000400140d0207903015101103114a108244030b841c1c00040110000400e48944082e075040c180340040030f40e004802d203840f000746e516181004d0814440540640100b41d19068910300b0315000350020300c010815640550000d941c0982c0300381501400300f940501c00d000d21000f8031442c2d48111600c500502a1240d5106662581e424015041c0c40080540c001d40c002c03440c2101e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 361580791 1250 361579541 361579591
    0x1d15091315060b0d0e06070309020a06080601120501170618030f0717040e01090f0507080c0706090c060f03060f05030309190504050a020702210303160c021507050d020102180603 78
    0x854001030b500c00201e120b02024a502d07041c00d0008080f4070805190a0741000580d607810318bc5002c4030b8590422070800d03101e4500403540690600c1070200e00074280000010529003a2071002c041036070200680c0d016441e500704440007070400e0b54850b001640103100500f603000d010001010080e200b139480720803009000a15540c250000c4e44680890481d00380100f012100600402d24081354185080002c2d261108001c2c4c6414000b5212500350103012841100b040001c2d0300001034160428482034400d42c2d40d40d00180700030000441c0303000080c24000d000a184103809428426941e0040c0039504240c1c60b1030a1100c110b0208451118045015200060780d0301c85218081c0546200d00703000d44d0f1035400c0e0040c403680240034543e01c601000040b03071000720b0040c00300589410840d034104441294840200803100401ea1810281d070051140c045401d5036040040281941072098055034024028164280d08174000c401c00071000719400c0c2030711403081c075240008581c004074000003d50601c2e1038003186 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 361582041 1250 361580791 361580797
    0x7060f1733030d14040e04120f030209090f13020301050a05091203040507030b060a1508061513170c040e0105040308010509010b030f0c27030105090a080706020f041d15091315060b 79
    0x2521240c003c52642c1c09200da02440c010342c80c603412b04084d0f02d09002c03a004550f4000e030061412081e030441c08081401d255140b400540250740080003444a070511460b03078002082c0c2642e990340280b00b0f0100800c1c0d80c1c990001500d00c41c0d500413000d48040c0b0b1031600c85000705000105a168014000140892f11050b00d000005520b12075644000b03484c0b910308244000011808558404070700148504503010101c08460404d40d21040580381e440940c2403406843c20a0b01200c2d55070141c1842c01005000f60158005882280203603500040c1d0390b40c403010b0000f0507070700303010380d030701d40401040058000700007171031007a800c0350703640d10264030740a2022101c01404101d410f03256800604146c080d040d520302400b41d5034102092801916110b00c09560b0281c9a108181d001011290085000003c9900460554000b4546001241c10844a0140c92820444101c5910f00149040324010702c0d1070400c8656a84154540c28070302e5010401034807030030150070301441d24071660ba07100d69011688120142c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 361583291 1250 361582041 361582043
    0x80f040305010911041b030e0f010e0619050403020d03050c070212101d07090e03131806091803030504020a0b0a0216080102030907060f1733030d14040e04 68
    0x303c03c02c0900e0300c48000849035207641d20035800c041400c19031480b090030800002e5198200007542c0b141f001102c0c0d0605002c403880565552803c0d4051426000101c0d200f44258070b40344047d050355000c0b141160440c0c00c265806401640035588900801d4080d610243e005019003211504020f51680007403145000d020785414160454040c2d03100b902c0440c00741080400a00300708080c240d0055940540d10710161041e075000c40d46170900780e1010172091080380c0d02c9005203501c044507a81c4500b020810200c03554a514034280c98070070005658036841c8540d80041000c03012400c540c5110b0b440c118043c0c42c0150050b41e009000840c000f07800c1c0001402044010b415030017900c007815000c2903441800c101540301c2c000d16401081004054a004100481607032010308100807000078044c0110340d120404500440041c00f1101803014409071000418180c4110000164800882c040d800301e0041150140d643c250f40140321440d2028040c250080824106095060425641d007460111244041c0c80c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 361584541 1250 361583291 361583293
    0x30f08040302040e010603030e0d0c150903020a06110c13020c0a0b090d03150b03090f01050a0603172d070203121b06010f0b0306041d01050601081305070e04080f040305 74
    0xe400c10441c14103028540700e0310f0035940204401c601d182c5001d000e49604400584c401c1240c09509170400080301c001c0400352071030100680d00030407181c0c1c0c050301110b05400207907c81d0421040008041d840f40d02c088000b0b0010174091b110303840c2554148442c4202490b002004507400744000038050008214a20903240600051a45400c0a601c01402c0c08e036aa0443c40c201810308003484100041001b1800031528170610300c664039a6680c541c40c4c103007447c499240490394202014444d003090250481015203014006445000100030040c2d802d0b4811703408415122148100082041c9020030b544c0500209603440203440d007ca60741c0080d05000782140e204903880000704c3d005000c520b0504100940c41a0240184620f504000c01c1c003000020b24840c2c0442c2440000004400781c032250481c0000c84031180e00c1825540690003028003914040301c9075400a04410000b42c001585410303440391090304440030307090351400d00b401910000401001039484840130000c0a251420b0344004200030350144d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 361585791 1250 361584541 361584547
    0x309070b0d06030f0c0e100609030f02040e0712020109090509060403030b150d0509010b012c03070f03050609060f071b0501181a0610080601030e07150f1101020f070b040c030f08 78
    0x682001c0340d50000e4540d801f441006001445815048000142643d40104642d02014038900c0020064500c000403001580a000c900180030038040f0202c042a41c405d8035141e15080e240c00c0102d0442d0000c9540030b10782d501034000300d4040b038025030000c0340d0098094124103e4640030301d00015140d00800010000c25960810031116400130303c50690705000c00d203410070365000e03400ea4040b0b50020800c0c1201d1485c0c10440f455110b981c0c20000d0700020240d002c1d562204c2646e80c00c1040e2988021030322241280941c100060100300c007803c03030501c54481910307410300d0503a860035191490010741070110752035941c0310184180e503030780d01d81c400d0b01c41403003018202a24203518030b20410950020344528007414001c030411714204d4100705140c1d4003060a00e40050000441c88416140500b2503101180d1403680d058400201980111044410040c50700d606102c50045100e0508030301c500c0da58600121410302041002480501c840da030098098103072442202e032030f40c640c06178090304003508503a44c400c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 361587041 1250 361585791 361585799
    0x20412020111010b0d080f0c0601090903120509120f090307141003060509060409030309020904151409120c21040311040b030c01230304061a03030309070b0d06030f0c 73
    0x784500c1d40d542c0003000380528074010011528190413540700418410010070b11540d800c3c0c0002c151002da0225004550302540c2d500440c00061103059400c0c0d0014480c15404c502074210b0740505401a0480c5000f4030301c102d080c1d500c032001e54100400b41c08881004102000503650b08110311030241105242016911244004110794400c80705402c109040c00d0050422907075950b03a0703c41d54008021b4401141861241c40d0171001002c0d8440021740c852040d50500c0b050088082d01c0000c4e191140c0b00c100121034585200c00d440c1c140c12a15014560700c404c1c0e00b5241c0c5101c1034050820802c41c036045800da1441c03041c200381010402c4003042c080810104040082c0b1060141404560500740c4082010507401c50100303490b000a84096414003003001102c1e20b20303000c21a0708a0b172070901041c02d81c0e1203041c07e00d01b2401070080c9506812224242d00361900c0305d8640441242d000d030402d0340c024282a883c000031002c1c80d0f0000b4400181151361150b0000114241c40c0350301c0e1a00744682143d42c001424 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 361588291 1250 361587041 361587047
    0x20903240106080c0403020f0a050409030305040203010e0c061b010617010504030206011203172805100614030115050405040212100605040b0a0503060a0f0303091d070c0210120204120201 82
    0x142d020404102c1c02c2c1c0c003401000454603003102c4c203a0750152642d00315130441e180414040443c1c0e40c0106c0c0c0281c50070400c0018960f150b844540124821402407160341d190284482d6605004900c26a00110070060071104490301c2c0c06561520300054000b00e12035549420105000f6940810920301b070351a1401c0004142d41402440e0242500643c2500360020544008048003034810030b030b4206055400100b100c20000e17218420321040c4803241031958040c42000c46020b031109842c0d11440720441440450030a0190030198210400070502c01c0c1907a10f480340708918540c81003481d4041c01803c100210f20782c0c4450000301540140c0720400704160900d45030240a000c120351048007004024002400462807040440790518860301c1c02503102d4940100064031811290301c501d908000c034207400000c040d00f100300c0c84129003105080c4440d491100c1010b503512a802c44080b80050703500c0c42544018a130000386014001041d04e41011414844000d0078101d03440742e0011100c03052499482021503034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 361589541 1250 361588291 361588363
    0x5040e10020c0f210412060e030a0e010212091c0c1e0302010f020606010909150b0a2303130303020304081c0e0c0102150c070f12180b090f100201020903 67
    0x20131055a00d1003022400580c00a500035405a0000007080034001c40034005039410841c2080e03000c0040e80e1b61080c4900380a0950b41e64008880e015002d155030300c56100413101c06807194610089c0040c0f00c816000d102e40360403501496000c541d40c240c40040403641072480c404626031805ca0107a20301c9a00d08600002d0328a1a040044508541c042e0b000c1159999225007940216641e1201c04919140840d00b4240d04130300d1900141c460950105148021680c002c1907507070f006117200d004113900303025100c000b4030030b110403100c180004095089000000e0310035801542c1c8640030380c1c5031600740320b01c038205002080048004004150380303c81000054040a2042e0341c0b184009000603d1072942c001000619280d004201c908050310214040044c0091600b40c0140d003030380001e05581c01c03121054090643c18404410046203112400c022594041103c1101d80040b0f009040c091140c11100401c895071b09458480d0741195000d211458094030100184d803500701d2411840881c0c00c1f05403217004a105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 361590791 1250 361589541 361589563
    0x41112040c0512060402210c030f010f05092103071413090e0a0b010e0c0405151e21060112180209090a021005090126100f0b0405040e10020c0f 63
    0x40c1240e01840016a00d01070f071007000c002c08014107e0070002403480181000c0c0800d280c65014010f80000c1c00803038906500428105003d80b0301080940c5401d140c8a0ba91003942d81c4a00c7d4a06895031009a5000ca00001d1a40807401d840c00032887c002d503840108054014030950140c143c001003061014000c94006c2c40c00301100340008280781040d41e25504030085040c850403080c0b458600124241001c0300e0111400340801800140c14010030700f80303000d07641d03002d000102d820954455487d0144200c420071100c1214803004406e25410280c80885800c0e42d001c0c5c0110b040c07200071105601c0380d0800d800340c6020300343e407100c5c0e0480c694101d00500085260061202c040c907040f030072021b001030f0741e0000c0540e2030340d20910b40140c9407014900180d40d0a000d0031281401091200308107948160124101c0b4400c2d0f03030a84a0038641680d511045080d23840b02d0140041e008001d04c8207100038200b0b41c3c0008200e03040c4900300e8440b800c5401500040344c3c0920b0b110800340d0445512007018100030030200c1020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 361592041 1250 361590791 361590793
    0x1080108010c0c0f020307050301140a11120f070e03190b0a0603080a11030f04122a0501050f04090203040602120f0601020d0305091e03090a0e011202041112040c0512 73
    0x1410b20108010808681000000d050000c111511410740d201081403002034480680200026140103d0841400c08200c0300c0015041c200350010343da4610030800d0741c0b0140c80c1510b11800c1a12040c0218000150080140003000404507101d60b0390354003000000c10030444d40d445000210000c0c00c0c205200100200320102681c109a0304000003403a80048a840700018900070150040c1c10b02402d0840c801c2007a44016640701003404905002c080341d8466502c2d200303210385040c604200701e5030142089000c10300d002d003103030b404800c100b1940504010f1030208030940e0140e103065141c038040000c907041942c003600e005501290024044072150007417500500c9031300003c00c4074500a00000d640da28440c04220405450320040f0b800301d42c00300015001c210701680f5426040c100c1002c3c0c5540c2c0e03040122101e00c2402141800244600c036540070f5810380e1407111110401c1d40058090002414a00705185048501000041e161490484403180664402d0f00000311451920041102801015080c2481 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 361593291 1250 361592041 361592051
    0xe130e0c040b030a020d050307290603011a090603030408070801020a110f10090201030219110d180b0307140412150b030c0103090203010204050d060b03060718181e09020108010801 79
    0x5143c3e400900c540c59240d04031071718400c404a52800500b50f0080c060020480c030007810340745014801404501d28406428425020b0560768841003509032200c0001718400c00e04820514085418103200700b6130301c9440501124034040d03580c54001d207004403541c0030030090f960100324110750661005403013215184c003500900341441e0101040d40c50b4000c58242c6c1c04903650300c1c400c450469000c2d0b0184c0b28620b46050440e4091031480001a155040f03118000c0000d01940c84880d80c4240900c98040203221040a0030001034145107401465907c044c00301c0c0c0c10b208500284480c4441e9480040c00a0303d00344194000c2c50103176242c0382c0111084072519001c4a410000460030b107407000196244039030000d280c04100100c840c00400d0081c8102c0e008181c03c02c18508400040c0700b0b007a04841038200050b02220929a2112004c030748450710b02880c41c821003501032080110300c0d2000442c036920184007800081c0041c4c4840243e00000e80301102441d0243c460381044203542c0c0201800d80140b00358802404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 361594541 1250 361593291 361593311
    0x609030206030c0c1c020c040f021908040204090f03021b0130110310051212030f10050a0e04120e09060103090510060e010f080c010509060a0e130e0c04 67
    0x18050000070800c1490f08404910180c120308104032200380b0034201d000c188825040348200944400c2c26190450245081c550000c01c48607081c030031900c0b80d01501115150141c82c04004172800e410182c0280e0748a030301c95031190302041050401d146a14402d800034104120044d501031032010f0805526418400f1140310802241c190807025207503022450044c1c50b40c81d003112114002805514148080c0001c040108090541641040c0056420480d2058002030303030000c03480d90324031b5040080300380e001040c004110500ca5000003181c1002040792400140c90312900810440c900c00e44c4603900050300314003400103000318080086a4204149007d4035214940b40101c0d1010301c0140c0442e04042e5140c0b140e00903c035041c4041105a100648284001030b611041c1c8001a40c2c00c6c00780024540d0f04440002d0b1140c40007502000b114410303100d1504040c280010012690000344500013030210b60380044407541e583d6000015604c90002000940d842000c65180c9403140f1049054002e0b071400c40304007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 361595791 1250 361594541 361594549
    0x3180a050c04090f05010501080f010b0d0804140d050f030a0e011722061d010b1002070302010c17030702160f061403070306170d0206220b0a0b1005040f06090302 71
    0x36625000c1c2c0300030448200310b1800d42582042d104000c0c06651034680085103588000c40c4000585640800a2000c042418100044001001d800070310092040004004105401c1c80710196040c00401c22104103540351030756801c1290250600440d5040002c1c0e182c076050304400781d42c46001d028685152160480d05518400400180c40403094409068480c086800c003400807040d541d5208009006113040381a41101c40c0000d005034160a50800043d4681070401500c8010382c03100d035a00070004030389583c0041d038583d0417494040d500301ca034880080740000c3c6400b00860040010790300038141c81f2002903240305103c2890304143c15400221504104050340300d4507071060b6004180201d40e5a031218441a00140303900c1d40403100c01491741e0800b01f5851800b0420340c0c0e03c00042d17005e440c03c90b80c0d0a007030328140c02000310301d01c0da421400104a42c003103011542025485100000002402c3c45400000380152420024581c0080d600180901c0f81072404041035004100a0030050340740390440c0c0c002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 361597041 1250 361595791 361595803
    0x3080f040f061b02041d010f050118020712030c0507020904080a0801080c030304030602031e07170a0b010801030609020a0b130807091103040b07090b0a031b09080c04020d11030c03180a05 82
    0x1900c01c2d622413246e41140e590301201203c1c0d035103a550080002844d009041806000248542d94030100d107610886907400a5008442d0250340c41440c00d88103140c9003030f0075002841888004004c2020604c40d0f9001611000d12a5005032300403040c0d1500c4070b4040400a055280580103800140c104032040c2c40c658900200340d40c00d5a600140158a0780d469888880c1080181c20030300850703901a00034080c406420490903050124644800750b03869030754405110503911081005030010f41a800100701241c41a130000102d144000d00e0aa2900d6540c00d15a50170b07008000c034802c02200030340c1c0800c140074040107068014085074501b401143c12803c010746250000400140014205a0026030406d10072605400a0403014600581b41c0110003401402842000400424100d03001082241180501940821508028003c02020405030240310103034104465401d00c242d1902a40f9800100c0280918800d080741310751b950f140d1410f00071143c0d0030b0020300d1008451750800e400c0c1801151011a075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 361598291 1250 361597041 361597043
    0x2306040603200117070305091e280c060923091513020a0203030a0b090f06040f14040f060c090e0109181a010305011104290403080f040f061b 62
    0xe030712103059281c401070b9000e13200c041016006034510001c010500c2c0d010360100f401094594100e4505142280070f441d1484125000c1200b03e40c0700010083c0200203103c0710030203500360010010030182c640c0c1e0f61248004c0c2c4076080712001c55442030b01448104c21400140014400c00560325100f0510b1030045814000701030b21540510500c440d0b007040c20b40ba404010102ca504070380c1c045556003075083e4020340301e800584401240d203003001109403441c548410150302420b10101c0c803d0260b101d8008010003801204c20042540c0e896419208a25a40c906c400c2e00c940d0188215070315000052a102088910380900b82c001e202100005200201f00c103490141521038000000131890724994041c41450000c0c0001401409070300c2504005568030425a412680718038000d011600301d0921280c005d003e00c0c00f80320b0020441440400846c0010000760b402240c40d01110703442c00e42c907620707011520b41c0042006800460f0025040002c0740c18469030b900105010702e1311010705076048801e20400070340020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 361599541 1250 361598291 361598333
    0x311040504151814010b180d0516120510050106052b230a0516051602030604080315030a02150d0b060c07050901171e0304092306040603 60
    0x7018075810010581407409810004580e00ca146070b0f040d001c002500402440d00144070003080009000040c40090350000100308944084d03041554040c0300681000340001e99030f600c900c200034007074054043c3c2c48001800d0119030b0b10503c5807403420418a0503900801c403100300f510703100040080c070b640711003980e41d0103500c02d500803d41e040065500c50903121300c40721180c809113090c0c107529060b0003900610b0018110b140a03884255558117043d021100f048031000709a2841104602c22580300c1c10003040600c0100203160090503241e00880d142a4088034106ca01610000510484018055003180c1901048004100001ca04d83c0400c041d400c1d010f144d80405407010400700d4203407146e03030015608000c024046036203400380301c0c401942c4d80791244075050103942400004941d00200c101b0703e040041071a4000c1020100d0100c1d240420f080001480c4a41d0105000202d4420f003180100c2e80a40c00c9101c00c441007030742480c2e26134400000940741a105074901442003001070340c40701c4501000c0400700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 361600791 1250 361599541 361599551
    0xa0305030702030403151a040c120209030a050d020d0215040206041703190f0f020118080703110604031205010611060403032423060c060c030606070b0403031b0311040504 75
    0x71805a14500907900010250851061407200c90807540e8403440d100522041d00340034806180c800d000031100f0300491840007400c0161102c1d4400520740040c803045c44050308032100528140c4a00c0d08180704048140010782104140d4817100d81c2c10000d08150b0030003810030304814289a4001441c0c0e01c5940b00e510b031115006440d1840400d41802507070b10f029507020311810780900305100188050301491091001c2090403c2d4041290320511413403040f4124000c2d48419003615032070300302d0260045a401c030108103850f03901607020b50040c031006005a10075114562221024071840080d5441600a00c0404c003840c948010b102000040c0d0ba6049901401d00007510b502100d200440d900840000401001070b29034000749403e417414051000d001d030862449204800f0400b00680c82c840c80000300403551004000c10750b000035650086804c0800100354a02e003404c980c3d42d00300b100504460643c08a645c54400e41031000001e46031100042441c9000c120741a5032003187c81c85d5010b24000c00f40900d540e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 361602041 1250 361600791 361600801
    0x1c0b060403050f07030528020d0f150203040507051206070804030315030c1a0a0504060509010e0d08031027090213050c0c46060c09080c0306090a030503 67
    0x1000032100075540200aaa112410100b08181c0e01c400c18807045590b80301c2c076201d18994004c500110031500b80782d01c07008054070f0b03038035000c203e00078100d10000d03030b10a1031105080002414203070801141c180820000340e1a0702d45400c040f42090a1035010901600c81074040301d032084408203a09510034054101075509454606040300101303100b1128100301c3c0c140007800310900c1031044e2030b002180c108645501955071190340b158114003034404010007240e001d2100f401418041d102900c4808810f14101080c1086000020401400103100f514091000002e0090744800a40400003911040a1500f200c41d030326802c0314a81c1c100d14951072042680d52240408541e00c80d070700703a4858041e500d01800103081c0808000b0180e88407044807045441034104424454450016183d9042c074082e0b5901c0703160741b02420700c10b100da190007032600d08000708081010000e106031044440150265030346802142c00c05c3e10151030002600b0905210b948402d0410561b003400040c3c0303002da03035454900a502ca0702c80b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 361603291 1250 361602041 361602049
    0x3091c0206090705030a322401150c0b09100204060e09070228080c060405060702070f03230f01060b0c0c0d15090201050d0921050307090605160212030912031c0b 71
    0x165000045150254028200c041e010208200123003044000a030400c80c0d80e242c15103042710301c10144400118803c819000c0c0420341c0003013802d40c00030054040d2680c1503801141c0d041241e1103600800003084035108071030002d060410156034032107001c2c0000c1140f0845000c6403540c201941c00700311850091450346100b040b5a007800c0d00c0d80803018108503110b07410a0f25180d6100c07102114413000520420b0b600244003100c845060048940080e00409100a04203088072132501c50070880700244109081c90004e4902442031030010701e05100940c6c1c0302c1c0c241071002c5003070030040c031613013481440c03201030f60000301340c00000d4524030410880780024004101d10040c0d0b030038007949001040311482c05c1196800d00ca81041039a00201000700e00c03000b0402d031402d00b52810b000594811001810310340042c0401800b45004000c4a0140d01c84405840c00c240c0c000f40407220702107030b8030342a6080030489034141d0401410f650074079502e04008e10f05010403c0c4401010007080c1c2e45101d80b40f42c44540781078084d19 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 361604541 1250 361603291 361603373
    0xc1409011e0509012603071e02150304060504060609020f18180921070b0a1a040e16050d051504081605030a02060906011a03091c0206090705030a 64
    0x74003000090342c0e41703248058000c01013070056100da400d4100e00c10800040401200c1403140e001d0160010403540b0390850b080408540812600079201301905030000d40b100020350b1050303200b4803005c40c03207181615140003a1880c0e0f600c0420003600501c4606e28030682e95007a00c28100d0300b03c4c0c405005141010008407003134001040860780107800070500141b0040451b0301400c2c0900004c04c3c0a045243c0d43c4174124900c0b80d400003500007440700340443c0e007640031a046032034142090342240d04902e400e1400202161813900c070f8a0260b91054812041010a61100b84020f14088400440710f60603510f5540d25602665545144044068005401c106045050302c2c0f10400142201030a84643e142c00c907980d41c0304840318005481040700282e000b0300002582410b030345007455003609007001c4c20601606500301600c07120700e03800340303c00c18101c5040b00c0728040c0c100c0c003040d801040fa030700b40f03d0303020703410300c5402e412450082d04600d2208010591740506190b07440400135000a4940c4161078030714241d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 361605791 1250 361604541 361604549
    0xf08040503041a0a081302060403060e0708060c04050307080f0a1506090c030506030606091510110a2d05070e1906061206050f0901030206070227040c1409011e 70
    0x12615581510400c000c04018001444490301e50100c07640b0350380000c804800001c20000e501010401c4103000103884e40d006041840340d4cc20841d45041d44590025041c020f08884150f614200450108001d10301008100007e02c04040078004d14020007985076112480341c1d038054004101d904001c2c402c04041ea100000401c99100c042000101c4440f00401401040e0f40f858400e1040101040c010700e0441003141c000c0207410100941c01e415041070046c4d1841840c40709007803208074214103103109000e1146504640c41b41c02c60030502070011600f20402004e51034804000c00c111070001d400110300007002000c2d1540300c0c0401f40c1655400903401c002080d1085101101402e0210000d0801d800414100c0c44406111782400120340701e105001140da08010801e6008107003000420250504100501d00a4005880740c0041c2000621b2040b84c003601d1a41103080c0b1808e8010082801010909440646410001e40c03151098074400955101810b0140e2010070f03040110702c112820400c03070040003c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 361607041 1250 361605791 361605809
    0x140a06230c03070305091608100f0b0315090102041a04030201020127110a08010f0e060106020a030e090a090c030803060112051e0c0c1005150102060c04090509030706050906040201030b0a05010f0804050304 90
    0x1d4507201d100781c031038420124418840d41040303420704440c032b02e03801001e00700e00c0068002c00b2400e02e03c0040c0704015401a1040c00702d95402c02010600000401d00c0d045048005112141c1c2c0d240380d44002800c603070104508412070701c0703d19454111441c000ca010012560003110342410181c140d000110040c07155804480c0e50341ca4003d00150700e02e01c0b5040502102d2201c026141903a0380d904090380c950f0402c01c00100020984000654245000304030725401958411000440d1a400c0d91096211181030b0001c0c1d0340c900c03010040052542c1c0c40341120302d8088402000f8880b505003500c0c141801d0440c02c000e88074030305040c400038170258085010b960210291600b00d6580030f10072a0807400411060358a52009040440c10243d0b550000400754010301007009054501890031003064010000a0460b0159000c100030000108000f4003070036005440c00b0001d400e49003071900c0050222625844203d001c1c5c0c8a09030108926a001300c1074981442c00b80c10410056680d91910074210b04c01c1c1e0f0821558 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 361608291 1250 361607041 361607083
    0x30a0327120302010c110d23041707180615050702190914010f0308030112050a02040f020a031b050901030f0204050d030503061201020f03040807140a06230c0307030509 74
    0x82c158150001c407800201e50311030312001c0441000c07694031890620007181c046100305081101e580c41c82100c1088d4203190f01280303403c043d1540c20760304c4080c0760500343c08602d500c141c10602c20604400c1e0181c1d8503800d01030080000c2441c007400040d468103101d0b944001e2060102e101c1d019925807083c5d840c2c0000010250f810b00c1a01c881002c402454101044000c01814400200e5800000c04200003640e40101c059400d6070302c2c10a019000000c40c1804646034000d016814006841d02e0040c50043c4005600c05130301c62a801ea801000c68003640300d0f41181841c0025088021600203080b250a8813007071802203080c2d200c450459000c0e108662040b0b0300200d10103034280a0603131140103103004050445600e2440141d922200303090f40580400010488420004100007a409800a00c11188584080000011290099070404500c102c09a401a80b2203110b02ca4030008001140070540360b0250140f0b0030b082c1184120038a010040105080c1580c91000c202001c4e010408110350204003901d82103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 361609541 1250 361608291 361608293
    0x24030501050106030c08090309040e1002031515090a1509030807050606090f041110200f0d170402040e030906070809090f060102153102090105030a032712 68
    0x40206070900c58070001910707000a010025100703a1485002c2c0c107404000713500303000700c40301000020a0103d54200e400e2040d524115406051030015501c95074500d4404412100000f0620030568261041094655400c020142550769040d6030101510721030403000300d05510380482a034491055400240c1142000f1648008114002405a219030402d544220300d40e1141400c50b818044c0548005040d40020140803c4905229141100130f802d1803400c40c1d0745800000e440f419600501c0a40010341c0c2100ba102140c03010200310181031064140b419403d095007014072000800806440244131300e460701d4004110b400100146da0001100070201503813881d1034901021981d21010185025462000c00210030b1040241610700c41c1206801a11450f030f500303640012101401441c008040c40c04c2090030380d240039441030900084902c1c031055031000585004100355840c0c164000c40c4250f012962500009601500301020708001d10710301c4c50300e4915100e40d1a0440507d4000c0e001c40c1c203035048040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 361610791 1250 361609541 361609543
    0x10614220f030c18020c060106050304020402210609160203090d060b150406120c0c020f0a080610030501060e060a051c0209071d0d030509060c010912021e0307030e04240305 76
    0x5002c81344510202c07031062100c4503519044e40108500c02041d6000000100074150280300116170080c4008c3c0010b10f4502c2015a03003640d10402c02c411100d10700c400c410050700d8108521550781112152410b00000544004002c5d600e02c10b42ca42d250007070751000c0d861010801580c0040c03a030500f00030b0401e0030032041000024816000380c0b15490005e0121120941d071200035105e20403440300b803a900d101018806400b40b01060340781680319504540241c400084a40b0240401c03406100d60583c0640483d1031410700c80d09441c060f803c007120a1810744240300340c59070b840c1a104101c403419a0320b0103003144051009040380e615010040e400a05d00c004108c0003030390100c41c00300314803880c0c000340f80c05c000c0c400f042c4004000c01c20401004200d0804c125011490500040d142101c05d0a0003c602c0700100d07661103200f0f503a100b8020004d41d01c00341c045101d010750302c41750b62400c3c40980b000318206445602e0083c0703081030580405005a03607661822449584261001180c80445145204c0c0741d90b803842c1407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 361612041 1250 361610791 361610813
    0x20f030709050708180a110d0501050405031b0106150c140706080712020a20010e0109110a050117070c0602040503010e0d02060a060609051002010b030d021005010614220f03 76
    0x40b07400280c18100045c404003000c805203241c3e5a00c90001c204c0760781c10f03507185c0680395101d0b0072007a40242d40e084210f0002e1800d00a45108030300c640040c54507a0b5004008800494200c5642031042e418990103103c0f4043c0146e41388000082e501e4110841004d908003440301419038031256001d4080c0c100042101500008420b0158280d40d88508003590844010070032400707003000000004a000c818070123050042d10365101c40c0c01450000082d503044602d00682101e002e42c40484210f00c0d0f02d00d8180c140d1400004520050800382030008020800400419000800034119030a0010380c00d002e8050001d140d0546010308006070082003002e2101286030380d1001451042c00c010310511000070008100e40c06502d00300c0714240c07a501409400c0004101410070740101a5045641c1c07421004020383e800c10030826006102e4001c3c01540e00c061180c070781901d105030000401e00c5070f80c29248181d0300c100411105a4403a80798500b2411480c140703404110b0204ea404000303020200b59002c01400019002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 361613291 1250 361612041 361612051
    0xc03020307050a031208071808100e01060317030c070609050610150f05250b100801140c2817010f08030405010f0912060605030f0622020f03070905 65
    0x1150601c980e620204180e006107804010640014041404411030080d100c01c6d802800504090b5942140100503211000d45607001d801c10303038402c3e10b01d04198500d83c0f0a025408822030024842d5904580740c01c0000c0c40b0000003c40c0c9a0030010008020b25074803c140c0318090f61007001407000340b02d18200380e41d58a40580e843c600d582c2020100041349142c2006414182c603003a10703000c0034103900340e8040d2800d811142c000c0001482501341c1d0655507584400c0d514007903102c2c417000303e21400c3c07010b8007803064050354100f8802c982c504031603000030380d241d126025030001180e10040c0c1c5d565007160301d00b15090783d82d901c031020026003082c5241c1c0241e04950040c010402c6999400403aa99844640341c0d164058404d074005031f04100010b0095521072080149507694504040600c44d5a600c01960a2031702c101080d80c4080e40d80d14244103e20b418850a842c1d03c421000030706890900307240108091705400c46280d46c0c071404030b010100b10b444980c1d009000820041c182c49119079034021000213001c2c1124 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 361614541 1250 361613291 361613293
    0x601110601050312090a090e0a0c0803040b040b03040f120e18040c03021002160609051002160b0309010b0402030c0a080702150106080a0b1c0201090b040513020702010c050a0c030203 80
    0x205640240000d800d8100c420007402000c0c0c0c001041d6460000341d1001000c6604621000d6000c602104207000d14521450140c0c000d200004d01c0b420701e00502900ca070001300f00b680041104201c001e000800f542c00b034076110948981d80b07844621b020303e0400f44840d401130030710070f42c1118000b1054001e08020641c0f4001e4548211000c240320601d14a03d00480d801080c40f07404007024405070520840210020240c0e00440d91306c0103840c0d90302c150340300307031035001c0700000d4020181444981000d544c00c0c0405041800148101800c40030605240f401e203014000381c00310007200040c405e1009400440642001600456490611060448903a8061890000401c84400101d4059840020085540302c203120b002040c0740d00304201183d01d1200988103c08080d1217400701e81c5681e948400e1140d13507100b0250400b983c00641c0c400540354480c10f51000c401070b0030a00c010030080d1107000d1a607404005010303005030307100700034070040e03c0b103020846d400b6103148581f00c90141000380b100108001e40e40214 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 361615791 1250 361614541 361614557
    0x10020904060302180126060c030a09020d150c0f051602060906070b0114030601081f140c070c0f18050604020f040b04060801080105042a0510090e01080f0303041707080d050601 77
    0x2036880e1b1018415040307a40c9150300050001e9409054507000d903400101c5600045805051600020010700840700c05441e01800403001c901c41800b103100341400403415007000d00301407503000c0002e803a5000d2255070958180c621042d170402c555940045940000d4001d00d0380b070b2511010304100b281290309000d56440600c00740c0c1c040c5170918002802e1412189075100030610361500c508900ca91780d10400c400101907890341c00143d403082018110a20510300b90340019100e00090621810030328280d0300c01052012945814005c85610203400d00302d44003e25404200c2c3c0d2100e0001c40d00a1248541683c038003c40481c0210b5100c2003500100102c95240e40d8210b2240d894000782d42c203e406c01d40d4001c10b0454001044500749030105409502c1852102c5000d205a0b501e0011400d41302c1c2003403005c0000340440d0000e000c04103080110038090201c010062907010500102140c2c1d03071001400160080c0c035881045100d040ca000e040b14074955024000036150041d102c1248040d020550342c41e40800e08079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 361617041 1250 361615791 361615829
    0x9030106080c0a030f060b03030703050904050a0501031e052a011404230303070b04060608190f080c030c030403111e03060606090d05010203040c05091305100209040603021801 77
    0x7180b03444400d00415031210245140d845041c042d8450000b203400c2034036000c080340c1c07a940501c003800d8894041e803070300d40c0d640002400300011504c0080c41c82d2107803494a001400032070801c0704403189010b039602d0041e000c54601e0a046280c130316940c0340302d144410000b0080d0f03426170f0300004884981600303072209082120304a10780041401036015400c1c41d031014043c100000c1c19101070001d03030382d2005000e99181840c252164880c55004076426148a51250f000308400c1c0c01c1000301e9045541d440041200b00c0c481941d4100c20714104140c0a090400041030f010031642c4203008031051a64044c045940d43e660b6480c04101c0c1a50303103507100303200380300d0030751918441c2060080311420352000402800255598904010854001041c0300360440c1e000d0b0b02100018109100460040d070041281440039441d0a04100b54520020f00050701010b2075a02e0000051000401340400d409800000d40c8a48080300421300801990f80041e43c040600801d40d60582075241a040c1a41e0042c0049491030600c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 361618291 1250 361617041 361617043
    0x15040e07091203140903032a0304140402090f130e0c04020a0203120c040b040e01080705010f020a060903120504080d06090b010e010c02040e0105040b0106031503030c0308040302010f050c0903010608 87
    0x494402c0055500c90b1442182c0040e10a01d4000000503c0c041060700b00400c00c0b01207807542c0c000107501d44420100440013440000e030103c008000c1c08294000b58a0141008200c0070403200f0300076464041d039004100c40060742d903035049003080c0000251110718500160a00c002c040d040a02c0c84030090b02544589101c141172074021110420f54680065151510300011200042c400901200f51b6500c24880030035031141c1d400041009005041d031041d01035040c801003a040c1119680701605000c41c6210f0003400c83d8010070481c56054121000081103c00342c14262031462900c0100c03040d87d850001004200180003014040300707951400100030742034450300c0203000c90f4680d40005022980e410f0402d5020340c030650011405a10103000450400001c800c6182540c200756022920350380c00d040180700b40d45d81442207a10010302202803640440c50b5882c058800c942300c0c103000d0100000c100000f018103000f5000b202101f035032140104003900d01070b902c4510300d4009465680c0f00303500703041e400205580 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 361619541 1250 361618291 361618307
    0x7030b06030c1c0f0c110102071703150619020c03070e0114040f020a03050103021302030606030c161a01050310110a0c03200d08090118020402130515040e07 69
    0x90180059156031240c403086003540e000a00e003a0910708075007840c0d9055035102c2c09803020a201c18000030911045c8164080c0060b213462143c4400e03a8818444603011400d143c0c000303152806480b07142c03076803501c034610401c0484042c1120b20b5040f060000e0504031400120305080c01c881c2c2591700303031501201890704260b1035504921640800b21400c5006000092800d13143c0d802e0500003c000140c1d03510798020580583c1c00010341d03070303009c240e40300010429401c0073b040c880c003c2c41ca400c41c110310318035140e030000d50980005484503440e46008116107024820745c01c14007114035001806c4c00c588111200002088030000d004281c020301540ca40b01047c1d030443d02443d5820840b8103120b034100005000102c034200c00a007c01d800b080310340040e455402c21a4407021181c450b10601500550307090390005480c204010384804441e80c584009030384646008003481070079541c110380150f0760760f140c004034244196198014950004040ca600300905ea00c240c0104110f45841c031802003207603690700b01500c040b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 361620791 1250 361619541 361619561
    0x1110d0b030604020306070e030a150203010f0b03070903320d0e030d0804020d0317010e060301050c0a020d211a03010e0f070315020d1b0914060d0e070e040f06050703 73
    0x80c1c804030107d1070703280c000e03c9803190301c400240c215840c541c0d00791240310300361041e50100399174994004014460303290303400c0c0041c001c1d0140480741440c50604000060805403240b00203404a517960000318000d446000301c41e4001943e8107400000c3e00043c418064403822050158000321b1b00b041e0b2521581d0134007160501c602c1d8013585460495aa0320b40900c4210340200790b0403001c11622158444104a4107003210340a000d04403850b04c3d45181a8092500f1550081c1c8400b00060040c000c00e86a503078001050500d55001d4034148402da1791030451030904280c8425158030440c00c1ca0390b021080d070200a0304022504045009102180582e12999201c0d00c190100b4101c0750031000e014400700b40c2102c00710a202ca03807000014074107804005403404564990500c0c040e4050120f9485030031580c88070240029203118031500d00d00690301c5002030344601c100c041c020a025242d0995403090b02c0103001080041000007082845031915107084c07440365000710003c8552030701d803a0204444620a1261410742 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 361622041 1250 361620791 361620793
    0xa050d023606040515070605090d0f0804080403201f0215010302060a0f0c0206070f2a091a06030a09150b09011a0d060e06040e03031515040801110d0b0306040203 71
    0x3401c03c0c085c0f0036014001e1340d080107412001c00200002a0031403103094821140c48000d400c51902c5070100402e10380d1090b007143c0070040304406020200780400f040f60220780d48401e8500c0140714280602c00040304117009503501c540c1e2001c445400d2010110200c03801d200c40c2d42922850b007440007549904420030300010b50404400e00c003481c049801482240590651824030038042a8568005020b075440104100c1d09e190702e82d9090410000c1c6010a80020b0001c0000c000d0700e00861300211540041901c10180c0d09910340080080c80c6443d0400045060b4028210f25030ba40b800410b401e024011310501120f2040e140350011511020078442c640d8400030040114440380d00e001c22440ca0888020a940c5c2c07141e104004407020756001c3e00c182c000074041d42c003c42140d0719100080001b00c540b030000702c1405030020410000074030b9042a818550350805c841d500c000000c3c004d220050b43c0500e40080110750701c1c00f604c7d03090400c8064003802d82115103030030500010384000b0515440740802d480081d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 361623291 1250 361622041 361622047
    0xb251b1427060d0c03050a12030504110405060105071a1803070c2c0901050912090f091003080c0a12110606011101020f04060c060c080403080c0a050d023606 69
    0x740050090100390040d100800074000045513840b0b00d1040c202c2d5910445041d0300c039007400001c0000c11014408440a41c3c1420015840d040c0c07240000441c0c82400070b07100c0c968401c0041e03416130045094584860300301d00c001101882d01016243e001400b541c490445044c485a0710080391400801ca48445901c0b03aa0000723220b03d043c0c4100040c10001001030055000c06c0040010509005a484c1c8030301080c00001c1120f0526030560781c1010b816901100d071612003000b44041c69210304150b011038103419035201109039212544031145011a8100401e62000000d078115042000645040b1040c001c6070484800c44000d14291248003c2001c5d82c004c0d83c2020340006c40c5507001e4001f03210700703038078240c0003518202480c0401855a03209800c80408100107901540034070100b881540a2507000e82441e02d03450525403009070074020001c212103001140000c10106880c0b082c8180c80985942c40420741d1286c20a45070300012a41100304040b40d2074040350717540303191942e84040c1048204040c0410345 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 361624541 1250 361623291 361623349
    0x70b04061d04090f0b060909070303050d0f021215041a01030902040603060204060201090c080604050c100504030209011710200c0106030c240201060b251b14 69
    0x141141d0303440e00030036601070004460403292102d010355000e80344200030051a0124038600915440c001910b09801455960208016007800146000580f9010308002d515001040300d1070001d402d181541030b03481030002c1842010340c40e0180b04140140c24084024100342c075181c041c03008481c180c001c450f06003c180d004c07840644d4000c0d8801150140041d1011455646a8460b2303400d07070703100380d0180d40142e548801403824000103058410160086d17030b0190025092a1301c54994542a05241c64443c0d1810070b103c10010307000b07004980081d41d004d000140d080da90b4840f1030440301226022104180200102000c0da41100e114280f4a0080c802245480003030302e254540c265008a40d60081c01d40d071304c000c080007140c0d004000030300a2100e950b82e40302107000d10481d903070255007444401055a042c080107000126224041e1428220361000e00d00501e00c02c424401124103800c1006400b4040305480e00b2074014101d1491000d5035019240c112070000b032241400848202c60464901049201c07a01c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 361625791 1250 361624541 361624547
    0x304050a030309110411031005061e0906040315050403140a0c14010609020d05010f0501110705010318061a0f01020c03060112060618150b07200102070b0a080a0e070b0406 75
    0x60310b15030007002c100306410b81d403902013000c46d00030f83e200307880d220b03000300c100090b00da100f0908001501050f00c1c0300d400d110711240e81070140301e00c5a041000074400800c0100440e100c1c5030560f00103640104443c142c3e803039508c2410b00280304c19a81500021364082000101c001001c00719400300d1840c0da909134490b0425102c0482d034031241568200c055403995000900d291242c00905011041007200040c9545044c0c3c10781049000c0f0792001d418041e1881c51075244030350210f402022101c007800e001c203020752070500c000242c4521040040090307240c074120406180810b11680c0b80c01e401550f0120187c80040e0040e0390f0354401c003102e26410f500400041c0550038231901c0002d281c9110f0000880c07161384078400d245c00c41e58800080d14100e5070303c400b142c80040c0040f4a0500400304400c40e2864011a521403c0200c80c1c50350f2000340f20215011a10800c0c0d200304200c1d4000c3c40b829002546618094030001c103600415200c416819003805a001d802100c04141c1c80c0440b02051801850680740000507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 361627041 1250 361625791 361625801
    0xc08030f190923010606090909050102090a0306140c0f091e0307060206090d0923010c150906050105100503060d1109010e0a0e0105040c0603020c010902190315020304050a0303 77
    0x8040c03544840d19440a45088a00582c803805124800c8071410300ea20040c2002806040b0840702002d038103203401088800c1e00031000c94140c403d202c401060342e60090400030b000e403055024580e0403908a80c800028445281d2040804000380500c4541640716850b000c1e0250289810b200c440c21703402c0040152600c2c1c03032458070b0100004055441c0e00c1c9a64440042d040c00c0b00ba92180d4050381290017004521103050243c2c0d000c2c25103909140c0d00380c6091510003510601905103041c81c00148928040c0035a01900200600551194100d280c042c030251800d4050030414070300316203030360500001042e2498201c90510300100301d07986031070450b501c9000700685000d2109013607843c0074182400000548908516034082c080c498400706041c02c100c83c010301260401c0c006107025900d8041440009a000c80140d0200c440314500036890350900341c2240d0041c800c00c04002d5100c140e210405008481c4191a20112801000e10784031055680403d00e090340720440d8003c006412a5035042e00203800b035840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 361628291 1250 361627041 361627051
    0x6170c13020717040f0612020307020705010e041b050a110703020f010302031305010608010c09120b0a020f0d1817070305030f15030a0303091e0206040306020c0a021c050601060c08030f 81
    0x41003820000d450203400e550300c0380d0450001603805400510085810180b847c48001c0341d030004503d503150000340251625043c0c0142c6040008510034400150b480c1c0d017203440c00c8c1036041e6103110010b406040250466002a001d0400b142c20010900540326002c107400046a4014080b1440306401d04011002584010250904000c0c00c11456010a0342445144041c114041c00001d1403403050802800c0f04282d5803002c02011641c0c1d00c104005880c040e80ca030341011038100c0168558580c15800c01160180c840359599881c40c0c0080d01031032150901c0041501d90107403070450449100009000b440b031040b640c0182c04920100041000c182001071072130b62000b100712a42d1041c480040000e0301300b031100a0280c0002c0c0d1500300a10510180700017a4509821011212140c24040e5003c40c02c240901d10020b41404d40c00328103400d01c00c0301031024003c210340c014a05641d0b0000c0203002c13255260601415901882490008503420780038011250005400991841c00c50343d82400c00101038600800c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 361629541 1250 361628291 361628303
    0x40b0d021b12030402040b04020c0307031805120c0a092a091a070b0c0301270e150a05010b030105150703030b0618090c1201171204060306170c130207 66
    0x1240d40c0e15000500041410000325100b2907070303e051070f0040000380c541c60400503100707901c104450846004008104d0f8100c95050405090700306d00181d02010058107030703104030b40008090301e100c1e443e81008640c14107118030803213080c0500d540720300d651411289022040000307900d42c001d4482000b0694070303910001201e1442c2c031b00c140c03a0b100c03801d450302c4d42c4000c10805d4003010049400700810200c90308640d4001540c031041130540d8034000343c0800c6141480421214907007001051052102c264100c00d4194442508071000c28508504003080071704201e992110703035817a180021600d040c001d81183c0c1241c83c02815481c070000c0741c2089401544c4500b50803000d1656a0501094544074030000e026103078100c0c1041503251540f0801d00c6440e102c000d0151030015000c001042c0d0b09030042c1d003c07605584a0010715540690300e003800700d02e0705125041561300d6003c08070340080d074554140c0000d41540c00910031307400111940043c4581d110003034615554401c5045a2600451038158003a1802e5405a4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 361630791 1250 361629541 361629577
    0x624082806031a130f06060b1206010318050c060c030705031803100506010807050d0b130e0c011716050408060a02030105041a0315060d1e1b0b070f15020a110d05040b0d02 75
    0x103c0500c01548101400410051427008001117981c042c441e03040b2600c1042d107424208000d99981644036002c4504051041c0f9000c10700c801c41d00c4042040c0c4032001d03440340840c2d40d2401c000303141c40001c2248000e424401d100300044880d0381c1445001c1c0328026801a104c0744829110040305551a40208a00c40202d41da5108691500d640b03500c8618a00c400014000500200c2d4440a5040c8000c46500c2410301c0f000417056044440ca540942c3d5101106503528005882104800c0f00d051091764400c558174031500c405e024540c003440e40154101c03181283c040240010361420030042d101c11a554580c1600b021f80d6080c0e0024084680d191721400040c001a0350005036030340d00300c078404032182440a40e04801c001d1410414034110701d680381d044400c0e00307108032031a200d1544520701c40c696000348110003c071107840070400d07801028aa50301d00c0140541d00d80e184810300a103404089850030256114041c240307500540290101c0b01a1601e00800526007400207650f83d020303600407100c0e514510011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 361632041 1250 361630791 361630799
    0x7030c0b0a020a300c02030105090c011b061e020423010e01030506120706020a05062208070203030d0203041a0a020906070605060a09020a090602010624082806031a130f0606 76
    0x71306281442c41840e900c0b11484011280141030071240000d0000c1c0da02c1d80065105440350b0707000f8050020719540c8490f0b1203004c148074a403010161061058565460f01c000804a007815460740242040c3c0d503200c8143c1d010303880e030707041081d00740540001d0752408a2000507044e40203520a800c4140c2c00000500911400348490785103500e45050b40d800440141c00c500d07828000c0181c284841d036000f81d0b081041c891442c1000c400030090300d030a580000d140d080005039035030031901d090081d261480740140c0c04540300d20b014105071010650300e2180e480700401c8080003400416044c820350b00700386030240042c1e0030100540e5a541c000d00c070140140e0b40c0301c03440d660300041e0311210740002c102d400c0890b40c84c020000d15120010703080d0707012508500b546405501075515400080300c4050440000c0349800c07a056100c5810340c4e509030904600c0c03010f00481004064881c0800e43e00800700b224407802d00300e40d481d00c14600a945594040e50114400310200c0c00990125a403501c0003141180111000581d05030750b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 361633291 1250 361632041 361632113
    0x6061206120616120506030c060307031b090302040e060f0c07020409080705031e040321110d050301140a0302090f06122a060c0607050c01020c0f07030c0b0a020a 71
    0x704482d0644010b40c1032990b80c2d03c19a001c0d004c003080c0c10816078144050300b000c1d00000d40706e403244d00711503004007030200002d0b4846219801c15038404140002068030390b01c52100c001c281202d1030005138040ca09000001110310382c0021050b20940e40c02611400c02d4464150820343d951040ca4180da04c0360326a0340c48004143d09030001c003001c1e03102c1c4d8015999524295140c031130124a075800400031300d6080c0401c002181c50354040d0240d1010b02e81e84116030050424060314041003081c4180c0c101e115900f240c0c0b0f4800d400c1802141a503544010074032103000340d00c00b040802c1482e80402034001850a01041d078880201e03c0300c540000e4001c1011070700084417206c9502d0101860741ca810042d008101c03140040980c4120384201240030f598403445c02c0c441c0401c60760f0b1580003070014020054000707120b1000c0d400a6050342c2d44102c0802c15201800a4424100d82e00c01d0b4a002c00d8460304884400003401100c00f0b001c83d120300419801424005e070f00364990003151000a40e1a441c024860701d500020864 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 361634541 1250 361633291 361633303
    0xd171510020a0c0f030203151e04021807110c040608150714070605160311180307090e0708010c0908060a05040201140301090c030c0e030717010e06070503070f0302030606120612 78
    0xa22904030135441c03560042518020364984000385544510080c043c00b500d16440e1202c0d000b24001d0400303115210b42c40440e8181c00500720720160f10356250b0601190302da00030811020304a20303008962151500c24100300484425101d0a0001e900104c1e816200d600e07080001544100c040c02c02c1007400b0201c60070490341f60300a210449040b5541e50801215030f44510685a03070440350300c1c04006400c000c180da8840b81c030503652100380044040d0052100c582d400c01000f4058158014248080f10719804465aa40d206006084140d42400d8031090114810355001040320f44d05002081103440b858802d500400c4013800030307070401016405000c0c0c840d501100460080110510008602c007000320020121020b8450b4241008001c01007200e00e60341c00111001514011508201525810300c10607004041b5420f9004403401030f032040010254100c1d01035803169065840d40305000000d600d08400300e10080313079015400300043c01072030540c01000181e00d0b4005001b0f4000340980c00d400030440c6c0307030007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 361635791 1250 361634541 361634549
    0x1504051806090f010c02030901050409021303021201090201031119120906090c141e041a03100b1011100f0b0306010933060804050a0c03050d171510020a0c 68
    0x142c003001d1886100c110034880d0800b481c5d52480903500704003808000030300621480c460408125000f0550b080106014414a0700841d40200108440381c584060f00f0301034101075909902103440c00d02070a14140101084880c48400c49103c0c652400f0b1102d401d0354036500b90260340e243c0b5981c40700c01000040350703441a0988030b40968501805185040141c45c0c04054042d01907014010010314400740d1038103840008450f150403200420308000d0281c05000c40c0c0d4130421307111b5040c402e1075a10b20717201c66541e201806081e800c1e00c003185000c01e00c900039114903c0113264080641e0244140c07190300507040d40400700f0b130420004082107510408000924108003030700242c030419500c51080c0c00c24a000c8681405002803034050752120118030004024915440c402c0d40140482080014101300080c09030007402584200c0c0000c801d41c0700d08010f5540c00e051030f0302e4070100302442907411051000043d13071840b4092600c45040400c00c2c030414807200b252121000c0342944a081041e1380020000c2012201070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 361637041 1250 361635791 361635793
    0xb0703081f03030c06050606090d02100c0204060e01050f09100510091e0f060e0612060d0f0b04060b0607050a030e060d020a05130504050702030a080408120f040b0f150405180609 78
    0x1c814581450800c1b02c002034a614031035002002030780b00703a844000e010303100a50125504240790301490300c29079201804180084d440380c0307004c50226405042c0c00b102410b8078401d950110340001c00328288000010144c50055001a1280e4100418903041d2005003101c0041c1c41c14114003981c1d40b10414142904440100461005035002e03c0350b82c1c1c1c2401d821008092514001c11180c21030404078100340b2440d05207520308408040000c0ca55120f1000200c1401e50003603031000c210607e13040c640c5501d1819501111078a04080d151501d03450101300742c40a82e0303000809401505a140c0d1300b0b07102052071500305600a00d0903c00c0c294441458070140c0071540d0203840e030543d41d10644903444e1004020790401e42c801c610b06414003e078141c4c00000d550341c03401c41d41070421594075030341000e00203401101c00c256100e100003410080f80d000804000d6005a03c24809810180c68087c50b8800c0722404441e4100c05410902581d050b51030a40c1000e5004030072284440c0382c490600d4003a03800c2900480c1e05600c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 361638291 1250 361637041 361637057
    0x405040f0504051c0507030e0f0a03080d140103080a030b0f1906020f03070803070503100806010605070b1e0712090c03030203091504050a0302060702030129031002040b0703081f0303 80
    0x184074081c881c80b0280107400343c000140d04c0800001525900400b0400b8080122145031098a43c8075099090b803100b00040c401c9810a41c2d80c0f821420703551015480100d040d08000f402c1e100406485032150507241d0000ca403d05018001500b280108a0780341da19030300000700c40d03d000c82c0c0d4856603007008020b607023071b2080c0c0d402900381880603240200081d44010705a1003040b140d80414000e00a0b00e8100450745499031356a2039010b1800c0143c0511340040c40140100e000000358581c00c0b41c007c002c41442001c5424560b940c940c1049100811451060300490043c00002d030750307500c15100080303145d034078000c00500245291503020882c4159002100544e000060000c0f89260041d0b4a00c84d03001e00c200712500c4c280c1000d002ca10340f580380d8807000340100707004104034045583c20b4102d003c01210f080031141585c03100309200c4500d40d241c41faa03240070b4003424018007001883ea008a40540d04480b80140c9000c00e02d607400c9409000c01004013540e404040d040e0810b0709842c46540f4002c6000e0364440313070307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 361639541 1250 361638291 361638293
    0x170723030907081507030b010c06020309010c0816141e07060e0c031b0d1401150303030f0903050906031b04030b0a060f0509160e04020a02031c060308030f0c0405040f0504 75
    0x12500c0b90541100c0c0580d07000684030a507601162484a520441901d0085000815540140c0300010484030050110303001100300554088150320181d102e4495941b00b01c8143c5a0341c00505d841e41c0b4409020700016020f2840000385d1080138021710850b640c150100e0380d5a4800d210560b0300360802074080300c034907445a4202c0725000c1d0400c0300908125017100685000d000807003000c6044002200d5141c000d09030982c4020a2041c80300c60320b001001000000c0c8500c401c4090300d440c0c5282c4900045021070b281215004403a400c2c0d200340d074011541900c0e034030b191004540c10003001c1d0704000c0c46220107140d0009801d402d90a480040c000a501c907000c40030f070f5401e020380ea0005840d50b940020150b540a01010071640c6d5502d01103a401070040e4031401100080700400b283ca9030003040c0ca4940007800003038003068aa900100800458965410348a0044034801612043e80d83c0c034400581000b00a2020880b074804100303840d40c11403214003074075140c87e0b60f60020500b583c0400f042c0902c002d03601c0007000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 361640791 1250 361639541 361639543
    0x5010801050a020c0703030f020c0a140307080f1203130503070c030309091a040f06080715020105010819080d06030b0f0f0f040206030c160c080a051605011707230309 73
    0x2608490b40000540c1011600444240c4e594901d04c00075082003911034404505500078084000014000340100c02d142e51988600c0568040031060b00740648144000021541c00114003034007195245400303084001e070151811992500301405403003c0580ba0081c0c400040c100300001c0c2407980c81034140386039191560601900d42001035101c0c01d0349506007070076250301281d906404818500f003210001100949040381d54000e2449401400e5107200303102011808442d800b08503403041205d50300a002c41ea0722440c404e5200c804091102101d2041c221006002940100140040440e120350029056a4988a4495048041e680c1200b803100090a00030603000014030b0f60307448865100d503120ba0341030642c042402d51200802000440d640403d5054540720885104a511900080ca080e10951034103542d6490300050300e01121140304100e502100c2c0300b000301000c000c8800584960f8aa880c030f80094507001e50300180b0400400c140c032040009420500c088500e0404008800d40d501c81c60081c17612 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 361642041 1250 361640791 361640801
    0xa030618021c020d1803080117071202151e18100f11010b04020c0105070e10020c010302032701140615160212030a1814090f060112020d05010801 64
    0x90103016004124490103005515080c2112036000d030760050740c0b80024440b40c0000c3c00201044802c0030180401c000c02c1c55030060105042e02d21f428070002c0c040c0309100e20603075110704512401410305540c401980161500c10040d501c2a0071b0381d5412860031001244001e40420b200341c000142d207502017810550050210b0040134013600c180c84141c02c0700c28154000d4007046031141c2c000d080080300480a60440801e41291031100409013003551500051071045000c1e0000302d0ba21f80020700d261044070054036011403141d0780559140c001c0c1035644002c80c0110040d40c001000740a188907019079940b400b40786500100903c2e012940005403081554103c0d02d02640040c00052103540b81c000c10b4449070704a5401c076400701251107000000340280e8802b16840b6102c0b044803120322300002c540090199000f1081c5007045c648070b11000000b03a00c0d80c44003d01c04214080b09500103d40d000018400c1a440e80502d4001030141024010604906111700c07d0b40d01c25a203007007100352560010880c08100340a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 361643291 1250 361642041 361642079
    0x60a05071211240a0e0708010f090b0c032202010e09090c010906030b031f11030f0f01050102060c09060a0e0306011e0f05060f030a020d050103060501080f0d080115140a0306 76
    0xc000034001203455500c0c0035040140011001c559605c2580032204c20401c004401041d45d80c0082c0300464000090900619585400751450540000084c000e108142c044901c00c1d540714000e4071315045032001d10320700000e034180308905000c0300f030b02c2d02096070307446c6440309109607007250040c00c418291100040000540f1340c00007081c1420300400506560f00811030014000034001c0ca0003800702c4000c0e81e0740c060561400540305180e0700005100411640c0c5011718412203015107160000c3e681c07200126502d207000c88010b180c03140c051043c482545860300042550807200e1070800b03003c6042c0c03000a03080c080300380d01440040e040280c40b00300c0314100c1c102d5000200030364040d90311031a2074000400d40c94403131045103004c071881c0040064030042c180c1d03040e6846103032007141c100306968480ca05000244406e00640307002e031003060102c140f042c02c0024580b0407220310341e58414041e481c01c40c803c0d581c4480d44100405008010050b03103505010400a041c02e100035680114806240c2800c000348252080e0b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 361644541 1250 361643291 361643323
    0x503040b0d1b090611070b1306020f0a03080105061c060b0a030b0103050c04050d08040e0106020c152820060103020a08030703141606091506061b02060a05071211 71
    0x3142c1403640e500560400c007140c00c9810300140d8100b002005509002c4182c100031092540404e8510b051425000c0345805d40d444d907000c468100c00d01e9801e02e541c803070258000800003198100107020030304040d0094519100b8800d403144401c0e1110a18000b640c069810000d0007403000305414040542c1030240c000c120000303090400c0141400303000b02c0400c0c411405201c0c0183c186061700b00c10410007000315001044c06134221510f83d40c41c0c520080d200d010b248103640c41944c03004500300c2101d190608480207001c000c50b0b01c190303000d051104515818413003d801014015000c0310110040040314125170b403000c1c414083c03c820360440c030400420214541000303000307a005001c1a0700094112800f00340c040c48012085844503141d10034010f0182c00d46800401d4241007201ca40c040002c0260303600441e005072502030054903124a011a50850501118000308040075215405070424800420702c0481f64031300703240b402c8216103d52122501c075015000c0000c0744411200c0e45c9041c00e010085201c0c03035900c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 361645791 1250 361644541 361644581
    0x20405060d030c11010513060504030b2521020409060f0e070f2a03030504030e06031b0306190e0f01090207022b0c090c0206090d0206040b040f0503040b0d 68
    0xa02c0c020180d21121000405041c0c0704550201c9a80c011340c10740da0105841c485401c0003030f44924004045422600c0100c0d80c9140c02c1d07002c030303810010601e0740b1910001c582c0c8058582c44900c407000c03114070585080c104880540b1121154171a44c8074001080600003080c0c002c541035203020043d81110401c1e83c003007011002c1c001e0602c004503074850800e00c0307500c8040c90100f21461079120550400d2200f02e140344d403001c07102c8410030100b5805801c00f5204074000d403070750790381c01d028101803044a02c01151100c1a42101941583c0b4181d40340c406583c003c0307400f030700c414010640305412246078400ad03001b80030303010200c0f410404010f6441407880d01414082e00150304219065020a020520081c481614019512070030462408201e501c2440d09801810b40d0f040a43c0d1040381100410320a54480c00500841c030004d201c80c400000d14030f08080c159401040380d40d03200d8076110600840504200d408070310f04154000441e02c104083c0c07020304240c1c0c0c981c03a50b07940004001e03011100b00c0000148500c01300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 361647041 1250 361645791 361645793
    0x20a0828080d05011508090f07090c1416120e090c03060102010905011a040b0a0b0f03100b04090c1205040f020f040207020301021b0618100b04020408010c020604020405060d 76
    0x2460003449030144586811003000180e1030800c1c650702a66014121091502d4000110fa410280c6064140c0e9001c1d19001c440d03440d0784200903140c12101401c121135034020f60040210140c5944115543c48181c5024901c0b00c240c24061621076003c0745012a041451101c10350500c580c14500517601002410f1250300c60000d00041401f0340780c0103240c03120410000c030014035164000e401010300d0f940e002008101d00004181d01d041c01480000219010b44d2411130410303034900b031074032a02c0141e9400300c82c0e075400d220b0520740281040d400201168010300b1180b000060102c6014060b0024207601c2c140440e5090312000020b01042c442460041824106814400442c44d0040100e40d80783c0c0565903800010003900100e0064032a2080c02034241d0f10004000c504004049285c0c80744000d01c2c001e41e0b0403511818400442504050b02855260b00300018848480c803207544040c06100014002504040d95050a9401c40d010322804001680000080008614042c41100d6100718101c42c02d5a0400075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 361648291 1250 361647041 361647073
    0x40c0f060e040207080d0c09090b0f090c03040f1a010603150501050712020106211202120d0b1807020606100201060f0506030a0b030a0503070b101d060406080708010603020a08 77
    0x364100707400385500007104802d00045a080792035001c014142400300c1c0e803a44c50001c00e072041ca0b20a40d01140c0c90070061100d00d141820035680074031001468001c0d140c680b005401c1c241e61020303108030380c42031440200100054030002040c4103c0a440b05411540d85410009400e41e485500c1000c0680340c207400901c090781c2c2160a03100700382e401c584131101840f00b0040aa00511403038100b07000782c640c074400f080c12055021041701c1c02ca0b80b24020364030031203c9403e02680c0e84c201011040071448400c0c403802001e40c89540c002d07241c0c840010006110010340451800d9078010645030704c03006070448020010f0358105800c0c1012042c04520082040900d4006441c541010350f01410f40728000000204142c41700c142c01446442000600b903511500e00c0d440d1095403039020041c01c0740c5031400c020014a016480310107a2088035a124481d01400c900441280c00020700101460361042ea04c0d0000b08081004008003406003828800000c0c4040c114010072040c084070754403010141d4880c8010403013102c1c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 361649541 1250 361648291 361648307
    0x906100b0403060510240201060e0708010302241605190c141906020c090f040b18240118060f050904020612040312060503010b09070f091d040c0f06 65
    0x80c1201001a030340c2c031030903420030710982c040e030045c05003c01c0301c43d01c1040800408001c000c8031403d0380080050580e504d46402562b03800312400004a00c840e0010009410048560b425105810071044440b0b411754045084a8001c0803581e504c00c40c0000b602410005e0801c01c0350a2041448e20034400d21095684001000505008007005103082e009503481c2a00c401c449400c0c0c80c0f80308002e901710503441d44802581c2c0c102c801e01080c8180d0300300000c51028107040c002140902d80210903000c1c1c0b913a1308258289811110381da80560340c42240d003e2490204101b0602241d4180c01031810059450915440304034250002503140040c40c0040c100134040100b00c001c003c0301d0069814400d45d41d07603400015681d0154100c0c8022482c2c42e0400c03c0201580506094000c080c9010700b040704684800908d800ca41d40c038014940c01400110200f200030b8018411303006a03040c60301d4004000c0b80c030f80e007840711031840041c03a00320080c01110611040200101d00c08002d03003100300803842c4e15480c014000305080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 361650791 1250 361649541 361649543
    0x9040201050a020c0303040308190c081608071a0f060f03060609060f0607050d0f03060e060f0f0d03110607022b050f0a0206040201030f0e0d03050c04030c0e0906100b0403 75
    0x1c4030008240345268004e11889807544c030010260381c1c46640e80e00380000203034000d5070b87c100b00041041000c00000e0261b40c100810f2600858003505108864050445c0c03003204c45426109200248214400110f0154034000100100d5003100911700304518000d290803000fa12a0380f02e07183c0345040711429200010000d41c00031049031102503c1d12003001042e003401540e030655030881c2d00002c600046c4040003481030b4000c070043d500c924910303140d44812001c6810b64010503d8003160040400c0143c81c01c49140ca078a91002032540d0b1a078203a40c00000c0148101000460100d0010300c6443c4101c9400d0003515480344c2c281c00900315107a002c1929056172010140c0d40c1360865810040c1e070f41c1d1079115005072065217100084075a40c4400804019613100003c0390f0890000b4100080100a5103042c015603404040410040c0912900300c2d01c10f802a04000f00708440c1c90400303006c00030210b41540f042c20000c1ca41200910b00130f040441d0050304001c40204840c0454094a004006c0d1012080031a0112 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 361652041 1250 361650791 361650797
    0x8011808030c0c0111190e01120b0102071e030510021e0304030c06090b061309330c030b1c03020a1e02040608070501200613050a080f0706060605030609040201 70
    0x1c0d5903020030440c0c1500800c40ca080c015841c2120821444003400002c0c00c500306031a0b008282c184070380c0030803103107000844025400a04406006140300c80d00e60001241d10405005481d01c65495a003280c01c1c032107000749400d00c0520031030f00400a00c1814000741001e50702c042e005518004143c2e21004c041c000200519800d20310010014007454070a60000404650008083c04410194108451260b00c1074900b07522416004e421185186854424400e5440d4004410045c40c04e002c03c1d0603081c5050724003000c1000c1104c11644021b0480c9116901c00300983d910700090f01c44042c4240301c41c1c0e0148410300300d603c0580941580c0800c0e00011211540f5078040044422551580011106030021403402074000c0d08151010441402c08105030044d84c0c3c0aa03605201215401d65480c1703407420301a001003058010201050390680d404000c02c017044e014900311080885a0b658191460740300742100003a400b008030f5100c003002103500401004180c685400c50450a1103400600b000202620080c14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 361653291 1250 361652041 361652047
    0x1505060306180a02040509070528110111030708160c020f041803020c03102906070c0b18120613020a1505030414070f0314030412050309040608011808 66
    0x690312070182c114020b03040d080400c0706061003603074400a9001070081d148a0b0400c0c000081ca114803400c10f540c81c030b41c0d6904050020b80701c0400c010a418800c600080c1c10009220342040c44000e00340107001d40110401c0d0001d5607450300d400010500c2030060725074003108a4440700c000c0640e91108030246403540450b040c0e0382d55000080040c000340041c0900b42c0d1075410a944100515402152101c62884107405450302c44075a060044101c5040c40d1185600380038040240b4165955680c040c03c803014054542031401c080c51700c50b20050022030707200103101c1c5030000e00343d40b654440199600c5c07110000d95080701d103204481402600c40c0f00040c0a1541d691b030419145095650b0f11203000000c190910300c0b6480da21000340000d020754400c9a09480344020b07010000042d102c00181c075011101090550300010341180e07901d440600c041d400400d41e0748800d102c0400c054568140542c5038512440c0110f80d600482000e210990340954030400c001e900d000d03082d03104554182000c0007900d52005103259 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 361654541 1250 361653291 361653301
    0x905030718020706110c0c150d0908070602031f0503030301060e300102130503160e07020f011d0f0c060409020a030f0903050c07080d1d1807120b030115050603 70
    0x8003d0060003809000346003030a41d0074164004803002400031440050070703981041d9402051060750032944030503c0c52a24104950610f61582c2e42c042e404142c070541c0074038030380b0000703841b500182e0700700b0b0310340c181c40d03030030a001a4500303400d01e486000c000e100690240d8155850040054071100000f18454000c0c5800c0140f01d43c815082c21200680c400b408200c11038469011120500035000300b50840e8542b010820085040d2038002260b4000e403000400c01d12245007040083c0480c240c01400e404154443c040c3c11064031035003801138a5007562b0254100e003084542044a40c9450710981e4890f075107400c907032820505a103a0f6000c5405856000c600541d0720b200c0c941d02213000b4040a04072203085407504601ea8201923204004140041c0041b003100c0d4041d4603083c000741c03155101814900455003c44000c5c401c15030085144d900a44000c0c81021194a0352850500c3c114080740c41a0005000c1503081d400201c0c85c1c81a00107840c0c00740c1c002c0000d10180d402080032040300d8059113200b2035001c00010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 361655791 1250 361654541 361654589
    0x6080402030a1703090c0f0a06050a05210402012a030e0d0b0f04020315010b03060d020a090f0f0f0b0604291909140105090409141e0d09050307 63
    0xa0301440c0d0100f181e0b112007101c1c0b10f0035201500191800102c0b17006900c071010807440c10000000381c40030f0050010325010b16140041e9038035480118400c0c04d00806104c4001d202c02151003140795045000e00c1d503120751a1030301c001445006400480c400c00312084010b2580d891401c08100d503410380c075051080101e1003200002d400440d8450001b8800151001040100714411010350300661080e81111103081101c201d511140200b40a5150800310130320002d0104d01c2d022003040180d40c00900070b080020b031a4001c601c142c1d80b250841c0b99031941c80d0360a52042c80034901c25003800031588401004403214140000d4600e01c213034496849070b031aa0000c1000321031850b000508c01201c0c49440b40d81e9a0384102640641c04003000a0000881c50300b441c0011603204080b40400e01c10816075517035103000301c820200001010802d8042e02c0c0c42c031203402081503001040100840c2402c8145403c00200c403502030032440c00180d0342489042025a10b010415a200000d0280950714070001c04030011916034145 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 361657041 1250 361655791 361655803
    0x3021e040803161e0c1a030f191b05090a0902040f0501080402040228030e030306100c031119060605060702010507031227050c09073504050304080609010b03070608040203 75
    0x2e2000e844c2d40c080d250401a007100303c0c20468007000f40b554070207820441c0441490100711100c201c1c481c11040080d41840e0200a2000110841c100019140c41c003002d4135407007006060741a5000c0741c0000303241801481e08000440017410030060551400707043c0380956000103028401c06040c4203540010804540c3c40c0d40698002004c0794001d183c0e95880d01156880e924244c003c1d510119103003043c482242680481200d120ba640a466441c1c032403003000c070881d805a000c1c1c0e819400c0100310700f800050740406100c1003245840c2a08401203d0f1000d04043c02280c030305620041c45801c041080c400142d802c40c090354980d80e01410b1139090b4494130b20103a00500f140d90b05507015030051115194080900c0b81402c41c485010b48101d40301001c150041c44030240040d00d4000104096100403010005a8850a0a413040c001c50b692982c0c480044c81c014440c50583e021940c0390000309090000348000c200c00346c1e03c4a075940091003403d0504020907110012030042e002040b20354400030341991020460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 361658291 1250 361657041 361657073
    0x8120a0e12071503020a0f0807110f100b1e01030b0612011d06030105070917010e0303090708011407090306090309050909010b030f120d021305060a03021e04080316 72
    0xc041c1110440d0856032211400d0080100712a800728242c0c0030b40b4407900c00d59281c0245515280703080c0d502c610041d0b840d924001c222004204007101d00761122501488022200c0501c8001005015040ba0031682076a101c282580d0040c00300e0762214a010007680f0700050070140c00c0c00e00241c450507900200b08a44070344504401504800000022080c001c2031600c01c00c07428001c041406a210032081500303039a42600c100300080c9031a107041c00110303101c09102319008141e600001d901c40c0d51240f030508581044500100c0c0f0740041000700b00782c490078001d07078001c03d9009104a11500e40088082d1101c00d507404050041356550184808250050603d10060040103041e0314580c50304240042c060400c4070040d82c0640a890406800400000317412180881c503854403d0400480c5035005009421002101a41c4007145600040340d858800050400150554003d43e13121007602404403011703000c140204040100308010440c0c2c0c00080141c0f10b40c00e1024000c3d08120140d0b06001c41c90501c003483c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 361659541 1250 361658291 361658299
    0x90b0702191104020c03090d08091305071d0316032105090a0b090a0f0b28050a030b040b060309101a010c020d1a0c0a031a1804033b030708120a0e 64
    0x808c40040c40b02103409040c80b004201d40710700358001148071550139102c01f61900408250b40e10504803120013028490905c0f40302c080c0403106040842882c0c282401c003594011703504284412900064055602001c070f003d0310440c02c0492a06c1410004904540c0892191400320300d40442d10a106503903d140307000040001d02c80c01380b1041d489002c14402c2c0c1d0301c904810b98240e6003082c41e2004103038480300c0c070b80a601003e45071541001390031003096003e03150f0701000704d0380503590342d51203900c1d0356520001d5030040012600810049080f40f28100c201c62010740030100c0724a00b5448259640c0c1d003c40712070119507050769019400f07a40b07483c022507410111410140594860130811889a40c0f00b40944400e8565a030b081c801c5c20341103e01c0310b0f0721030303c00000207410400303002d06412040b8000c2d540c0c5800a21902c0d008100c00f09a002072010a074a84200c030107401c0c0710012035054011600102d55001c081100030345450780c40e01078825691814040c0c0b03103000c1e500c081102008a0b0045407042e0318004060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 361660791 1250 361659541 361659559
    0x7080c070b09040c0306230303070203031b0708010e0a030c150501090f0b041109042a020105060406050105030702060f0705070c15180b070201051c090b0702191104020c0309 76
    0x11480c089500400b2005000c2d501c3c003411840014824090b16040b2010b814000445030300e07c031024803c01c00ca24202641500c07041011500580b410401042401c01d01da42440034404034442c00307030030404550b12042c03c0d40e0505070803481c0410702040781d02000358507040a2a4500081c541480f1340c001e14803884a113103141800000d030306034440e0020f00510514207404c004c900f100270100300031100c1e0840601a00002884401064142540a10040941b410700c4c0c60505015100218110040c0625403005035169002d0020a01b030a018180c0506401d003030076070541c034045000a6030f8000c01000d981e40400340c0c00202e0901c0380150304440e04160854007904616803101420381461600381c0b0744000140341c0c40d440400d11001350f0b10030010744034050300741444c00b61507400448441e040310100481c4483d035551503400d040d0741845542c00e0700f88590010012850200d20103400c3c4644104040d150384105882c00b000180c0492111603d944115401601d526650454503e180100c502041e080325200c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 361662041 1250 361660791 361660799
    0x210302030a210534051909030f26040302030c1905031203040c140112090213020301030f02011101050c041e05060c0312070314040609170a1d030303060a03020607080c07 74
    0x3c910070f0703225038016035119044c2c0c00c039504d2040480403e204002000400c140b12414101c450039580320320140300741c609066826100e440c0d00700001503050303085480d1041200c44c00d0144640320780003c088040509401c0c20302d032564021a4441074035559251003100c2c00800502034041c0c0c52240350181002900711a03404400b29914101070784103941c15079a40081c81000601d103c1c00341c4004c40c03a03803010f942d0410790b421040501000782c0390030030080303034844480c240240c080c1c044e610156001314001e114908804413a4000074210740807e01c0740c001c803039040000f0402030361044400c4504840d4220f40340c04c1c142840c00d01d503034610062038000c41e44c07203c00020800d40c04800000a4031014000314080c2d103843d00c0d950000e0702165220a07060203205c0364800040e000c2940c65105640c15030140c48100703210003442d030228095600030303450f90340490710080ca00004c40002c640003140c100d9055004520350705040000624a800c240310080c49000d000602138104107522054804030450f070b030700316000780b80c076 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 361663291 1250 361662041 361662061
    0x4051006060c03120501030302030f0315150409050603061012020f04020a020109140f060408030916080609071208070209070c1e111e090c040519210302030a2105 71
    0x52150b0a5000a01d08031105002d103034907103e100d040726419001146807105441c0d0951582e04001d00700030400880810309601c85c1c82c0c01c40c40880541c0c4c134181c0b61b030303445013800210012030b4005072003603002c0e50000f4100405a04882040c1c42504e00030301c007404803420180f000580180354400c0250b00240089440c6004940540165a40f20f11404420040b1014224001c0c2d80340703034144158100354406004074000c155050011a003042501050314403c2803002c07210400c12184d94020600e5601500801041010510261003d03140a50030644003000316110f101c05405000da000c4d105040c01004182c00750f0048081089980d800b00c03481c609440b802c0c102c052820901c9105490360030b40a620221240b42140901082511200c0a00c0f9070030048402c1c05640d1030010241304102038104004030f1030703030f941c80340341040c10391410550750f03095003000c200300410842c1040a0205607016204240000d80110603152084260305d000c0b05511520f181140c0010103800d042581e041c81d100c10b00c01e407092 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 361664541 1250 361663291 361663307
    0x230070f060e03030f070e010c1e0b1005030a12091e090c0c050a03140405030a0b0603070605160602030a02040504050a050402040c09080c01210c020d0201110405180405100606 77
    0x401514104185211070034096203d00c030456454003101700c407138001001e06003d40f402c00d0f2101410300d041c013241c58550b86c0b9051550705460800d0360000100c0440d00411030700392405640031020702003004000f45800b001c00d54903140d03c42c0040a0b4084540640400c501c14005940100508800030148242c040080984a07900703000301210642003842440c01c40b8000d147d032940d102e6121009000314821a1003c8409510650005040d00c404020014843da41000240c0159002e800042c0c81d03411300c1c200b010b141c00202d0748180280042400344545024224412940036070300081c01603560b82e10b0510f104000e119a41205074064501002c0c407011000781d5100b80e104610a56003040420104c00702175a011802e442900100c0d070007004400581c0d441803800300d40c4800340d140719130501248544c0e0038095071800065280180d01400c60b210285509010703401d4078030410101c1d24600b50900c40800c2d20401e07070081d182807410010020a04112007000701e9a0000f80001c410800709480704c40081c0100c0b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 361665791 1250 361664541 361664543
    0x3031a0405041a1b0f0304051509030d051005090c1303020409030815010e09010504020a0c0b070c12140d111201030b070e060c1c121104060f0e010230070f 68
    0x3802c072400003602041c04c00100e00c12054160f0030075080214904051342582d00c01001100c1500a000c03070140000d86e403100103070091103c000503648551801420b04103e030f03001000d031401c8110500c070400041e00d07442100e5421218000d070403035580a0100001149129980c03009400c10314203460341090641c444c0701540214004101c901c102101c0100440300d0320185602c09a101102c0001000b075403803e43c0c02402101c0c40342c1000c0b08144d180380c8508540540846055020441d000c122004100c8020404120344000e41450884040b40d00c800c0d50003030140100c031213041c580d1140510110255107081d140300b0060000e14040c20f68482c41c140c100070314141c0710400418001c002caa0220310340f03102a103a603000d081c002410584a6034a5900e5a15801b00c11001849503190b10816002c01c00e00820035082e80c004819136a403440d214004003403002550f0b010041040309200d4010070380c2c4c0401d00c3c81c10745c401300e00c40d020040600e4141d004506031481d001e500c00000080c041081000e101040301c030075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 361667041 1250 361665791 361665833
    0x31f09090b060f010917010f090f0201030509030a05030109090c080a1401150506160f02130204080c04090b06090702032703160b04061101022a160b0703031a040504 72
    0x240d102c4000780510f40b060402d11501082c050001880b104815046d442000403100001141d036541000f500c1040b03a411483c20b440324000d040d90711055581500a1503000007010000f5450100354000042407400306024245c40382c0e440d03400305030500c4040c004007006800c1080950340c0fa00c2491801c2900d26401d800032f0714a40d428400000c11036081d441d5401c0c11075402070000d03807400c0b4480040a1912250380d4048440216900c036010140e02c890928405800b503140300141c2d42c50034001410700d0140301950b141d200b64144a28900002c400c00c0f00c0d6900008260307903614464807804816402e5010f04869200c0c0d80d00c1c03944d885442c10014400e01c5110034403c2d4251040c20018440401d040c01e805d015032074030100100030400c4128031400d02c0d64000b500b000001030800801c0448010780e610303000d21410122075880f0480304e5090003803000781c0664421502980d211032410001c1d517034038001c8140242c10306076100310344018030002403100681c0d081d00900c01c209504e02454403403003050030040d0520b0301c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 361668291 1250 361667041 361667063
    0x14030403120c06110c102012011a160b040201030e0303090c0109090507020303010e04060603020303270d0201080c0904062607080106060c0f060b09180d0c1106031f0909 74
    0x2100c001c56181046100241152000704004d84024000b507c07c8622210804113000030121800d002810448903182454100703540740250b06214100003882c200560202000710141c410104c0070080509a40a2842901556503000503001800801050300f10781c0000400c104030600042140c0480301c2003621180b00b8180c90f088420200c420450318403000d60b00030401840000c1002031401d070f0151086102140d503a45030f6000c2404c681050780c000c0b03040408030311a007070100c2c03081c5041180c0203c1070388c079030f804407400ba000203180010103032003080750744400a004940343d1190740000018141102e0411001e0001c44601a0403001307690044c0102c4c041c411011641e00010f0250004175a00e964401c000c00045460f960703910f80160000b00c5603507654010100c03994660340c1080e13200b0f0201e0000c1d5401c01341992801400c10340a80b031440c003040100c0c1d91040000319091074154201c40162031543d00c070798032490007554000700c4034800500005401c07000a40740600342c00c00345102e072003503c203014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 361669541 1250 361668291 361668311
    0xd050c0408011d06010302040902190602011b02210318060429010806010308090109030506070804050705010306060203030a15031403030916050d060f020d0906060504050108120714030403120c06 85
    0x1512060280010f0f4203400075001040540b13041c1c0c0203d0206e5000800d0040101641c0008540080e0640c1c400e00c0540d4481d406491100145003241e02c40701d4407400a4004c17207030a40d1441c282d41d29205a2a2a000804008250004030101150b031451100608607011400d050610a0340440280c05810342d125031a10960506000c9245081c102d80b580001481d999095607030f045080d81011520341d0410040c02d0000000c54410030443d80a5521a12091590b09103401d00e1070030490250000380c14181498070412103258004101c0794000044100041d4412030f018103078101030b50583c406010404094025001c3e80408801107001e650000110703035200c490801c0d0f41c11000018464140d00031410010036010400c2600300312000b10380d1070401442e00b442c807101c070b00c21100040310599581d40e554205001d1401e00e4400c2c180503000c2500100740b0613100001c540014410008010503540f2001c6100220040c00c1055801942d40400705500504d00348200a026000c02c6506440013810140040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 361670791 1250 361669541 361669571
    0x1203041a0c0d0516080a030507090b040b09010e030109021203041e030f02010c11041a03060f0f19111605060a09120e03070305062508070c02090c0d050c040801 70
    0x520425008000380081c82c60030711094820343c03c0001003d210020b6544514001846040101a0034100e51030024044c102410000c4c601c01c5030341c0224406031020001800102a401c0658248400134070346101c2d11a0701c9404640905200000223402c041d403243c0d40c0781d5100c1c0120140c0203031406ca1440342103000c1c01441c10b0260502c036220241440c0300400384540954415898031900501070658401c00b01c04107804101102c0c9050f101c200340c072094421110203850140b1000f9001440580f070303c0428204000076450f000c00c050a208d405d21170300ca141400792412900181442596039880503140c0100c1c402c0164240800201103425014510024841c1c0d0400c0c418000340030b42050400c174480380c0344c51050300d16002c00244d460b49481495400400158200300381c600c0344850318208881c468420031900092101142c045e01403112200400c00c0c3d25511a030310b441442c0e01213815501c95120003403003005504c2100761120352030b0309101c100203075011490020405c507504900200203461802c5404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 361672041 1250 361670791 361670797
    0x50f03090102041a070818010e030f010e0f012a091a030103030e0111070b0309150103060e010c0f080708040606080607030605030c10080103060b0f060d0905060105101211091203041a 80
    0xc0142c042401030350b0fa103009184c00c84c1f82010703042c14242d50401440000902d00920005844c206a44030b50a41c4607548050110450b2110020001d11041d0000c0031040c0b0b203110569003e40508509042d100400b6201321407010080045800554504902100400c4158024081500407a02c00d900d00f00e9103510542c1400240c1c0010070103400c02c2070a08070746001551002e0088a400d103e95400e10340e03041303203035420b49008501c01d200008807050424005829500ca14a40c0014414000c48099002d904509000c0c0d110100349030618031542c0c1d9151210003020b00b50480310480c400c0c9400c21524035010780c81074003131311421800c8418070070a9008020801558030800000902414010000104141c00c20301c44020001e00e011400340b202c0001c64600d404c030718400782c501c940f40c00018050080600c0f5840c0500000c2d60072581041d03480001a008858495418003201d40e1103924900c1488010300382c6245180090800300130600250703203650340b0740050003454400003150032801c124040000c12 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 361673291 1250 361672041 361672043
    0x4050a0e061903120e1e0d0501110c030904180b07030b0d06060602060711030c070b0c0106050d030519050301031a06180a0e010b03010504051c261503012901050f03090102041a07 78
    0x380810f284d0441c401c3c8102c11f5812081101d2564031034102c44149020640a065501e0000b0000d6884500010410083c0c0d00b0392103d040c403141500100101144811450641c041600d0501103005900800032410381c00c0f0b41c00c009499103241c0f074800300d40310764003140b4140900c2c0155034080344c080e9400f2289849110b207056030a05640720394001c00c01d22200c840507015080d007480c00042c00035500d1010544040d51030100b1030011700c4c0042d0690980300a0a000c000c40c0a440c0350003402d5604596404c07110704095002c16410074184000030798543e80f81c1010080300c901c2c216a401007410120052800f4004400940449508240081d2080e00b41485544e206941090040690505081c681020303034045110b02010040c002d5804e03026540803082072048180d095203040001d01d404182800f1008100340454802e03414600180c0034a5815501807505503844086048102a15230042e190782c0304010294084c2c0702d0120411003581010740c0900116843ca000c1d040000b0040300300340740f0602c58408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 361674541 1250 361673291 361673329
    0x201030b03161a040f06020616080118090206071703070e19030b040c090905031903022d07060f0516020a050d080604061d040c0b04050a0e061903120e 66
    0x2801c00003c02803900080d441c01c0c52080e03040c5016140e010070f0a5042c119000040540e0000d018090800101c00300c2d0301024500346064070711541004140ba4550480364071588030079855401d1002035503245d408403000c1d96440300c0034881d610f903a00c1140819820880c3c1410100d441045a10782904010281000c141408001c03440f080e8250364400181c1503004e08290f54100c00354201043c09160752180c000407501440065485441c03480e28610144540740160f0201401408840e03a41d41e04800c0c04080b01503800488031080c82d04403a41440741c018240050107141c100305a404d60640c0c00d5002d075018611803c080c241c001c6108805a950b90903280f00107140d0f40c030040310056241e100d003841d80c2d040f4a0041011a40c40d50b910f13101d04185050001c82100c10705504240402c004000c40b854000340100e140b0141014541000101d8184482c8104480040700600190300c6030780e00a01065190000740d000c6e43da00c0e8881c207280d0150450465014046840f08155601d035142080c0f04d1a05900021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 361675791 1250 361674541 361674583
    0xb0612060108160c1203021209030d05180606010f030e1509070602010204031e290f0105030610051201090c17010c14030121050607020c1e090c03040f1209030201030b03 74
    0x19550300c4104480905540c1015400c0c001501000000280d0a0127aa0070f14001c0d80c48242005070042141c4000d0051034241d841e130441000914008208640d02c030b14242400c0400301d08001041e006486040c0c0d9025942c081c0d170f0310a0000c4046540f80303900900c0103908a440340c3c2d40300d103c10303800c0340f20324003020f0700822012251201c070074072510100800610410401803281603a41e10790110a00072204c181d40114400200a940015210404d0040500700c00030705041c280a83d49501c084070f0382c02084e01902003416045000320003500a00c03549a840740f02c1c4240d0558400608104460000011040b5400c100c034020360f8034440e6621401003160050098910f9191100240c07031160849070407050290341d8444c0d400810018400c10344600019000341c101c24515208102e4080d0740a07100800009000da00002913449111045510402c01c03d070655494507541054008103042080081c0740506140da00d51080c1c0d84403481c10101d038401c0c1c0b028407101c12030104150312440b41d20780d0301450356030700 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 361677041 1250 361675791 361675793
    0x7050a030f0e120d1103040b0702210316032c10090b060f030a12050a0f050304202101020a1209020d1101110f0f0d081b0d0b0612060108160c 62
    0x1000102401c0c4c032883c4001490300c550003402d5825801c2200c043c0c55045660003000812601070142c081c0216625911049813080844507200500015060800307040300c0d4089450094001d5000a10a50304204281c07004406907500303104c5440044070f401d0b0280140304096040442d030f40104001154400440d0180c0c0c1e03200020720070b8032100903a4065061048514213030104818001d00c800da160603035106951400d249402420300000441044100a420401c03c4041079034644107014040d2800380260000c4c000000043e01d000241329030247c074202c1902c005507403580c15401460b90402e1a1034501180d810382c5580022a0441900603420002d0101150003344101d021036042e428141441401c210040c41602c1c901a8000e45100c0d043d0f100c502c20f286200010441d403000c0321041d00d0000c000d45000d8103030321851403014050310b8444402160a1441c002c0c150000c008032000034200580301c01001782401c0c03001900382e40c9117010414a03800328080303200858040e00c5480b0b042d1035a0f01550b151b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 361678291 1250 361677041 361677073
    0x604120c050712020a0e13120504120f060506011b080307020c030303090f07050f101112041d060303210402062107080c041508041a010303020d0e03060708012c07050a030f0e 76
    0x401880c1c0d027040f90400c030100e02079003c0c000351034403180a40d1030b2110101051614000b00c40c00a001d2906220641162948040180500120841c0c0c890f81068507501c51440a1b032420003614030283d4540004010001c01f8040000d03012070082014003220340080c0c2d15402c3c031101e0050000340c5500300e03038400e041d05100d030b000d921040015244101112401d071019072454a01d5001070300103111440c01c0c011102c9120020000980e0401ca08501a62030680e0400031402440348000c645200040c0c007800107410f5598110903607840303034a0f40c010030078003000c0740c0d4410303001000455940d00442d0000010460007030780d0200351360940e42c4080c4420141c800400d402d440c1c0d1500240101ea0340480000420031948005810301e009500c2034004140c0001c0b00c9901801640d0207102d9107000b40d00100401c45410b5103c5066811600c5103d0340000d9014440812055074030a0664180f0051090061100440d4480000c2603c0340c0a03580400c68811040401e5003070300c60100764424240c0c07180070a1489510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 361679541 1250 361678291 361678313
    0x915050901111006170f0105010e06120c0405100302180c040b130302033903060f040503120f060a0506070b0c0307090e0a020405210604120c050712020a0e13 69
    0x4007120480701440f2007607014a050b10500d802c041c0c803417509070380180d460034002c00400c055500780703800900566051030990801c401000380103c0c41441c0308810504907d5050108010203030004d00140607600c1c0503030820082000910040b0302072034541042d1100343c8a1010814003821580001c0f03440c0901c1d05030b0406c8650010704c00c0d003840040e145000001a60200014210540304200c1c00c549008110503505204001544a4042003840c006004841e900030484551204204085101585550030041d00d50302035001d101845480c03d00034002440ca0000c1001e10a800c22140ea0908540791024001d140c0a007040040285018030b010520844110018540c440f00615003504001d5517201940d40c80d102c251000c48146600080a010500740000d42d807180c842680c0c050940201d580306075541c0c50074001d20107441089040f605c0f4034821310452080c0c1099400104588140d40c86444402c1c071071030400412441120311600010ba0ba0400c0c580b0244180e14010341c2c0f060105160301e80c100d18031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 361680791 1250 361679541 361679567
    0x13020a0815270c040209030c0604080106150908070b2b1401171005150604030c080705040603031d0402040f03051c0c02010212070201090e130311010b0a091a0d0b070915050901 77
    0x40035252403500326484c9c1c040600010051240041921454248100091030500485ca01080003510741400a2140000c0c88811110740000302c0c1c0e91001c54000c2c0d5407945111103540c200c0c0f0424403005191040e490b400509000c2c141c0c042c1d42c1c1141c0d0380d8078040c1d0904e40303a82d8417110080d0403222500042e03040355030050f64840001c1c0c8031410300710f030520002100c9a10a07041240c0b08031944405105c00310080004034007501043e0b50400016007541c4014020f114803031140200d800281941e00a030b52125010340b001000072400040e09c0c0c1e41c80b45040d544425803c007a000480d0f002c02c51841c0c44511803074400f5101501130b0080c16100d01c001c5448111036101d104164103000030007a000a81000c00003e5502c100b0141c280441041c00794940280f1440030306c04e81c60350980c18400c1001041d5516080c00f01240c00310700d07000030340303502244450009030401e024141e4030250743c1c08298148003655900714401d5845543e045206901c4002200a095440c1e9003803001403028481c140d0380b5402000c0600c460 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 361682041 1250 361680791 361680793
    0x120304061d0621040507060206100e090f1c18032102010b0d0303050f060109080d030b010e0d0303020901090b030705190c200a061713020a0815270c04020903 69
    0x21402c1c899444540082d03400c006036890f01c08200c18440d0500c4120003410892000c0d10b15800c0a0500302180f08040c090b244116072100080303100c5040420000340500a0b0400303841d1182c0840841c00910b940540e107407000700301c9849541c0c41d5000e482048030305a07584a03502c18150010900301054801842603040295940c0f51103040d503650340c1011130000148a50360104092800300503186182c100640014188100010b09210080c0040386012401c80e00c2c2c580000c8611aa40040340d4480000c48c038241c010140509003411305901d5001044401400c1c0c03105105140e41741480b110b075210807503194002076401c1c4900548030140200382100c0b83d1052070006102945a04d030100c02d804c07180902d01c1e00280741c04c511412410001c04500050402d070402903021070501310030320380503000100518003102003c0d0048d01195120a8418040c001c039900316001c40c100c0d42c00e46008040c1c2a600850110810310709014200082c51507082444088000380550b10b80b44400d000194009031805d0b541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 361683291 1250 361682041 361682047
    0x507021e01091a070c15020706031802060c100b060a0509090403050c0102030f0a0b0612010315111b150c090108060301020417030712080405031603121a120304061d06 73
    0x8240c400042c040c03c112404120644e501d4581c580b103590802964802600102200b21691003140c01284100840b2070504001c55401d041d1a140c035005141803000944c00200881c030f0103498180018801c801103d090b40401c0101c20701c0e0104000e50080d03411000010344c041040703002038145410041c3d0024400d003005400e02c0d144420160036078204403401044018141d0130025500c1d818020309200c0c040950740c00745051f694110000700420b0500000d829202c0c42c6e10021580c0c2c1d0b4075400707045851000c0850790f03182c0000300e8400b10070140b80303015003405208800165001c64030306804180910786005141d4980f6051000545000c1301c01002d403645550300340300c0000c4d251102603d4030240c40d00f060107140d955140b4585481d41c501c890580c41c040000b2a4100000104000201e4018142000c4040e18501c0f00e0b00e0102c07210700700150311008050604540d14a000c617000ba041e03a074510102c44400c81e42425600c0d039680d034007940c0305410002e080140302c01381200c0e0311241045039040c0a00114a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 361684541 1250 361683291 361683299
    0x6040b01090c0c0606030803061905061b0a0f030f021006063203070c0c080a020f09041b06050702101403070c02040b0303041d0901060303350a0c0f0507021e0109 71
    0xc4695a86c0251490f000001c20090540348c4503281130042e6101d02c0d5240d0344142000c0c0031030720ba4007030000c42c402912902824082111030400503101c20a034841e250f0500c4145520f40100303031480869103a00584982c008009044203107005060680b0340c5565142c20510400d01e405030348000f03040c05c0c503100750060200c2500c078081c100c1c000c42c4605090780b42c1e0042482280b42c402c50b5080c80f640041140d42080d4041d400603942c0e10300002038042c040350011800d44690420300300203003102c04200c800048540c0b00080d407a4000d00070700907490003201c040e803403811405006e03503030024880d6000c2010102000000c10050069401c50500c81c00a0b00000b294880b90b00070911755882900641c021103800c591007203110040e07121f4543d0102d0407000034014075182d5907010b08100b080b00b8415201403803001242c0340b00c0c80504417900f2100a022040001810881040c20084c458040484000344442601c000000d000340e08a441d5964040d10b40c5901c2024001607240030700a5224480c100050408002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 361685791 1250 361684541 361684553
    0x4110108150d200f0a03030f1806030c080601020a02090610020a0501051906050a06020a030c141c03061215090512070507061704021806060409091b050306040b01090c0c 74
    0x480c03901e10445007407030388940a00c3c400d4090b94482050910078585103044a00e2500d40e00150b2040f2945414141c860a4943d2010780d40380c03141c0c507400840d444201000152596141d081012000c4854444041980b611401240c4904422002941007060f80000c90980c2c200200e0407051040c0ca031060b16443c902c9a40e0311425250240d4469813012b6405000302c00c0300c0b8151103210010601140c01c022410303d0703d50040e481d8112040c02030140028002071310b041c030610042c00c4c549402c00ed03082e84d410800483c04020040c1c003412001002918112001c210303801102c0040f140f0b41d40188071100b18a925103400d1020b00b28001007160580035a90f03001c215480c1c08005030803124421800740c03441c42d060060040c1a08001c140c00d44110480304d0a00002d602c40084502c02c02e040b40c001c2d038413a6034030100400c0706403045030b12034100c480c07902da01d80040c0074000da03201280f4440c200143c01c1c402e40c2d5204041d07441e4026600903003d040c1c0d20004125030001684a0307150010681401d0302c4080d8151500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 361687041 1250 361685791 361685809
    0xc030706030b0a0503030c1f110408010c0e0f01090e040c030212030309060c030f07051608042304060302010225050a0905090c0a2403020d0f0e12030411010815 70
    0x8180429103581140701d00703140110703690f4080c0005400560030b10b1403032a291503030740c03070701040d0020004881c5507052030aa142d500040100000e500340a03a4031603495821b1402007814450301c034000b40c02d0325a54003c515006051180c200d00503554400d1060400d14000d10f090400352084030b10700500100000140c0319042480b5035001c24034041d40d16891b00c18801c0303040ca40c0003805000d201174100104003842003280c112680000301842c06036207131a4041201488101c40e010701402c828000300340080c22a0800001c0190fa044c0e1f002880598050074046c041950982d0000034003681040940044204070107a01049000c0c1d40710744100401d5030b8101090311144260003181095840e01d04011858000700f010940c4d0744e0f016140e48100034a030101008a040f51031082000030006161070f0b500d000c0c030070b406403401825880020400f8090101607200100807040001e11603014003080d40ca0500c0214095901c00c0303400102406281c140c4000440c2c0035200100144070f0070384030030161103103134540c6080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 361688291 1250 361687041 361687049
    0x1a03010c0201020a0206090304030c2715080f06090a030302090a0e040b040b070e030703080d110d0207020108090a0818130c020c0405061c0809030c03030706230906180c0307 76
    0x5a60744c100840c000c1c10544010891141e03940b0412080000a0002224504850024003801000035a403e100c035000209940000403103400c0c5488894210040050801110401d00840d0034400345c0b40081c03600c80c82c0894066421340c03c040d2420010a01940041801035001801c074580c19817155030842c641102560242d84000c0f81c103080200b0400c044a2064009882e81840c10031500c0c0c40f400242c1d60203860000503d982d8011408012400f1260004500107051b03610710780e2580c607141c1c0160002d42145000342d002550300ea0100702c1e6410f000c504d5130390b200e0700940424038050380c5000c1c808500744068082034000340000240a4050107500c80c1102000665000e401c485981000b00004d880b0b003d419244564030188507940d1a404a18a882100c3c5e44244495114919140043e041c10048a807a41e010b00000402d10108511607003c54040c5030360321480e040c41000400ba0071507800d800c55954509a06c80d0380480e01680c580741c02d0620108074030086604018020002c6810581c0b6580 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 361689541 1250 361688291 361688293
    0x6070f0c1d042003030904090524070207030f2d020f01030b01051204020d0f0f0302061303090302131509020d1802010c020d1103030304080a030b030a020901091a03010c02 75
    0x400340301522146400c0d00500214050a62590515407104041c0c059050031107081c822030b1600041d03c51318144140c07a80068010002c020349946418425102c03c00e00003a00c0c06801c100580720381342d109a0b070803280a10540d43c001c00d031090541d55030f075518400098003940d200c4d805170300f010b4102c3c8880b510fa5040388442d1903207440345405c600c14400812418128030381418202030750303501d581c0d0303201040c0c6014104502c00c0030416121800411104500100c0c0034245807840495402440204045505107910075821100035942c3d1010703510144c0a000e00007000911000010000351401c2c068002034030061060000703813141e506c000c3d02c4400b07010381d04c100081c0b83c01041080f00040c003840b881d418901c0440c03071a8000016540020904110280e00178850b5141b80c500c8401e00c038a001100340405406011030340d9034145800c1041090b00500e00c0c60b00001e0070842840c00d10704021802071003056000c0c5c003c024a908002c034600143c03010810302141c546001c0e0140d03406035070900501d852050781da0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 361690647 1106 361689541 361689563
    0x311091315090207020a09051e042a060e0103060308092b08090a0501020d1409120a0f020a0b070c060e0f030d030507020d0c051b06070f 60
    0x4107002030501900d000300e4103034850760061500074001c0b6010310680307541d0040c41080d01c204841124047d54079100c001c42c1c802c410041030f90042e1180d0365894070b50b80c202c0101c0b40003203113140255001c0070032000d0401400c2d811005062000c00280703000e0000c1030440d196000280719403103045000d2054600391955141c1e9200d207048480103844200000030041d4142025141c00266403540f192000b401c0000322580009030898002c002601e80311100c2592000c5540d01c0d4011400c2c054100380400c800340311000051002a108600c11040074101e02c10a005000c0219216000148604802c010078004648c480c41d80f0821078149160003100c450703540001c00c0f45114004c85940d01407207615503118840743c141d084070744a085140e00f00c5882102c900740c11240c0c0c1c0340e540d0001d00f035904032140d0a0211a40c1d40e8180c141c81c0006403882307103401903603940c00d003034401c841ca07056030800b000e2 = true := by decide +kernel

theorem cover : BRFrame.Cov 361510791 361690647 := by
  have h0 := BRFrame.cov_init 361510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 361510791 ≤ n) (h2 : n < 361690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
