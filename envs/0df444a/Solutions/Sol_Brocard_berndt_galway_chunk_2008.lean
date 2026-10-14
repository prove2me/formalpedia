-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2008
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:26:16.110983+00:00
-- url     : https://prove2.me/submissions/5711f2df-3295-467a-bf79-f17437bced6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 360971223 ≤ n < 361151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 360972473 1250 360971223 360971231
    0x1031e0e0a02130603030e0d1713030201111506120307080f04060801170a060e010f0f0f0b090c0f0306060d0e011b210e0a02090a060311090709050f1c0308042d06 71
    0x142031806644c40b500c9d1065400240000e000760101d2030856010302035a200340c81d00313202e010301c44050a81c2c500003100b2a000c03072080c00010501c079103403c4160144981d400e40440c0c0ca80000ca5a5003910b83d04444580a10840042401d00c084c0b50410140c502402c00e40e0b1a41200c500b6a02d07049a41e01011200540440e560350a4602001ca007904247c83e407a07103040c410b00c0380510300005040100840c07031401c0c1980f8680428003000389041c607907443c010700e21030300b6850800c10300d0000690a0b0b030024001c140c0c4240c2c100440c84002c20316002d14004c0c01d82c25000002c2c40c0350958140c0c41a40e072010000c03010002441000c5110140644240c01441001c00340001c50a000702281d034a44601c02402039805443e4000b040300030311050700440300b0780703200301c0500041c000301c3c206220840c0380c203692034408210507180c107204c00e0604001d0040482c0005008004d0043e4000d54100c845841706c10982c002003140d4100001d0103406400b04108010312aa07000c01c0c1c2a40c1c1004100029100740300608803926 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 360973723 1250 360972473 360972499
    0x1c021c12180e0f0106020607030606090b030a1d010b101e080408090a03060e0f030703080411010e060a0f080c16020603130b010b130803120601031e0e0a02130603030e 73
    0x30742000c10014001010101403030741031080c002400d440b024459038005224080010b25082e200b030244c2c4c800c450041d00c3c2c003043d4600b4440005001d400c010901817941d0760f11a03928001c0140300501c03481d01c1007101c00000c0c500c103011090002610001c0351150600004100c003000c1c0c80039090115000444510f44020551a54542402184585203000e6800450036074040280310160b84404c480d420760a040350700903002e4010b40c44d1240900000540841c0050b4002804a40c202c45548421001450075220440caa403000400c0384e007002c040b5000040811198080d0903400681054110396025403407810b28142051400c2000c030000300080c042e034070100102d6039040102c03841042e43d5502c81a20f03102d560319040c018400340c004141d000590340c030f0301400240d00407000c012100d82180084960b01c00f0f0740c2d2200158045c2c401003080d41c0710302004944490013001140700b210101d00c0d1440c042e02e01c0000c0ca004000c0049920012941003503d0003001300002900300031a082058001da8245001c448 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 360974973 1250 360973723 360973757
    0x50906090307050301050c1809040f081b030a09050301050f010e01140d05030c01050907090c08060603040f060606051c1104090e071508010306110a0801061202091c021c12 75
    0x2c1c540e489950103609190502141600d0b40e000b828880c6040d030401d402130001d03842040500c40b010f0310041e141213212050040800c5125004081254844980c1d40000d900d99608a180d41d205070409800140e4800c1e09001515017805110b401080c0b140c454881c42d4140751100605400620640700c42021700c038280c20294071044034104085401109403600d50780e070700388481d0180104803007480301d41c06051404900000c15118822940f80070384c0c7d40da800383da42d80f01404034950029005650304c0c0d654030300e100c0018881d4000c4401400b040d550386500c56116141079041100103071820b2501904000381c080f03510480c00c041c0d900300c504600001c6559240c0c00b60f4142003107a030340c01855120b04240060b14410740c02c094054100c81c80381c50700304024400300100c4601c41c06412540c1c4000355510004010140c822003810200c102c81c0300005107403203903180028038540380c0d40030704d2052100e00d4040d1001b940791030310610034204d4881c81c0e82041ca00e820b40c0c4009030340f484410404140107900a0341b20b0140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 360976223 1250 360974973 360974983
    0x503061e0702012306030705090403020307030e0a05041b030e030c0307020f010309020901090e0c06090f010806060d0e0604170301030b040f0602040e04080d0507020c010f030504110a030309030606050906010509060903 95
    0x440d100d0920381c0101c070049a80134000200702c503024002c0c07264030300004660401c0c4078030703510a035010f5020798100b40569070100c80d88640c0b40002c40c5e01240e92507020556685900c50200300c0d0120b50000c0e402400c400c00d018003a20242d00020b601d540040c007a1038545034000c0200c40a035030b81250032031880b003134850040c2c0040c680301d00080e402a8004d400402c1c0c0d60300ea94444441d509007802160525640c0d401046182d00c18103075007039040000049035140950261a0081c0c00010040ca010300b000007480c144021158001d81c0d0305407592103241800b00b4001c12283e0102051088807003a407844d81191070300060624050001040d400e1a002c0d4081809002d5041d100070380781d080708425450401d414201e800c0d03009001c02400722450100030070595400001c2902c80d03641c1c1a101c010041c00c0340301d0103500810000b030003070f101141c007506142180c1c0e41d1016100007651080d11052081c500f1420020101d03181d6810003800f644c100e20600c84107030781090555001c0d0b1400c8030030a6641c805103011034100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 360977473 1250 360976223 360976241
    0x42003030717210f150a170f010516081b0f030901090b040305070b0a050603190c05042c2b0c020406180b040209180403140a0f090503061e070201 64
    0x7280c2c00c0d000465581880405240200800e6074212019102c030243d05d0040d0810440703c070b521006420003080001a070403075003000000b0745030580d4040042e000049085d0f40089480c400c040b41590140c42c41c007a00408203903048440d03d641110341d050071070a008868424694880340801c800320006140c0e42094008800d11540003052000d24100380c070f8050407d40000204540031940000007407600c1c0b0b0544a124802c0da0000c004100d8181804910740b4101a6030750b081c3c079001c0803040c0220f500d4459014415000305804036020000e0a2021919240d809590b084074080e009240d00030881c7c660303130034555880d104482844000c95440340303007590040c08506009400c42d05001d4001100b4280807044051000c5601d42400102c024000700000c81c451080c050b54081c406240106510b681503031001c0c3d01501c2030070040040c0c08808580031240d002001034000051480c050032212a5200d41c0410083c0001e400400043c1800f44441644000120b01c09088032038280c001a00141700350040e02007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 360978723 1250 360977473 360977497
    0xe0310091e15050916140420030105010f02030c0a29070c02150703080c03040f1406070e0a0e1303050d0f0605031203190c0e18042003030717 62
    0x12000e842c0c41c8280585404405086034030303100010301201004903002c5809043d036509a603203035003443e6103a181c0302c0003030a000d50001c1d41e507a41200140410b0103400d05208a14080300d4881d80f60000041c181c2071022081e000b190011b10012000220005105d0358469000320301003c002452400d5003403e10340ba0441041640c41041480012900108118a0207009a031030303054505010050881a1062000c000c0004403500e00040c001e0040401a6821a1045900e40c40c10541510744219450b62a610351103160070030000c1c000340b583c0000064003801c02c01d9805078130f024602030b035440c9503030401070440703840251035030300c1c4801c1511880c111a0b450103500d004100070b07010a090903004004500803e4001d10540c8001d500010120094034031984501c9a110400c0104c18601c10141c03484a4142062040c04059016a6980c0c0414801030703502410241d080d61500c0d061241d10f075010200030440604202034140005d460210445084030340160b02c07400c0c40b0ee00070a13444142e00ca0074000070b032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 360979973 1250 360978723 360978773
    0x4050403030506031005011a07060b03150109060f12080901030b0415180212060d03020c0604060c0501140411010c0201210203040c090b06040303082e150e031009 71
    0x10540c05070310043c01410268125000529a85a11012102c0c02e003d4000180c05c80c1400f0641101841c008240c901d01c6400040780d41c806400c0864039040c09621842c0c20500b540006010308945842400010300f420a844130940d031030040081d1841d8800d41c40900000380009189140b079019800c045c010300c0340a042000304401c4c20001e00002c001078050b5408007080c400455449104034000c3da0f900342d04503644a50703541c442038200180300403442011810342c05660083c0e0f2155803503a020308000c3c00681c07144150410ba40c5032080c2120b00381114407000301b00d0b02c2c0501010070246221111402001e0030407858003006c500040c0c852080071840306200d00b8107240c11074041e00075600554003c0303110310030389a0100d4842a170344c801c4d9801651100d4024400380030030008280f18080003900101448140001d0b40d5018500d001c4900e040e6508200c2d00c84000000c1089903816034124640c2101490f11032450440003002903110750a24026078481520780011405201d1200c03072200b0749001d0161420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 360981223 1250 360979973 360979981
    0x3c031314010b0f040615300204032102060a051f0801020c160303020c0d1103030307020106050a0b0406080610050f0706150e060303031609080106120b1e0f0a02090405 73
    0x29001c2c1c000c6408090040310088079400303450070309000d0b00b8107a500380110407004501d8a1800c540903500c6002c080e401e00882e462040b10598422510b010030940c4d200096591400c506002040300311f5030075902c0c40034a00b000f05203041903001c03cac2150041d002c0280480c40b03444040a1200c0c807100941401c407103a425400c005059101507005111000a036801e41e0740301c01c0340e0034123080200c41500c0040c0c0940c11042603400c4900d0000ec440d43c44905c900ca0101440c0f4502d8080391464000319400d00241c0c0d036500c000d2255241c03e840349001400c2510044d03241908204008081200240072a80240544034071a45628062025100781000e00250300e40c031035880c0c1c148680608810071500301c011038110301c0411b080204d2040306c6d02c142c10240c0158556200c000e1115024050b00d910a03080240d000d001007040c020a0207214000c00b0550508150800319082410307500344040c3c850000c075494001c040a4204a1601e40c03a8409100090b40c4a41d07a591404000030744115a41103921034a000208 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 360982473 1250 360981223 360981263
    0x6050a09060905010503060f040b0901151205010e01020a02030f1303080f04090506090c1b070b040906060801080d1e1809060815063307083c0313 64
    0x10402c60780c0800307090020f030366100141512801c09944080100d03200c2400178010881c075842060300310880740c0000070351407000c18000d080c3c1100d54001c010f8001c0c500c0750200a106007409103010904d11320000718940200124080d640c0d1144110040c00040c000c030700100301410042d04103000b5a04011046d07074503140300414040c603074800d0040c2c2414501e0311003c948507007809000c15214800180ea00341c81e040301e45000f0110b000242411480d02c3c800c2c100003051108030180904014400090301151b0241403aa0240070b00314141c01540d150340c0075140860a05034450080d41c8034a640c4810407010007800c2c041207801015000c0c1c0048100420a000545d04003168820422580007405444151100e8580001ea0074030030f0380e411758030800a8110440102c00054080d034000794402110745000e054140b200c04640120f64245c42102c0041021444d058400e4210792942504030415000f81001c09030700c100750b0a25443e401b01e40c44012000801c0a9604240c407440e4540141c14510306060303a40385 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 360983723 1250 360982473 360982481
    0x308030a09050706090b18061c0b0f0306090709051e01060c060c020a020f040b120105090a02100503092e020c0d02010617100b03151f0506180d0606050a09 68
    0x44440748200d00c400a030145c8900700d124182e6840007101c80ca8104080d1050489184264a0550013003041000f0310701200a002480c44900400d040418900b00740800c00445910448030315000780c104100b001141100801c82c81c0c11340f9451100050240c50714800341040c0704460303002c440d081030901d00108040b40c104105002c0184a40ca0503c020302c00c0391412601c1d9080b00b41d00941144020f40c01651500e840e800510300800064100c0c039802480070714080c00e440007650304190580240c6c0e4904254100307544440034140607828041c1c51401c01c600201e544001c40342c0a800c41c5449502202d2020070004102d03942550741e010259102c50b40d40325455168602c0309804000766103095400203100003521418900c1a030a280540085003c0c904050064100703046d082c3c0e412700a1580303000103175240e50b1015000c5c40c131544030706820a009800c1071615220540049209010912441c8440e50b8051414518814240ca003015240d60314030b82400500300b19009513520180501d000305001a09900c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 360984973 1250 360983723 360983741
    0x160807080d0f0503041106130612051003020310091e0b1008010b030a2a031a060922020112020a05091f0828050c091002010501080d180308030a 63
    0x1d03508180c80c0c00c10305842407108114180e01091040c0000340c003240301c00d4030015544002070843c520340b02d0401004844a1904d8210700042002600b007203107018240e100d00f0340e00000e00300240c034006003903800003a51901c0004100140680b902c41200c00c000c000c00b1008100780c140a45c0458072012450510b2001c001100c11154030746014000190800c01401088805c90b000b80c064503103c582a110348a40042114481d41e040c41d08020418142d0810f9900000540c098540c02c80f1160004281c14030500b80070700710364442c2d81e01009010340c01d511740c2540140645003043c48512000540300513514010881d1a02e8403903480800c84034030b0990400024149420202d554000b5240080031a1149040f1229040001441d00300045c3c1188040002c580586001400c1c4c44407241c0345401c0e4009031207017150a00300c628804a0000814100a00304586e1504180002d20540d0305104d0410f0307940000302101e104000e000441d000f2881031840841780a190855001a500d103031120540026202c3e500b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 360986223 1250 360984973 360984989
    0x60703050703200a052506090c290901030b100e0a0617040b0c0d0c0c02040c031a0105030612031306080106090608011505091e0901050a0f030b09160807 67
    0x86110f040c07005030201c5038110b0342e00300400b00d41000601c41084500d5080400140300d14102002803864a40b00d02e120303a509144610000314141a5902c1d01c0d4105800300d501c142202c4084015a21902140d070360780e00b10060084c0074141d10359194000482c05410f002239025003000c912132110034004e40c00b145084015800f503940c0c008259070b940081751030403440040c1c242d211001c040414001a81000b0b0f036034004c2c400d0007640381007401031400300088948094500001c16032003910002107040c00e024600100229040c100038403100411407465400c20910900e040103000000110355941e90741a40c910180c0c02c00490303886080d4080c03910689000b0380112008120705c0000003464502c1508440161240e0703075602c60701e50340f910541c11070040810050400b0710100340064003958a0711440d0407040c03806c404002500200c00c0d07052282c03044060b04070030f01400d452030051200502045034030007141d07804035840c0c18941c1c07441807450402d5045403d450100f0420440098003100004041c000c0e10401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 360987473 1250 360986223 360986231
    0x1003050f0907030f08030601020a02100f020705090421030f0906020309010b120706030e0c040e030d051012080f0c01051306110310031e051606030f020306220b03060703050703 77
    0x184003a41e100b566200042403c408084014002105c890180d41c0100046c01100c08496840c0d001864a01e09698100009907030250b0804080340d04102e04401880240c40c1c42c0d0385820591a003180440c00c00c01403601c8a2003885991404520039800b040c4d01d100131040c02c1200543c1c9107850001b80d807007a07504441b80c0d0b083c0f0468480e5850800d0400c9880d003400300c000c1100518283e000d401820b030f0301200c1030045c01010a8450a0b4a8a025041c0503030600405103039140c00b0300c1d54410403108060007004400d20109000d001401000c4000d9000ba90811b2003280c45541c070f0b1951044a04c41e10036500119405d0078140040c0c00074101d03100c00c09134441c0b40140b1040c03880c0c4414409038001280c0610840b0340d90278040001c1003200c600f5154505034240c0c0515880c5054035410300d04098440c02c2118201051030800c649507140c0f042c2032981c041e49200b903145d42002d000144210301981202080312240d048002c0e07414250ba8840c02014601030140c508920f401c100c042c00400b0200c036100042410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 360988723 1250 360987473 360987481
    0x50304051515041410050d06390c03081b070c0e0403020d0507080304020f03101d0f0106240c0605010806060f0d031403070c05010603141c0504180b1003050f 69
    0x1400549a1141da10000034885c041d282c1410400a00310f05603040c0c405640d60034440d500e14480307000d8040108620110400c440c042c0c00034813800b80015501103020000340d5489100002e0b400174040d0303040000b02c0b1507413041484d540e4001da418410400700800003c007440000030201c60a400551041b8003907001d0300c80710644040280c4c2e251050200c01030107244100005001403804034540001c108015046440404e43c60b00128202c0700c01c16002c880c00381e1070ba015881c00342c0041000c0c42c0002d402100900080b403400300c921418004070310401004031006054044030b039200311401015a9084501805503581d180511a00e54105482c59030150043c84c29070742003401c0240f00041102d500d903503a84148030103404407041e15000074150004004a04110f503010a600340071381c41c0618001d108150024a4a120003031170040e9205500000300c039068026642c15404c44180c408075054066000d88207a002250b01008015416505030321031401b12154102c070b54103074007a62103210800b02641207a11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 360989973 1250 360988723 360988751
    0x803030f070e01140c0a0303110412031809050a050103060506010e130b1504060306091506050a080a0e030d1e150b07032a0c0506091509060903010e06040c050a1505030405151504 78
    0x400e60041401503841c464bd0f00002a104140c541e0484240554030381403170380c031090351400703aa0082c0c913050011a101c00051041c0601da1080300d8120809007007040d41444490080340c5044540a07091611076510802e450441e2a041c0d8002030300d421070444c26948588031200039004100724058811030a2034800020400c0b46410700311000e592244d2202410419001c02c02c4a80c08401031031061a00d071108110108090100043e0918121051001c14422035407907960711114032902d0808443c034101015095120708107402d110503604460400ca98a414504054902001e000381c0f4045904003d40010a40d0303d5140c104002c041c8107800481c1c1c41c82e82d6004101c031501403054010f03809030403030355001c50220320900104503464014241604041c85500000c1c01c403014002118400e0704804100b00070000c00c0c1020101801d41100d450440340c1c240849031441240e006504414050000003282c180b003400c00107800c07084070958181d103441c40c26911725034011303e900a60074047e9080c1172010810071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 360991223 1250 360989973 360989977
    0xa1d090109060e0a05060f19020d06030813290702060a030b0d060506010e0a030b01090207020d0602040b0301050111030307020717101b0908010218060a050c070902130803030f070e01140c0a030311 86
    0x5201c02000148c10041001c198000b5881090500602591880300000083d0901e01420382d0111611702043c003145040c1d00c4050040c6c2226000c2c0b201a00019811400203541d010340d17181c1d070340596100751600000c990a03001031413a40d44803030703000036100319242c02c0000c0350300024420103081c0d8400d51490120f00c00c1c04180903550000410211302e00d0011b2050280320b07405019420700003080b51101d20419202c240c00c80c1e001e5000b200500e20300200600c030950708281e1405455603482d0003145585045d400081d15204640120780d850301801c0c034019134481d010410301800d50300c02e140402000742d070940c2c2c4141d201c9600082c1d04c080340c520280000d00e8041071007558100c080854001d0600c0d22888104a80c07a40301030740301e506000045c000042d21303040421086001c0c6c051a48010ba803240901d4408000805991000d106a032003001085203880c2e0b90000f00d034228140d410301548101c1c0240c01623920030f080043c603007007000010131078012500b8002400310720540241c404006241c180c0c000c4010074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 360992473 1250 360991223 360991231
    0x7021008060a0614120c0408060c040e040605070302040306140105041b0c1704030b090304090f05070c15060b0c101b0f0f2c01020c0a1d090109060e0a05060f 69
    0x205480790b007048594003a01008071a0400d210600c1d1a1030b201041504e90100159182551004080f400303109400781000259080b007040540c1905040c03070500503003000705004000800c079503151804605898000d0301136502855001c5014841c00c502d1540b5541400006d1045a105e01d0424130380101148000070002055070850381d4112848940d906c9a25184900110041d05a80300b0071000020a4850001030300407035070040515581d0b464801000d0a0300c2c0d000002c11009864003050161058000079055110396116885002c40881d5a0482e0002c050399801401c00c50030003c0c0310030314901d0218002d84041d40141007082075a8a030b84113031840901a800c03820100d003100c94065580c81c042e420b5580e2032040d80c0fa00038182700700a60084080070b4420390301490391102c1c000c3e4010540e01848032500c0420305442c01171940780740c021001d21003408076500d58003140c00107022078415a000e41000b4061500325006020341a030600d02165114080b41050b2103034050b400104600712081c0200e10f0003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 360993723 1250 360992473 360992479
    0x4020114030c09011d060c0d020f2d0109140109032303060d0c0f0b07060c080f0a0b030307020307170d03020c0a230d0f020c0f0d0303110f0f0702100806 67
    0x34a48143c005440f80301032854135082c0344c0140080403403159100d000410740e40c0410b60123008482e0b0400b0780030b0310300208171502c0203140c2c112141c03074850082c80d90401e02d0001d400502128040403c03032042401030018010140c24203072421103142c00d15805400658500f4465a00c0e005124801400d1103c00d0408007842d1040c00d8040010840510700340f140c00e41900e008501c0c00b10156550b1403400404513230761303200d2025500003260807424081540314450500c0b00a003400c2d410b07407810010304900b072000208000d81d4590b44a2041059850030000d42e003005a018007180d9180b134a90046d0401c51020405509a07403003074100b5902810f102c0d000341c558040a8000400d2102055070f508a04070700f44d60303142c1030381004c41c400108400404010143c0f25500c1030300d4585e0055581d01000303041260b81c80100e4000c0304403015526203901d40135072034509207805140000701c503a00341034200d06a00c0780c1c1c50f0001a4030404a20f80d40044c40c94030060100b948201e50380801d007034043c2e0341910042c0044401c10380c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 360994973 1250 360993723 360993727
    0x70807050a03060504031205070909110901080402090c0d0e1018030c0b18030a180501090303080f041a0403090510080c0d0504050709090b0105150403080f0c01150e04020114030c 78
    0x7001580913085950094400d0520f0210781c442a01890200d1b00300b01c45440000d60035502c00c01203001c10781301e4229035a26400019191040d120006001703010003500c0280509842e0300000c01002c070702002d03581e4902d0700101c20300400c01d4140780340d942c0c0c2400780903000c0d040e03103040001c0003000c0c8040d910008555140c0c9607414094113507240c803015210018038114000c6110308100d0b0141c0c4c807d1000f409191015226a90054010061000384e44803d4000b00c1c140903603035034180702107500100300315880107051220784400d5495150001030034012982402c5001d14100501041540001c0c000b41984c0050300d410300c40030600d940459082c2d105039022800b03800104400707500701d00c09800c040c4e07005001c0c0c5d040b075003095a51840304040304c1440700144c805900d10b0700144900d03e444406802c000070395840d424242421038842150074880d80300f51801002d40024014100b010a400c448149044e611910006035580c01d003600707240004407070803400140b03440080d030701407a1040b06a9015100001ca628 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 360996223 1250 360994973 360994979
    0x9060307080d0c2907033206030a0b0f0702061f0506090f13060e01080a03020d08130c060c050609010606020d030f0906060b12010b0f070618170309070807050a 70
    0x503c2c401400030013074a0040910040150709402260701144414640150080c035140061000f0300b00d407100545008444148211410590054440380c03420b115040c410070003d895000000307140180743c0000070300713105e030907420048041c10020781c4501c240c0164082c0c031902e598055986540144440120403413000c0d40205201a06200d8040c0100020240a04640c0701c2e1960000700840e904100000d00703152180014840d0401a0005a00610000005212000103580c0180d1514200000102048090350015060400c542420013410341c005207160051074541c40020035182c8800d8090300d00c0d100340da02096a90b101489481d0131100700341d0242c00030035041e2504a01a24002c805000e041d51924624404540c0074440c1ca00102052411255a03e01d01c1070784075003005059200d01031800090003866141d5000800307c0e4070340d6500c182c0c0025412811000c0514001901c400504624448401c0c0256404403000035030040c01040d040701c0d20715942c2c080715560b5840c44c3c080c890f007201c0100c00070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 360997473 1250 360996223 360996227
    0x901060915170c030403200124080c060c070f06020616080403080402130e010e01020a080705071113020409180506060a0f291305040b010c050604020904170a09030209060307080d 78
    0x142d504141b080c030301110b111002415042c155500014031010695403441d003c0c04240420305840451420701101740c031064500721040d900c17440100c0c0418010a00091110220a018084103003d000341e60011a01540c440c6402590b8180440e56078080401720101481c146001c0e541e00c901c41c13607143c0d03a0282150b0316070342803260102d035054900301c6850303c0d00c42c030780802c010a00494414010301000161540614403000349a444058050001e00004105210124802c010420302c40a03003a240e49003084031101c1c0800003403045034018070600d4940703080900c407800c40c0a03011030020702030070854010b40c41e15020008519154441d04d081c21100701c6040291004080c000d032148440d400601d5441c00f289248804240d01070344281100c00c0900130140550f280c00e00c10004403000a11748030161160950f00d0030340c0d0382005400139106141080000c2d00300000700348420300f0041012215038562001040203808101c240c081280b003440c0b034000250440c1030004101c4216003401001704001c018000b41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 360998723 1250 360997473 360997477
    0x403080a140414011506051201060f051615090305190801061b0c08031b07150c0b090c06040b0c060a05090304051e041103090f010c020606041104050901060915170c 72
    0x6100c2654032a02d01c1407011800017080801483e0b01c0d1200c0d40d4400311030504020894050700010184070b41451081041c2d9400310955211844a1400c040702d0318260070441c204c60809200031020349e0408140d0b108140d03001d00981011503e81c64100180c145a880c05e40300484240103380000c1d208030302699031003003905440106540109071050f80591034a0240e400d6a0006011080951190090741e00040c82085004010f0108102d21030b070a400d40003004041040a0402400c8019020b010071303d002c8052156840d40c140c01040560b030f6950701d51040d082904400c0e183d6180c4c0c00b4900c0010210203090043c1441a9006000f03145410b04140400c0007a441e0304800c4581c4e203844d44002c042c170f5200c034424101c0c03030340e18004865280c0c540701a12510700710306101c140f0020b0741001100590030f50001280d84d040b0b5000c6502040d0b00b1f407808244003031409030f60301055020422300d00010f0080e0b000341000090382c910058a40070303011004801d84007250b0014420326000c40841c0045e0b940c200102c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 360999973 1250 360998723 360998753
    0x12010c050d09081c090201080a050106020a020d0812070e28031e201c02011706040f060b0a090605040305030a0302090d02030607021b01020d0e040905070317030403080a1404 76
    0xc1a810902080c0d1480021303c0d0035403498401955580f2004255038000801903402009024103211039030400500940380d103500039009024098598281003040700d01015180e20340d8100c0c03842d03a20703890a2040203000d80c110303404081c090003a100c0011180d40c000c1d40142d0080f0390100034082103514547d5003c00844120741d08a0500410000840004109641a044001030303007001803d80300580b030400c04001f80604a8a2126079401e600c2c00050745c0050300c41c1401d0b00580b91362212030b81c81d500450301602340d004056124603c0c2445c003150500400f4041c02612003103941d214002911080c00f03660318031817400050a154020300c2207142552294008105008000d0084242c14540d0f9010900e00207090b92104c015804c88005990311290606031004048002d200410034031418220140424001801081c092034403001207909104d4100900c0004640c428110b82c002541c44402d41042d03001a03d046000520600c0030902501042c09044108501d01000703100307907101c60b0795000f90100c03060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 361001223 1250 360999973 360999983
    0xc0603021e0708121509010e0103030f0807090f030b01030c05010c030c1401060509010b0c010e06150405090a0206131e050906010807030b0616140f07030b04030c0b1512010c050d09 79
    0x11919001180d00c5007180a8010034045d00b40310b000c00d01c10441d501c201600b1010b105031010004001099000e00c030020300c1c244a0401d40629142c4400c100c803084010f400004000101076000410000103c0005048178099420b1000c81911100115140d441024001d00019010981c0d0000300301c00d5113981c203001c1c41c14000042c1c1296910301103008000260310444c00d0703039000700b010800c51000780074150404d40b909010b00414a0302100c44802840c1c0b50680b1809195103400084802e40c1c204054014260010607203034075407000740c075010b044da18280100c16011403081d1510166501c0c0c1044003007902d074004c100311029600d030740044404c000020803d000b0540c50340121506038995500a1182051842c3c541452002130f0503e001400c1211007068080d034450403503c4044503020444c501501e911400070642a142c5041c00c0b1554040e014000c8c0400913508180000341480300001c411000341603890008605a03d141a801ca641c071b4100c250200b00c080000006100e6240c0c8445c5000b4460 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 361002473 1250 361001223 361001227
    0x906060912030d0c0f0e030106180c050706090f030f0f0f030b030a0f0308010801060e0603030703050901110f0c10020604120503061201060e100b0721110105040c030c0603021e0708 79
    0x59002030040e01c01c3c1051131000325800c000040e01083e44004030701420b04055009200c0c1d9032504413010103000121004400301a82ca145041d2554450002c41e100c0d1a00008140018040c0e81003aa0081442c88011008110303050752400156005001400c1d40e05030301e4a40005400c15440e040e8003404500002540c540550713400400014131030004400414040c1da103a0b41c50f5070414070f1603421207031280c2215036003040000401075103940020031502086d41c1362402540301c0000360b00503200c00102105050082c01000000600f550b8000790b00800c0c80e07011105260125031070303117041c0d885940a95020741290680c0e2121640e070390107807004642066005c0c1c841102c1000e881c92840c02c40700b0980104a8503006142884110314203000d0220160551000c82841c0503080d5850445846d5920700c06451220240e01084005005d0703490395900300d5a03840288181d24052403c2102c1d06164002255468988032012036514424800d89038082c444070070f941c902c0c0d0310002d0001220f400c1040c0440f40c083c02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 361003723 1250 361002473 361002487
    0xd020a0807061b12050c0f04140a05090a0c0f03020c0307030c030210060308040e0705040602060a09021815030f070f060c0c08120315060f0a050306030a2102010b090606091203 77
    0x140d10400350180042d9a000040c2070b060784c025060380e00207007101084403420b02100300108038040c121070031034003038a50084050080c000841c80d82281b40e8402a4000c0000d8204500a1b0300b40c2c01c0b845840466548026031181100000c1d0208d02032040440c20703e80c401d00404c000a4010300060141b603000c0c1c01250482d510f0b40c4420002c1d11790f2500210346844002c10304001e5481b81d6060f503500240541040c40c1000c1c20880300940d600340c010410368109480f03281400540d111090320032800840304007039000f1450000725441e154a52070138080e01900c10841215030300403000c030340d03401a951118a200e049070718001044410b81100300003030300c050903078607400101d120301000b900800ca0340400039540c6924007604c00d00f1941a449504c1c5018020400035203203071076062400c0303503000c450750304240d0f07220340328100400d2030507001d07a0008003086000c1140724481640e0102c5030b407501010350f0090020b8503020040c0504c84a0680f5582c0c3c1085c414000c2c50344a01e003204134402d007a04010210390a0840d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 361004973 1250 361003723 361003751
    0x40b0304020a0e0c04140603060603190b03030412030e0a030203030901110f010510031b080309011b0c060203040f090902030a291e1806060f1804140c030d020a080706 73
    0x3c054940c003040d400000340400151040340114103004004403561410340c540280482c5441c4030060002c4800e444110081c4028100390340f00d01080d40001d0100c903200c980751542148246441c41054001c0350000000f12881c0c81d050040e58281da07805405542440c21400c010f4802e03100400012880d030281c860f1100302144240325803482568001481d0b80410b03d0350a1035205000160003114030260120720034010088008201c4000031400c0c03906078116101800c421130100c0b54181c0080826041c01c02c0011030945c00406042034950180001e1001d5560300030510460740e405000940641060500c178003c242101c0f5035100c0510722104030b0b038081c040c84100e100c0c404000c40303a0100349010b55201203042c540400c4403560103065070b2110100400b0740480030b540c4150042c0007500c641854503c00381140c9505103d00360884082c080005142020302e0803204030384212900c403201d0710500001d0030a51030b0005408105048580140030490707140c2d00c0300c65569002c0d000c160f50712500c0c0c0060200000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 361006223 1250 361004973 361004999
    0xc0405040602120601020a0b0114062701031d0a020f0103060f03080c06130b0f07090b040b040305010c0e0109091a060408060702010507090503070608042d0b010602060408040b0304020a 81
    0x74451880141d0314901d031001181c0c91440a0809411980200c0405000401041c04141520020f14580340f0022104000880600c030b4413080c0d2142c10700d8007050b1604403299460309011900c00340c0702032240b0a91200c1b01000f222010301d8541c080d43c80000c0110240c00c18150000d103900042c5070124201d0341b1501c0c0c104440000c0d5008940d0b00d00c0004422402d201c042c4103ca0304081d070f00340c941e0a1011507880d10b0800c04805000032907044100740100c0c6c0c59074050410400100107081e076080c0c40d01d80c0c40c00a0402a08148030a070b4565082c800300c88400e03031040005100410050b1125541c00b070501422900800c00409422484c040c00c5801e51890303074844020780014503da40040140f45001c0310000e0940310040c218206002c071f0b0302002e02540c3e50210b410400d803060351810700480d40e134904214900e2001405203000c0341454046141b05d81c072480c000c52030082d008514951144e40d17100412a0b90395411107001d408040b0900c010b001c0004100000c0d038100340000e10b51464192940406206a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 361007473 1250 361006223 361006231
    0x1d2a0303130303020d080c070312090b0709030c0b03100605070f06050f040218090304120201031b05040f0b090d030f1205010f1406070b1f03051609051f03060506030c0405 75
    0x7000036001d04004250741008402103da810b4a4502c099044c1024a03807203074081d0000060070f002c812400300041c0c8141d41c2c00140100e41080a949040c20b01c0345001e808203019000c142c51020420601051200b04001164002d06032051000300e05031800c0030071140c50700036403403c840320030710741458101140d007074004c40c0d02448500000401030704261041000501e0a054a00780003060380007040100940402070b1002c860300c40c0c0c6030340040304251004800920502c169010240c0d0342104c004e030566405005842038410307030881404260303141d803a01203050046001741540031119a080b040002d22800b9807210840142c101514070031520528002511000d8004000302c0899020810890300407507809106444140c40301d40ca01021a11101d070840b80c010600501d840790b015401c00d411915150b40401140c020082d140da006400406101c41ca44d644074050200c0e040c23102081c01d140601000781c030035026000a000c503032031441d900d580203042c00900260b40f50184800c281e9050311180115407103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 361008723 1250 361007473 361007497
    0x307052418010306150801090b011704120f02060f0112140607020a1106090d02041a1c061406010519050910090312140301030b0621010b03011d2a0303 66
    0x8401d012000107080303c820790b226500f400c107206141c15046410440c02815a0728641001c1100260840141c1c0e000c0e0010300191b00c1c00103070340200018461100304840c0d40f81280d80d2410f0b000105180103ea41e0001902c120081300e55900040004400800b803a5450030300c40d01825401c0606464180c0c14444111134560242c2c201ca50305030100b02904d403441e1540c52040b50840e0070301c0c40540121311405074014009004e55610381c1c211407425045e00701c4043c2145d0090004d40d0200401ca078078400c0c4041058112260b50a0200010110078101c401500c19101a0744440c1080d6201400508100c00c00c500d800a000c01000580201c0d1507105840015041949404003014a54601492000e103810b01040802c4004035104806c80c001008481c112904002056801c1d140c2900245014001a482410201924820f48042c3c4410b40203046d400300124000c000703400b841c09008251064480d07048a03e0f4215610002d41c10441560885000c0c1801142203086007030b04002c02d18640c01441341501c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 361009973 1250 361008723 361008757
    0x3100c020c03070b0c0d1404080a050703060b0303190513050907091a0909040318080a060902090a0b03030d021b10021e070201200a021504080709090203070524 70
    0x30301c0741020840300c40141141c1c6009458080f610000e02e483e1011661400200040042d110b0039170400c03142641c019052420503a802d9811300e00c1d0085d43c4084070301c4100c65003414150f07450030038640802a60b030750003812503460245c01600c079803c031fa06500c550007000411070301c0320012405864400390903101e00340300c0d203484400c070381000b00400a0000340201184c50000403c00d0300200d0301c0b8000b007550040da05052504404008100380e401030700454020744810704c5000c2001d0140001c41d0800c44c8440e0003503801d03582035140d1451020a590403041d080350150310800600b541d031801a070080166950508d06050301c0c68006c4149820322195409942d1919008a0b02c03d0101603100039000c3c0300d00055200b246804019030010b4400d140039500110748a40085110515680a10001240b658010041880082402070081c010342003801420028824a840411404001d10500d00c50300d40007001050b21074900010489134402d40350600c2116050082c0c071000450808001c0c010710007550000c01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 361011223 1250 361009973 361009993
    0x605190b03160b030421021b01230c011d240f130602040801051003030e010306030305040504020d021603030b01030b0a0e0403030c050f04090b130b060301060c0203100c02 75
    0x14058569860980c1e1094100900105411144021540846104071125503c950700d41c00d1600c009007000c044403120400650000900c0c60307001c11284686c1c5c20780f0750707008005000140111440d1120842520003043e44102000820f050603002d020890320210011580c07501c2000d0707003658656514440d400980c003100443c080720260702140011601050055052441c00a032040000c000c050080c08007111040012014084103404440103840444028042800c12403048030b000c0c101480142c0004603200d07801c0c074156100340200d0084a415503142800d2509240810000b5072211514582140d4200701140d10300b8105406111224003d840004d04c51038580009016030f9091030003036115501d401021b1018115541725260003682600c0c0001ba440c10118081e54540300d1106070710191040420009001d13039294004ea502440c00380c23403014103100495141c005940040c204203a00c01700034001440114803400b800c20b00d00f40014101d032004c6039085c0d81702040f5004040441c0c01078014512030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 361012473 1250 361011223 361011271
    0x609091603260903060103141603030f020f1f0f060905010b04030c060305160309050c0a0f03150606020c0d0f08210916060e0a09020a02060108120a02100b0402070605 73
    0xb4980808468a451125800a0b454074014000200558a0004a0b01e50683d007001100c00a02041203a00e0a080c2c81c2e08000c3d0803400c100cae800380c006104040d410a48820301184181c4c00300305c900030b0020708400e042d144202a00c0d01c440c00e21280c0356500400907210070a8040c16000707105010055076590f065040210b0080501d40000e000e2606050600541c0780074034012204500041c82d000610300d5040c5884c909000e809501240e0100680101041000c8405545402c9a21541c180180020000e100c08251403503481401c0243c2c005c14400140b50801a0400c01003d02c5451035120716040c0c3c0d42c841c0c00c00d8100d4524a0015000000079800340f60b042c40c045500151050024400da801281200c2107422803401013008120141201a8058640c4858103010302400b46003036481e8035409034002d40d5000c091240480521035804032034480480707e4100c50010b00907501400240007119442d10103840c180d0300c915005942000307480049031076440b03158015106078003203851a00203070943c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 361013723 1250 361012473 361012523
    0x2040e0610061101141b0c070b090a1703030711030d050406020a0e061e0d090b0f07081605030a020f0409020703031b090f0509180607022407080609091603 68
    0x7000c1c29680c9000c4001c1785110840c034400394403442c40744801840e00a0a6030410550040540006031032044000c0400c207803105134041c1a5500d0155001108a5501c8240070788140c500c5103405000d80040002c034403130610900d050184980c81c102100e1620304440c01c83c2c0c0440e9030440d800c0d07401e160b01040c5600020b90000c004207104000319211070400a5014055101c050b00204213944c41000141445026850ba00600c90054020701c07406181d141178281c00c1e074070b03020854100c000075440500180d402402040d6612800b071083d4cc5071400c42d03440208a070000c1d805910f0608800c882440002050038150000305600340c460382e40401c010060210500d4003a581c403000300180b240303520081c05511003000100048517011035122030582c941044420b0840312200101803c2d006403010000700342e40010701d106038950b8029242c1c011240d501c0e40300480c12816a080700000b40180c001c1600c0e4900101141e421400c03000c2591003608903503400d082d2441d03a40d81b04071000a0f58a075440c0d1008c0d80314203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 361014973 1250 361013723 361013747
    0xb09030a0f140a0e0a05040f050901060603020309030d0e070b0307020a05010c030e100f0603080c1e011e0902120105011710060501020a0813050603070509040e0f061302040e061006 79
    0x1400ca402100c481854142c1d40128280d040821240c5203205038181d54502c00701e0000c01c80940100046258640d480014010403a00100c0c15800c00c0380004056100340b007200c0c031940704400550304204030258a01d0141a013554540517a00c56010040303042c20b1744030002d40c041e40c29074006051000d9546001425a1804030180c0c00b410315044000103558030114005103400d0728158001002d1214004c102c0007054035070009010010003041250301a100060400002000c0d403641c0c5140f003070243c03810741c00d032001c0c0d01031b601c440059909150980b4030660010940280300401c12111400705030301403421540243e025000380796512000d20702c00c020510260f20f504003209030600c03049040400103587c650381401d00600040000404107071451400000d40041c12000b1302040e90381c14058070040651b0086400c0c9882540b500c150309071108130018075400c8650203400603207101d40e15020b500d2010790500c80181e82150305c5500d850190202408000c0c41595149a2640c2c5603007414030051080011403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 361016223 1250 361014973 361014977
    0x5060306070c050607110f0d03061d060f10020c130b10021207171303110f010c1208130b010f060e0102060f06190305100507030509030403080d0b04090b09030a0f 71
    0x10102c078010036404202c1c03551000700d07400c00100d60300c51b406d241c52034505520b64a58880c0120100c0f400c0907035154010004480d03640010401c0280702c150803070034449081d5121544031401000740066402e0078403108243c0c2100e401900c80b008078a50114616281d0102d0b06600140d90b0064409a0301d000f04c0401701d8420184001d01c40c01e0103200c583c0581d44103070b00020740403203542c08042505030030702c5044610075030718649485452580c80c40c01c0d40703010fa813400c20184968800d82c1103030b5555200b42843c0c00c03d10303040502d003840711810300c6007034a180c031025012410820003000d43d0341c0800c000451041c003c164002c10710a11611b0420000c007014070031400c09045401c00d20500c00c12011030662a034010004841b1843d9550040d24840742058803540028010301500300344c01045021035004500c00d5841e034a0520072aa2007220680e01d034802c07800300414600703041c4020b9245251990182d800c001c0003400018031800d06848946a04a01f12170442180d40001083c10071541c2c03040101413242607074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 361017473 1250 361016223 361016237
    0x3120f070906080a05130807050a1e0809090c0d06080a0606210b070509040603050c1302130308030a0b040e0f0f01020414011b210e10050f2101090506030607 69
    0x80b1006154102c00b400700540181c0307400200c0c22a51220002e20001e9520107d12656407120345007a9858417132004003521240c0d80b02c400914507000c0b804501a10542c000d110614000d0300c1c0301009446000604408401042400032011211441c41004041d186400042c0900c0c4154507142d4280c60345600a0080103040328172401134460066402040c1c141e10292603412650340c40800c4410340501004244d010b400c00c64008240580801c007805107000c1650512400001c0000740004d0f8030032900c1200b41c110342000d0400110302c260000d580c0001840e80d01040c16160880060145e50480d084111250800104506505010481300081c1c0b01420300a504062034071114103070380d140e464081da060004c201c403050403102178081100b520542c0000400014440c0a58034616041c007102041d012604020341031280385425000091a1000d9642d00c80c070303103012074000b0800c6402201d08082410400c9030050f215841480c44540070f0079540d54009020300e0810304242c9003c4001d440907082c0001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 361018723 1250 361017473 361017479
    0x70c0f06080c0703020a06020a05180d02280308130609060e090402090c071b1505030f0c0a050412050a0209010e090726120702010801060807020c0d031103120f0709 72
    0x1c0e0056500480000c5810f480341198101641410601c0c41c000300f2140c03000a000360090307000b4020340131071403c400c802d600107071101c0c2c02d21001c0841c005020758070034184040105c9140060700a8030081400d0340200041036078940c2c5079441034210090002c10b04030200710030300c21a60700c12141402480b02e8541171946075402c10104c0d4100d0b602801c0039019440380000510031013200c0007100c4c09e03c1d42c0040c45815140260610021880c4c0c0d0f8050403074060111401740719000d00c00c1c402c0d41c1c0268204040010680c032150481e003403903401042618140b00f07081c000018800841040e00c1d80060207180a0300344441c0134030412020b01d005030030904503c0d1411041c0404181d0000d9402c05548488c2001d0000c819000039603055516070b1511001d00303110711420080c03072040303402c0541444ca100380c030b0380c000a980358441550410b00841c2c40500590100f80500c6071481c0002c0c440902c6402418840e003901010300c500f60440c0d2100e0381d6118010754010511040d04002032049902c41c1031468005002c6003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 361019973 1250 361018723 361018727
    0x71d0408070602070204091407031e21110303010e06090106050a210b2d0402031b1e1204050c120705040f15030b0703060501090e0402011101060503030f070c0f06 71
    0x20740354020b040c0c1640403410b0300454031039600103104c054010340c010a9528201220558907116800229000702e02c80c007843c0201c0d50100c3d40c8040030f540c0040095061600860502400010b5031201d0703081004250403800b07048c90034001517000c0e042c80c041d050424a0200c1c148038036541c040e44000f003006000c0101d46034440d444030403c0e01d684441c1c0c000441c3c1e008007240031006000201c00003940244001740f2140f11584060400c0c101101d240c40b915a01e05805003000300302d00044600e410032448107410400c20308540c2c0000c025183c0d00900b108211a520b02c80003440d0b80003074a0f0b0f5a000300c001001c2c04140001045055041c860485010719011112400c0d076880b003d540c81482d020b692103118010311400c81350007030f8271a00007501c03504036001d5076401d041c41580c0c03041da520404a4036041f40400d46500c11441c45058608080412030551140c0e03004650511240c40070001d15503894002081c6607909100400b074081410710955295803007424420610041984500d4500103c90801c00401c0c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 361021223 1250 361019973 361019977
    0x70503031905030702010608070603020a0201060b070b1605070503030a050921090402090a033f080f06010e040504030801150306052103041a0301030b01060e090f06031509071d0408 79
    0x201075141c16500d0b40c403050b000f64094134080e080707010703075000311507000c1151a41903000e0402d40300a94028040150358401c090114400d540000c0c1802180b07a0000d20100019804088203049611344030340b82004689420b0308540081d0703240b0011548600605c141d413003040140d0a40301e080c1100801e120807102d0089280c0f849480000e40c083c94020502903a01d0ba03600d58114020b54204022030a141c4a82d8480203580f600514004541900031241c000b500700172a180c0c04003201e140c3c0f01e04002d0341f00c08892200b40403008003083d0403c010380302a6a0b00d604c85024040c0654805c2d2280d00a5505168001040016242c80142050314003003040100e950340c68440f408850401c80d03042080000b00f1440e40c150b11498210f100c40380c14044100c00a81c804070000c604890081401410036605c41d0400c40d141c0482151307050b88041e020010400c0f013440034811540044c80103040710030740780ca00b2084d02e180d4601128204d245400a44c0f00300020b100c808200d07031a00f92141585019841c2c159200c1ba154 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 361022473 1250 361021223 361021267
    0x1030f0506130c020a061e050c0a0e012019050c040902090f041a070206040c17030304110301020913090c14091b040e01090c03270b0c0f03130507050303 67
    0x915102c0f00e01000c0c4600074400c0030746107900f014050003840500b5109912041c0c1d005280b036612071618000a10142c9154180d0703284881d03a586090340c0c0000100110360001607800c01080d250102081490b910108100804089500603030701848135540b403c089041c4041300744554061802d0120700c00060b41d41030380d095841f14110481c400c00b5251401d03c442c01f500003a11081506281c94148061a500001c081d0b2007140f040d5503e00d000d5840340e002e030290b0040345a22111661083c000314002450000c108002c40c64060001801d1030701c1807000802030001c21a4114034969995009414030801241d5032025043c420008410038220002081990358010f041303001309031051140b241d5044003001240c00074000c0b540c40503c0d03541c4a4171807400500b411006800401d282001c5030074228a070f01d81240c0240d110113103007211001c054490106504000300828186603003007016a44624038940078500070101c80c03280c071034096003034688186403080031342110784a54002d02000203400414010400a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 361023723 1250 361022473 361022509
    0xb06390c1809280c36110304050615030d0504060302090f1309060f02070b010303050c0a0203011103010e0709080c0d0f0204021b16120623160e01050c0304050d030513030f0201030f0506 81
    0x7840d01e14000c08006c2c0100c004803464101c0000501c000e21030002102c50042070944224140c03904100c0c2095510b80700c070301950012410501040002071301a5001d0000b000000e80f008201d0043c0000207407000301c110000b440200c0c0e541240350203101d01c52050111428841e001140343c562a525115100300051000038104440041c00303600c9090140f001c811441d038054000d209618113a048120260024040c00c1203900e01580003a04062243e5409400c4894203c0584100c0c07000a0031302030010f40d50f400035074801c1d064540d03c0005803202e20042a01c40554a0700a841042c41094030782048180c010118040c20382d54802d00c91013420f02803035000558803800000311079009441c41d40c40f454108070000c0c0441d12090030040d03d40002000846000155503840300c004403490700558041c090000c4803005c5500a020034011401e00617444081c2c2806401d2060810a4503103020201a400ba0421541c1c68160a206411541c240c0140c0d0301701c491342e000030b100d030780303040b05c0411000444d204030b60380 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 361024973 1250 361023723 361023809
    0xa1407290f04080703080711040207020f0105030603030c0f0c030708030a09120f1a1008120d05070509130c080a0603080702040b06390c1809280c 64
    0x110300c0c41081c101e5000701610001c1c2c4030315960fa42052003c4c1c0e0002c900c19201413405036454079540c030701407003154481340c0c6c01410195039640340001103415410041005030544001c0254820714101045070040c0c01c5118001050940e10100501d410290720b580290392551041c007050749110340200c0954141c0c0e400c142c0086e8202c0c00d60824410b031541c50b00b0301130701520800380e10030580384a8800c1c40b8422001c5a4140d0070309659011510b603103040e00200f03600340d000144400015100c51c0d41110340c02c110941f6001c0c0c20102e007400007540440c54640030800c4240c0d5065005803039a04400f01c10323403140400d0001c0050b2441d41c0c0f5025040d21540034001d00c60307a601c9189940c15602e480556804001c0c107107117070f0705071412a0903584080d0600b14500071784546c0b0f00b440e80c2885000040c0d1945051018080b604007540000f40c1004041c0007400403012405900708100e01606004400300b044511100707001d42070120740c18610059a41e03038111122640741d60f51010404810380101d810311102c02c4035005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 361026223 1250 361024973 361024987
    0x5030c0d05150a110304301202181c0317012303010e1603060506030a030e131b08010608070e0a0506161407050102060a02090307090507110a140729 65
    0x10000b022410321180380603138080203000c18082d000a0032000d0114100701d48407521862508074140348494001c10340064040c40c103813965854250054940041d41c900102c42c82100000020300102609880800c0c0c000500740060515510180b03442042d0300c40c1c04c0c241c1165060010041008842c0f540480c0f00c004011455035103620700754030400d10000f1000682c1c010600301400071825182510096800350706200124488e480c000c00d01c51003131a4036445e015840344038001440703541e014800290300010b076120341c1960960120807229220010039658205590304210b40038182c07520240c45842003003403007000a9150346440c40e9402c15101c048640c0754480b0001170001880e40848074000380711982d4040303c100c6210700040d803441036440076000c0c4c41d2a0f0f9100382a000490140b000c10990540c002c0004201d00c032107130350000350010118903042d15202d07001800e0ba031504140c54070454004104100b4504406410b11210b40075125118182c1e1032004d141002010b0401c0f600011691104001000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 361027473 1250 361026223 361026241
    0x705071a13091b0203130905061906020319080603120f090402162904081e0304050c0a0605090306181903050304020f040603051506041503060605030c0d0515 69
    0x38a15074450458090103241d102c00200d0040c1801a2105030710078004085101c3d200d0000c0255401910508803d418841c034042002000d031502414040d044004107442001081000514002400c0c131a0015070340c0b041906888110850700b050060300700594030b41400481c1d500890f040001507106d40e0640d881d0b01d007400440800d40f090f002c005a104d44000b600c0c18180040030101e112250181c2c010340c0358509a0464103103d44400b144c031805440c1c40310006000603110802a04451424005402541070200e010048076441510150307031035440411000303410f1500074030800c0580010f18105091000b600c001c02d40d1080007074950007001544016030000b88604214444202c0604507403500c03464194100075007558025501680201c001180844035420070f07002c0c0e80e0171070798017800401480915404800010130040c02150780182c03500045801d500d13629146802450040f038000610620380801c01d4039083c5030450b624051290f041c2e00002280001c500180b0b5090780302c203580b415079204281 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 361028723 1250 361027473 361027477
    0x302150a1d03061b09030a030e031b0a061214010e0f01050a14011d090403091518030305030402010e0909010b1c02013f140601090f0b07031206060806030d050705071a 73
    0x3c01c5d501489a40b080c0804d141c2e11240e12001d03560309409031003200b83c190261004460341e070440b454000251480c104800d0b48100c02000c10000700311000500c4880c111010300c0050001c1c1c0c013114407000d0283c203101114000300b050314014841141c0f40b011003407070b0101d5078124070160f602c0c00741402420140b6000c02940700c2c40010030140b0043c05108140303490316026107200098081d5000105285029000180c0a082c101780140d00c0600c084405030b1955504032182e6100410480c10066144803555964554a02081c010008100086030701d120510030b000744858141d440352004120311501c000540d07000341610400a0260b0989a401c90785890381d07030180c0c103400021400c12100c0c200c014002d0f4806620a8158001035042408152100c400442d907400c0726001c0c03e07420318810b00c400c00451340481c2c000c00070580301c1e00300070a40614009002c011101d855002001040c0c10f8010440c5a29051001e84c0401c1000d003072460a14a6039114981d890b030f03540c06003010504400d5444c903008907580c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 361029973 1250 361028723 361028737
    0x809071e08030a030c0207090603031b03020c0d112b0b040807080d0609180b0712090204060b0c0c0111060a0b0d02030f010b0109060c1e020a0302150a1d03061b 70
    0x70440c0e41e1620702c42c400600420080b9101001401880c8010a40c00f10724020f0303004807030b01075640581c41c202e481c0004a901c00a1401107040d407052806d0701200e5124469440c20003401100801090a41300c808c3c00702c0303c2c0403804104103210240145400703c561a0500880d42d41d049900c0c402150394620700350207140310b0800e002d07068200218500141c2e01007900b01da8240c1c0c12170282442040c0f030198031720b0030300c0ba43c260b030042c0381c42c501701f0002e0681c9100304011480f041e01d510000c100708900b50040781c00c0f0307042d6400c18140104c000400139803560f402c01105294490a02c0e01030582ca4500e01d9280c0c0b201800303009807400c0c036203404644002d56101d85294815070340050668180c8102084100d00a24410a40f2400f190300f580f40025450301401c00b42e0b0a0980211080f0f19080380010300120210344094103d91001d40001f02202580320280101c02000b0202030583c0e03075110f5503001030729400141c0070284101c07603080901400e6440120700d65030840d042e0000a2400781d84002e1003d070a000c1c0324 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 361031223 1250 361029973 361029989
    0x90503120103060218010908060411042003090c03030405060a0f17090313060e01020703030c050a050601030305040e15010504030b0604060314010b010315080c091807061e0809071e 79
    0x10010091203060740c005e00841c0118081c107401507003e01d0054501441c00c0c0b1856001c2d0300040c00281c00702d540c1008038406074000a0000601140300c2001401058840590350f001120210802070160030401a010000b42d0890086040514142c002081c6200d0120707d0401c000c840101c44034824081e640001c0b800d80c20303a80c61404d510f41074214a0741c0c0c0e0004102000749180010001552a0040c02094440b26040c0e000e8860a402c1d510306032a2100610004c8500c1d201d081000b2002c14410b000080c0a10f1003666402e03540c0385803e03401448820081c010429494001e504108140c0e04501241d003182d60208142c2490380d1843c0c00030b070050805900c040c080348003448585105a5041d03000c5204c84c0002d0703c081102e603c094005480c40c8845010b91012940500d443e119613180c187d0b0300542c800a90010701c09404c254a0707405003403402c13652020f00810040444541c0240760007141c411203c04624001000e403038a150241c0c0c0c3d074040791003018025000c001c0a0082d01803110001c0b000341c4004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 361032473 1250 361031223 361031257
    0x2c03090d031119031d13020c58140702030d0504180e0d0809030d02040e010e1303020706111005130215070309060f0e0409050d020d140d090503 63
    0x1040c2d01c0040582c02280807000200140d40c00101418002901c04410b17801502002015070380c01c0080d40258083c0103650104c0c0b040d102003148181c45001105101d24040d00c4040309039010301d001c1200841000c602200c4418414844100c82c5050a08032070507140c0d901e441980e004002d03260b1041c03407056600182d0140503440d101c201e0641c00c00300070400c4480c0165110665691400350204442d035207503480145030449500b000382288656525074004034100c042e0380c5084000c01c2c3c00c804a83c0f043c1d20035500440e50030010072100041c0b002445c2e0003e0040d00c00407528500d47d0b0000c0d00d03010345000d82001d114201b510b40c4540503040000a81d04000000100120b04000c4d43e02c03000900300d6441248a407110806242040c00e0031400c0d20360890303050b15001101c0741040303c00d07a0f00e03058103a011410044907524481c142e603254010105104d015001800650000b481c0003403c1000b00c0c6c0c600e04c14031488414150500d034501d01102d52940700c51070002882d804900e00103003944145112061481302c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 361033723 1250 361032473 361032493
    0x11805060a081602010c090b07110604030b04060f020c03160c12150606050405090c09010507060f0b041407140c03040b0406051b1209091b030702012c03090d0311 71
    0x101400360f000720780c4140e14441403141c0c0d03241203080e2000501c1d40000281c01d0141040a860000050f0100e18450381030841c1c6000c411010407000d8210340d00940700003030b100c030901007404160f220b980948659004154900100a0140e03a5070b0701c035820942d0b0410003041004010702101218000180c510802034420920303031400c02c0040c4601c80754940300e42d68901171000031214040d0b01180d04a51380034001d0089035680d9000803413150840325030075040c01020000d0b00b0000300c461066046131304000100042e080c8188040c00101c0700c1e205145290f00b000b050901c082250011803511080c00442000b65541040c58103107815401580c2c880014690003090110380b03180c02001134401940035004a62000303440420786546d650845204038005d2204000400b1a802c2c01c0b1a055805402070702c0440c004811003034a0300640e44102d5100c80142d5450314004072944160040c2030100c014420f21150b52443c00c0d04036034892144078411441104014444c90030540130311000403401c20103d05a5490f021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 361034973 1250 361033723 361033727
    0x6030210030c0201060f1d130614150a030804090e01090605090607080c040f05060c0f0a0501021809011503020a1205190f0c020a03050a0e3a11011805060a 68
    0x80d865542d4050f500701031000c550901030b80a0242111000020072040d5007285401c00d01e0072601501050f040f49107a0320000220304240a03402c1d5200841c0c00340345031071070704021007208106500301d481e104001c11001040494102001d440941e41501340000b034a10f0102007032401003aa21000521460801007000343c181c10210340d2511030141030b1100c45081e554034030600ca19104a00518420001c0c12100340424241000504002501501240c015801c10b4038121310b814a0b0720012100d60f07400140c0003150356489881220480303015200035541d541060411146540d11a050204042d03012505011591140b00c0443d41c848400d1820403241c01c01050018240904c44031403a011810152010300303100540c480c0711000d213035aa026143c041607a5401300c7d0141d000010300000c000900810080c1507884440c0420004070050001440714404000c0c501c0d0b81c403003e0700d1524100c2c900404040030400c1d114003c18240002d103400c00550f440c0041e1110104c80c103400280c3c11081c0482c82e0040a9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 361036223 1250 361034973 361034981
    0xc12050c10091e1403060c1905070204020c0d0e01030e03030c0304110604080c1512040f02030102210115020303010315050c0415030f0b10020c01050d0b0d030f030e070605091002010603021003 84
    0x1240e07105503c2044d04d890051680d00c0d5825030352025582810882004551422403442c405902145413651412601d50001000c0c0e8004480b071381c2c4a50040f4503441645500030050f0320030424282418040301152011070341e124040102081c143c0400000084c00700700380311b4004450303101c0082040707890b141c40e048107550350009540d01c607004440700d6a845060582c0c401c2607815483c840b450714019952103645004034161019400c03a0559002c1c040d070704841c0c542c1003031241c0f02c052082c1c03000c1c4a076151001115546413522134440c2503400410051001c210007091200b840c0c82490300201c0c00d0345401448612920581d40b0003120034810b46405c404072a030542200d041d0a0315242c6c20302c8407540381c20402401c42e04104849000d41d0101a035030700070354040c002509290524800008404100d03001003000e040104404800292402c5481c0e04070030340511603c4030b00f6000e1402400d08a0070140003510380d00c140451240f09501001c11100002d200350025005150302803c03001c07010344d080b10040c000d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 361037473 1250 361036223 361036229
    0x20d150b03160504030206090d23011a100203120c0702040606050a030b03060f1906050a03030507031416140322140301020909070309050a051501030c12050c10091e 72
    0x204510300740070611180f14200365802d4030b40007400c0344d203030441100405c800300700d02603000c072000440031f0901c0b03045070440c00341151082c10020022625984111400540d00d0003a496030384074540c41c40e8613800117a40042030f0340b1702c00d40403d004000d98464400031042c5000300c03540298031600340040401c9140d401805450540717803944040c0500d4159404154542302c085400c0c40c03598a22500040c1200044801e1814901418a000403010744072004518800344640054000c01c00000e201020180c1c056030611003c3d042030b08950405082e403400c0c01407a403000c0c1c03015050305c0d064640301c40789400a004841003031850415482e01c1d603241d80b01003590b840c42ca2044008003a61340d8803403002802c060003203551500c03006042080e940d5803800103030000c01c5a980287d03410b00c2000740150000c1c004000ea561181d0980100b04010361643c0b9106070341607400d070400400517158003060340002c0d400041070b04080b20304442209035200501002c40380d044080d03004160501003010714604a0041d48110019 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 361038723 1250 361037473 361037491
    0x603150c0a140a0c1b080f0c090609070806061b1501050f03070f05191a070203011b05030720120702030c0301050601090312030219050c010c0e0a0306020d150b03 71
    0x1550001c2ca20b0700e03180340100b40003030000c41c0074910b2120001d06880380c05001c546405016030a07281c2c9515016150207224140107131143c0c80390b1098649881d144040341c5e44101c0480300700c29103142c000b40c000d10401c030140c0b400340113800125910003558030001c001e49000549004403500510300c081d00303503ca0b000a10909005100c00004402181400309801040c2c850240c02e6003481850041803026920f090005a0307440ca009400100c0c42094009035294608001052280c54071130900400d070840d400f0115814000d030b5001c1080302d502d0380050540f03500000a050a55102000725480c0459400e244400c440c03d00504625105a54083c0d01600009000341d049071341120101c0241402c0700c1c4150398460100e00394020410010703002c001c0448003030801303207005420869a205c1020310034840c5030034100454070200f0080c5e0034074424800c648d003a42d05842c108080880700c1c004200c41d1041400050401e5800007581d018098050304140c43d113180c8c0801c001c48a6907a280000066081542c2c1926 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 361039973 1250 361038723 361038737
    0x190f020612040c0e091e010209060307020303040308090610060f0e04061d090c0109031b15080402030d1d0105090111060f01170703021c0203010f0911040b011b0303050603150c0a 78
    0x5140e40260450b51144102c080100503551201d106da068081554180e510f9640d0204001003403a210311000d5402079200fa00216140c0c142868003070a800002000c00760319034000c0e0104001c0c1c0b200c60303603200c1c100c074002d042c0f14140042d10b040469950250710406034000d820014002600418400c0c01e821000007000b588c005601d071303d03001c184c491001b860028000340404905001284c07484a102d0b20984035814180480365440c080b01e00000340944040c80401c4007401003000f581011f008a040000e100d02e4014810300f4a0400003401c2c3c40380c41c6299040000100b02c0c128183d024035498500040e8040c102e1300580303880391460000c00003d005050b144110f0702c020784000280000d80b2416258000d001c3c002c0100f03e00914078100403007000c1a6810364a43c0044507800c107487c07003141314041c0501a1601c034040b81c1c07010b200031f80d01d8512405040008030300041c40501c0c250400c42e41042d40c0b42c90701041c0f0791509000685132220600c21005034404400500c82c2c494100380092005040c0303516011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 361041223 1250 361039973 361039979
    0x130c0b040503120405211c022817030a0b0406030605040201091502030d020f0d02030a1d030403150e2107020f010509280f030f020a090509190f020612040c 68
    0x2c240750003681721795070300800e02c40030b0101060303003040c2d034402c9029140040354804003426242e00b145214440ea90700150b00003501d4410300403028010f07001c0d56465460804170312104c665034840ca500207181a03004142c0d0110115420b041d0311b420190320144024418042ca9489042200042400780d070220b0206000f000d000030148640003ea00f2a41b515030080c6040440c095400780c06944400b100d4080a2400c10890000c02424806540100301d1b0f100006015101004150246114510000056803061000300009501c4036030701c1c1f90000080c040030031105205c45440e07141c114865080c245030304541012a0104c0c0d00b0318040c001642c000c441008820004000560382841680107081e004106015004c00584000c060603084036818403d20030a41d030740701c403001c0b41843d56030030854407542c549160714198a4a20050310241c503000004102c2070502107071550313070b130218082c14642401d03038000e030324052020228608031076a40107805141d81d51091101c80c00160360031501180d550755181004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 361042473 1250 361041223 361041253
    0x19110f07230102060a0c020c040e0606130203012607081e190312090201090e090312091209220207060203010e090a080405040b0a0312030204150c020603040b130c0b040503 75
    0x350207110060f0090310740b980380d00c07441d4000ba203c1201120150b100d0b2208803219a11a80b08201c20b1810b03982c040c0036117042600070401304241c8048036500141c014401030284040b5039406500113500d011000401240e5100300a040a2031648005554000d056070446d42b520400d09000c81c0d54422402e0350340c03851981c00a1446e19400d090302600040c14031400c0c0128a11a078440351040740141001c001072981c0c1c010111100100300c3c0d4815040c0c002062071480a03910101541e00303c0702c940d0280186074001383c001c100500940034694030840511044400c0b0021000b06c601c00001d1103402035540d02d0791410540301940c400c1c41514800e8941c0000580400c20100d80c1ca500f0952089d40c00f0700c2c19242104000161200c2d460566100386144d50000010b41c250b0002d0aaa030031589000d83c8851810b0100c51415004106ca6018001c041400340c00503640c1c0411240d101307034443c501e0b2180d612000c040d8104500f020b03170014150b090b02480401d4600309240a0720031548100d007150844688107902c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 361043723 1250 361042473 361042529
    0x1c05070f081c0c0309180b09461509050406140c070b0606030a0204050306040f03090b12040b0705090607060509071406070605070c02030a030305070f050f19110f07 72
    0x80039000603003484081c0100030035400e06c2e80e40c14143d100d000c03441c0500c0310001507510105480c9504a22406c0409000139030307460020f030710381180304d030b0103031000d03091000d01c1e40d032080b00c030903c04869241d95015410341c00b01c0e190b180c00054414001c04000c6407905180c03480042960100b0410008a800c0001d401d84102c0402c4818866000c2ca204550b6100e200c00d2040c20340020304008815a002e203c04117060b1010041c6a10a40c061310b85a250703644e071800d01420505c80340d0450500c5c1e80c01000000e051185441115420640c0921845040d50320790030304481c3c0740618400300d81d000301c0c00603500c1d051110b5600035600880c10001912000e564a0f040d1103501048644000c5c0c000c40140418030114649074821540500282014000d0300b14036400282016900d04044002ca5602c0d4148821681d1000c82c03040c0b020200e080c0149440701e8040040a103018411441c3da0b030030701410041403070901c120a00115030001c10103d400d254171168140e43c41c0c200a0180310308012810340c800c0b13106484207407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 361044973 1250 361043723 361043747
    0x1061d1e010506070f02030c03031206130516080405010b0607081b2802042a120c082d07020f010e15010b030703060b03010b0d1a1c05070f081c 63
    0x210a1074003102c5c0e910031440c030340030360750a0368140210406074040351014001003801c22180c040c0c05c1c1140c50141c0400403410100e0741d6200030580f405c010004c1c1c1c1801d2200700300d4160700f5810241410341d0b4525005015101d14140c2c103802c400f02003402002c02201201070070054407011000a51b4110700c108007940c80301003a0042c51007211952104007107101e40d90aa100c04c0c1d0000e0004608086070702e9507040250a50110000110480fa001a07490360340003550352014880740b1401e00141000540c001c00c0b0402c05030000d04203074419840d041215030307241940c000e03400b903510132404a1315124801940310410380e00441260b500300b84203100241004100f640d002c3e4000c14142c81d2a0f400e0941100e66904014034410a040e03450b8008140303090b48034080d43c004e00303504800d10740c0ca0451401000130b954804640d8040c0d41228040407280d42d80e9803142c038424041c0c40407948001038141c104186000e60643c4046071142603850041419000810300d100e408100944070021511801070403501100096 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 361046223 1250 361044973 361044979
    0x507030c091a1e090a0b040f0e15090702030c1203060904030f02070b0c10111914071b031707050c06070c18060e090a0512030901061d1e0105 62
    0x400601c850a4102d10b40019112200d96071030911580c00c50190484200140b407501d001d01c049800301c032514000243d83c000d003510301e42d00b07400c05e03280405242500c2403d0040180c2e1410007000200d82a12050041c22102001411521641041c5201035200d6100f101e00080700c0c095004050f04521401c011680110405810303918955220f88041300d00c4030b50740b0300c2142103008044001a2001c2e41c0341c081c10100c503685c0c1c080c05085100140b81002c8401855030074002901c244001640442c402c50f032000010b400d4207000c1404a0300c6d2105c04098401d1380001400e184071040f40041c6d2002a110b040c041d80e11960104401644070526100c0d14082d020008059501ca104035500d0b41c1000b0b0040c0212520036045a07000c0c58036120600d03002e40785207140300d41a80e5141d0080188041d103016454020006a019000313144507a12515113030110710f00b03200029400040440da652600354007a400038410001092100b5400707030b0841803164025660098a07002208100546c58480d050071812a2002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 361047473 1250 361046223 361046237
    0x5010c030e090702010e0604120806040c05070f02271803120121060c0503070e0a210c080102190807080f13021f0f030f0902030307021201020702130b03010507030c 72
    0x7020482c0c03440e0000c141004554943c1c0400129450070010b140c000c91007009a008424a100f00003400340700000d0520f4400c0f41030880e0142019000012281a10380100c0d070b03c10100c6050010030303003980240403c0d00e4489502e44041600c801009500707400741d02944041015951a0301c2210360702d010702c440305030204286800400542540a002030b000341480a01c1d071103011420380f601c0d02142c0030a007980000c0343d40003042040d234550003c45540c020748101d03401c0b285941054141d038464410103503109900d43d00340f02540240055021103100810b8084c0007995152010740e62801240b040c0062032000c100280301041000740a0242c9900c60107002071140e07240c1d540e10b40309800303409000e0402d03600030404500c903c0340c80d00c0e041e40030040c50100d030719000710303801740020000c04541c41d040e100b28080b80b5108180c40107940100484400c0e0b5011a8003242c0c0a594403c900d00a218251000354848441c4040e207203000c41d103401903541001e040780200403035501c0352002d8050341d2410380000000380503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 361048723 1250 361047473 361047497
    0x1090b0114031810060302091008061603020d090602071217060409230105070f050304050303060d02150d1a0d0f06020f040e01030b01031416050d030e100804060605010c03 75
    0x1040950383c4411800984444010384000b00d03030800050010545066840348814825810404d40c1680c21110091303040341001d19001d0b01680300c800c041e219075200f211410190300028442e40503907198500e4524100105602c034945603000b548068001c85141440d4120001080c3c081c000d19110710500030308039549591550104002452500c8044800030701030010401100c840b94540070414200100015540c200303c0d40280c07240030f02e26170039410002c0c100704001c0021000310603650051404e90300706110324a41e2001600346002002c0422100d1000724920300300b00b40b02e030000d603a44609421a140541100c03003d000d00403d148501410000c00d01e4400000114942d000345030f02210303c84154101070f192864014200005c2c1e20568001072031800500900c40001400c10120165200901c040112404040079180031446014414440e441d004024940148468040320100030100d8002074142c07400508071030340544080e10750038900b100200d0254028481c0ca5044c60b016122145c0c8665 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 361049973 1250 361048723 361048757
    0x702010506062805070614060109092702030705060a05040501080133050d06030302011e02190e010207090e030304050c030d0e04090c0f0e0f060d03080105041517031201090b01 77
    0x43e164243c2e0070000c04010060104400340308030300d03130400754005041c201d007020030005080a16036000207220501d418910055401040b00f80d17401482c1000075000104460300009040c0301b85640030035005034000409590581d48180100b050f61000d0b2550700300c50741c03601041201d58601c1103075100e816261180492000301949100c488030390305071900c0b07460505091040400e40d0460707401100540c0d12054030b82c0c204418200e1141003214050411402c3c401000e040d1581124140703849018018aa0305060384e9910a003d000042d181d0351400303000094003044203581e250700032103041c0ea49008030a8012928030b00130403104400c0b00c15a403100410080c80003008002c0c002d01130115804240d041c40000c2c0000c10b9a070032401030214513514034081c588128481e100010041c0b14510800802911000294200f001103054420941e800590f40502038031a80d0780c0c41403608600559803d4071003d5044c0303940080100306544203001c02c1c9500da44e03905984826200c0140c40302c2d001c12242e14038480060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 361051223 1250 361049973 361050037
    0x60e0a15020c0a12050a08011a0f0309010209030a200a06020c060903010e011523010c03030504140a05060604060f08030403021207031b050406050f0112020a0c05070905070201050606 80
    0x31040e8040d6a03a40140c2c1c2d4816205136900d400b4000400d102080745c0448641180c0f03418018001c0d21005810810301e1032200140d40308105000000d08030220108010b28401d6040d62010300c0c0180448002841d01c1c104030340c03c2e03c040f2100d6001404280302e0940c0d103041c065000070803160301c0c1c1c005020800b015401c001c69600206045609590b880d18030309084402402602c0000329828480c840d82c07801c02000060300000030720160f4110b40b04800100c81d80c1d900102c41030701d4940518000546440d00c0c503000351540010300129016109900e50841889404200903020b82401c50b0100f040654620b403480030181540300f040101c0d08103200030805424041468501010f403078007601d42d20f90b22540c501410a44220000340102c600c1075090255003880d00c504005880c0c00c81d2158070014200700003d1401c040c1c07002226501e078000c12030004282c0540c1202d04040e5001c0e081d90a4a074a4150341c10041104440440041d805d2001095542c18203100701c40046140c2000492691324501481d00c4403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 361052473 1250 361051223 361051237
    0xf0c1211121f2d060e01050a08030a260711101401051003090b09030d0c030e0c0d0501110403142103010e1902031911090d020f120303070c060e0a1502 66
    0x1400303848400f03410802c1410449071108098000200103041085890140505070401d0340560b0880d20b0500141400106941d0441002e142c1040b809411781c1e41815589840c1e000201000440c40500010302e400c1107600202c1c074190000c94915071018006001034450a003800c01f4440180001807020781001c0c0074030318107040e85040210707841d07405540c0c803130400404540c4020140c00104084100e1481030003004400780d8a460700348400c1040990310342d114030300001c4003403041071298400000c00c01e00390080c808110141441680b1140d682c00c100d44030790780f07403540c020b158014100b500500d500d2543c166a1006840c0c003404d41140c0c00c0c009071140700c00307000c0c042840c20b48160314111070a041500003984141500d0351038074440b55131805850305480740b148031001c5038039003440b14007802d0711014610508207404450380c1c0c035507900d404080348031074040002e40e14030307400f00204102084e600b15004600c000d10428003001aa640c913410603483d0344000a00606c071600320261400c01c0307103598020b0005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 361053723 1250 361052473 361052501
    0x20f150c16020f030312090705010309390b0702041b0906050a090e01030c03020102161503091a0403080613050105011709010b030a0c080705090c070f0c1211121f 71
    0x5003c0321000080c910f401c140e0401400c44401410040d02070418002c1800414003820207101e603203556030f94031a1100c40007040d03004c02c48000121491702201c051f14900b824901d101041034258950612242c140d200400c10782c06070b402c140c2c14818807040c8181000d22a01660b80e898815400d0450440b50b80d4410343c29801000746448000c02c814250400c05402144102e065540c210701d07501c000380c1490680c0c8801086401c031034504100311034820200420294141c5030004a450031858003906c15125000c0700307100d400e5448204010103801c1043c003806410203d4400c040d200030018240243c41c42405280e00259040d61100311044445c2d25503600083c0c070b00c00202c1c61010003400310740780406010080d9048440c0c000100140ea6062007100080d00040e6492402460907000c1900706104600008052035103e48030481401080c101040284c02151403c12620b803060420100e810300c41104179104c3d8070f0f08040c04007001d00001d80c8444180c0f003002280321301403101c42e500005050481c0c50101e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 361054973 1250 361053723 361053739
    0xe01030f03110d0518040209011e030905011409071211060306060421120c0c030f0507050303040f090b010905090612010b03010f050a05060312040e060d06020406020f150c1602 77
    0x20a48400e0111504500641d030750340e611561061803668a805004001c580218410400c2008c240d9012540700a001d1006d440a003e040c0c9040c0114001c11043c080500342d03501e0248000008201c100e4014060100041251801a1600d0747c101102e44100d04c000c01c030044251042115040200c06075a0100d4002d217428100703542c4105001480720802400c3c440c07032100410701000c0150b018034902803410b943c40e0020165007142d035112030a9006010103040c41c00f20681d50401c1040c10800500540405010750780c4070f40d625030b03003248494154010000443d04050381031240c0c2d480b90368500c0444074002d1400d03009407103610070701060308035500f8607407219500c80c807609580381c80c01d01601c002820391000000345460400b00c010116400a482d0301d00c05d801020540c100c215a0f0016a0140c40f0882c0d00600d42e07484800005a031021031140007040741c0d0021400007440f540215822110101c16400e80d001ca40c440f0081002e000c10407224009415801c4c0702c101c00184c460040601c4462010344205 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 361056223 1250 361054973 361054997
    0x4080c090f07021c1b0803040204050f060307120f0c080601090e0d0c03051e04141306030503090909010b0a0f0e0a05010323070905091e0f0d08070e2e090e01030f03 72
    0x30302004030860040d01c06c0c460000034002141401e1148541c1700a070000e65100e07504040b000207403074020314410700d01c40b80038040e9070b5800d000030740c0301803040781d03501c5105801d0705a81c40c2d400030340f00c420901c204c11080b480c2220051035202e0102d12001c450941c0d40c2c4030030324403006035020f4450f82c1003000180701ca07502d8400c681c1c1c6865610720003080a48840304c12450790088450800040200c2c03042d00c6104141003180030400104008103865100408070743c850341d10b90b5185402401018140006580b00f4500500014039000d000003140544101d8011506030740d90301001a0152802840000c02020001210051400f064100348554060701c0060300c078400d650348122001d89030161441c2035590040ca03d80a42c2e0b0043c003152110800488000d00482c00c9401001c68842403401d40101c00e0107c4500095070403440350329a41c2e0f050900520034500b0000c0494490103586507811401650035401a074400904d000c0c07034401d0111200c030100d0031401da003103603105108805e0114046081c850a80a01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 361057473 1250 361056223 361056257
    0x203090d0f0e0a0e041a0c1306020708070b03181015172523040b031204051509040c0c02120705031e0a0503040b0702010909020301030f030e060f04080c090f07021c 72
    0x1b9a0090400300b001c1e03615400184090845e8070034580c061002d40d8000542002200c4012455500311075002001e15202da581c41501481c21405a0b5503101d10701659110500030a000c9c4c1c0503003030343c600004014180e01e031500c2090600c05d00c00c1c07003000100d60258a4204984603c0e13680088400c014400700c50a0035600d00e05e01100300c240079105580a0441d503900207090600d445521a1018101d0081080d405000d8440300d4074420350103a2400b0b80300580c04038050150100c00c84900c10400f41003006900501c01009145100305102288a80c10000c00e620807564000386a0b0f040d01d8008014011034403050041e0b0380719504204056100340a980d14076404200144041c00040403000011036807104548001054400241c1003070002c3c81c8148010b00c041030107618108042585401c18252080c1d055000801d28000c0010004501400042c0890540c001080442e40d4200c29903000b81c0381c0d1110100103040410031121040160700062807180c00c201c0d00008107040480d80d041c444603103e412540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 361058723 1250 361057473 361057523
    0x1305011d030c010f0605010c120302190c02040c050408030912011503030906030f0203041104020313080f09091501081f0b0f18040b0108060d06020903010203090d0f0e0a0e04 76
    0x14055081d00049000b840345502030040101105003224100120780c00c0000103840750107000405003003490002c0c905c03501a07000b641200c030042000e000f1401101d00c0385c000141b083d03515040c1240290300344401c9107030041c0505d0644090300d8181c405907050000181c140001844a020065100d64075002e40e803500c003000d01c40c0c070000fa500a035110b4030340c030b41012809015102d012100ac656284100104004101e8100d08415a960225170150f502e03101c1d81180d20729482c003408064000c52000800501e0545150010501c3c40d40960f90840250b0710022040e60a04c0c11101d03075808100c00100241d440c404e03480c03c03180200d004a9052206a4843c0341c0055141c00040303900c40315010004451105008440c00480d45020480b4140007042141000074096503016210764019104071042404000700754040d00c0114a01900841d2a460046103d0b1f0f5a171490440d0752010038141c01c98458424841c2e03a40a51131000600306220b0315103811103041420000400569090420311140704c80e00d245450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 361059973 1250 361058723 361058771
    0x81803010204090c0c050f0a03080c03151f02010b010201060b032802070c1a0702180901061824140f150a090e10030b15030307080c0105191103130501 66
    0x2907010040e01741d61038401c2c9801c881c628452a15489000560002540084800d0f804903081d4022610b80d12003040a64003a00c02026031760740510300d044185000191000c0507051403030640d000744014101c4500582c200ca4042c02040541c02041001503401d0f0b0480c11140e0141d02c00340138810030360040e4540701040307803c010300494480c0301c000810090b248142d5060f440319080d8481c40d514100302c6500090109448030300324009a603172500028525202948180001c00c010140700313203c207181c0c1c00c2d80ca005106030403070141e42c940210b61103d03050908141301c0d82510002c11070f00038251008010890020040000360b0343c401440314400128440e00400b41c88032005a440d0340c0003445c1400c0040035101801450440e09800c01c400410108100340461504021114010f6003048800d8010034207503c18090302400711030f0300255103180e40c90154001486080e140c409900303810040a00801511016003080400300c9051002c40e071400c1e0300c8440044020310500002800301c2d094807a5881c030300e807208 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 361061223 1250 361059973 361059977
    0x10090c03150603061a0907080403030e121e030c1c02040521060c03060105040302010c0507120305120903040b0403032d0c0204140403020a080a02010905101a030a081803010204090c 79
    0x1c4400c0007040701601401317040c0690000c02c142101c0c5180080754100b03000420600c00c0042e10070200303007814003e9000c1400100004140c6100d40e2800211407030561290f44040329494116a0107003454060030144c070700505608401a01d405400100350507026148641c4d10300c5250300b00300000c2e4581d215686803140003070300c1e806c1c020f5664080b6065802c1002c01000c0d00342d4110200300f004200d81e030010481d07003601c0d42403e0810ba11041420123715150b0300740c00612103114a04403a40500d44c00c03401819581c0e0111030720a02e0741e81e845c8606c6032280524401c2c110400c1007480140300082c0035580e110034100d64031042c0f040074501d803134211032060314503000b1101080714499480298105401800111115000180310500b030076600256101d101e040050140800444c5860b0024070030b401600c007040d0064103c074030412080c540c4500810600c6801c098040e03590015040d9803d010614a040507003114001d03060003418000218281030800e03c459155508010100e8844210300c9024511903540e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 361062473 1250 361061223 361061231
    0x81204150912031506201e010b030f0a030824040912020c01090f170f060108150f09060612010204080604050303010303080c031308090a05100c03020610060210090c0315 74
    0x42c0c201508940c82d4510650b00c080d040d9000703014158125200d005040c3c1c1404500d0070700c1c0743c42468681800140394500c80d08945414035991170030300c150460409000d0440c29100088080308803580c3e600003400009001c14020800202c0004009443c0396042e44102030002d081900d60300050304070380102204540f56080b00300021662a030422500011081c01e0134864012420100303c41001100c510409854400e03200606061003020302800c0e440300b0b0041c04440340c2c9c0d40c4866419803541e0b200100e2a0043c5a101c000400f20071101e000075002d0905030300130b059640c5581d42481850343e50171140e83d10940d001c100c001031a03a000c2191501c107074000e03001341d900ca505501e402403000340f024000c0341400784140207000a4240f040640c099003580020000c2d0796008401c01700d40c40a0702c5910044d444000032104051aa0704aa004441e680c400c1c2c1c240c40c2c0c00c1d030b640c031885012404180904c500692080c11142c0c3c199030942c0c1700e152814041c030703156010b0995a03034803030050410030342c0c81002c101d0319 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 361063723 1250 361062473 361062503
    0x2160b1009050a090f17070804120627110105190e090702010e0304121505010602060f0612120f070c08030703232505030c15060a030812041509 63
    0x710344115500100e0105043c020b00885031158200300103880400f8140101d081420000e00c01d8070000c0b1813a41e80c1c00750116803170300d5807518041e03001883c0d00801c4e10140d04144010403da00c2000130034000b1031501017000021610703a20b030043c140b03482c2c0c2d04c3c4038140301e0208480e00c01029080c4d035503090042c0d259641070056400c0c20034400406000b070404c00a40e81480d40c00d10b4803040110599040d100c004080303008505d81820000c07040e07c01404010f140510300710001c030f401075003c244c4520480b4151003214003a104c000c01e00903c001c02c54440010f0f600004a07010b01c1c060201c004020100d4600242c5040c09040d44915800031a640d000d542c2c00d50001421004058214003900c520400944062030300d00101000320090b44541a0451625403105411450030072400c3d00105615030080201da031192409903125640301e52500c0820780d01700c500000500c040c50841c039041c040e40d0f4402460b43c00c11908440d81400c4150203401100d042d0307283d00c10110110054402c43e421580916803013204010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 361064973 1250 361063723 361063739
    0x6060305012906030103020108040311010f0906090318080d12090203030d06051923012001060f0b0711040504050a05061303030f021314060c030d0b030705010906021002160b10 77
    0x101c00b901c00741c0141c1d8284010800350382c0122405070f0268040c18140d42c2401d01315151801810307903c0c039002c0202e10b4040c0a006111840e0703c14120b1520a4503442c810f00c928010000070a0070794842d00d541c84d1300048070116803074401c80c1e4104001e50318520200700a40c0c1540000d045410a04c000c111040e990703241000f5526050b0100e0364010401105901140e007440402100605081040d6040d01e8412982c56200d9216440c40c1000d1561504484180220001300c00c5c080c04091045c1c48060714100303400b0841e500104103c0d03101c03c1d400600c00041000181c288005000010300603901405060054400b1a10901c4814130902210b006a0300b410703440c0c035000d007c440c00d0081c03181c0f00c1f502c1808440f010400d100c1c01442650034441c0d441c040d070841d0b072000949038801c02d0580a1035000219001a090346190000070b0b04207000c5080d12105900d030f90044500100342d00c41c02c40144d0080d01c01101c422115401019100021a48405140360304e40f654115010256120200c2040725a03080250b08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 361066223 1250 361064973 361065041
    0x1005010509040b040204090206040b0304030e03010e0102121501140d020c1b030c2101020c010b1509030312040809090106020a03081605070206130f08031201050612130606030501 78
    0x481181c4100c00c0d410076846580041c100108020300480e52000311300c0555540c0c0301601c00428074007001640e07a00e02440c000b08544245003090b4040d42c00c01324203544501c418001d441e83c60f00e181804840994501c1010310301c140b000c255150601c48101c4045000001503030041c40012044080541c1c1ca0030510032140ca440c410760320300305082c4a41c5807d00e0b130039540031510061614046420b007240003900da21964100c5010400740d440d5620006004003a4081074200c000160304c11a50f50510f140c1c090b00e0b4002c0e52248940103079041e001001454002007145481d00d8000703019510b158107252241c0007240071a0001c0e044800940d214a6000003016442003c0a60100c80380110032001c1c5401100a40b0341d0003050b6000303204200104482d0a03841102070584000e0840c03a600020036595414010780302e85c00041520324403082c802c008030319030034000c0c02c45418026010742c80b1015541e20000550035030307180008803041a280e50000000c55424024004285001115103403880c081c00d80e100790341 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 361067473 1250 361066223 361066229
    0x4020f07050721110f010e0a1202030f03070305040e0408040504060605121e0601050c0c04050c0327121c1d010609091a0702070803040b0703090801051b1e0408100501 73
    0x240d4102440f43c001803100310004804460076130302c08912813400c00050307444035101c0182c1e0707402c00071408002031140002c07100b006032280250b00f80c0b50b0148420740b0a80c0c90307201c0d600003d008030b44108020001e402c000e002c23455000707015440346800c00380c540001a003500c040da885a800100003180c0f0003201c0f500036205540200602c1200b644d000ea41700303016440400e004080505000d804200007101c040280031856061100500c10407581ca002202d01180750000e6440488040b42c8400541c0504900440c180071019208010244070841c0710681840742d100200c03051000c2190581c003101c0141030b01454a00072070480110101d0340d0300d1034041b421101c2daa07000c62006410b0200807000308003001112410130700111024001580c0350341c02a854850940d02c51100c1d8400098001001c082d01e1000c1d200051103540c0d81413129544442190a0700d2059441110101101940c1c00d40d03c80b404004145866082c0d041d0740d2402c0200340074103200c3d0025400010f0b240c00c0303404041c00d50110340c440c02c0c5c05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 361068723 1250 361067473 361067519
    0x105160b070e030d1224090c0201051608190f0510030311031e0c011803030c020d0809060a0e1e0a050105011d040b0705090d060c0201060623030604020f070507 70
    0x10030340c03650800402c4803a604008a8407295a141b0400407081c40d00d03528140c01c1c0b081d040100b006c596075008040201400640711005501e0480410080b10030f400c4a0342d001207255552403a80d41301d100c98820968401c52080f0aa69541c5e0401006082e45008440c0b0540c1c0002480d640180f650401525190480c4040c117881d40082290001170502d13510070075050200d100005854041e06003400d4010006401544900d02081616008141c1d140d0000314900085a0956518420807041510480001d9440c15031a0700207070001411080980d02030100004903008680103100060402c40280c0400d02c4200550b03044812a001846024003455005080707150140706071400001491041c00c1019000405604080d008030303c5540c8203000351a11030310010310509500000c0d00d0500e005090303504c40c0030090350034a600002e500d4010fa402d10201c40100c03603070700901c401019186207254801065540d200c0e80c00c1c0310101850341144050071030781c0c1c800c100410b03040381420721080c0816220b10700720007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 361069973 1250 361068723 361068733
    0x516080d141605070f0509011202010c030e040606050909010806090c060d06080102030c0912120d021317030304140c1809010f05090610091112060105160b070e03 71
    0x441080002040a8004101d1420708070395401c002022030140305030341c078045480e81010180010701c030010800724200d59607910398181840d610014040c000b4001d01c528044c0c91001c49079480954056a03d00070424840c0c03030801704040382070f00018100e40880e0484800204080341c2030400c0d050a071449405402080f0091203549010004d096035001c0f6176004602445002c28001c203481e80b160024405052000002e41d200d2501c01031400c12500b0400c00300e442104a015980074081010401e080c2800e50540418505020140070501a40c0300e441103d94007130303044800041e994541e05543d03002c040d00d5005035580382401d0900010304901c1d072a10100580001200c10320958502c4a100d2500c440039440c030001c2e41c0c403403101500510302d24000700045418841084600329011404078031490280500841e807a071559211012a6803030168800902020401c0d9007240310100c2d4180d50000b814540140381c040300e10310210340c01e440b000c000c5658103a0b61041c031007016000740d868241c0c21807d400500c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 361071223 1250 361069973 361069979
    0x10f1b0c080c06070f0f020604180213120f0b22060f060f0605040303030f0605040207030c0210050f0301030b2d0702150402060304151b02030408060705130905060409120c0516 77
    0x1100064117039030000c09400038548203a04648604c801c0d9401095101c84000104042c031126070080d620151106400c0d1001100c0490b41060300c48040c0c0d10300340c02c00003408109105a0b04c039181c03440013400807224100701c44400784642c0e2991000f2008940b00308001710f000001c10040f1029901d80385c0100306142d03403100080c4001640030040d2800c4035018500440c2c03e41c1d100e001c0c2401018250882038205000154820a041d080f00714496160b2080d20b000b04207220104085a040c02510507148111038200010008104848880f0340c2280c100110041c680005140c3c02401400c1c051850407100340880c10000c3d2a50148080001000c080203640030500e4a5030014565100040008115000f400200800135202e40e2150002c8400d4940001d052000c0ca20065a0703038220344522030461180e000000d420703600ca01c0c10f4403502c1501c40c04c004965414204050041c1070010070b4260804d41d60042e490102e01c1a0080352400b03400e544904081075000d050080c200101c0314042461601c00620070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 361072473 1250 361071223 361071233
    0x150b01120b01120615090b040b1b03120f0108060a09080702101e03090b06030c062b02031503010e060f070c1e0302060f090a0809010f1b0c080c0607 65
    0x115a19004203000051604100780058401c01442031036611524a4a2800318608400040000304440310ba19011082651034040c4070b0144500d014909901d2428064035010300702c04150407110848160542e0705000b40011900c001c01400c8811446045140c401000544014482c00d0b170040070001c1709211840042e2200ca44902c216000207008008480d21496090311802040c038145074000202803a40b240e144008014102041080d6905111a00441c00600d400650502c2c88030001d0481814900100b0720b0109a15045002e49014050030312050b0318142c480c8001d40c4609811541100f81a00d0750041c1401c41d00616032800e9541d1107803003444081d482d900c0c020344c1d1100951034200440360301450008044c4290402c0c0c3c10310b00490345188010150042940340c410b041405c55640d040e91018005950b1b409091300c05440340f0070230444ac20f02035100e815014002092030810403041d40d01c41c8240d410f0601a05400d441c1080308020074401d0f404180040c1d100301c0c104813034050600000791a9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 361073723 1250 361072473 361072487
    0x1e170a020906061c0507031b03090f0f0309090905100609050f01030209090a0b0a020c060c07171602030a0b07030609021312140304030c05100f0203030604090501021b0307150b01 78
    0x1c2c10301c1128085484441814014807014105005030700600c940d040410015000c0c01c0030321000004c110041000690403032003880740d03800b210340091400b200305c0c00d40d0310340800441110200380e0402402c05004a43c2c5400d0380200c1d24000e105134020200c1d5008104100c0440d003d54005030011170034801803190244042d4845c9040d40e4045034400c011340c480542030303440e10214200080280048800304070719500598080c285528103902500c001c1e5070703910456900c03446481c81c001c0030607400101c140b0154030441c010f00034080c90010044041c040b10b8002074605070070a40b003200d5030030120b401c0146482d458010b6000512000c0000c1d0f041007002c0d6000c403840c2c3c034180196809180f0081040c0240480e16010320080e10b00030003502d41e0b03207407070f0b0a01d007140b000d003401124050151100c1eaa4401c501c5200901c010300c840754051801c0d922290104005032044001c107071065902403041e50329245840741807101c2d00c0b50705401155241c600e1b18000c8031034042120304a540514120120399240d0300505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 361074973 1250 361073723 361073731
    0x3060906011d0921160602130e0106050708090a21031e021009060f0501030b180d050d15050301110405030c03010204030b01120c1e0612050417131e170a0209 69
    0x10001840c0c0700401032804d400d015a44505407443d03100149042805007681c000d015240d0b48a1044405c9900d4084070071000000388210070004004100308004114031101030403030321500500709600c0e595607840948031040403107040301a18061103c500300f00b5401c0420290380200d2403800000b00c8500c000c0c069120340c02c61900c2c0400a41391901d410400401750b1264944030400c000070002943c40b400d0a880701002121850310340844000341001400c000903495054892594030145084640506840546441d108501d800b00610340d01140590b028007a101c0f01c8856003034541d0b00c82c0c1c5004200f40c980383e1034040380d502a0b44104024000314060b00c210074152848d03c0391b0f10890010f00e14000c0a40c121513400480091101c1e62018a5440c1c1041c850048030340320785e213600281062603004021a0000e032002483c9600c4122260203030f9442da4003401c183e0050510303002100350360300301c03406207060b0161405415000c5d4880a103d200341c03100e00c1d06000c415030300c0280001c9407144d0101c2e0000300098 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 361076223 1250 361074973 361075003
    0x5090112020906030103051c02070302090402061b123414030717040906090212010510200604140609121308011503110f01090b090303040503060906011d09 68
    0x25440310400c0c119804861192a0241c241c0c0d58944c3c1d02d003000e0307403150000341c00038480320422484d00c030019200107403090560340c005150300015201d0307a00b0846980e21485960381e1146551040150b520410300c0b16407902110800703c140c3c1c400701000104142c01e142c281e480d40340700c4828407800075081040c0004030034590003400c4484007210a00701d2855401400030060a10702c09080ca28030090000016008440e9a284180078064485202005a0103410710420301100b0301001004240303421040b020034444c031030410390651004107586017402c184003104103c4503807220050104120140020810000381400034014070701b44280390039110480404516417a00001c501c081c0c815147d4032144009016440c001c0141015010000b0250201d40c07006a903110b000980c240614104400c501044800503550b80d90801d00b0f28000540a80064200e107030144000d010204481d101000352078010018180280310035031610360f82e981503200c00c01010480050003010302c04d2410000804c6141c0d50641 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 361077473 1250 361076223 361076237
    0x4060219024e1f0b060c0f1c02100c03020d09050304050909011127041d010b0121021c02071a0903040e0103030516060501060509010e0301020403110d060e0703060209010f0807050901 80
    0x1040c00040038004e50b1002c00d0b404540000c14140203000000ca004480c0046400d03a10300190081000c860b4080b40c0c209500581c000341c20299103d0b04c075611080c09502542001424099000245411540400c4044400e64070018060103640740610000d540003841b04c00034026041501b40112071400744101203170760b050045105404942411181400d40e68000e00100422420078601007007005c00c0070b0380e0400c1035103440200f26241d40324901c0c0e9180c14001802d03848201402c60075500096001032824866603113014407121030341e590340c0020000030f03004d805c043c005209007800803400044054441c130443ea10400040291508008000d1304498050401079114400d03140e910180d42c144001c01480c445c6040004240b143c1c004d0b0151084560a90315280c185400009140c08c1b03214a02025004114124a5070f10500d071100c4e41140305880384001062a402007a02e41e40b40400316042240c1c81c81d00400c0d4100b595a00c0b485e00107407a02c1701d01e00f811240c20041009045841150f403614100042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 361078723 1250 361077473 361077523
    0xf0f061b050111070b06010318030816030f090308090d050403020f101803051b010207030b0604020912030d060e09030910030b01180312020105010b04060219024e 71
    0x2e41c080c00022900c4540e8a41c4c2c1c80007841c009002817011554540401d2500f01756030122524040c04044656158407100b407030340c4584400514800e03183c0035841c20142c5580c51a4403c003007c0c0140800144251100441418105185402c144000c242001000420320003000541d031202c50311b85002c070095035165940348401e0412152161070b08000000d1005100000040140000b011041402d844201348200c0700d0b8074004907251a981d10004d0421400c3c04041032152a1030b5008100603134000700148041412040c003141950840c25001c1074041c0d58441c104900e000c100c00da55840328103000076502e404401e10006802072400c00403101099582e100c0c900d8983d024415060f4444050300000d40007944d649480c584082c4040b080b14015403c003000001c001c0c40d803005030f9095807a00c1d005881c60b10000d55500038580000b1105036884420301d003900380020040007014404e1081c60040044004204005500f401c46401c1041d0900301000c041000001e000300c0d44800001210700410b1f11072139 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 361079973 1250 361078723 361078733
    0x1504030b100528080f06061002070312090513141311040608010617010506100e0307090f24050f0d0507030503030f1006080402130906060b0c0102040f0f061b 69
    0x5100c1d084903400c60f030154511091081800b140754080b003500c0f900f2001e140e031201c1c3c0e0f640c2c44155032004008603a01c81c1010440c28580780c41c0c4102c0d14085481116800369072501d0383d11403020040c26800105004040070302581c202820102c0c0854446ca60a00480c03558001c2c140000500501d021000c80c245a103001c10884030034203810480381d00a0041c440a5164426240240300701e100e90040d1904201e040020f1b4201070188074411000184a01641c811815040e04c0c098090b8240543c1800b031004042140e034003921628201d5007030880001400310254104c00aa1801004001820708842104001e15920750465840016091380d007400600c0c200c4c80e069107001e105400003001e5000110810080707006590003540308043e00900115082d607548415030302c0c030714141c030040d4012114140300300700c0d103203540c100c0c45107240b09607030004981e6990402c80700c2c550450303800c4601c1039400280401c1a5200480d081003d42466514088000e190031000380481c00040700c01003c1124544004080c07007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 361081223 1250 361079973 361080001
    0xf03140f07080a0c14010e1e0d05030c13090c0e010c110f0d080301080d17071b3f140403030f0513090204090509060f241c030801051504030b 62
    0x507070700070780e585001c103c170b034030000d0180c4294004105a8814100240d0544840d800e0380742440401602030100c44402d01d2003200c0c00ea20013030500d4000300040120019080d103101c01b62005080c2e81c1000100307101b800f0740c01801205814841810056140081c1d804100e40d0140d041100a0440c0c0c03840042d485a070109009406c07180c0040d0240e040070000181400c40450810060481692096400e43e14181c000a40d03171002e81e91080010503090350204110b003048502c140c010301480c8400c00200a9081d0b40ba81204001645842e01003042e0f0003c0490100102c0d0184c100b0544c2001a00246803140c01d00c201e020f0740c8406410080b2000410303c2540c060000c880b25410b801902442c125159140a4080d600c06c1c445d0b0300c41e4503e004002040a41d0200d40c29010b15508030840703025440b401160207031000c0052458109002440840c049559010307401078080e070091541c0081c1841070705010340b400038141d021901070341224040034042e201d00001c80c1c1c00d032580844070b0285034454815460400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 361082473 1250 361081223 361081247
    0x20060105190806090f010e0f07030b0402040e030a0f08160c0b060402040315060302031603020d03030e030f2113020310020703020118050f010f0c0909051803070f03140f07080a 77
    0x15000b03c1041c003000704404903882c02c20201010007403000c0319004c60702650740c00c0e0803001e00c03c00b0b8120050910021350b1190505030490300042000c1082103900da042411a4044182d05010511145954802d0b43e001484198011184040c203019421180c9002e05245907100005018616000004000e6680d6034180c40c040c6400ca80305105003804007a0000c0200f41c1404103a210b84565901c0207810b182d00d91900303066130f03800f501c2c0303224540301c0396000ea01800b012601c010b00b5000c240106004014001c1c0030f01b040c016542c100c002e6084101d0b0102c50314610103484440100001203100001d41c6001401c42c814100c0400016a00d0499040807801840366000c0c018149034aa803541c2c06203d40040c2000040f000f5100030050740d03240741481e00480314101c061034040f50404a040001c410941d1211794003504500d4049031004500c90401e0865000270012100440040000001e00d40d0215541004c01036900d00c3d00e14104580c4100b10450045c01c40c010928580050961001d9103d1444070700c1e5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 361083723 1250 361082473 361082489
    0xf0b01030f0302060606180907030608010f0207110a08070b030c0c0d0809100c02120901030608151e04081801020a121e0203090a031103120d0605012006010519 70
    0x558407481e040001c5508400e0070380040c412400421102d2038080120f402c0d01c0b5110301100c50f0301d03403004240302c0040301c0101820289a56003a00188010082c081c20301e000f0408400140d81d80003525002d00a01e1440540340d0103501030017001c3c0034001c40002d5a80075698800d07030a584903511805601c005202e090110586401100043c0417410f400c00781e1240071301240310540301509005400101140c001c00700e842c00580c0705d0281c0c00140b03001c000007880c0b00101031402103451921118414900507040c2c00c62240d1900035020051403c03090041390101d246000d20010141c1403a8035400190f0181c3d040510349401500c0010703080b40c0c000c000202800c2d92186501d45034401008000e4007603101d01d450002d40c20188501c10180781c0c804000c540c482c810003000c0001c3c4504544500300c40921505400303030184502034012400b01c2c41100035202062421030302141c42410130000608080c05a816081c1c8401568500890b4200105809055034811703214800151190f800d80410701c056036020080b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 361084973 1250 361083723 361083743
    0xc08190806130510060f0c0507080f0c06040b070321090609020306100e0406050703270c06031e0e071d060307050901050603040809150a0e0405100b070f0f 68
    0x14840350060051449400d003101c0d04500c42c0c0050a16405503030301103036002d02c200d0550301c0c00d0003024001e5894081c45002d070700d4100313000191030351094903003000c80c1c01c040416072244a4260802400300034940201c5000c0d61500e0401740341600c1c011035801055402030500c00074501e03115120306020001074000d04c1e0340c82c091040d0b0500c0e04011004003800b2005038000e000c2e01000400da0408402e083d400c50302840b44030102c0381d681b40c40d4103000f40405043e0008141d12070400d4072101e031003070342000300c244008070900103031150529002c0c05002c1341ea44520141420b03d22001000d00d200208030384502a492004030f24030117001328144c10f100d4250080c0c040754080c103140401614442d84828864001a4208d803845a11030b4108001b4910074800c10b5803103401040041c1c00201400c0103000c0c4184040d08071180201c15001018854104070710440000e00d04000003007051a1074007840e03030004024024602a2420701200c206a03225040740907022007900c0e040301080003900c40800d071400c2d40225150b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 361086223 1250 361084973 361085017
    0x70c02060f120f090d1407050105011502060106020105060a030809010215270c0f0111010605090a09060b040b060a03091e110306220326010b090a0803040e01060c08 72
    0xa142900148082e803848181900000e40801508501500502c4500000d00011803c14011140c0341d0350f0740c80c12407850740705101000000d0024050103000c0d02602541d4880d65013980d00083c94a40140d011108580c142818403420349c8400360b8120590360000710942d41c4802c1038005070303e450490175105214081c100100862500910740107041d12034a00241da04080034101e08650f54030302d01c5429071340981014802c01c02c075030040c813000c42421550400030410603601c5002603240801200c6c8070401030b4445e042d07201040700e244614070010100712801c10500c10b212010540038040c0c042d0b080145a5038641e20030a0003501410200807440b41101c40c000d02c4990315007100445c0103071074194041d200c1c407404292018004000c1ca2004100302110b4221200161403c884e10b0b40940c84072000203003200d0111450b1103407014501c0c06005407030aa40d030360344045000c0c0300000c406a8440c40123a0001d00052200e8070b540320b00b8504454680c54907403a40300c3d840c184040305100d0f07030b4201c61b0b1080355a100c01c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 361087473 1250 361086223 361086247
    0x50c060f090d0e031518010c0305060108130c0e100512010f0e070e0f04060e06041103070602070602030d020a11190605010b07020306042303040806160c0308010905070c0206 76
    0x106101c1c48400041c0c6941c811081000e843c2c4003074100b0100d138190003808400d12444108800d0b10f40c0904564104e407450ba40a0380340a00f182c140d02c8800340002e850b02c1c1040310a50300010100d81042c520044c0c060b003869142c072850a0086280610358104e05103102050b140c023840503100d0041c040c005c3c0440118404e4410703490017080c0c140c40c0c110290f81485a91284800081002c40468007003070408011650f441140c2c0000d50401001281c05d503640740380d1600500e42c2048800d01c518881c07030000300c0c0f070426031040518040c11640a4021036118075800c1c49090b50100a44142e59124140035131501010103041e203001540d482c4a84441c07144140089603080c1d20440c000c4200c0c01902d04205590300d0301c00402c4036124101019426520010210f00055102d1054040c035181c41051a09070030800624981158029800341a103030344440d081c000404064048a80308501d2070400d42c89190269a000d000313080f051094141690355000007130b940d0f500800ca05c0d14610350040000355100d143d4420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 361088723 1250 361087473 361087501
    0xd241503020a0f0e04060f06030602180a0e0106020c04181202032d0a080406060b04080c12161a04080304170f0d1d040207230d030204210201050c06 65
    0x140c0c410620040e0005140200380362043c152075036140b1400440e961a01ca100203840700ba00001d09880d81c5000000c0410036038801342c000b00b003e0103000c01d13840c4000c07020003000c92643c2d0040c1c0e42102d00200100300c85600004d01c41041c04080c0c902090300c55240c07481e04a06012418007404442c09940800c0103540d0102c014040791400c094000707910000706003800d0101d0f030304541d1030400348403c100c2d04040e10f0040600c581d204d80715000c00301d10180c43da48000b04940041c1e100d6551075000c65511040c510304030080d60380320903240004103034a81c1f0400d240c07407001c6468494000503044401052400f20700c0391f01110003a09101080b60761b5180d4a450f170104041040e068840c80d4003d00010080300c10000c02d4004501e480d650b510079145250040c400303900200f030301c180d551041e401c221901c002200b400080d90002030382080c02c4412030421b0311107070610108520b000c0416104120511880344562840e1144802a0b07540c0b4a10329800e20050f2018452501300890511866081008880c1d003802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 361089973 1250 361088723 361088729
    0xa0f0209031e0d0908070e04140f030c1014280203070c0c0503030a020a03031107140706140304081801031e050105130603031421131e020d2415 63
    0xc40c0e0f180e4600d030708112450b040310b000300b028a401c110801c02c865060383c030b411034000f8002c2c082e951540009401307161400b04450080051070300080b500a40c20a005c0c0300514018802c00e4041c44411410310388a50503880c01801828078203004402024480b400750401e088be021045070840d66410100009082d11002203802c41d90003402d04c1d0042500d04000c001d80c0c40740c45454009140d075014a641c190084c15074009035421640c0e092002401180710b81c0c1804540d4030081015048140c2424001005080301500542c4400810803e00c0005040b040850300c1c030540440c0c1442e900d080410048028007004075003284180e220b52228500d08440e035002c28100c0b4402c0b21002400750342084041c055440e503100150204080c0c07116121221250401400b4214101c00707404080514854a04454081900c184002d101d04d001c0310805c02844004c0c2c440c0614001e855140e41030036650004a01120716040104009919542c0d034400c4080c51909954015407514103002c0401000c02c15000c03201948 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 361091223 1250 361089973 361090033
    0x2040f110711040f0207020d150b06070b0f01060507080f25050c01030c0f12091103010e070602071409130303090b151309050a0b090f100c031b02060a0f020903 70
    0xa0000c200d44d0f80688222074034103601808010a400ca00d0b100c4045804a80301030b010565150408800740d95100402401c1451080e14020503a007890404510003620503003000707043c40010001c20003c0746164054a0403072000011150750703602d0344400751904d900f8a142d4002c0036000003014504200022400707127500002a40c0070403001c503c502c0211080203200e06060045036141c501944602071903041800d00b24010390414039a4a03901000c40e00f1142540c640b40800c0c0c2040f501800700e2541480b40800400c8071148003a05600300d02d001464910028204686880d2107540c42400c05010f80c00030340c0791031782006260984d4588030501c24000742082940501c13030031070711030300807640170451140c0e02da40d81e003010040450800719610040c000002900308070300f0b032261a8581d074401d1000c0100d20f80014000c20086071010200e400501994001400d0b800f0b2000b00105107100554002031059200c009130801013080d9040d00000d00091023485005501b5008055030181000c1c006035460031340403032b90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 361092473 1250 361091223 361091231
    0x306061c0c0807032904031d01020c03030a0801030c0e06100503092506090911090405060607120332070302030c0f0315091e0105010e0103180b0405101802040f11071104 74
    0x203103040b0780c000d01701201c3c02404620000c400c1081100c606d081d00060102c107004461400c0c1003440000d1071038108002100001780b2000c018001c0090740c403005802070407644010746041c10b0000000d0b5800c1ea0a04113101000000b10010b0760755402000300d2030000502103108452014802d489540d20081801410041a9a1000003a00c2082072142e00810181d80e8850740c200790714502004081c0801030081903001800303200c1c80d00451a0b0003140040c070401038800040d6440031000401703e441e101c20401d031010f080b0706400c0100155941a8542c03040e40c1c3d20300141d40c0e60b00c1800c422558001c80c0c800341c04c3d128011042107200011000380109050088840840d19502c0c1200ea44c1e02d1a141540c072031104c04000d00400182d400350140c890398240504004c20b4a92038440040259260400c090fa1201d0601c0300780010f2020520942d1124008814140b00b0b4041041c1481c1d00c034cc81001d8020b01a655441d0050410002907100c3c05440c0c950080480d55009981000c2170100700c07482c4120b201d60304d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 361093723 1250 361092473 361092533
    0x161b0b070c0303030e120912030f030f04030f050316030506130c0327150b0d0209090d0f030219110a0b010e070207150e1c120f020c0306061c0c080703 66
    0x1000807a00c648990100e4007518008078401400038822303c44420900600c82807110405211030780d0003440c89540c1c21000141c140c60b0508006010056084d00e900c1480070070801c0c0501000b01c07100c3c4666520b807074107001c00c0585070513003c0b0b07842c461980c0d030a0f4481807802e84414000342d403507006075a000a140c80f0300703210340b4110500c24801c915103040040413424001c2c1504c80e50712164008030240c050080403412101c138a500451480f40d81110100c1caa500b060140c0c003081600220081c1c405205484c08504143c20100c0d1a0322000b0845c840200f4000482041502c0820811607030380c010381c1c0082c0c0f942c1e15503501d41c52602c404400350742d044054081d002003c94484c00c4008094030903c0a6503800101024400c288070252202c100c00107940408c3c0070700440468080746c143d202d096110766a104280002200080c2820840d400180c1300e60480c80a000040d6501c469204070306042da00344051054a5280078210341055030f000c1d0211b4050510000180300101c1140034480c3d2001900804c9191 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 361094973 1250 361093723 361093751
    0xa17010e0702060f150402040e041506080d1b0204090c080715021905210a030612020303040b0a0903050f101b020d270f050301060b161b0b070c030303 66
    0x10085488100690200f40000e1104c580003590341e800620241044064554010200b800d983c883d411032001030717000e00b003400208043c0894510f041101e0060800a86050102c03450311b44280621800030403425030407600d6964090210304c248654000d10811454090b8a040c0c0031111641c4908105030103000c000195071000d203211504003c00365800b03442c2a0f4540c0c05125080e8051400030f4641d84290200a0411658694002c80c41e686070040300ea140c80c1002401030540f42c0c107401200700301281089440c0140c070000b05480c15100700c00a01c40d11004071150071541c0d420745030b201130114070440003042903100300841e101441c140b20300710074000072a207140c079040410005c0c0701040040c0d0060304c44090951103000d0705141101d1507092183c000342c0701544044c0c00c1500b5000500e0340b4404440400031032409100302c0000300034030220107003020030011441d4030100c04c4000140a41d0b0304126004540d038918161100a401945500e43d11214103040483d02e90701d1a000c12000700f45092103103980c0c45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 361096223 1250 361094973 361094999
    0x154140a060f120503070210050f03040309080c010e1f210606030b04180308040201050d021308010e01050408030c03100e090f1b03250b03040f060c030209010804021011030a1701 78
    0x54009005516200d407a82c01d03c582402048c071100c0401038144203c50924003524003c0d40240e0103999180c0303109081028144c03c01021141050501404205161468581c10a6041034061001d0300045c000315000003a6150f55511078100c00700280ca820f002c082203400d500c07160545015560070005901224180012900c21781d200c080d401c506404003800013442004802c1d030081c4180341c05402c00ea50801c40c00c05a0700500000d000c1c178080c281040c40790040902c40c9421403d49032000780064140764565030494400580580c0c0b20803030000010740e00d041d080b040140107050007031800303440e0b00d031004103203864507818820092180030b1300c3c0000c4068811203821401d9400001c014089805140e0b65601c103a400102ca0440f810844e2031b80052141c25800185100368050310a095a414240c03801d0802c44034070340c3c0a9000e052040c040e00440c1d0360f00900c281d5200303905031000d5510b801f01c05015110340007460005802d42c800050700c00e40b026131080714003840d2203041c2a41c4075503980b1218038020300d13 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 361097473 1250 361096223 361096259
    0x1a0c090d06050a0b061812070e010512071a03041b23130903050a09060201051012060e060406061703090612100803030154140a060f 58
    0x1032821400030082581c560100741c1014034644002002e00ca400040b0ba9244c11410000031018499440c40350107080204105400070740800140c45540d00f8130110780d1802d401030103114054100050309068086040003041c2c00391006011f1048909520542201964422201140c20181121010400d40000903411042d00c035000341c1078011110361036402000309002001d4603405000c2050340304180d040c0d4842c0404090080da50280c0d41e15016401034140d849550190085a252100308400024a0148203003914141d10000c07a142d80300d0708044c4c018151218030041e0b18000c5005110412880c0c2d0300c0300d000c5881000fa80304691003e05207450300c07806a02c4115400c55010890b803900c40316106601035002d40b00d600034007155604c030f0300f060786075400c260050140e04403100e1090740010441c940c0ca0380ba61096480c00c88928a84c0036100d81d50741c4000102d50b007420990004030101502a0300301c1018090608094180d0740b40800304a07001d802c1c0d40c030401c41310040032200480c405100f00070715100b0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 361098723 1250 361097473 361097479
    0x31008010e0a060c1202070506090c0a0e150a09020a0c020a090c020c09060411070614150d0b190906150f030f110a0504020f0306040e0706020706120b04091a0c09 71
    0xb90941d465103400f5200d40c03407090042100580e001d07143c1e0049031010b0480d45004000034055850040002860000c610031400c2c0706140780c408c104044154080000e034045508d0680ca01400a080c010418030380d0141c100c1e0402c2400403a070b401402d50310144007800b1a008843c0900c81603641d130250384c1203900c401d100e10b006811501c0e41c0051810038a041d280c02a80141c00000c0d10b44041e4002021504001012605291250110540030510003280c0340c202c1d40c02e40c0380000f011f20800014042a4030036000503e00781d00c510024858a0f51402e411407400300000d4140704ca42840c0c0380000052a1b04650b8820341e4400070000304805405840e903009032507020320f280703446d841541c50b4003140724041e03000b03168880840600441c40b504c1c2d6001030f0070000900b10b40d003a140e0819008000c01d480142c4219030a43e480b111003001504e90005e42401100c00b00e00306101c4103101288004054400c80480d550010f003032051000411030300c02000c64129044800881141c0c5440d2140d1030503103c2c2241c000c0e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 361099973 1250 361098723 361098733
    0x9052404110411040b0c030d15090b0306011211032e1d0703021309050304060e040b0d030e06090307330f0c06020c1905010e0d0e0a06110703080f031008010e 69
    0x400c545016001b084103103c000c0c2241d0420b0504100715056a840d654460050701080808002180481c0214084060124041c1c0103640c100707505075040d462040c030301030607901940d00d43d51016142030104001c1909000381007140d04072800f41400700d01100c40301303200205240c0100d1003095421000782c070200380424000f8010311440c1d0340800024803121241560303626500ca421100040042009000030300351034468a9004c2500010801114070300c0000500818080d0420f0000a03484809500705050848045444841c20000b04c0d10301909900505c4d29032491461034042560b0402102000039010940e03188400c0f85c0c24800c07281401c2c1d05245c2004035100342c9801d030000c0c80c0d60b005002c1884030b0b90304440880d01c0c0d001804402c980d07840c03400d0310140d55403210000403074414030600f61035104e0b90030180c2815841601064030f4100c94490441000000100244840c6c0240301c4000115003100f460341d21810140c0003522603900907501c51131800000d000000c2c0d0f451042c000c1e20711001700070000e80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 361101223 1250 361099973 361099979
    0x30b030f010e070b07080c030c07050a0503210c0a060906020304060c09030f030f0e0303031003030e0f0a0302090402030a080304110f010903210509120309040b060301080601090905240411041104 85
    0x14468005c07040440b502102070260181042c0100043c7c500100244014100c051812050041035007140e0041c5009402c00900d5460341141c0c040008011100d404d400e9035105085d02140e4107004440300b00030542c41c100301281c000d02c80b5a401030750180d070040d8010010841045819501401a44001040307400440c020b0400b1038010340033003103000b0250401c0b01c1001e07200ca000030705542c0104d030751020090550506100740b5500880b00101600b003503030707400310b0605003000140b00a0400d02c0001d10500c0000300144c110f403818018112500c1c0d01c00c2100e600ca052602e804011220032800f224042e6a9800d0801c86643c403410300c02041b203402c034040c5000455080003180c45515103140d11018030404000800c440c0c0c07500b01d07000125800b40c00146455900c4c1c0000c00007641c0800f1441072041c007044c07005000d10180866030504449000f44005200c840b0b42c60924100401c442c020280c200560700c5202c100e0b01c010700c00320301c2540300d0000c2818401042c810003044850107a80002c904030140824 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 361102473 1250 361101223 361101239
    0x90506060a12151a13080102090109050628051c05130b06010201150603061805011a0307121e05250f1103280e0105070204020901110d030b030f010e07 66
    0x34000341c145070b807007203100c40d44809250b1601300e0310b01e42c00740500030009801300d000304004090700041c042c1c01000350714003041140000c1c0865490700a1a1203074400060425540c02c0c544066000c144204200504800d8074400c060090380080e60701c041c1a506000b0410f01038401880b8180c854100c1c00b84000111025071541c8514010040c4900e05566035604011107125031000484010130481d50041110341c100304001d0f096a84401034490510709000c01401011206400c207211b070062182465182e03501e0020848950041078800c00c1c59518000080381c0400d1104039031058680304000c00d0009845040c0001e85040d0502460821128080303440b1031503034494040381c024441075180c8408200403004425096500042031441035203000d810180c482c00b050405400203040074203085400d0015900080c00d28410580300902c100d43c0041e421038541c0c01280101c91503001d0300222200e00700c0640c005002406010740144c444e2080700c0b98403100c030505000705180c0320115400340214902e001d1803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 361103723 1250 361102473 361102481
    0x30612030806040b12010c0f0c11090c040b070c1d0709050402090609190321020d030507050705030c0601060306051912030c080a030501050a1703090108040c050316090506060a12 78
    0x201d43d101d03407550600c1e240c035500c244d061020710740b00d8000000d6004420f00c0243c84c2c43c400c03100c1d0f00140000d980110010420388260199641001d460043d050742d9110703a0030b00c0901c5103400501e100d0307e01094500c140161102648150754045030b01513290a0080341038084a0300031101100080c180080921007814960041c2144400103010903081031000b00000c1d808403411070100000710b004c1d11042090002d1800300752040d44c246c41650510054682000b900c030303040050000e061646030b401140c020391007542165041604030b003c0e0b988994070b07030342c0301602d50100b031040e04000303401c0c660b01103000d1405900c0c2500141c8aa15504140351500390319a448100d07445d000c1d4140400010610085003a02d001000c5100a40d500000c0310740c104010001c2100c601c0e08002c100d02c80c54401c06030f84040000c01c55004800c00d091241c2d040d40e8525281c3c0811010750011509800f1703000008a03c6100620180b0a0300c02a240c02c0c0708943c0c03800b007880b2260003680140030000355009111000b42c0900d0788 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 361104973 1250 361103723 361103731
    0x302010c1403130c080703140706030b10050c1c021605040219030b0a030b04050d0f0f0f032d0c0e150a1b050610150309050615131109030d0306120308 66
    0x740081c1358a0b614241503043c031100b58403e80703040302d40305500c51071844c0604c80c1d6409864107040811902d10340ca004a400f000c1741c1151102400070000301501c6070041000441c03c001051790481d40c1080c4104002034890601d81c03176510046500308800700e1989417034000e07161604c144003224000c05014103011400380450707020483e0401100e16000c000f0840c40040140b080e4001e0b8000d20060542080007403400b181004c00808000b11110032414455004010b0400d01a2901c1c022035152842a0704a54040c200e070b81e02c105484401c8510226101c444d0440560f0351440d48803c21030040e10700600c0380d1079850504034240380c20104004041c560240710300300124013a82c401c5181406080c0d481520b4110301762044c0005140d01481046040a48424002c042d4080d00c1d092000c0206a5501c03590350601500352800d54040c4c40440703038162101e5110314001c61041000780482c11041541441607032100652031f0280c0560110700000e00d01074022041100d01c03030828100c01c0b80194034100d50400c3c000e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 361106223 1250 361104973 361104983
    0x212070b090607080c0703061e060f03080d140403080901150e0c0f0d0204060305010e130c030312020f0d1407140415090509040c09060f050307031b080601030f0302010c140313 77
    0x4440390704d03071140400c1b032800603610030000040c1c415010200c0c01d02c0070416080340750001d41441030038400440300b001d90030112580410389989511060b481d4a01410420b041c00c45126036110800c0245036002d0845805200088000c203c0c0c1208141e04401a4480e03024403007001c0a0100850b0503504440000c00c040f0380c144050f5420b281c285078066090768025880040044d88400c0107119250822508076041070304c000045501034051f0340d80d900420030600c4080e0910150100030489400d281d0100c85926043d90f0b07103607079910918417200c4014191042040081c9404074001000980108040302030030340961a1241003c0c5040e0404100329246424282003064800c00043e50340c80d440700a074022849542000a443e090110344400c890070340d40f04006004070284e0400441d1404500201a2071704228460601da212010b498402c40c0164031007400e81c80350000000038066404a00c28074076203c0d80c001c0c0020a2090002c6a41105070007a0030040780040010481924805040307142581c80b41c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 361107473 1250 361106223 361106227
    0x3240f0609140910030b0c040305010f0c020a0b0a060512070806070c0308041106040b0d05340309170304030c110303040f0b09010309052505040207110105070f05190212070b09060708 80
    0x341d44c0c6800c4146c0c16103211080fa10042420f000b0041d0030300500901d48510b65003000400a825030084d594500800041c008070400004034140c16501e030082000b41a0207000300c98401001502250b40310f16512491240380a00004940018814103400390340c1794050b0394a01141d2a01d0300c0350b06903d00901c0c912640320b602008000b448030901000b400041603140000503007454088001d00c0d0910f64032040c1464201411404200316101d0a41a244a11240340020f03969103140f03002158206c9010b0b0902c4a4040407013008101a8400103c080345481108484100100b50301410350b24004d50007180062040d1b110103000a6950708054909480145000b041c00b0050780c54040c24080b00443c131030b0b030302584604c40701010494507118a008120a89003107203402c2280d00d0f5a40041a002540f50403c00001510400d10071806200308403180c02c2016281c2c0200d035015107403032592882900320300a05040100440701743c3c000c20040e00f15115a000c280c030700075204040052591040104440390081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 361108723 1250 361107473 361107479
    0x10050607240903030219080f0a11040b0c0304050118080606090c0919051c211107090906060902130620010e0709050907060c03030c03240f0609140910 66
    0xc2c018506164060781300166205241042010b90104000010f0140030108050200280041080707030342c480250b03240000c811100c20504100e905ca20781c8203950300c074000700c1c545400c01c0011008004841090321080b200c590228450000c8803414031440c0800c2c0c00c003031700103552824041180350303200f03496030f01080c83e0120000010712401c1842c4c000b003100c1400c0440500c0a41444841035003040340c20f0082010b10061965810346e1495881d00002141a01c01010321059018948803404c2000d070b541682c880e69280c800c03030001419200000d4520381e061a5001424118610840d0700d641e03d210000003015081c074000b903900d1080407107503480d841c80c000e028201072032081c401d1420391240c50003e042c50900d003a0304c0340160b54000d401802d05401c060007c101c42904124030300c080307a501d41030100d030498101100f90020049082c044c0c909881025020081e0b5082c562030100782d0300c00340c2c00c0e02d041c41e480ba1700441c3c40c03902e0740c0070b0b004114079080f42c41703407081c42c000040342d5002c1c904a180205981d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 361109973 1250 361108723 361108793
    0xc03020a1103120d05070327110a050d0b0f07021515060c06010605090102060a0b0d2a03140d020c1e180a0e0706090f030206030a0902030a051501121509140d0f02010510050607 77
    0x5202c0c1c0e058de442c0f0311180a21405118440d051900007840b0700c01004507150034400780118860140a04019003000d2600780729035110320b0180c407020440b110030748403250f13500c15025000b6032104003e50b0060281100013a0740d110301c2d03c250010580c0c040e2104a48541941c0d03140c020318031402104000325440c0f81e01012109404c254540654030070810f1b81c0d14032040b15011460141400c10b11000d6400850840c01e850f01c440e10b480c060501c040f41444010041d080100314000032801e0342c590090180300401058042c0c9401200001c10800c0c02c5400059507603e00f190400743c42d0080100c2204120001c101510388440516003000240c140000c0040885d030010380303810702020301254107403c40c080100381890307441010b82c018009501c000a010b0b40540e100280500140100864181d852501c01c09202200029901c10081c1e00220b40d05412440800342c240912042034900641c00c01c1d0004900030002d0150100b100c03c0a0116400c0603855601c2c0d016201d00c42040600030080744407144480c41d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 361111223 1250 361109973 361109989
    0x6050619090e0a0501020c1b04050105060331061409060f0c0d14010e07110105090a060f1404031116050a17030f0301030b15010c03020a1103120d05070327110a05 71
    0x30301010700400d10f500320104000c08440807007071214840c0380392000401c110b03120501140c0e80f200800b04140c00b409010000c00c400c401cfd900d0301d40700c04107203035131429410029981e00c00711000d4070b5114060380310b0f59a1003801e17a49450403607000c011001c0740d0300030600f0702000c00090171000e01e00351004582481030f10090a9110740c241c0c403181d505002c183c00e000c0c0c0d00d5000044a0135100b50b90f0020700c0039103051074945903241c41200e401000340e903451514111404640d881039031146240d40840c1c0312030806060051140e1030207a01030105000d40301e0b940382500003080b600d508507080682812826440d00e001840b1480d4403d880c0c01041c001003040c01591318484001b03502075842003460340d81c2424410040c81420703070340c2e1040c1410312040384030040209800007010180c00798800e02500c4030041e003101007404c1c404052401c0b480e8040100303448032400016080248107003640e81d01001020140300c6c220304100e40c10044921a4405c0c061010045801b0724800b0307800a00c06441c0000e103d5651005c0f030080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 361112473 1250 361111223 361111237
    0x518010504120306060c03020601051e060d140c04030c031b2103020c09150d0c09060e09010b030c06070b0901020f040b071a1b07020a2106050619090e0a050102 70
    0x142c1540100d0341c142039010311030280601000d02c0c0c60302090b40e0030f650280d81c441c018002c151041000340030800f1611001030001403652805270486072600640742c240030140c02080106104052200e0008209101d1310090b40c0c21a6040500041524650740302e43e591840801164031552503010f60202d6101120f260800064000c2c04d4800e40e100d6036404c00a040c01d642600482c815100f0105100c01c1001014504258910856100c13a080030980340880c1103d4850307211000082c1018400120701010540c01440360308828000e02c00010300700708058940340c041d0049680a2010302c04080030605260f80c0660003019180014038007910075a0000c0240c005504c450529200003501d141000108100300080410080701c103e45803c20014030341c41c043c0070b00d81c0300001c1c03140030403003405555403040003200400202e154400b07804100381e1402194940c0308000e644803810840030403850b0500150003200d40481c248050591030405000001404003612400c1c4103114546040011a2080c4020301c48 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 361113723 1250 361112473 361112483
    0xf0d17160b0702100903120f1d070501090504020a0c08031005031e0f0106080601140604030602030a0509060c070b0c1b061f08060610050f070f1a0105120a060518010504 74
    0x898609001e009242010301c04c0044066810b00d90400002a0415000c401c1040ca40d1004102d44142c00071840c018180190b0f22000b58406002c02c035410403000c680a82902c000b82d80307802076030b51514103000582c030910812400007a00c412160010a04840c00340d500300c0c0680460219207507490b00000d181406100400b264403071042c000f05510b1804106c03000e050000d0800038480c480c5000d41141d2a04414802d01c83d100044030403070041d56a84c601154003940d4007100c119128100101502c00524003110400d082e84507500c0422025040502601c6150382d0002603907102d50340b415020780c4a41c00012003290f9001040166100303a143c20300c0310911541581100c0031030202003c2c3c804a00e81c1c0b656012500c03c0c1c004405115880c3c071180310401c01d402050401955640240d80050480e01c150000a414540704a00c1c160802c10038030b018a201e08030110f80801980d89031810425a00055000e07007005521003119a00051820f80145910030203c050075040c45c00c43c40301c26425140c0850301125 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 361114973 1250 361113723 361113743
    0x706181e091803091403010e12090a06140301091805030c0d02010501050a08060f0903160c03030201050f0c07022e050c06010f1802030c040b120405010501050f0d1716 73
    0x10301c02140700d11440300b1804500c0c0c0719034915544000c0c0400010380130360641403558804010442d2025003189905e101d42808075109200c02e40380950241e0000104144142c01d90580056014411070141a10004041da25491a4039000480000388613414074100c41c1c000c00da4000c004941e09102034000b506181d07000d041d100284000c001e084039416080107204032116042844000e01c0014900d40c40040c0e9484403210b034881004040c03840c041d0085280340c50411041c004100b01503030020a0840b4400d400030f11494035125501c042ca64000c681800381401e0920444000d40f07041105c400410381e030003460188039038a0100e0300c41c00c410219580c2c0c000c160001009641c12800300810350050024400c81078203030b8202100c40400301d514100302180310340c0100104d00d40408600403280100b48192000350340c3d200e422030700c1c0702440c021a403d4400354a8140000380a05001341d10b4501000d0007804c10070680c01070741e12081d4081c0014003812500b00c0605c040c071804881c007008150101d0080d40790034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 361116223 1250 361114973 361114979
    0xb040f06061805060c0a0b0405010b09011508010801060e06330c07080a0f080a0315030c170f0c130f05151e030d0f0509030109060b040e0c030706181e 66
    0xb0550500d6800f490150004000d943e40065010584a40c446d501050301d99032502c40e420820301401c907000055038020302400c000a1241c0194298104800322034a94404507a603c01c3d100c4c2c22100700b481078902041c6030340300103105881d016505205808800c1c1030303440910741000c8180c1c001c0807112030b0014500d40011307075400c00107010841a0014804040100a00c02c441e0362030744141c0d4a0102c00908032030020a42681c014001d402030a052440c40503162141603507070816080e0351425102d092451030b200c1c86010300c02c01010841c541c4034060f00c0c000307010141c070b40e40900030546800000c0c030900b6680e8082c400503103851409038601507a0030170201258041c4075010410001c101451030000820681146d070010b46005c142c0d03113188189414140d06d001445a8103403094803407071a2a2fa0301d54a4903081000300003045c1d002140f54103054504104441e81c980c042da0391844002803960b41035110307400400003d40f00f00c11401c0014136000ca95200a40d42e2244520303241481e01001980642e00c12080c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 361117473 1250 361116223 361116257
    0x10315080102031e100902090d060c0201020703030f0912110f0f07080106080a0b150105160b0901050603070303090e06030313030c0303081005062d0a17060d03120b040f0606 76
    0x2500420450390103c4c001c2c10510703200c40d00300750948580c5040319000b0030311741c0103942d075500c80407007058203d80140804104100000d00071740c8400822404031703140403e5102c0795212846580c8065510403004800410401001d545039038114101c1082c80c030401070b04403141601400f00100700d480b0b100041004504042041c2c0c29690302d5007080500e54081e02c1d081001c94a02c240343c541141604840e01200405080101c5041c400c2c52034002070404850110410002d200003042d11507030361100201f000742c6408007013540310f401c50300c0043d00190700e915040c172424802140064200c1402000c90740780c0070b0014450fa6003483c1e03a5209403518403220904205154000c40072070780c4840c0182603c50b69505190005c0c400340540c0140480d1010010345040c20046120041c00d500c0790118815510b40320030440041c0407401803201507000c032642c440805d081c0d0402c6d000c0a000f055054450040c00070303c0449000080c109045050f902640790030291084901c075200310401b900c2c26503103500180d0700075284 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 361118723 1250 361117473 361117501
    0x60b030604060b090901090e010603023d0507060b030a050a080403050105100302180615040f06030f0c02190507030f06050105031c0219020609060d090209180705010e01031508010203 80
    0x844034000f80100410307001651100611410b665a4501c00124111080310490042049800c02500044038060950340d89154415404240000000e078035a41035503e10300f45104009251040c0104030280030b108005001d5030006802c0c030030060f04544210303401f500c03003520b03000caa410140d546980c0000c0a2050000038014164009040000740c201d0340e1443e4041009205400726001308038080344007007010f9980b5412a0248014030a4229848a403070700e00d0003420500500c0360b900030a01e08440321101d4240360203403101c0500b41d07402909101c950410200c1c8002c0c10b0302412601750060042c04070016400050a550040c000c03040020b10f9070425050500c1c0034681c00c420000303043c1140000a01aa0001e0004c0004020b461300011501c1c0500c0403541a0042c06c1d0215401040801d501420350b0207580010304160080b2400d4003180c64086c1c2144160b0a8000503a0564104010502440d4042e80c1040000901071400050b200082ea50b02c40806501c0e412600f1310340d400001f400011416018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 361119973 1250 361118723 361118729
    0x6050609011202090109050703020c16050a05010e060d02070f1703011511070b0901020a020d06090b131a1302091005190b040e2a0a03050f010308070204090c09060b03060406 76
    0x2d4030803080002d80d00040c0141c20144210741e0300c6622540001d4203644250143d402200490701150000c83c0081e90103044040b1a00400740030700d140341ca001903a0741c0308136403171260448050b040520300903003091540301952101c03c042c0c44c4e031600d10f16001c000034084d03010a9284050080007548a5040904520450700303a0b0714610104102c050f02c2c060031f400041044c0045a070714050407a0785040b400c006030300704440590040d505c003105983e43c00c00d0007869000001301038480c1c11580406e80d00d140c1a080103407080800039090704802c0b685400c03002c208003d059005150303078000d40c17420025640001c1c4201c504a0f1021170328101c001c0c0070804d0382841e05a05003075504512280343e4003130400d070041545018511404c08070380300c4200403941111940d9501818422090407041c41d0307445284120300750794072100318a00000c2c030300000a50354094900c9400e041c0c90b44019541d00c2d0865035000c200150600a1042c3d0300ca1070452000101610b1034840e030300091060300b00313540e168a080c504200448080b98 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 361121223 1250 361119973 361119989
    0x30712170901050913060f080109060b0d03140a030b1509090603062a0405040c0203040f050109150c2a031401020c0d2607031b11060705160c030605060901 68
    0x100181c03000d6a00301c0e0640d83c007600140c1c3c451340b070700c0ba21283e610040d04043d400441da500304144041001c46064105048403406050305100d0041803005100020341858405800900000c00403000010181c00414400c0702360301d00400c425440a00282002d48a802c151805580020344803031142082542542d201c1d00c110301410306450b141c000382841c0314213a40c07826800340245090300140b0880c00b0a88000e44006801004104111900a540d030b5000d801050440c5150900016007588504c44000907101c80d403001005440030800203030b40b03104008004031048610149080c129624082c920941e1003180059040c01900d5230401c0010341c0100055210164010401c1c01405c0c0c2c00010210b03600341c120315100311001144d83e800d1542d8074041c40010002400d48080c4070607280c1c107410503c10b210308000080d801e09415030099540550b100212149504588005503c0c980108042c0524605144928140780030503614180c4180075600112840e9680308240801400c1903404240500005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 361122473 1250 361121223 361121227
    0xc010806060d020f0d0e0a021206040807060b060c0f100606030501290f030f010518040c090c050c1002040906080f0307170c0607020c03061501080c0f04030203071217 73
    0xc039110b8403620346400c0e0b0494001410907450620315003100c010301c4096104102082024803540e86803000c0140584c4960013907030380c0110315007010841c070380074603801070301d080c80c0c01a50364454000e058160745460b40004c0c11b0096801c2c40900f4003410f1903c03c440c0c0054040090101c48841c210303629074205204040c034040052019641c000091840c0b242e0b000070907c0c44d2140080000081e120f04442c1744040480401031180801c2c440305c2003030588004071140e071079400480251301e2004c10111806440300b030300c90b00101301061450340904045442d51400a00c0d2160004500e4a001d0664500c8862180d0028080186c600fa0340700c0d03040941200c00240c00c2c08080e00a40381d03501e002d5410090500004d20042d016401c0c8041c0c01c5400745c41c810010365425181072403020b0f44901840240c0c5001e80110f00c0090308a4000c0c0b0443c41b802c0c10140c40f104084c1c0c40c0c0f00701481c2d1030380010740ca61340810f404200210245e5010400f06004214508443c0002c12840c0b601103421540c51011000c49181 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 361123723 1250 361122473 361122481
    0x100e070311040b041d0a03080604090f170d140906010b041503020d020d050708071e210608010518010c050405010c0204090c05060c16050f010801050108090c03011d0c0108 75
    0x186050102000001c40d00800c0d08501c000019008100161407907086040c0603005c1c0c070310000082410f1101601984502e0402d642c1c07034080c0170561b06130500041c5400a01c6140e000081c00c401d0700100316900806003141070408400f054011141c014070300d01800004241005940310041150602504007040304a00b003c2c944249a4860150f10401c5002d164011410407400302c242c3c0e0645100145040040c001405e18034000380030084243d0300500000e030529149101c03c0d5034903a51f00141100c40d07a071181401003220000c04074801150000b64100d0b02c4120005441c0804d0003024021000110321806082c0c0000b032090840382400700c01030521105110400150307030170065401c126a019a0049500c1d110381c506080040d45d250810f43e80403e0100e0708007480c0c10b00049126090420010f048600c50b190b004000c10098900003140c0006c450300014401e652140d030407150003600c0d560488a0b074548000c006400d503030704808034100201c07402002112507c0100400b06007407000f802c203450300e420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 361124973 1250 361123723 361123733
    0x90106230603010b160f030302030603010528020903010e1b12062a0706050703020904150f0311060c0703030c03140c07090e150c0c0c010503150d020d0b09100e0703 72
    0x1445541303480000403400f00604208064a07110541e4022082e0502070041c0c0b80180c0290030a8842a000b90300c2c19001400d000c1004003a0107143c6044090a0040d184041d0542d0180d40700f0300b02550195202c64654541e8a810003982c000910745000c00544541c5400a022003103d0410781741029601507420f204046504961032946551441403d804100142141c0c4440348070310480106820700d00410071000ea580b50340500701300f00d0219024400790010510500340b40d00c107405500c0307041082030410000240342c003050102c50800500300f00c0c101120600c105061011075807040d000b0561810240041560202002100420640c40f240c10440311500d401e9480c103280c0600c0c1e001950301d421031108590200b00030710030a0760302c10340c400c402c0c41c1603600c10206400000b0040410b204400d0704544643c00352007500d105c2c0242408038001401910100041c072075050078240d800500035085200400c4400c1800c61150500e00c00400c410084403002100b1036400c08401d26254200303120510003e2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 361126223 1250 361124973 361124977
    0xf03120a05040f020619030e010603051902040603051204061404030b1303051b07031104020301050123040909120206090f12030a02090909160911040308030901060b030901062306 78
    0x966440d10020701c50b40c036403034101c04140441101a5001c0000720b0081c5441c030740000e048410700c41c01c2d0303070601000480a440c41d00341c1703d45010080c450380140b6242c288240046c0c88002c25135000420100f0119621b0721120b027000500040c201c01c80710009018042940c016010500800c5030040840ca0585141c88044c40d074140503100503400030701454000145446802920802042513a15191808580c0c4e4450303510b41092100315003212110740c0c55101da1426200380ca04803401a1034084102e07038840c181c1500c410740905900815001400003181200062150f040d449100b03074000715215001c0c0318040d02d0400018203001403540716400100d808100030940303103c200001c249068598442c2c1209034068010f00c040c16030040c41d090308220248400280500e03c00383c1d40441400c603035440e40108000d0f03840a41131113105810030041003002a01000085038002461000026440c1e00d03140c504069038810303190b41201d1f80d16070105100700e190f440f00f0145003010301c11140c16409050350100d0030754 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 361127473 1250 361126223 361126231
    0xa050601171306240503120a0905060d0e0601030606061106011a0a0302040e040503040e07110304030828030e330403021504050109030306090e07050f01180e090f0312 73
    0x382c0101c1c0031004121090700001495110600d05a00816000d908094200032500c180c6101e4415141400f005011603400c5601c202400d507280902e15041034103000c1c4035401008041c402942d038004071400100140884d5000c0c40c8107200104030903141644c014035007880c01d81ca03000e035030300981c00400001342c56200400c0c01c02e8129203066219241000181c000f8090b551214454101e00070402041100100c0203206852200795050056254003034120b03240128511003900a80c420401400441c401c8409424031854001c051441c042c104401c080214040d0a89400402d4444c86694030504090003c0d920f0032a0203a034240702c95076005030404511b0301d40c405d48032850840d480807034140340c030900c4444402008820108060706252420b14002e00c110807085c0e001034035101c00070405010314050344800000b030a00409619080004001441a102c0b0303200d4140b04000c400c552020501c2c508281c002c1058001c090000c0c90b1840c440360810b00b16141064142e0410018991525042595144c00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 361128723 1250 361127473 361127491
    0x60303131e2111010905030f0703140a050d140d0f0603020a08010e10110906040b030609011205060a0e010b03100e060f040c03060c02030f311214160305060a05060117 73
    0x840c0e03c0b520010381710603405400442c1c0501882c84983e00c4488005105d100b22482900c440b11502856081140c560010300700c01402c54016051551b00c0030f1041e10300c0d030788100f6010f006900d0014509402001c4a9040c3c28901c0d08a4a46100708150700c0c0444840000340314440080c00607480d0030220039202c14119103451400b541e50070b940801a0700e928251105164050802540c03a0f4036885c20003455002203844c680b188034600004214a0708419032081d141d5405402081d56459240c650405010080c090410303640d40e51416100707070343d010800f000454080c02e0000869210102c8990b0070b10030010a114200710350030091000003540f9180ca6000c40e5040440000c0007003903401d00b24114450b50010300084480402c0d03644500046110312081510fa051001110042e80c0354580040e90395481408503800200050002007040e81c1c1c0282d84102001c0240d440140140700381e852408416081907480d94090410844084c0140c0700c0c040e00070f0400d09000107003d0781c9000075118858018040d0907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 361129973 1250 361128723 361128743
    0x9060303031e0c1303030507110d030f270b09010909020c06060607110604140f0f03120904150b0421050a06090f060905030a120e0c0405060303131e21 66
    0x2100090f40804c0e038850820840545035110380c2c0c0e0500038820380200c00c094848034207100c04100b01d4600509801e031001c0d41a26051982c0d02914415240f10500080e848854060150000003480750f401c13084001d40020040c498540c12004001404c548079038002c48940e910400c1501900030000450b180c0c41001124420394032100c43c9881800c0e520741c40141ca07003000b40490041a90a070084c101800c464055905680c0c50301d0316030420407100e442184403501508841d14000c100400300c8010603101c01c004e800407807000039103140a1040800c69111811a6101240c24040c00040c006130301c040714805104440c4100c02d0352962070300d44c4403c51004180302d80d940324100c20403051800c04101c564000d80c0400c1b0005260904548943c000c4c4070500016025000110f101555441001c900d10b020b58014140022000d0600000b810b000d464550b061009100343d0080076070368100c80c3c0103803d1994625030740a02c1024030348114880c0703403c4041c0750301142e0b49508803d80c01d000404419074120000f90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 361131223 1250 361129973 361129981
    0x90c031407090c0c14010b0d0305030901060f0305010203041202070803090105030a06090e160519090c0c08030711060f0106020a110112021206031b031b0f06071109060303031e 77
    0x949410056480380903428100f0f40f1128800d42c00442d43e00c07450380a0000c072068000c00e200501d0032104041a01071f40715007800c00310b0300420320842c003039035001100c003000240180d29010810986480d542c030403101e5a4000041104020701281c066140c42e40d1400241070340303820521072603100d02641065904012002c400110300c0046600480010009080108100702a05140c2600c4240030707a50030006042041d800102402c108843d902025100c410060320b042c100181c41000c2d003000348010040242949142d8003003a5220020f50003620191501219006002442c03400c05500426258201c01c06800401401d500824894905644001e08a2001c41d0807401a14a500e86110044083c3d1001c5126261403d0303141c411402144200c08880814280d07080e410840d202c4100d050303800d600504044980040c00108166840718010607110100204202054131908244401e5400340548514041541403080c46a500241c003a8061441d51400540341e078450f1845070107030084904840005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 361132473 1250 361131223 361131263
    0x3021003020d180305120705090105270a120605090a0812041406010b120a0b0604031203020f030c031608070f0c05100203010f2c010b07020607170c0d03090c03 70
    0x80c52440c82e01c03c8501c02000d034503041c000c20342d401c1014803030000d41008001c110028002c1c0c06844200d04165603052030403003034030859044003e42c0744030b0010072203500e1881c0303000e43c1c0c5244e40c00c0050258241c04411440a908000060314000380c0700d01d0658200740e001801080f1507008a0703040c21000e0b0328010540d211440c28006c4c5031039200c103107000707401024000318078402c070303000109846000a0520001c980302d0042034411180d894502e03652107034081200b00001003900702c0031804d43c0007a050040c00c200c0c0182041d01039600803241c01b122040300008110081040039170b100c0e000c040b186001029454029000741c042c03406501c9120520090700024010044108480c46000b40481400d5490f544d40c0e546140501c9047d004a84070340c0102000d1140c8840d0f526076401c8030055070700f44c4e0710301ea92a21a280d8242c0d8803421050b13800000400c048404203813001e041941c00020042000c0c0d03a200c07060659403d1003541c0400300d0806081c43c01076004a8503020100050ba60000d030150045084c02d010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 361133723 1250 361132473 361132481
    0x306010207260a240b280909060b0a0e360a08070c080d020a0803060d02040213050405130b0a0f090c06030c08010b070308070e011b1b05090103021003020d 68
    0x42d10120740306116880d0200900850075203404240f0200325440f06103803060079000d8564200c9510b8003c4800d1400041034000419420b451b102c0440501e0741507916407520005039520024140e54480e00c0700d16200c49400e24040b101300900321311241c402d0908160229298166516000b440440140052107071001015142c840483c0302801c00c40300d2180880c9409002ca0300b1080007038840505010300015141c6021505401c4240d041c0e018214038407050307940c4030064001501d91600680800712480058030355100030300300a010b00f80c00c0c6010503d4241088181c80d00101b88481e90481c2c141000d000811b5280d0140d0804070881e0080791410b85a0794000080c01100c502402000c0810b00008100350180d000030743c1407046a42c1e20b10b0903a00e50510200074890000c0050008010000088145204124a07800c90744140340440d508240481415405110f4240940700340209904840d86260754543d413000801003590048441e61543d000181c0c046004034507003003807603000a91000c500940381c2c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 361134973 1250 361133723 361133789
    0x12022d0d020a080f0112031202071a0901050411060a050a051e130305100b060912100c02070f05041406091b21071805010f030917091003020306010207 66
    0xc119200d002a00c4000c201c0081581c8014107411000004507101c280040030031021600f545448500c2011420324000075441101300703880c912001c009032450511101d50700c1c3d00662040c030001c2860b05081c2450340020b503880540030b03c03c582c10020620b903503070800180c600900c3e160900030f0f01d07001204100c1e0581c0d9a03544c1da41c00e5400340080d80425501c0e0003801007040e039000d04200c41400600700c010710100d03601d900b90350750710003402c0c40030f009540740c4800300e500196078038016549a0b1088408003002d0340c90610754500035800010f02800180c0c0e0800391b080080004980038413007944d940070020042c45020304003500581441c0c001400c0920707440c980b04482c54010400560f14400c0141c035140f82d01e0911440e00340b80400c04c001c10700303840c400c004004220110b84a550300461a20005481c607114107400c400c241500c0d04241c90110b40b50454038980d8a03490b5000030346c0c6140c010304000110300951a00018035105205204241c0d0b800104401600c102c10314040d0400c050072545620800500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 361136223 1250 361134973 361134997
    0x60103050114040f0e060421080103020a030f0501020912030d0c02120a032c07090507031e020c2b090605030c040e180105041b050f010c111f08060112022d 68
    0xc002d07c07040121041e420210b1280e42a075040c0440413441c412501c0e00c00038400a50700c0490440103002180f00c4100c02100035100e00c000500d041010404251000465148140c10f60408101c00300100710a02502d2800c0c1d005101400034000e854503e281e0360301580c00400b081641e511400c110f40d200c05298640000700000d83d01c0c0d555214805069594402c0b4000e141e04941014003141d0351a000e030003421071200030100303000740080035068150025001030703c0d8100c1078816907019525900c1d0846520221510201c2206117079038030140054116912503000d54100320082040240c034078414000e40e8191000f41281c0505600d0b0b8030240d8400824900035451103500c6d11044c4004c0108043c5103880b680e10300120100c0c480e07a0380c0c0070001400101075581b8040780c0b0b02c00103d0009982d09038001031400300203198040000e40f880b43c508a4079580d451203000308034528188942c540e0403030402c514030b0900407015858401c04003114040740055883d50805640390a20804503189150203540404c0204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 361137473 1250 361136223 361136233
    0x1090f0305010608120c03160c0b040e18121204030903230c01090501020705010305180d050a020f010b1005130e1302130905190528030206060103050114040f0e 70
    0x39041a5009200500c20140148250b03014483c4d0390b4000400c0d01c0c2e42c0001540510704240301030004100c10360210340304903440240c0c0200455031180d9600540050012201c0c11040da1a18000460541604d01101140c84d0301030030405d4038010a00007183d00c003003480015143c40c0e8840340344c261500d0070300e40c000070a1082d80c802c003112042800a40040d4541a840490ba0060a01d0005580503006070249a0060700b003020148495402034021a41100148000540341d601004089003001c2c0c003004110b002450006015803120ba04010041c0c1d45a0070100802c5403261040004e4887e01300403005605001011402c1c000550301c0c801150f0041c81a078613481c03014500400e00907007481004500324805c92000c40240f560715071501c50071241d00e03400001802e60003404401d4510344d40707480030110340503c110380d9155030401c555888a1809003d04408004001007032030044c1c1000d0004008904151503c0010424403010f600305410380c1034140d8000515070394000c1400090040302482c0c40540c451 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 361138723 1250 361137473 361137479
    0x30b010b0a1134060f0e0a1d0402130e0a0611190905210303180304030f060b0114070209040803100e040c0302030f060f070516150f270f0201090f 64
    0x510742c2a00610302c0c0c080e41d186040d10a540751083c9920481c003480c00001c001e000441a80c2d40940300700010000b004000141c521b507551104c1d60962051382e500612003800506002c2181000300070f607101c12180f550184098100f010324580d42d9004081d01501040e240c601d5200110003001c1150204580c110140c4240048080060001042841214010b2400840e00b134103100003a901c145480f00b20380007451950b1100807190030310100680d010903a50204000000000d82400c3d24194190b20481010600210040c00035000342218544e110041400304443c0c40182d861030541c65100307501401040c0c4a03119451a90302c0e26845400600b8000d038941c0900042c41002d154a0084034802c4040b80d214002c9040190b84403030003921400700322560503011500480c050000340c441c1d000303041107011010216880e5602c0c074103908440d00712403e580d006241100703a01030081c0900ca07000c01e04440d912500c030030310300103030000c0b008009400701c41040452811607204d641c05000401d003079040c0901041e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 361139973 1250 361138723 361138753
    0x1602090f0106080912030a05100b0307080709060905030d030c050d060906080d0504080a11191712090315100b040e090c03061e09010f1104031a01030b010b0a11 70
    0x8428000c1102041c075038000102d00a50000f00b5600c81c100e05c401560a5071692443c07034001e8440070b06811484000c140001c2a252113a10140d0303c40c09640e0f441c0e086c28285134801a25041c0590003440801003a11000d018507100040e03800c02c0c0c41803034680003d10040490081f240b07405581c40c000441030174842c00080c826030a42101e01501c8030b000941c0c19280c0e00391025907d500c254468020141c1090012002164803070b01c540034034103001783c0200d0f11128200b11800105500d070f040b441c09041d2842100f0116401003160724208020b2001c0d483c541201000041e56541d43c03911141000310100e8005100711200200c40e00040c0444100292a01d81710001d04d510300104581100e1580304415102e14940340c0046d000740541c003000404281c5448454a0000b882c1c4018000396071903407160419188030881e8840c8100f1002c1c00c0c081a07840d40d0951070888a0007c2c1400c40c00101404000180302086060010b030381111451086e59a5620764a21f060b540c00841040c0581140558580706000b25 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 361141223 1250 361139973 361140001
    0x20c1e190b04030c23120307020301022b112217010915060302010804060c0302210108150c03060103150b07081b030711010f0e0306090717030406050d02160209 70
    0xa11642440130070644554146410341d62005e40d841d101c418101e07180030075007011884840171407110b400750380c41c11180c0d0f00032a003a64440010620b2011080070040c0d5092148043e1440000a210040c40030704200100e4a07402d016400840d07040202101075448401490702c6018014408030340454440700c2e0200c2124020300540b038080c3c0d084c0040024400741d0f000c56100e800c050f2a03050f141c141d50342d03c490b240c0e14010702007507001300c0c14550b080010009500f0b90805110540040030403100e01036040522442c00c090503c48070700745101c1c2d020240680d0044d42c3d0143d03075000340c080ca800111640d420780412164005d03540241d80c02d9800085601c24003070054018464500014217100390070010084040e5207104402c000f4181040004603444298881c60100c040c141d6240707801503400040c8800242003542c00c0c1c1d080f23003456100483c00c000794550119603045010b0407002950401e8070300039000e042032043d840d54a019550000e0b11b8000d50444140d20448950054400300b002d15100c0442001c1c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 361142473 1250 361141223 361141229
    0x171915090c050408060103060b010507050f0705010e04180b06010302040b0a0302030a0b011b17130e060f0907020a030c0c09020304080a0e040c121508060c0712020c1e190b04 76
    0x81d061641c81150540140c1c1200c044410141c02004075038619240e8000a0820b0101386042040c10030000e004220100002c0c40940030900150441610f00300014007580c2c40d1440c00c40c0542d0170211101040941d190700c8400d080e4000d00343c400e60b9034481c00120001e1146801c01c00c2c2592000c0303486a507096265024501c80da40c20b00c3c0070891050582c00544200d001000c2c0310303091403080080b0381b00040b2051001400c00425183e40b034149081d42c004441000025040009105590000c2080034a84141900254001645e143c8c045080c0084000e44460640c42c01409014509080c4020003140c0d805420003402c100c6421510790406240040b165030082550400059440383d1054031031800c0e1145c4803860055884901c1116284244100039183c002c100c0c0405101c40302c4000313800241880428460f0b08042042a42c541d407500c0c00c008284c141a5400003194481001c0080c25120703508800b01780c00d2401002d5200c40102c20004010901c10f0440000208030100700040d03020311400a4425 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 361143723 1250 361142473 361142489
    0x60411121012111201060e070f0e0a0e040f050c09040c0905070e28030b04060b030d1403040f110d120f0513030308061801120c050f01171915 62
    0x141e55010102e51401d103604058005a14803101c81c6040c80e002c001d0142144070700d40081030a0f07959581808100404070f440c1c00c00b00b19000705110003954004581d840041c021580c0d01c5840b170901c0c1f00b15105080c010f000400c90061138503080203000d800c01c8500a03803000204080755a180034642004882514812003601d6400d02e00800c02d4140030343c011055552000e0b00d01c45c05e07110701c0740080144981c002403045910001810102c00301e19807140945c41980201d002041407480542810714151991006400300070140c0c000d9103016100b001129005a040701c1d045040f01918100815107021222186034400e007036003040010040c840507451959140c54a4140c501122071109486901c6034015a40030300d0f0b4016020710000b4000d46010303030030050103002070200220b07900981c07407201000e070004034105003454028410864141015005804150b03404403c84007584000b800c004080c080342c48101c600800020394015004c1d041c4500c400442c0020710240c40d5114141c805074044e400380d559 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 361144973 1250 361143723 361143751
    0x708070c05030c1f0c0807051b19050c0607080a030f0608010c0305060a06020d0e0607170403050a0501060906121122021305100221041a0a18080309010806041112 71
    0x104d262060700c1074109640d55500d038403040e951141c104680b02d62003400b041c0710202d0310341c65aa428034000c20100d032444859415000d8020110300b81545080d007200d400c1441100200403180c00035042005494041b81c580c180070510f131a844002d5030241100f50460945907103071644a00300603506800c018042c4000791140041551101401c0340c484011410303040100d5140e40d1901c110381010b400802d0350074001c0c94045140d48078a44030005650040e48203691550010300d000c014000280301e200300804900c401008142d14012030b0741034042c140840038020450800f2808043d4440c110004c0c404400e4032043d1411143c2c00c0203950080d001010301843c00d8810b9074000ca00d508188000741c1141070f59400501c54040014100c0d21000f02c132501c003060b801c2050000140c1c0501511052030360000403003e031b940f6030001c544001c2a00c9503803444102c4400f84d80310100b01c0001d002c41111041c0341e082c6441e0805584020214019004010071040c05060004a042e200002404258002d400c10041c1c1c0c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 361146223 1250 361144973 361145023
    0xa0c03053f060a1205010213030b090106150f050901140f0c06060d021f1404030f1401050c090409050c0910080f0c100804020d02090403080108070609030b0708070c05030c 75
    0x8001c0340c50880302c2c00c0d084001d0340c1c0103103d2600c410314152540c0307100b080090725001c031400f820340b61050181c0c400c0701c501c01040c4c01c1c440303020070a0144202818000706145024001c2c81780051600e0b20400c0c035841404400a42607106910903000c9409100141035480e0b0754843e080b52000e803907840800110458010433001c0780305494003074044107950750000c3c031002c070f840715482500086020514100c404e2001c0010003c814040c1751000c0c20046004040c001312002c0681050280e44104041c540040d0345410100500b04035210103940d003480099600103014070315850114901124401d4940c0d20884090401c489480c0100d2001c00340ca000c02c05036406185207280c4141da032518010250b41c8005009959519184102e00c04c0307030301c14002080180450200e801007613582ca01540c058002480c19401805519820062074005004920705845614070716100c40320f6000010f08803601700086d510100d4500707445410000a61a009025241d4800e07110b121241d44500c11220134200c249989400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 361147473 1250 361146223 361146337
    0x10f0b030408070215040e011d07030504020d12030f06151403040308160e04090501091202070515090102070305070b0903010b0f03031204031103070b04050c150a0c0305 74
    0x500e00480d803014a590411103543e00308154802030a2985d041d081081c000003c07103103410800c1c54020315207941004003080c640700008540306030041103082414102000d120050f1503003509025000e402490800c0b00c81041138048010304640b4500c1c00d41107040c00b2002c9016420365485008410b0181c4500c800085c006003503c0a500040310090086000c040c0000c40d030458020300344441612074a841c490070a00030000404880c203110095a075695103020010801c0300c2c6203140d81e01c00946000400303040d07140c00001108114002090102c80c403011800707040c0d9034000c200342c0c3c000d1540001541c07455500c441d4900d819400281c1460310075030a10702c4840d070b1420901c0c209060303210080c1c044c500c2c20100381d098101e10b02001d0022010894540d402c0c100b41002803014000c2144106030f1000d06007000d0601a240c01100036013240b0640e182c1e2550b0300c2041122040381c4d5041c0310750030554900d105034101070703c1c0c500405d840d10000455403150060f07000c001a400301c006d103072854020b00040c00c0744810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 361148723 1250 361147473 361147477
    0xe0d09090b0301060306090f0209090c060d1512150c050406050405100e0613050a0e0c071e1a07030f0e0316260a1e0f1101150806010f0b 60
    0x1440424a0410103014411154122024014001d4000310713015550341d4504c801ca4881c1d010075148022071600c140c0451800044064225041c00c0081948034583d0340043e90520030b42d10102d1105a652204000c041e0807807000710003c1c481a405840ca90701075092100703c12508403511403000e8500242c820040e80654103a03016a0341560783e0034142030403c401c3c80303051f144892040c001e0100040c4001c2d0307035070707550401059640e444090340d50b843c42c501000d00000a0403034201001c20503021007000b495805207416911040d400403210a00c1c0c940707141000c08085000c1001805450340e20450b20701604404a65600520803a0b404020302100c0070240ea003140d11a11a2018a030410000c94900519400034807003c640120a200b101e00c440310401d00340705030b403542e01c0b860350f18001ca02c610300150070000481142c2e90190000b00000c5840702c4c010101101140c2c0380b02844181c58902c140345000b58481e45241c22000808094962503c0700b5554500e024460014840e00c400000304001d004001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 361149973 1250 361148723 361148743
    0xd09120b042003010606031a06030112080715020d0c0e0906130f020d0609090201081b0a0302070f05010e0a02090a0603230f070b091e01080f0c040f0611010e 69
    0x1403035214907129030380c034142c91040c25600490702000072100c082540e502071040000030245a18002081440440c40d0711100303554100303592080c4014401040350b411a009401e448550200140303030344000d140340c0700d02d400d0a40318404041510215211445450990201d4007141c843e498020040c1010010454299400c450540d00720109803100e440f040303040d41041c150841079002c0541040d40e50302c91030040350500e03446404407035100c061420035540c120380269009140c4010f915075002003000c84052034490b114030882010360010b080d038184800b14610b0fa000b23691100c001d06c180c1a91611141e614501c044081c0d101e4400703000841c1d44c40d104d510602080b640c1c024103400b4004c0100002040c105000011311400e4000c60750b5075840c050080c02841e010f800103800300c07600c440e0790009009021a071001c0c0c089440e01490580116680c203c2d0002ea40842c0d101c541d4141c3d80d540303a006141902441c0c3c8005210155118045200e5400c550291031841206000300541c03140c0358100799458540c08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 361151079 1106 361149973 361149983
    0x2100e0f031606050c03040210050a0e040e011a09130609020a050a0b0a021b0d061518020408150f070f020102041a0408010e06070516051e0d0912 64
    0x112a90341c12203004540e040c21490300e580421803940109c1384a1003886000711b950b0706503900c2140d0016041d04084d005000851083d030290b1b0180940110300c6c00f06140c6007180d8046414102ca90520900308807442e40c80100d0162584401448295010b981003c402440400d40f078039010800c10003030014040d183c1c1d80300042d21000303090100780e20124000074001244a5141e40e40c082e0103954003900128000790040d100d407500b452209881e800400500d225114007410441c0b103502410441d08441d068881d0ba401208909031001003c58440d51071101d460f0105450383d10841003098288910700005150607103d101c0000c1902040101c6c4004400001d8244030000c800c0c010940396522a80c020100c07030520b10005000d42c000c1800060058840442130020f010307042147c40e2008080004030020758100c28000703500c441d00c1401c8080410500800000c240c010608210070f015000 = true := by decide +kernel

theorem cover : BRFrame.Cov 360971223 361151079 := by
  have h0 := BRFrame.cov_init 360971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 360971223 ≤ n) (h2 : n < 361151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
