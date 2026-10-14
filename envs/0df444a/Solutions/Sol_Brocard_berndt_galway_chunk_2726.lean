-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2726
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:33:22.256382+00:00
-- url     : https://prove2.me/submissions/41a032f2-cfd5-48bb-bc7d-9b0fcd5ceeee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 490107913 ≤ n < 490287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 490109163 1250 490107913 490107929
    0x18060302090a1401090906090602040e06010f050307050d02180d050303041a0f160c0c14010305100b03190204051e09090105010e07180e012402072907020a 68
    0x19246105102074a18050a10000507040420600c3c2e9010035945550441e070b0401004910a010303410180000d00030010040d01150001501081140801c40000c0c0203800a0341e070780800c03161f900c1045940740016100c041c00181c0030810000b0700c00043d000707408140c4415a03142d00701543c04000442e60040700303500729400d41011041009004a15011642c0800034000180031403074200d0303404154000007018290034401441203007008502c603040e51030a9541c0400740b114010740310302e0111075900307550341d11a0009041400080502c6111450780c1c086802e0b2042c174500310b440d90444810800304c013101011900d9030a004c009065a0740c50420006505000c40d281081d40881d030a03c00280c00043c0f81000710303814813004110512540311a180d020183d8580403184010391059088a100305500400040003441c0010503c941403d0001440c071140c0d48805072640941502680c84104034072421040f0f14003600104071880c80e141c55140f07604050503030245000d210380c1c0010710351030040e000308c0d039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 490110413 1250 490109163 490109171
    0xb06160b010f090c02060703020a030e0609070911070f0f030507051603021c0c03020f0f0303121f0803030a1e050a09030801080312061c080a030c021506031b0a18 71
    0x8000092841082c0203480040414032a000760b000300659180b90184c006010103034006070748141e9900c00c1c0d10200301084c0c008195501400e0070392400e66100b0701b42c022130403501d00e40144101c110800c0001c03914081e9000e645900307965801c1d2143c802107441a2015001c3c440c041290100046082c40754540701c4840400c0c2e4031599007140103016401c16a80c509070b0740030410001401c0403030034100b41342e0100c0342d04841c0252446c40302404500038000c010540380c0c0511000c01c1e2004400d03848030700300340b084900c50010310312003a19000c20030034950b0600c1075100c11341042010814114068103c4070ba19a80b0001c0b81d0403880303006213402d04840b82103038880088d03a40d40702d141c0105980009114018010a001941010034042c265a4500006844a441400026185030230041500f0007a00043d4001e030a05072030f0302c0d000e103002d000791170010085c0006010b03450382d04100800581c0c0841c041c83e8083e0082c42c0e1240c080c1100101c030040400441c0c1e0010303220500164042070702c00305200c0c010015a01003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 490111663 1250 490110413 490110419
    0x90a080a030e1008130c0b0c06060f0a050d151d0303070216060909091401110715021e07020d0c06020106060206090106120b19060e090f060405100b06160b01 69
    0x40000d4542c031840c0703205000d00308a080c0c60680c4071200a8004001d4451801001d00d0f526080300c8081240d4080604a180071480103494603003ca032080c40f8140a83d80d80019180c0c2c1420000300c0030050280c0d0364040240c8203100d022908001c014850700d00240000614001802018050140d05201c070389000d50000040008056044c00f201e02e0490400044c25030103810640c01070406041401140d9019682c3c05455081c400b02c2c0011886541143d002000031240d071100c0c214140d0b01c40d0700d0a50720b900320244001031140b001d00c204c41c000040d80851844000300c0790619181c1e035001140076a8130a02c030318046004519107950400c002c20b006e400004070329140813006030409200400c00702459242c0b0004111100c0442c40034502d4541c004a03c18440d5101503610524440061240104c903280440100d00320300385561444c01404004111401b96604000a46c4d07208011078006003540c21031480340c00000a1074221520182004201504110a03015a090415410013065995082c510010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 490112913 1250 490111663 490111667
    0x14040b071a0106140a02031b0d020d020c030d050d0e070905060103060503071a07080f03010b130506031b090301021204060b09060607080f09010504030204021b010c052805090a080a03 80
    0x11110401d210031060710340b50324040000c1c10040341c000c202400d050300040d070104118424001c43d008511985840078010210600c100c0d916180240410058462580c99405650001864045a02c030090040c1075a010512080b0b4031742d001014040201900c074807130391320307412001d1281e83e0107482d10751400541c51802000040c20b44181d68080d50007504400380502c4403908a0300b1689207000b2010041e1742e5050f262600059900c03074000b10164461000c400445e80002c02d50091140308080100600d0050304c640c01c00c080d61000351070300075410303110b1241c412242d452080030748003210b00140010306042c024141e60b10b109ca41224116141070f521030045080d032405c000040e4100000391402414841c2c0c1c1e07603c0c40c11b14801c0c100605004200445c03030400c580c0c0b04004640107542d001d030095489400900c40c015a40010360a610380070350030480c2c0c0c1154144900c060711814492001c0c018000014404600080c281118001040081c00c00c40322125172243c0d058500141184001006044518100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 490114163 1250 490112913 490112933
    0x1050403170a020a121104050d08030702150f19020408030f07060f0204060212031003020a120b0906150d020f040204080303040519110f0f120313050a03050d0f14040b07 74
    0xb06014920500500d248135074481100200f800c03002c2000985c050002e50515194002e030707805180e0100401c1d002e90200403804010f1401103c046d021103541d0241041034281501c822145007145015080010303160742100c03020100182180702005241545941d10f4500790307400400118031160000891008101241c41680c0240410120450515080c820029180d081c0003880b8841e454000c001715203030910342002d8500840e4000c1c02880d05a584103010041d100034580c098608409020014a020030f012541c24842c4155203203140c65402c0c91401c00c251413041d400d00342e1700214911848012034565100400140071200c0043d901da190600e8071301d29002c64403444880c25010408000d0001701d80328040344000600f00e4507181d0340c0d6014008100000301303107038006900840d0350042082c07001000c0010155041c3d038440740f5650315200d00603c400700c1c1162000410700c1d4000e98101c03149502c5009209107540043c5007644041c40f40000003907140d0002e42058001d4000041c081080001c4004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 490115413 1250 490114163 490114171
    0x108190c090302030f0f0631060903020d21020705100203011403060709050603151c03050309070806010807170a0501090b060a0501030b09040305030601020c030f0f061b0415030e0105040317 83
    0x10082280c01b0b0240c4410f925218050f0000b40c5c00300d02c40e00700c00e189000e003002c41940480070111284100e00b1508003030000e81136010f8150054043e00c051142264401c8980c40b0000d4003102141049000070900e100c000e600c03009060341c00b8001c0c52035030490300c01180000e600900d21201c0302d2805c501d40314201070038940090b01003001c0c48003084c42000940c0301c1c082580d500c160707007410350960310340c008001c50341c09085190041945c2c035241d1843c4007055082009140940f04280444040c5a2210070b119a1a10207000b000d10070340c4a035004000d0400300814180741590004243c403410f04059a909007520040760045411010030f000b0803000b07080c2408110003c11b0300346824042c1d00701d1000440c60310313a03001d031001c0c007080000400903c2e964000c106407403a102c006011030700c0c8800c040021688812010349100c000380661004540000d4401c40e80044920030000c440d481c041c0b8000d205400980210b4820301810340f14101d4030851002842114451070094582d10a024202401c2c0e801c1c1d448010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 490116663 1250 490115413 490115443
    0x2102010c02030c06060f0406150909150602030304080703020a0b070305090c0103020f07030f09050a120c050909150601090f081b0102030c0d03090807060501032006180108190c09030203 81
    0x301400840f80000610349403c01d0b4103482000d4820301da0804240038020b150090456200009042480c05a120019101711340c0300c05400c00000312298603042000a6901c01c40005038030074000314011905800041500d28440d00486100c1035045c0c2e0388040390341c01111900042680d43c010030159940a101c0103e900c2807d1804514003840c162040e0840c2c001c104029080203600e41d01d41070b4190040d1802c601605009000480003542c55540d81900400d0020844142c0e004030740004050814141041c02040700300003502440c03515604031045201e00418040c100011950001280c2e00e00302c1505002e081c100c4060810a607004585ca0340e81180c09950074115481046101549007002c00e6881ea00740484c60041200001d0f410521070a00801a029007501d2030180000208012003e1501200c21100244104034128074108661400398150f0050482c580034030160240d031042850903804940c154500b460302c01310001039000c4849411240010645110b010300039841c00704010f19000180c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 490117913 1250 490116663 490116667
    0xf070501080106050304030905062a0304051c06090f230c1f0224010602070b1e0306031603051f0207051903261005060c07150203072102010c0203 64
    0x200000c098100c144a43e03820807a0110120302090320036882e0a0080000900c501c2d15011060848040c58000c01032070000c59807000391203060004048143e5044400c02400c0a600d11407100d055801c04880c1c54044499958804031500051100515206901d010307054146603214250401201000c002c01090155404800002e41c980d5030f000000c405155500140c0340e0303d40c4400c801ba46800050070311402114030618100c00014600d502c0c00f4125001a800ca4041ca40e581c00c4c07101c0140305220b20604040c042c0d10401e050345041800658010002400701c45140d040000c41c40c580c00c1d1150005c40d00e42d002070217070f0902410b14081c00c0b40c04901c0008214600101a5540c980d284400380c6280c0f0303944415130b0804103150040490300041d441410110b041c0071090311140c22030a10031299010418a0004085207a0503e501900ca80d15503402c02000598140220004444101e40001c02103200401268001032000ba00c8061001076a880c80041056007007400390940314549a0b0004540c01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 490119163 1250 490117913 490117919
    0x100c05030a030b09010b030f06061b19030206011e090216140106140f01080f0402060910030203070909020408060a0b12010f0209030c0301200a0210020406020c0a051f18080a03020f0f07 81
    0xc12342555400080844510360381d03c0040c610907000c940c9022204499006842c003d0482089224440d01814465420b5402d50307078940010942203030030421f0088500c0c02042c010b000810203503000744606141c24000c6a9052a2075403281c04805c0014001007070340c2d440d403000700304418140c20880b01c20789040300c2c800305c5004030100080c070200c0024840c0030803400c0c8401160a54684d5801c84020010240c1102502c80e00400080d02a5209940c1100010b90301c41c2c000402c11000c0c0300740e800391000d041c050301141e221061101c014000d8040040d03030114609071007108a00c42445411041c1d41e03c03400168495405008141c1460721405005010303905184c0024a42d110751401000740f81c6d90341020030f46480000301c0403071400c1030032400c502109200203400318100e82c00090950980b1400c44554803090780700c4040c410819010111014449107100605845d075008901035444a40c1c0344005082160b500d8000516202c41c0000130350143e0400240310b4004c01003805141034001000c002403035418a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 490120413 1250 490119163 490119181
    0x120105010801060512040606170304030c0b0f071101030e102c030f0307050c03071406091f0b0303090607260702011e02010b0a0602031306110606100c05030a030b09010b03 75
    0x5c151003c902d2218100c500240070002c03950b00ca40c1c0a4003d440c410a0040040805503503280c0c424001034899100c140800103a02e022103040f15030403a29207400500b03001a5a84030f03d5822411000141495100c80010110300d200b0130084110044401c0d0100b01c2c01811820752245041da104c401c80310b02758030a00f003800800e000080340d010345d1020000d00d170b5943d2000e004449502812601c0c0b1024007000a22030148800440300c429026101310a4850070b0b1502c448459680143c1100707405014104032480d20301c1c0c441503010360f040b4000602078a1030710715224001109036010b02003c9030030b4040540c80503900d01c52003e071800d44134151481c007454020302e6000640195246801e8101c184050600180114800e40020800c0d40000e841051060f44801010307407281c102000d201c100361130124001459038400c025413071110801c0000307002540c480c01c05011b00d00881091a0083c04038408103080010030800050501d44525940016509144820080c28134410303800000034407000c1c0280a4808 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 490121663 1250 490120413 490120417
    0x501090b04090c1205031315030507082e05090c0a020d0512010302040207110916020d0f0801120f08042c040228180510060c1e031205010602031201050108010605 71
    0x307a0581507614004c0684c6071003890752081140144401130540e0000800c401400845184003c0c5914244041d55805904542c81442101c00c032807150036400240d0300c0c1180c04178100d8a901418440e4280050301e41c4041003641509a880b409000c03000900003d881e681400f48085440c07180c500b592400c1080a0211800b203018000a4442d40c0e0004400c020030144020b0907540800291404441346014040e40301d200500d07000900146c0a075005806001d032094550007003400d0715841c3e04159074201402d440b03004407040700071699200481602c5010400306070181004001641089448044003c08509094201c11510403c030881d0700c01d004c010398400e82d81d03600304c40e590941d604428400d628000d1158019910440d524025450360400d140410780085204901e60200210756542c0c402c1c0c04c840d0314900e4007001c0c011485c0d02d2034910704031035480003802e1114028600a04000107011140c000c454081c0d1043c80560b20000d10b090003402841d03880b034010030003400d18103459850002d02610038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 490122913 1250 490121663 490121669
    0x3040309171603060e28060f0908121905070914031e0a060b092703120f0603010c030b030709020901050403120302071a0c0a0806030a0212010501090b04090c 69
    0x196420780018150400200005020600000e1045044580e0390030319000604101c8180d81c1c039402084203450041c05202e0340240071000703101528003100700580f948002010a005030440c4580c0f07420801c004a011000580034407041a83e070008503091441c0c0030000036890301c14165800741800100700031b8580000c00c183c2110304d421541d02e06101c6903c0024217000c3c070850441803895052441c8454440001401484c00784100010000034881d001040407038441102d2440742215250f040310300e13110354050200341000300789003183d041020304540200010421070700c0b002c0c0d0750000c4d01042414035090043d18019002428104000e0502a01003074464040f806485501030300065480d030a41d200b0302c1210020340c1c00001e40c00040340e00340002000395101c601c003a030b01c1c0c0b00311480f07011901241c140d013180500030013140a842c14164041c142d50f01240286400d0303050080002c0400544c681584211905074880c0001a8960401020a0407110b500a4480c002c51908051400040e1880c15200076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 490124163 1250 490122913 490122929
    0x10080d05040302011b0204050f0114030703020607022e2c0f060a02070b031305010e1f0f020c0a11040e0d05090618100e031002070809040e120a0206010905070503040309 74
    0x1080030940f905d001d1500300144001c1d082464001004a90460441383c141615000c28031641044126000c060392907101d400701030342c8410304000d0100140391400c0d08103020781c14504080e11807110740900e83c810484900008000c5884400303090380b01414101001380d01e0000d00015000c10950001180a43c000060200d0141a0000320b520581d8020403500300184444201903950f40b41c030144484541c04442821a015820484200c12002c2c0100b484018210982e08103030900f08074444d80d1014155100f602c080b06642013002030495071052146422040c00351641244001d41c8106000c202c13800f4486039206178000c143c0d006d0390160321030103e030b1682e90704485441c7c4943d20240107441c80b0004580c0583c0c00b04400481d0b04815070800c0b080f0381202000c406840340b400b001c1c5400d005038030800d0b100810418003085045860b01d800d0b44520602d00840013220920b00b00146c102a07030398410040c20f4056803100d0010032582d0030b940203181c1d018040b45000741c1907060941c1d01902950442c00750480b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 490125413 1250 490124163 490124177
    0x10615020a030207120807030c11040e071503021e030411060c0d1701150806030f0105161e0e06130f1e0803071113090c0e04050613021315090603050610080d0504030201 74
    0x27061002c11010300301c00000c018401c101ca103c44051050f91481c044c42206d08009540201da005a8040e00c296102030a0520302550409428045107810360302c0100700f1245103c00040760205030704c0c0e2002803c4156401b20090160321000308020344005480303158600104003480050100805000340c96002c0f50759402e00d101d054039180300203420400c60401101c2598a441d080003030599103c2c500950000d0662661001e20342d01000613104140f00c003100901041280c00c120f1014145080100540d0110320030759910940c444103046031159199000e00007900c0307603107803003074200c10903040c10310040403030070300a40c5000b8541e0390341e03d5203803003c17000c90b441a041030800906100f0507400c01800c0b141c0c0605490700781520f0310805094411300307860907210340c401d61000400c0700c2602c120b10703040e00b07400500c140c0c2840d04200f14000035189084009001100d80d0400060025050080401841c4500040e054504c4c0c074801690b00c00300726520011441e40a03403c0c121215800004030707015640c0a1910395 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 490126663 1250 490125413 490125437
    0x6200c150f0706020a1e1d190e07020f070f090905030412050a0b0a0507080103020907110f07170607140f0906070c0306050c070b0c030702010615020a03020712080703 73
    0x14264001c4822800440d040058004108034056009100024050300d5600342072094985041c00c41e052400081d000c1281c00c141c2e06111101207018043c074031002000b8284903804480000031071040d030362000901ca204501403140c100c1d0103125804050000100601d2220b00e42600c2046491052107441e44a0303035500b4148041c001d081c802c80d00506240315020302003500b5031600650341c080030348055541c016840d002c80c04003072a900500b8016500360b0340f203030082d9082d80c08010790701c1f0000c0c20f04c1c02400350010030b035405030380188000d5441c4011032024201d641e10308640c19000c2c141d95440c500c00c540040e020024090b0b0480d80d140652407550188075140c980d008001c00a038410460650303030000001c90740100f004000d0b210601034034030031001480341d07841710031500304035006812000b00349141c0780002449021030030004d9a13001541c1d20000c01d01641d18600418100d90030541100181c00c6100e25200781901000041c0c02861901d04c3d0500c6258181c40e40c41c085e0094032001010030658141003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 490127913 1250 490126663 490126699
    0x30a0318050d11060d02070c030f0303050a09050c0f060c0d20030c060a0b032404110901080a060213240206060f2115090f07090b030a17070c0902030106200c 69
    0x7581031281c0c88106041c03905c1e101d081903102b000c2007940450002c2e0401c0c0010f25040306074040e09a43c80d500500a01318a100c201c00c100050501c00c0002d50014400c0c40130090032407081060343c41880c0c15455403499a1210304088071420000b0a282606600400110301560b6001a07001e60040718004006454090380c000203050603840501e2a400201a20246107450301c0c51000a004ea4440ea002004e040791100070b000300342c1c600340b1805407203401c6001c049011a83d01d03001010541150780c050018203407266603001c0b40f101e1681511414203440079130b12803615010440c03142c202c40f048031100d00050303180000030625100000c09000250900114000000301000000c0900445054404252401400712035641c1c0c0d4103441d408962203602c80024803d41c45200f21510036030701030050011841e054692004400302501c0111003040d0030000c007004a02c9400480000d0528000c0241e80e0303514120b001408107407042141d102c1424046842003040d40300140096042c03805440c9201c91000c16401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 490129163 1250 490127913 490127917
    0x904031101020403330501051e060909071e0e030a0602070302011e02360d03020f01050f06040506222408030c070e01080607050711030a0318050d11060d02 68
    0x4200c13005017032000e6403503085203050001040f04a031a00d200c0d0550404031000713a0300c007131080507001807003008907007020109103403100c243d0000035214a00d002800b07008600920411a05a0300180d2445a2601e400d801d251003c0403580c09803901700156481e00c3c00080c2c440e184082c0007010380764000b81000400d4000e421482c001c041710740d40c038442e03500201d6000d000b039400fa10f0480c031220241c1c599818010b002d0703100f0340c200001880e20b0780d0311034a104040c0580301845000c00c0d03083d403040544c4040851400d0040c81c0c440e42a40c1a035142e20301f40742e0288000d94134013410f024454480400604a088101410314611b0510200d001c200c805075a4120280c0b1891803500c0351685c4c11200e8041440c1c00000300a00043c0281001c03200100e03640c0740d80700e101c00d10a0140c03040c950014800315050301d10501c098a00750380161442d4004031040d40000c0d1a12031204030403400300d9905501250111954254100104800d41e42e100c0e01d540b44ea0f40d114908800030b81140d01c01c502c00714031071900c0050350741 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 490130413 1250 490129163 490129169
    0x60506120327030610090e1f0b01110d0903120804020913060b030f0a0b01080102040302010f0f0203090d0b06090606251b03140105070315030f11040c0f020c060909040311010204 78
    0x804d84059061800030005000854011421602d0401007000124040014143d41d5200004100c8280142c4580d02c0b10140459400b52410000c280d120200404018030805558044903114680e002c1c1c50361901a544916044030714080c0a460410840940c9403100d08030f03071100402a840000034105e1070803000401c45109003942502c074440e142c00b50104005a266040b501607940d200860780d8500e4654240e2145000c028009050409102e0760315000c1c00c9110f10907106401600d0405440780c01045c0116000501a1381d1952000d0900000c0d013041d840c138582080c0701742e643d9072070804043c5a0f4034007000b41465034000d0750290b4800c82d09120840d280c990758000c1e010380219a844e0b41e410481912080060805215441d250204518500034804c208044c00c410642c00002491621600c5800042800aa0f09803a80c50800f000f50b640320712501070320940b25107032403038440704802000780f91165000100b030040504001420880e903405410960041d13040c40c00003d65545400e071140640a0781d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 490131663 1250 490130413 490130419
    0x100204031128121b080d11010f0515100206071407030c0212061f150305071b03020304090c0504120602090d20010f0512160c020d0b04060506120327 65
    0x440030400315100030122120601500c4144189a010203000f000035841d071181740c1d0350b9844122465009400340260313880b0064480000a1641c51f00161f59003600ca045800d42852106144080800c0c80d15010740b104000d46880201002c2c0362844000e00080e490008424000001003000b0b000c01d07118840c0c07a00f100754003a10f440788160400041d135070340d01802d0700c2040c3c0c6141e181040300d090b0700200f20040d084510016070260a690200ca0a900525018100304100818010700200d2195200310000b03450344070340c2c021681d445c604088141250500c0041034108101080100309031a0705004203003c5d541c00c07680041e540c0148200060b860524081c0003084950400c0100340c0745c0c1a0b60b03281e180c1045003a2222400400450001c03140c0b03101d05420350604074802c0380443c240d050100000b4450b000b045c100700c05041c5d01c540004500c814103140464800001c2130070481004040c5c007415400c450107552103c91b5014a00a2540724000d143c4c2040481840c4813240f60007404801001c29622005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 490132913 1250 490131663 490131739
    0x131511040f0e010b0f0306060310030807030206090c030a0819031d0105090d0f1d150c0319030606021b0a0b04090e1216020613080706020d021002040311 67
    0x1040e860031040304074414a511002c000d00002401d04a400c2280c0324890341d59025480e59583c0b01c02c1101c1500043c0c540007850300f00c4800403000500400003841038034002e800910031484d02004003403814600d1128580207030800c11620000a400000303840700455100c041d0402e20101c400c0c110002c207552441004016900340f0512007440701980040d01400c44041540e460140b910001d0328002e0340e019105000440211244448403001c84003400b003080b00801007a6031045203044d01403540c00400e0006d01c2ca400004422203002040c40148094440c903080600103a851f0440c040c0d10341ca40000200c40028648541090f180d84042040c00604840301240d52180d841c0c2d0300410050020002c00d50142c03040810307003c4407518003030a860030100c3c141c0401000300095170070b100319600411802461003105120100704803000340051303c090703c190303402003020ba140003000a18100c2220380300c1002c50b20400091022690b610408690441c00362215892400000a107000142801c2d80e91550f4003c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 490134163 1250 490132913 490132919
    0x2180a1203080601020a1a0411060307030605040e0a030207060f03020c070905090c010c020907140702090103050609060a0c0f0806130c0203040501090e091e0304030605010b040e090613151104 84
    0x1252a1a1046000740d0b00c81030316584102c01a80d49001d070410103843d4036200b4160344803040590074115481032246400e03c130341c1000840860060780050f900b140c08aa1240414401400e0a01c6403000040c1c042005140f040b050340c40c042e4a5807854040c4a041140c1b02204601250180d0122180766051030120340280390f07207480f1038000b020103803a190400c1c06608441840740d0f100d9400030101c0e0780c0040c4581c1c4103403100384090b12140410b800004043c0701c1441948003507621514038500a50240002e000946080c280b81d6040001c01801d40d03801910301620619070350303400100114441082e0819110302d4a4540c0000c860302c0c1d010240e11000b0b4107001814000642c044050401c8981c21b0700da1580b4907803180700d4801c0884040300c5181c119404045000d0385d0349041507151070484604c60540e441d04d5200d031100b000352002600003080718080000d0070030241c40741810143d4004030300d8010300418200040d040f548030b10600350152060b0000d82822800f640b9661003500c6801c011100c00340e4690b5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 490135413 1250 490134163 490134179
    0xf05010c0e030c310516081308180a1215051302011409010c0510061503020903060601080601030f0f0603060c140a27030f05010506030c01050a0302180a 67
    0x22042038a03000a94141c078040580c0c00d001421508683d001403030288461950400b0f81505409509101c1c604103042594078030b26482032082034021907121124042000610790f02801940c005041682c00b4001055590b000c512802c1c2a11040a001c1951f4840b10100c600040c02c4200290040c4a10904140b004000c000c0800070101c039503202204240040e079105010700d5191405217102902007800c2c41c2000c641c440c4e298008091034081410b104269102503140e070ba00c1e0640844901f12000d80d103000500c034103003074a5800302e0045054075081d0315001441005c00c0d02d452000d00441d051181050215000e42e003c0d810003c144d4003003540070130a403810140c1c150050401c500c003d0301c40764074105d036600300360340300348045c0d201c3c0040c0170f031100c3ca03003400400c0403101110300000740c40215a2001c0600b024811129203400114001c2c4500201404c260810701d084600192a280c0700e030344040c04091036a41c010090b1204140541001070300c03002c2d420345c100e400c00c03800003a03140e1055014601060f018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 490136663 1250 490135413 490135421
    0x7290703020d3209071a180406051e03011116020a080109050d0507050a06090303050105090a06080c0613241107050604031e05120c0123041e0f0501 65
    0xd0031124180004044000c0380d690060000328010883d189250a030840d070150003080c0e0b03801444d02e90450b007401d40c2d5420b910329480d5800c40e8040d604803000801c0070301d0760b00384031441c03218407401c4400b0442185414006403801004000303007001c41004000c2c1030313401c2d40c0c2940419600b5040d02005580c0380d200c850740c1c09003600c03079a034101d00c5100d90034400b0440c604140302d010900e503441030007800b03103c0712400e086d2602d41040304216071902c6581c03a07540000d80203001e81c404252103078030f0205095040004100070440000c0014103038628009080000704000200805400400d0360442c0d80c1e1400406401d403000655040040c051070340c14039098454042020840c4541c105580c3d040d00d9035100400982ca810b40c6104803503104d03000703100510101c1c101030700c501c0300703020021a240310358001c95a6450400445c6c48503d82c0e22440440c1ea800050003e02451154450b68540207200c0140f0102080d0010f13400350001d840d61b10305203070b8510801410f40300244404d03005101042d00781b034070b440c0050181c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 490137913 1250 490136663 490136677
    0x1206030c09060608060d0308041e05011407020c010e0108130f0f020f01021c0f030e0607080105030c03070305211201150201060e06010507060c05090d0f020405060d080729070302 78
    0x9245400790003d091440f40c40c14074010707000104590201d6240c2d4400316106da0005d48252000c04858542c41440d901c1e103602d202c081c5100b64000b041e241c18002c2c1da140039071001411107003503400811120605030f07030007880201307090401d00304800741e500c0e058802d06109141c10b0005082202140c074038010300c400a114402014800c8401c89906000d80004a81703031500910301048034a405014244180d000d41e030642c1c10825075150000308400007180e031503e000d00940303c580c0404d8402005000c1070030107104028401034164000e243d8940b0b9607441d01e540c1c440007085003000c9200d10304842d90f18042d880885a00c00d0003410144071558546040d01015070f009942c0ca00950310b40040041c0955001c0308282c4a18416103403030b400c22807242c0b0303550040e2406c60b0100042110400050003103a03111010030310254000c078040c80f0b01c1d00052041c403080711800f611035032250070805d400703e001030a02030881b403040742d00180700000b410907103d004550f40c407002101e4094241840802000c00c0c0c0c190702034118 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 490139163 1250 490137913 490137929
    0x504090602180a050604032603040b040c0608190f02040302060f130509010303080609041109011427011a090a0e04051905370602190e0a0e06011206030c 67
    0x11051441e0204281c42800780305154100b60280010404903070070080e10042d00d0f1b1022818a915595031181400036170049a0482d8483c4064bc203000c01d01c0b400102240141c8414200902e1905100b1459083c4503070815040762140c1e100c59800144482c990140d03001941d0262000313403201e034856105407480d002404072660f00303510600c001819160180c0e0700c40c126034050325510201e0302c694040c09a0b0000c003d0090300c414040700704801c002c0d12001c80b1b1178020048000c0600480116800700016a4903205540da900c031903111000c15040028107003581100c0440129240071100208020340c03e01078254925800343d1114000590320180c036032558460b81c4168240c0c1e40d103900d0b004207240850003100014000d94441484101c3c1c0d00a10003010780384005080001036402070200902c0c0111002c6001164a40c0c0c003c1005140345800c1048001c01503441d0400c089030780c5091000c900c200c0f45601c5032010b10707070750040442c0d400c0e4058400215550a03844080c4079083e1039041107240c0c04554450080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 490140413 1250 490139163 490139197
    0x201020307080702011404030822060c1715091306060636060503060a0906080f15070e0409080c0d020a0b01050f0f0f0102030405090f0a060f08061602070504090602 72
    0x20824410702c1201a03040041b8090b0145407203d4400b11040440286030595800e424603004100705d8500710f00c00142449144042107601080d0703c014003103c0805440c00c901c070b603d40140401c507900401c462940c0b8500341d90400d401c1d0b90b41e00e0f00d00450300d6408000341680d4130784a40413030001d40c007584807017820100c480c61542485490016040c0b01d150000900c10400e80c3d21006e0140c103201710019a0404801400b001c800c0303445001c1482280d850354044c1d00c0fa603124003c60480020184004504e1401d2544200800d240480d0054050242d400f01140305507585c603a58810800c08105841c2d400840f8002c948140c41c0807100695100701e00002a140c440f071083c0001054507090304410184070016240f00b1031340d20180f05000130180c1710b000203810341c00140000304190b1682c00843c0c0c070802d5054801c481030706210082104a4000e600324140814420205000324000060110f41200086550108060103040200e042c1107164000d154484d04103040e16083c4541d68019100300c14980028076 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 490141663 1250 490140413 490140421
    0xc0c030c01050c1905010e010e0313051504060e06040e04121103032e050303030c07170306011e18090606030506060a02190303181415151c0210020102030708 69
    0x5107183c09561503a00465004d040c1d031480c106107440465241a01c620000b00c1c000d02d030025040d081d254601c400b10386a038008202188041223800040340109030507552080c070007020f000c120505100380d02540e814041c414504501a881d00801c5a004003e01007120180341064a004110a011540b40d01c0c00200000040b05d003010020080724050030000034621384542c5800300325544840741c241d03c1d2540e50340c4d080d00010389403020303c01903205200088600750341d03207524909280000c1c5000c3c80525010428010001c0d2a40c100039a00001c541720034030402280a426012265141c0842031004001115880020182a1f54000009170b40c050385060041da0345600c2845024086c01c00031500607130142019000d4440c3c07490900300298081c1c5408100130003075007044d040c9210b030441c0c1241c0401142103011000076040c400403000c10f0304403071250b0403800c2045001100c0300c003810340b06100300e20300c2d286600b41e9907400c0038400f4810303070182c400084503100c01c0001e8000d4100f01d03a10808214060002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 490142913 1250 490141663 490141667
    0x309030516060807030b220608030a2a0201080a0203060402090301060603020307020d1e0f1b05100b0609010c140708010e060703050c0c061506041827050a0b0403050702060c0c030c01 80
    0x1460b40303c01c060b000b082c2da40815488056850206100c110041d40d48100101c2c9c580410700052401c0d85172601d46041c4580000c2840540004016401134450701c0c4034032450040c0ea01400d903541110141c0300150b1240c4418000400a10899040603413540c40d100b80005c0075a01074001e103225000f00e40942d041884440c005440101b50211034403030040036442c00c4d00045001d184907a83c10419840c040e0a28052000c180c40040c4c8800015551a84105201a030319102800340304190b01c000c2c2c0d8034600300070724440041d22010100c40e00a0050100d10220355070350700108245401050301200034007030000495425074a412059941c2000a42031100180c0d6506000c801c80b900b40b008400100035641d01c140b2103000e00191388550075030013103003080006158800747e0381600c03410030403842c00160310049008100d2180c86142c205da200c40042c454003030201c1c0c0b010403400300340c64120380c5030b007829034032407030304581754400e4050080d44140080b81049118400040c003e44c0c7c20f0094044500c004100001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 490144163 1250 490142913 490142921
    0x170304260a090b0d0914070305010c110c28030b04110111100f09020607060f0e0d09090e1005130510140103061a04050a0f1a030c0d030903051606080703 67
    0x1280100c0c481800c20000142140e004115403403804000181007241a0ba034a0190506c040c50300300030b0f0b400f800741030052082c284501710340c0c425142800d01d03210724092403c40d103d00a0540d040e1049042c1941003126a00700c00c50003841078003803081004896143c0c540103404810035070f41654841d40f4400c42d044194045c0310016103000550000b03041040f031020f50040508031103a4503120031602c541031031005131a0303007000d000c03480c1c440d10010450191019904013158260b8280c2541c90384600c4155800380e070018a4a001d6810181d0b02040c0141c0c030540c1c035864420110020f10341e440c504010048000f0f808280954510b100d6010b441454128440d0308040d00c0304010718144d09201c0400400000b00d199001200ca42030350b1910707030b03000a2100c001a0448204071030a00c0c21a8136069003000d0f400c0f181c4141c00803500c0240030b07044010664004aa81d4001c07040080b8011150f003140e08007458054000c0d100190f504c20219810840003210302545403000d07205507030203c0c0303220740425902c42c0a801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 490145413 1250 490144163 490144177
    0x20409060c21180f06090501022106031c1115010609030b0106050423040b182221020f07030804030b071e12020c19021f0807080417030426 61
    0x80c8401d03e424050700c407800c0030407100707404568180c0c1d180d99060002e042030000d0300c004510351000040c00c03204a403540700624001016184240c00c8092071242e440d800e803c01885110301440c2007075040c9800c3c8407003441c1c1002410702d4107214560200004070b940d48004408143ca1040b080c00c1c003282d990301400d07140c0d030040c1e0080c818203041e101388801030707105000705400c400b405c002c10102da0803181c00003145c08000344460f00c41c840303410002008901c00032a039038224507030b84c8102c0400341240d081e203c0308603510354941c0794510320204007100e0002d41c5c420004910300c0780b01c48003030300ea00b13540e280340200c8260b00521007103440001d4040001e101e240600d62208440314010622007138505000c1c0200d4050200342ca442030525424405207011110820562042c000015908094112580100460195098046d21800d280c06207034064455010904030340045413418903942c0394a030f43c0740c2811004c0c800c84607006410f1002c8100410b00142c2214421a4030380000d4030744025940701400021846008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 490146663 1250 490145413 490145441
    0x3030705164b03081c06080708060f041410020706110429040906030c03060e0c0307090c0519021516020a02010e06040b040305060f0604090c12020409060c21 69
    0x100c14606600d41c800c080b044840c0e0b2003040b84101038030790766000000d0b017020705042d001518210050040044138810030001d041d0400090040c0c602c0c0c071280175901c010050800d10b031510343d0320100c1c04009400580428240d99142a5807441201c0b000b2070740250410310301039400c241040049984000079004072002d80c1c03075510140c00748080e062054048480c0c20208074540d0541004000750301c090300d1090700061445241c000f141c486c034600f0f084059400800050f45180c115281d0908107503000501314040724a5500003090100c00d051041c1c8003809540c49060b4840d044c1c4411040f101d41c04070707080c01d82c21400c004420030f030384039802d01ca101c1660407400131000da444143c450780958050720544100e04001800185016202c05a0101c0398000d68002c990316403020040c4036800d4a0002096885081580c042282007095200e03814a00038911500e600d100c22451250155100c6802120007260030140c240310200000310300604210f1084040140c075540000f030340d070100d4428000ca4450500304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 490147913 1250 490146663 490146749
    0x4120302152805091c030c03050603030405060403021002071503021b0a0b150d020d0b010515090a03290412200c040e070305010c0503010323100b0303070516 69
    0xb0040103002040c02804203041481140342c83e40da080f0b0840c0da07a01c01c220320742c0d40100d4066403000011b03041e9000544200c0c8a0380081c0424005038072044292800c403a0102c410900d07004a5500503810100141c01045000341c03801813414645825800a1810310b409500886503104540030311074941c001c10303a00401100b200000300d55524400100148546d1000300000c85082c0d1310b40c00070300c04103034a61003144c0340141e138401041280760240210b0f03514981c50b5440c0d0701c1c0040c0340000400c41002030100400d815012a40008941c081c50300f2288641c03002ca040c0300c02d038186401d15007086c48005981400058400225150b042d405030141c3c42c40340f50307200003401c18061aa08100140c00c80040031292446081c60000215900b4000c0c00b181452540f2526600d505600300152140f200c100b62008102c81100030440425000409289414036142c00240e0001e050300003e066105000000c1e2452142c4038443d190054220244c0003240c0c9030300c0b01508841c0030054003003060101c4c3d00040c01070352a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 490149163 1250 490147913 490147981
    0x15020d02060c2a0d080708010b0a080a1d0c091524090901090f0f02040b0a031a030d0e030c011e0e0a1d0603010605240903030412030215 60
    0x20354090304407410009209074103200c48810b2940f0303031007003400f90340300640c05440420491900220803640100091074804038660518240c0311300c6104510200c000c00200c030700002c0c1c0c1c0e8241070f40300245032040c001890348403500c02e001c115910701031006114880d100e448080b171210320403000e13843c02150010b0410000400758007400110f8401146100c10b0320902004082955580c0301c3c81c8a001c5d001540f000a0b050341d9400396481124000c14007040080e00c10032061000c03100ca6010341d01c0380c43d003626001c0b0750303141244101462003101009030f0790148501c8a0000d1410b402107011303a46a4015012110b10222100044408039015410100c147c241460100c40e8980f0407201d04c050504054080001a65108040711441d680034031240c008a02210503c00795113000e002d40c10062908030340f40d0415420881602c042075100340764100880138002055542600d052041d280204000d90034080005030b01d00700a511250f1482090704002e6010f8006890055200703030441c84140626810882c0c821 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 490150413 1250 490149163 490149181
    0x1050117060f090f041a07080412020c06040611060a180f1106070308040227010527040803060a09020703020709021612020d0f030212060103021c021315020d0206 71
    0x10000d4003094110415250150564990003d0640070300350141c040720140c0342ca400c24808402c0e1104250b1703020042081032180a40d40000101c1c0c00c1078120784201001c980b1000180c6c5000322015031a5080480400c0c0060325a0f00305200b848400c000c03009540480e43c4190201c4111107803109180515036040f5024030224545210f0000b1f00c500c00e0107030080c07001f031a00000f201500201d070101d0009014204110031400c0800206000180000c80d10948070f42021090180013414001c0c43c1c01865140000e59000c00c010080440c40f2901661402c020308140c1800c024030781c0300304d80c12802900312036800203000b00144200c41403140c0560142c008103060513180400303940002c0b10444410b41e940703140004502440d00001105906400404031894095005800094611041000d052041c081080580c6424030150b0f03001c8000d00e0b00590761290180000c441a501e40c00001c2498408108144501c1c4001d540742d00b070341c18a2400d0000c44e032602c1c0d0101d940d42185118000180c00610105031541 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 490151663 1250 490150413 490150457
    0x31d0f0d08070c1706070314070905091e04051b271015080405010506040e0a02060a0c1209090b04051302040906020d0c0201140105040c0c03080c12042405010501 71
    0x20340724482c2020b400341d55041c440595030510036644e1250b0407840038440c0458051250b100100f074601c40d114100e2400000c050042d203410300c5258050b42150303000030503513280000104481180390340e042103142410708005a0340e0400e00001c650b41c00b429401c070842c9181c03070380289070340306c20041145c059890f040e20000000c010280115000c20150640442c1046480120300383c52401551021030314500303410003e094490180000380207a1420305c458980f80c001140b21801c0325010b94050350b84002c1b03004121080250f92401500704414082852116544034002d081240d0b1011401c5c0002901311003084101c4405603800d00d030041c210108800107090540024409038025200107080812940d5004c0645440007140340050b5980c00640d0107982d110000b2a001d170400352410011840380000240042000309006800e01040070005106002d219045950031011511101f9460405180c8101450003001100c8250303440d0212503801c074166441160304980c016500d030909140a60010041c0b4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 490152913 1250 490151663 490151677
    0xe060d0b0303090a0305060411040e030d0e0f030301060c0b1018051803031501110715080c04050d0f050d0f140d1104030308061e01050d0e1504031d0f0d08 68
    0x503000034856003050740d45130072811004600a90250145103010b141c0304030964540a901c0780b0441c03600000300f40d10300002068800380300c405000094032001041c00c01e403401e2010389103501d040c440000081003165110ba507401d02c9602c51802a060b03500c507004417a0b02c0303070840e002c0c01183c880740b0b0400c05040d44281d003050790040c2013040500b00d04070a003005d1600316401107039a90111040107275010202d59006d0f41e21000c0203e0745020702122414410740746070400c03040c0844410801c00c0008101d540c080001124018040180040700d408900e03c0c0001241c01c80000076200342c01191050008507001d012080310445003507481c00d0b0079078040a80c040319600480d0301407500d40e0399206200404200b01c00208007650082e03c4200c4a407500b24200030b030700c803800b40d01e070240c02d600d00e800d00d4010398203d416188a0520200081011041031a841d0b2510408840254010f4048d00522040c150400b0310b0040310701c1301640b5200b403844c1e820305000c2001412406d40d9001039880d80710402150742c0d18080c081c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 490154163 1250 490152913 490152919
    0x10e1b060d060b0c1b1513080f0c101d0907030e030c010203060a150f0e0d06050a0f0f060308041208090901060f0f0903020f04051009150f060e060d0b 66
    0x524800c14000001c882c0c240c0c11110b502000021036200700c4400b0450030300901c0060b01d110382c0488881e4046403074024034045400000d80040389400c1c03807aa00000d0440503010000403508070840e1000041e03602e00391082c00c02c2c003c0039100941c3d00001d1081540110501c05c0d200020141c0c03050000740901c00500801501c101951510b001d409004280020310b02c40400e0300000da12800d021040007032091855001ea245000d4648400c43c0c2c0070782164481000c42882c0c02d10543c91100b0401190100040120040601d071500c0100701100d0f59a9026205000ca0450100030108075403804004940e014040900486801d2104001d4001c80205c0f84c030304103105010740e0b03040c1141d00012a031580401c0e0000404180381021211516030301c009140328103941440d003400020310f0741c2c0210321a551f1052416005a4a40002491181040e6252401440e10900c1001019420086120b142003c1d005a0480d0b041e0500d00040b00d51055810741d818901c010102d501d00100c103c0984e00401d00d0aa82a070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 490155413 1250 490154163 490154167
    0x61c03270f050406180e0106120609031d0315130c06020709050c0301060c0807020d080a18050d0308060607031b080a17041709030709021306020f010e1b06 68
    0x10100440d084068480020a0344a00c540c904040c2021031000564100301d000d1482e200041180108103e08661070300c01240d40010f2240c2110400c1d409040141c228401a0042400308010000c896002c2d4105030302a40d41c255241425240c0170f5013850303441400c1545540f22414250a10302c044540a0b08880c01e0490348010036840e9035421041c070910790102001d40c01c03000d0100003850140c010241e20504c11241c4038650340c141100505514034528001c3c0c03140d000801c0d404115112104800d1204e074210916030785415021000a08001d0010980352029021000010300b606020f072051040c243e264a4495945d84e58009020485d0030414007a401c0105203480e00143d1061070382c1541e61a03010b010407030740c3d46883c0c070740c082c0942c7c030460916524154178508000c08a40d58485031b1980c4005288401d17502d00c080070029140601c035400c40e0408920002d508040881a07001c2e46c001c0710a19001e07107000740700842c8811f0032521102c1c0054840d800c0065481ca6086e0382c1003071048c1c88038001700068 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 490156663 1250 490155413 490155437
    0x240c0509100306080f0d0807020127061e0b01030f050408071704090e10060e100302191701061505030c04050402030712020c150612070e0c0918040b0c03061c03 70
    0x1601d40110200d030290f8035008040d401c800e0300e0340705440c1036002c0581e0000303000c04520203c1100c0b408026002407030829042110358030801c4216045000c040540c1c0c0c815420dc011080c070040010000c03003582a022a190014140d9490301c18041c4034400d41c0c2000d10141420010b4617400d210014800440c01030031010040818144214850341440c005181c0040401c455084981012151750350401600104d45c1c03420405c0341c5040e41c89000c1aa80c0c113565134215840800d4403110003044079008a01100e074103001c1c9403504d40c0f0562002c4129250444880b004981c50b0b201511680302c25503201258440400052007079003066002550415031034035050b01441c0b2031000f4601240c2280c4400c83c3e140e040740d5104000031039440c0045400c040204d03150000c0c040400c2010b682e4644a1191070f0040c2d0f0248001034407e003113101a610386410180010072610020710328984c0c0024110b40450300d40503810301041554510b541580d2240001401d070144074584240c100c030121002003070031002c0001c030712842 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 490157913 1250 490156663 490156679
    0x6090f030319150f03020405180c0f04020d0603050327090703020f120103060f0c031109042003040b07120b0d03081f08010902120f190807050604240c0509100306 71
    0x143c004000081641d01d4050440c410003050700e4014240208000810700c3ca0702c44d107000030445404109080b5515001c03003284002140290041030800c0301068038214000041c040701000901110148007420b00030010300f40d800d810a041c9004003d41c0080c0c0100c00a80d6841c041e6005000c44010245154244407101d501c2071440c941c02d130412a1465200c400740400680300f4099035260008508050100008100a008290041c113031040e101d9a02d4803090f4607040b4002000c105080c020368000c0d075491405082c03040403144159400700c0040e244045a03043e14413148501c0d81c030364400030680c003541c11440d101100e13020f0001d0001c012149840000342c1001c1c000082c0f450090903000004901d21105004004200003038111603803041d080420700d03403515840031400d07030201001071129051130740d00e9040c20b8605000380c04d00140745101e024103101c1881040d00c440c070707a6401042c3e0300c030f064400075820354802c1c4c400c464070740c0300842e40c01e0054400d1440c2c921443c08006105250002d00d941d507481031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 490159163 1250 490157913 490157951
    0xa081b0613051c020d05091c0f140604050a320c1206190c02150a0f111603030b03120d0203070806120304050105070311060405070806090f030319 64
    0x11810740e094441a07101004000d0101c4142c88601040b8100440b5907148080d45400707401210008008000820038401d13515031209081694040b089112a903081e4a0200161036044106403680b410058804101c00e40005200d4807039a0700c1000380100040700d0342d0b500e0040e4100300012405103601c087d401d41141c00044000040c803081d50050041c54002c40501112401d24807990009030044000c04c800b60041c6420105132200145001030a02031400d0224240b940a64400000a0000e0f060105c42c444582040e0b0a981c10340200300540c01e1000150782d4288241303141d000d071300300c0240310341400f080c0643e02c420f84004014090340c42d110080d003030070b01c0540e200e642d129189982c00320902c201994030a00d10755106c00c00f03507015403401e044020030542e40d0140d440b83e1030410900003080000c262280314a1401408803100321001030501c1d01d4241c0d03c4024900a8080500c91080050142507000854542c2009600702551442c7c0310080007014401c150f011261100703440c1c0411030011000508 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 490160413 1250 490159163 490159171
    0xe160e060a05091609090b0102190302010204050a2301080f04020d0303110d090b090303040c030818060d0905010e0309010f0c0c031703070806010903080a08060111010c051c0c020a081b06 82
    0x19080120144d03d0000750025101d0703006100c0d81858034040c40640d0b40c00160107181c0395000500300b400254241340c101d01900c91a00203c0e080000044005032500c00e0f0301041044000c0c4615022420011400440303403181c007140d00f020680895408200581010004130003031602078500441e4001c8010b107100d00b40d502441d51602083da460039000144880001403941048111000d1031840c2000c5c1c984100d000300c217001c0500010000900400c0b492012410903011000142129846080707000f940401850801000d8a0700d50800000384d800541c0441182d2003030f40c05071500c0012403c113480c2262540e0000030119082d060903680030003c5035600e46070045c8541c040d68050307501c0c075040c00d000b080030401900160600c40b03210801c0c000620540144c40c06138185240945055980d00c00403a480b40104a5140207940307000c003881c612544c000000c040107070041004c070841507004d02e41c1004940382100c504006030444031841c00002e508000030a0f2218100318030003e00b007140c00c0b0460800f50b041e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 490161663 1250 490160413 490160431
    0x50c12030a020105160806060c160306020c0f070e0a0b010c0b10210b0403052b0609110304020303040608040320071a030405070618030f0b06040e160e060a0509 70
    0x7160402150794240226507006054681c501e42c191644040500011400b810146c418440820303c0d2401140420601603007a8a41000b681c805a07170b41801d00003540b0040ca04525805070400034150408002007c02c111440c0c5402801d503036036500d4480c4020960900100e0400050801c1240468102070009005885900c20781d0006890600501c0e010790300c65410000d0b100c2c585003610040f41d14210065485509414542e84c1c540151044414901d540b036051018102c112180e0f0a281d40c1d2075001d2410782e25540780421072103443d900d80d82c00d00d00044600035490382c020402800321511480485403c5803090406500380f07035003011582104450340074420b446038007040081208038007900b04044040070b03507202a0300d181415280d4a45681290142c08113110315014904104c1e00c43d0a90032008540148421806070b000d49442d035150241918124070503418900600180a004030f040c400060b200040001c00c189040e2010040341c40040180b58485010b1600149989500c4051441100b810b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 490162913 1250 490161663 490161667
    0x70804050f03061905070309021305181b06091504030f0204110309030a0807050f070b060a0b0c0a0f110d0308071d0f0d06091208090106080d0e0d050c1203 68
    0x200c0306012000886249080c803d074028001e00803e040914000c005a42c08014003081641d103428098010308801c0c070000b9040062000d05c418101c3d12903100038008d0f20304034900034180f0301461b4410381d200700c44003100d0391500800c3c1c00c1e59820302d40b41c4000d088140d0b011302404d128481021446d1500e030015402603503100001c3c58100c045203018490300509240c2c10300c0c1c80d41503040c81290385a40f07015034880e03041403107020000b2610081c02a000c4d0b50040188010b200d644022a14010a03240c0c000e0324014000d035a8054041880c0362044180c1e03401001860080032511107a4841044000c2901019a16820008003d0240340c503652241488503010742c480341141d0070655802403240301d582d0240021302c2c1512002e1205a40e501c0701807181e5040072540d203101c00d00e02c4e04040d4000c0900d408001c2c00c0c0c03948001c10854017130f088a502d512802100c402003003d2907031048615122090100103400040350342200c1200c41c64540740051170305001d801120150020000401c8840d04241340300c0c2c10079840 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 490164163 1250 490162913 490162919
    0x1e110c0418030f0f0819090203060c0d182a0503030414030d0309080f09010311030a0621050d03230129090603071b0f0803010303080f090a060f020c03070804 69
    0x21030384010403d02490705412003021000c0003000000040d00802010103014044a04c040c89074000d2078903103030010150341c02802c002d00d103000d40342d0000340c51609a50804078850308404400540000d0581c0101407000e01d014298084243c0711407008240ca000462060003064548041003d08007800d4901213000d0440024010145840c040154040c10103082001190000d00b140c0c06443c84004648110303602d842030140142c000e0150300f0315000141e540801000344c0000560000c10448420442610300988000f11555650b55009000350059114501810b48244a90321510030101d03060407901c08452004d0305140d903043c1c20783c0480b0b00c070700c1b071245000c4415180c044044000c50350203c1c12850000e014001c54203902004019100f4031204040c1c03026031204c408490200203510201507001c0e644035180000594100380400d4000980c8500001e640344900c104442c0074840150080c40210099982c00307001d0944c84000d010b81a4003807000d500e420000700b0240160078410135080382c80300e00f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 490165413 1250 490164163 490164167
    0x307210c08010213033305010302091e0123060307030c02010c020a0c090b060f030f0708070801120b040303021312060c05030c04060e0a030b0705030609071e110c041803 74
    0x100d801086aa0f481002110003981c541c4c806102202d03480354040300d21031900c0c142000d8846001e030440090311511888102d05411a42c03140e41640e01c211040402502c4603103008825210b5441d0684400c0a44401442480c040410840007160001c80c2e1904034200707a001f1030000e03001035400001098944403543d000507020301a402e02c042c0300744010400300c0c0c559124100c1103d1548100710b036082d5a00c0020606464035000c4032050110350603800d5482c14203d1034101e26042c21141500028000720124031494070580f1024101d134542c0d10320000d40e00301c0e911400000100540308805143d0308201017890350000006100c010300c1e64101460500c905030801e8030544900c0c5860008200c42001000389024000c1d00b1399043d2491407425551030500340d0042101400c1c950005441c0207490410001540c0e13020005510402040c0c1c1c1181e2161640941074624681020186003000085081d1118092003808140344001c90041242d19002204000c02c0440d00f14a4100e94031144486001e0149a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 490166663 1250 490165413 490165433
    0x13050402043306051e0309160f0303180b030103110f0a0909031106040803160207050303070b0612010b01021f14041407080705010e0d050109020306152d0f030721 71
    0x2c00181001ca10f4059641801c912117801d1000d2480c00c05404404501d2040d402c02180c84500c01400d004040c1d82d1300e5010440d00b200c491302c0201c000811aa20701c207201501a0310400031200c0440c0c615007141d08558900b905050014000d0740c014052088040440d0b0303902525400402840c04009021101814018102542e86070340302100d038007200c00c0c000018400c50499a00c500d450302c2c80191286a5001207080c880d240c1d002c0f507403604c40854800300b80300d03600030014060710342200c11420041c807140000c2d00b6211141c200c580981c0010200003541018500580e07981c0d4800703440090028001158580c01c0d1205480a44580307802d100e100a0b01803007080010054000c6038000d242242c6001d00081030385245414007070003840d007456003404100003500705c1071600794010107607610351900c2e01c1450106100e140d1a2881061840c1030021004082698a4025007000c0503004081c9484400e12050301040103450350140f10f8a10b00080210851440407400c80449148a0341e494003410000b03415 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 490167913 1250 490166663 490166669
    0x70c030b01181812210c0806040b01080604020a050c01020d09050c01050717070c03120807021e191103101a090115030c030608010e10050f06130504020433 68
    0x1040c5030810f06485407010465994403940e001240c1e001c0c2079810303042245d402c28034a0150001001003200b40680c41e409400c06141000f079959014415542c800801c0140d8409601040c0440c0e055000b28071203040980041c01d00700b000703080c10b130b01c0c000030020300c036003283d00521048000951380c504001c01c21800384416605020f00b40780240c10200c0f16110b500143c05107005000212070005a40010800b41030125001560401301548404d0100c100c05000020111500740041c010590300b0256080c0498003000c2c46041e10740200204011600c1100c01040c0c500020340c2c0820b0300c024010403c1c1d0301002980c803001c08007500480c01100050110307050449222910b80306070301c0c0e0070041c800e890300f0304289442c0c50440c0c503001c41c045086000607401003915400440080d424883c610107410b80000c0e40154036410745000700015540d8050b695118403043c0c801540c082009103036020a410355400054001303000a100051202c648401968034402b1511080322082c4c1a8010501c6000b40407411f02c02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 490169163 1250 490167913 490167959
    0x4031113060b030109050613020c0c0a0902040605040905041a01030c0e09061302010305041b06090611030408121308011d060a060608060103090303141806070507050309010c0602070c030b01 83
    0x4902d04004501c0d00900050244d01601e9688000090840d580e440660b0701810480d8811507a603800314070000d46a00d4a10720300c81c0158541c2d08000f5541e22540700712401c80380f00d599840e0502e4104070716100600f0000c0d001f515002803240040000d45041c1700032030b000714030030204540c010f807508070502e40380c103002090303095103400c4a020045109a5810345850455091038001516034440c80c14000100750840f1411448401ca140410742980140584059031096203560500e80d102c119102d54074841e5005581c0107411407515400c00f05051405007403a2145d4400310361461383c94240a500311001003038060084400e0fa07010241d298400e001045c2c01200400090148508210000c0c09401024200a0405a440b100c0c102413611950000803142c1c590704a0150b5030410103041d0b100c40203d42ca40400c01d02a0b0400325408038042e000711286681c0c004003640c00c3c00c60741001910104012041903402d41c0c1c0800c45031000603603040c800c0d00910b1251702c0038042541480700c0d03410000344818260103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 490170413 1250 490169163 490169171
    0x60314010b0c0304090902010c0b09031b0115030210021e010218040b01020a1514130309060804030206040204201605070602010902010518041d010e0c0d030c060b06090604031113 78
    0x78402e0004400c07242036801540c0c001c28a0030840c40101d03540c0d0651400a00f40503d62410b0044140010001740400d030240440040440c0c0e40b000e5060888500078513040300340034061300401c01030900c2c580340d83c0f205020340141d030044444091038400c13242500c090105580d500042080010424441e4812151030584080001212043c0082d60307a500603a4041c1212803041c1e50000450710a0700461340c40e807440c034145806418180084407003002c4c842ca00b100840c141d41d0007c42c125210300d40c0c80f4403c680560040440c1e03101d40d000e020007049440c0c80148020030080b0140300d00003401303000340600343c0c6481d070a8100e00c240342850b600780701142d0044011039050990900c05030381e2050990ba0040310060103101c0e10312000300004e0040240d621901d4980b00c580221941000341980031020480300c180c00d0341c181c1030000f01040000c6541b10b500401007506801e00c0f40100c0c005d83d00c086c200d5800a03003610b00d0b00094100140c0c150300540d00884032400403d10b810242c0c205107900410255102ea0184 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 490171663 1250 490170413 490170427
    0xc1e0308061905041e060e0403051602040912080702100501050a180f05040c03061518051b0f04031a0702030f0c0a0c030c05040b0f0a141207060314010b 67
    0x301045000352006101d0701c502e030020300c0910240c02c410b8009040080c020030100e0340c2101d15400c108400c1c0c11340d01e400307440c0450014580d013684030030074421640b59482d945000c00d4043d0000d90342040c18000e80c3c002d81d4620090001411a0f00c100e82c8110b525200c1c0406441d203040024a824500241d800601f030420004118945904030034405a4000880701d104161044142d0001811103040c9a5811802c2000788003d103c0910190400e9900a940501541c00321600048204c18688505080d480b6a038287d40e40069159000d0742d000300c03980c03402c54100c1d17042c44500c5030644c0201200c510b004000103810020030003002d040540c0b0740400000c01c8541e20741204007a440e0701800c4403050300386000046552860780140701645034a035001c00c000e04c846840303040402c0c0d1a40d4902038035004601d400440301291400104682c0c5051000340700ca94580d040c01100d150030f2a40215054203c0c884900c43c00c9465002e01c510340143c45a69000103d01140038000d803401d500680c402c20703007910200054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 490172913 1250 490171663 490171667
    0x615091006021908070501022a01090c03020103092301050a0605030604050a0f0c0e010902070212060f0c0d0603080706020304060624050f070f110a092a03090b04030c1e03 75
    0x3c024076261100c5071601001c940c1080d91031803184807801002540300040044440301520005104440340c4192149076401c0c843c8000e08075512420042d2087d0a004800c1005622075049910040e1040501c40404040c00a00749805005c03d001c80f484c0c0c0c3d44840030401900c2127845648001c1004900400d00c0d800c09807205070b1680d020b0980074000400c124045010311503046000340081c003940c40620141d60b916401d41000750400c4404034410b40e890700e840c0a152000094490103455004103a2005d9201c40b13140c400f49030301c000070b800c0100303845a2001000c2092030b4003400c0d420f4012000540c0d280744c00c1c50084115030385504000d00100c10200070100800d10a415011440d1490a0055481c25040c2d9084901d025941c4013704804000c3c19801c108510290300844160781500e0400d40a522142a5025034070744111600301000d1514854a42145203003001c2c020001d94140010b40701c601e61104d444102c0d0482c1c01f500030542c0c055507003040003503200908840941c070819030500c01400f5500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 490174163 1250 490172913 490172923
    0x3042d0803041101020102090a06020f0106060305090303060f01030f1805150f0a0905011103010b070c05030c03280b04140705010305070c0318090c17010902040b04030b04060608061509100602 84
    0x3e03000446070300e404040780e4000d42c112000814001c00038642250340d400c00950f24030300c4144000d142c1d400d15170001040c0340240540307805190080061810351303540c10244036405000003102410161a00c0d80d1880c5001c40b4031541507050b0700c10b2910000e03c0c5803402c2c00c80c5000b000140c1d1465200d00d80c2c007000140f484801903ea040180c2140200724a140c41c01c001e0b001d440c0c1078012152440e80040006a0032001c2001005007a110b00c0700c00b0802c1e544c640801d51a8042601440d0f09500044210a09210032078060011070b03120300c845070030014a54807141c0000f9804c840450303040c0e2512174460894201041082d00414017443c0903c0f0519004400910161139080010180040c50102c0d40210085040302400390041074010070900c001120020700c0b8000f54030342d810492030301b14004202e6880038021503003941c0c5c3c200c0100d4a003d1039990389614000c4010b00660340d407540c8a001045141060000038050040d02c0403400f0032150f22400c2251308500604a102d400c101031404004840d00411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 490175413 1250 490174163 490174171
    0x212a0503060f180c0301020a0c05010b040e0c190b07080901021c0c080304052a01030c0c05070b2a01050106092301080a09021804030806010206071202130b03042d0803 73
    0x1000d0314a40c1c200c0f407981440c0c41d030040c1d00780b0340c554004160b1005040c2e114035901c06c00c2d40074200038030200124200380422107001c50005c0d0820380011a10b0001400d1140c0800e4410111010245640307540b003a011009070000130017190b5480001407046019a81045a10b07007014420782c000c840000303804400392420302c4919009003000400300c0080d0a104040c008101c0c00959032003041c01c104010a000d00c00280a8541c65010031714122030141001d120312450b0620561080040c50031604000100b41681c0118454801c00750011420300600c44849081c060b0004900c0000705440d4106900545450a180c010703009962070500c80110340c44020800f1a08080207003400d5405447e9003000a0150088140282d00400720011615a01d060000c1c8a44142d000381d4400c809501c50301c004a072150810780d11500001e80d81d2560201c031180310f0b40140014800d502d2481c41866030342d05050340940003107a0a8910034250044907503480c5450600d009800200804540f05102c2603803401c0c01c500003d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 490176663 1250 490175413 490175431
    0x7030e031602131b030509010606050903120d111902010b0d02010f030e0304090212060405070305040c0e130b0711010f0e0d05030c0403020603010f080f010b0109212a0503060f 77
    0x403500384040320700e03444044c4c8041941042c2c0f00c00390300804041c004d40302c00d036810440e85d80390036000034074180310784196041d000000b0007800c0500c0082c00030700101d401002d451800196120400104c50013010000e10303007886036100f152400d55504c1d201900b1070f800300c1c0400380101104090000145ea02402504081401d41070020302810303070300d040919500641d040082c0031440011685690465500c8280c4141401c580a200b20f99400c50304034140d86003503400400001d0b0005050141c90809001c186e84490308202c2c48501e1220342d20340a502d41e80c142d0710807000c288050010240d0032000e000d200c6880d10210014041d4000078281141d9501150303044800b044000f2002c91681084641240e00a50300201136503200d5071500814000c1300340600c10030340103100b580946200401c040c0184441010140c49104009181c139404110517603800540318001031200d141b0030005000d5100b0b0155060345a24040e4012102011504141c049500443e2003030744250204402c00c1d507041145640b200d030071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 490177913 1250 490176663 490176679
    0x1150c060c030605121608010b010503060d03020c04020310031115042105010f0b100305130b06010e1e10020f030a11030f0703020d170609041205071a07030e031602 72
    0x20718002c0300146440c2e00032550150040e1090201e10714009480b040840700c02c151300f6040c503030745c0744504e08a8854000c91808107500b41f00251182c41c000003840e0742c0d1402030061300d9203d02002d000408070b82c001c40b010f05034009000401e10074405106081e000040c0c040d01c209418214001c4d0aa03001e008520925000f40301e02c01c10b0000c04492002034203001c507840703002840b003030100d0350007030b006402c01400c0c00b4011f001c0c88402e02102031184c091180a109584550980251a500c0340008008000d00f058107000443e0440003440d00d548504180144002c40035a144c1c9001c0000c1000b24005941003008651002040c0d50208001100b203c040302007034107110b04e83c02906c5100a04500400310b440001c1c103400700f2301805154000c9200314010000d5682d904500381e420103021400e0070241c2d50355400030f10351400100011a03a00c03c0030300b681100d0403c641802d4096031444401d46c0c1c640c600300c404001c034400740000a070b018080c94605880400107142400f01143d0342d0700b6200c89080d8081c2c814094 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 490179163 1250 490177913 490177931
    0x30102120c0307140f0406080601080c0406180b1206030d0e01051207021905060105090c0c0a02100e0607030507050111160f08040f0603091401060b0d1e06120b01150c06 74
    0x3000e0044c2d03066078806155445a03062000303121150042e110b4500424048800100c044d81b140c58032900c00c201c8400c4260400e0308050045030a4445400580c10074100c1050224402010354080e001030070000d810941c86142c0b0030281802d080c10381407030a06000c0300c03e000c0040341c1e0300241030714031202c03075440702402d942d40b9030038124a040d00030fa400d241450080002c03841404804078910341070711030540e2045050785401c4039074412881020f1440d6203540081000600503c0c01441443c0704000d580f508030f1100494000140d010f500c8007070100c0200b00c0000d10712040100070f024a0b40e501c1020881641094100840c8440c80050040c00500003a0002c401200700031000c800c1ea80903048982600e40c110340c440070082c00815400c0c10903260400b140c504010000d10500940013500c0f002c2442c907041103c400c2c4004080c1c00c01050050406946170140705600c0758031301c00c0800410040000400b110911700b84501030300410780008420ae0490840d01d541c1315004440c20000940c07040d000205550 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 490180413 1250 490179163 490179167
    0x20301060911030702010b010e0d14011e0b09060603090a0803040302010212100806091c03020903030903100b09100303090501050a02150c19090806010605070f0c0b18030102120c0307 80
    0x2203542000030102d00d030001d04404800904040e6200e0744154000300841c000b8100151544003a9105031a0310200a60712840010403004000c4006200d01d00049034240800b407284d960042c0c603541800d00325031760301d00c07800640c6840c0a074030703400ca40161601451800c14081c0c2686428060a0241040e0340010100d81014400d6048451065030000c0c1041c0030b05058a02043c4481a8071a0038040e00c110404204000e5011420000302c0b400e0000d0384a29032040c10302074019410548000d079050000340020382240e20b0500c80d004800ca080440007401d6042d2404200c900700018001031a83c01c5014002d10029411203c0102628400d0030000d849000481b0101e00e081c0001030000700d0b61080d0814011301c141d104c00a014001d03d02d00309140e0100400000303d800800d648a55502580800c0040180311300801c000c02400d0b008260b1146c00e180c15880300303100b107041a4031500f480b150000c0c1c552075490040ca03640d405000e0440081d0f1411580c0e100c0c02c0c98110018000d0001e070036000003c102000c3c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 490181663 1250 490180413 490180421
    0x50402031003210f030b01080a1503061a0114040e1f082b0e0904110307170f0706050403050a03141303060902100201060b04060f030228120519020304020301 69
    0x941d006555240d540360901c000041c40c41d141c403c810200d1108511000043c0c0640034000341c105040e5200002503841125540103400903070001c24040070f1855010002c640c03a030241000004100161824850300480014081e821841a45a100c00b060100b440000440046250001004100140428a10f030010392040318280d000b0f004600c20300492110000c19100980100045d80c00524100b01600d0004d85e8000140d82ca1039074400411700c0010700045609164a610729005012142c1d120707207a1043c204a0b6414070702e60280c41c2d0026200d1b60b04000100002d002030025881c0c0b0600b4a480c5603210780e0b550350319075001000d100780c01a0050240018105503400062150380b80a010b40e52818944010704441e02c2c1640038185951410740c03054014011202140c8000c5001450f26290210455802d070340081041c003059000c010340900305181c40040710b000304103090501401c640d00c600161106400c4501140d0303044c1050200104000e40015031103071000c10420144e40d9a4580c80024018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 490182913 1250 490181663 490181669
    0x6021e0403030f0305071d0418050d080108071e090905010f0f020d0b0f0109031b080706260f060f1302030c0717070809061b060f160e0303040504020310 67
    0x1000114001040c5540703e6441200d2052a4400f04120703141c209046490541c100030b08021201380c60300b1550303281060340c05520540030b02d01c0c02c40440e03200c07a0340b01400c1140d0a4130150000320444014400c40205010f098028104079520000103404880c080d58055502d116403011503942d10060028824203400c13503040d00705900003c00544140540000007504120002c1240e00d241440f40d10340340c10408690700c20484140c54002080345186d90f1410981010202c81d940e800d02d0744800160543c00300100d07005006292102604281a1101900e4031185c1140c0d6003180030a00e41032140b41481d0b14025034110400f52001d145000801c00400c070440b00d591403d1080360301c0041088401030b00704010b000860b1007031030390300324802881801c0c0105014240e00540f02010070084100f0601d03041c001000980620754168106400b20505142032010803102c2d61040e2a15000b00258002c800614862888560401103107402059020a642e40598001c0714041c582c0040411041005c1500741001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 490184163 1250 490182913 490182967
    0x6090607120c18030b07110312041127040b0705070218090f031201080c011701090b04110c1501080d050306091503100c140f180a15020105040b0708060901030602 71
    0x525961320b046131300c00d0b0040303031100300107604847c41e0741b03407080b02200b102c580040c0c2030006205600c0d03507201e000b4408400e0385000d80c0f01140200c2091415003079111038850403840100410b0614042c10003501c1c0940050a403020441e04024003401a50381e078403030350703400103818542c00c1d0140da42ca12214544002d00f41d04480521011810619080640c0d003d10f05843c0900d05036280c070b0a41d500155000300fa1640119a0400c1140040c04401c800b540511000e04e4020008211980c8441c03034402c40f0341c408101d46c3c580c2e820840301d00d161440c0c1c6c028203d00505030100240100340e0142002403042c00702400b080d1003405044049099048d00400d50081000f008080d12018981c5061600c000e044140d00c6601154030340400342d1600d2103000035103021a4141c11424542520110800d250400d000b444661000c248030000c41e9011480004030342171210740c0c00015050615061100382190000d010340d0030004a85d04110803502c0b040000c030b04407940044050780f0741c609103098822004004840c684 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 490185413 1250 490184163 490184207
    0x120a0b040c0909151523090f0108030a0e0d02030f03070303060f0501050703120915140603010605010215040c03021507060b011419050702090a060806090607120c 71
    0x144414821400c0c0694032540d00514282c0e03694480c1c2c410303a048030303002400140c1007089a20100c81c5981003042e08a2106400202c02511481540f03c800d88142008005010002040c0014244400c1d4690440052450501e056262600b01c541e82d2254008001c1086101c00c1c0c40082c94441200e40b0907003d0340101582c0c1c0c41c00d00d22001958a0700888002c2c0e00003824458000b46120b10300c1030042c151401030396064640046078034280c401c100c01c0428001c0301c40d99010020040f5101c102440c0c1c180000e010302041044d09070380800100c1001808a034441c8c1d00d848020045680c001802c400d03864803644402c5115501c03802c14200c500255800a50031500d4415000300200e1500020406548501000c0140c8541103004450004407084d100020400c200722814101403000210003902c03a6514000c1d01d0310b140c581c0800c4d0741080640d811244561034100078403005405102603039006800b640142010b29191100401565234082c06001656941da4500b803000c0c0700b44114140070b024454441 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 490186663 1250 490185413 490185433
    0x5040515030f16080c070203160f090608070b1b1507020a151808130504060906030b010b0f040b030a0b061306081605042105100c0e0f1c0212 62
    0x1031003039000300d640d044a448018002402001c0004080781034820130781d148030869481c0640480a40d0100c02c003a0ba051003400750503440d401c00c440d00d03200644401100c2070955071400e5a11010b480c140e4100c1c1400e0740000c8402e2202100b0034090341c601d0f820305030188401c80240200c0c00d0034401060000207504804008001e62030380c0001c6c507280503901c40c00c03400910001c000b850504032945242c154654842e0000f03800085025480a444100e0340c50620000300303036603000018101c600952203280d240340ca0710b104100b40207014946a0043c021010007901d040340260321003c0038440c03400780e4000c40d040400032960241007980305418580c0050311069480302c09c921860180c40c0d02d88100ca0010300c0c13580c0024804030300390010200c0741a90b515050304050800d113404e000c3c0180c8603e004610500d2a0340f074400f1880410040003d0b0f5140900040c40700040bc0c070091545580b488924082c2001e030750050207640b104001c00035026035400c804040c460203480060345048224510f01c010b0703c625100d04e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 490187913 1250 490186663 490186699
    0x2070809060703170709180606020a03030c1b05070815061315210605150f010c05010b03060103140d1b1101030902120c1c02060406080702160b03010e071d10050405 72
    0x800594082800d10a941d20300000b880d42501c8d520301034040140c000d58050b0000038040e40008d220154581001d00701201d0b0b589110051118141c0151f9490740005410072030700700180061503a81e006600d600843c0d21302071001c40c5200c00441d02000030582d1340c101603110741503c441088040c2003180300810f140100d400f500c400d8010f40039000e0f5803007458003006ca800b0203a80d030b545100c02280a0582c0c450424020015101007034004000e44040d5200d0859041507075080c080503010314800c000d01142d102924410b0b500c3c040c04001010241324401112417001e0008460011030280d21410000e6420001340c0103c026040c1807400039009905804504c24035980418900016001922411308060f144034bc0301d5090804c486010390001c408000034802c1c948140740c40380d03101805004a401d00340301e01c82c030407090181c0e0307a00400306103030084018000c1841155901d070b00407107640784c10b1b881c008804d8802c81641e03d54040e05c4d803003640b48283c0038a8080c0101c044d1002010002c0030710441c2d6900000b8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 490189163 1250 490187913 490187927
    0xd1511070212070623091216090902090604051905090d030f1e02070515040804030b09032b0f0615030507090e04020d0201050f0a0e1003020708090607031707 69
    0x4120b200326a035440014a5100005843c002c43d031103907460300d45100f62140c0d90900501c41444081c660b00c1d08025034000c0f0b07102d11041031b108406010081c0300265150201c000c0804d0300e034110803c1c0c1070a2049080150382d501040b280c0140c800c4800040c5929000e4028000301905003a1a0a082c01c0c541088014000841e0002000710151400d007d081d103813040200407103c4600c8a81c03000d0b0500301e020b007401d840ca40e0282012900c00e02c103c2d103400c900220302515150007150122250280000c062080240190807190014500300007141050094841c00740d000e2008814401141b184c0d80c89008000940d0b002851700d481c400e030041186a46424010400c0740550081f400820b043c140400c50092060429000715aa01d0311a4002500c66a080241342c0001c544c0076410081c5c248640c840030003221008141c1c1d00ca850311211040a201402e100f01ca0105a4000c02418814042000452291003ca4034180001c4851541e1104a441c1c01c2d607020100d0381c60343c40041141010080c050b600101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 490190413 1250 490189163 490189177
    0x60102070b04080a081308060c09030111040e040620041e06050a050a14040f0b130618031e06020408060a050109060506121003023001020301060e0d1511 67
    0x800d60300019254858814140300c0e510480046030f10020218000c03801039405449108280c05100801542d181c941e00d107005025991104420400a4401c3c40351900b4403802803101083c2e54103609141c40c0414000700803000410203005262a036105113018420a41051038052046940c00c0e19107450748820192540541900100204594404140c07103005005480000d2540d5484614002103070508482c041c0c620f018066201009110104211540c45406d5000c0d00d55010041d403200c845800e100854000c5921030800d0060100418044003a01c614540030380360454840030300903221002031001140000c202800140c804a40032680b07c2e40410000d000c0c442c90310051006980740d1010b04c081780d03418410140d0010041000100050888000d603034803520010036004130541c3c0c1e4005c100305a2a200004030111008090002a00c00c0e101e40c3e50380c00d481c080021411503061420142540001c040968410001c841c030301000c10407a020a0007501208030410704c00350616844007103607600303c8a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 490191663 1250 490190413 490190417
    0x30f0b09151e1f050123030c0703020c0a2103050906280806030703200d060516050306060f07140a050a1e051b0102030d020c070905060a03121206050d0b0601 69
    0x422030450701c0f40324041030a0207160320020716078a803d00644846c01d43c501c0300c000714040410000343c00100c0d500030710b00ca2510303036182c26030356152490000d00700001d0462142c031402821400b40148040491105052021500102100081c5007810740c0c06000714054113070b2141c40002d00d0781d180c02e00c1d00701040520800110140e84003802c1c0d041643c000f4802ca503802c1e0143d000c0c034003c03c0030840500c2d07070150441c1c0c2c480246560f620f128010841c4481000c0007542c1031078a03003052103206001c50103600060304031031910768118101a800200e1910a00000200000001c1000c00901c9040019143d2280c03140040710750790389145c6081030320344000c104166010300b000c1070610341c4001c0c80748070344035001d610902400000082406000ca100f484c03450150452009205042c03103581984002d03d600c2d409100101600c074030b04815001030b5040240910300951083c00c081000442c42c40c40c0413035404140c102800050b0310035882070024000b991241d80e0000101d0301e04d6080c0300d480580d00303003d0082a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 490192913 1250 490191663 490191721
    0x10b03100e09061f083c06040b0a110721030c02070302062a0106050109050904120305040309050a0803031f03200d02131a0306011202060c0f071e0f030f0b0915 70
    0x5011030881c8654a0b030b810047d000034000400144083d05940e81c4105440310000f1401d03402c2d0300042c0daa40140078200ca040c50756040755241070342011002c03c641c20701c0346030a0202c050010b0b4005e403101d6040c80020700071900414504080010f60365400000000c0c03c4070070541544c01040345019102612a2038085822004003040c20305207060010b00c29030300000001c01102642404800802004005804001041d071010980d0341e03c04100d24010070200e00115181e04101840c1b16204803ea6008650354200b1001000060ba5950026541c1c4c03000e5680a01101841c00c0420b065640c000c0000b0350101c05040b498030029220340c400d2220380046413003098140321400505a0302d080a0003003c28886180140b81c00601d86003009158010a040c02c2d143c079201417003202c41c5440d0701034209210108403511054128054540103100414191002c0c02c2d0051030f64596040344044c0c240080c080c000ca041c00180e007907108005100034626042001c80c03280c90b01c0082c08090500c800034202c512480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 490194163 1250 490192913 490192993
    0xf0c03040e1501080c090120070f050603090a1b03060c0c0312060506030606090415030f020907020703080913020705060a05070e09012d0e010b03100e09061f08 70
    0x1611909a407401c182c40e00011911851203017000c0c2e801110100341001098542c0070314600c401100c464a074002c010040000c2401c10310400001126500300702e00501c0b042c002c1003240c06000aa1098961300b0040c0c5400400719040024415131054101801e40c034100400041320aa001040b2042c4c14069034480c9480c0048105a9041d92020320540b5030180301030000c01c4492804038020300b420100104002504292103880920001d5035510a0f24442240c055010550800c9450aa03201c461880640591825940c1c0c42c1c0c8103005001a0398000c9104440000d0308010b140d0440d280640c120341126070038649001000003600086a050300000c0d440513080c4d2541c1028a5414161080c515601103a40c010441c0d54080710821a40115444d42d541c0c400600b900190204501070081c00a10341d90b00d20381200142c050701c0075688101d2209152108004083e1800b00c1d42d6500050f101001d104001040a445180a020364201c90b01e80d008003500300c0b10f030510100121407071089030703540203000d010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 490195413 1250 490194163 490194181
    0x100e0d2306070807080619170c12011506020609060a1d06090709111201090203060a0b0406020705041a091801020c01061410020d1209051005010b0306121603080705030f0c03040e 78
    0x1f43c0010030b107a00b55440c00c02800048c2e001ea130452040c00180c0111425548030900103082407010030707204807050355204540040e8881d180541c6018040c0d60000b4942400c001302520350b150001000859429510070300f505420a01402c03001000391910120364160620844070381d2211130700c0c400c0703d00061030515001e01c00f004040a49424158010590040760705c0c2c42e556401950004085691010b48041e020074245003440240014201c01c1c0c0c001e081c12400c00c8107201c03c49007050a076101c03220044485040c21f07030312900c170b15038030101c1c0152014003031006038071450184c007172681d0b0a0059400c0c86800720b0450b03000c200040e503d400840d4041d2604446510030790301c2c2c1403112114000102203902e08844400345800c0701111500c500100d81002152030441c00c121002030b00001c449000000a001007450106164841c100075840604191054041031a10040d00c51100802c11030020901c0020b000301401610207021996050365a1443d2074000151640d00600440030141c0c81c00b0080385c0701d51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 490196663 1250 490195413 490195429
    0x14040812070918050a020412032c0a0506090301151203021c0e060a090315050415151a0c0a0f0b0703020f1c090f0b06100e0d23060708070806 62
    0x181481500001443d459030715000038000060010740115020440000c01c20145180d00000310300940d1500031812820342044e1003205a000214402190305942242540c0c0d0306d41050111001255950b541c1c810100100380503040301038407141c02c2c466449002410703030551103c1c0c5542034840e5003541c04140405021000c000c056000500000b810710113582000d0400b50000d08105003542031040100b41e0702d0b0f5600203007404464000c070000d170b200c5d400d0004018001c0301448015080c60010b1041114070252221a0245841403c1c00000c00c42d4030394225658400c1102c124680d0a0152442404203080c80c000c5010600390840d07412005000042e0b20038428800d071108010761004291404000403d40c540001e203940007d100240c2d10098680010a070304141d0fa4960710030007008a942c98000c2c00c1002c0b207030400860205202180e600415142d0341d10500c8003541e9404201060009080f10300c801c3e4584204803028024814542806a09e5820201c41c3d80300e422241d0740c80c00c299442805201d080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 490197913 1250 490196663 490196669
    0xf0e0304090b060c1b010c0605070918020703080408090d0204150611070e011202060d051602010c0207030c0b070501020405130b130c02061b1611030d0e0117040501140408120709 78
    0x5900040300b034080c0d00d189080d170342c0302c442414507005000d0744050b180c082c11208203032844008a6040d075030401540c080d50910908000e1090300440c08d0180310784024004490007080140f5004001032007200d145d8400c9006101c0300d8002e041046412203110304130070700e141640a69804141048003048828000040310010741d0004500b0907050b9182940f640415090800100e070b1210080c0011403107000309114461050210030589003400c1b42449000e801c41c0d003003541c911b0454215684c10f00c0231403800e01d02c0108540c58042d5090743c030101405c0450080c000c85d00050703807140c0100c01401d81e0604070b42022410345412102c100203100408140d1040300c0940d40668050b8125a0020f1214040a040b0540703c840303100328280b61443c141c0c068621101c030b11004454041c20022041e54904040018010b4200395041000b11050300900180c01c1040010784124150b00c2180061f08002003034102100003010b030282030744603080501e4040400d80107401002550503981000030b01c101d106030148021 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 490199163 1250 490197913 490197937
    0x1212070c1a1801020c060a020d0e1005040612091208150301050417070c090c05040801050907060225080304060305060f010c21111006060801080624040f0e0304090b06 73
    0x40c04003a0021007440c2d030190700701c850550090142641540d22564002d1542034400d83c054043d2202585010f003c000b08280118000d82d150058a112a504801240c050364054105180b00d1950f200d20300001c0c206038640140b90650342891100c1c1c2c1d94214240601400ad0a9606200400c42009048c222141124046c0492000075503071005603060030b00601c185409240318032005929004014180d4802040c804000381002504105d1780c4000e10820b074015243c4c0d009010180d181210095448124a54050742c0924200c247c002c1324180160b440c00a03d440c50641e0707151550380b1405401404111600350182e8000402c4131131961094007c03204140d4044101251003016414880d01e0072100e046000900c209500500c0122404200140038100e80401c00f09030141421780041404a045c0e100001176130042d4140000005105840025940390125003014043d5000010307018041c0070142c2008203151440006ca0003001000400a98422140520007220324200340030140c8292420340381 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 490200413 1250 490199163 490199167
    0xd0c02091b09100e040c360f060206011508040c06081302040e061509090a0602030703060e0a0c020d020a08040e09012406080609040201050304111212070c1a 69
    0x42612241c950601e4541511030615090054041c0407803103007401c24039414046013025181840603d054003030103032802d00c1841c200009102030041496107600424807000d540503100380d400315005a0389046802006440490310b00707a41d50f8038019494180030b00600300d6620103c40b020030018043c000e02802240c0c401c80103c5528071380b00342140d08035006000ca4a005000c0388806c40960f03114003c4050a0302060003518450500e1000c41484048442070b00c1c2c0501c801d2410400610804514003504580000000d03a980d44c0700ba0045006225540042480707540d0b01080c4883c603d51644040048070658003190742c180540c5c54144e82e0b690003064001c0224404200a1005169100020703402041a000102c0c4441034400f402130701c00500c011803910b00c50241d2042214541c05110b690704580140e60121290a068000030581e02c4010001b805000d20b604017220b55403101e120000e24603800d50240c07402038108001000d05070303010000c1030b1a41d000000307001c110b0221660049611003000c0d803150f8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 490201663 1250 490200413 490200421
    0xd0305090c040f020c030c1506031f090302011b020a020108090115212f01030606050901110f07150e03060601170a0f0203010b03010e07020a0b061c080a0207080d0c0209 74
    0x8030180c00503c4024055a03001d0040700a540010000b414050303507031001405030220300e25807001c14801d0013041c640c401c0d4420900f000c000400c0d00303a90229442100030125031300c03003075003005c1e070143c4400c0100240d40c1e17010404040c0d0b000c0e804683d03010361034801d995003180da858001c005803e03200044a010102844500304000310280d100140c02076584100c54140e42c0071903500e034039400f10800c0703940040700044030100e0307940d41094640422007008242001c20440381000c1c0000c2150007102d600074140404051041d82d0b40d0000c10425905034034040840384025220740d13071900b241c2424006440814180c0310200c6043c81d004c104039108982c10b9643c104030720390000d42c10060110162a4043c4580d45581c01482036180d40010760207440708000c050360b01c1d40b40070081103909900070302c8042190482c424100001d50001c1680e900b03c0800c0b242640b0542c0708664040c10004e01030402403000400180e015181d035004140d0b201210604805d45a20b4010a802070f01c042035170352002507100c0e030650001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 490202913 1250 490201663 490201669
    0x302150424061e171209060d201305040519051e1e01060c0b0a110d0504060b033f0f0a170a110409050703111b0d0305090c 54
    0x2454103580c0e00d11020501ca80d4814255003c1e10411001e80902079100341c091151000f661440326008003000024040c1c096038104490007405421221031190710001031043c1c0c0d80c00c00c2d80180040b0b207841c41e102070300049004400300c202c0e8019034102440c011155000a0940b9041c822180318000008000300707041d6406024a0041000401741006d00c1074484440480d5844501000d10a040440181220794001c40c007503280c8450503840b003010444e5000c40180095481c4881a400002003c004030308804000507aa000d8020352840040151902042000b4025240c1202d03000c0c4100f076054072001540100040e840c840e018401d1400f08074107200b610410890411500280041010081d091045140c00b8150540c02803042400007182c000c2103055907100f0201d90364220003520020004070303408030440002c0340514860240841d64450000701c0560094201c0841c5d002540f0b03403655a001840300380c1402c401840c0200d80288a80014410300900038801c060080f44890700030a00f04000e0420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 490204163 1250 490202913 490202963
    0x20604060f141303180b430b0109020901020d05030601140d0c03110a14070501140405030a03060519120213020f04080c040c0503010b1e1603021504 65
    0x40d52000e41d0b0b011601454040007180743c0c01804000042207405941d4203005050104141c04255054a100010050b840142c41150304190820300d48180e519a8072001d481804000b6112900100341c4071820f08880420301054107000d4882e61400c0345990701c0d0300040c0200e019480806015034018456400d885000710080d56004a05140c90240305202422040040d0840c80840d0304441e11407005091303090b00350181402c4240f402c201e8a060510903680101850501d002107001464001802c005003c800e400440003641740f43d00c180000d040502e0410359982c0046000c1c030000e4034050b40400d0914124004070801c02810707551f0003540e824200070703490421504404a074482e440c4e95031020b40c40f15074006000e8840030b190b1002e4403145015111800c04103080c1c3c90511940c949107840302040e4009051b24150341080103896212050394158114203035203c41d416031a00c1000c101d0404071541034003482c043c18829400d460300c549880350700142203a82640c00401028142c0c1c0030048141850b11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 490205413 1250 490204163 490204181
    0xf1208040608130c090b100309020f04020f0c01050408070506160e0909010914010204050f030309090708280902010f05190503070219050a11060408060c070215030702010c1b0302060406 81
    0xc5150f510555440d11400c54207075006484442e1288114041c900e04103105102d8015582020301c144055540080e54181c05001014456035001c92011040f0201c4415644004100c0008201c141000d007008200c0c0c0c3c2103030400310b40c14415400003544045103082c0d0710360072200e0f540b41ca28506000c0c1c000c002d42c00000a0111006650740e002d8800800c45e1040344040e44e20030000016692420304081c46141c14401c1d032164004d80c002c111401c00c0d0f0700c4201a2030b90281781480d1003441e1352180210303c810114130580380c41b0441521041680d911a641e4030100c1800d00c00d880d6070007100243c90b0241c696004e01540104908180c031880e030744950192005590101d482c0c81540d54034500701c1154018a1803004040d0b41c0c0e41d000074811000c2140707043d64440c050380100c84090404d8a00350925580d418002c1031203000f8200441c11004648075a01002446055001d00640324a8425070003402462580d1030600040c8500020280081400355a802d01c69016070240c841552141c4807803001d080d40340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 490206663 1250 490205413 490205431
    0x1c0512090a0507150e240a0e0319110d0c03020306010e15010e030a11010504090f0501170a02060403060b0a0905041401050c090f0105070807050a080703110d09170a0506100f1208040608 81
    0xe80108a040e01c0f070401800800d20540b2503400524418082c9440c10f070501c0c20030070000d007401c0c200340041080403a04001000302200c14820000b1385103002071001543d40e0009405103d191c0020075001c040100c098825910240c1350840e0144060045a070061010484ca40541009100d407010552803003440000600c10b0418510f0f155580c1900807c480980700d03001d41e42580c0d0b20044c442d201c4002c3c5c41d0740c0100c01c010010034001c1d07015000225244110311004018603914150380b00e00740c8413843d04400600e0f401008100c5490203050605043c1c4948414000359403070100000e0941070b1000555250303c001920100941800800542d0a54400c40d42a2018003050106c2000118100034170552244955441c58a8812601e006840356407600c07032612072a00302c07107020381d14180c0c0102810201c4680d902e410742c441040c00301d030b2030800344080005071007401050100f0055500080e4403100b182c1756003440403661692030985451000341d004000740031580c02c000801c0910f105030401c0e90004048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 490207913 1250 490206663 490206709
    0x303121514121204290a051c1119080711071703090409210e0904060c170103050105100806090c010c020307080d02010c031802031c0512090a0507150e 66
    0x43c042c80c09141d00194440e4441015107020143d541e04c011082e15000b178058155036044c4040e401015001d802a804006003642080840782030700c603030540040c04403d400c65150b1f603844030801c0d00300e142d480c9010b0614010a42c040081100544104841104070280c400035248441c10594550054050850b604045202c14004140030360385505c107803809148038014004440041e200e01c1c2d0303108403d62105e00140314030310314000070a88489005980c400e500c00340004011412041c15144104451111180c0441810010080100550042c1c2c041c1e6102440034607207039602d48481e40d480304c0499096003a40c00c090700c134002c0d0354080d1095800c7c0b1403005098402c0340362038041103850001c000345281c005070b448201c10303c1015014420101c62450245500c100e42c00d4079000300307691b80429212781c04104190100b128003988a030f4241c400710121900c0081d1103007000c4119581c0c9241c1c0c68420b503075a014150000030308509180b80d0403007040041e02d903520000c541e0800c101046c00030703400c481c1c00d600340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 490209163 1250 490207913 490207933
    0xe0a030503030109090506070804120e0d080316030b1c12050c030a09062a0f0611040326120f07140d02030907080f030d051906030312151412 62
    0x3040c006076000e0111500005090881418198600302c0f0142158051010510500c00800c0d04528030f00d480d02e0f00c60030b00d0b0200c103801a002c43c01d1ba29008002624505001c402c1c04035010000300300540040301560f060010100c070208010212403000e10490080164480440000e0303c00d907074091942d50203040c0389007001d48040c8002d042d07900100c10140091034251086c0710391500081242c458032410440940303c010303460f10030a640c0c0c08200300035080c0c0b00124144410080741e5041280407070581c0724400d448640e6890207000900340040000510014528225081c194803002e0315008101e031413021030b10307480e100f030004c00d2041e0181800003040081580002d1444042c0d0040846410454005a6034038040c140030f401c040a6420069107500103404500d403054000007910030003000c0d100f001540340c9a0400f203081c0c00300d01c03108034041282024400014180c01200325503004c01000e0080c4030b4442d60b162020350f040d640c0c2c080c00c000001d800c10528005d0900c0d008140368208844202d541c0c44c65 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 490210413 1250 490209163 490209173
    0x90216150f05190e3f0a020a0507050607050a150216210809030319150b0a090e040c06030c02010917040503010606030e0706030b032812020613030e0a03 67
    0x102c200c0f0020030003c00640c20107501403c6209104145180802403c4a80782d0304040104480741c0a41c00305030700d072080e10602c4404602e010713050301880607510401e542c2d03d03151402940700c561850b400d61705800b420b4800150f60030f1450455012540c884083e00c0005103d5071203441c24441d01050102c1580c0c02e011280071040c024080411481c01000145d40300007903ca240603401c00384460354010007002c94207200410b080001a41c1e00700700b424207124102105426a00010101c020405071021000c00c0009020b0320240001c025583d04e0f0782da900c9a2a844c0c2400c4400858140e400800484030300300e0401c440707880b81e400001c82c3c200b02d10000c2144103040c0c5400c03011007038560024581c401c00090030019854244a0003000305928141806040d48440c0040c0e2900514402c200c103040d2a5400c041c00c40e903051102c1880300b074400e20041d0400400011440c3d03416003c10007181c0304803450818041d0f050001590750720030f030020500c000000f9a607550441e890502107141a4018400d0380020000403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 490211663 1250 490210413 490210421
    0xc090c021c350f06040b0a060e03120409020310060f0f050a2601080d02010b030c0f0a080d05070c0b04030506040303380a0608010806010320060a050d0501090216150f 73
    0x4800401d0740245418a410300c02c060250103480c11740714500e030003142c003000d80b9440e04250884e91181400e40b1401c0c0400046820600440075010045500040204455020b980030f140101c02912000440540320a000da4440c03a580030304c1800b2030600c101008855101d500284981c15043c0b500410318100c0045144015401401d80c00280b8108001482081780401400e040d800c001e1000b80049030500c40405d48440c0b060395111700811510100010b1030726980d0003440141a07007000c80f541c400444900a001d5000241c00b1281d1011290000401038909002d40d03060320342000180c1040d4807603690580c0141a07801e02025412240e501503103000c240740c6030482d0002c00b03020080702d6a8008404010810403550025001c3c40140c2c40144214800050b0f801c3c10340e5840701040c50081d10802a00c03002c00b0394080faa80c0d00c07100c00101c1071540c6034808042d0202401100c0c0c28000c1c4d0340c0710160b49069004400303809140216003049040494040c1c021090180190100001d104540080c420159 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 490212913 1250 490211663 490211747
    0xa1104120302030d2a030e031201060f09061e03020705070f060e010801050409050a03050304050c0406181b080a020f0f0f0913021204031116030c090c021c 68
    0x1580001c134802d03501300700030300400b03100100340404000801101d1886980764841201000e08040d6110380d42040c915003082258800e58103003603514050b40e9109002070042000b600401d000130094040081d00c103003d40c1c2c80d0f8801c142001c8940307010040600048000b504100400d9a0343e1280200000b400300c44c5c4044400a0032443e43c03200c800040c2c11001401100040c4c0c80640a20b16109403040400d4011590100c05039061401c05d5036a00c803820103600d841d803003843d110341c440d240c180001034001640c806060795043c10002400750300b0301c1c201400700442c800700040b004542c41c0c500060380c201c0c260703005080303004a41f10480d05040702002120400d400000e83c00405000002e9240c2c654540f01c449e0070303605001c82e5000d42ca000340014807070341c0a0078003030b0008080c040300e1079819840540a01550b040d05ca036201240b141c0e80d98904006a51514511400c0f806620302401200b0705440400c58112900d03240d041c1007240e40038039404840b01182e90030184482820480c600039010036486044080d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 490214163 1250 490212913 490212917
    0x30807120f02031f0b030109230703020a0311130506220b040303030e1b06030a020f0309100506010f0e060706060e0112030e060a0c0f05120d09050601050303040305060a11041203 78
    0x342c1c501024059903d20240214401003201044e04000210311320301200d0566211100126000c00d02d1101e200c0c05e0088200221030100401003040351a0b80c0c0350b40a0314400c0d245030750902140c10445103c01552081c15815400010504001d02080c03c0480051044001d400c955a20074400c483d0500c0590003140c114890f081c0c0c0006041003815418041c0115290202c2d01a0030000c8901d2820105d540030500343c14007440e008000980d00503d15030648030740c1c0c08034680c41503807454201011910b51103e005d104140d43e01c2c02c0086041548a6601500d200c044c5071039003210080300b4003c0059a400c040d10440382e86440e410003090301c2e08648429402442c5c0c40203a4507811101e07213400340102e4844a15107005400c14081d640440d40e01501001c8640d411a860900c071a400b0b00303003181001a400d484c00004000000c0f0281018855409800c0703c0c0d0099007511100e0f41c88204040d1248264800039010342c4c0300324089580c0c0d03401507005807c4170948041083c909595244845400d40d4142c2c41070300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 490215413 1250 490214163 490214167
    0x815030f0a050705010801081b010504030204060602060a110901020304030b06040f0c0909240312020a060c11100501030506061e150d0f060f090209010e0604092f030103030807120f02 80
    0x801c1040c100704200280900f406e042403690706203036080303985a01808225500c25024209001117900440072500039580190041c0541602c0317840296481105030781c441d000c1031a00ea8010824140c9000f544c03008001680074500c0e051440c4c682c080960009442a58099981c2001c01d044d1100e40c07140600051441d11000714952402c40313088125075110462011240307a912100c0801c002444032141030300c1d809299810995160032007240f4100780440000e109a203050300750a6010340040e1642451486030080701c80010340c8040c0c6005903a000c1c403004111b580701c2c03000b00c1d0640c0391101011040a2520600c0c3c19030740707020070004006040b90222403001c9200011f42124600c001e020b13a8050350741046041c020b071417515400a030322441e1032113002080c079800704190a890380308a52030510510b00511483d1169107a1600d08010b084d002c0d602c0140c00c02c04405602d01198100c16003c41400562450b42075070301e0f5440c1614100b00080c200410008150f034000e2a5400b60b21802e100c400e41c8080c011303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 490216663 1250 490215413 490215433
    0x209090a0b090a050f060108090a050601090e0c060c030414180109151d060405090102130b180d17090105090607060902040b1207030839190803070815030f 68
    0x480c184030050034800c0c2290400f8100185d0091084a054010305d0a103440380040d91288070682c113154400300300906900a200002031f0f418000d4100340d10b26a540d2007500c0b10716044000304140c52091114641c010340049c4000c100c13802d062034100b80745101c060304101e100071246040500d0f5030001d8210603411551000c4280494000e10180c2018184141034020444204c000c2113558820041c001803041c1e403501300048190342e0039010340e51020144100084003e88410a22202d50800b10702c02d403480c9444041031000d0b28283c0c1e40900404c1e0090800c03031480341c500c8884840781d0301c612402814008100001111034481c8402405000d016000c00502050b49104210560350500c01c042e201d80d40040c01c28001e4500031451000720fa0f0b11080d0b80790349901010010304040c2c4803030b01034000050003540d00d154904074020480f54102c040820350743d034030038920b006e41118045004007800300501070002a6200c0e0041e980c00c5d802240800d01c0901030040c1c440001d1030034078101c140481e6500500c984e2703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 490217913 1250 490216663 490216669
    0x20a0f15090b0906120a1808190203090a030f030c15020304171911071a0a0806030304060e012327040b01020d18030b10060f021209130209090a0b 64
    0x120014046040b003081c500b01c030407000a4110b0060401554811400c40b01103031000700030750703ca1108440d40c03801d030074a003002c87d041c01001c58105007180ea502d60340c00c8106109080c40801140c0016400800e025030242c2552034a80c0402980c84088040c0568038094001240d400540d0b103000210005000d640d030b28080ca0000ba1135842502c02e82c6900000b4443c08408141410a0080000641c42c2c00c2c2e00d2400c0402120b441c01026500c1a960010120304010a2265140080000d225540c81c0c0204a07100c840038103907a403007a48101c030005001615000010741c4180034240b1141d004072401c07050811281000da02035030084c0c21001c500341602603026601403002010111000c802c840421810180d440080d4170389492f101403c0c00c021840e441c2c8545114007003902406541c10080304002c51406140c9400315a41500951003c10480b201c40c50a00c2d00c000740344c41d446210000c2c0c0740e050120803001d1101d800703c1101000003460302444a19401d07180c00141c80c0c8200a0240c000c01c00711010814 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 490219163 1250 490217913 490217927
    0x909060b030714060702040b100c0c06080405061b19020d110303060a050d05101a010801270c120f0212072606011101020703030b0a170c0d020a0f15 65
    0x1640380079030801141000b000c0d103020760329069154282c07481c5a0341d182ca0310001e0014840c030300074282d000001c91045000c0c560b00a41035002e50b48100011416aa01d640d0156070b02c450455004005a00c404001007403c0d004003540001900702d0b040350b9052020b0444900e40d040020780c7c965005900211840503a980d10164054203c07200e40c01662850800c200450310080752809098062400c819000f010070004000c103914000d690102007240c0341016210449900f0655603050000e4008000800c280010003004000804a140c24101d800303c01c1d04444064052140c060013805460141d41520324414010f55040550040c0c0050703072800056041440c00901a11190030040e41075920b451014a020350140c044800380110101603444100499450304c0780d07140d20940754004603141c810150940c00c4008a01000c603103041c0c10795111810403032004d681c1c2c8800f88031a40b100c0c40c2c00a950030440b04483d03032103001400f0729000603107681040100020540c48803422504030075540090940c0065 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 490220413 1250 490219163 490219181
    0x503061e070e0616050a02180f07091215180510060b16080f0f0720120a060b060403020d0b342616030513170706020f04090906 56
    0x30801c0d001d50440b0045501c90181c4483c0159550003407100d0000d1001c20028940e840fa8010320740c461401403692042c010240907541089641c40134004154103d00460781d04041c6c5945500c14080c04081c0e4a94030120f00021310000c00ea580cbc0c0d0800254031034150220111f000e400b400082c04041c001d50030755011203485900030040c0c854144680c0c89801e01c0ca419010003d90001e000c1522080741181301e423842c0c800d01420504402c0c001031100304000e45400d20301c529030380d140781007000000054180901c515110707401140ea500800f012100081c49a80302203007103603019203150706080c0c6a030302081480441d04400c4d01c814404104001c16040f09245403e14140e4101141039800c40150110715240c4501c0303154401c0c4200d140f00b07680f002041422801d4060450714049405040c84d90054205048046400001030b05210014211054003039121840d40c1d80650b41c521000c12405802900d80c001c19011a0516002c0007032071043e03090704000d00701400c0c08030400184810035113800d1048a403001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 490221663 1250 490220413 490220417
    0x220501060801021c050903120405100f060602010c090308042c09010b120309011728150b03040203150405030d0204080c010e012c03010f0f0903180b07030c08040503061e07 75
    0x400c00003104004419912409200501d01c2d40030380399850014200045a01d481c140b0510f4033315405a030940c5500440100c030b80c20340007040340061070601220358003428040a040c01310108800c0204159255a00d00d000000491490007401e02034a9600d900740280c3d200e807016034464403984007034580080013940c41c0c226640154a40114000081c00700e28000e01c1d0380b100140701100040c0c10a03501c0f86107072545a0301403d81c4040c0c030034065251008103903c4a0056041e140e141011601c0c1a084040b20300403500100103040000303110b22a5080c0100042044400b40414081c03010407038010300181c0041c00e050b00103008614085000140f2030382c03d100a1034100a018100420840c0006414401e0b406404803071a0801042d4000700c1d025201c0c20b120b2200903860803e04070850505a441803201301c0c400e955801032440d031a40c43d40d0b0b1040e01030080301c442140c1000b100001a00590303042040da4426a03600e4102561000005c0c2044c40840c1c08064403800d525111011000c05c01e85564400514 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 490222913 1250 490221663 490221671
    0x7090906140c0c12090d0807030210060902040b0913020f0c0f06160c02010806010e0a0308190504030201091202130507080402040509030c0d120609020408070f05040b09220501060801021c 82
    0x2071001c83c2e6581812150108501030006241c441d1901e41d0420a103066401281c078581c3c0b0405864003e58490070040c00c070450a2400741c010455800d2030085030304603004c000c0c502d070030b00511508115484140b035462902c4954204158000c400b82c05010f0409842501c0142107451140e40c1c0c0c090038020020001000d00312850b8035012544e4100d03003581240394080c6051102c1e5543d800c010f0b144603c00350003da50000400d007000041181420081111b441c3c140300d240c4c8400b44840e415100f078080c5010080c0815141d000c140031501e0001c8120b00307101d0006000c0c01800100e1101c0301c003140c0341038034450002552481040305500b49400fa5a400480c20801989824180346506460740c600c40032080410000307075105200b00f075283d0040301c040c00000d0011591359941d4404a5070700c002c28811007a50819002e030000e5145464031420001103006801c0c0c41c0c081c1e80d05060360303a45201754481042c4500303454244c0400300d43c00348103030405000c1102c001a0b8900ca5040b55000c41c404908407650300c5810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 490224163 1250 490222913 490222927
    0x3040312080c071b2103180b030f090106031a010518010317220801060e07020d020318180405010f181104110c01090c090f020a090b090307090906140c 66
    0xa80d108441d0703120b422034036064100c1c03100d50141d01c002c80030b5408902269081c80d8142540045e040d80d08100f40d200740c60722125410189806510600310380700d05003600c1020302c0010b81625242c50f008e580200c0c6600005021612070744c0310181c84001e200342d00d00c41e80344c100041c0b0150804501c8000e910590385000c055641c995614890f00a8422408090401011900c19050a040004120304075070340c603031340041c06407a14499402407270248600c128102100d13001c1007a45001166010780c42ea503d9001e0b61800c0e55228540750301c00540c107119a00070090904010080407401002c40c040ea01c00c00c004180c210350800d411094642c00811200e12140388101240091104042c182c0540b405540c04502000206000d0301c25002d0f00c0b44032000c0b035003004480420482c2e00b020341c84c190f0780490340c10015005410202c2040340110792400d00810a840010b20050081e94060070803294014100c802e89501ca050358000e4030707625001247c1da20f88883c220010842640c103640d5100703580701011420084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 490225413 1250 490224163 490224181
    0x15021207022d01090f05030702031507080f0408040b03090105180309091512100f05070302090108132105070c120213090c030b01030f03030e07050607031d030f0304031208 75
    0x1802c0356514001c210684995401803080d000121025004403100c01d2100040c248a61207500000c3c040f0303c00e00880d0200c004003a044c00209014441c987e80f0003c00b81e907203810f250340720040078000340c2300c40c8000e100c000761000e54800191304c113104c5240045041c0c24030740e00c00c00340905004c0c1c800003150000d1010100c55140c1c01d048550103104540014450202d0401049049020b945600c506001d0103040b119004000e40240ca201070440004000f15610354004a0880c0940c809207400150b0410214032103500c0c1c05101b0424600078610a90000f00314082c070003030b50089088031313404150b0200e0b841d414031080403201c0c001030080500d40308101c401680046c45215191440c02007a030b6a81d00300100b48031101001c10081c0d90b0125220740341d961070f4144a03c081d102c5a074114000380c140185030403080004609041100c4028100a0810203169000ea88251905501a40502d00d10404481503a004c02400c00784d1820300d00a50390744c5017135040800030030041680c840c06008003030061100303102d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 490226663 1250 490225413 490225453
    0x807050c01020d050f0d180507081506090103080c0f1903082a0a090b04060905042301091d07061707020105060d03030f0207020901140a1706040318031502120702 71
    0x11031180460303655409059954008040c624111142080b581f0b12000400200107014000c0d40c0110782242c16070381c0a59525041300c2030850b920b0f5002616100100001800c2c4009041144071420640c0c101441d003444061408217143e40360b10440d040e861002c0107254000c005541c12100e400c0c00201d008400308200201008103080340c501c9503800085082c00244140c00d0396000d0512490640c1d07481d640c0f10801840c004480c000c0c184140c0c54a041d240410002d140507100e203141881505010b43e19086d5800c00500c0782a040c90040b0304a0024030980c1e01e01848040301505071920761aa010b00c4412010b405040020204810340e0b1406040c0843d42c0d517a680c500c14220742c14500410341c0c1003070f41c2101d0041d000d030004c0290480c11580001c03ca21180004100c60780074155905200ba56540c18214810340480408080c1500080003040220f0312441030103040e0403803070841c1d086241d41c2e0b135500d01c0105100c1104030791040c8c1c0450710840750102d1030740164000c45184010140f010340354a982c0021 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 490227913 1250 490226663 490226677
    0x908030304121b0503041818020f0609040e151f031a0408040905070f23030c0306030c0d0303020903101b18080a030909110a05040b030903160807050c01020d05 70
    0x8012600d450003800040f01507101c1515503c48283c0e40c40b01c0e80c503070101540700d503400c00418525080c0b070719041c491200c0d420240d004e00c2e00103010080b035080b01ca0500c4115405020084d41150f1156110300340c43c40208000c504003041015608402d14026600c0da02e500034940041c440c0200440040010070545600100021400324544146460718902000144142ea0004550301d04250400c216982c003c65150009000b82d1a0358071070340e12039106904c951001146060360514203001042c2c440710780201850344000007404482a8112407000030718599660101180060340001e1901c0302420300b03124802283d0a815414003218591500242800c0520728a0b0b4041020480070b4020064083d800304004041d0704003500c0c45540d443c2030041012405d0b01680e0121403d052090424400280440d11105070aa0b600f40c1460306000890700c0c6980050030101c0380703110500402c1152540c0882c5203000702d124006059889550b464414203191440c1000303030554001222165030b03240c0000850303182c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 490229163 1250 490227913 490227917
    0x501061409150118080c010e01020d140c0c06130f1e09050601030914030d1a0306070c110604121a010302030319110d020313120203210d05090d090803030412 69
    0x52500040101da184106208101100c01385000020381c6a801003440da8070030f03c080c2e982c041ca03000114016a9683c00c0b04007404000b4072035426801b0b9081030f40b005094018100c500b590100c0040c43d000590503001041104500d00320340368100414554000e149009102410000c078840d100042892444c1040e0312a0401d402d4580f400140161b01c65400355001c5c660100c505520844803c00c0c059030303504045011b1028625003000a10805005004090900310060062145543e6a14207d03582a200f40049501d0000b84045810582d01c14025001406401d0302a0b00c50201c94180524605115209100307607408403030043c000750310040111506820b030710f084004441e01c1c8a00845403aa407080205020313004001c44080d426a01200910001e0050382221078200c2c0c803160001584e030740000c0001e5040e03200b0780000b6850400a0701100300c5801104800b4241001030011100b580c0003251ba02d03442c2d070030030210082c1c0250048580350140c680c4200440c01c620781170fa54003180303407991260041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 490230413 1250 490229163 490229191
    0xa05070509070c02091005120106150f170702330106031d1005061807090905040602040b210c04120602090a1206090201020c010c030206150a1d040501061409 69
    0x16041c1c040c40d2110001079000d040000141ba10107000c245802481c0540b03445100c1340b44091062107014017456003074580914a1892508144001f0740c0c04554503269502440444091010054240080c440c89003801ba005440c84121601c182010000b000304d8100702074000e8225684078804242c041170540310a41800944010380041d60340d421a520340c1e85c66810b100d40c1824455040141e041507024100c240c420b038554400c8040352200320ba80c200d03848000903e4610080180065540029070841d014030001440e05450b503141c0c2d2219403040c1030291482034100004004049105101a40107200c03220741c900741810324111040701034218202414058002c80c410142c0d07540c9951450080c800c0f80d01003c2d4900a918160b030140100c04c40607405801141305110865000d803800300c128036490f50103441582e0300d595203503500d10052100590000174500d000b003036a6403c1c03c1002002041c65908a18920b01440d0240c25619240c000c410b4880c4007411441c8039071115081503400c48000741c8505 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 490231663 1250 490230413 490230421
    0x909090c030d020a02120d120506040204090608150108120a14040b040608090c03010b0f01030e12030a0204081e1c05220306050708070516030203070c06020f0601080a05070509 77
    0x240340012a488496042c02001061031505400203030a03800c0320f10960f01203800004d0382c0c860b151940c00c9488031401007107002c030420140c040158032459001000420040c205512506c59104890fa1508202c1240c3e11120911000500d800e045500400d040070041544504401d50700516008840b8401c00307000c101c150300030541c0380b0031080e10003408a00c03042c6500c89540d180002e2108200303807465482401072441080807424180940c2d0302441c00a0108030341180201d00440044c00c507105080e92034010110440c842a170103200450140c8000b40300544c40b28100000942880136120b001c401d0b00130700c04c0d988007003d50081018052070348020081a20040c50240c240c1d514820070702443c0c6102218070500000380c84d90020300007680c1c0505010800c80c1c0e1094010344035108203482d02c00115109008102d110550480c49000c51440703413044c0da040003002da40c0c0d0306078a10030740c000c00050b8010b180110200d510070043c160044c0a400d00520140d1402e403161521501d003030092501a1031804005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 490232913 1250 490231663 490231681
    0x3230f0604020f130204180207020109081b09091009050d090608060a06180803070303090606050d020f0f04020f280f080f0601090312030c02011d0c2b03020c0a0e07050909 75
    0xa03800600340d0b400b0b1160b140802c0030347c0500039440f1401c00c80c04120350031800b11307504a00041010040740d55498807076154a445003005024440141340300901c0c8a142d1004c4440a807034040d02414500c42c0c8004d000030155008003904060446e082041000705002c10481d081d030b144400320701290b000d41003a0040180581041000109907000100d00d840002141c03130816905502101155015202c00c00225031104204000d055003848081d5100f0703100440c0048034a008d0a41c0341c485139004000526180015000c03540f90381100242002480350030381c20721003a0340200102003165039a8078014101128800e0080c0581001030600038101e4888000100680d029034003240195030015601e5048480d01c9200070007501040f04200c005500304041000c0c801e5141d20365950311040381000c0c2c5942c40c040401c3c4088100040d02c2c26603040c10919229844100200c0d40d01c07070b03946c0030340d0140c030651117404181300c1c0c1543c040d4001c0503c00654410080220340c000c05481c01c281341200c86403030365103030349200c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 490234163 1250 490232913 490232917
    0x50c090d0807020d0b0103240506011e020f100e0c01020f0d03020336010c021c1209020a03050d080c070c0501180906090e0c0612040209070903230f0604020f1302 71
    0x10017019650344030300100a014810303441c5203c1c0007508642c0c50f03007000b000420b001a6041030750340602142c0d510126051200c1c065000c00e110392090f104440c1412084a0501e203003202501442d50429600c20641e000c0901c01d20102050348820700040051007059075038641c0e03400c20441c5204c2003590100c089401c4007051001d29005440e001000c100800400d80040040c01410302600450f6103001754047c4850300115842d0a130002e0140010b0041a141e1010788129022113a54440341d581d44460030011ba40300650320014602420050008424442d0040e1030704001030700c2e13480d07a180f060150300000b900c4030f5046801d0320000e290401d04030745560f45400d40400c06400c54907036141070802c003044260095001054200410049840c41441b035810f0119510480310480c4c2e03540d0740d01c800180541002c0c0d603400c1d00030245180010035039680f5240c0a200e10a112403650440003040140e6205d850701304a084500e82244c40a851582882c0d13000035214944903813018000d29800280342586580341d41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 490235413 1250 490234163 490234189
    0x6020409060e0702010c02070e01050402070501060801020a0507023a030c0209041b0f1203031e020a020304030b0c1c050a021611120703050631060b0103050c090d080702 74
    0x11040c01030780e84039140300a024800300c464030010341c600520490011301c001030350011140d0851003981603900744828000170707502449050b0780b5992119000102200d00344024500920696102e076150700140c41049985241019400b41d440c10a03441e04580000380c41200d82031014201d00303600749000626050301d140c60764650295101d00d504040006112880920080b550320b400001d01d00a40c4698403140e050a8500400306400d01c49070f02200001d01030707404001c0321010388001c100c113601c2d1380c0070f84000e903481102c00c100107800c0840e042040200600200d0f4002c620400210308000d0b64010268000c1c0d0321003440a04c07151504085400842c040d4115000701c03114900c80902c23050350742445e2680c1c4820b00b02241c0107a0380b483c40207546140220701081903907801070182555031181c0d240902c2c0c640794041e895200400ba220048036074410040c0000346c552080d030011818501103000074084a0b4004c101000d01103080105807401d0b41c42c0220b0b07000c0302c2d900c8001107032100c4080c000b2603a4640014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 490236663 1250 490235413 490235429
    0x5120703051e2d2b031406060c0109080309070602010f0e0a020f0a1a030405100c0f1805060705010e060105010f0e0d08120f09010f1506080a15060c020f101704060204 73
    0x6030310715800d0152100640130041502e120380d10042c2e269104600300c0f000d41050b5101101035030080b0f01d0307502e401001003605204000010940081ba51900c03681030303206132010755190f4445a0304210a9030207002d2111001842002044580c000800607611f40c0c0ca0564000d00c05d441200e006415581c6100c04403000e030400c21a882062400c1c0718054540d5402600c01b0f90b0039102d041c980300395008041c090040c80a20300d9072000020010800140c40030200e8141011802c0d80b039920100b40d58583c80d0250410b1406000042900c0541360303141820010184c001d01d0402410b0703c490201690003c120f00b4550000381c1c0c80d52480382050400c03030541d00809028005c5a01c03505c00380000802138600f1140103610200080001300000000841200c01001d1030b941821440c801c20050140180c5d00154042d45608003c141040074004105a400042c1c11060204003200056002d50900f01c507016204802902c15090824080102400b00503612907040b1140a542000808110168041e9002030600c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 490237913 1250 490236663 490236673
    0x41205161401170c040e1506070f0204181718040f0501150309051902060c060f07020c0613141f08040b0f060d1401020405120703051e2d 60
    0xd0014844074002000d00300340090f04005004600c41c0c448002c2902650341c0c0341d8818a0a4542940c1c4000303281c0040c0034881c1c000190341c3c5089944c540d0030043c002e0910030407001d80b18078940d00c1003008035015809140c159601c2ea40c1c0201c0025071000003980c510429480d03181d118280d00b410b5200740d510304050395400905040b2043c900b0350341364100300e0503030356180f0600070081e030841e00440844005a402074a03030f43c001000b9a411061018840040c0e90020f804c151424414500c154034240b800e4860a180c00314160030008150341c180b158405200080b074101e850881302540c0c0e4840c5000d240124410042d20181030640383e9039a40903684075120500c0001000100d241001c3d003040c804860559010110304001000820404001c40c0b02da4402000b5258181d40758488240d0030340071603507400403903600304004501581c0d102040050892070f2002080140c0c11454000d05110055500c454028200782c0c400020600110340c0102d1034203003001320f0041c080c0c1c03070700c0c2d807442c107036445801d40f507a8052 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 490239163 1250 490237913 490237919
    0x30203070b030405011b0905041802060c10060902090f040c110d05030906130203191104140114090609010308090301020d020f0705070609051e150a21060b04120516 72
    0xc07040c0554440c030b000320020804c0108031004400e40980c10124140091034820050080d442c2c1036000300080c2c0740203017803607607400015804910541d00002c0420071a42c40660900e00c464260300908015203400b460039418042c0041c041003420b807810718824480d6445031541881503208412940141408000b103501e140c4d090701c0080c181c0c2d401aa4082458083c607400161490708046003180c0c80c40e405001045804440341441d0040004440d0440c0d010218166155146d0b55038051880ca01c54105081c070f20755450001210351016029070f407940a0350504040103010b42c0c1d400243d40c1101c0e08031007440c0e1740d5500c500000740280700b29280250340d18404520032540b542d0180103000c030740c0d200344101c420f520345540c0145c480c840305100f4650300500d200011702d450a141c1d02c107802405805001a0143c8002000c1540d0755004400302071300140340c0d144103980c40060071248030710250291004025050030051810110b1050303004100c55102e46150740d10420204204c0c0e500f52050b42401040000d031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 490240413 1250 490239163 490239179
    0x4060e0d0807020f12190e03070902090906040509030f0c010b3f0607110106030614190603030c06020307020c030d1e0e0901170a0c0b0301090606110a080d0603020307 73
    0x400b039034a4001131040e44515044400000349811240390804403050070b003400e031a030307820070800d07200304650401c84c00f11590210398408022404c00b5004e08480583c84848050611810b81001001c0c144114240350a012000d440442165805800d8074002542c2d031345080c01071805880f19a01142c2c1102844184000803088001c0e240000c040390160814088550003002c44454907100b00710212f178020b60b010900c2c0038040c400c10550a020f260010603410380e46c0d11224200c51a00c8035240420031044104001d58041a8918104203d415020011347d821038030010600004d0107401081143e0000c080742603d4020002d05054510082c2124034804603c280241124440d01080050403410721140c241e03180030f00c480c50050a4007a00348020f82e8039100340030310080e020150f02d440038064500c0000208100204400242c0400c43c01566a54540800740003201c1d202c0d80400104011074582510803103011540000c0690030055940d1111041c0b10100010443e5a0009502d0702c103d0300c0025400c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 490241663 1250 490240413 490240427
    0x31c230f0610020604021e0d02060403051c050f0d0902040b030f01140c0a140a0c0b01090605030d030507120b0a0803040603090204050108160312050d0905010f0608010c09030b04060e0d 81
    0x44825102d01c001101401800c2e030b916401658000c0d440a0700140b82450250180038603001c5141c02480800b5140007600402d20348d038440d03081500c09402c1007038a01c20032411045102441c0b42d4900e0700500d82520f00c0d0415080380034a100088405444914800942d9629045020000300c02010b0324129524450301a00800040c000f03e801d441580001441c40b00b6820700756102d0443c2911045405001300300c0307214459010500c10310522841c00303580c10100b44503015150203060702d075000042132030030502050324101c1e44c1410303030081600345800c003e40c1603802540e10101400800c0082609464000001c1d000031254010101520001ca80000c03c40c1e415004085014000e80b01000980d03241e45606840f5810240503800941c2c50a20070800996010480c0813103222a14049080543c5540f00e541940c4002c6400e0b03c1c207030f4466000384c0c441c00f1544968001004800c0082009050f51440a000082031344005004808180c0c0020248400f0303030072a4403c08100015034581d070400740030244c003034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 490242913 1250 490241663 490241671
    0x62415030604050c1602120f03030f070e04020301030c0b031810060501030b0907140c0304030c03030c031d090a0b120303100f090c0806120c0306090d02010c02031c230f 74
    0x40381480f000c101c40311051030460341c01d032105106084140600380c084c410700000c01c529040d01440748031402407100c401440990b014010030314050004d81400c3c4402000300c4600c1c1c130441d00c541d104000400009000c000100d048404410b113480c3c43e540c2e6049106400112094201521700078071022a51a54059103d02c2c241c81003601c080245604900074010b82e0741e02110504007082016801204205409010f050103c50700b408991034545c8036a10b01c0c3c40070b0348550044000c0350103984c0c0c0c1010142c00080707403241c5a4007000e1505c800800140020180705003d450b241c101d541d54442c2e400340d506c443c0340c01043c03020014210b981e030341040c4406140d40f0600340320740000000c1a410120701c480c1c540c000c0090c100d8207035507103c01c1030f00c584d400c00503a003100c2240204c161191a800d00d6454405112692050b91040040d180c0c01103c4003019095490001c1c12504540042080300c3c072024801402d45c9000c0e042140c001128980c0c00c00c0314085503401039207071071003031814001c0050040d0248025441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 490244163 1250 490242913 490242919
    0x106050408010e1c08040f060c020a2f1908060903030a0c05041d0a020702130e01180308310606061b0305031603060510050c0c120624150306 62
    0x428000c100c0c0484d1500010707001140c586000740042c06200c0e10075042c3c4c5400501030036940d005480d466071104100c501807a00c1e000503801c190441d1003401254054502252360701030031076440c10806645041d9408860484610403591400d051203001b41c00e0700f000000e40112002c540c010f05245000a907a90001c0f6941c0c61403e080120580d01a44903c069804030303000c011076581402e1300d80c0b01804035030740001d1003000303810360900200c00540c1c0c0b00d4070346040103400c00c40000703400e103d003a04c1c0a003981c25586619010501c4104890700103a4000c5440c2e51001012207050284502e0800307580500ced50414424090320051b4100c00c060100d40d602c068203e079900e40710390300d910f001444100d0080c0820000075000c25018000220795110007810b0150001941c900041c880344c0f038000045116405680b2b075000a9008a000c0c0e0141404100d5171541500841e0701510f03540000f0540d555451008040c60700d40300e8031800701c440e0840b034a981c0704104040140020034130003807440c041d403054000325078042c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 490245413 1250 490244163 490244171
    0x170c0103090c06080c070f060212010b04050d02060714070314100c0504060e04060302330c063c1f03150c050f0f040608091506090402011106010605040801 68
    0x658068800c0850050380410411402403804800740c50164000708005d0102100700001400a001400c42c01e0400d07208880041c0c82c0d92880c0c02d01024504140c019100440301007009006a556100c00c00401541c11503002e5641c000915110141e8002a001c0d40910306c1090000310030840408101060202131404030b0b9003448030001c80c0b4056800742c03036050000c1760081106010f00d5100d900d0310a042e8001400124605503241d0100303080005555814152450024424050228990074100141a1090301c03e04041d5040543c81d1201c4000d000c0699000752181c120380c96117190300000300a480c5590101c081594082e40c1c1c1007034800100c0e8181c2e03410300100b4581d002802010160700941c0c7e0480845410450194611170040c901d4070707244c405100042c0170200c04109580010034030b200580800c9610f49241140c0544030341350141c22880c06422541421500d0109800c0301648140200c54603044c60703c0328001aa0078080c108070400c40c40c0244000415a642c00a004204469a48000304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 490246663 1250 490245413 490245433
    0x22107050304020a05060a021e03040504060623070c0803030f060f030105070801091a0604170c0a0e16030204150815030321061c1220030313060f0617 66
    0x36014441100e00950000703d001041c01541448005010380c080940111160070040c040c40361041065480c52000355440000c09202c039060900605009140324245004400c052914000e880c402c0b074030900d03091a40c00b0800e141480100070391000206102429680d607402c1150607800d84840c00c0301c50038018a610000440709040c144640c44c441c6646680d01031250b400c000201c03010b0120010503180038101130351a800705960341070041009052500e28211039100101d2001c3c00e10703144503203803481100b103c41c040080c02103820340307664000f404080b001c00282c84040158002c3c052078101faa0390800c14509111850f800400080c000c814180c114034031a1f002d03a04040d82c0b8400c008a410740c080c064010f81c00d208605000181d0006001015000d8000e001d203212081c1280307001c0c090b03550810540f13003a04000d400a05886611030501100e800c446000625950380b44400341003410003c85824482090180f0359011a03001841400180080307987c840884152561044041c80715002d03c4043c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 490247913 1250 490246663 490246667
    0x8090603090c0a12030e102705121219121d1006060c1e14071a0304020d1401090c090609061e1712030f07081302010e061606022107 58
    0x21300e62954196500010068064180030040d0260003c00080c0300b4030400c0c1c800c60600c643c59107050105c0100ea5211028580400c00041b013005000c003682d40e400c101010190008400e0071200011100c040040c1021012403044803a0251105600034061400440c00701501344c4404000700080c0b2041120901541c402c0d401c0b040ba01d5520030980800c00e107884443c000b6031402c071400c1038030000340780219100c1482d40f45c01072030001c00d5284010382e820914080c000750000110b00e142c441c0d000c842503800d52030310742d0105040f24000f400140070b61180541c03c90521209400c600351581d80125000b81140c0e4510540e400742c503c5008034618941800780210f1000300c110b8101070f41103034950071200d035186000030914426240000c03629013030145455040030350010100a40c06040ba900442e400f900d41114000c1103408043c00c450410f0b007080600e42c01517a030050041c80c41580403501c16941cac0882e50320160301e0040060009041324004910f0000ba90f10382184d940155400c180d41c8062a40d0300101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 490249163 1250 490247913 490247939
    0x90f0b1206010e0601140d061d0a090807030815100f020c03010b09060f03030708070c0e06030d0c06051021030801120803011203050d0f0e0c01030c051608090603090c0a 74
    0x25000f98100302100007259507100d02c0c0214428100300d90703d2071600c02c5003403150003a1903150700964490504038503055414004035210b5503000141000070014080c0c10b075142c101320300c1007120103030030801c0840200d50444050314029400c04801041031a0010585c103014007921040041000580103480c04400c4908040c00351000744c81000b083c1548070750b03607141001400700c08114410b405201c240080000a20400c000346525070140c13101e14481440d10300400c0070518006c02ca24026001003209580d1181c0041044158541c08003000c00e49079038407140d02c1107504803075000c034003605e402503100d1505c04c2540301045c44180c080d58403d82c40b6a00c03540620780080d40800010010842000104050303000e907100301c0c107a60711038944586010400074110307082c1c0f40c480c0c0722407241980c1d8103075200360500c007000301460302d03030080c01c05100fa2611640043c1445c0150341c003000245018981c0c2d0010003680742c0890304010801013496850341030510310340ea81c60800b88a102d0003014000804601d010b03402e04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 490250413 1250 490249163 490249169
    0x3020f0a080f061f060c0f081309021210050303180f191805060607080705070506030405030310080111090d020f04020316030e01020708030105221a151e070c090f0b120601 75
    0x25240d15071b216a94803840d600441c000b06840200050210356503a0541c44401001058080f20142e10f49500d455408210140079009071840c5492000400c0076443c080165141e0507880c20b20042c08091400208030304204400180e0b80c402c09280003d44480c4e440104042a02e010f0451040e100c035524039203908030740094880b60b038800e106010801c0061050402003404a1141c0705039280c0d2507449010a11541017541d080341c040d080401000020800b040c4580003c0000354024464040d00000001162103101005406480d800080c0c6095403903070740409003100c0019208550303a20348100b4040b02c918420120100081c1044400030314900c05009890071550001031241c0b8603480c01c801c00c45640c20948035020341040b286000345040c07046103c1c01d81ca43c12056250399035106900200101c403d940c1e1030040e4100d5007840564481101580509003c1c0c171910500e030303911071039404d15141043c04d0b030303120141103030030318030241d5100f200b5803c200c1001e4015292551030803001c2c00929200c80c0240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 490251663 1250 490250413 490250417
    0x4050712140c040e09010213030c060e030627030705030304030206040b0c03060109150309060e061005010912140a1401090308240105090d0609320703020f0a080f061f06 74
    0x1003c2407121180c5101c200da04001036200041c81c001140f281d59008981d180d10648107145040000c105094004803204844074084002d0901880c101c110034007080c4080e0099040150200001500ca4800700110b80c007a03508003088a07146d01d01890000d503140411038080341e800c801000031030780ca87d6400d020369002d144140c40c3c91843e141000c0610302900280403411b41050b0b00c2d03c413190003150a0348110448828018041e01031b519203801c2000348608913500443c100400001c08200480041084c14010707640500484000c4003190017071440c06c2000000500048400c01c840d440c9250158403210584d442512010070390b075510040d4450700f0041252480e00ca61215282d422558400d2006200f401c0d8020705500406146407940011218098012588190007844545080600390b140011601842c202000a2518030303208a072aa521840020301494400300303400034a5482c20940c0000d051b01d4002c503280e440400c9200e40d83c68800f41d5040ca640500100002c0d9908040c50014007540c00c25 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 490252913 1250 490251663 490251667
    0x60c090405130803040f110a03030e1002013c02071101031d0a05070905060a0308120606070210120f0b0102300307120b030316150b04050712140c 64
    0x290900001c0c00703006000682d00c4481890040000391510301542c0134078000e00002c1c0c60500b0a282840b2410b42082c0001d20502008004000203a4800d00500642c00151415031410000c404140c1c0581040c9180b010a0361200c4607440464500351886804061461031280d00100303620081400c0b8851204068034000d0072b00365810507940a81c200a031024180104000c84103120b29004e814007002c810100c1d059048020100481c000d41d015481d00301c84102c03010585e0505c0c50307885000c4c6100d0521010302800800b0005003842d03407281d080e601041d8001d012088140c88041d00100415503a40c81c402c0864035001c030348140c070f0b1070314800d1844d8250f040c0c0007804003c1c0300c8400380c01c01844603040e143d00b514204200342c1c1d841305100003550085055071103030001006e8000300d400c00c0d01c2c04c0400241c003c0e80103001302044490041002d00005130042c1003140745840520200c805010782001c02d540142c2042c050287d010380c0414028441c50740c4000401c41c1c10955440400301c500d007a14090098441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 490254163 1250 490252913 490252927
    0xb01090c0c08030624090102070e091c02030c01020a090302090f06032d0f0c0108090303070906080405010f0504050c0a170c040203060d05120d230a1112010e01050a0602060c 76
    0x200c1c2c0003c50300410028104010105070032001c54240301c1d4100000360011000c01c1000d1a540c0411000003d003116506020701c9151811105070346600810035140608036003116512914020300480d5402e6207014000d6545011840025084800d1481f08038051443c400c00140b0030208035441030f024620041c050010140c0084c030b4100c805100e601d800d501d1114060700d04c50b1009080007001e42d40118800608490064107001400229000304031034a1a0000c00c100314111345d01c042c88034140c5603c2c0c1400c112a88517414241e00410b061401e03684824035003804e00c004c1c0000000c400c000c00d042251400c2c00c0c0c0d5100c8100503413103190420050b8541d0f02c10000c20318285002c2c0c01540d03201101810100c800407041d10b586141044114140c0f42c0c1450000720409089110301075124400365551650155006000341c160040300d004081c4540c607507690041022074450700d4110b0724003200314030b214403943d44c44102d18030341d6100030304c9054460f43d0b082c0c500040d41400800c400d845124202c10882c24040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 490255413 1250 490254163 490254173
    0x70503071e14040905090f16050904230c03011a0f04090f02030a0b010602150403080711030409020c06160c0512360102010507030b22020f030c070b01090c0c 69
    0x40030070301c4200340107140c1150280140101c0280006005049010a40b810a14192418403100301031920b070795000a02d101ca1103034040c44d001c0048401c1034a400d08642da841c200090b00c0e10031110301c420740e0504440400003480c000160b25800c010304034002c0002c421001c01461620244400c0150400740a01c1c105440f49040d0b03015500c414012007080812080c284e0000341010044801111000308840040c00119410010b038110050f12480c500440e00f410b8034040d00e80807000380390710200003682d6030380c00203000103009441c01040c10210541d00c0e201540303807260b120003040300c0c181000410124660001c41c8a0302c010100190003c018003461808041c1441e481e50140c901d5544003031100070248101700c0103030145c007180f641666910b0307540c44c0d07400b00080c02d4900181c419400c15040a0100b10780d0344d0b841d095244003202d591013000b018000812640040e008032880c400c030181e0088100080d0014280c005d088140c17144030650b02c0d680c1ca800d509000c460a00d00b400c000150301000d0036000072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 490256663 1250 490255413 490255457
    0x80705031f110406020601090f0b060d050a0908040f030b100f121a010e180c030c0415030b070e090c03010b07080c3c071802091f09030b07050307 64
    0x101001e4070109041054040001c0300d9441030b070250740183c4c818070041222810603c1280c0181145000510540b014900014401c0c081c114008040c1a5902d02040e07440c3e0095000242c03c692100c0300315101c80d984c92410704203054500c0150780f101d100c540000e10303598021142c0340544042c01c101c96182c0b400c0140d5160400c40c000e00c01c4171048002c02c10140940d122200c5107000709001d003124074452522058501d201c02204000003148d41c05000c940c0055603011078001c0118105030b80000b00b82240035122001052298070141000120806025a49a10001c1420240400d0310360003410b44a6215059946c4030910039041700080c00c0c00b1810000e90042c00600440c503004c1c044420300c0909000003074a4030714030a142803000079940d2030400e0400008030400000800c0d9400344c440541341009000c08210550203810070950b00280b0900da039610342c031280400940ca0620035600180452010b8205041400251509425200002d000910507000c40b0f108a5155482c607844540c001000300d206 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 490257913 1250 490256663 490256713
    0x13090206041d10150c020f04060308030901020a020f0604050a030c080d02030901050105030c0a0501050d090503130803090103050a1107030807030e010c03200a0c0803060a05060d020a0908070503 85
    0x810400c100c0003400700c0c000404000c0500481101180500703098403d14030b06039503580580601568040c10442d11030300300113018607142d019a480c6552800e1040020018001500020b21080f008000c0c8805034205502503d1106c1d5036808480d20503520708000c66550b842250010415880021800c00192203583c18149071380c0300d06039141c14014000400b101740c0e001118103410070b070354580042101d86010810303d01e41d0f4000ba101e52500c58203150000303186220b00e0400080d0300f900c2e83c03003003c20090704101315003410350200074200a80340c032581c4203038880c0c0c0140c0e2f07054002410300f00860340c075120603c85e403000c1c0e4012142c0c0f00d05d072050650b400da0392480018102400d140e40c440071010091002e000d8105650300c01d030f1340020707540c014101080c03001d000c02500282f046028407a1141c8142c01080000400d5000a112912030750b92000280a20050b40c0000750401008919283c1d00e80403900603044040c03043e110190031a4613401141d8bc0d0704502c1c841c0302d074161b12481d440d10201b80c0203213080d004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 490259163 1250 490257913 490257919
    0xd0507170c0607021005090c010806030c0405130309090209061801030f06060e090108071a0f0c1204171c18050d0b010e07020d0909020c031b0c04110702130902 70
    0x403855958010440c58216411845a60304032004100c0401d50510150780020040f140070000c0341458002d580d40d80c04a4035a2506104075040850030303039641040b2001c0003a4000784103104030310b000514100c80c5c00c0491811800316540344000304103a0313000c2c001d440c0e810300040c5c0b121b414000b1060310100030505140c0702c01d0515680e07a0710144071000c6c03800340e10003074042601e42962195030f50f010b20140b0b030416440710703030160800e0405010b03010300e5900c0718034200091040280c850100c5940c084d420300c5244500ca0007071007022020703203080c10540003410849505640d104040e0151180f025151400e14090a46020b10281500b10440c007c00e08556002c3e80f42d00311016160f101c80118403401480d1200b55110083d20740100042069890610342c400054409414560120100a40460b80c1e5004080a85801042c60302e00094100f040d01c06815094010a10040d404003449454503500e855250140e400c0c8080310385804188021540b50315401303803920320f400b8105809000100f0100c5412a4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 490260413 1250 490259163 490259183
    0xf021213030e091305070f150309210203042d14010807080a020d090b060a080f0c1509060d09050c01180302090601090b030708161707030c090504060305010204260d0507 74
    0x8520104001c1007d00003403114040e0560a04c4541600002912000d43c2094146105030001800755141083e90703800e080b540201c40c50507000e01341d040d0300854016030182140e40c144100c2c0e0312901c1030060201c50166500305072168807580c01d200003089108156000c1542030002c1070100b0f10400c0700790703440700e400700f4014201b10043c0298404d80d506e02c103054502a04101c01c0c03200501e0f145100300d0050a0200088c0303501e6006000c1030b078940d641c225401d8407410310040b01010f610041011180b01d190010f001641e940a00b002e5000141040c0f0002d5959109681c6c03244140d5004810710000c01c01c21310369641c003ca00c3e6070300300a03503048001e0580b41005100a070001e03614070050051401442582c0310003446203444a41101003100c0c030800b19042024601411400c01d080b160915000300d40b5241c0800e42915000069680c00b04c3d41c4c2c01280c0080c80c240c0000103020341075025100365030b45503c015415691901000d41510030224807900747d80c004802d40c10155004030000d148980c1701d268210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 490261663 1250 490260413 490260451
    0x31a041a0621010902041107120318142b12020c0106030609200a03030503060f0a170f060105150417010b1504170d020c10020a05010f021213030e09 65
    0xb111040300100920407503034440070000b04518060250b00958403000e0a1503040801c540c0b2147c80703078072195400034140356860300c5a8000d481c81c4200104041c1c0c004e411a0302c1494003005244c0ea8001500100d10740280c04603a5180d01c00107141d5803081ca0380c0301d9a0700001d107115816400020350081c0100201740d940c61a000002940318000c80407030501510407480d40c0980f40030300f070420840207016284140450241440080d0700702040d2508500207989095059541101055001d100d44c1c0080170000203281290801c040001420111084240c0c20b81d0b2169a0324000c0c401d24000200722034441c440240001c1c40300512110b10840f21486020011401b80690f10210300c90078110210b4200100f000101880384c504040061074241700368000030608003660b41c0d0020348812900050b24850484007a210841901c2081940708590b000802081441c3c2c00000c000006d5000c0040e58002d000740e600051171200c0d620524840c0581c040d103d441d843d0030b40c8010030001d00740007854980b00100c4401c143c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 490262913 1250 490261663 490261699
    0x6170108070b160b0a020c0d03020306010206040f050f0703110a06080609010b0a09180204050405060105090a03120203120a02030618011503201204060b04150302060f09030f07031a041a06 82
    0x10340a0705000301700583d5081c0c3c034034403541030146054480080c107004101b4844142d90005070154020340044031888a40101c1c641907043c06000c2048100c00d00c076160001c0103000b04080e0042c94944126010394030380f555080c05880c00342c000c1b50081d6000c007180e001001f400c0d000000504400c00f0903c0d2100c005910783e214841c031440e602511380122a4003040511480c1018070821350007242c2400e01504001c0440d0029980c10290300000f00309800c0f203c002000e8030f0080080d0b8220002e010b02c90034241c64040400d034025082150441c0c421581c250301410107a550301d020342e0694415155000c40950071140c203030040c20440801030f030400d5030b8906440c02d20340100090f02c00290f010094401c58101401c2100c29a4081620103200d0380c07505200100c2c08104031402001c44e80c0c183d070b20f142c5805011070303102110300030b810489405001e01801e0000300900440c2d004144d912030601014110300fa422044407110b41200c0c010016080802001608031000c1c469a0f88118001c180051109240c010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 490264163 1250 490262913 490262933
    0x1504061b0203030718080a0f0602040f14030c0603010b0a182123100e031b0d0f0203030408031302150d1a060f160c0e04080406170108070b16 62
    0x10340c0010703007001c814010060340c020000baa40120f0082c3d2620f0140c00d00c03480380d850303800c5030000500d0a65502c038990108585074050301c0040070015601d10185645a07409010341c507030250800d10074055051120000d2900c031080c2c0e4140e8800c1c015980c2400242c80041d40d00d44642941280300c00105903001a5034400907800c8440c0b13042140142c0004240707481e1250091f1542c040072401c03075006031003960360b4110004610300b6034810344030301290405002c105181523201c0c940032180e1440400d001c0103c480340005110700260340035901c1c0d50b105441414101c1e100c1c04141d40050007542c080001c00c144074103101d0380300c2126000901061411185c20282102c0342e01160400403460780740c0281140420340c0e00c400700c40220050720a1407500c5042402807245108112803a103112003001d00603000d00031005c1200e0301811070460a6205c0381490b04001d8010f0300030f44202c10004c0c4007580807503d00d400d001d0866040320151402000c03900e0520345802010740000c03030341c3d00f41075002c0c02c4101c0100b075194403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 490265413 1250 490264163 490264211
    0x302090a0608100e010e011e0c0e091305100204030b060405090c1207060207170703031b05010f06050f0f030a0b06010e09010e0f060604030b1303260a0e070503150406 73
    0xf0000710b4000e058586030075184141d4a100e8103915004041d01c080040b295150880c1c40079007000201c100c45a00c09a400e92000c00809401c50610410024001c0414481c2d00c0710340d000d0f904460b582e4038003649417030507480740d400001c2807010500c02003219401c25400603074000c080001a030304403910800c04905c004804800c00403440e44428030030819290107100e40009000b10720030014155036455034240c0c0d035041e244001010071041c00480b000c2c045000c40c1d03181307085510030700902091205040303c1c030140140d401028443c8401102c1403629241000200311f01c0e48018014000f0380c7e0990710f480d261000e0041020f81800603026a09134159200da040314040d000c0004c2442e62800d02448440c54010002c00307890088004210a00c00710b0340b1540960361004504c900c61008031003910302100d121400041c1181480c00700b12100c0c1c004540e40c900f07544108407040040003003d046c524103030341c1c0b003550b44100d0341c060b08000090b885103200540c0d0103034054040c0d900030402152812242000458040d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 490266663 1250 490265413 490265443
    0x120908060f1021120e0607060c35040203241b0f040905040206090603040303050702010e07050a0302060d11070f060b030c0901060c14070902071703100302090a0608 72
    0x1070401201d040c00d10080c0c8040c1040500301c0414031094040d0301c406458684014040400d10740320240c0b810b00c203071703200c0c2d0300c0c1c05c40902455105c1c0f0b0103103404405000e00f000034901144022405100e0444041d00540d10516200b426800d900ea81c062003902c0f03540c0c040c01c141d0b01400749000318aa1001c0302c1b00142d028840d464410005480d001006106450801e413030042c40450030090908590710b40819141a41c40e014400201a2210b10009603148034101c100e5030020070100801c0107260301940610b10808068000344652462200055242c903140c1c00b990ba88112503402c14400f600304000034010700356581d01d0004840c20000c141000c65048000112141c803400030b042c0b82041614001e40d42e0345501079000b0714a090340d00d0000ba040900501903034080240490408060003016410400e0900903003081e078201680f00c0303907a000a948102002e0b5030b03960440440600300b1840008513481403400c5594000310714210340c01c2190344a4040c03d019a01622030b0700106801505000003000a0901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 490267913 1250 490266663 490266691
    0xf01031524090b040303080609071704030e03011d070b0a030b041503031710120602120103030207060e0a081507051b1e010c0801061b06140906012112090806 69
    0x6500141a6442e5030020f11580409110800000750441d41c4a5088101200c01038902d40c1c40301011140e180d840c0084900e00f030744113800e00042c940c204400d62443c81044d0028400c0403480740c0310612400c00300f460840140c0c018141084220b003500b0142607815000d150125035001800e0004069846205001c0500402c24404008041c3c114043e080f0250b000c407403811052610000c0c00700050564480d0b1540d181191490b0f604002c0340790304945400c0b0314901c85800d0b9507140d0074000c2d501c1c081c6005100c041440d080902580d4a840004001120307142c40040825001618207a480040003800010500c00c003402010344452a11100203d90b102c094010441e40340c00c07861090b244046105005030340d034986410b43c800d03a42e120500c2d90656049081410107200c15a103051584100100d002e482540340800c481c8a80344d807100b1981c0a801048100c660b00d989851076901d2400d5044482440d01c0c84450300d0307100103480441100100502c3e400c04094041d6107103406801d02000f101c0701042c5001e5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 490269163 1250 490267913 490267979
    0xf0609010c0215010303050d02072d0201020d0c05030d1113030614060109080a02220e10050a0b01021f110a020610140d020607080c121201050405060f010315 69
    0x4100800d030100c3d45003d0a00b0081e5240d5180a8003600c11011644103454000400c1018000f80810200c0000310b51040105440b14030180508031410301740c0c04034014041c24000f030b00c020b84a08061036540380c01c0005186010b080e80c404000800c894030142c405c1135030510501c13600d4820102518001e40c002c0101050004028074100c40d82c0e07800a00603818081041420b11040c580043d410311180e50507034205030084420032600c103d41400c1070070604124103000e0600a0000041114525169000014001c035202c0220301c106851005003030764010390042913030100e840540e40715044030301850300340040e0911010100101990241002d034000d42c1c030003400d01c03031062001c1100c41e00030100030710010040d1035058000703514940d442c04042c3c032603c40400c840041c44192803c4030b1001d403064084a0710b04019000e003010030b8020050343d09109a83c0c0c00000744504081c081d040c40307004010025001e039038641c4015001007041032654400c0d0021034901013180708411100c01503c0030080301c54181148 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 490270413 1250 490269163 490269167
    0x2408010e07122a050a180e0103110d02040c0306060201201204150c0f021c050a050708091305010e0f060d0b130b1005040608010204080307080f120a02250201020606010e01020f0609010c 81
    0x1100c26001070418903103c80030408200356003407c5042d01c0d8811180108000003100103140301242c020041e5102e80703001c110140280e015449501180c410390000d002801c08400701e181001c80308440d558540783e0400410041c0c020a4891940c041c1c03184a071104461140851a0115071040c1d04101c040b511001e00340046c04c2d01002002c80a07260319003004070380489850018814002c180d071a0040c040c000c1985070802c200751003a030741070035006000340801e018030f0b6004101404082c4241d022900b1038030042010103400807080c6110b03900260002404800039604d441c03990f01e00404103201c001c0c640e000b000004021119080c05034100074010840fa034100303c1080210386607640300302d00d503070300c100001c200711b01020094401d80364021041030f441d000c0d403420143ea11710424265161800d440802c100302c6121550181c105c100d030795000c0c0c0e2030300581124224221082110040d000d40c0c80000042c08540c4511400e18020406105030303001610700012003454150203454070000c40c0d466480e6030851035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 490271663 1250 490270413 490270427
    0x203010f030b0c030403091505040b120109050903190f0e04050a050403110d02060c090402190f0e01050301060512190e0a0219030305071502042408010e07122a050a 72
    0x701003c08094a5418241c0d8090102d00d4640b055240005201d070649506a0144050f50014030f100c2c040c05031f5550100000103038003c402d0240d03ca03060f19040c04121100c03070000036a04c6800102c514201500d100c03040548001076042801c1041080c9480007409030b84980c040c03280181c042d1400810241807501d800381061034504501c000d55800307000078540c515800159aa04a00c81104050b81c0ea003071640440c0280c403900d03e45202d1100354400980203140c1c0607150002d120a01d6407400200d804035001151540b0007071241c41c00103403050081a080b110694181e80d08001c0380800e905c00818031814601c00c1d03d41d40d03e85081c064100c0d000400540c1400352500c2c05808100f2a8100c0e401c1c11607034003800034080e0301c1c40507001301d2101000e0031b0b101c00b1507070445000e8501c0040c1000074802ca800c40d980345002c02c144110028401000000e4203104070749003075000300c0990f100c02820a008840360700017446920b21020460040c80f0301c01038103400142c0f41e0500440e06903202d035502e81c400c0001230b002d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 490272913 1250 490271663 490271671
    0x10f021902070b0c0a03050f070c0303110f0a12031805010609060f080703030c080c0708161e05060a0c05120412120e0f060306010c1401050108100e0a14100203010f030b 74
    0x360f00c2c00c03c542802c28001150410304160f050420607101e22511210382464018001c4c01805455186004400d05401403880311055003007204840c640b4480c83c82c01038892003180d000914015248641e0700e040f5001c0c0d006243d40b070616090b4071000c0d1415456003402e442043e4480600b1a03502c48080c0900d56079a0404401703499a80c00030442c8a203150f900500d00400b06401030722250020580760b8650700140100710080000d401210040481c0c1944020460a02e200d10701c0000c4502e640d542c18111000341c000e04a401c01031465080010416081c2e07481400300c0c0044509000383c1300441ca421a4101c060800741089002c1c1030150342003403508031003048070034040900f4440c1c07444012030a03603104100d10841040582e0595203d4036000d0058580c0d01600794003d100e0381d50740128010403901503000d24120307024601140d03180c46002e00d03e501100c130624205015600801701040208401003007040034200350200701d5540744505c078000c8040780c00c2a04069405a40704d402082440704620f00c860708 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 490274163 1250 490272913 490272929
    0xb041b050a0509130c090204061709060403023c03030106020c0603150f131803080a0c0215090c120c0301051605090d02031f14010e100314010f02190207 67
    0x100e050100003500580000d1840e514131942d00348800c200a90403a40c800240050002035440b162240750141c0080c1848001c841914407100018001c1c60000607002d00850f01900500540100407040100c0c80a0a0300515601208222103006180e1100200035903000c003000655225414507400905010b6240c4401d071280506005100c642e105802000c2942e500c21190050700d8180a80403c000b0384604ca242c9920314500101c1403007018050624400c968420741c0c0d00d680035540c0406040480710340e0469400103a01c80c040307215200b406415401d4105001000712020004c4403800206c2034012a00d0014032604100180d0001e42400d019050f082100a81d070011104a030110050040c060114268401d240b140c40b0074066403800d0000c3c2082c01070100803048119400295107001d0500410418000380c28400001140406154000d0090b503e11040244075403440c1c880100300e54500038085070f1550784501818813004240300416280080f06100e07001045a80d50103420300c0714a1384030300030f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 490275413 1250 490274163 490274179
    0x110d0c0507090b15030c07061413060b0604080a0332030c09010c0501020d0b090c0309031207090f0611010e01151215021b0d030c0206040f0201020a0b041b05 69
    0x51020903181c0a55100030000160103035401c0004031407400031002803150000000a02180c1c1c0f007031000411200c1c4c01039409222103520003a8400072510225500750074501c441c0000c0000683c640c1081c00040b80080030a800d268642d0b4809081c011000000c0700800c4400c801c03204143c1c06800003c0407505a000007691078074030400050b00c0ca01c4020181012140006580011a03010300d00484034640c02200854841c919018580010800e4520b0140f0809900002440941c9244200c0e8414401c580186040010192100c030b2841b002800e4901400849174002c24841e0b0410441c800424107a500c00040f02e0761300c0500c40c21a40388060120069050003041008650611460b000b295400040d04c1000d0b14103050000e10b06002041482c20180009005180010140d010300c004c03a0b0290f050b0388140d0074110307060b0101d52000200501503042200085c000c641d0840030308032920b0060040d00e001081c1a541c042e00702c8000c403001c59111902d4694000010304000c8640c0c0a40f000f520101c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 490276663 1250 490275413 490275437
    0x3030f070b1303090e060612010b090411030118020c030708070809040f140610020327010306121709011704050a0302060709260a020a060503010312140910140a110d 72
    0xd02c84d840500a8203440c140803c04511152180b60031a10345048a00c2030110a5840b15035804c295880b2141da24441ca0a04000c901e00e120100c00b100c0c129000c100500ba41600e00180c0702c0065040803520b106e990205029080104152000820503e071103002d249666004000400044a034800b2020442510b0715030903982c900c1040f0301c141d805c0a0101c80081080000100403465440350b081159180d185199a0024109100700c4108681900b62000d1001c55101c0c5c40e15130017000f0303142c0040c0c40340980030301000d152940b030b4009103200ca0061400c440a084940070701400b2443c240d50480791940300c0c040038801e06506004554201c141450300d0728406191548400414054800500c2d80018101da4001105030030807003400d80980c0507000c110742503654140540660001d210985031004a0092088040c1c0314000c11449070109140076420040d2000c01e11040802d1603004109000380d45203001c05030014840503000791901651036844c2c0b00a000300a42c14000107509100500103003420340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 490277913 1250 490276663 490276667
    0xc1e0915050706140112021e0307030804030b01080d0906030903030213240912061a03120304051b100804051f0209011e05030f040305071b060806030c0609010e0f03030f070b1303 78
    0x10f86c1190111402c68120007003849901111a541d08800c0d41407045c80c1001007003100e40406042180d007e64544103041c0c1e07076105030307580700d170001d440030000146501401d00101e802580300007500d6000c1d14006080c40c03030440d00c0040c4800c1c1900f001140c4010a0201d0108801b92104442c1d0407900303103000350b000c40c6804580401c249100f103008102c1c0c0d03250f281d500603418100b400342050513002003c540d8003104000102c01e503a80203841c155401e0041940c0b5259581107070503010050301001d003804a00003110b0304215500440500700300d84a00428280103460785c1901a64121a214404016500c2c143c0700300140403542c6035041514035500782d00904080c1c0790032030152030348030b100c0c0705610300240d550389004ca406124401e00107101041b604480016502c0c050702c03c80c1907880076107481c881a29002c041540da003c080228560107001000441c0316940f0070410001c0c820805408458010341540c000b0b415900100807940071508007060b41c41c184031400c0c2c5000e4100a41c50034110307041d0345680780 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 490279163 1250 490277913 490277939
    0xc0903140d0203030c1b0607271206020304060b03100b13090209060f01270501090605120c09030c0607151d0a0204021b03070609020f03010c1e09150507061401 70
    0x3508101202c0400c20b407404540e1b106c5100e07885020781c0c0c1a1903180c0340055018044051101500842d010294803107440500358008035800e84400030100d901c90b51650395084007a44c0010001c0b41d910781c89158100c5180c0302008600e0248002100c08a12821540c0c113004040d0581890920190304184600d40582c5a542585400203011744041c401c542d061001078440040d03c680021308039868003110080400c10001e840103407042641d4010382c182d82d5200445aa020300300441e031f0340300480808540d5002005004008001010381600c0700e03000d4400005529422021096541942041d010102211207100e15880e100b4118807100000c1f21200009544550f035500003401180e00182a1000c0c1000c0c03060b400e2400c05032000c89a5500c10f40c500a00580b854050480c001d07803c800401025140c10300481e01c0e420b520740e0307440040c10030703161a412103402c45010040034007080703a80c04140c54020401c0104200c0e80c9450315035958000340740180c111241c420003000100e04070f130300511124100c00c1d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 490280413 1250 490279163 490279171
    0x609020d0b0f0a0b0927060403050d0605040908090d14030c03071e0312050702160306090501110324120102040803360603071e09030203060c030105010806060d06090c0903140d020303 80
    0x440c0d42c02041c1c600700c1003050000110200c6c1da1085004000030540d02100600310010140d0040c0512075442c000c0c44180c603244100105141c100340003a10260a201d0b20300051607001c3d00b051182c0840d40907041e030542d8804c1c21489030b0754000040420500519410041d07501c80036040d0b00501229945004045600f01d0305074a0b0300302c1d120008114400d01c200b1106045078056401064415503d00d030140042140003011246ca5081101d9140b50180c101c01352071203050070744d00e05100300d060300d003400b02d0801c039402c11075030702010b90301981181e50024409880135002480c01103594003002c04115254101d441c0501e0715620950000203d4840c00f4460f840a0740e00c140d0309141c81740c40d03001c01942e42c6494000500242480024041c0030140d100108104490090301a1605c036244c96a801c06944024041d072b5011130f85c000c0200f00c66040030030041010314688034001682c80d03290f25140b8290b444602c01c1d80c00040012106100740540c269012801d1044c0c00000d20f400501d999002c0c0d00d03408010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 490281663 1250 490280413 490280431
    0xb03060903040e150303040b0a030c0f0e10170c03040c0b0a14090d050d12060603021305150c0a1b08061501030b0d1e110303160f0609020d0b0f0a0b09 66
    0x10340402c4c000c032198001000b0044000303080d00d4580781c9402d10b640141e0845901c2d01c000038100917504100038000e000342064480c450b40e80540c010b0784401400451010a800202000240540001a4900108103a00607030100d003005550307051030306040002031950b4010560103281041088070884d0006e0f0300c014040e840034460b58a811000c80050400c407808400500f56004030382c6186082544188515050030003c2020081c1d55101c0e00304600b240109a0070490714400240181b1a51400f044642c0c0c084104130009460510352401550070840200d900301c501011001c04211040084400d0b04007511921005100918001d074072071110852081150341410b90386d1001c1501510b41201c80c1044a0708111818410744541c2d03c590381c0c01c84002c0c030076170f03140c040c04002d01c0403890007000310740702c001204006452240d01600d400200040d50704048500560710b07201c1500584559412844080c007522010200b860110294400c0f028014400707442103140c1800b41526070384103c252600500c6907 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 490282913 1250 490281663 490281689
    0xc020f0a0201120618090501050c0c03040306050c270a09090201080a0c1b050304151b0b06190603050601020d050c0d0e0a0911030912040b09060d060b1c0b0306090304 73
    0x305450f20010032594101c3c9441c44011100c0340c8890245030030040700c280c810310013080107660300031148806000d0f1007000701c01c0390010481000407403e29084640c02040d11442d451a1130000c0c1508110120380d000640c041c0c0b8503024074040e8505d03205c1507000c001d01c12000188010600c60340000d00c2000010410305001f540c581d00c1c1d80896101b10001881500b480e10003002031901414641e544c0d4005100b0051100072680d07a070f81d840c3d07116803003001c03166143c825001000d004a41c3e038481d100314000d145039007104000e08030b80c1030700365064603000041c00b141d140007400d414540c00080c02e00103421044400c2c40401c01c46154045000251940042014034000300c500e14054000b895410b025481090b556003021a0040c900e5555001180540b41450807100042240640e96115000368410030100240070300c900025810b00d60010054110340d42070000305030380c5074443c0c41400d8001d0007901c400d04030074001d1000c042c0298822241c00040440040805240450b0050364a20031805125844150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 490284163 1250 490282913 490282937
    0x620030f0412050718060f170307081e0d02070b1308041427010509090604030f08070201020c0d0905010e0d0c030201050c0f0d0f1e080a150305010504150c020f0a0201 73
    0x200f0301036a03016120b25030031700702c421000103000000b41034240280d60303e1110788200001d04803048426aa014440040a1801c2c0481921070102d01e422000f440001d8661307560301c0720158a203d5006118283d0000401a124049800d0400e00024020403852645040d03042000100d1804002d880841d2080c402c1d00e036080010318040303650500443c012071130f0302c41000c133400c0072051480c0900f07050b22000c0c0c60900107640c40041c240c2e91240b040d60b000e40410303d07010082e016207100e4200d02d0342c4070000340005072412075144000c1303185c5044401c042c400244090000d02c040d40e80200303540700040007200c0888046030691202c14406c4030f540310090500c04002000004000140404140525054142c2d9041005420060425900011641c0008500c0c0c80b82c03c0e0005482a003000031010a541c4995171903032140c3d25000101031500d00034045a49030000040010424041c541c4150b21034260241c005494980120a489010721920150740100c03030f01010078100000c10f0a00250246000c01009507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 490285413 1250 490284163 490284173
    0x230a12090c0306390e01020a0305090405070c0b07080906060a0315090c080601030803061306080c0d05011d010204150903080d11090904122307030c06150620030f0412 73
    0x242c014940131044100014001c00501c01c0c00a200d40801e261142c1050f00038100c01241c8407042544010040b0380c040c0318a40e400d091590000398400c3d0507040074101c951480c5c80358104c04100700c0d646e00c00600c2c417808001408030144500343e044203054070500b08581c20761b620329103400d080412281c4035a41d40d80c1840d042c000000389a10040450000351041541c50f820700380782c590300c110f03000c038018106044181c0c6c1d81c600c24401c0c40700700c46054028058400c1c41d9000c00c0142d00e0141d4094402c0e44d02d0b1812020014912040c03800011100c400041c2d54a00d070078003848135206135030642d8080c0200320781d0800c00700d485102250001e035074250300000c3c40d400901214141e07006641a440d04003014030100401c0115850944144907983e4440d0300c240f14884040c60740d020b074140c6c0303a041240800e1291000107030180301c13034001c00d51041901080c1e2404c801c06403400292160300003800140c0a00345100041113680070003110ba00468003461400746c41c448001783c1ca20136881a444865407181490041c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 490286663 1250 490285413 490285451
    0xa06050603160b04090c080606030a05060429150a0e060f0706020d060302090906070915021504110a0914060f06090a06050d0f0504170307230a12090c0306 68
    0x100155080e45000b0341c540b186a440c0e90003900034441118501400b0641581c0248483d610401005082d20b21b59030320751080c600a41805007119801a4503514510701c1c0c8503c0007020300d030a510702620799910110003401c1050f50074030350b0100280f88004000359124550310030301d200340400341982d007190380e40040b901c0041d00c1d110f1400d024001510106a00c03103d01c04680051048a000300d40b00d9559842c0c0b25605a1141070503103440000c6108001d00304030310800101c0411000f041c60068030f8483d2000080084031560846085400d03c034048800012854100c400c80050031410001300b2013440f500301d00c1e202d0081c0151121341300f100d02341d00a4045036500e2046881121001e802056541da844502070b1007a0451030000010600f040050151100d551090340c1c45540c00844025042282805540c0550f2024210034200480e2280b000e000075580503607001c00c0c911310700e415a59001c01c04130050500407140c06201110b400c104290001c00c40020500e07083d03d40003a00010500c10b000000550340d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 490287769 1106 490286663 490286683
    0x312090d080403180b0c010902120f070308030a24180b0a0b090a0803030f090d08070e090a020d0e1e010c1205220605040302010b060a020a06050603 65
    0x4a482071109a04001c2410540003425846070505c42031a8800340d10740181d41c0d143d404060841c140840c4001c2d9544014010301040c03c050f841031925003030313a0711000c0c3c110400440450f42c50f0500754444010684002414900c100d2480f0461022813203c0c896060884402040c1c0c02e0300c40c0a0740180044d02000400411040c1d0400f405080f181d001001c0300d6800014022001c114810104000c2d070003110712034414003080c5424619180b0700500ba50b014820002174800b403140080d007141866820060844500d11315030781d50070040009000d84041c0311505400c00607081c1c0d501e4404a400a08a442030007801042401802c81900b6508906500000030780501c24803072020545d0b50000360405051140003814070550403525495929041c800e65100e1b9440d400e1004140d024400e82910003000d503003040c10040c0901010751600207258028008946035400103030a0381d000e1201410ba = true := by decide +kernel

theorem cover : BRFrame.Cov 490107913 490287769 := by
  have h0 := BRFrame.cov_init 490107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 490107913 ≤ n) (h2 : n < 490287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
