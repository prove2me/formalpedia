-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3307
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:16:22.358826+00:00
-- url     : https://prove2.me/submissions/39007251-c3b1-47e0-b7f8-034511c9fdfc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 594604316 ≤ n < 594784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 594605566 1250 594604316 594604333
    0x100504050717071505160f0501050603160f060302091504140a121a0702010b060d02041406070f061104090516020d03060e042d11040506310b030f 64
    0x2c0c80300e0122030340d844800b9001851803e48102c11910441900702c080c402e000c26074208401d0401140f2244e240c00c80c24540c045905420094002c1c601504d03018003901405800c0108a4601c002d000d04440384031180ca000c00d454181c0440003500440301c03507a8000c01d500e460b000d480302c903607001d0700240c5200414000c1d05070039102007003e44681030307010038120a80c001080000c20304441c81c1401c1890103100700c0c040740c2c1d142078049004150303403981d040e8008804110303400781c072081b0ba014101365070118288101150005040200900800c0340040020890004d1800000c01d00c0e00003611200c0c0d00b02180b414292140c1712541501c07800c075240c540805000c0512143d407a81081242000015801c0411906d4142541c03400380c0d100041001d00780300c10030f0703000c001407202a0400320100c01002038010320400c51450080200704040171400e1041c3d042c2404120b07c0d190a03440a0002c0810030603040c5845801c05074085100595407100908a5503075400ea43c2d503803018003400150403a420007600385235 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 594606816 1250 594605566 594605579
    0xb010b09100e100804080405060a0e09010801090f060b060708040905070e04020a09030b0405070b04121a1023040509010b030616080106111609020703020d0206040b181005040507 78
    0x400e036041d5800304100c0304902000309034680c4008260300120710b10300320400303540e541800c110300d206035841260005d60000700b601d252944510403400d40c0a08403815182660780340b205c5800e943c0322050280852900746004400160254042c2c41c0717043c0301610090404545441e00021a045680801111900e072401c015590340d00009104c04942c04980450400020070300040000980c0c0c000101a05030b00c0e030210b03081c80810400c00c070041404000b115661a2945010240b10381c151100300c5240f81859411006941c52062691207100c1c12840700d00090314021001000b01806200e01409c0e070044a10000341d130f115802000d102c1d0088130004a0410681c606042c508071005000503000e0f400420302103011648203810904440284c500b0100300c10203211481d08140400240090000030054001a080700e12303000341c40031500a40968000d00c0603643d043e61902c200312001000000684000740c608081071a084001c0f00b801001c8451030014411003408403035050301c041d907070741d803003d8030070000c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 594608066 1250 594606816 594606829
    0xc0e06040c03050103080d0f1104080d020d090e0708150406082109060901032403110a090b03120f0c071206060605070b07031d060a060f0803092404030b010b09 70
    0x340750481c60200465803450710782c050540140c20b41c0d0341b04a61121008498901d55070041c82c404c000080381c0c0303603440c0c2c4da405050742d0b1500301521040160082401c0c030080700d401590f444e412607251500c0824903a45102007128807030002840d0008901c1c480b00c07424070680b034921412003e46034000084c0041d100c0646d1100c60071000d40c03a0030080840030854843d454035038000703941044100b070070f01003142e20110249046c0124003a007220748400c80000000b00b808046a1152004641519440c0e0760b20b8440e19a0002c1c2c40c5400d51290f0140e012900203403650755020018a1042c28116986041102c603102050406c05980d00a451200030319866000380030480c401ca07401805c960a00da840e088469850100400d0020610707024999102d048040480580c1c08000f64a134040d0b00b964014a00141d00c1c1004114502560004c603007990f0000c201d42c0070000407180c007283c00804018440395425aa0701c0c0d901d01404604410000520000000407030190b044c5001e045100145500c481c41c0b2400d2200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 594609316 1250 594608066 594608081
    0xc03010f090302100c3c1b0212070f0b031b0403051002341103010501050102030d09110301020c0714060f0d09051e0f0708060408250c0e0604 62
    0x400c58074110000d00042d40004018080380711800010400c420b45c0c0605943c2c8401440982208051104c01041c413211982c2d044920442c40c441601d0700c961322801c08484a02804012001422100ca800009458144120b81c080745c955012a613425440c0c060504520410354400d0580000101c24000010502081500681e807078402c0b05081510f03503100d207646e690b8415040034000d41c1c001401050550304c0684603100d8400d8100034050300c9244941c11902800000c41551408541010b143d081e10341030080324100e5038140c2c0110304003d2400f4a0b04002c0030030440c11101907a4104178075081e51001c1c009007111001800c06049140d142c070818956080301620824806c2e00308101c5030808042010941d800b0344c83c070303500004914a0340c0c6401031030b054a44091080714400760701014110040018462010921482910480d80d520105561303603003030541d001000c0a10512440501d40c405640c8004014903600741c001421178070b1388031121400b5558202d4a504043d100070001c05e410319004500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 594610566 1250 594609316 594609341
    0x2004030b2e0806090604050d050a0201150303090518161b350c071503021c0509100905030a0c0201140c030334120209060d020405032107030c02120f0c0301 68
    0x85e1615003030341c0c0c860f21264060a0034045c4a408224020614403d50103141c5103544550b42000e17003522403c01400440b0184100c903c60b4403001d810036807661841c0c4007140110008070302030841a000d43d40a50f00040380080f041c1e40c00c200803a0940100e0000c014120380e020b0326400703c05071404c41d0b1140300480805401903421060040003055443c030f40c00180482104c9a001b82c0e243c041a002c5002c9010f44200c28020041c071102e44941c000e0140b050741b00c14000e8201400300d0391554640b03d4408251244000082d081e03400c103000742c1e03d585015035284000e01d8814500503000c1d10000c0c036a03c495070043d0686003c603520110070000054403119a101080f40c0740001c4185c0e0464601ca5131154803800f40c00b0004120404004002c402460b40545000100040116440394141c80340540250414030505100e071099081c59140d40da0341c1071610b0f958071402c030101c61030240251400e03904080503400490b0441e48096664000403020301105c110740014002500d203001c58202010b003500c0d203e40e03548 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 594611816 1250 594610566 594610573
    0x525050d0e15090115080705010807090e0a0c020706022a0f03060405030c10091101031505060f0702150405061b150a0902040b120307140304150906032004030b2e080609 74
    0xc2c010446c5c00500b01045400911b4640c2280d501c5260031070b002c0502c0c0d444640041003000034081c5001041e000784040c04965400c49884075a81c0808aa81c4c94030f03920050398040806280010010700c10000902c8828041c1041c10070b15100804a483c080c42202d055466800102e03401c2d040c1c040a05c01c1d00010911008248004925070326029040c01c84000014107041e039800891011010303228074070008200040c440e6480c1c50003548040025803150300101c0c45040364103024001900c071141503c094843c0500154203001448806a104d1010881c070080103200b1800d08031100c14140750308031b00c509030100010a1442040c4184005d85820f405414410404525103400003400042031340d51241d003007c0b040800400c034080c01c41c15442660000200003100300c103800c841981124041c012104540e50800c003800343d81c904440ca00c16001c0f1485454a000c000401c0801c1c0007040540d000ae1520104205010801103901903000710b20150380d0914030480e000304103c160600005a100c02e400016 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 594613066 1250 594611816 594611819
    0x3130902090a050405090a0203160501030f050108060417040e0a020403060516350702070602100b0d021002012c0706210c050c010606050d0525050d0e15090115 70
    0x100b9002c0140038541c012581c950001d401c5c0d071800c2141c0c030341560b0003900755010b10280100e100303900503c50144c5808a400c0000d8521001000d12a441c100c0c1e0b840400b50006031030707917680c07104403240c440d403489e076050418070020031f0508420140c180a00c21500700140d8481c0366140050a6643c01803075130001c4c0314405d000300900e40c1c21800310502c0d17070309209155040140d04100d04151750717101c02d81141c011500404100c42c0503000036142c0c003030325415003c544a0076400383d800e2055600c643c80058108450461000041c01e200301e1865185e02c40380000304441150130020a02c400b0219024046401d41d4148410101028840c0501424403858102201007840c03401156950f12006542403042c0d540c0b081150840c49681a82c2079100e040b0020310100b95504001001034000c1020000301d1403a240120b030b81981440166049a883d000e2a58124000c010050702c03039030043c034442c1851a0311055045000602440f82903013444103458105a45d041400001e800c48001800000c0e00b81b1a1600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 594614316 1250 594613066 594613069
    0x8041406090a0209060d05030309030912070f0b0d0b190e070311030f0604090b1f14130c020f0109082a100915090b06011404060912021f020313090209 66
    0x82c500903040d01a10f882d401516054041250200c01b02000f0301680004024040780311000b2009191000045801c9900d500c0600180c030748600700d034401c0141c44410307804108240d003d41c5025014940301c1f0440000c0c25020100407582c010f200d038001c4e84203c182d0074030500110300303074552560300070340b0a240c108088105c1000d40c0c0603d21026008007801c0044900082c05030340e1715048103030000d611200d0824242004a00004d01c04040c074103443c0705040708500402c03ca000519030100c0480000d001c40701c00200e2128140c0104000d1810504500400d0900030080300b0900580094911402c201c66540c110100401d80c0340558060307581c0811075a03140380b004851700003050200c4c041d8001c40011010cc9514200305104043c2c0043c580340e500300000e48003400274501900303100703901c2a2603101c24100c000b40607610502c90f0b40901c1003c1604d4030701c207002007580301e03481441042c80075210390300075151103101200c4103502104e40742c0181e02c00a81c9003031207504008010b00401000b0002c0d41420000d50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 594615566 1250 594614316 594614323
    0x60c041404020c0c040603081c110a0c050106030212100f0e15070522090f0b010822050a0506010611010e030a0c03030906140106030b0a03120e010504150804140609 72
    0x844480c407031500840c81c000302102c01e100c0c211200e54018010001c80d40da07481d124602d0380184010b42c1c1c0801c1403140061303400d212030141549068001c4d601c64a80504c0e0754090300c0780f6550941c142c5e210b6594110110041c5c8501452001c0d007801c00d0010440d40814000030400d69502140070800c00b400c1c510000412200041e2a03810420800c080701d002c0d0361039190884550169101500e000d1207007269403001e1004401c407020940340030a0042c01030f07154500d80c6006592582c400d480c000b5081200080c5c42e042c1d030454400d40744030301c0341c82c2131380700d817203d480340c9241450a500a5419811060041285a07000700e03001400e44400b20003800300b00a0004900c0c0c0741d014030800d0105020549641d04205403190b48a8040d403544505c003088815030301c0b6207905481c0802d00440340440d1034484000168600582c0d140e0869034842d00151040b103c040c000c0711910700c0b03403d010703044c014180f02c0403c0f1060b403011030749840d01c0656500092442c103800d019070703144209146002103030091004e11101c1c09011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 594616816 1250 594615566 594615599
    0x307030b04140307060c0801080102120406020f04030f080310050a080a320601090b011403010306090618030305040c0f080c280807050a05121f02090409080c060c04 72
    0x422011403556590030300c500c81d05607848007030500e40800154001040036582c13010704000754540c0d40780866070321400340714200d1003008a4010b422148070006400100960020140e011824054a0426a0307035540d000f84444d8501044400013000710422924501140c4d13440001c11301214110001c1b03240c46212619560700321301c043c00c203041c11070780c115030005081b100c00d0b401c021a000c242851000c20340035640740d80d004c1c00707051a4281860390580c0298814541d0141c480e80e4012280d207564a1651000c0080c442c840084910907240c03413250424401351000d9a064a000c0d842c00701c1e807460540345c01107100c100780c0c00640102942c2002403110450000b00300382d2076203040e2201d088012140e509100003903000300c1c100d1410ba904020200d0585008604102216001d40b0260070007134903041003108104001e002e0100c9644205221010740c1060b5140402190807240b00614000c08400410240c4201d400c0a076403420000820f180644c0007003010561100000c003205087c503090580c14901c0309240b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 594618066 1250 594616816 594616823
    0x207180b0102011b021c18050d0c0b07140105010b120106081503010203011707050301140f0a090803070c020319050c060a110313081209030a20101e0e030703 69
    0x1510600c0803a64002d40c4801049030340c1c3d60904042d4030021030000c2d5140e00200880100307034050720515040a020b00c25a9905011201ca04445141024240b11110086000569441030443e03400600f082c0040c0050002c140218005414011108001c0e425608185c4c402d1407010000c00512440d821015142419160300d4508030046031100700010365050945c449166140d440007000181d0315820b40380d482c00c6105a10140d072140c0340c1ea542090b0807543c1200340030000e41540d000140c0ba00b0a001c002650101c0150b174009a000016161802c440d00104d40b03034400710b05645602410740c542081000107000070303d00000181d0b16995101900e031020804528007a03280401c1800a0b03500a205d52402c80043c2005c807030701c80307508404504d00e06001344144111070041540100ea030583c5001210302d05140900140440012980e60be0300003680b801d20b0340480380ca80b8a0201e07443e5591150000c51743c1582d40d0340c0110703010240015951013140741148085c80100314040e01c03140c4000c500907049a40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 594619316 1250 594618066 594618071
    0x1b060d0203090c040c1101061d010303031d011e05010e090a030503091f0914030708160606050913020a14090606030903070b01030f0507090203012301030609111207020718 75
    0x702c5807040ba1030800e801044035881402e11500d9401258004c001c546803003102030003440019a10400d080c40c003c82e04d04011141442000107102103030107a001400c0366a50742883c0c05051101704070700c500710b965038030108001d20001c8901100c5914203025641c09007400c6003019009003480e05140d0f40d581c040d42402001c0c403001100255044405008003818401540c0c045c20006040302441402040c0e42c95084403c1030041c035490a2582000041e140d50b01d030701012207850040c094031040d0380c01480c034078101c0d001900e60788007140b6521092442805928800c2603400c5905d194810040f021500d50010802c00901c2182882555540000240c21020075079010380c2ea901c1e04200c66045114508024103c2602500001304110407078150711156409101560000d607118001d00040c0d2100b0b12400f081507120406000b01f07002656402c0e401c811050400242082d91030040d0300507181013880308209c1c0c20303000c00c02c503580d80f011060290b0b001c8000e2000e00303481400d2407a42044082202480000c3e42d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 594620566 1250 594619316 594619321
    0x30302010f0e1b03100e01050105030106120203210f0d0f0605030c0d080304080f120403021207031707121820010203030c0f0d050a0e100614060a140406111b060d0203 73
    0x303d05206001071171800b80401d11010300e00900f054040e003820300c102070082d0710300103001841072070302d09181390f0859005010784819a43c612000070340c01092620181c501004003d100d400030038180050100447ea0701000c0b41c258240400f0740111022644024029080040640990740e258880a1070040d07010244580342d80301c07420300048038001c54811401c0201d000807144103ca924458107403045200c0d0f07086559022204240d07807554002c00800030042020040b42c801c031001e0a0105603030151080c5441041141c044250f00142c804240420710902d5865070318000303005a0386900320b0402c000c50030890010f820000001d42e40d110003000c42c64088400300b500c08051403000100c0e00344540c041c41c14030003030919030700c04030041828001502861080c03102c0d280344040303540504012030701022a595080c1e040c81c410303c28075502c5481550300b041400791107011083c8031300000e040074250035595504c40ca84403214035445c2901d010880c0000c9200a1900212540d58030b00301c41a00c1c0c000c080268894 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 594621816 1250 594620566 594620569
    0x5040b0906150a0e27100302090105060a0302070c06030c0f140d0b01020a050d05030f0f040f060c0504030f080403020301060e0f0c07061803120b010509130207030c050d09030302010f0e1b 82
    0x200480840340c0d05c0041c0840841060b140e011420030074001c514401e4205d500d82d107188110042152200942012a2500401032403901c0d030b0282200800794100545001007940d900d02000b0b10380d40090001c00d80d2926910007660744801041549280c604240780440e00c0341c6e07a0580705000f0383c41e2038103000f6218540780d650350340300380900ca5103182d004003115810061103030050641d400440b60345049101900024001310b00c0708050900454100400d2244003903162120000383c61351440000502608000000000e01e49013100104180550380003502c80b82148105800d590a60344504400c15240c000d02807211040728400c1c2d0000c5045282559132002460014046d0100c00b07210700b030000010400406041d0840d81c1c0242044401008110072640c00b8015185809102c0750302c0e42100c0c0da4480c55003041002d40c01456001c0c000d003045a001e49039640d62514224030003400000180701e5580410415409010f81c191000042501740441c2100407411655010724001014100203d1070200855 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 594623066 1250 594621816 594621827
    0xd21021506040507200c0f0409020d02010804141509011508060f060a031401150806070f0815040203040516050405040314220906031502040533070c05040b0906150a 72
    0x80c0c81d186640c1858070445d175074a40c0350303994000c1e540d0060040f444510f040d85440d00c2050308031640109100981e159603001150640001030080303c11209500341c0c0d1040c90420411040d10703182e09074418155250911040d401d55400180c0b0a010800360b120074040003170f0204582c0c1d400000c290784080c10350f0f522400241c58581c681e01c09070100c420102e41c0b426154040d00408402c1c11042d8030851404d41e41d40d116540c2d0380f800c81d0701c0c00010380d070a41c0c61602e10303110700104d0342c01000040c038640070410700800003012a8000d480c00c0380c451b03110b40f26000d107514568800340d00902d0100d60802c61450552000703040c801c0c0818510306a041d000483c9000e20244282c11640c041c14442d01c0d2110540b039098060007095607010a540c010320503910603210840340d008031810350340094041800302c14454a4410b226002d0303165003c0f5800e08900c040b220309100000b500035580210250032601c0d00e004148070449100c00c8409010700200001c204a035140c050001201c14a040c40256880e011301c0d03822160b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 594624316 1250 594623066 594623087
    0x12010209090420100509040903030209061201050a0e070c02060c010906110306030115140f03071a030604180308060910080f030c25230d21021506040507 67
    0xa1025014003404240710840c0030f000c003480404480c5002d990b0395641040050590390103400c0c0001c1040001005c0c6003441d0700114401803081c1800b6040000323000014204e81c0006030500000090032004003d02d1802814007402810451201e002505010308020070203410329038040d00500c1e0016555011070f8095001071251500701c6002c05c0000c05402e88900503a006541c128030a60070b00c2c403070890400141c8030460842e03484c400f1251075003861400780040d2040c07000c056503040c0a48240001c0b41d0b00702c0c031070f2001250b03000c01d8159540c0c9040310402040f60100c0d059180180301034901035000982011180d504140104c031858100d6079001110301350310489400105203070145c10042c00715190004094007140c0d94200680e0b200d0781e0892403070030580c04149000400034104a504000010260844042001c4162204903000d511a8085100c030082442c0868100a491950b03c00d0894902d0f602401da00b89480078200a9205074032000c85c107a0050a000d11450b82c4002241c1c465010700c89502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 594625566 1250 594624316 594624319
    0x1b110402031302030d11061303140f0409060b070203030a1112040b03040c08061e07020705060a020d0225091509050c12010b03010b0703052212030212030405060612010209 75
    0x540d01c0c540300340d08000395040d10030b0881c028400d50140c0c20360507001b0051081c095103148014030160752000740d250001045680245d050109015060848090759001400c400600302940c4e036603207282035056011520294001c160806050103500d005076800301c01c88031b207a00315260030000c4c0022041c1b45410840035140d250300d0710100240015138003890202031807140380121510b034401e07681c0c2d1004944646044545000d145814141c12068907550402c040c2c1201c4280704944540d912038000c01c40c82d901561104000d68410007010300040e90400c800c0e0b051442030000300582140e803001d048031385036150107106c0e9482d4a446407100c1450b00c00c0449001802e106206002e5814842003d4074164441c0c000e10801d80c0c02100041a80e00010007264103c0e58040c00c100d16051260314200c2d04c90300b28035007054143d2041070b408902005100084070180c4440305010085a0040c80c1c040d280ca40d000c1c00e5401640c105204002c0890800711f149c07540300340140d0390110b400341c5523040e1a00902c5480c5105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 594626816 1250 594625566 594625571
    0xb0906100e041b0603060e1b1b010e060f01330f051201060512010e010b121e01180c02060603030a110a060501090c030e03091f0912050607030c0504061b1104 69
    0x16004d07034190030101c1240d9034446003d1058903044650f00021904004c8522400c00c10000c1e422003840d4045003080b50034480000290b0000440da503107061003002d680742040010f401005005000382e0121000c100003070040184010061901030f04201d01e022800340d0140050a250485524010012511041c22414980c0220343e1100d2000c1c00030380102d0114441031313980d00004101b4121011a032410ba5540051f848d0800c0070041c484612954010101c0c2c91b80c0c078028006d1405448042c900c03a01810f8891a102221002c0d00e415400f210498215030003158031000074020592030100484102600d0351030b080450740c00e11540a0b00d4507041003c003d041c2e0303240a0000031041e059902a00e42580d0f5641d0a00602030f0f12802180d80780039070444940d21183c40e0340481c141c41e216180c455007001c2e95082c0000c84170764445002c01c00c80c01f101c8096a0b41c0d04808204000140d252245007002c16060034868240340c280030005010a80c820071059070000000d0001c2c040c0a01c80080911030740c80240b09 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 594628066 1250 594626816 594626819
    0x10c080f10030b070302070c17012706110702060712030513081c0605030a050c0a120b060f010311070302071a0403030807050f190507030f03020c10090f060501080601030b0906100e041b 81
    0x127001c2c0b0075942e0f02101c0a0780d4602117a400811000c8110007001444040387c0c100d12660076210030006224480e0451880142000000010384642016190060003a6094680d29101507406416500014502d1941c40b102075075003000940100b058503000c10701006503603965200d0b111644002d2038941c124540c0362050040100400800103402c1d0101c0400380e42040e00703107541da00c4203d075481c03410300700a00c400454000206681030040001e02400014900814500c107032884140250b031020400364011b070070010040c027483d8a00350168100da04101d41c11481c043c9582c074014500c507006071422003045400911000c2e01c0c690350090703500702e000c084007000c05110307031a4026000b60300c160011000319000030380300110640a4826140340c08440406001e2542122001c203000304581b24040380c480d0280c0c038212010607080d1040a0181180307038002d29203941103007040241e1140007000186598404401c200c00202d00711541800c44e544035000d2a030726125843e09012170518441003000110210341c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 594629316 1250 594628066 594628079
    0xc021203060f120f1507051c09061503021e0f0904031103041d10150f0315090c02061308190c0b04050d090503070b1e0d02030702010c080f10030b070302070c 69
    0x7207a440000903a8215204003619206000103685c0c200c85c1100451414003042c9031080d66040081e041308040c0200156600069075000125001b600d030b81c030040e0000003024001c60400b80d1070308680f0540d241d00241907440480000e45107601c03841d4410700619110011500b018041d100c0c0300c42c6203c08506036a1226158040c4603480d1000c50305060000d540c0c0008100903265040a0320161800c010b2b00300041c0d54891000d4030224002c040100400d5520b142060002c0e102c15030480c0503040400c0003050020ba2200c009240450203815428046106d11131500001c0503c0103c6100c0300c10380d840d090003003e0034481650000d0f4031000c00381907801044100020842c001c42c0c2d510744040e45841d1100595152014199a40c4c800d01407440040300c1080750305400c0b0b014060045d80740c0b42c0b04240f140b0700311610210000341d0f082a2020b00240c1e454248000585070401c200d00e9202001c4d562400851800b07155124603c4c00c940300c098035034491000403420203486901100c451070341008072076030340e291380e0034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 594630566 1250 594629316 594629323
    0x6031508151611060f100902041401030b270a020c010c020606120708072105030d0603060507110c0103090809031e0d0f020601170a0c080309130c021203060f12 70
    0x84122508403080002e0a2065000300c1151110b900644018089555001d00c2e50204801c050001103118600f038070300044001540c00140007800c03c2c0e485401c4102d18800001d42901e00c064489441070007000c0601c1c41825070074144c04542c3c5c00446818503151102c0c8000c6000740f15820058600d542410903d07244543c000640314094601564070900703000c848403000343c81d03900d2070040c039143d9080f2010070007141940d546800780c1450b480c51b40b001e85442c40d55800345143c3c411030718407600a85030b41082052000c1c0307121f1103600007240e0811042c408030038000c86031a0382e003150504e414103903210385078020b06c9550801d4410f0110044c0484482803020b4a01607000808030a580c1154440c8001810300607101d080504c94140e100c0d001060301da400d01c2804420ba0000e07003800002c074400c05e802c400c04100300a01085c001e0810901030359407a40c060041c0035081c800300e50800b50310340c00c00d810298420344c0003505620a003d55001c1540702c2e00d6403c0029040d141002d9070640c013100d8180494040344010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 594631816 1250 594630566 594630571
    0x5011205070501020102040501020d0c1e030c0606050103050c040302041a06040f0f150e0123180108280b1c0803061831051203060f04060f0603150815 66
    0x400c110360035203544030012801d0b882680610b40c0140c004504155a841c0211404140b451140302a40d4008020b40181000c501c02080305074001000e54541d1070603c17000e842990007810703082c60706006a00c1e10707034412813841c07040d403100038095666026524019458040c0c60310000c1001040c5596556840c00f04922094a0b4056002801c0d010000050300c5c80c0c1a64900c4004221030700c0712903810001c4001981e000d80b209910010050b03100740e03201040c001c0300b00103000d416410b01c41c01d10307520081300004080400041400d000c83d00100310514020748000304c1da000c2c0c14a80c00008c2000200300c0007081c50803102c080c40822210300008110100b102403030141d403080300152011110441081040143c0d40000d0b2540f50340e001042c0b55102400a041403800c864440c541002c8400a000390784152504450241e4035003111170210505c40f0900d01364440c80c3c1c81500440c1e05100150501c1c0c0041c0d52030209210380000d140d0f40b13525030500451118101402451070000350f0304c2e0128111111460200c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 594633066 1250 594631816 594631823
    0x100504080a030c210209240a0f050310090c030605031c02011413060209012601140414010b07061d01090c09052a0c0f0f060703050c0703031806050112 66
    0x6186100e030710544601280284d2262025105604104c05411000254400741c52113800164034003081c07908080c00f1103522900b9000c0311000e036450781c14140042c11520034055540400c50308009018031314002c01c503058241c0b10281c0300060041040c0e0b805900800441c2d001d10342600841544607600c0081540e40300b00295981c00910515111404040700d007041151080328242200c02107502003070265001c2c01c10000e0604000000341800c42c188400d07040c1850703602d032240e80c0c0303c00184041c1600205110401506407402d10070044406102c3c0000b680c140612104210040f6111062114036041001240024203007001c40842e400c61260180c195004140d41240c2c10b0500001c45c1162446050301c40c0c3e41d0418450040c02030124500f18000c280e02c110400010b0621221030030650511246074800e01004c0203081082c1d100340c020381091002090300c0140362900d4100041c084594040303d40c2c0552502c0c001907425000160214500203a80d0060300032031802c400840c40006284888a0b210300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 594634316 1250 594633066 594633071
    0x60b0f0d150b0108070c03050c100501032102010b2112210c0702011202031b0301171b0901150309080f030402040b040c021902121c0f1407020d05100504080a03 70
    0x20b000c80152600c10050b502c3d800003591751121100864412400ba040e40702404007614101000d540184054900a80080c2d4004030300300ca40e4040c0b02070b03611000100351032a0000740806500580001c01400e454401c42000d920014142c1c41445018000044051558a5142d499144040c08441c01850000d00c0d2410605100301103008104840151007a0790f90594540300c46130b050000c140d020750005490362542100d040b2008609446500c051800390241c000d0502d107810640c0116450000855404900c1510002c2c43e107056454103504641524440e003c3c81e16000072040040380100140b09000e08550b1f404035101480701e0f800001907004a0007104d0510152b8210010001111800c90320000540e110381c0071400e8040d01401c0400600c0d0000b801e165181008000860a0841400d541c07820700508020031154150414004000000c20b880c040e070408004c2d14981e90944034040c0d0207440340c080442c0400c20401f0070400b45480e03035452072080c800c9081c9850074045030381240c105a80803d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 594635566 1250 594634316 594634331
    0x2090c0702120c13020d0f0c020102091003200c0a0507080109023d0311040b0703030509030c0304030303020d022209060803090d0807112d0a05060304060b0f0d15 71
    0x2c800911032040c84801080d05071090400b034114070003580801009081e01e40c8a5110214180c0300f481a000003024603000565900c400b00d0402c84035880884d155000d151414041e00b4030f036401c00400c2d40d80041a01101ca5450b204190000d00d029201c400050581c454200c000c900d00d4010b4102490491084d124802d040f400036410b80701840c660341c2c614078107141d490260125468000d45082088549090000b030950440c406880207a02079001a05402400102c4008065141c440c080d0302c803071200c018600306526900c1043d00e034451440040c04164010603104040d5001c0c3c0c0c119607103451050301144030340865620144d1a45010700c2200002485c181000990800100888541000007800140a8903141c0d484a030703035400007030080e1601d1000420004180d10352110070b000c07804100e000f0041003210458000000c01100200c54000c1009001c100500d84038101075a40203a4003100100780c0d00c581402280203c00d039900d5140e40000c015100e0020301108882251403c02c0d00781c020300401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 594636816 1250 594635566 594635599
    0x90f0603150e06160c02011805030a0b06030610030314180409050a02010e030607020d11070b04180614060a03021b1b0a080d02030a180b1c050a110d1802090c0702 71
    0x2134801070040d80825550344e514070043d80315100c001401c04100107210440d0703840c0c4010030324001c0020002c40c2c00c05602020706c0328a203020007655a1000a0914000159040d075400800b016008842c4000011010a02c82a070886078420305181060203041040b0702c072001d0410541c0d810b00f240e0143e000c591507200036200780c03d0106841d40701e180f20743c00030f02402e4040034080341c5c0139561032059802c600690f4400726000d0499001840203140c11130307410000003000105c080880b000d0790300488100505020907166a00c580c016242d03400c413213060042e2200d1a90400440c0c91602c0d07009040780340240c4040242e1881085945943e1301c005079010011152a4400d0f079544014900700040540d0050050710680ca20607800c00c1c042d80d1210f21003900f4690748850741d1200e508800166044a901104100700e00c003604d00c80c43da8072040102041c0030f4981041e02d610600d10a140354911616124001c460000468120701c03410607a001d040c900452814410100c031a811141080340308440d4840c000c1c284 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 594638066 1250 594636816 594636841
    0x10090b0a0b0a0501140705010612051203040309090e0c0901030b0717010e0606090a030605040302030301032a0b0a03330f0612020d0e0f0604060b010f0207090f0603150e06 75
    0x80a000303003202c20043d0a00c1c00641e001002c8900082188100300f1450001400a0144d64003c102c3c1d070b12120f006100c185812428401c0c8041c0728484210306004100104e40d206c0a0b01088030440100080c040002c2e0280c02d040140e50078149030824010b10000082024007144079125041e941e5501c0308000d50311340381d88000d420a2194000d01c18100012070341910b8080f00400090360018108010290340390340301f1064070300c00c035030540140c0c00c0440101f00f442241d82500c140962140218000c1c0d09821244106460140c0100040201f001c16404040c1d4041da2245203403100000f070394100011f451040700b591035040d6a101480f1071040c480050802c1040120b0016109640c803108540c26040329020001c0d00038007210021035803980d000c0719034003d0a0041210300b02280014010300d2509044c41001d5070b0700b1950480c10081c42030801d1001d280c0c08161001510403801c400300b691038842800308045d29094001619078010001020180b8a542e40401c212211000640703c05035200d9902c0390742c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 594639316 1250 594638066 594638081
    0x40302030601141c05030901080c03091b12030d0204140a0614030406060e010e06091b04092f04033302070510020309010b0f0621130510090b0a 63
    0x4041d440344005010403d401a0720508503403014180039500c0d0b50302202da484014441d60b0036202c4d0f800000394801a1350f44030703000325840100c0c400c0da00c4c40d6007080b00000c1e03510500f0307008400b035900304005460282c4d1745002105140d5920181260744400c6a03103501c80c001d502901c11f001040c05915006945400e005c0c501c00101c1d600b17a12507400c417600d41c03100b4100075840100210f030300d030381c0e00c2c0b201180d0308150a0b40305020b84042d4082a440d8584030040c00b07528940a0145000010007000300215680c2c00c01c100c40503600d04a40c081007122808107019041008040200d410720041c2e80c8441140c1000c002810850b800369200d10075006004032400800b1115400f1581d00503143e001c6079a090107913400074910140300740112403102c040420300038202e8105032030741002651180901c2c8400c0c50680b4245408501c202e4560f0700d80803607000d003403110b0300384a011218128506400965645c01d05451107441c5904081505c2c070f900001000e150007080d03400402c44800c81080c0204508903071900c04c500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 594640566 1250 594639316 594639319
    0x30a06050a1d01060c03022401170106030c050d060b15070209240d1b03080c120408280b280207121d04140f1b03012c16080a02040302 59
    0x2c110341d003810812a0303032501c0c10318242c003548100c59060b04181c5840300b80032884410002040e030154100b9442d10300701461109000780e035a0500c40c0520101e05088032407400c54000320360080b80015103103484070103044805561540041a402c03180c00c01ea00c00001013014a108a1302d2007844d680f0b814200781001b0b140105602d886041c0c1088010b0b1741455100d40280d203002e0b5510380d501c0c1a2503030003040e0300003d98004807015940401e903c65610410406032100408008005084c00d046c608400c0c1d0f00d0025480d2919499001940d102104004590701c0c85203e0b0808495503891401007031542c0c0c050741c414401c5000c0869500300c5a401b2005100b0380c3c4006510200ca052a041440802c0340e5804c864041c03450000e0780400c0748041341d034a502c100903070b001c0e4030b0311424854504101d1010052000614060140403500c1c8078a20000603074048074159400d06181e10004050680880102180103401c800b110445005001101c880c41d401c5808408240d6562600c560710b5601d20701c00c1c0e00903480000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 594641816 1250 594640566 594640619
    0x3030405010917271315230f0f121c090e090d0309110d03020a060510030803010b07061b02061b0a050d110f0a08010f06031a04020c0111030a06050a 65
    0xd0340040d014002c0f09400c0d00d0014002c0d400707156003540c84021a4210011010707105600a02084424000c03100f40414800e0508940502c07128600840c1c0504110b060052042c00d65000b00000d4ae40c60000208442d09c3c2c0300115510031854010715032140d820840020f0128000e101c00003601e9043d01c2d2014401d106030005000c2214003104250080c0581c49800c0301c464101c03420380d800300e46074446110b03d4903009074001c09030082d140c2094000c0b290050030308501e00000a200780b021130401001c40341160744040401e60b43c1d00641c20154002e0013200900b841002d0001604a2040c0d070000d0498001c051442d00140340300050f80d416030440c40b8000c00400810014080e003190030b41e19070700503550901140086440c0c0412440a030321360750312820400b0f01040007200140701d0b03003852052140290406043c100950080241000034805800719928811500015481d03001c55003900041e1035000d4900e501c0781c484c1003280b07000000e84840c4c004c0d5801000399880014041100c03019008400e218000d05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 594643066 1250 594641816 594641857
    0xd09050a0c0f060c0f033509030315010f05040b0304060501150206040519060608070f0f0e0601020a06020304022d01260411030a080301091a2202090f0303030405010917 74
    0x21030550005e4188140c01380000e41c81155407500e8407100a40395285191480880010100880150030a004d011915594014810410300c0c8540040104030300c1c1c0709003000081c001c00441c046503140309640203101c040c4da0100074401001242c1d00510b046c0d810304443c00440600f50303034049940e00d50442d030140159202c4400c8040c0f01d89074488105985014040200d8207c0c1c4480403546440090351040340b9008141c002000140000d602c4407010340102c10403103105040c001b000035500c103084080a0001603000010030115a00c40d400e410701d065050036170380d09130304c1c6141003689181000c0e90510b004c640d80c8121080c49915a18015514082e10b07186400c281d191034850310b01880384445601e0f09441034001d04004181c0f41d0024600905c1d4082d004035a00950b1110300d4916a00b045115024280ca84007441c0d02400d00d410300c000020b88514010b884401e50000100d03003401d6080f009815000c0041444103100c41034014141e4035000300009003000c0742d4602e0348151071103015080084248113845 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 594644316 1250 594643066 594643073
    0x100e0601120209030c060c03031e071e0905090a0c110a1e021215101215050709090c0c050111071a0c09060c060603101b0509060d09050a0c0f060c 64
    0x9003c52074401340464000c010800e0100b65a40d1254540e450140e00c04400c00208100741da1040000e145060811022800c1c0460042c10252070081c00040d190004a00c10810520a032030510080500906050160922030701d40001031a502240000081d450303199502c266600083c103901045d031000b4a44898102000707980c10310658800100c0e408014000000e204900c2004080500300160907800a603082400d00e281c0104240d0740005a0824401c03440d1000c05c0740f0040e03032440c1018002012a082d13861920032122071703102c0d41003078071603034502501c6003410782c4e00064071150b451046000700411044d80f2429a010b0003200c00060040c0399904014008003001240d20f5001500701c00c0c590b040c690401c0009003030350031100009025501001c00c00c4203030300c0c003009500d0709180d40c5441040b80050582c00c0400400403500240148500012034194580b20207084589445001c6c00c10041e12540d864283c0c0c8414440005032a42c640041d8013103162038208405408903040b43d01c8130b50a00d0126603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 594645566 1250 594644316 594644321
    0xc01020c0d02060c0d05031503071d09121912111e130b032707051504170303061e010c060f0228030c02010204050306040308090708070e100e060112 65
    0x42203803c86828480482c8100e0f00708481142e807605921740310f880b0320f89040410003114210400c1442503008403000c0082d94001d441d0480700150880316503606a5070103420b103203010460140c502c0c144a00041103500201c0c000c911962404540e0381e07902100d80541c0d814410b91340c11078580d00e0014800c00002181e44c10103007400d0301140030441c0042c28a07000790001e442948035a0311400c815180001008010319080c2c1c98480c0b44004003c080d0b14001103240d6860741c8100a0162a000b100c1a010f450b100006000a13100280041e1221150070500300c0c0240d41c681c0c00c00d81d0400d004101d55000004000b0144058110181d41a9500444109280c440300c0240c03092602c034040c940c0d0f080100c0c82d89490b601503c0e03400c04a0551250141c841c0f142001011180380300c0c40f50b400c44e4414041800150703800b00d500780d0000e80624201a503915813611003410705a00b9804918503125010002032010500c4006610603030a42903030f410030550300c44400f070020300102c40305c900244044d290111441d8055 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 594646816 1250 594645566 594645589
    0x619050405100e0f12070c08150103060209040609050a06150c030518060910080403120207050307080f09060301060c0c060908030a0f0e030a05150603030c030d0b0102010f090b16020c01020c 83
    0x10400c88a000154682c0c9a04052110f103170768580c02d01c0084d5440030310803505a80303801000c40000500485201494107a0468810700008000a40008170202a960341d900000042e002103c02003005041203200903000702480c0c031450103001020b150402c0362502440345007140c243c1640303032946803041c0c00c40004580d5a80c806296400170043c00315030903d4a614009034210400b5484a00c40c0d0f040030706028254101040390440301d05d00402900e0f0014002100341c8000c55403204001e038480d0b0108489015500400c0350541d0841c4000c000000c07110360150240d025180a454a500c4080d00c0b00c41c01c844c1017916001f0764599034010132900c408144a4800b00825990910b0121008a400e1000900f8040314078821340341980802090031440000549181c4c1118007100114505a0710084d6680c99014151038052460703540c94240035141d000b034214543d0125000400c214510151521030a0340310141c0b80341c0004403a00502407034550002440314441e060503002441e01410040810402d000b54 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 594648066 1250 594646816 594646841
    0xa060c020112020a090b212503090206090636180601020a021002030a08101421010f020a020c033c010609021b03041d040614010305061905040510 64
    0x45c502c0014001d86071800340081641c00c02501750320141120000080d82c5002d0b08260880d02c0b100f429400942e201c841c28203200c807050902003010100f82c00001c0c0e86018140b00c680e0400c0b00040d8a5481c100696502a0000c4400c16202000c215142d042420009010b802c0740e08045142061400060601801c5510640510490b074a03000140e0115108010381001040581d0021542d04c4a043d008514268055800b0303402d8401c0e03030710b0810b900402c0c0042540890007203046101303500100484200030031143c50030400902041c1407442200000398400c00b00040180200b142e801c1c82880c02050001140c15a00903000c1c008021241003002c0103920341c1d022400286141d00c58031860000c0c0244401010310500050310b4102185201c01640d6080c4501602c0d030f00200010311581da5140400d8102070021207001405a13900e1401100803c038005e810702501d030b00000000200000028441c3c46241901c0284594501d180e400e40159031060724010720742e07006540d00131400c212a92102040445 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 594649316 1250 594648066 594648077
    0xf06070212100b0f0609062d0c03030615070c0b03071101091103070f030b0109090204021c05070306090204080709090503091c0303140903030a0b040609060608060a060c020112020a 79
    0x1c0c224581450880c14040381c82101e901c0b070b41c80d18481c0c50809007102030540190b8401e440c0c8058180010401e10441c074560305000c220f1920075079141d02000e64000c2e88210305051550f07500840c2a000ea81e40c004580c140e228651031a2a0303200300040c0c2c41035441880d4010803c42003a41081d0310344480b42c1004140408010344c2d0501c107507000c81c09001d80d01210303000303402c5111001301c2c2d8000d0600340ba0340b541040047d07440064003000040c00303264095046030100700c4002040d1f111880010040d119485016041b44003c1003844049440f03580801d004100507281080041c0e036998025081c0e01440c460038001e5048034034108110b040582004000610a0080c2d81c80e000c10000014000404404000c420f083c84644c80000c044d0181306560b0b0b0440300074032600283c5480e800356681d0384030040003958000d813242140300d41b40d15640c2109002d0030003c03400380009030311a03034020420031040707421511a050684001900314000e0303000c1410590180d458890000c01402d00c84003175400a8604801c000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 594650566 1250 594649316 594649339
    0x302030c22140f0a05040302060a15030f050c011215140604090203010b18010518011101111c0f0908030612072616080d030e0106080303040c230f060702 67
    0x1c1107104552090354055860051400c20b5200300d10180c100030407125445103000140404203400041d4164030480300c100111705116400e5410407140c13520745c801041e646038403d07440300300440410400b441c0c1c0003e076561440700d0165507107002a610007154001c600e45401109214034903030f02120115900380644075616156454200354100c0e40268001681c800003c21442103052003035510207070055003440c1c40e6060000c41c000403409030214944e4030317041c82105943c4031505d2000b90050380700c40441c2141c81d07888001c4030b8010707550440c208203030366540c0d49824426104070055202f800f00340c9800190141c1140e8510051006481c0d0980f1048103d20661500040000f0120203070051402054103000100b8a4505400c2c5024080e081050a40704501024820040e00182040d044201450003140074480803000c01d00410072600903104501000080005008a580005080301d4041c0c280e0010446000124050212200b0203603071700c001000010f4480d032800802512100c0c2c0002c00740e06144 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 594651816 1250 594650566 594650629
    0x200304030f06060f091e021612030e0d140301050409050f03041e05040509060a020f040f03050331030f0201030b0301022a0106030b13031e0221040302030c 68
    0x1250302603002c0b5601d589070795042c00164003039616000180310044080c018044428500301c401e000c07541030000c1003035001c035a14110b01d101180d03441c2d45540101c7d208020410f1100002d01404407001030f00901d1260000424940c0d03c03981a4a9070220103075030050841c1d003010300708000303407400c42405c1c3e4841c4129201c030044000248010001080040800700080903900e118082103540c0d907200c148624540010000014008100b5603446003070aa001680e91100f0081c0d5415805140c02000094030060800b00401c0790010080087e81c2c0c12045260304400400f04000e0800c050705418540100c00b00b40402c0050307100c981c0e281086105040c0442c0359444080420f003260842e010840d0304030961080c4102004082981c0d1b2a20703041c0718001e205030350031615035940d114400750003038030761000e01c0048a0a00d881806a40d0800d00180e15150383d041c02d500009544030f102d00d01c3c000056506000c01c284840ca04d104032000c59501501520510810008100b03000b428184102d5089150840b401e104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 594653066 1250 594651816 594651833
    0x60b0a05061216113906120402011b060e15060d0b070212181207080714030a02090408030a0e060f040204090c0b0c011505030d091203050c061302010807090620030403 73
    0x2000311500041e4019820764604000c00da1507105c042c404000000c101c2c0100d0305c031002120400841e8600881c215111440101e034103550240725080e509d09403203c00c00030801c0b50b41145004100c128210740401301d10340d4040c100000c06840d040c6c0d01281d092000f40c00590501255903002c05540107481d030618000380d207601c10340d0050a080303290f4865203140c0006840c0c06402c100751880305100030642541041c007016614075590046804460301001c039044565010090103c500b540901148424100f62078001c0c1d0982090320104402d83c02c0081124a40d000003d03010b104203c04440041c02ea22540c090100404482d842a82c90000c044070200f0362100c410002c155546c4a20000070341c00740180e003400c1c0307225450782080e842034101c042c50488141e404881c001c203030b400c2c3c1020030358454a186400d0740c49202d06410041030740606001c1101049900c503a502c00039000307888401c84c0341d03a2090104c6e0030030410701805c00800d01031070847c084182800100101581c2c0082201e26054403038407030680 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 594654316 1250 594653066 594653083
    0xb09210316030e131b080103080406180302030307030806120a03051209010212010f0612060f1a071e0b0105030303090d080a14041b08070807121509060b0a0506121611 73
    0x10341c2d910340f208540045c0303a20084841c62019803406004650441e07440c14218401d901c0780340308001502c031180f0007900d0104c2c4048000d550080889540d076070603240140c105001220306900c00c0c48411545803d1450210701203030420382c955a2103241c005001c502c5a035601003d401000c003076600340010308030788500840d080d000c0c00f050712400ca211031920360010800304012214054180c10100200502c1840114007811f0f54031015031860a6201513038064035500407642c3c042c00740c003928400c00030401c0c400b4802c8005180181982034250f070300c66060503501d12041d41c02e18a5544406d682c0920381d8416003029400c0010807402241c80c0019584050448005840945040f82c91507115400d41541c0034024008000c100060600036240141c0980c884019220300c14000d0740603072150007003125020b290650100d20b01d03402c020506107810484020007807030081070701900419a022519240c010241c03400303207554261010301580c0303c081c145400000601120207124140b412262003010a0240740b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 594655566 1250 594654316 594654349
    0x509130f110301050c161106071218050402090904030e04290906030a020a03140102130308131a0702040e150f0703050c040308191101060b09210316030e 67
    0x1e090900102050308580c805840302595100c2000b00b003900174800b01440b003806400c0103e140c0b14003290804a04140301c1c4100c02000d880e2010a480e1603150091502c1c5551605031441302d040b1601c602c203001c224442c2494550740000e200f0002000684128074012450101030070210b2400340014180f41025032180b8107072007000c451501100709083c84140e040e4408001c400808200302c00d500494113858003800050051001c11111310b425240940484040156110f0103030b0318240c1d203051006c02600302490344100101c4014002490000d00c2c01e010442d184d400ca88940b52100c282e0800000b0104072000600d640149050444007c1c0c1b1804194420130040740c1c005086e142149006044a800402c0d44000302c0c02400140007280e0844255091440403480c4240c01d8500214280d0364a241d1301c000140d1136081c000045006410040644401003060707a00c1c4c170b43e00c0f045040306140100002c00740070f5107900a101030301840301d00d651980c040c9800382c00d0210016041001251000840b1a00700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 594656816 1250 594655566 594655583
    0x3011d030901120b0109030308090c0a030b04051c09140310060b03040b180c1201150906092f070f0b010815010e04021806011202190908160509130f 65
    0x281400d50300140f04020030148040300300240c2c4c80b15400a09000748900001c2d003000001c1c0005407030854204140018010000e0405802c545d032498031480c1c4240490b07048a460050a40c0b0301a062410848c250301009203440b10049241000c1da108101500000429414030802450011005940c41100302600164400c3c554038507103410941d111020250840790308101482682000700700c00b06e40112020002c581904003410259801c83c05400a041040080d00030300c480080c600301590312860072511801014044103000c0c100411140000c01c1c20700c50005003024030741041303e46d003900a01003680326940100c54004680c81e28280300109821240d00ea520208090301e1855411088030b0040106134181c1e581490301d64007168481d00842004140600c444010400b540c0c0201d4489940c1000c20b1011500c03698948481401c603040ca1801801041c1b19500209e0840c0000c51031006074031032030910115081c40c0c10300744421604001d29041d00c4040400c1c1400c00240c1e03140e41c1c0c001490182898 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 594658066 1250 594656816 594656827
    0x2011b060f0f0608070f0e0c0409020a02010b03010e0a080906031b030c070b0c0f091002030c010906230603070b09040b10050c06060a12020f1513060206011d1503011d03 74
    0x82c1e00031184282c000019960000c6800c0115100c1409500c09641408004038071688903203801d2025405140c121800881c00821890038440d8150b000c1181036500f10000c1c00094400340119843d41485070001d4010201007048010302e0622000640c0c201c111401824100d2510101801440e0410344200c10005400101101030080d0042030503081401883c4140c40c3c200001010641c5100d9001c4043c0211101c0c0400c0301c2c1e66000b4425900d02540240003481104031070316044004180c0451190f80544d840d42e41034000c1d00b07060005a110300170280042001070308181d034000c401e0308100c00e59988592205403c80064444400b68a01e0321169140c00da1101c441d148518113007403000b0714807400b0301c4c20351208010100e00020540c0d0f149405403180c043e141c01030720118220030850f210300181810b0001e4260105040c0c00881c0c0300b02c1b41070358250b4010b40d0301c03203804e000c1101d01c1c0c001803140c601111001c129a1034220b481c22200080c0100001050510380d03410052401c0100d0020500350400f088 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 594659316 1250 594658066 594658091
    0xa0b040b070c050301112d041221030b15041d040f1208010303030c030c090b1e031303080a05041a06181821160f06020309060601030c180302011b060f 66
    0x5240202110f59010459a400a580d07007e040c01a4810120b40e502c0480c1d01406107e076445a0300502d00c24001c10200b0f2090200b00034001d4081020103900641d644a0100c03403180141e000d803400d40b890f40400140186c088045c5200c103a80141c4140c41a0041880100c001080d001c100c07140000d20b0b448460071580346003030185c225800d00c81340310281421b0114065196500024a40540b0310551141e522240c2c0d607441903141d00e410f070740c21700e044200c00030510403250b8100c45005200c0d8071a40e2804200e42d5011020820fa52041d10003c007488440300800c2c1c13040e881c0411195004101901f2050600b4030410b203c9524103007500c160580982044021201080c188030403082c207040d40032018410941b81c12002c078544244d842115000003050400010480008a001c260795000302040d0346a0600720055500d42d0001d40d841070202c4d250002c0300060070b00410303003c8400c000c0c411000a8243c5540c00542d0000700e4004a1004d0440da0860840018081d21800c69034000c44000003030302140d00c8a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 594660566 1250 594659316 594659347
    0xe03160e0924160305041a07020c09150a1a040312030209090a060503010507020f060411010e03030f041509050d0b0702010f1d0f1c12090b040f0b060a0b040b070c05030111 75
    0x129103004c0505000803c0085131620800b202c02c1992503018000565030084102c0c14180928080d5a115807020700f031105d148503c0140d4205100110f8031804a07550700c505441904079503200c10891502c083c081080800c1c0d5002c00000034030b2003420050702c1d0003503600004075940011a0b94003800c40e44d600003030016050900c103003075008030540002d1803002800066a135407194000d1005242c04a01900704200d40d100d118a02c01000300a0704681e11800c2c0c0c18480c40b00e0b0307001030158801860068160750031041c860440c201c200c0c0c4020707083e032880c001661074007110500002c043c00b056640700c0101100c61251171060066040140d029891303040f152a15490600007011261619036009502c0d040981101c00c20600340e151710380c10b104404000614810000e80341c2c80b44081c0c840c03040c0303004110521107072401da00680b07481008005901d03a100420000300300303030901500400101c00d100a0040c900c80000074196640200030a080051f582d2002a00707450103113002840d481804aa000e07190140517 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 594661816 1250 594660566 594660601
    0x509010c17070c0e1f1d130203060708070305060303040506090409230706090b0c06071107030206191206061d0105040305030f0712080105011431060e03160e0924 71
    0x400c003810300c54031b03009140d40056800c01c00400000100d6003c1104207000d000d0762410941d001c1c0580311246010341c0c010f00003450443e001c201090034940081c406240100441e030a545004100c00d00f000011403d0100401540c5400c5401858881100c0100bc0c020b1b281020301c1c08407500101116800c0c1030000b0842d58080c1c0c40321210342d00a1240100d130310f101003807031a0b1001c030500d4403428680260101910384001070f88007942001e00020010031000e820b030b41c507004103c0305881e140e080d010b061003804100c2c5d036284101400928061501070301c080d86901c4003100d000052401c1420305449840e907600790342c0301c0c2000862860303001540f041040400d4421400e180400c2c1440c1d0b82540c9441d00180600c2d10a0f01340803011400007a441050f2071002e2034034100c3c035100500541590541c1c18080c04070016500407200410360600b800480c901e8005003c9842c2c012102d40d18808071301e803100c400303545c0202500756509809144e05c40c20385441c00d00f6580907041d0017000201c01d6424804425a59403031807 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 594663066 1250 594661816 594661861
    0xe062403011a15070f0803062b03050c031e0c2e050a0908030a0b03060108010e03180a120303090c090c020a0f06021b0606100509010c17070c0e 63
    0x40c55048500e168500d20b41030702c0d9040a40c2c05124203024210500040c1c4100800100310804045489041c03014990195109072070985110202c20b1120b940704440000d00e91742201b40c45144004200042d00c034801070800b50b040042100c0c24046d44001c410010144100d0034042000007103030080758100b081120340c4141e541100510000d04d441855160707003020740741e1031010701d80d1034501003526620180d010000a82d044283d141e12820421042e00242c1640031100b4802c4c0b04000010501e1181840781c0a2500243c900451500c2c3e91002c2d60400207031045011795101e40034050008582d0000c01c011050544603940001d40301d5114607200e50901010f40042c940e03a8078000f0030002c50364001404050140d001030700105031075400d14144003c3c0c03080706032003a0380303c82914188405140020300f15025100031250100c4003424180d045480e03009118031140011190b01a0101013001242c40002403c1c00c000406e1034011036846031080c1c0c500c41d03404003005404c0c050030044034100b07051450100294 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 594664316 1250 594663066 594663071
    0x20d0f050105010f0c0206040e090102031005060924040306050106050d110a0c0813031b0521060606070302010e07140f010306231807030219080402100c05010e06240301 74
    0x4101c00202414400140c15040c844c0c40c0400e1011b40d41e1301425500244088040c03559075103007580752035010750015180c03c9404016041c0100b40fa01e07040381541c41400700034040c901c500782d451003d51840191011900c005040c204404400300e0100e0060318081c0005860307080d5582002c20480d011105e035801d0a1102e40002c1c0301c1a2051503000707410b4072189030000c6c1c0203616102c00107041d4103080c00b16400240322a040c02031055103498031100c0c44003110800c80e96074902c1c001140303d0f08058144c3c0706484145400420000e0114505403015010207806440002440a9403003600d902d4041d030f90b0044602c58051282c0302817985094903d0644041080c47c041c8642450040c0300c0305080c210b6040c4c984080c00d400001d20458031500e88105800d0610090310007642480740000d00258001401c400d1842101e4031205c000d18050886c1034041c6070302401c405480940c01c00c040300c008018138411910340d500ca020b90095100100503542c000c1c080c6185032140004401813881c0d00411a19101c2d00030f90 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 594665566 1250 594664316 594664319
    0x203091b0303040605030703021c050105130203060603012105012901051201211a04060b0a0e010909030c0515010e0702010632090103060902090105090c190918020d0f0501 75
    0x220080240c800310f51180c20001c1d10380c7c4070660705074068002e090300645400b14101c4100e00121094100c00d04032801034030a89001e0511001c0d20003684011500b041c0c1054040004114201c01030a0350000080520030114002019680c0c4609403500344d1401c094000b507140035150500718040c0d44401490302424218501080140301b080d0001d0705110305581e84060050414800c5c40017408000b035035a1015819543c2e14203150740c20050f82094500340c40c0d0030301d8840c0210b06410520b000c401651480b00b10385505a103010034076400340640711802c40820044085020002e14100705521122054111301d9402c0d604140502c140c4035401007002c002c5a0402000304900c1c1c4206004040320f01c2208628400c03004981444c080311800380814640060445000205100c40c0340d0021710744c0c42c4229866840c5984c0d0300d0411071000b00588040400300420000350b070f0b0322030341010050110145800c1c403074003150340c61844404110b006030480e07008607000980c410101001d48940d640b81982c46408101c00e5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 594666816 1250 594665566 594665569
    0x121b12040201080405030f0403050609010509010603021507030c02100806030d0219030c0203070f06020f16031707020a170a0c0f0303170a1503060c020d090b090f04021c0203091b 78
    0x2000240029062040b9280802c0a000082c0110b42081003042e552660703550760703031401c681d880b1000c40e00070901d0b501e0a0045002ea0308107018150881b40c00401a0000c41c0e10f112100c0d0f0141c1c400f8101720103000070012071000686400b811008501800e40340e120481c0741102c14541032844103040c1c081103400410740781d18010002c1400000340b62309071a062020046600c0402e15096941d0007000040020304000114a680002d080c1002141c2e9000e940c40044000402c00484900b0b000c0205100c1d400c54000220411200144c414035000414400c49283d5a132614a400d4001c8225030720b40b40c0021010300107000c1c0d03440b01c40c0c00070011008910390107407443d2001072039a940e0a201640c101c0c1d8074004070700700c0d20035a08422000c4080d4106101415924036014009060b40d4200d00003501800010f0301c41309001d04001d40c11610f156201c5841d100e40c60080000543c0c40c4190241d00a90078000c1d03070303003c4050450158054182040040c1e5908080d80158034101c00c007040c2516040e00f004460046 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 594668066 1250 594666816 594666847
    0x1d160302091e100804122106090c17010803031b07020904050106210218060d05061501080f0732030a06050306060334180606030e0a0201090e09030f121b 67
    0x24030740140380000c460b0380c03280c07494102005607d1001c84480d040c00030110320b4507221b40c0b04481c820225100c0303540905100f541e40d0b0840310b003480b404420b60800d00000e0000540010b01e113203034003c0c3c014024540742c0b032a40082c107030040c10381e030984080c5e40d10881448209104140e090a80207452944e0812880940c00034241890398035007151281e40e0400032603140c1c0c4900358801e6000741d012058904034602030000144040c5d00700140ca00059110011421200c071018905001f41003590f955000c00c11040c0344085034421081c68117104113080784c15042c03007104e903902440c0500c0102c040403d0f04c6240c0020580380c01030242009100740c005a03944400c003031100e035000951151044203008480070702c860103c8544031303d5110444041194011800702040d41d0b200720141c0f16140ca080040001e80c9048a0791030688410081c0800e041358070510640c480e04103220351045e08542100d25001c03090408903015001141807802007109581400038035841c0305415140c10159a44050030170700501c030755404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 594669316 1250 594668066 594668093
    0xf090803071b0b0a080603010510080c2e090906090e0304030b06040603020a0e16030c120906020c0d1d0103020702060f070f0204020c0f06011d160302091e100804 71
    0x860351808103030322060b0481c00740d640d0051948289140e00c40321035000140c0020000c5803818829461710000a2440401d4180e4400f0b40380710b4001441ea24000c28288828000e071102d1801080b01c030071940c00d0340129810080029410303544d6a61801d41d01e440e0b9080166211500604840c60810000c0c82c804600041070310210394200300c0b000090f0b1680008035000380241e400c0a908411114008603240003403854180c010000f0007844407001031064001c60441c0e1305103013210700090b4220441c0401c0d42d820f40080c0748560181d08014600b100d00080305103814546000c42d00400d400f020313204691010303210001030720724083c2001e510f0101c0345d50008545218020310400316135404039100c424091300c82c5019403e50b0380904115501e070303103400505541d08100b0080c101d85214130800854055600041d100202e802c006145a0589030300495013020804110141c081507802c0c450a01e469542c4c440d102050740c4140b40c49802c41428800b400010242c2048a0040c0144042880300145500b1030804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 594670566 1250 594669316 594669323
    0x6030506100b120a200405010e0901230414161101060f050127090209190305030a3507030513020a030b0901020d150f051504032d120f09080307 63
    0x152644e22541c1c482d0040c540300c0c5e00c0e00542c0071152000c00f508071000f00200140e540c00d898025800746024200802030b6000d000b4a100051001011041401c0008d0180301c2c0e18001800450700001c50141e610202d4800c451400c030800340b44492121042d00560b0391a001c100d00402403100c14240b0445400c2c3d45030702d10a031810400e0340681004d9aa90071b211621694400010040640d695021980003070b4000200d076500c6808282c4e00c40030194164500c050840b5403100182d405d10400c143c0545050101000603081148001c501e81051031022071700d500390017281e441c0440a81170820b0014103c5d40002c20804d8081c81016410002d070783c4492941003120b600000b0180e069844d001d606019014080c0c0e051034190a103003442d1188081640040141e844180c408050303540c0d128100b100006410070744c5503180e102040280082191500e405501e00100c100700c01000b907507403650b4400310130880d00c2554240380300d20040c5c2803664400150001115503103003d80101d41064941e030f07141d12521000a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 594671816 1250 594670566 594670597
    0x9090307120806040f0e01050604180b15040e0f1b0f0d14030412030e100804081b03070212011a09010b0406030506040b03030a0f0306051f050c01140a06030506100b 72
    0x3003444e91103810120601d14540320a00c8400112400c06000e00780a035100b910030350414843c94048402400ca4021240d00900c00c00b202d80c869414111000d0507070b54100350040e4903051204248402040b1080e01000310700e00802100c4c1c000c5011022458000404610440400c80745d80065607460382550f079403039005400c1040c070080100c21030b0b2640c491548000f02480f01c40c130728407080c5600100355014001003a12103550350f501940d011910b21100b00c90090a00005000c00c00c0344e460b0040503294140ca062003200d180100700d80005030390151b5210108000d0f91079507100100c2801613101c45816200a075a01c80c4c20394181141c0c6c4420303002d203000d980105070341d80002800c155150b0b080003908900280c1600d940303074001d0b00c2c0208001490b03442103006c0fa04000000645040425010aa403104c0c14810a0911036819048805500207060062199280c09400750f50840208189000303d48608001a0152540ca46541060030003806100800480c600030800920071408954912884a0740c6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 594673066 1250 594671816 594671821
    0x415090c03062a08270a0515060307030f0602070203010f06090b10020c0d020102070f0303050309061602070e1911031803030f060d0206120a0204090b061801030c05070209090705090903071208 84
    0x2e00c810040054040c00c00810105c210607088000302d560140ba40c0104103449036031001650f44088200283e903c140c0550010304200041042e03200400700da180b2902003d440c01005400090075610342c141d007120480d550750020807131510180700d450741202c4182c0300d0b940d001042507406905c1e0002850500d008060710f8114004685c4203200381005005054491403505461b4140108160402c44000041d44034131001303d9601030040811028009190b0300424201e410028040c50a00d000360502124501c00008080e003007540f0b014018407e10305c080e1498880c6404280407a0b15a03070340140c00400d410400030b100200b0307202000c455204c13070242d5450000f01c0c16880420002c1c400e07001c0e2200e2002c540b81c02d0109405d2150024412544c14440a20000301000100316041c49004500e5009100090301101154000e400c000424206410818140800e58021404811048860703c8803504010305c24015450800c00d05038001045900942c144110f41d91060418032405140500f4441c40800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 594674316 1250 594673066 594673081
    0xd09050102010b030c01180e250c0f02061e0d1b0f140c0a050610030506280b01200102040305010507140d0e031303030305090d180e0415090c03062a08 66
    0x1f1440000c10142400c9429851b04200240c030f480c83e089192034000103a00c0a00074420701c119800d00103540c01155066407411503600f000031a91004d0450050030003100791841020700100c014100b0040141d40114a1900d42d014491341180c0020444080c84ac6091000d08000e502819407281d00c10580310056035034005000e22460704031410402080b91280608208442c03410090f40011a40314004982c0030f0707152060308441a010302c0780d0504c1c4401f0300070301400008049030801f54420506041c007034524404126400c0d50108495043c101d103039000102041000401d10680790301000318501180f81611560305604184503041c010702d02d076500e84401c103981c040140f0448209010312a4812aa907aa03880c0250241c41c04803000310060240304404081d550041c10000b03501c0400c070701409a1301d0b0030100f0b080c1c0040c1000d4001d45440c1c560150034002d0b00014414058010b000c1c1e102c801680b803840c6484000c0d0b40e003003080342e0626040c0103440604040d40a1401000451a0030002c14a544648 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 594675566 1250 594674316 594674357
    0x405040e0705210c030111070609030c15020403031803030c2a180c0f1b17030411190308040509040602091005040503010e03031b0918090d09050102010b030c01 70
    0x802c0310ba80004004a5000c0501c003010b0b400350941e002d03000fa96880c0280340101401c0f42e550301d084400c40c620800090001504507840311902d5480380c02c0007180124a5250700100e04401107000b006140d00103400d0051507080710300e401d04128010364103040e10381180d0f030040407540759a10007044c0340301a44210903500a6a101d0f444081e04c2d0303812400f90583c1d03441d0303203112092808450b9021f06152540c50b0011920032451503c8030300c0242c4a171399940990648040c2ea850403400161540400100070030380c0b2541010045001c0c5004604100e2130803400810811180d80c040008004005d59103000c200150002e0f040c1d07021100c2c1201d000400c0e07640c40c1406400b03442146499507008503540840407000390000050000d6270070540c020404101d0340d0303142580d00d110a0301d641350074890703402a0707051802400e001400100000f50450070f0383e040b8030002500042c020b66a4011941120704ea001d001984404001d0081a0900c001d004240c03a040120f5203c001c4040d4640c1001201c803400d1007c20b1035003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 594676816 1250 594675566 594675569
    0xc0f0a0b07082508120c09090f130b040b0106080609040b0703020a090306020c0a0c05040e060408070204021b0105011802030708150a1a07020414010e0c09190b0a020111040b0405040e07 81
    0x102d00c1203c10600070720300180580c1c800241c03842400800030100343d040c0b000001356035501601820b484010703220722601440303209004000007461014440005d0010302807c010b82c0c040c0344a0504000c05505144000d003c555004000034081c2081804000114040030105a00700c91107007001a84e840000c6403c0360308030980e0308040c000c1400003e00d02c0d412000056640c41141c020002400e09603199003c100c10b54803403910700c40583d4010340c08500824130b40340050007000e1004000601d00503d4603c3d100c20103020528151950355a0001008128a401e8580700c905841080031807862410304e03c05425010060444601c80040b202034000d10b44441003650041c041154a5250702c18004a0700d182d1640110000ca00850901400802c2a04084540c0741a2100302806030800c0d650380c0c04c0e607540e03904100d220903441255094400d081a01f44031000000d1b102d40b500301655072125100203400c0d5a4011080556400d08000401ca00882141510b043c0c650441e004150352100c200500e2500515 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 594678066 1250 594676816 594676867
    0x20c09071206050108070504090e0a1a0f06061c0504020112050a020d0b0f010f14161118010e0705090a0816061710050103051305010e0c0f0a0b0708 65
    0x18424800c11036000240c041d440c1800d0581071100c03030303100c80045400c200280c031001e022820600082c0303c0170000e0382003210701080d080c04894000d01c03a601c40d15a4482445800c0110690507800e1101416a000d42194008010740e00240b0f058900c0c1c0c1444d00090200040c0100301c1d0f0780701c1c041421684a0b442102c0c559561a40512403401d108003008000e40c4452986409685081407846071802c1c00150f10662110503120b0340c0302803000e5481521580505402c00f40520000c001d0300310104034005c810110b50b0701501541d6510000003040c006450140c42d19231b00614240c400402440b0800c00b80198050441c1c6809600c2c0c50702000030030042c424a40000d4640d0060600d403480545400c1801c000b104c0169485010b030214280c2040a0681d05444440d2402d600e14400d0043d54040d03041aa004819100e0520840ca01501c41c1821600181d02121442c1c000c01443d20203803900e00c9c080e0380c0001c0300325084c4c0c040d149840000816441080401080e84001048080c08420740c01c2451824003003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 594679316 1250 594678066 594678079
    0xa0b030105100501022506110f1204090c1e030e01110706140f040809060a14120403111504020f0103020c061f170a0213020f1b0708060c1207020c 64
    0x802e4421105644180e0007014010301c244840140300340443ea1074021201e1081c00b800d002c050a180c0d00701c0d1143d41c181c1104503903206000d01c41812000401100c0112109611420344079400c084600050b100301d100d0040400c04068082100300d06004101b2a82c81041d00300052180140640715025061450f0704d51006403002c110601030000f141c03ca642c1c24060340c150b15040b641c0c0c0d0b0b070420482c120240c80203410040280019072450800000a111410050501804086080c01401100d5200c0c424000340d000e61082031000f0103800001e980702e800c3d0000082c2c10904400091007040c0200280040d1049100310704184659019604542007500e4000030f031285494800059440c1e8188110f0100d0b4803003014500140c1c030100d1018044c10325010f0805032801140c59001c01007420039100c145260507600300004888510200300400480012501c81000c0c500b466080a08000c49984441d0050704018100007541e0454011284045c854811045a94a80c0c0f00120318184800d00603641011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 594680566 1250 594679316 594679321
    0x23040e0c0415150c030801060e030a0206030103050f060a021c0f020c01060b07030e0906090f0721060801180203060403050309010b04110d0f0b03030406270306090302150106080c030a0b030105 84
    0x4904584240c07011040e00340c900035002d00041307a86014101014000403a0030005004862150100d0740000000904403110181290000f071000d601c20390045130981c0c00310032a00103120003409070a1780000c05202c00c6062a500c81d841000f0b10000c5005000600c1d078990680008040f9039042e510b00100303075802084190703251511007101d0707808071506501092081c3e13121192841e10b0020705101e0720300a019145c4686134500034004010024229109001003c6100760041100300c444210900094001003450361410301e8460071110130340500383c0e11341110051071016840008807207402c241e2510785a5501d9035884403540c010f048000b0255807060a182e0341c0d1540840303000c06481d82c00040d100c20002180082c0051088070030b040b0a46030150810300081124034000e003401d503101a0741d400340307400458034804440c07400c0500342c000f10b400964450345541455030400052080c2110020690502d5040c031038040d110a4000f000201c1d00d200000000b0040f0320070b03030041d100e11103018000f40090b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 594681816 1250 594680566 594680591
    0x90207111806150f0c0f0105150603090714060d05040803060f0405060109031203061208070b010608070207140625150c0e060a02010905070605040801050123040e0c04 73
    0x2400030640452107541c0c1c0c0918001d8074a507404000e80074000040030580194008002031606802005002d84c800b04103200f120f11001041c4010030001c01c40500010301441d0052480f0041c00d0f10082090160f4810310421802c000c00007070600603207200b4900d0b0b040f1611014001441c1d44078082402c007040742010284003c0142100240d03018070700403154800740158007014081281d004441e082d000400e40d5108201181101100c481e0301038451a01146458852440d0701c2e5001d15040c040b80c2c40000010828280030320000224050a8985400402030900d028001e5a420040c005c50546004c40d503480411552040d040f190026403440d070018040303d0650709412882007844059807000f92805001c07500c00c03818401c0701380d0400d0a484803260048600240f091a0300b01d451044199913843c0c4001005c104100f04ca08024082580c609640e43c1c02c2c424601d003540c01c10703401580400d02d10032030300b10b400c0320220a241c0b683c1002c2d500000c54428400c8040c2c0340c00b40450030150001d02d00b05210307200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 594683066 1250 594681816 594681833
    0x1020a08010323100e0c01050702030c130b0d0b04140604020a0e100f0b030411010801180e03040515070303150302100f0e151b03040e16050706020315090601080603030d0c09090207 79
    0x50302034074400d1b1104c229440005448610410070000c4d416000512040000d142c8801400700c009d0505c00c00141c0741c1c4003c00452040b0f29035070400d0307a10340141003c210804c2584440302c06000c0b0410041c003001e0070b090340405e001000700c4c0600000b010440380003c00300070000c0300741c81c002d211045542450a641d8080102c003603006490a0b00c0c200c036a07011001041d405268414100e62942c0c2400002840c43d480c50300c014805d0b018034137580e00080200241551303890000311101c40c403581c5455500e4000e807502500705c1c3c9008901a08500e281041040582d407204000c00c007200721400c0c039035245403181c103045500180043c1d1080c1c0c4a0a403001040800340054040d110030781a4502c03031420b11480380ca2103070b034038003840c40f49458002d050030019544400c4170141001100e110705043c1e080c0505a0b4520051f82c104484004286082d0208400203142100700710340c0205082c00c00030541c0c200040070079102c1c0314940003d02a161038900001c02103108841c0305c7c0041240803c01c548441230340c5801c901 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 594684316 1250 594683066 594683081
    0xd060e0103020f1e060a0e090702070611010e07141c030e010306091811011202030a02031015080a15030c031a0c03070f03110d02121801020a0801032310 67
    0x260506081001407800e200c0c031380700c0d01410310a0720004c903004030100304080750780002018020010003201004050311601401409203015401a090301390900000401c0000160074a40702c41e17040601242d071001c00440c491044d034016040c1e61700300c2952140414120482c01007603442d0601f22400b141d007403580c440304205012030300b41d800b8400990756002c59001c2c0c0303a1114001e82441007a03075110300024078424100700d03140d0040c1056030f0b20b0320300319604404a1708115030500391150004100500f01c1000c04611000d0004926940b40181c58003000801c003c400415081c5e1540d944e40c3c481a100030a83e0308000155480401505070710b07240d180c1100e8849420b41207001d12000da0010840548501c4180e0303102d00d2f000d41e038110828000402c05c070040c18041d03000030f5824038208210402d401140c0028480502c0c040c550401e0707420001528141001c800c982e00e02d5907441481131032102540300740d000781100e4020356106800c032120005061718200c0341e80082c00900c03c407110900c04101c240c20900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 594685566 1250 594684316 594684319
    0x60816060e01020304050a0e06030a0b0108011b0516030c05011b110106150804030507030912080a021005010506070204020c011b020d021b010c03030515210120031303050d060e010302 80
    0x1000d2860040166130364000c80c0281c41d0701c004118018850034404503030340360788044000d08940b8010742e6925003400c500d00a030050300b138594445001501d100514a42072114507071501e00306150004050b100200902c003c84001c04000402c42c1603014820250018094003a908003c1707101d100030a01c018002418141700d12880707500f0700c0c40000d40d000e0102200c000210355510340500c640d941d9a401c0703460b588030701400c03014091603042c04900d40611401501500d4444c5c910340740e0314800e10f880a40b82001022803252014185401031210340c94117000d0301c00140d4103880160326500541800c9002d850240348100c01102c42120100400741d00050803074035038601c0d40035035912120451084200781d0001100a01080b42200c40500081c404d50044e80c0c0004508481c40803ca01c200005401c65402c00014420410b80f80b03d91b61064828418594a0b0340c0c00b0300b4085c41d610900b2421079150100401c000070b030b01c9042404d2001d06001e00700722140e000f0303c03200c20400d0317035240d07100d2400c902c00a000c06d9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 594686816 1250 594685566 594685577
    0x10f050a09020306011e0309122708070b0a03110f1c050103030e1018031b0e040f2d061401090b030a021e0301023712050a06081606 58
    0x2000c040368400c03a801500d041c0d5a18103428148290142202e0102e0710046c1010394030002c441c0032420002a00503000419562038003120080d080700c1444c68180a0a8424124600c00802004d130b0f0000d403d0040f5000f201c40f00341c0f5a140030000345d0092000412803110100d000421040c5503011000a0410280c050412060405480c0300e07481120000d020040c04a00b903000300030000d141600b1010000d0b0554034090500c8180d1100c40d0386070f0100380d442140e0580384500305e20031034402e1501c442c018068149807141140f030541c51308491103081c40400344c481020b8541e4083c0030b440001c0d0111001c010803008204c15070803442c0c460010204403080d103120410309800814200303075600540040e940010018a01e040c119001c21035030070090000010040d0011102e07042c0303078070280040e00220485843c00174000c1c2c0c2d001803034000010085291824040100c9241108139003000e03c11507450384000e070005440e42d4000f016002400340b03401c011454401c000006084c603414501e8881615055a0380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 594688066 1250 594686816 594686819
    0x60c07020a0e0f0a050a0204030807140106080d0206040b0403091e030b060a030317090c10050d18080f0306060f040b2113020904020409080a02070f06090e060409020f030105010f050a 80
    0x4260802540d80a50390f107480d00100d40b5244040d007195421401e02c100c0140303030954a603141802684007507404c6a540c0d003403880707101e9072500030302c5114020300b081009849000ca20000c001d48506008000a10700c00d200004682450320034002030001d041990b4044441020002200000700d40c0ba01c021158591051700150301c13802d10307070f0b034800c01c482d499100e0308003444560903407d401750001010240c1620030480130120302c0d50b03566005400c1060395282c07166154400b151240940b080281500c058640c10021000050440c10442e08145c1c0744001b25910303512044c0000b0710030b104207441c4441000d030120b0041000034480005103816003a48044007195020200180603401d0200d400400401e940340406015040c611402c40d4824030091000500b500070b40e8807449540c0200103210016800010f05005000c04e04400d1009000f180c14600e80340392a10403c4450303410300400c1c8074092030300c03080f5540464440409000307507080010024031041da1120224a0104618030800b441200342d03900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 594689316 1250 594688066 594688079
    0x30b0f09010e01110a0c03020c0910051908061f0e07110114090316050a0c03060b0109080105060a060c21210e0706050a050f070302030a110d020714060c060c07020a 72
    0x138041c5111000f418031800c10260740426181c2e2038200f0025070545c065203010030074036600e40c0e0309580304800301010f561081c0c1c03c000c10700071610240c0090704d10000c00c0000500090400240c02a8000ca4060756070501c02010b9421107090845648512440c007500414412000d41050302d0810404a040007003000d002031400c072400e40e1070306555401d102e400402c010a0300402c80b180800c08280240b046a000020b950341f0b090b0301e42c0c05e582c0305403211039460b680020b03650780c030484050050156400a0110b802e20400142d035030903c510405040c0720700000c02d4000c0001a44074000e1505540741180090248044044e0406c246071003009a0700c540c00700541000e130748601c20740f900c581c0250000d003c2d03c2c5c00e22600340d4840e8800c5101c1020b1020600001410300d20310030007000568442e81c05507403107040e142c4001e400010803810514240d00318101c030740401540020098201d4541c038000030300001040c0040b036080d10a0750758840160090400700203541000f94002d0080b0361094a040903440d55545 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 594690566 1250 594689316 594689321
    0x12152508040b0a0c0302040f0f060f17060d02150a020a03090515040b0d06050a0303090305010f0506183114010e0d0e011202030a1d0c0f0103090c030b0f09010e01 71
    0x140d0040c0180400703000b0403024040e9904c110411485410b0052501ea00c403049552001a03ea02050510b900c046050144540c002071038401c1903001e04115031114040c8000c0007860800a01c414003680840070f040c0155511f000740102c1d9101d1401d45c0d69501e0000c0c0500070749030540601c080e8045070502c00c00103a01e042c0300790905003224480d4205130805041001484d20f9521580e00340c901e10303868680104440d035038034507010015840b03034480c82c3d916442e6141650a40d400e0204004600b031805003041040d8403208050f9013102038071142005e0030350b10300601d811302c141c10710203100f038a551100e0003d00811082e0150303410640100703904100b80275a03454032403c1e1031032140c5010f5141c001480b42240300c3d005d02c1e14205421014100f40130401102c22104040740c0017100c0911003151203000300404071285410183d88c0402c60006451040d00e0540890390080558003801e04055482e01803100380300340c03000c29002443d4070045c0d002c1503043c40140701c20380580c2543c031401c1c554a0000d0804a001051 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 594691816 1250 594690566 594690571
    0x405010c050306030a060b0316120b1014060c160b090301060e0c07120512040308060f1801050118030606080312070c0308070807170705040f0e130212152508 69
    0xc0040c50440246d51714080604000288550036204150401f22551400100c400140c813041c1c0455852590600f000180140007800c5070381c03c02001c07402404058100215a5005041515210fa0307550040c01160b1820450801c4074201d2840c83c20007054a2511800600b0314060890081c0006a10748000d010058002c1c1c400000c616800c06c10380000030f4401d100c12409440508180307080c0203c2407410a13030040d04950440c00203a01d402080b0b03152801d00c5800602e554142c901084034001c518141140481c180541750500c045d40d03883d01c1e4116103c1040b00003035688014203110303060f620b4000a50780e0700603058594a83c520100000c2c00c0501c141400c050f540c1c3c240d6200410790b10390501c10f0350007400182410b010030a81c000d19240c4010a0303c8014080c400355652a6556403803c0b554144060040d008103880c0756660301400a614901c180182e201501200c3c07401e0700d5080b22160914040c0c0c3c46001c504184410303000c114900004410800e031301c0305d13580c3c0d9400740c0c2c54a609044401d613808 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 594693066 1250 594691816 594691819
    0xa0311090a05041104080d090e0c09131104030807050c0102010b01050c070308030c0702031605090a062318010609030605130b04140c0a030b10090b060a0c0303020409020f030405010c050306 83
    0x102a080040c0c0c58260071144001d43e411101c4d0780340503199a809807c0c000040b4801010408000301001030b0045200c41c01d41c4401c001d12114103204404002035581e501d0794490070309030f94566803103821000d0f4010807600111b5004400e25a01c58061074002d0b1a000c2a010160255280c805c0d003401c2540100c0c101c41d00400410080d1140600315504c4800a0708040c0040d00f6140050119000684041102100070142e45480d1600e02e46030804001003a48000c040c440c0d100e0038100c0c204035509000440d1590b801c8001140c40300315421102040c5180007096440884150318000010300a40001c82641924021181403216580c0c226500000c807600c404010000c1c107005c00024080b070b80d80c800c0400e40d100c003030382502c0e01091a000080d0907200b01303030420f450b2110010705001600c0141007141c4020412400c007442234100032070004507280200340e045001e1108191100e020540701c0d50440b4007601010a04544403e191070480c0095001118100e40325803800f420401c41c00c2c026000d9902c507540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 594694316 1250 594693066 594693079
    0x61804060b3105060d0c050409020f0c0c01050f041a07062f0a0504030813030204051611160b030a1e1b020c03120c0a050a0b100608190e1009080a031109 67
    0xc04036410000b40054414030b007c001c014071010402d810140001c3c0030398245182100d484591120401e81003c403640b064070305106040000c82600d10300301003507400316070a0011000380400301224024091003801801800c1501d407420104054200403950380300e00f000e030041444008980703001c81400d031144101c1003010820a101c02c10001e42e4a0340281140e002d645280d000c0d4070742e01e9020900303540c400e80356a05801203841d090074019078054203c80d60825400e000340854002d040e054801001715004910b00101d00000099005180360840001020002c04600d075801d1420f140b407000701038481a045421100000c3c150b00c20340b00090078480b0f040010b0250415044442420426a0005440d85841e000f8181c0b001301080040c090744400500880c10001075240080c0c0c8140d15010039040780040c45040c1d820700048010140c03440003c1e601c40c50300041c01101c04111a4a0400c58001d018000c1c0c0c00c20030f81c1784c00c000d4401e000e084102d00c151824804442c40d03003649991342c015010420f40025 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 594695566 1250 594694316 594694327
    0x30f1006050f180f040e030c150124050f0706050402150a090608190f020901030e0604050303070804080702040e0a03110708060604020d180b0f100302061804060b310506 74
    0x20602142100040c001044d082d101090301d8080350968000c8142c038800e6030000710f46609504003c0c000e00c00d403200c10542d0501d45604010f684508c1c003044141085118400144c0d0485040c00345003101c546501c5142032a403a4000e916181004e4441198200c0c025510400c410a41c4850f00080e60750348030894851004031400d0020455980030024500458201030100700700b50101d1074030030300c490203000302c00c00340c0e80c0c4044030000f50688400d1810300039603500035000c1101054010060f43e0b04140c01c0d00d42800b507a125070801c9902d41c02030b0f1001942c45850480e00c02a600781c00900c00480512a8a03010304181004105503118819846480301a030020000101c080c9400c0d030081c001e000740b083c80011680c01031b24440350320882904e01200d0f01252071003445413002142202d540d00c039042d0010100d560381180d012504a0007050b4031060400361100c00f40c0c40c159030b0f80d080760001d0700340f5203c01f03500d46490101c0030b000c404c88080914000088014204550f1071404500d000b41c505c0940010b1a06 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 594696816 1250 594695566 594695587
    0x1051c0b01021608010f0e070e1515030a050a050604150e06061e070c0e16120e0d0f1205060603192406030f050f1305030c0102030f1006050f 62
    0x40403460100ca04600512541850041003541488040c11300c1c1c5000107107801c21401c12904481c014181614a90310400382044031200d0360a00320b41c084c140410b807200300c0000038007280292005030314440007440c010041040c40c81095119a106142c41b15003170041e912082d052001303c52040c1e5500041400200c010300126580b4503040c1d410480c05403140345000c101c07000c800803007082c5085614074084005040810702c540ca040c803501416840021742c0d03040c03c00e44900c803100400035503a8418007115a24000c00000c03a035021080c40da160304240c0303a5a0b485108024001d4141c1801d04010452402004140d94401d01c04e40d0700c540d4014000300e1440e00c80084a4076000042101c40440740e40754400113031060002800c508403001044000c0c000c0c1403c0c50307000342c1078504a9007a44030080c0360004000c4001c110541c0140c210906850350f58141c0043d060450561081c5080701d08107600000034400c0501e41c08403154840c0c080010305c3c1c100c0b152200d601b12440d01c107200410045400500102c04103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 594698066 1250 594696816 594696821
    0xb0709081c05121e0f15010e030109050105310b0708100305121e0903071403010f091b050102030301120b06010c2112062403090f050c03070501051c 65
    0x140590a109040100460418240c41021100002e42440c01550b05681c1c0c3c0a005000da00f11107240c811411034a0042c00c01561088440c2406c4d0400600741c0c44071600d91403e600071401207410000030703c414a4038a88203690b03520f101e498003030040c50301000d050110120003030f01c100046d80724106801645030484d00321174000001d4444400c0301c03514580000000c3e01080200c034141e0611400c107441c3e6043c14221a45144040c00403100700104108d000300c0cad96400700d005001e07101d0f001c1011510a040001090040c0320050b0140c40b11841c0c60180700900510b41391003192420501480b8030303c40d84900c01241c590000384603032034030415408101d0b800142c0501825034091018545071265159540710005d20ba070a580c50480c1d0f81605240345074141ea841007682c900300240150034826107180880004d42c1c1140b4520b5400ba0542c40306000d1f03510f91003a00645a59600075071002c420500f40c4c10a00d888609020f202da109100d9108005072550003401525140d40400c41030b1135104100d503c08401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 594699316 1250 594698066 594698113
    0xa150302131104030b070f09080c090a06170703060b030c0901060c050c040c051201270207050f1f0612080d0b0d021c0506090601151121070b070908 65
    0x2019403280c03120454891002c010348000e50180742d0b6015981001d1030007170309400030380d1001010880c0209007809003940004182444407410b446989659a41000c0600103040303a80050081100d5010060100d9000140220540c0d00403141001500008410035079682d4900c007005411005c07840040000a000e500b142003ca4002c800b51448400440002011960400c0344440460000700342c1c02d0407040c2005459000d0900b00801c40e00c1d1107485041500e4824202c1070400c1040d40000792242084418891103103a09a2101141e0384481c01f4030400035504500f01040100c10701d0404002490030810000c528021303000ac0303003e403518079400034250180600591907074000c2000103581d401a11114541d0000c002e1410f107540c0448018948541444005000c01d81d081e4400c0c001071010810761b61010180e002c45041a070320711010b83c05841c1c1010940710b030318640402455045401e1342540b0300180f42440c802c0401806598401e2000d9a142c0c10a00504203503a22512100002c50300d03100d80c800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 594700566 1250 594699316 594699349
    0x6080702030717040320060d1a1801030b0c0a09090e01020c0d09170102030903180d081606050708130b070507170711100203121005090703140a150302 66
    0x2d2402c00719440302ea5410032140c00348080c00000080070004d01c10f2102c145101621252010b000c50f020300b10000324603004403000030202558a1100b0407507030000c4403040b00d070850040d102c00071800c5030305810000d0f08802d220645000400c1c1000558604401089800d141c085498000406007024048401403505c0c411240180d0340c2003104807000e40c010401d003801001641e071240c0ea01410400b040310203050404003403c66a005109028180c8070200c10b507540301c00641c0e0030b030704010750380b01c0010311543c1d1801c0050302569001441d0101c00c20080c40f01c01c1c019024000900c00354a80f110201d40710b580448002e40700d0324100507150b001034141d0142a03084903445c900241800700940705c404944d65150b000f2071145a00003407440800074003d86c03841c100c401c121140302c1002e04405010b500c83c4038400c60007001c140600e0001c0c01380c08481074020040c00700503100070b41d1840c159401a0092000700d040d8100410290700060384000b40b4096200649210803500c5440340c40c0d9404d00144242d45681070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 594701816 1250 594700566 594700573
    0x1d040603060213060216030201020303041e080d0c0e0d05060406050403021002040f05030c0405010b1801020712060b0910080d120603080c060415111206010309060204090e0c03030c0706080702 84
    0x4a545800a0100c0591071400d0f025810300c0c0c408040e10306040e00a16407514018401c0801c00350380c020041c6c03503029030403200480b142000e00340400c2d90940c003032400a00c85100890302c1000c0000580c4418000703174694840220034440c1c03000304005408070100003043c9038082000907000456541049803c07520a00442e9020050b118120080c1d8100f03401c0743d400e200e44040300304198502084000401501600c0400165042610103030891280c8840340030340034041218800700e64801c00400c00101040031000b02c640c1304502e016006020702c40303402c03441200c01001040e1089803100e40e0f14116a00c2d10014251521007450580d40b884a20fa0410342035030340c410000011131000401071848000034000b519481c5400d00d04a403502480000e0000709a02d84548541845049001c68604031150101040b03295501001200684a10f100c018842400498001041941604a42a0860f1040542d1080f40f5401e0074107603607003e414454043d80d4004a0100004c50064406680000c1a44150f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 594703066 1250 594701816 594701819
    0x30a09021f020a0302010623011d0a03060b120105070203221503140106081b181509010201140c030406090201200d03050a023f100503060c0a1d0406 65
    0x4210384000e94000000940c1110b0380f0001056820b2180c2405001c20080c1e00f000e160b19680200d02c589444001c103410300100700341c0c03084121400c20014205c88401404c0c1051180c6078540700c4044c01c516112140102c8014404880d048018081c01d4491400b0758003c6003000025400380a40422004081315050f00465000c5005041d08441203031000380768801043c0504101c80185101c40143d120380b003009001001c0c01298400c1140044c18040158034241d00c0c0c141c45030580303d480348011000741e03028400f07907200180140c00c1005004030141c240c008110404841104007088d01c0f048a0841c0c20203410800600015500d40c84592180e00615140f0b900583e032020075154081035a0058089901010410139003e605028442e482181e81e207080d070824400781504440390185000e00390070750780d07412900d02c4901281081d40c0720308140c400b405a000c1c10900355504c1d84c2c902c139006460081c052040090301c40034100d4101c4029203ca583d0300929040d1800c16440c0c0314484041e071503441074a4120 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 594704316 1250 594703066 594703099
    0xc070203030f0702030c1210021804020a0215010506070b040605040606050628050703050703030c0210020409050118090503030a0c12090b07020c0301061a090609030d0903170906030a0902 82
    0x6081448040410301d0750710103c500400d841c0890850700d043c841d140710107640c00c008002141c1408076619214000d601d42d43e041c02e100c000d1402540c1000c0d000307031000c02d0b4584059800500246400c0460702400c50590300d90040c8400381c464080050540c2144101050000300240e00c51640306005050018031151100c0001d08154070001c0c03003000c034031071120160320a0100030040700250030503414600d10300310550754090840d00800c9005424107070350710417107581c0600034000044000d031807203001c44d540d645840c42000101070038000d80990000380d084a904442280c40b41e02c44642d0030078020360071641e80d088400d01620340c0340c015904010100c0d2840c0e8061070140280600b0300e229051000951a102c02c00925003615144182e21036810701c10b04001200350885491040d030b60340400c3c00c1c1d640c0a214049078140c4103844000c1d07054481c0180700b81348140e11021200a50303102d40764100120700c40450200c0540180f080d510392201040020031505c0c1c1c1194043d41c55144040c01c0d103480c0348807184 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 594705566 1250 594704316 594704323
    0x304060e06070b01032303042d0b030115121a060c0a060504060501030b0f07090512120307170a02070510050712090b07020d0c050d0e130516030606020609150c070203 73
    0x1e00442d0b140d0607081b61184043c02c40a10008144079002c002c41c1440c0c5080c952100d000c41001c541d4410b0448034000f01004c0e03d40c582640c01801300e54241c03c4ea2965581055808110015414800a0851415a40c0005032406251011201054035260a18a0108000b0964020348452007584031f0b4441c01400605140220782c0720724041c4400158561446c2000e41500b00c00400f50641520242c04100310a9040035140003500d00681e07100d400a841040171520f000f4140c045c2a9901e50044100a000c55000700745080400c4100715140d03040d12007450300801c0e030283c96001000c540040507005002c0e04507134400e5911150518000c813403881c290024008948200c6401e4803264a01001c0104c01c640401c40001c0809041c60701005d90502c0da200d40e80c0380d01c3ca46502d5410030004100c140e120740c0d0b40380c602401407041c0340c00402c4503051001c000c0c503402c0946000c02c00880c2c02d140002444030f00100d4864400c25400c809040b488000c00317540440b1081c020480c2a50450a0180e84056181003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 594706816 1250 594705566 594705569
    0x1324030507051215010906020c090c0a020304050603040501050a0e0a0b013c03030201061202030a02060906190e011709060f0406021b0705040e03091f02100e0d110106080304060e06070b01 82
    0x403000c1c135405101400051629074290003080649d03014000800d0241c90f140c2c0010381c050114801e240c2ca80000c50000c90440c402d03030f4011903001c200401440144941940000c2c0185a801810884c8201c034050040d1195540d13a0080c2000360340c0300c0100160700d0100d001122050000b407410b2890101e4800c5042300560a5600c032240c078242d51000c0c803c050702449004007810041980309610201e680c0081c0d074940a43c107000340500d2010a103103070f40781ca900c003d84090040c444410840700984e000000c18686a500106000500384540d04200c1c1c1000d130b46203401250030402620940c0c0c0c590b2142200c02d40080c00440f4440c3d401c00032082001288500410072032540406044642e18000400050b281d000303122a04540041041281c103646000c8607140041642b017a40b0401c1201d03041c10b900382014454100105400c24a9601c0f045d00c0114021004e04100d403581030760060030101a80c00c840c200c0c002c1c0c09042d4130802090113001d0040d102a200554000c00f8240b070004142e0302e10241c00004e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 594708066 1250 594706816 594706831
    0x30a12140304050a0309170304090f02040e250302070809100c0b100521190c0f030f03030c02060601270b040b070510380d0813240305070512 62
    0xc040c01307820107500201490081c0a41d140c0c0844004c1c3c0c1e800322640b64840e83c852a8007041d9900400100c608917501603d0043c508449922524038048940c210758420045000d4a540c08401c02800410b000c0c4c401e03510131070380258200341030030a58030a20030761020000c1d1107002d10100e8400c503800144c01000d22407041d104052401300c1c140c07400080c045800103e0300c4980411201e103d903108004000a54400b1111000c10110710307090f014200341c50544260381011075400700b0842e002c01071240000321144518480e660030003804d0340078841240c4442c002c0d1509800100c00020f581d103246100500c40f41401e0681c0c041e103551582e11010714402d80d21035840300b02802e5003c03d0245c1808014440c105050090510a2141161100040038900c4094413841144210301c0b4121b10141480300d00c890700c08401031700020800b8154145001e1580000790300d030101c40340c070322404075400030348075480801000c0d06844000184402c24003680a050014404000c1100511005850424526104c2e000300070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 594709316 1250 594708066 594708073
    0x406090215130509013f08091507050607054b0703080c0307091e0e0a1503080309010213270b060304230703081b0c030a1214030405 58
    0xd034401d007858210b00f603200074400e803003071801044014600d081c40f045105444c00250000c07080304845c0400203041840100140904080a1080100000017040806c40c2121206a44070884a002d102d622903002c00900ba034000d400420000b900510181519454035101e00c942c1250180f0481c41d81e035400084d0010030942207001851a0020390201d00a1082c3e0010b00c61800c005ca0b2005824420058000b14403e14000b000840b82803160502c04060305403440030600000203064032040c074090601031400c80000180104074440500d0ac40c011400c6100000310380582c6c5580c440352501c2d0401800308200703540800003000c1c1007920043c0705024008601070200240c1542e218010702c0d81c2c5541c860401540fa02c42d0a01c034030355464060302e5100341c0c000401c10090341004000885840341c607215903079510921401004202000c0d0240c40c11503030b1004a040103407403144000d41d5503000310780c146801d508510800400f284442c41e09010490360390030312103030020422444003c40e1340212810780d2a40c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 594710566 1250 594709316 594709327
    0x911150301030b060114070311030f030109020a02010c1e0503040c0510110d031a0d0c150c0515040f15021c0902010201050f060a0b07030e0402130314150f0406090215 73
    0x3550b0f125940101007807806000084074120000201d00c180d100141c24082503903e01c03102d50710300300300b1204400d08030311129840b960348000b00c4020350007203040701c00507500b80103216581510a5080040844607614840030101a030300701070701d840e800038005440a43c1181d00c0032800d9141c004121100540b03580e100c41700c103516400c819060094121440c4101420310725010081e0300c402405010302c00d01207030b0801c1c50b4031030352606142d048115801411610000011030000781d80012001003414020340035240c0300c011505420401020403680201140801d03a000d00204011345d000400200809000525001c1c1e264050b140c0504c200301c50034905522031901a04659081c0600f5800c13806401c2010719074101400040c403c0c12041c000c0e0342e0995808500d540925100d50740500d651007016104540d01c5d401d074040f41c000c400243c0825507000304240c01d8803254040004d60b408000105400150302d80d01c41c2d64080601d890f010b0410b4500340d448042c031030302594802c1005c50484004036202507a69 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 594711816 1250 594710566 594710573
    0xa03050f070603060e040b060f0306010306150527060a0e01030501200721030b091806011a180d0501230105041e090f050d0203030a0510030203030904091115030103 72
    0x114003034002d5400c05003000d40c1088825943d0000d1070300079600c1040340a0035a1514046802d40201501040d03140c4512000002030003481d40c014144141c0c00005010903544070340074085002e80c1c0110440c040e030704500324041c0241c0c4000300a80c020100034a030944d1b82c0d6983c07403040f103d81d1007a0005d45160359641344425105c0c1a5511a000b1808030410640c02c3c03620680703a070100492423103030252100c1e01001030042001e2095021407141d0800a01c0d0710410b0a20b001d9000c513040d2244c264545511a21b0008640c1c4a19000c941c80139083c80b0f106145441c1c2c01c03400001d0300d5009156901d40115003e03030001b002583c03c0c06115041da48280340304940500340c501c008440c0c0d2041c0d11850003a80381040d42e00a003003680c40f1a884440d0404404148007000b0310703244850300c15828016116000700d014906c0c0495010008600903403100000b4482c40c6c030741c44581c1041d110940310003585030b40104000062814103401a405150003405591a00340706100801c506e42c50700214440060400801401003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 594713066 1250 594711816 594711823
    0x130f050313210303200a110c01110604240c020309030c01030b030a03080c120c030f0106020705010c0605072a020117010506070f1e030504030b07181406090a03050f 72
    0x1031081103010714008070444808480c85602c0070000d0700b01034880400403a0303c44044000001c0e18503480300c2c95510056034034002e00c20030455015165a00038000384165640c031901312210000c0302c42c006815207807204d907030303a282041c00036182c043c2c2868444a00008010382e44038011b6100302ca50055581d8107101010541418402e0450f0380c10b0503c1d04600d615141c1300012043d00e0742d07901d42800ca02c00c0d2030f22880304015000310044415007862400800c0320a55084d0080d50040d5500b400c9450a642c8030700301642c03190725034040d0900003100c3d012804041035054000582206a600b8240440c0c90040061542d1180030380480c046005c8404020f011540c0c4901d5101c40c601c440c9155600950400f80040c4007445008009000710035400410070070700503811a82020554594040c0c404031007940741c042c0641c0c00500c401d039a9414041e00290607c1d000ea48040c8500c840d014036848000e0501c0031009403c00d0141c0b92980104050090a549031101d6602401550154000f0040d0004984a0714035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 594714316 1250 594713066 594713069
    0x140601021f0902180a02130b03010308160204090b10051206010b07060c0203040810050604141905091213080705030f070e0a020f030f0105030d110a0b130f050313 71
    0x1103600040340c070080e10031038590001c08070003081404914034006000048003514440343d10114000a8000c0c4010380c0281d900078950a80c005c1e080946059a030018850580004d02c00a01900c404014021055031403050000717040784000c1c00011645d4030790f200e4040410088545c200c10b81e56000c03083c029450981071030214480d2680c000e110540c1840c081c81e48034040c1d00c0c40103003130580b6880c44054290082c01a20f010700100350072100940d02c207641d840090721099449034000c920741103111424945440380c07941b180c0b40202c400c28030304c00074003024001007500a002c0300b11401205145138082200e10300600b080d1b50403d0081610707608004074142400c005034411440f0b0362120079800c502c10800b05960f400c9441d6810072840e26500c0340c40c0d01c0080d01c0741d10007041c0d035142c0000c1040131080c0c892905605880c070035800c0351100a0a20410359181d1440714994005030b110300c12010010b803010000c40d602020100060380010300b0303035541100402d481041207600360404544111054a04100c140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 594715566 1250 594714316 594714319
    0x20301050a02270303040810020d0c08270f10020702280b0708040f09020c070f060504180914030406030b0f09220212010f05060402030903042102040507031406 70
    0x14600011000c00d882144040f005900c0444107501d500007a5641c14002e4030020040c8405580c10070002c071300614001c1d84401200d007e464a0540080400c5106862692007400c2d0b03602404d0110801c00c407696117800444880e0111031048a0300c2c00c440e0002880809900250b1030000f580f150742c075104100c10020a001c041c502180d548401c680244a240c1c0f42d01c0848181c0750790983d0b5071242d0f0500404600c201e40011140081006000519000030fa004111803000102950401c60321030010343c0c0e0820052041000180e020700060120b0340840d0466401021401030004103000740b952455216030081215071515080400c040106070703018041d8481c00705040f02c4090800310007100040c05414003811505441841a4020400d1b400c1c40c1d414814481c2c0007003640d419002c0049946010f00001d0500051050070f0001249803800d19000742d90241480e180594186410840c503110038032010305036512540019002d0b50f001da1035510400f4014a280daa01240301040102d864204900203030909 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 594716816 1250 594715566 594715571
    0x603050606033d06050417012009010c06140103050d02010603050a0809190803030106030b030303101202031005040c0f080c0d02010f05130905060a06110303010504270b04020301050a 80
    0x1020340c000c207183c0c0b1050344000002e07503014600e82c400040d250202c5407600d403549500f000c0401c3c0c85404c10090300440b520007141149244034120b0036800e03100c2e03101d5560443c400d282e1500e04804a4a00500361041041c50501104241c40c3c80b00819241080410710060200300014005d1000c14050801005400d0009205252656840a0b0f9540c00307004058001913020869810940d556028507000020510440e40392036180d00c2c1140d200d0303100b0311810010915000ca06032280c14040241e0340f003014180e0100000d603141c61040140985000c000301da0500030210b500703031003074554810309d4003950088103034400443c20002c2e0355520400390307088000c06078030481c8020700030394865007030005041d4203103007629095a00c030034244d41a00915040884085414802051180f400c0c2e03c81e520030342e4201c550034116079030380806403460180484e41c43e2498100300018401400e0a800035105410b0404241400606407504040320303001c242e80c1103d002d4280070500082d481c0074001c0301c1d045408c52404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 594718066 1250 594716816 594716821
    0x51c0c0e030a11130608030c01150504091109180d0c02040b0d0b060f0a05030109081905090303040b0c1617010c051306031e0c080712021c09020411040f060305060603 73
    0x44841c80c41d043d03035140c0c3c41000c500380b0512003030801d500728600514404003141e8403040741103c218040c0c44010611005122030403c00995864070303004540359180c01007c104500300e2004107000d00754030000e2003026180d10424003c050600e0800aa200044542d501c090b000300c0207104102c1030301c0c00b482c11070b0321a0300c28440700000301d0030b40454140c100c001101e6450000e510b0001180c500030040d07000c19459460a5480c1e41444500c400920012541180fa43c402c0201480709850340c0c06000b6103143c00d544240400c0c03041d1040c80c4000e04000c2580070441b5100c032111007c0036030009064202600c07074800d110f11442c000d402400703120254031150401608040b4411a01c00f00050703140f20341d20400d5251f05001c2c0c940d0f41441c1c41070484e40c00c000720070b102210350488080c2080000761240700004054200004c0026618401e1301d11000c194102075400e800101580030203005085010f80e4410364842d0795103c600303000c3c0000e0006003040c1807030710169441c04001504503000101101d0180004008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 594719316 1250 594718066 594718073
    0x30b010e181506040c0905101110020a0e060c12070627030f1d040603050a0c060e06070b070e09070806120114010e040c03080f091f02060402060a051c0c0e030a 70
    0x78000d500200940e0000317003040c61410112072a000c0c0f680550b4004040c6405c040030381da4446800d8000d2400760b82100c060202502c00d0804070b1082c18a91800500c0405c100c680a05d0064005c01800e40d00d003044034a4410039078500c2440f5400880226451540c44258080011100c1c10000303035840e604181130b1510303610344c034058600b14040c0b90f2982085504e403540c400d401000f51f1400910000034008000c601d803640f402da55501500c0f9001d580080100000162442c81013041584000d0090010fa0400356140c3c4d4040e074400f4003910800600c003542800152a840b210340e814420780b200d41d40c0f811141441018014454043c203c00c11042c4d05007087e0f456480c29404c44a03044810505001c10665207609000070840d82030f82000301f02110024001c59000488030280c24188822a02d2130710110300c2c000800e04c11142100201d002d030f084040000c01514018020700404021801c00528002031071242030b85102054081402181e919084260340b40d60009407017451480940090001203059217 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 594720566 1250 594719316 594719353
    0x120105090402130f151502070e01031e030528090503070b1e090613150c0f02100e03011817030405030d090c2c060a14010513030b010e18 60
    0x3e41c00d4001d80d00c504c20403600d010203a10001c9180c0e401c52644420548821500c080c10211445510040c800c1c0300e40810303034002d01042035048030b07031080d541c1044c003012902c0400c03003d60b01d007c20707800d001050000403041039400103c10f00b40040c54070b2454002c2d01e071000c054110700c1d681d0031045c042da02130700f0140106141041101e080080c0035280041088058294102131b1040c954a26040350000c01c0c1c600c0301c00880108842560240581c1d004654500c20b401c8070041903064020309035880c4401c0c0ea0015092105110401c0f0300140380c4010301810000203e070030f40b02c1c2c020580480d046041600c1c0140039030145001000010b840c001d03851800c02d07850701a50b9004803408091501c2ea9042d10004020180114000a018001c5409800c8142c580c08449241820090308a282c243d07c0000d6610305e019080e0034156012121051b01d180018001110705800c2210310070b000f400600710101c0461400c502e480d00808600300c09840515206101e0000300c0c000c1040d01c1601c0d40701c418040c10000707030070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 594721816 1250 594720566 594720589
    0xa14010210020306030c0607120e0103050c180d06020f12010b1204020108090f0d09081e030a0513080a0c2d06050f1b0d0e030a02030307080c0a06020d02120105090402 73
    0x70003588a4951400003801d14a10648569212000042071007c02c40c0d0761413040346401c00c0f521810752107607510b401941070702c000701e4020155200420400d42d03080d1124181c5010290b000c1c016010320282550703034030700300d03071114055003121100818005d111502401e0054090010f5400c80e600700104401c02e140e031884040c1000f4140801d060015a800c00100504c5100d0810b01c4114bc12000032500041c2c0000814020201e4901032000203c074032407094840b10903010780c0000114901659010221601d421504040c1040351494030300040c0d6150420001e50254051107100c24460f1030711060300780c010101140c014070b0300d003460704d010955600c800380e400c00c4a6003801d000b03540e032048141700d04191040f020001e020700ea81624400140500050102d8060001d840b26122078281c1b008040d92140020300007941940200801d0000818420243c03030070200000894440d0314180e0b5030700003130f60000046120815404281030000810a6401d107005042c1a20070040904154006c144072803041c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 594723066 1250 594721816 594721843
    0x50705150106181d04022205070f1d03060a0c110304091b1e1d0d050c0321030610020a080a0203120a0506030303040605040213090503040f06171305010f1a0a140102 72
    0xc18682421240804680415200264010021413400e09c0c0003070980030251f5107503400a241c454100e6500402250a03a040480007070080206589901c411401303488101040d804000310036110100303102d01003000c2c0c0080e100fa400086038110f5803002c90412603c680280100f040300302a120b6408194110840c00c10f00414503144481c20b10740b044202c00165101032072034021100b408844244000800c0181e550002181070f00c03091945c1c509484282d214071150b8406447c03040001c20340620708400001e99003015401500c000a00d25100c007643c0360880169400580c000240200303030790243c030450319440780110030100020304190011175a00d020040c0000c168640e1034002c0390542d681c518100e050501d8001d400d03c81c030002d51510f45c0d1250858451214100441280491400c1c05031000713020016194800f0361030741c1e598002c0d50804c011003160555030b5540e00c80380b100000e00340d400756020318400c19211428680541080c0010f00301598440300145040c19051007450380e001c524035504408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 594724316 1250 594723066 594723079
    0x3060e28060b0d0215030402031507020d0c0c050301060f09060503190303090219080a1b270e0304090b120d02120705070e01081f0b060406050705150106181d0402 71
    0x2031480218402c5003c08030040d610034602c11100b4030141c50301c8000e501c035903c2942949c1080034610032034800200250b40d52005030b0000c80003200030522810300d195406002e1030f81340d1402580d400100e82102c80a42006c420404441014000070b0901d008250007030900350000e14205032030003602c9880803078030b0b1070003001c0640310740908080d555459070501940d8001019544070781d98480d151a0b444c582800121900c4000c0135492408a1074410a5012103641c15001140400311f034142c65014034440201c0d021095403030340c240008140400142002d402e00750800100103455408004007908080344450559000c0d4101c8100c170796010610190300d910001826440d0000b51904a04142264024a03804480100002207034140020700301d07d85101c1c1c00c5c82070f403070400816070130082d500b41d110304c1900104d0400c4100f103154072680040484501407002e540114492003407417038002c4801e038001c0d400070700c000340885400d041c6a1008070040000d07405001d0b52004101d8040e0303070824010406441110b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 594725566 1250 594724316 594724331
    0xf080c0406050f071a07170405030d09080f0c01090c05060a09090b030109020603161407050a02090c0409050f0402010201051f120203210c06010b04180b010908030403060e2806 77
    0x44020042d540b070346622001445144101c0c5d015400c04000c1141ca80c0b00289421500d0b035050030b00d64440601807500300c6c0186260084c0d400f400c802900d940304c1e04450b0101f0400c8110340d500c1015010380151101a0000301e0070320350a050401c202c00007900214800d9100308500c06040d5001001c54007203625046010512030030140000b801800e200d070700a908460000704026200c844603803426035541d22a01d404071148102480310015001c1c0141c001c1c11079000030200d0001d89004400c3c41e03400744401e07111038641600c1d00780341000d8500c10717501c40002f0328440051000310743c0c0a000b000c1e884a200300b500601101803400c1d001d29149540320340207991340700e156103205540b004c1c016034010401300c440c100d060340b080c10742d00d04031030b44131516826180c0600e00c004100c0b05002070481c1c0860b050348540c00c00e03003207241d14064001c2c040118202d050100036507000407140002d0005c0c00c01940074440004403100031350740580c20b2810143c0c1068140e0646240c6800e0004003812a408446d0030440008808 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 594726816 1250 594725566 594725587
    0x70503060f060d060f0905010b0a0906080a2306031b03070b0f0403080406020703061a18131202013315031116021207030201120b0103060b0d0902010f080c040605 71
    0x188034120030030346610701301800030900446000d0040d04a0340c08036001c1100b6a62096050154060075103514001010075504110451181c50b5107500105900e01c0000e60404c860b1f10310301c60b84103c584d00701880740c08000b001043c1c40d080c800e401d65900d694603e00302d48106040065151042400385982c00040400c400050082402c2504c010703681c44810590390f19242c0602a5131144c0c1c52000311405400c29480843c4400303240780e00c01c80e205000d03140510310074802c0002d00c0d8a6000070309401201c100009550b010078070240c011140a115500001080203a43d034011078080d80c0303110100b502c1107003c00014a100b0f603500400007115010074400142042c0940704502904026a881521a40226140c55001000c40505c90100c0c800c40320380c10861809600c86445181a210190106003003403144940007600f9007040180680502d0005038054a60042e521150003949620800070b503104000400c550700951407070440030050520030054034090840080c94401c50003084200030001c180104030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 594728066 1250 594726816 594726829
    0x90201080f100b181206041203020c0c0631090e030301030512090a08011505040516020607030c0c02042906070807081b0f1c0f0c0b1005120a0201020114070503060f 72
    0x904d0340062104031030041304040700750354040035981515015002c1c10441041400b1344210789450020300e020f4102030212808112031600a2020503016012384202a04500c0c0540d01c45000d0340c400075100d27141039050403001011122000c0071b014203a0b000300018004200c00003200160781660540c03150780e465044002c5414910350364080c0c3e809600b0551f80f915080303209140e55040c6c450a1340c00300190f0380c5d070b01510404000d4440c0f110002d600098045040716129400c07107000681c190a10f1000440e40d507012030100c2d0300144842d20384180c20003100818142400541a1059084072100e043c03498540f90320650b44910203000b400740c2400166441d41440058000e0003120080d400d940d41d40750450041c0303803541040304695030200119410301d40c00034080c1040100b000e1596036801035680941e13903000300025000d40050b02921078403100156503900c42500d01080700100300980380c0340d0761030302c006402d6850106020b8a04015041000001580003040da54841340c11245100349100351400318a1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 594729316 1250 594728066 594728107
    0x2070606030f03030204080c0103020a0e011206170c03160302010206070c170c06070f0207060e300f0105100e040f030e0405100e09030f04060f02071503090201080f100b 74
    0x542d1241c0e03100b60342490303016406082103c14040aa51020030320100441c124451815601c000c80c0310300301c01d44603a510030b44034a2100c0401500004403161203443c04030b58892112031a041541c400341e509081400d0a005071801c400c1400001c4501504590010b515010010b1200b0100309806c07030014180483d9203420581e5041c2c6c1d002d5140e070348203050030f407e40340d4600b150500041030303011070314800003840020701c2001c540709a07880f00140c6980301c00700240350700408070580c1d140907240800c9601a50f000048645405800003c000a600303038081c1900303581c0c6c018603654500b00040000c1040340d00311001142d22640c084c1040a91140078a000c0d10034070049505240c1103807a050402440f20a6101d502c820f0350103a900000255075003616003540d0303100d440c10000041c0004e0000308607940c0120150b20342c0c000c0d580180c0304250380707588080c90110851204900080c0c1c4800d917083c10741d40c10030b404070b40020307056485050505c1d004902a41502c801d1081c1d62042c03100083d07940d420420805c8131072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 594730566 1250 594729316 594729323
    0x30f020f1c320f130b0d050906010b0a1103070c08030910110c131506110c0301060b12061c0606090f020315010e0d060e010e0f06040c0e04030c02030114101202090a0207060603 77
    0x24400f0b1744821006030035030800e4051980b041c0c540808203140c40800201d060481306c100c81254a40745500074112151001c0a104c50000d00c014003100001440040b4141d01425000005640ba0030503541046402c801a5425000f07011442c681110485000f086040310701d082030b0360820781c510550502d50005c280d000f50301c20004121040101c0c034194000d00f0410420070910441d00424803400406003261103034402c80203000340409c500c00340340007170071200740d803140303004083d1070317860400c070300e01401c407489080c421140c45070344000034805906184a075440c0100b001000b1421841d081c010700e0040c0c075442d0945414070071401000300d070750380c1c03060b99600605a00030700500000070000001030213050340c80d40c070301c03054000c1c441404804d9600041c1c3d03512803a04035a000146601e0081c0d0350703208000c090001d0f002c104d160702e15200076031001d008031028401c0000c0c080d01c1502d48246440c00741c00c2a600418014000b01d0460300c00760380c3d04907210341c00c045502401a84c460080ca8848000c0601d0b0780000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 594731816 1250 594730566 594730597
    0xf011b0b04032c1e0105031b1209010c0f0e09070305041103100e01050a200904140403020c030606030c010909050c160c03032a030f020f1c320f 63
    0x140403c5024040340b8038034800503207071084c3c032410348210101e02c10744407034100380052000d20005005488a42d0411104071414405529100c0c0c40c520f59001100b0481ea851031380d80d12983c000e00c64980c8040c0c416003205031450700c007190101000000700b002902612806c20140c465000c1010301c184118041c0980c40b0041c00c5480100071848080b002e4400040c160b440b95103044002003104180f80510005810003a094942e02600d0a45481d0355411040140390016030300c02c1000042444207281d64007031402900101481e2094030101864008010711907070081d0880545c00c074069800034000001c1d242c800001046035641c0340208800342c080c0b9030681d1700c0011003503149030510880c04039804c00d0f02d010f5911108402480300e521030050142c22152103024900d0412a800300c0d11410020016501034070603603062000742c00da860301e801200070100728200c40c85624510507d8005100c0003080c0465003181c0c0811407a81081031403c405500f2100c40400700050801001e01264100c07030702003202c2e5801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 594733066 1250 594731816 594731867
    0x7150b100f0201060906080309130e01090f0516030b060402071b0f060f0503150409020f1305011d0408180d0501020a09211101210207110f011b0b0403 66
    0xc00407510703041c02101652a03d60080740540c2c541c0180707019205440700a5240c103201070180900c0700f4400550300141540d0f1407041e10059070a0080404684c000d4414420030540b909016080540e4850840e48510703c0030800c10000e008000c0060f401907040b61f0050f2600d029080c080310303084c00303101108030303103554000081620440c03104594140c078116900daa5540c00d40080c00e84052100340c40245480300c000080b003401e4035040c0c10900815101800c01840ca9040201044030320019229060003075482d2001405542a81c00120040003540001d407481d605181d01e9140d0310f4400c0c01000380403050100d0100c9140d48038801c0504560340e00000846d40c500e0148001814901d0740c0c0180e2190410190880e8521410810321900f540d03000744216480d0701d846801580c02c100311217000c0040a003004000c01d400c64041c400303800d40d00d00815195020090800410001c2605d041c0994140302c0c40700b00000051508408806026500101091594495040c1a540f041540d450390700b0b013403141400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 594734316 1250 594733066 594733099
    0x2240f040b03040b0708010e040b07050417010e06130803040b060a0e0403030e210d050604062303060703050405150604140403110715121a06030424050c07150b 70
    0x45110328011030113031890344c03074018044807501000e00c5244603a007440310104001c517184d441419081a02420f1140c582940c0301c0c400c082000c0341c0711605c50203035503446900b0f645000601415600450f260780301004c990341982c40c517800d400050710240c8420391041c005811529060651805003995034541c041501d000e00d00100500039440c4401450700541590004407003190030f510070012511240f490510b800780f10b03000028000245043d034040d0321a8000110704243c0300c04107030350300402c0f0108130581d07101809140c540040034001004240c48c00e401c00c1b01007040401e04660070220a402c044c51a20390200060162181c0d0403292415403902007032200b016000a000c5200c410700b001030741d140654542e40c0703c4615000d07400d5600401c031000c1e0314800411041c0c1c400710100990391032100c03880d070b082804540150000c6404a5200d41d00101c25440a104510345403200e0607403c10a10103854405404e202e2802104001402850121086000140950440c8001060142051407440c00c801b5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 594735566 1250 594734316 594734339
    0x60209030a0c170c0907030209180a090308250531030317040b070c020607050d031d030a0c1502120703020306211203180304141302030402240f04 64
    0x100c0c0380b041201c480220703d4036000200e41c4032020b207001032403825103540b0b8203400d40107540902a416400801545424846041404202d0240b5200400060303030007411729000d4a2140b000d881900680344201601a41461412200e4080300c1d06182803601c5810858010b070002006803140008039024503580000140c070041024200c81c007e0303035500191242102c802502d84000c0d24060000ba1030702c800117120f00d004401000c411480545804e1a00e845521501d003801c5080d90800000b0b030700d440c100c0550b12130000548030541c0401c0c02841c078180f0394a40c040c280c003c40000090481408070301203001c4201650550f2614010034083e0391591a02d40401402540216007407031007040c03407032002060402d00c1c40d40c0b200740313000d01e0005200c0b00c001d224086a00d40c1000306407051842c50b08540c0e0140c101c0a20142c401003400b040700c0074030100104100001511f00c00d2110038030310f00c180304000c05a52507400b858034800b101c6000d002544500f200d40d4a84d407007200e4162030041c000190005880c02102c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 594736816 1250 594735566 594735569
    0x705090405010605030601090e4302150a050601050c0d1e0302040f41090610050d27230120390f0d1b060209030a0c 51
    0x3200c00304001c1e80c80c0d2030252036501042c0c07002030001d4a00001441076041c0c0c40c000ca40c103c08103280781000d840c90150854280e4080d0f80b0341411100302c2a036950401d00a0800080c548130460002c0c1440b9549540010702c8040002d09144500d6114400b09106074011411070b00c154114806071014036420780b001802c03502d0441c400c480c0152159070803c10842c8039209a50075036102d50a0141d8082ca01200b0b2030100000da8810605a040400d0706107900d003440200d110341c1502c0f450300710030803040d80041001e450401011180252512004803640c1540401103e40c03541b00e031003002821a0210b04007070710b61000200a03181d014031510b00e81041c0602d00224804e20022075014241f10050480c1181c2611881d900300c01c609080c9640225a20000f20054091100b5901d0716281f82c1903248900d03181d50080240380ca8a5000510b544002c3c03500038026201640c11442c001e06503d80100343c010842c41364006041008031103c1c900e50100301054040790300d60030004089996040e41d03402c190381e02c0c00383c0c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 594738066 1250 594736816 594736819
    0xc08030f1024050d02130e090607031b0f02070905010f05030c0d020603070c150c050406024605011a0a080721050a051e0d0e03060a0c090b03070509 65
    0x140880011080055015000215000c42e07202c052080c000406070303080d800a690041303104e07409101a100038402c00d400d0030004c1c00311003e078100e581007951080381050809001c2c1400c041c10800c0404413605100c2400800005070310301f076081c071404080101e007056520340104524604220000544480000d9040d09803501141039030190b0422008100c60340d801190020f4112a080c400124454081c4c0c030180d6003076018642018009003900381c0f00c804c0701d840b100c0c9400130030700210f81801042c2d4100b002144842c50880c800b03041e400180011502d204140c0c0905040850a620a540a0b00307a0059541d0203035004000340b00030101210108c940b20070400005011700440d180019000e40000b409801300e55407404041c128020f65401e412003501c0c041404d40d03192191082e0784001540c208503251071203044070a500314039442c1d10400d6003010440040102042a92103102c0c2d2290b4011410b107800061121000078030a0f106141524000d4183c0d000b14410640401000b551540000041100500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 594739316 1250 594738066 594738091
    0x1003020712030203181501030b1801020d06030c050f090408030606070f050106050907080705041a07021c031e0203250b040312060b04180906060810140702060108060c07030c08030f 79
    0x85d403e4607a8400304080c0c10107a545103c801000400c03081c1d500709801038810308000500d4545403820070b003668800401c0350b0750107986480810a12078464004c0014001c01c44080c0c43ca110000c00280517910050000740105800001161203507844508594201d640144000e0001c1403d00b0150b000b810144540741c0a00c0f580f800041d4620300c50034409126208603206d10b41090304100d605011102c2c4020f0a000300e20302080803c2c00f41e51544081040c0d684a8948110000c00700d15004152418440741300c8040c99054440d2078085401005488004022116a81201c08040d550080054440b80003a0000303070b03190248024180e000e020401695000b200c240302140d82c80f04441140e00c1548a002c005800c158075a0203411015040f0b0410b8a01031140031404c1c1d6210104030b801c010650044c000d41c0303981c4e0709008450341043c408180c1e100300300d4006012150701d07002e415502d400e001014004000320002d80c280802d40605000303003410360410078041e00d0380750200a00c116100d05540c045082d21 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 594740566 1250 594739316 594739351
    0x30405030712052a0a0b0a183b0408030a0e070e060d1406070509030f010b0a06120615050702010210050402010e01030e010f0912110309010503061003020712030203 72
    0x942c404960001651120080100b00300d22084900460105001c007203150740c4003058143c0c181c5c0e0b054140d4010f40030070400140d55800301c1001505c008030320107102031217080c021003c219415800582e00c0488501e5140e0788072a002c1381c5600310446641007803e1482d0031505c403c0c0401c4c400f1080c007840c407550b800d5104001300c24036040030550301d00c514840e40b58460b0031100000c5a40c10001440b47c0311910821001c40711155000c00380d810030702d04a501000040300032891141c1e51404000c0500200c14400082041c0402c50f00414409400d6000b05402e0084424410b850740c00c05038040001001e1100d4002e00388016000700038190b40c86090181d0062003481d1079000c2401003440307868002d40d41610307203403138416012006401500607502c484525560f02c2d2121282e6012130300552000c0380c442e44506031b8003500540040d14000943d2000881d65105000c40c0d49941d0b080320489400143c00c49140140d54101a8120003030702c01e4000c0286100900342c3c910100c075405802a50041102800c00070404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 594741816 1250 594740566 594740579
    0x509120702130e1c03051909080f09010504031703040c0e130201030506030c1504050411180112060308070b090106091109130e061806100b071103100e0304050307 71
    0x500450344007035408400682c02015280565104002c140d0030442510102000d5501c0b981c2402901e40c849800300e515042001a04032000c4c07480d41d9001404001041280a55252090349001e0003100c1c1d40c10302c000180004940e8019000c1d28002c503440044000d080c04102e4a034a0b460300b060b5012900c83c14044000f00780c0c0480507400a201d0750440c0d1000805103840c3c0c00440141101925050309070084d608210440c0c2c4954424083c450305400c601d5039124078003401e0108407000138031140e68240050100407080c80c034443c1031080d088024a0507000364000c64407254010001584001c081143c0029000c04200c0b000440c144113804090080000079951200f120a4401081c5030b0b104a140401088003035180c800c0c1102d507004000a40080d1240d10415060b141c5141520a1428410480070b1407a60400c10400c0c00d621000d40b4590f403404a1800c620309040d4065650300810403c8288410300303050f1000c2040e905052200302040c864068030020b100d4a0342e0250017030078002e002d503c4011403103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 594743066 1250 594741816 594741853
    0x201090317190c1e0c050a062001060e040b0c1902010c0e0102010b030a02040f0905060106020307142b110615180f040206030403020a15020307081f061d0a08010509 72
    0x745800c00c1080890f07801303100452118a00352a000c40c0e004210480100d0142c0380d51a000c0e010b071071251109010204a24240c40d040d00280d4203184d4242c2c1090414801d40a1259017190010b9103d0054801070321100c5060080b40030f8559050030300b071204134030290301d80d034150041d01e40e1440603124400546030400049080e03071014642c0d1a0035a11401410b0010306155101010705804a2800140daa0140d0f642c41c0c1088070a03400000184d0012605005102c0d884004d4401c0094041c01440c03203008c04041064134580640b440fa20195964001c8042c1d5809105502c2501d0349001c1542c82e18a1b01e942c40d031f420b41c0c01d0405518006d41c0c0400310b91024900d01030406014403107803184840c40399034036400c01c0030301d0f80b00034011003c41c020350840c100016050b4034180c001401d00b002c0540c407850001c0b8014490200100052040701c0b1200380720505002440c01c07082070750b00b1481d05590002d203030440c000030b6810390503946070801084400091000410742c881405030024030b040d684070b081e4841c5031402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 594744316 1250 594743066 594743087
    0x1507270b030106180e04030c17030709060e0301020909040302063306131d061206251b150b03030f040612061716060c0b04020409020109031719 63
    0x560040400040c01007500590b041c1c03075850711380c100c0c0104044c0c40c0c944910300d182040c0d4003100802e8213501003404000e4800350340c40035280391100440c110f04d071440009085040a101300c00621140c50701d4050191800c1d01299a14039015018140904151800035a9648102c07070151142e40000c2c13180301c0141032030082400209000880d050513070740c440100981c9910000c0098040c00c8000c40001d010031404841c900c03c0c0001c1002d103151341c0780c03501c180720030b50b004401c000d45039401c85010491800e00541c200d0b1040782c1e01011004c070b0b60107514000e581a2011502c021a0347c14840000b10800008400301d56685070001e000340800700c1000180b6a6a010305409142249002c1c00203000c0030b4400c0c19900e04081b4511008502d1036601c45a01c02c41b500152070880310350300425103030b65908402c400580000c045600c1c4c6000300000f15203804405c4400a08002e200325143c00d002420b5a2003050400043c3d80c012a40761450003001c1d03400c1d071040d80306410b0203503145030340d200364001d250041a0002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 594745566 1250 594744316 594744329
    0x6040303090e100e0702012a120902061b01050402030c100512150d030203090906010807090b1c15080c0a061d190b0a0e0f0d0311150727 60
    0x10704904019609100342e800604180c000c40315a1800214295a810314500a00d1107800000f84403025000c601100003040e002000380300c0c1195564a80168022800d450010700f008000903102007610000d140e074800e1200340038242c900d6849402e107a250640c1301c18050780c421000c503400304c1c1403c1d05002d640c10741540301e038000c104240509680b420101291561000104484c00203034040200014840b0185503016001070344040b50320001811f1a1080741d030828000d00706900f8500e41030400138100140c40c000c031020040c001c10b082f0130002006100f40c0c4109410391081c000400d8000c8982e0001403a0b00ca81c480c00e03c2100c0075042942403064842c0705440c52030f5140302c440c0c2c4003100000326460241c0c005541020010106103190844062150058180c420034150f036000c001c000148141440c0720b0341d600c9a0210041a0040d58a10580043e00750341800c3c940802601134040d43d042c0844099022001c1090404004041e5440380c14800d20041d41c0301607007140548141c214040c195140240d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 594746816 1250 594745566 594745577
    0x20c070e010e090606090405010f050c0304120806090601030f0b0a27020f07030c050c0306190c0e0f0d0516030f1514010311270109050123040b0103060b030f01050f06040303 76
    0x117007190600d03120715640300340908004145900240080030480c1c41c2181c0baa110300b50080248400c001e90f03d50322a990040e140f41070320090400000050141740080c0075981072660300c000e04486a10301d5080b0001000d401030007180020790324145030710603d107802925090324131803098503440c5040d14801d40f0b045002c1c8110f01401d00c090b07070350150b841c0300d03074080b09585900c00d075183e8540075030302004014802e8054a07030002040b05080703011b0003038407030441d0403c2c02d001a586400000d91260721901750784500854004086a0450a0540c2461034402024040c03903600b94010090014454080441c14031403511141c82d1074140800d04200e466220003610140b5003400108045160902c100300c1c01c0c00010010080f414440d03864220489105c11100013100340440100701005603841010f00400002400c03030004a84030366208031b03100110040d13603c60387e91400c1b0421103920035404000645055030b03010703541e8201118ad4900080f0b0907c240c510840c0807044103030b4541000025501184da0640300e9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 594748066 1250 594746816 594746821
    0x3030e060f090118170d0806101202030705091e10051611060d09260903150702010b12030d05100b040e04080c01060323030703080721020c070e010e0906 67
    0x44500c00c4c944205400004014078002c180b40061031200641a03501600400c03038030b00ca0040180840030010310741480340b080a021101da843c1c03c411003d602e40c00003500180d887e03403400b006544600503d510650804d20446104d1400540d1254a009412049459810401d030b84a8100c4082c030858142035003050f120f101500000308070400ca40441c3c1d90080203d4100790400103c0c802f143d401410179106001207a60300c41d401120a0303606950303581003c01d014038001c0c04e031002c607a41e01180c100c01028001d2150000701960300c01e500605248400500326552070400c02c400507540e0704202c8415400324031301000b1071909103880b0700310700c100d550f040d0100382002c0c5810501100300000510070f4490500400c5100c0c1012000e100c1c002c0658814080c9481a48401c4100b6010715805400602c00c0d0340104555070220b030b00840080d51045c1c261400064a4845008601e08540760313414980b000c5001062003038a940b0049490406c0ea0041407618000d41c0c0c0e1961040302070102900e00c40c501d90800c401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 594749316 1250 594748066 594748069
    0x150405280807020321070606080c0f1e1804120c110f2b0507090c080a09050307050f0106180614011b0c091a030109050607180e090703030e060f09 64
    0xd8290b0500050a6505002002403984e200c6102d04002058228001038404104075003480b658004d071480340c1c014403807902e400c4007040f0143c00c0c0303d441c54440c40b038051400e2000310100e140103881da840609040c804c20550600d94150f014241c4046403120756542c2d009144e284142c521540392504490b203c1c0c8010b01c44000d10074035040c16450361390800080c81e5910000e2041058103014545251151020b044082c20f065040541c0c540040440c2401c1c480108843c561000e0b40e030f608149030850028500c0510b1070061b00e50300c54840020500c0c0148407847e5080c1c0302c1940010201c40c030380c2440c03540c6c4129a8880d1400c0f20881c0c014105c5001c0c2c0406c080c0b032554850b49011094071035a880551025806403107018203c200c80e8005d01015894640302c440c00720108200b0000007a068000703101d10b8100340c1d40c0c243c480e0801401c445c1000300389200066440b0440814100801050351928014103003064056200c8465000030f13004503c169011400906000048a49150302642c029083c81103020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 594750566 1250 594749316 594749333
    0xb0a05040e060f07090b03010f0602060601020a080d1d1903090609030305195a0c06180b090c01080103230a02130b010e040209100507050304030515040528 68
    0x3050f02c4c082108900703002c107903004d13442c005501a11220550042c00c91810000904c0c01200800e0541150050b282c400d00041481c41542e0750704030410300205049200120400150801c44030348442445005551440802104048041140641e07a80b60304940c503800140d900c07014600c00100002c0c0108500045030702c010348208000b481034039000301800400c0d41d01d00000288184502c40c0010110a0a0f50201010119405403041b0b00344c034841004a410702001d540d46400b019100388802c0001ca0002c02125500c0f81210b180c5502001c581d80407107041140c2010b4040b1100030b40bd110700700c0c0505096004059085c1201d03070110644003000002070000c1640714908002542c0b0348140b519040c0140e8407410405840e6400f00400a100c0940d0800100002039400303d0500841c4108110355958a5115441d2104841800c24503500d001910304145188a550700140c0207001d0950040e43c00c240300300c240e40c000c034005c4040320690201e15901200c10054442c0981c0241c100b0200d004c0081c42c0784 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 594751816 1250 594750566 594750571
    0xa03050706090812180a020d06050a060b0408031b0a12180f2d0302011e0c080301150807051801111c231606050c0f0a030b0a05040e060f 60
    0x1000040354003402d5035141803164009601d80f030303076200400c0100035009086441d035a80d194100c100901008015801092419860103800740000ba100c03400940b101c10203402010003403060303944082e074496070745544640702e4003e0020807241c0c1c003d4480040d8403810000e401e03c000d07901303c6a4030010380345045003541d0111402d00d01c45148201d0740d0000030800481c10462001700f418a2609403201c00051070318082000c070703809280014200d100140050f0745d01415801c1000c1400000074034580b42040152544158900001c00d0201c0000003c1008401b003800040c40304050784400d01070744c4500d2400d440c0c60041e11134030700300b1030740701d00d5418a19031268440001103a50142541c0b4031005001c26505041541c2c00140c001c190030000014580c40341940b41c200001c1c7c0070a03800d0604034540c21559201680280240005442e0700c089036612100c1c1d012203e4040032004000e907220710741200a80581040624681704084240d40080c65061601500b01780002c040090b080c5035841990680703580001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 594753066 1250 594751816 594751823
    0x10b130c11161410120b04020c1e0606012c0609041a1f09090c020c03030301140405010e19050709150c0204110a02030d091506060309060c030b030a030507 68
    0xa03800c092124810038019802d03200d21a1030201405402d2115004943c5180030b6024021101d084c00094280da1040c51040809a04c10010030345000d00701c0010041e0140c140c8182d15805550000d0515013600284100c1e0079821006507075240c1d88801c0107503910501421440781c904c9840440c1144012010007580c281c4400912090401514034041412601c03009106c4584040d1808411000c1c42d0085048031b200c000c0c500c40f20503d07290003400500740c4080d40301c0d04248a03180e907614000e1600a00c0001484440502220307180c7d82c0d82d15089001003084984180200d00c0d00b000440e500707807a5190b492241c1c411a0842c1e4241841c08422401041c004240b082089840c280200300a12a003910001c24001d03039a40318502e241600421003207800750510300c1489081000b03607502e04c40d00402500c40003500117800240d68121802e0140c501c40d81a41010840743c0703000c2003c56003a41550100c102c43e40200c008200002040f241a8203c45100000550543c403002d103040001e0711810080200d14072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 594754316 1250 594753066 594753077
    0x10f0b04031b17031809071b050309040c08011a04031e0c09020412061b0c031412012301020c030615040603080703020d1b0b0103080703051b0f010608010b130c 70
    0x564410110841c10f20360103009283d0800510500c0048110b1040e0f2000c1d141200d01d4040c5081c005001340c10b000f0345112080d10078162400705014000d05005658860b0400303001030005006041004089900901800d0b19000c500034020300320700ca558003613400356544850810310801d62000c03014030016a82c3c5044801c0260b00b80040340743d12050014000500302183c0715070a0b04010b181c01c9050710002151b10250604080d00400016844800b504200303405080c00d6080318812005450301e48a220304558030700c5042000000c07008040c25040340382c80030031114003014081d548012a20b0b0107803d0b8a0b61f0b4154000703001b00d0240181141d401c150b40030001c000203401540c036a550061038004c4542a00940c01c4005020b01c9180c028108071860b8080e8005d0a00318604c69448588011040c040585100004201c0d04209801401110045152082c542ea60404c0c52584950364580345149445154240400040c1500c0d0501403c0141800205044184460400100020004480300030200310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 594755566 1250 594754316 594754319
    0xf0b03040b19090809101106070c0f141c0f091502070306090804050108010e0108060a0f2910051305360105100801050d030c1103030d090b010f0b04031b 67
    0xd82c8184004244036145840d02ca6248100304540701c2c0c2c2c01100d06c000c0c4060070300f90794101c400110b280f0707034840750500341446031029500708a0020101180001d0403036001c03114090b0840d500060360a80b040540c0c2044030f101c11998011950103c1d81e403640c1000c90809202400000c101c14040803182a091049400c11076076030303e51000381e604204040e500024005024031441d640b245c01c7e07501409a9008048840d454880240d545030130080c891404030707680340e12513034210050b5000089048007094002c0409500003914421401024491500c140007c03101c0301c041a008405a525035020b851b00040414500018044500064900440301d40036074070080c112039040d44d42c8035140390300d4032001c5001903042000b481024800503110806200ca80d10041000c1d980e41c001c000714095052400c180100c1361480d10040c200c00740c03100960b00d808045200d103090f01440d800313411740c50300903145010790b66031f01c1c05590344190030717070060621442e0200018000316104a0701e03800004146442e07100402e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 594756816 1250 594755566 594755611
    0x103050402011101090318080304060903062415020105060306150105070203030706051906060201090c06111216020405060d0203060c0703020309060a0e040b0f0604090c0c02030307060608070f0b03040b 88
    0x644a1740320813408990105200d8001e43d018004200241c2505d900441c0350505000b00030300500e0061000401c0b2580301c180c0c1801410000340401c80c6103030502401e0101544860494001c60070104040e40107619000c0001c3c0703580307800196240944942510044401d140c8001116a9403005400380e8152208001c2c64000801d07a22546204815007602140b80c24032106000e0280c0d40180d02c13004c00c5a040c2a09840840c54954070b9008840c40c50030700c800c0c5505c41c0715400b401c0601d0600940f80c500e4001c00c4404c100322a91920f110360b02d00c08c440402990f6652010403844816081010390035611001c001543d4458817001045064000d0048a0401d203180c00003810360341c840316640b00041d1031042030b08100d050500034a030000200700c1d0368205000821012034994003861007030140f500e0302d030038010141d03500070041c1e142510b8020307064940e59070b01030801c04050b00d118807402800d44240340703001911039115900542074891915145185440e41d480e0061600d46c041c0901103d01400c03140340665 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 594758066 1250 594756816 594756821
    0x501030816060b12060618010b030c070f0507030503040f05060301141005120103050a0209070302030f160c05010213030c050a0605030402061e0d0e0f0d1b05070e09060f1806060103050402011101 85
    0x640c1481340081c4118649403040c0610b8445d44891030208103031080051144403010f8040e41d034004486444241c0301d40717090034043d800e65182207000e8400d004000001c418001301100038401d603118074112401007640c076010703c20305120034441c588002052300304400d40c03840e10705d149c900e41002d81d207825828200e0070800c00d01c458800b80c1c13040760b556220710000c0c421030034000d2050b5400f02250804506516214100e0f40d0960390040800c49402c51498464142d00d000392500b2820a030003c1c02151100f00010800d000f050443c0402d0f100612062400900c1d0320704070015005941142d80e41904580786c036070038040300d60424006550083e1052541c0c5140f80f5411002c3c1200c040480c0f8041040c00700d11100a080000f000303c100382e640c2050002d120283d4010700501505a01c4550746e6181c1001410140c2c28000c1941083c003401035518140001e2120014405004003a8000241c5460b110350981007084800c11f1020b6180d5000710703000641c02c0d0b01952003540e2160041c18016150b010480802c0e08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 594759316 1250 594758066 594758089
    0x5040c03020c1f0b060a1e1e08090c0303030403051e0d020a0201150f0503031218030f0a0801150e040e070b13030c0b090a18020c07090501090507030501030816060b 72
    0x42c0b50041003081030f5081064080c01c1d001000549000e481c0c500ea0341402440805075603511703080003a40314040000c00c0c0c0f286c10b0700311701e19800030042c3c0031580540100500d01101503950600318801d05149009600d00801120700465068450f903243c08040350144034140e54910800d000c0980078080100c1c541180c0c001480c070042243d000080d241c0004221620f502025006044692000f91060110f40c80020450310603d82c0d5903184c1c0384a948071442c40703541000800032031074580404124080700006100c043d01c0015055180c43e28140e8841005c100350300c102c420003800291111480d203d45017441d0b80305044c035071404001d448809407212948a0158002c1007103040300701110008100b440a20070440015025445058ac503003100c550014210400b02e000f44000d0b05101c0001078190a225411030b02c00b001d40d40305a0b110f995552110100400d802d1007a250020b06001c00550124424800c05050b20b43c8940001d05007030a2075440c03000848410000c55203e6500c04003800595181c0c0786104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 594760566 1250 594759316 594759343
    0xb1e0705030a0e130501050337030e0a080c090a1a100e0406050402030f0601031d070609150c0203300d020306040e0d020601030b1308121f030201080105040c03020c 72
    0x90b00705440c901130028070038282c81403840c02c0380707010700502035650042014810030b04900303060032400501003000030403c030503120780802130b46590502c402015000441d001c40007008650595969a40b41c64581d1500107a03c40e4652015000001640980b259403103100310680072031601100609440c0410354411600198101040001700541a280351a0066070013501040c1ea0a5083d800c0c031090100c010b10700501402c0c14140c43d00403403040b0650441080641840300c004035030500b903882c2c201070810209070246031412944660243c407494060440005601c0d0302400070076003160520000e084082d65605040041b0003030102408407400c00f4000b4000c404002440180e13203013032020402046036007110300c9211541000710103e003000c0e000b18a0904681d0404160a2a5502d807040b1000c004201007004080420120340503001074580c8c650ba40c4100d00d20521550003240c0d24080c900300724801d01c0001e0004140c4801803086e42819080945041c5140c1000760030800104640d038108400c41c1c8511 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 594761816 1250 594760566 594760577
    0x408030a2d06090608070302120a0807030f1206030b0a051b1b07120201122703080610020303060d061e021c05010e1b0c0f010e1506030102040b1e0705030a 68
    0x71804440d500c2800001e050200081201a19010304c10b5211041c51001a00c12420f80954000081c3c042c008007000d0399100381071981d00c9000345405045035620085080020f00c0650050810318110301c40c45081c0d07900000503080a03511041c0400c00342000810b504002080c030a031800c1032071021009015400704540795040c4c0a0380103800c0500e009510f0740150506040c0d9070110000d030b600600419012900e041010400100a500340c414000d250070303c0d40c6020840d140c0390070900d42d226428a0241d0021200201803c410346005c0f6543e01099403165800424050801d0021300607070b00c05045200d1281c0c25400e0403000740c0c1d0440898000f418000010000502c406101c03660714441c080c0980128411101c403030070b22030300c0e40c0181411a4010921864005051100a0070400c00080c50480c044000d020b0304513591011074443e2040c03081801400b0025020400c90315041c000c0d034040d1415401c5890030860394050850441e40e400d85841c942da04100b011902150b806c0c401800000140d03110f0703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 594763066 1250 594761816 594761891
    0x90e2506140405060f0d0b0a140f04090b0a09110a0602010c170103030203040315022b060605090d17070b0901050106080a0c020a1b180f0b01090305060408030a 70
    0x2500200c420039041c20700c01000c0000344074a968600540d4171542008800c1526504030000000017131110707500701075001111000c000340b110f40c203103080d111540c0142d030b1503041580c0407400d12081d2840c4000003003c004000c40004c20074240307a0311070400917025900034444080c900020a0800c0700a82100740143d442d00800300c1c105800040921f0b04880408150206600d507441c002c2d16401140002004519000c2d6440c410341026016500c00c1034108441e200a042426a140110452000c0e400003403414100d0001340c0320300031815601100e901805a5003154001d640710400a000c2030b142846006c0c0601580002c0381001600512540088e000001c0a50411801808100c1c00418418191b0b00340800500350642c0070608110107a441959017034420200040d0745483e610135048080310101291000d00c4c6000719402c043c001000d42541046001003c000440b801842800080d00315400140854001407580001316404603079600f00061035140380c80300405540f80c020361000c140c05d01e0b801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 594764316 1250 594763066 594763079
    0x106031b0f0518130e0c0a060519110f0a031103070f1211060a0209041d0a0b070e100216120803010e04170301091506021f0b03010f0527060402010801090e25 69
    0x1046d0344008121444543c541ca004001031091140c0b50700482d91103000c60405501d240070b0440300303500003200d0003920f0807020f04641036551140d00c0541030f0009190903d105480040c08801c803601c0c5500002d01c5503c05000b074070b90411042510a102080100c0d120000380207203001d01400e17010303090314400580d460700000e04000940d1000d000210100854901500780d0242c00110030a10580c04520601e259480300819101c00e18035580103138011a0308442e002801c2c0d408985001014480d8008008158640c1c120064080c07900000601e5150100010b00000c800a030314294007512582c181c0d0040e10580c602c091180c0c1080e4051000551206c0a41aa0200280c0304001802c070340d2004000d0030742098600410640a2202c2005940da00d0340c03103c026840c2034201c800c0d00148000c0600850600b040345004070310705910140182c191403000d4a050301c0b03020070094041d80e0140e6a0074542d90034583c44c2c100030001c0220b407a076640301d90300703001c40303c840c0b424008814284003034a403103103c604e4403d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 594765566 1250 594764316 594764323
    0x30c04020c0c09130615061d030c060a02070614030105030705090a15090504020f01030b011d12030307110d030e0c2209050303070e0103061a090105041a030106031b0f0518130e 77
    0x1b040c0d0b003408502d03120601440d54000b40d03084034107142c05c00f041f4244207003001081c244845290704581000d4001052a40e2980000348181101e010356203603001103142c451200700901003800703826410340101d442000303940b07441c40499402a2002000240c0d90381d040d9140300c08900305601c001c5000b5224001c1005501d0081221301c00410282000d01181c900f840c0001c0111200241f0200f018240311105001c0e03845000d04003241c01009070869503642080b14001e09000034141d02442d81c1d1003403007440d0315058420b008608180809200521740c90301004101300e650581440c220350290002e000c00e000182e100c1c0242c62506000c1d10103107a0780c1c14031140003090340301003108590505041010030440e480300541490000d01c0b002c9190768440354800012030700d520496001c003030503540344c054030b0703d11720710890046040300d0702500c04020b0052407101401450000c411890b02141c41d010015036928040d1008000c00c0030010011f5025203e058001080709003811a4882e50940d10103000107806400c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 594766816 1250 594765566 594765581
    0x9060e0606090f1e06070c03060b033903100f24050f21070e0f0f1504110c0a0c0504110301060e01020a0c1e14030c04020c0c091306 58
    0x7901c1291070a040c034004911003100300d8030024003440f0455002805581490794400c0207540003400703290340d100c80e42018050881d043c0003c0d60b40074604501d440c0c1d02c0c81c0000b402c44020410050341c01280c500d148200c0720311080500c18010403502c0000070241a074047c452040c915081400010b508211103d024040392680070341c038034072000605640429140c210101c60100c9200f1202480e081440c0b0000c50040d60f407000c01c3c100444400764071020400e1011910f4800d031109046111481c2c0c0e07a25420b0b500881d0151001001d0b01003c4002c24922000d0303e0f051406000003034004540d00e00c3e15102a00c05603c20040d40c0ca141d0000075410080141d0700c032031700c3c2c0140320403034081c0040d440036084d03002244818840c980500803c5805c000143c0d00074480e010186410903020700b061540c0f00d54981c410700f010002681403081c0c19002007814190b02c021404001c901400406c070840181051200070340c850408018603200704a4000c40c1a526004400e10840d0400c665000074009850f000e015101c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 594768066 1250 594766816 594766819
    0x4030909060506160c0902031e0703020909060103090f1403130909050706051b03280306080d0c081c0b0a1d04060b06120c0a0207061d0607140709060e06 67
    0x100801040b069543e8001d41340c11000b110403000300d4840910b40100014402e920071502c90f4004420000c0322158410b800c01c10512101002c000740c2c0c1d620034200c040b4480c201e049580321045001190700303548a0791117154114421060f644010100fa2100c1c11003d600b101c2403c096030001034410050ba08501c040b5006201c0000244907070922903848640701c01c264003030171003004404a05045d826094038404494000d0b11415a0398458005100250020490142c200348450301000c040d40c0c14880d100b14000c8580c90703030140100f001084802c6a003280707002d000b5110060184180340d08a4803810700c44201e100d030064000b1fa0090031030184001c6c06460340c040924540400c040c1d0a401c41c1c6600c00329401a44168001035140039203001400710302903448141d06220b00030040060b040c00f0f41004000d00403468080300e66180d99600100c0b1a0701401003000081600708460401e5400e204d8080c0a58070300c2030141d41001d42d1007102003441c1c0303401c50780132000803030302c0f82d0f01041000784039078059030440300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 594769316 1250 594768066 594768071
    0xa02031b030a110a020612100906060801050a05190b09010e1e03071208030708070c060e0c0103270f0f1a0703110c0d1d030d080a1406090411032404030909 68
    0x945070001007950050004c07d1000e40c1c590307000120303003490080020001e4400c454081215686428004007410401d0081501440041c03801040d80d2804109011408041071000d1800904051610000c0d4100400c402d0501081c1e5004040303e03502d01501025030800098002140c0e403100c0101442c2101d42c4d40700100355440c00700102c0c04550a03504490340403940d41030a2256444600301100c0322455030038041d00a501d8034481c201070f404041031000c80d112007640c007400858108099240b814400c1e603845014600111969400a5640e0f2130400ca140d000350140701c00c1c1c0044d9100c0403034201c11010fa44ea0100c0300e10040101c1141c040c464040c03d44003040c0041d0038071800d04e11041c1c6e00c12042c03400400344000c03000f601442e884c0784445458581c2002d029074460300d401c0200074003046000c4d12404002420486e0340407041c15443c006034421a0000d080240c0da44546d04c4201c040407c000c021130b054068209001001d004001700b001d604868005007a28601c4c00e0306000b4101c024a4114102150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 594770566 1250 594769316 594769333
    0x6080f041115130b071a040c0314070b0f0c060c210a0912020706020f151513020406090303030b06070804120c0302030105130b1305030a05130e1302130c0909020a02031b030a11 77
    0x123806003040f9064036070058124510a81e446007251603c0e01c00e5108000d07241001802c076200340791030b80251010146081c125500360304c0781c050b1904036015500b0240294a4000b0701d01911110705507415800c00902c0d400001c1c034481036200e20101c01042032012016a0000d002041300c240e041206401100c0c01001620b0220a02d5030034030705454003e00200000c2000003020700641e40c50132000c1c14082649074085598642ea030501400e8580d09200543c04640f42400080b45804e01e402181d80c40c80c0c1c0504906c6c6401d041105a1184842c058170a41365410130800200050720700f4400c0d10b010760619031041d10300504902c0d242100180007080700b030907544020046400034078004269010741c241030a1150710340c80814280c00400e00a90b00400039108147d06001d80c6041446d0002c0200d4000d81d482d18610f00d503484010180d9018095000005e403490404125000711039000d01110819803040c1c0e450414407510b02c0c3e020000300545801141c00014809103403640091107006001c3c3d80030050420350 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 594771816 1250 594770566 594770573
    0x62710020c2d040207150614100804111012061d0c07031e2c0103050c030f0c090d0501020d0b030c0a050303030a05100e04060606080f041115130b071a04 67
    0x104140c2c080c09025a4010500d242042031204c0318080e0500032810030800039a83d0425203800395085004140250040c1c84c9501c1628802d8010510030350b00704043c0400245103d007802200c1c01946140d408000c00c1d01000d90001c0f0036801044010546440124001d01d01c1d00c90345040c2c0c03403016101c400448004c0160800281d00720782840100d41c06030750684001950b941d82998a10503182011900080380484050050f42004140340c041d44203030380c100704555130340301a100c40d48000d03114090304d8580303040064a40a1204000c00340824050540700b8103410b259141800ea800c800080c005c0c240d101d40300742446e420300700a04040c40758200c4641000c5403030312300420b4a80c40701070300e20322900c1c0d21000060340d400704412902c4024540080c1640503842e003420440300601c042d00507980050b00780300224060002c0303038851601031a0004c0c0d003404441d1940042109440b03680c1050b030225002405610703004006020718030024a06c1d0341740c070f55a034500351a01c0d2001415010b40c810300d104d8003a0034803020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 594773066 1250 594771816 594771889
    0xb04081f020a0c061508030c0102272407080a120b0a0605040b1e070302100e0105010e0f09070e1e06062511060d2306062710020c 57
    0x30340d03005140001c0c00c0f0180c3c003901d03a01c1c454a4201052901c000180050b0744601540100509200e2102e2641030140340107080040000c4bc801240e03011001000700c41041c01c0362a017800d40c2c113856a0703000340f504030140e1300c5800a4101c0c0445074046001042404501d4649024149042d8000c4511a2104c0d081000150650040e0b0140c0b481000740817500c9182c22400000120310000300c09136140d2a10807078a8029612256003000903103003810714510360011201402880d040c0c0b40400500c0303481341d4502c81071f401350030002050703880540310b94a40000d010f0701c103401442c02546040ba42074100342911108400c0c030440601420302454040000002408041d171074100d44800e000406900581c42e0304102c401c0101c460400341d03020200284411200d501544607c46254080c1d444040701c40e0000300c2c1e42254401107600030b070046020841c0384001020b5849452401da981881c900c04102004046110143e0b80950400035034014040b01485180200d0f64804010004c0541e0007030b4010012181803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 594774316 1250 594773066 594773087
    0x30219080115140a0f030b0a0e040212010b030a03030c02011b020d0201060609080703021216180501080307030e06341703010b0405010507020d1a0a0b03030c06040f0203070b04081f020a 81
    0x1000f01181c07405d0f5282e4803c0d0030142520324010110b82106880b9528101e50110a440482c850358503103800c190004418043d00341807080080251110503a02c0e00c2c01d030064611444944d045544e110052207010000e1140f052113405664020030305441784038006821154590001c105004040ca000c00c99018005840b2040c0c0740c0c1910240c22840585a1507440d1800444800100300030920700820f0103016085004058101074006019076641c50002903264410420050000342c6039148206207410920014040300b111400349101d1302d003000c02001c1c1520030290300c0f8041d111049134070741c040c00704003000c4e41c140c0c564204480341b8551400400314414821442000d06010700071421006540c2d400e080340d1030942d00103803004691008510306c0300311604115a43c0c0702e91450030b44032a1150800000355030b40080c000004110703070388941d1620092120b24000480e4940b2500002161114508000d40010080c10008000c80115242c0c80a0f150059856050b415481031024608141d8007094025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 594775566 1250 594774316 594774337
    0xe070512070f1503021e07110f131d0f0c0f01020d081308090405011710050c07060506030106080a031806020613142a0117010b03010b0a03021908011514 67
    0x145454000c0748180c019006e461480c5c00f580c25034000c00301105025a0003003604520480022600103e0141002000c02c5540a00d07034000180025070705c949102c1d41e200d007402038450360109074903e080021072380ca00041f111030340c41c1e16002445010110704102e00d0002c1e130708009001900d10841014030051080d50001d00412808400e085d000c400c0c4180c1030300710350000300090001d228039038558180e8103804000c00d810080c28840c0395001800b5200b1445102d008104085000c2d1501d003840d150040942006051507a040d503903900c000036440000c1011300c020078402c1d10b5001500d403006030842c601014980c05001990040410070031202c0007441411074682d030013241c482e0664400f88016103000c80006603c0c0f003e410308070811411004c04540e00b40509001da07180b5480043c0c4a24070400c58800b841940b0000705e0074801440501ca80700c020f0004924585001420403007000744034000c06c640c1c40720480c041ba0300c0000500084226245140780581d5508106003054a500c14090301c5104401444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 594776816 1250 594775566 594775589
    0x1e04020118030f0804030203162402070b1b0601060306031101030e0a02190f12172b020a1b020d11030c03101406120a060507030204090e070512070f 65
    0x10090a4450110403010b550000300040003064070340b801c40c0061744140020f900c00d10415034034603040e010b020300300c0d0261030540d4100402c21045128100703116085102c850154054098042492021070026116101202030b022030020b540b421031130300341803041c0c0014003054240a014030200702c910320280704403202841d0025400c911161b00030700f020002c9100a51100a45400207100490a000c2c0025a0310807020b18500c40e07569100c41150184a03031000f80440b1500107100150038407080030780840d02c42418641c1c903c0448500c2400703a400316400c090300d10780d40490300c180d260ba8001081c1e0000d0104070010070b40d281550f00041c0c48011402401040f0319400c61842129840a001401052a010307085800d0110714001a00140001c01c003256607207600c01d0009007403807404e03100e524510907030324025051260a40d16440003414004000e030040c1602084002040165480b600c05458404000f41c2441400c10042101c08103400d8510b01440d40703c100140003250110214900311658064013 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 594778066 1250 594776816 594776837
    0x61a0307050d0612051f0e070509090705060f0711060a0e3106170a030c0312020f0d050907050618040504020d0804030309080d0305010e010608060a031202030703081e040201 76
    0x10014103c80d400081e4145910107141040003000200794100700b508008a88400d41503601d010105d4510b007424090f5648045401c00403070400388842074200841e03005075004140c6441c003041950340603b81603001100001981c509001202010b01104101203810914020303604070024405280c00690620668100c000d50b10342d8455984084549140002c91620001d02c05404500400c0c10b0702c50b030b0194600b800900c54200c600402c42030300b02076043d100e024213140e041d1000c40d03900317195400d0035030459030030008030f81c05400c0b410240980102c05500851140703080d140c040e040c50360755803105025503001e1060a06a801580e51218a90801d64001400d580c0d1800020645482c0140203040c2020005000c41410b60014549060382d90000496913003001c10081141140d60901c10a2003011000b8014401a84142421034101c1c100800c00405c5581380e44070f03c40d5003285d00d90450056400060310b5420180c000d40740a40c451480c5041d928600c03c008541055014000d0001f810003946218 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 594779316 1250 594778066 594778087
    0xd14041e09050114130b090c030a0603080708030115020105010503210d050c0405091f0302010309020118080303011406090307050411070f060204030303050c0711090a06170709061a030705 82
    0x440100420251000788401d50396030354011010407565031307201e00640c8492201e040498181c050034107035541c040c10f0400144d903203600c02000c0360005010001c81035191b40000002c05c94110162003000c0c0104a060358951515980d1380200406034400c6065905180040150741d80100300003000d580c001251816000785102c00702554451408680200340c13401c0c2c2031144801d0100b0152040c2c880c00d9454004684802081e128002845540c00c0000d502c002c206100551081e040840560301c107050510b0982d940b42022240010503070448a81c6600100c0100a60b100c0c1d2210040d076104180c0700c491400c400d850200380c031242940119801141ca900078004140700010803181640c1d04800c05440b061082d14201d0040d51042c84107400003403c2501040f4211030640858540c540d001c801c035048410703541c06000e00c036030000700400781881d038031000003804c2c08080e40c00d14804c0b9600006050303503504018001c1c0881380c16421002c0303074041da03500d00301140411104982e04a0b9041c01e02039200c411000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 594780566 1250 594779316 594779369
    0x30c0806150405041505150313080702040f0212040302120c120c070b13030201080f0906070f020c060a0206061309030203160804090c050912030307051b07030506010e04050d1404 78
    0x10f100030b80083c506040c48440f070f034003030381850300352072007207982d080c0c40344c1c0380d070104840c034041a141c00d401110000c2c0d1a600007880c16000b4600544003600210b10440788031120310072600540c0d0240007803408901004109a414050550ba03024442e202904000c280c440e00751b07a980d040c0f0380403009420000f484428800303080114030001c2410416043d6180c0c03461101e400420240e05c4102d000c9030104d4003143c04004ca51651902c901507050090100e50b0310003d04880b582d0050303070410705500440c021851151581c0e0014226507015400501103400c1030020b1281e0000014000c0740340324035100c5040c0000f0350100032140d04602017800646a40160b0808582c188101d0f484022003600e0110b03500151034008014103124002180e400ea52201c0402c0c0c110781328882220024006202003200c0e050940c400b1036503646801e14542111030300c0d5140d070b559a00c1c00c0000c0c0c02c920320380c110780c20411080083c10456405244280d252244003411110b4500c50180143d01074106154012801c3c20b012074943c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 594781816 1250 594780566 594780569
    0x2180423060f0a0b07060c0905060d0203060409140f0c040509030702010c1e030f0e01020f030d150906030302030304051b09150409060f050105030705060708070f02150a080601030c030c08061504 85
    0x4054a00113541c3d8201c4100750342c09500115400c40c144082d2001046c0600304d400100c0700d01401031440c2c8440c6810781390081d80020803032684140d94000c0130b804200000d0320091022710300b800600700050514219440c00c8141c20f18280b00701d05190030040318400200582d4840765082c02c100302010a10701d004100161520011507400003406000303011b2552084823000314103060b40312000d01d00c1440700120303120840303802d246503554001c10a24100da02d180d03011040680c6424107000c6201d440b40844c0c4140c42d403580c070a800580c0b0110600061084c01d03c19420b22580c000707140302c2c1400340344010801c0614000e001e0307049810340208115150b141e80e0085c2d08002e0f400310040252076200c0401c0da00810382802404c3c000d210f90100400c490900e40c0c12140140e81006129090031503a0743e411704158013085040341c1240090229003481c134102800350102460940700e200c503034506100010308540d00410030360300701410203a010f40600d400c0309010b0f40054007a035a071203a820f804001901d1601c01c0303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 594783066 1250 594781816 594781819
    0x4050d030c141b0d0222020d0207060e070f030519030512040c0e060103020a1224032009010b03180c15030f01140102060a0c0c02060304030302180423060f 68
    0x58203600c0c6452004120f0340005182180310a4400042e401807040d0300240c08002074101050142d04020400500003c4410650401c409858022103401280903a0803084048400b80e40328040444003010500101003c3e050030b0507a90328062440d203446994503105490503000013103c500701d4003414881c000b241c0300b05518072a8001300d410310345002d2903203c2d4684141803c45c03814202041d82580300303008460360411156614058080c1e00030030700004100c2c403090800d010400d2405405a00d41c49103882d0029401203145c141103918403036010070382c0d56850b01110321650060005000c40b6860721305981d00b008030702d060100358107a960000c0f85030406554205600000d40207115400a903018001c62003040c3d0000c49040c140d0ba90031056074084220101c56000da00001c0005050001035403215500e5882c81c5400103041080b5004074010354003c0d80e003074000031340000785446080d801144040c4640d03030542d003c001d1a030001c01da9098803c00e44004001003441200411825502c40035403d141020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 594784172 1106 594783066 594783083
    0x5041d07141c0b1c05030a030e07120609061401080c03010f020a0c032d0306150f0e04180506130c060c0201021c02010e0a03020f101104050d030c 64
    0x4140d08240e00110114407511812622a1106132500c0c051400707903540300c050180007419156442d44440c6541e00a0408102c4a00e1403200840450742120001405410a02d45035014080108041525401e10030000c103c140700440e001e910340390200d000b0055107141c06041c0040e80600660440441c61803000c9a004c00c2c041c1c03140c00400341c07030b0690650030360041130b1000c400502401000d400003503540d1400e01140100b12a807a512010038200000c903840071035001091910510203407030040e600c843d40c02180c50403260040026640c0314068076014030340441c6081c0251821b420940d4070712900711000454038083c05000a0190b01031f800791145a604660801640801c2c0c080102150360300e007030b684441e42040c051440385510070790181c11498886614280f82110f241c3c4002c1d041e904c5c1a440100d018000002c490480e4000e4458840c0c10303000b406e090315542848407014100c00b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 594604316 594784172 := by
  have h0 := BRFrame.cov_init 594604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 594604316 ≤ n) (h2 : n < 594784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
