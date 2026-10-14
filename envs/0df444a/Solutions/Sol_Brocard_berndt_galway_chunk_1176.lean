-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1176
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:36:50.746413+00:00
-- url     : https://prove2.me/submissions/80c46547-833d-41c1-aab1-5633cb89950a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 211330935 ≤ n < 211510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 211332185 1250 211330935 211330943
    0x90a0b07050c03090307090203010f120c0501080406061e05010906023f0708091801211b0905090607180e04030c0b010b0c07080f0d0c020a09140121 65
    0x8000244020300490280c40c01064240949290241500c0003d0a198041c2c00c1103070029800b000501c0039405050b41c400140c50307078403009011414661188034480405200e510704100c907404c006010000d40381c203d00020005811a014140700c1022440110342c02030085a0000f0385e6a87c0001d0440c0c8005041062607807000e00c24a10380441c183c95400032600c1c4ca00c00c078020718241402501144811004000080c0180c81060700c66040c4400c00c6407480d0200a90030444803910010b00c0341c042070000c4280a402d0481c0074150001d15442d00504045101556000c1c03112443c2d400100f001c2550091442901c0d45020703134075982e592003400e5542c03034040c0e106a6800080030006010007940c45801d1a04240a405d12050044440e0fa61811003c82600041888140840c440d11a50420408000a09070a0000d03084040c40c000d00b0560351020341d441942000b56a100c01029074503021011070160080c040144502810701e8550440142c00f8480c18443ca00c4034030609109800c11000e0203c103e41c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 211333435 1250 211332185 211332203
    0x1b040506100c0c03080f040f06211d010c020c04060905040b1611060c120a05060f0609040209090a020712050703081602010b0414060406050103020f09040e0f010e0a0b090a 75
    0x1580740110303010031441c0d40031521410004000300120340c41c00c0291101c05000c02c0f21341c1c0d4490030404d110f00080d2a0340d0100c03080c4241e440d541607000c244601944003c5601d480000ba00356100d1650f192080a08807a000c83c9500e0f2118005043da40400d880f806403070251814030605995210380e10445004460181c08044c6a0f004590300a02030002c034070080c142860040b1b0200b24440c40903081c5003080d01c05080d120000035201e85141030074130080d588514045c104101c1032402d0300114103100b10148040748201700005482a00d50b03150741c1661004030024100307029616142d00010025401404203842c100d43c0c28031901c0000f031049040315802c9a01d40d0f5000b4880d160380b442525400500d007580c1041d5520b031000070400391928030a41c260010691440c1403103042c8030060204031105078118030304050040002c0c0d04001c01c0340b0100d8560030000e0b540001c141000c1500507007051044405031341c0550804030080c13044580090120411401a20200c007507883d0311240f40d950b100d10325802404500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 211334685 1250 211333435 211333459
    0x11e0f05042301080a031d150901020307050313140d030512071b0501090c05040c0c02100c17070201030507080f06010804050712050304140a030b0c16060207051b040506 74
    0x40c10340280704060000c951008058003184002c11100c102600715001d564016150803092507800504241079609080d00441040c4c4203001144e00804442100501070100045005160340708101325508140c20200340c9451782480c0103518040c1441d0305c500d69045c0910b11015859141102031102100c2d03041d211a0b10b0180f250b000c0c0f41d045003000f4030300d805012050800700c0400520341c0e80f50400e20f1091000207865083c503d018585e21660381c004a0190f880e050004400d40d0b00200103400594044802e00c6840440402c00c42d40c41c81c001100030303c880034090b080307244520407102801e01c052007604c0c20301055458210845160000312850450a079003c0d0200c2c0155025203500e503080f41c09070040d100d9480d00d030300d0035040035403d48a00f250564000a0200410f911010b46041040d07021190f485205185444002289a000c5e02114442000045419070403460500c1382440592161095458901130300700540c6030143d104042c004807160384490096842c10744280340c85484020704401e0180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 211335935 1250 211334685 211334689
    0x510050a08090312011206060801060602030a140d110d060b03040b060415030b180601080312070807030e0118120905031b1c050105060a080a05030405060307020c04060e011e0f05 78
    0x74202404201560004004810240010342013a0780a014183c02c8950246040c0c60900308581c2503501109140c0d24040082c8085a404411110700f0304151078a8151210803182c00c030007520400c03008444962400d00c049405031400d1000e000385494003081007040c540d8030305040c000c030312003224000c000c00030302000030340c1501d4561301031a0340b10521808082019160b6407525a01d92090b105000081082c1006800880c41045600d000d012140091803c5c440071840d0f145400d100641001c00f4002c0d24070000e02581e120350300900d1012500c40090028030380d000d110248650b10235a084e41c4100d103091400c80468041c0000a08452015004104010903601c40c3c09109006036207180d0f019148500349007801070080d44003441980070b403000080c1c40c14181d080244c403400c83e5100e0702d8581c00040c084000b1075800b0051314100c840650b82e040e925524500224141200b02d0010350b40f00d8546800422100203802555044e110044c0901d4141c1d03c42e00d010420220652040f0000080d240e10148414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 211337185 1250 211335935 211335947
    0x7123e04060816050d0f0b120705130e12030408120708070903080d231e1e1308120603060903070c21050d0e030c01030605010e1521040c0510050a 64
    0x201c8081c030703001d420f01806080303000c1502d1581c1c481080392512100c01968032300c1c0c5050326510404a9038020100c080ca00004685001d4045181811080c1d0b50407031000c03140018000c609011040800f46e642d01c0c605454030385085d820000020342c0d504a080000354145000304c00c0e96002c0c840d107445070450103156a5520903203a11000719541615101e440f5214454403004804411503003130781000c4010310b0003a1800c01803c0c00540d100e1079240d402c805104013006081e6100098000948512440e42d4507100ba042e8450341c0c150000308164000901140c0e04403401140074040d26044040c0c034071903107a8940c000e940b40210500940001c0c24031908208610070b0107410200c01e60055901e20403d43c480e1103450601c034000d40010003180044c11004083c0ca018411840c20113401d0030100aa181001c0c0020b06125510804070700030014103206a0006030400140c92421110300102d004207030712803a06484518041d074080344e11642030b039004515440c0c15210f1020041e01035a81d2400c11140140c11655 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 211338435 1250 211337185 211337221
    0xf070f030c0e0907020705030304030f0b0709030206041a0f12041a0105030d030209030f0d0c03260105040b010c0501020c0d02070f080616090f060521060907123e040608 74
    0x40d44031b4080700080c1602c0031300c042c0c40194020009002c4030a142c0c100a50705d0740300100315104000d0302c000140010794504094505442c041036012080c0d940c1d4a01545c002e20404045545600c40442d5801d030820221803600c0c81584105045101c0004031040c40e00144020700820360305801c80f410052410b0b00c01d40c050120b00d02c0c000c04813081918a402d1850901414910502c0014012503460061541014400c140360004a40601c000001d0a01d003000006041c020640b00f00c1d21440260300683c42289540c1d84950800002c40d03403400480c4d9119603c0704c7e15180b040c094003c4410018001e075486041104540083d00644a983e44419411030300a00c040105800d0219500011607461900c03003011002d0321264a4003541c4080908014440200020203a452662030b1010080c503134488044040e0003000c0303400c000e820b5404d2075508402501f07509045480180056081030061030310721804a00e181081a014030002400100d80d000510960044201284920b1702140c41c440e0f5400303078012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 211339685 1250 211338435 211338437
    0xc07120807020c010c03170108071502060c0d0e0c180106030e0a05060414100204060909050114030c090a14160e010216030b060a08010e0703060b04022d070b0f070f030c0e0907 77
    0x440907c81c60400c0080700790070b801c6817911b50710640081c0036003190142e042883c001d040c0024112490b04034104480c1d4071a512480c00c51640755508076100400c10007100c000c008009100c10340c43c1060980074040756509214501c000390400402d911401004521600250b4100c806828141c3d540d84030088510b00c0181581070034800d003144420a000a48080c0c00030302107641e69415983c1c80c0600d400c1c2610010b0700a4814000d80c1428614203650024000110000640d412000c5982e5104914000c2c07a250b5500152801d0b00410002c0c1d50b40b00404500e07404000707407540340000b03a080340120b0fa074252082c1c22204598141a05201185a81a6450340803500a00d031101030b13511100303864292001d411b03022416a02c0300b181441000030074010b0407001d440580d011410b08140d1800d204003038100c0440080031040c0d441c003414a121740481201c00707580d0001000c06c0b10307003000302c20f44580310400c4800c4400900803421f00a01e29110b401008100803d503681c203188440c0c5c0c20104400580301401d494 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 211340935 1250 211339685 211339697
    0x3051608040b030c03040b150105030f0a0f0c0c20100c05010b060705010905060c1801030207050f0d052d091309050613020a080f031c020906030c07120807020c010c03 73
    0x9440c00c1e0b04004501c11400c992410381c40b4109850301030f80c100d40180684007004c1e81d116949940380d0344401a0396100c5c1895809000586078507441c0350041103840005a110350421724242c01c100e40082290310b075076200b050000c0f51100e05080b15081c08040500b51a440140725150700440380c841c03103604541c20f0007a800010780c055110000303441907222840850380ca03510b4802c0031051060a0004550007018110080d1804042011401d03001d0010520541410340c08130701e540510001b00b065800d40268034013101c441520380540075107240c005541101c0c0106494050707403040d840c0c03071030703d2140601103d00382400d02c42c21400300080070006034054010301360394400f03203800b107002008810300a002d826060704000d0000d00510610300c80310b41090100d0ba002118040000748000201e030f10101a00c1d0381100c04894061000c03001e4441c8a100541c842804024400d1071840c81c0002d0507024803800c00d05000312407100b0203550341141200ca410140c2c0103102c1e00c01055008105002340c0c030b84245080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 211342185 1250 211340935 211340939
    0x3030f030a022703010e1204061b0602030f09120403030507150f0c0f020c0105030f0103080a11031305120c09010302010302090f041109030d020a080703031a030a050c04050a06030305160804 83
    0x1414400c21111000c3ca0a80403003120b00050401784200c0c45108010409800c2c182c1d0740040b001000e110f18440c90301045520140c010200444140c20b03484c7c0c44c0d2001c0c05541d2030800344280640f09200f079a9034407c0d0300510604001c0000e040044070b0440c1d6250300c4141c1007a206440740d0800e080ca181e06801c1d06a10780d50a650104e105214203900d065a5445200f403405002d800240703801d50b107ca140b0b0500c4030403c00c0c002240c3c484609a811282c2c000110340c3e035103080840c2114841c1540c030010810b44400f240c1c54104003203080c0c42c2e00a41d03c0a035501c95600c250b0110150751003130350311080c60704450b0130001403001d944290010f08000394041c104980907140700011030106c03203000c00b00000740f11b4045014106407a0910000104040c144018010841142c0358400d00d8070a00d10020300b85a92000c40c1004a84c8003030f08034202d01401801c3d611008420709205460340007a90100d03218500e80341c00151101c01c10712800060741d4141e03a5030b504200a088000310911503d01040d03074901024800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 211343435 1250 211342185 211342207
    0xb03030705150709050607242a2a030219080d050a38240c0c0901060203071b0f03031404050910090e070b0a0302160b010906080c03070503030f030a02 66
    0x2003607c02d200f14840500390800c040849107102c07018011058460403d610b0300690b680e50840c1d0349040741d5240c0307440c03201070324001f0035140d80d06000c12085c800d074510700641c254100300f14446891b09010780c0030f90352040015a5080c260040880e4003e149007818002a204500c45078043c6600403408036000403140d003082c00c100300280c1c00b804045400801540781ca03032444a1401c88000c40c00090b680c0084458540d20030101ea180d4008044044d100c2c0481d080c88010002c10050740382ca04082c0010380156160000203481c2d9100641c1507a501d088040308260014080f0160740407101e008000c000d149003940c0d0304961922511441d44801d481c148800f2840307645d90b000301c5000307c5c541503443e1501443c1410200c00d5541d0b140c404205600030450403c52085900101c80b50b604140c84e0050340c451110308403209840280340003411500d8200008500a40160b0040055a4500e0211048140f40358109650b401407030149581581003032200c150270307902400103150021901c03d0054104112503c07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 211344685 1250 211343435 211343437
    0x50715080708070c020a2301030f0b01170a0603080d06050f031b010e060714010203040510060e0c071a01080105102702030c04080102211e27011107060b030307051507090506 76
    0x10300318170307c024600310070b041c103603010b100d4400921010002440b003d0740000010f40001c02c05110001c0c000c40400024042c240c003513021102a55011004030303244c1416103070100c014112405002d0241d0b070951090a100d15001074100c038000c00003a02e0b03103100b0354503a00464031f42c40f01310300280d0001024809a03001928140703a03880701d04440400140c5916003400d08501c0c01c2c1c400c40c134000b0301d6807a10301d003400202c46104202d40d1100740d41e58001e55a400903d401e2811024031071210b41034000400003c00c07083c0064000354015100400c0e01042030780c8516038910640038500310a0300e1104902245e50307803000282c0107164003000c3c1d070801c1402c1664442075542642d1045001903214007548003006a01c2c8001c101242e0804030790200300e00e2035000510054085840503195580180c43c8580c00500c0005c1e02ca14800b09401480007400071b0f44102c10240700d9904100d004540c41c40c01c040301c4100d1030400009480285030020010a04070002c1d221766031965001400d403000700000e00c10085100c0e11040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 211345935 1250 211344685 211344719
    0x9030a080309010b09012916050d02060106031d06041103010207051509010f0c1b06020405030102040f081c1d03120703020d020f01060b0d020d06090603050715080708070c020a 77
    0x2d4008201c0d091070740100110004160080c1c4010040c201c1d040c03848000058191410000b24100c5554640c0c0348044a40d800041480061042c807416880c4440e050303010801d28102c40300d07502e0601c13051805c00c50f5207082040702c0e00c01190a5100328000303404207018400e005600c0e40c1c003800051800760b4545407207061081304000c50404525441c10310000601c03d1149984806014008000040f500c1d0401004014081244440c3c0301c40c3d0b5082c04144900b55046800506c00140219581c5036110f4070756406904500c201401c1d130046484040702010205200d4003801c2d41c3d070792800e0348140c03c5122a0140242d48800d030380c00d407141c5402c1d0f12850b040e00d002016000c1c025001422280707a031100c021714107140304080f030b4a82e0341040b2040044040640968544045440000d602c0b690760102420003490703142c0c071aa04050400c000081441004a140d80c241c42031481d0081c10065030342c905650828003598a0350004284c1800250440c3c41020720b0b2190610040025903240c1c0e554520786a925564 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 211347185 1250 211345935 211345951
    0x14010e0a0306020a0c03080a050f04080307090e0a0614060c03040b030a0e0703080d0b01021b04020d0b0604030c03020909010515040c0302070209090f0106050121200703020106060f030506090c09030a0803 89
    0x3402c0e481041c550041f816a601440400041c01903140c00f00310703080d03c114064401042e840c004004150b5080c007480c860805000000801e0b451441e220b56194094001031150f1100c0080d00c04d43c002c203d04001c03040703032681c0d140d200041d4542898800103184980c8014041c2e8401c0e9a07680c44440d49102c140301c010019401134007980e03107408140701e407081100e08035005907040d0351100103d03000d031210350a89044829000c0b9401600e036080b00240c04081d141071060264000c1000a0100030021b01c802c0b032105490098810b115140d89103c0c41500703c40e0302f51560011508241c0e03034031003c0e1401c2c0e000114481d100e4038025041420640c045400c03004156003500c4180c000b01403403500480c0900c91240180400d00c1c1041d00c91140c00c0f030026a816110a05500082d10740e00300001c41c03500c14150004081103241420b98031112410700a0080c5842d0003110b00240e40d05401c808811b00c03030300132540581801013503c80366031541c10350b02c0310a07130007824180e40600070780c0400b801142000f00554850b80300c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 211348435 1250 211347185 211347197
    0x17070608010b0a020d08060d02040e06180706120b04020d050703090b07022a180903040f091e050411040e0313050103050f010312020309060a050a080106020714010e0a0306020a 77
    0x40100203050600c050b00030310400241400112241c9600007100b034407950079820580d1550316508040389901c1c1d0540030203174209040560f007101031100041c507188108103503018040083d00302e501c580d40b50a4240705003070010310340c060074034601c045603400044184001080103140a14002c500b0041d600122f4420020036903644103041405954141d82d0b034019800e02c081c00070b2118451808494406401c26100c90b05501c90603a4181d4480a401c07200e010340c0085038120714502a6034296881d401030017060a24601c204c0d00080b030710158054901c00c14090740c10141c82c0418500c50000419004000fa1000c01111081241c0e9480350310a0404015199003c2d41d41c1d801a1300070ba1440018a0380442d042500e000104030025134500b2803541900e50000201480002c444800c078503500482a03204e40c404000a44007040c550028002d0101e481c240d1140c00d242ea80c0c60500741d07141e1050b44502c0160440340350441941e507103c1c3da920302001c0ca000303100c1200c00307407240c40b0f12049800c1180303142e000c82d132 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 211349685 1250 211348435 211348439
    0xf090f060a26010b01081306050a0902031e0c0102010510030b07140301060c05010501081203040f24020703030b090106050a030b030f0d020a05071e120204142e03170703091707 77
    0xc02c0c042e031315503050301b03003091081030500b201c40034052807840502401c1c940e42c40003c40e00351911900400c1c4620f40007012508095024641d52118100c0b02d010029284960b18600516500600401d031040503030500c6440300a16640320080039020013006e082c10000d040c0c05c0240103541c200f0265020740310070307910360402503514035040342101c0b8103030800902c540c800c002d0135031902165400c0302e51140e030081100440031001d14202c040c10052021180260b08966020202070607241c0c05009618040c0d9401d102102021042c081244c030280560000604204008014a4025009524030000290480341c03c1990f00501c2400c00914084003030040c1c0082030a841805000c022078000381c880c94842d981c00c1d105402d0f420384a440a48280e19000c00bc0c8105401550b9490380a40740c000d151800d120b0300780c5000c0c0e21220002ca644910300c0390039000000200140406104c529080c0d0f41d00803132640410210302101205502300d00d000302d0401540c0d10703022a116128004512000030181c00401e0814 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 211350935 1250 211349685 211349759
    0xc050102070605040b0304110307091118010c020f041d0313031a15010318061b0824040b060c120406030c1e0c020406150804110f090f060a 61
    0x2036100d0801c010060005010174003111044942040c3e001030076401e00596600032a09114407903121090062a007420800d600651000601001d9110010050102d840304015211022800c00103904032514030340d806458100b03940900c541d4600900c000c051800305d40080d030b24540c07040c3c90b540d214900c0d00e0010000c200030744e281d00041e00c0c0d182d0309000203803800000a141207014090014105525071210211050b507680e8000c80e0a81c1002007030189842041032070340c5c08104001c0c0f4000150075040011501c10101500258030100356080c00ea60301c0c010001c000c080c04400d200c003a80401304101c4613001c40b000700301004041141ea0b1615885070b140c0340c005012114284001d005000000f092405040d4006103012581903c40c10100c803499018000300380241010380100910f02c2c0c0ca03a4044554030f421a000910a520403020f40200c510500c042c0012100c2850403290030000f00c10101c0c1005150002c41548464060102c2118681d100b60078010386810000c0c414614000a11400400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 211352185 1250 211350935 211350943
    0xf0a030807140d0f0c0c09020d0e0d020105190207050705040c021e0c0108041401110408071404200c03120f01030213060803030c0901020a0203060901050121030206041205090a030c050102 82
    0x2c282d03128040c0420700c0882c0c001402400a81d00281e0802c248003504404004650107074502504024200319103c40c100c003130010041a0254520007188602000381030104e105014480c482d0302d002415040100800d000c241c003a42204404031240d0252000218036034541c4d03c01c5c03002208481c0e00414080c1112240310484004085a20b4404e8103c6115420f007a6000200540c100350702041407d01080e0b074407480c50040a4200782006540000100040c0100c00015071000b030f00d604111020030780700c0702c404100885803441e1043c480b240d8298460000f098103080030f08090700c0d0201c1a40d103803c800080d0f0720180c8404441d0710b10f11444890050095003400c1d2103042c40968201c0040258500f40012640d407030100405103040244000752088841c3d2081c0240c1c00110741c09002c4880fa03090201e001d0b406802c09000d0008210a501e00d10042810042c2c0b180c0f40c215096005000c080c0c03a00d45860081810200115091040401030395219440e140034902c02140a5090541010b00707290009041c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 211353435 1250 211352185 211352213
    0x213060509030607260408030a0f0506100f09030b012c060a030623010e0f091c0309080705030a030507020d030c1d0a0e2e0311040b0f0a030807 63
    0x3040000e01c0101c030300782c0b00016a0381c1c00a440e8104984240072000c442c454100100d6182c83c080b03098082807104010404004d10f02410200300d007406001c0705d12a0550884d0411641c1c607a0104210450b0100240510070001d080c202a00d000700340d003900da888000201c0d00a80c4981028900047c510444030500e03580302a07982209448400141440000910000c01500000d8072040e620482c050700081800003010140e003c2940d403581640c0d44000c804010a001c507036400e040c941c01000110f24844c0071540e41c210405031078039000740286090041340205001c150886584000304808030105408002610340f4030f1b156600402c161500410003070500705605000020705040415009130b040e08440103100d80036104d01c201c0443c0e8000e500107070001d070300c0e81d00440c1c9040c201401c1c040c03c3c1c0a41005070280003e410b9900b14414868140c101440c5c00c58407025108007612000401d00e880e02d07400012000f480182446d40070306030b1000288006030700380c1c401c6600300c10015445040245003c16820 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 211354685 1250 211353435 211353437
    0x403020c0a0b3901091a0c0405182a07030e1e0d0602070f050a110a060801052e0e0f09010302030a021002030c07180524120309030d03021306 62
    0x4140f041580240c0f5400144480c40c0c0c2d1003059030050100400da6210303102e000000070000074030000004e4200810444501300340e001c6c400186200140094103500c04850407a03901604100220300e0301e00c440409018081d01c1607464140d03601902c2850500111254050441c10002c7c941e2040c15240203441344070044240c60094aa241070103066146034000703103210b610305a601000c3c80f8800d2030070034001d128220340144000000c0400c40c050100c001013001e185881440c3d200310030715921007000400113042c400c000000314840014022070034500c0405205401108250f0b40060700c2040318584002092603101c00581d64240300151898840304140100206450310000355055401003901c07665a50406400f660b00c0244007100a4420030445091031101000c0d66045621201c90b07100480002000c039a0a40c100300c040340440c0001c244000c1c5004a40e0b81c0100c002e4070000902100550180d6401c1e41c1e40003d0100e40856102404003640d010f11075540165500c0f002c0c00c0b002030314241d9030003800c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 211355935 1250 211354685 211354687
    0x302030108160f050607050c060301120519020f040e1f0f0606090b030f1008060903030a110c0a11041e020d061a0f0906070f0516050102010e0c060d0b090403020c0a0b 73
    0x500300c0f01e0320f0341055580681d202962040a418050f192803010004031fa0068400400051001d1101d00b0401c4100d11840030b90f00e440c040c0b24103821400310b0004010b944211045001c0b12240341642c00402c29440d00f50990f0ba040302800000030f018150300003140e00312a01d40c0c00311b400c501c88510540c805040542042c00580b13003407201c503000d1408000e000d030075003003904c0300403915400070007070044001c000e030008075491890007034042c1c0d842c0e03001a00d040140b00c0c107000441d800c6026003401d40b2142d12018000300360508041c0ca0386201c1d1fa10f03000949400030354802d00c0031408114281248686114803c0141c3d540062001400469071154001d60450300d101171620750304d9800d070003180c03d842005150390382c032403419100084503481108001000707507504026400802402081c0303500b44100d40c21115484682d00c3c40160700b40c4000c1110040d503a0403004aa40407403401c0005001c2e140b16540c40010901c0307030b141c0420201c15040e542500980d000b603400420390b2403d00703040030107000032101d81 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 211357185 1250 211355935 211355939
    0xa0c081602030f0906040b0a090306060909080304020409080d020a170f041509020103140a0b090f27010204030c081e031216020f0118060501050a051c030e0d03030203010816 76
    0x2074507809050f540e00b03260600024403e5060b0b8601007a1005480d58030401959203204000280c100c6800c0d1004952581c248100004c50580c0c40c843c0200d000d030010111481c564407582040000e180110088034503100601582c1140b034110700c05440190320a480f178080f000041e02680ca1000c5004041100200d0300e4820407000900d80f500c2110a4154030101040d004028401640503005178038401740911030600412056004541083c0e03400076007a207020005031500b4804080f03058007111f001d901840070900f20015448904c04040d001013084000609058584c3d82c1c00c050840d032540022101d9000420400c40700c58402c214070210054070005502d1301406000700200280001c01158581c440004007001c00d600900c51380400d89501c500802c00fa80c5184143d10207196148170596000d49010008146418278160850548030024a0b4003c50000c03401c2c00790500401820460810208141908060312011000c0031040d00c2a180941c4a60500e4803042c40d040d42e2150441003082e0310441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 211358435 1250 211357185 211357187
    0x20102150402010207032612010e0612060601050714030304050d020d0816050714060a200306060d0902180705030403110a020a1a1b0c0405010b0406080a050a11030a0c0816 75
    0x80a0101c0f07074407d6413100380c691501c00a050880c501c4010917408078000550010200310104081d040c0e0700e000180d0309250b1200c006200c044400e101c07803d9282e901040209011303601a5015000403440340e0501303803902405c0b03100390381180c20656040301c0d164400794103026060340602c118412101c8901c2c00c1e00071490005003400402003040c0f0311385c052002c0082c500041c000305a040075a50341d0098203c2da0306040c801803804c02044440500224400c0e2407041103050701100045a0203a000184924280380c2d10307410810003429407060891348216040052444000c04d80d038428441d200769110540c9030325141c1000390200f40d04030b2000107640c211440100050b42c55102040644111100800d0400440c0411541611800150006d030388c42c0300c004600c0904c0c0000e14007800c2081540c040c00166642d0701c4181050095002e4040840d0550b4002004443c0c181d11850740070a90102c0402c01300e002190150690b44140d8500850369201d1036005910394112600317a4221540702504102040c607544 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 211359685 1250 211358435 211358443
    0x60506060304120311160f0309050a06021c03020909091011091819141609060203071407030b0f090d0203040803220302060a0909050a0b010903080c1002040807030201021504020102 79
    0x46400301341070f92034213a076810030162802e840400005185107980001c0b641080031860904040c118001000b0940210b1581081c003140c2046513200e400030100742e0114002c0105000c50210ba6008042e402d21005a0036170354008010b014000c6d8102901c000c01c08802044262134000310010300f90401008110500d44a20307180d906111800c800200c0c3c143c440c40b06a50220004684244807a801d00c06010700500403030318841c1c01204810031300201001e940000f0380380c81586100d10320240c0c00c148052401301780320000c0b0072900140e00007a600401c0d2241d80300b620401086d2000c0e070302c6c0e10001d030401c01407000822450050541a0009605061912454582d41e11404120f0402200c0e200800781411a038008040050b5900500b40350b22402c821030010076400c52841080e850781d0500c00402c4030040c4c90711842c41c100c0c4041e50342040c25425600d600c84a03901c5842e90964038400c1c0740d444411b00c4000d1001d0300280c0340300ca010745185461030000a14010400c100090b41010701c00a01006070b030000303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 211360935 1250 211359685 211359713
    0x50702010f0e0901140405090a03020607050d1104060503010618030203030919050402030405010b03070f0506030105041a041d0c03031201120507120506061c050709050a0216080403060506060304 85
    0x46801201044998400c5501c2c0c01030641c40303604403034004000704040c2948000650040e800b40d804101c180d079650320341940c5a42e42a409000f42e000362011410041c4110010303c0c11158100d0b0102d41c0c042d50030380c2c0e1001d0358000d600a400084010005110140c2d216000345040700403203041c21510b50442c4c00103030f16846840519032046c00e000c150780c3c0903907a0000008000308401082107441c1d01e42800c289010340140c201aa100b4000d200010a0640c149601c2c202900d8002e4007090a580c00c10090000034940d603078099424084204108010751348902075000580040c44641000088800400f80b0b05001402040e12a0300288607001c1200c880300051340c111101c281500134083c4090401905090894101800c0902c50008682c144030f40010040c2c0551002c0c1c2d0614141000d4414904180400200061954101f003104201800e0180c100b15040100e81100500e4114415120303c0000c000c60400c50b9a10780214040043c488903100e0503078050b10940c0c51a24626160355180360100e100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 211362185 1250 211360935 211360937
    0x5060f01050d1106030a090c030c0f05090c030a09060e0105040f0209070e010c0204091b062a081207031506081008070f121104020318100b01050412050c030a0b091002070305070201 79
    0x88001b0786031410035000100042d0b000380143c10b13900d4490a2400304440030340070b903421401c3e00070000506804c0030034074180301d40d8100b50404e040d61038002041c0050b0600c010151000d64840c625408107103c2071164602851040100240f08509072051142540c0000d1654003400108003044526036049200c0210465044a000030804100d240c40c1d940f070300d44e0b40440c1001d11041d08001c02c0035a0010f4405101d2100000055901200140c181100002180c0d000b40090400e006505040140c00000c0d600b0045508003c10303040100b281c003141c44078082d0300100000380d03c18180085031889161040c00307001c0c0c0101801116080c0b0001c0d981100d00391040d0081207080d00801024051a00b06801b50350200030030544d5641058000000554021010300301d241c0507000c0014062070044c440d80752403440686035142401d00d0081041c441c82c070340840c01e1fa0103018961007951207580070720007104610b10a030322402c00e5003421030f00c9500e008540c0708071111292040084c03402103074010040d16181942 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 211363435 1250 211362185 211362187
    0x305060f090a141006020c060702060414040f05090d0809060115050d0b0402030a021b0d1b0303020403141507080106051b0a0501090506090d0306031a06031905060f01050d1106 77
    0x880382c50781e0082503003c90030b03074016200d9001e2000c00c0140c40314031400c49016508507114060400208003041c400c40d600254850810001080403803000f01e400030001900800015100d001342030400c0954100300d42000c000e4200007000d104650300b00d08010303003003c18000142115810882d030f10101e000c0b209512424040085401209500241c214004181015000350b4072400c0299550f0060340010f2183d0500b02e01c7c140d094452108001b45041600503a617a810315210f041116005500001e0a016010560204000700100702c03034030084c01300401880000e10003581000358000c03805801819500421020b03a00400c403150784a016100c50b41c50310341100c7c43d201002807040785802880c5000a00c01d5007819900b40034060040b4016120703403556410340e1803400100004400b1110780e400020074110141418000c4810a0030010b0790000d000307400c4501000d900e00f13031401540080d0703000329480d0740108100b0070140d080302d900a004040554101501c1b41465582490b0308510400d00340c05440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 211364685 1250 211363435 211363441
    0xf0509190813080309100305090a0201050c070807030b0a060b07050c04021317010906050601091805130f0f030905010c050a021e0a030303061401020c090a090f0b0f0f070305060f09 79
    0x100036085a91880b4407a800d6200d20b552100940c2c0c8980059005070b10400760842140c40e0b95005c6d004292044034068050010b6460560054540d90804a1001d4848c0726010010840c0401040f901014500500a03003051f86018044201a2117040c0c002562000b403d000c03100000f5000281c0b651107010484015850788114140c0180040681d4000d518081c0304113400b8018a006520444691b40035020a1017561f6072600152902c00d600e00c0303402c14000721484010800281d82e4410741e0004110194107060352515144c1e002841c0a528041d115580c0c007403c100105030f04080703580d00801007801c1032003a03544640c50f0152900c044a0010340161a01050030114524080002e10025402044200304540b642401001842140a1521200390452030785403d9800043e5900b01e050b40181840d140d56100501c00000d02f6504204540b1900c988000d40009a2a1516035210301881400341c0c0310b92400c00881c1c0c0403804041c0c560004c0c145444d0038019070b611840080f00f05294166a808000d031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 211365935 1250 211364685 211364693
    0x6061306050a0303260f060405011a040905180f0312070201060b04030602030a1e061d040209010b160203030f2a3a030c080f2203180b0d0f050919 64
    0x174500d82c0c0118007241020007000b40748001c5100d4180100000d42d010000c0e40c2c2c23645d50040c080c850709104035158400034002004070b03005035000250310901e55241100c41c10030951400b40341c5504152a000e147e04007140211801401c0e919050b80200381d44001d120700d40c0780608140c43d6105502014103c960000005030303d01055800c03148144145d5640090341c0700740391800c1030061485003d0065542025103c402c084038840200038010307a002031540304240d103000710880c03160744243c4d109038568007442661000759a05001400f69030718850741d1183d07545601818070341011210090b003290344035240e8201c840c08200185080042c3c00000c100030040c02d2131409007c0700301e016900d890340d840c0700307201900d06036a00d5000303106070000e191185c04054454074030031341070f00e18111085150304044007254000c1c007801b119103005141c00f9040c000707941c0707814240d242c2c10031883d80c000c02c00301c4200143c01800171b0028811146c070005030309001c03c01420700d4940b91b84c841c1d45000000700140c40200b9020180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 211367185 1250 211365935 211365977
    0x906010e01060e0d0203070f050a050d12080403091d1009020304260f03011e060203071a06010c080703021e010b01051210080f07090b0109060221130806061306050a0303 74
    0x244d0b80080448441303655070745080c0c606691030b00940380aa0307a80500000c11742044c45c010a103040c0d00940301151070002072000c440d0b0040007403056017044400003000880e018003e44003001d007101d00300080440d16195003c01440402984220b018a01c10410440451600350340c080540c40d401c2000c4010302c0384600714000f18041c03401c40c40070100d400400041c80b00c850a50b5035004007440a140e0840a80da5002a0f0b02c03070056140161124841d400b9001081a01d1860540d001d03505061400034884940c80b12401c40d0880c1c0000c8026900c83c44032040d14a101400d44004e50f00101d0003406012000e00c0020203038010500305941120180001c1414124000180009408100100c80c00ca00f046007840d595182c0c24414290040c0c50010340755940d5120351080c10680d90749800130f01c1d2410080555071280c406d010351ba251103500c04e111a4000c90b02e014110402890088020140c60421104025a800311146031070b0909203001801c00498481600100c1140d4044c00d2040312080402002204 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 211368435 1250 211367185 211367209
    0xe100306081b0307081203010b0c100e06041403041508100b120708070e06030103080702040902060d140903040806060d03030f0c0306090b03060f0c221d0906010e01060e 74
    0x14a02030ba075190030190b80382c0b042440701c0c5501201110100b55441d0300d1652110518000d03418000400c000500149a105008040200c08182203516404408907444201e039100b81c090165600031809200a01045445001075a00c0c0c14020310f1815280c082019440b2060605803814003508000180c41140380b07000050050aa20b04003a6803010161101e02001000325a00d0b800700320303001d000c140f100d481542e0a410010300548501d2540e42192141810740d04220001c9900c6501c4005103001600c4020141094240e4500041844c2c0e80301a2900c0c13031007800500212440e88203100800c0210b90025030103410407010340e4100c0d800145814100c1c040c0c14030032106c1680c2401c1c076001040041d496400401160300d0800304005080d0000704158403020b0948024180e01c80c04000700d138013030703015000074100503204010318503a040141c450320072040305039446584280000c0c0140b2030f82c0540c0c0700c03805a002c4407100140c5115030610264581e03807281030141c03000f00000c56869004035180d510303840e00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 211369685 1250 211368435 211368449
    0x1030e0a0f0302060906070302030603150a0b0a090522020a051002030f03011410030903021c0903150605041503030c120504090516122717070b04120f0e100306 70
    0x41c1462641c100030b55a1441694180914841c0f04001090b441c468400e6900070312000300070b40042240c00100202d03400020b80480d0385295107000d0100c06603503000040c001410907840220366413a1071015100890420700584d000c3c5880301e040e210040c2d5a0030f100c074040e40d4003150507581c20b541211b402c03403841c00784a1105603402800000803d0340c074152a80604d03a1202145c0028030004524021816959940c6008025a1100d001d074000002d070399403415800300c11854a01d052070381e640c40c5d502c4045550901011100c0e0355000a1000b420a809030012002c00980c7c803c1490b450350ba0014891110b284010b04036180461284c04800d03c10340480d002400e4680043c000c6080904c4050460084602c591004c41c1002094900c41050f9000f12075454001e50150b00440604023100c144181c4d80c00404c071842031030000c110000403c08000f030300c5618004c807694400f03413a240c80c4c0340311030151188020f424810b00ea00c0200d8000c0d40645110051321007607640d01101440b0004c05d8002c1c2041b038020315 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 211370935 1250 211369685 211369703
    0x70203040314012c0a120e1008040507050103050402030d030b010201091a1602010c0509010e040605040603080301140604030209061201090b09030a030f020909060618030d090302090709060e01030e0a 87
    0x810010701504084000d40d1300c90401c4549036461428800c1c0720444849084c003e8010f0700311003000c01e04058000c80002c850b030508008a10b9104000342004007860710701e8000c100c800050005104003080700c2c0e005008203003410401c030b042540000c0d550ba61a882c081040640b0b410100007aa4400c0d003044401543c400400300c000358082e03048800340d05088803140600340c1c070381c81281d4215205001d42e4640304102c1e160146880540001116014280c4a029070020707100c031000640c640382c510920000718043c3c180030b6140e50601e0007448140c00400c01c1188a88800e00c410b001595906102d2500110100e40c503108002d0a207803800c0c0517240301140a01001d04c203004003c0c42120202c0141514106a0360170040c0151210114041b80100510540c100c1034920015081d410700900500898007081c2d85a0403e10170030700000c0c0b404226551003800035814010130411402c180380004e401c2011410035910207400c240000f40958000c14a8a040580b01d000c0c01034103000501c107d161042e048480300b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 211372185 1250 211370935 211370963
    0x209011b030c170c010c030b090109110f040b04050307061103030f0a090b04030e0f0616030c080708040f15020c01020a170405130e0c1203040513060b130602070801180b0702030403 79
    0x5040303e03811040f200c400d01d5003080c140c44445880380c4542c07030075400000c0c00031416034240300300003006100550a4560500040029103404050314014100424180b60141d03500ca041006043c145070341644150288440410740b4a480305012003500e91144a40e0040ea41c0c558481c0c10000203003c201d000075040c02e402006000902d030b485000d10394052801d0f9031248000c00c0403014001c030340c842d602110000c0c8800c00351040000e4444c1c0702c405c1890b80602600703070402c0e0301c50b00c0c1c00342d403540160303c42c0030a0880340100f0484424000c034080c408142c01d00140081415840010313459407152000100307103040f070105aa004c03001c1d55044d20040c0c0005444640c401d0b0300c00003950010142004404041e1081240740502d51405a4441c01c1c1220100050350410340f80000380a100b064104501074415101c2d5408500d00c00202d004d0201040e24119a00050389440d6000e0304107130300d81d0016030035039060030070301c110706030b4402c2031103990b141d00c0b900050350303036070380550890450195800007440c07a02400a5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 211373435 1250 211372185 211372223
    0x5030f0a020f0705010f0501050604140405060102031909030201080f04050d081b0a02070e010906030c1e150810140109030f06020d02070b0a180b0a0b01090302120f01050108010209011b030c 83
    0x2030000c80c10003081007e641ca980030441d1034081d5102d644421000c1d00440c1c0028102900b0854000c00b040c01240c2c01c0910345401d802403504001041f5001a03001d030403c2040d580c1c414210f82d08585841c0e5040001e091a0b280e40781c443c0041c0200c1c00900003c100811900e110450030f09151001c11150f2070340303a119460b0000d445106c01c0c800c1042d090455000030401c251188511400ca940c41b4400c0840d2518010781e489980140044801c2281000b9000040c03218858003074580d0a0710f150342d62001c0d41b4101c070f0014800002d030b40042415804d41b803080c0150303036000304100d82960303041080152044001e181a1010348a4a182c00704c20500124441c0100030b0001580c07401a088114207000d05140080c82c50100e51314a240a040350b81d03c100840c015a0b07199000b00040788042c508980070f65100e401181800c40307031070706542227580024100c2042d03180030700c24a405884131000a61800c5c00c4c2c0e01c0000c00c1003d412002001d408500849101014041d06a162900c0c0d40410281e2590419441d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 211374685 1250 211373435 211373441
    0x510021804050c0903250e04030309020118061407051606081012110d110d080c011a06040902030702150403050d110720121917040605030f0a020f070501 67
    0x64603030045080030082080004981c0540d115032001034000c1090b03030143c00c00b40d06c0b05a4050000301ca090280d020102d220308202907150720a9019440201e00e040403071000410440c558007601c02d10a0f002d440500150b6848600c00e40004c0c1102034160319525a410010700f42024054071000400c0c05000000785680c00000c507030721820703101d0310240300304c1c2e07980d0500c00319021243c40c020900c000b44100540b80b0b00d40321200e90096405022100459581d280115419400003103040d11a206c0100e041720102c4424021030101041c0e03202c0143c04218618042400d034001d5018074640140c0100005501e503100300400e1400c1d2031150070000315400d107401c02504680c00100c0c0d01d0460f60410800000c0502c584081b200010749c40a1030040e1805012200b041c040315030f00105900c0f101c002c0070340312600c200b0446480c1b0f8240c044142c3e85017050074a420852000c0030100b1001c5964148020044c0e550002c06883c0d122240d030114014568458041e20000c2c840c02014482d2a07801040d468240f00e0154 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 211375935 1250 211374685 211374727
    0x219030b0135090604030801050607060b04020a170a0b0105030103060504022701060311030708060420070b15010309051218060313030306050405060d060902030a0c0803030709050114030112051002 86
    0x6003840b0220348070190780ca5210042102c025020401c54001044581807130b200414400d0b004a8000840d41c3c0c0101c0005c0681c1e00600e92354002544000100c000064844c00c2d0640140542804114800e003040002e492800b052101900550703407580080c0540d12402c100340104244406604010018241d00c090030740c6080c0100b42c002440c11002002441e03180d000c5a00078540c039101c442181d9500c008100103454600030290780e040d034403000c110b0315040040103802198840c00000c044c1e4600b0f0311003e103000241000304c504040c1055640408a6008900b40f103900704000420ba03524800c80c810120a842803000361508624004100203585046050125180e8800e59003440b00710764070010841555001d44095500640c2d03907801d580004c03035542c001c2100900c00b5050750201045601c41c50003c00c1280c5c46420a504000304101001d603201080c6c401905090804060b06010581c0da5650780c0014021203440200c03585803002800b104010410450041c81c0040d07540300d284040380c80e01c0b08510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 211377185 1250 211375935 211376027
    0x3040303091406030709170a0818010e101b0c05181608040302071e0b0309070609270f09060504081312080f0901120609050f0a0219030b01 61
    0x9103252030302ea1401c00202c0307005400c9940c039075102d1820300110361914444144041030500c1050169400226600e02030041100c1d006d2b04507101071a0600094642038203ca0340c076100d0045410f01c5058503401c58598041c642074580282d00b40040ca203404880050290401071307021200004d1003640301c0c10151000e1281590f04103401c03080710495415125202c0c00c0d2002130158011030b1040c4010401c005407941c45100804490025903682e501c07601440c3e106960207101034101c2d50b0f00b4800140c101c0c84207401001c00369006042000d81d95000f5061715042900804503680342e80c1707403815403511504000d048982151081000b0300701031074120002da00121840c05803d030452400116122450100d144450300010000d18001025803201003550050901a05104c101104101c103400346d07100700b80c05049c01c0080041d0302e06152034119010800284a8801140100144c419422030240184001c040c542404200f00100c81c00580e4071940301ca4480c103100019442b01400440c40c010140000844 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 211378435 1250 211377185 211377209
    0x2070305190314090f0f0301020409050c030a0507050301080703020d03032d06061b0b18030a020d02010506040c0e04090203070b12010504110c0a0f1e1203060f05030c060306040e0304030309 83
    0x481e02e050503480c0200d9074055448a00761745000c409040103401c2c40400c4a00800051900d9291040c1000700d540c1a11030300d8442c4800b00402104002c98455150049441d003056810766140912040d51107445020080c081c052130000d6408040c065084401c42c800c09103c5080075031100c00e80380c43d88490070103928040c1810300703600140c03c0c0d004500b0800d88204984110701010b000d078448920916015019460600b08080011480c1105002a200d4600c05501411140c3c0e246000203080d241c0190440f80300f940383c8040e1201040d00540c502d841c000b0151400300c0c180c84640002401e000741540b05400b040000540001ea54041102c924141d40049400b08519941d80d42c080b0b0407400390301107668107680031040603408075140104c0307100120310412182641d0450428003c0d84601d901104452000c1110302428840d0f825015800107001c0440c80d80554501d032800181d030314880052031500a070400000710380f16444a4005042d0122108200c0b6511a6289001083c40750144201e1342c0c1401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 211379685 1250 211378435 211378457
    0x4110301080c1e0a061d03060702030a03050a050106050a08090715021501140a21050d0804050f0606030d0f0c0c060e01080c0304050a0803090a05060a1a010305010f0b0a020703051903 80
    0x14580ca4201d040d10b0040c213070910f1541482c1c81980c001c0801500d5442c3c0040e00c4c072141a40303a03420042d803480b4004941c061512a41403410250a4a5000d041c0c5080c0c6402d0030018070925500c01c0944800c8002443d04002c103403180400c2505002068008600030b142c00074201d14020303000200c1c0094543c00018030034440c0c0c0d90f280c00400c20881c0d1000542d01c50b4122204220b010b200380d03100c800ca0781d819007004001aa043c0c3d00c0c01d160a00c00c94030000895080c0003004140401071112903040740c0d800d80900803d2400341c000a8480308040e08040c01d0010781c00c840403d0070301c10240d009600d40e0000c04820110340b0b810028106041644030140040e4000c0c0c001480b041446054074029540b26000702600c0061b951108100e40000307105651500c1503c81e1840403c1d010000c15005020894000440c000c0014944c0c16070241a02901e05040c1010010403c8c3d001810440c412030342d15080c2c8940310102018103d045c00c210341c3c005032080c41041c1d01044544c1c820100300410350b205c0d44624610030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 211380935 1250 211379685 211379719
    0xb0c1b0c150405100302070312060e04020a0909023010050f091c050901050d1401030209070c110d1b0902030709060905010f08061201020a09080c120703030c0204110301080c 76
    0x4451400f800e0307048044801c41520700d9000790060b0080510a013007118640701d41003801001c940144d4885c960703043c1400c00340800d50074201e031840050305c1a46030601c005410380e0080340e06240b20146070080c8590700354440e121581101103a41d0000b124bc0d060340c20303400004590038041c1c0390a4640210900000e80483d41a540009040a046200d00302094200844c0c210507101031b001743c640ca505000d810040da0a60030800e00c211011840d6060309007501e941140140010030740700170500c0e420300c64550061408100042035007204240101d1b04e05101d5420b515005102c42e00d11040d11311074589100010842a13800c1e00a50710610407039035025485642c8540c00c90b6407485511906003c10802d10040d14424440c2d1010ba40c442c002800032600007040d194102d003283d01610360380700024415401440700380307014086c80c900305c401111031413240c800307110a10b0f403074420500c0300800344091181c1302411034550b90001d00e210000a40e485440750783d603404e05078903500c4541d0b00c0b9200e6600041e07003410710 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 211382185 1250 211380935 211380937
    0x60c07261504080c01020409060801020d0c18030605090c1206011509151b1b03201f0c05030415080601030c0806010507150c0327050a0b0c1b0c15 64
    0x12000c08400c455103900c40351501e01030384d800f1a03403000095408000200707104081d40164070080204400044c3e030b03000b16510840445400c602d600003000504c0400068498001902c08141c1e6041140004c10742c4036425028a407141d0403800a4110001c03c1c0a03001c9400c000c203101e412103c11001980da0240d0030305c01101c884200d80603400c45031840780b0000c90a203109500680d01d41d0100003080501000e01d840e11030b80010810032407040341000410a00400002d00900303606c812078900051000009280001c20864000306040804814480d400c441c87e445400038046041e0070000f130300e0341e0342d480304e0f40252031540140c5043c1c0842c200c000816000d5129104405a070300c910b40d1a04880e0700c0e4400111002d41c4402c6058611098582206c00140d1403480f40d40030130520350301c000503143c141c0c18610450f940c4000101200b060900c2459000c1900890134030261503010240000d83d9440d01c01c0100e41d402420341e40459110141582c40c8544800507070b029040310111104541c1b25a2a8180c00302 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 211383435 1250 211382185 211382203
    0x901060501080c16050a0b0a2906030606070b09030307110a020d0b070207031a0901051008120304030306080d02010f0e03040f0519080d08060f0a05031b060c0726 71
    0x29050900040e048090358000c1c1110940a0156296204150321780038030301580307003105032010304000c4144001260070b8400c6d103204d100b40c811503100d188030107592001c00d094034000c8140181000400281c9555600c42261141c03503001d03003004014100b4100859032138104485e5200811000160900d01e0100014100740395035005160719250051962410710510003e00b41c8815842070040110026440300119008000f001011000e14a001c040c01e0b401d484003c1e112084a502d06401072140183c081410346444081000c1c89030303640c8691404070000c1c8040d500c085079501582a0122100c5d0f41134000c184000d40313100301840f8044034100341c43c3e00c03486940b09054500c80f07840d40400050400aa85c0c2016000300000c1620790b40c0e0b41d00c066070a1025400d1082c000919910410a030383c5001c034000051543c00b42c030152007007411f01c03000c00ea80c0c071442c1d85130b01d041c000c130b008244100382d039010b040b01c4441001e035040c2d9050503699003508a07003958440600030120744402c003030301c1c40e07090000c2d4001d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 211384685 1250 211383435 211383437
    0xb0108060d1209050d03020a0204060f0e01060e030a060603060b040b040b0f011d030706080702071203050d05090f07080102090f060c191b171b030c2e0302070b0901060501 75
    0x4001c1d200c1e661680380003910b07082001c0a02940520018960b610101d240420f107010f50007070b00c5604610300c100412103d154102000c25140c0e12814400c040c0c5194074181034071010b007480041c1c2410a0300280c40e11a103ca001813190b4204100441081360507080b13070151074400c0c0c4040c01001c16a030200400d444a0312182ca030071803415182403146620410356620641c0190300d483c07070311820b180082401c001c00c07904404045401a000c4c0702e440b84d81045604010030b0b40401d40c50200e0041d6600501c28810460054242900d6201007040100188018246102120200c035200c1f075441410354007070741104991921039061422009002c0c00c00c0400c0b540280311101c090000e40144010074011100042815141281d01801c0103002a0300301c09483c6c05898810703107080e405041c541c503541c900f00440003091040302803200002c010341c03400141004510811900c001502c83c425a561241c403a409150014990360700c12201101500342d4010306680380a000401195621524000d081c0c40e02072242034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 211385935 1250 211384685 211384699
    0x305010e01052509090e01020301030c120f020f0111012901020a020d021915031b051e090414010f0303022415060f0304050c0109141302070305120a0f0b010806 70
    0x10161001860241003c6401e6050070340e03d19440d11411402c135101141110340c1a90300100600c107108084030f00ca001000078100c1d050044c00f00341e03203101c1e880b100418001d020348940c24880e561a0f0145181c3c03610305610100801008045201c4245500380307154131882504241a90460203520100700114441d4000d840300c0c20b8110035500f4005c0c4025054040a00008500c0e40451420444c03241140c1610305a58041801e520131408864030902410052003032000c2000740b26001c6100c01055400d41703013050203003602c0e411a0004100909107181c1303040c00344280c4000100e02069945019001d680c025400ca03000500280e800d4504080c6074078288503001203100c002164085d41c8004204649000740c00d40b400c119801d00b1001590700142d9089130b0380c0d04a03086d003600ba941d12809540041011000107003184410002084c140341942042c00046c44d0000b5000c42454000e80441d600600482811300080c500600c017840204a04a00b902900342020b80581d61903204035540e03402044020012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 211387185 1250 211385935 211385971
    0xb01030201031d0304360902010206100302090402150f1b15040b010e0406110301080123010f0302120a050a050a05011406090105060a090f0b1b0609120a020a050d090305010e0105 78
    0x32580e10130010402070000002180c9a83d00c06e4004203030f007560200c15400412070584a2002a04007800100381d142d12815084040015070b694903c01038100e0740607180c81c800301b0300040c5c5144142c0b16050159400344400100518182103c00401580340060410307504408140d541901d0079501c107980203450501c0810040c04100d1018900540040c840c400006254450441c03052041d0000d0f8000740b09030355030344004403102c940042586000450355145080b03941c14000e0f0440c00000d1400080d0182540c40202d09002404010a6158035004030482d8001d000c1460600e80d00d12030350301e08036059402d141980400400da140c61070300a0100825105480e030a0000340204e036040218200100410714900241c81c4691018050203040c00b1078000d5500e038480103a945480d0400c0d00d003065140d201c4c03820441e05900201d0f545000600c65104555181c105a10481c50b20f105c0c40c80250460103068146c0e00c60702c1c2c0000100013107074030600091240050100d0304c1403c03030300f0403900d010180d4034401c80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 211388435 1250 211387185 211387199
    0x4020a0501080c0405030106090b040506030a02010504090906060e0405060912040302010f14190f0e06030c0702060708070c1211220c21020403140a0807021e09040b01030201031d0304 80
    0x2d4a0780188030f80801418035540350b0003c0e0070350310b0385d9010208259a031000d440d0542018001e07140e200703500790300034030403030600740d00080040c807ca100780d00b407036039032881c9030030030080d568004c000141005c4851b05a181854203149840780c0e001ea54035030300d80c403c0012104200800c242568100c3c0d40586922040b800100816141c208515102c08813500e010030a038103486124170b10fa59004c2400c1da84001110165000142692803440320031441458103004000504c28400c0450700001c0e81662200c1d1240f80d289810f007094000c80c0c4009004208600011600c244200e5800c0040c43c0119040045080200c050089101c0f41180b040810310b5000100950b900c4a0b400c9442100c00900e4401c48a04a1151f411000b00310250180f4145400003400c0040c400042c0780c2d4149c0303090080c00380035080d50035136034000544642d080013405030180c4194851030424940200c401e02502401c00d880c2c0b441c1516082c0c8401100740001c0b40400d140c41c9040540380c1040d5000c041e02101c500095240c5410112 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 211389685 1250 211388435 211388447
    0xe090606010c14031603090504060308030a0b010c082205060306030a14160b030103051b06071709090406050609090106150e0f0a230402090d110d02060316020105090604020a0501 78
    0x601030311001d03806054010151004c100404001440080101e098221854001c1401005a000364441c50800b6010b1011400e81822030382c22150310350001a544400c10300503240300c190b083d00641981008117a1550032003440045800303100e0359040c500071192316200bc21607130b400203483c1c003034040d4090040280095400071389064851041c0c422211100e1840050f8007900055401c1409120350100c01003041040c00c0000b00648072038000400700c143c0011010a00d80e005e806006001c40619802e810705010b0948110340c050040a03180b51850315250401a000c2c0c00142d0b50180200001c00014641c04018450712064405c0c449403401c611019060440300300300305048a903031004081c800901d040e55492103d0004108141201d0f03610340c020308540c400ca200300c1c005980141d004001062a0b035031800900e90a050f0b1001075901c200c4101000320b5840d04880300000d403c003000005000030908001e00c800c121407403950081c09180c0d600d0071a66111034003520002e4201c10031180902066000d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 211390935 1250 211389685 211389707
    0x7060818190f020f1c02040f0c0f05030c07050d110d0e01210212012d0305060f040519030320040e0f130b04030309020103110a02060103080306040f0207060c02070e09060601 76
    0x4c00c2d052845201c0000140c00480d00b9008001810301500c04c181182418011215843d069800401c0f40a802050184c81d812049008004000d400030001d9040030141080d20390442e049005c4828007800810090035500c40d58403c490180318681d0b043c501c0c00e100d1807603040d007900d041c0e442003044404189907580c08041d0080001980c3d07020b0280c404d0716a15a2000c500a08950100c1d81313424a0314403c0c000b801d46602c4c50850704152109003800404d00c005500c03600214900709032901503036079060107414280013418130751019401030400010325602d604813200301450f07010500500143d541c441c1c00640315a00c1000e09800a1078000f230000350580d40d440d035200e46002c0342d99000401d82e0b13951045c0f0540482d8200d000c666504c1d0003c05550349485500019400104410710740341d5a0302002e5960b0005110041000000100040241c3c645801910b041c2d48002d60075500da803031600d440800707030002c41802001846001170028961907441003480c001c0c0002005030581e03465400c01107800440704 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 211392185 1250 211390935 211390939
    0x101a090c27040e1504060b1f0c060204150f090803040503070b1e0403060f06050604050906040507020c130203010e0f040c09020304170418200a08040203070807060818190f02 76
    0x1071400301c1034110b014400c1d40710504080c0d10715051440c05203088412102540d01c654040c1d00708d890300c1c10018000d016414041402800e1007100b0307106a02d004006442140c00c2040f501e0a4951408086038100d88240043d66103500c6502002d61074002c141c0e80d0f401a0710505a05a004080400c1000080d0001701000307030742211000040410041840e505030300c15032084984c0d60f500c0c2646070080000d445041d02230402140c509240a15010010b6840c84024005910450b5190007203004903000700280070b480800a0082000100d800326890020340092003021403000c807010024082e480e106410710311903a848006e80b8903083c01c1007402c00080d04002c0040f12001101d00c003110001d203806d8068002042c504c1c0740f0320440214080c41c8400c0e281c40f40110702c40503096040000821840e18150b8440c0c22041c07800c2c607915640c82c00041d140042e03d034400f400344d005920022690503441088140300d030043c008403130358100c0e200741002ea44046a01c0001c4820703500c4040c000002d414010703240141800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 211393435 1250 211392185 211392191
    0x20307021504020a090c0203040810062d0302100c050606090c1b0309030a060204061215170102040504020a0203040806011505030411060702030d02010204061805030703021002101a090c2704 83
    0x12285e80104840880c0310607400743e800828100400c107030030010b205075409042d4052201030300e81160b8181c01c0c0306003c00507140c3c5449441b141c103080c009a07202c00007507400402c5142c41d00c40b03116003c0c003646840c0605803401d01400b8001030700b034104001e40c1c0303000340c20703511400303203012103610742d0200d02519042c803290a40000c011402a6540400148010074055400140e5451810401401545202600b0b0940c0703414240700802100308041d52104468801429607181000341401500a100e5508002e51151010a01004443d400000b62081d210098200d414a907202c071141c00c1e100241441e404001241080010001844505076100008002d04128105460340e40041d060012a000100060b903020a0821503950700c48800b203034404210008010a42c20900030031b44543c61404042d014498402060102c28400c00c001041000e44400411501c40c00d0280d900e015018201d040c0d10412a20001c640b2001c1c21108072503c81e0f5402c8156468441200110300b8228000c0208a030301590b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 211394685 1250 211393435 211393439
    0x507050f16090c0f020c040b040f0513111509130617010507081614030606090901080703020a0e061e0a080a03050d06060302040501080c131d0f0a020307021504020a 72
    0xe0400040d000302808030766081146040c6001001200c40b001514000c01c00e404080404554004c24034460000c826103010911449400101d40903050050340d003206180381004000c00300781d262117030181c1d55100c0e140c960b02c60320441c01040880c000081c24010054400c010031900e174588403002c1142090101e00204015035154032a66102e136a84c10240d4441e515401080701955201c03030244d034400588207001400035000780707004104c100b14180c0c42d12000800000f191841d941c00080d06d0885500405a01c1079603100d141c400d1712041c0600c8124000c011441e000304124804039446442003c0280143c400500d41507403800540c040c030043c0c1074225030001c8001c580060148100304c412406611000c0d076810040115078202c03102c650000040502c140018043d40e079020324115001180511100c3d210b40100701d940f210312800c0c0c2c0c01000e41c00207552540715185840f155491040100807d422032660b18240302c4001d030b11003164000c0043c1c001d0101c4d180c1c203400390103070207400a00240c20100065 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 211395935 1250 211394685 211394713
    0x12090109021c110a0602030a0309080c1c020601050609221b030902090c041203080901020c0d08040317060a09020f0c15010f08010908033111120609070303050705 71
    0x118402d660512040b40e89415209012030300b6000c82c402d03682500ca10313440d45d2602ca0001e44a000d0050785504040d111002d0105100408050b034218280c3c800035510325403240003e07501c501e050035168001600504000048919024094914400c00a441140d06600c082c00140d20109004c00018080b40d40d200c8991718560041102d40081859480000f9035140d00d00411180c4103000b041c0f120103000070070003400b41c44102c2d00d115035102c6c0c1c0760808140c0c540341d26501c6806405616803020540c42104140100941e0144031180241c0c001c1e01d81500b003c140032000d03034880c0380444a00f40c1064114008100e0b000310ba40c001c08040d600003040c1c60612171304070803440c2002d0090002400004400c4010712811030801c50383c1005180c140000c1086174000e55500701d15010003003825040032110680c6481112402c0030460803071151040640f1200341d1450101c8442c94144000d9004019441290754800d83c0060110b00030803230b0f400200318480c550ba8040310070b90b2015000311454051502c00408417 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 211397185 1250 211395935 211395949
    0x703030e010c0b0a02130503010504051005072d0306050d111e06041706010803030702250e090d0809031315050408030409020309010b0a1d1812030a06080a081209010902 74
    0x207000001e8090390b1b98144d8140304018003659000544243d240001340000601c0014041e44905140b501c0850b0540e6041000d81d2240d4101c8044503000100700101e1101c4200c10340d544c050070389540c038204101034540c0c0a2080d910440c1000178950704018400104e41e01d8040c00440c581d00ca0b850b80074181c08001d4002c034805402c00e13400300c014044400b02c0003d9018080c00180d000d404110003c608514100c10b0013581c40e42c003101280705603d6041c0345001c5034840f00c286280600105003540d06542001000180d441007c110038000003200800031500c0b0410100032260841940e14101c0a40b2741005551400c1d640641002c2c0103000c0704100006c5d00d040d050000d48003d01c4c40d1000180c903032400303841d2107003500e00929070280318040381c1200784072881d11004101d0582d04000180c1e802540d8014901c104c5107c148601001441071000314415025820005c3d07104500d404420f0001d42e0740c031100c0700e6481c40d0089000b828040305001e20424821000101c59121100c4c800208814191b134001c01c05c1e07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 211398435 1250 211397185 211397191
    0x121b070f02041407090b030403020a17070b1012080f04090608030d0f0204120b0a0908031302010e10080115090306090b040218010b030c0d0906151e06020703030e010c0b 74
    0x1a0040040350038056150030701c101ca0000d00d44940d410824602448000e003081c8540c02480c00e070540200c0442c0a06108209000c3d5056102101ca0344280301454580c0c00ea4101d503e088039161151800141d04643c11460441100c0c406c01100004040c2951800c50b985c12020100c501d4000c14000019840542c1c000c40b0028410680590754901100303220100351032103040e0ba031b9031080c010801000402d038460410050a0b0700185007034496181c203100c920280003040340103440150040f0500c510043c2d10102d00311020b00c01d0704ca82980c41115001e10904050000710000498085801000500e100c1c10400d000390b0520315001d10915100d9599a00b11740c280801514000000e00070042181030002600b06190940884001598500820180b141c44000e2a10f894004041000c00326020b164001100042e40a90141b150741c0302c1d248a00b4082d2030758400d0410400e046000f8014140400101c5420f03100c0c03c1d40a411244c4c19510259082d220015031507040044100303904c00811a407500b4140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 211399685 1250 211398435 211398443
    0x3030f1b0b0a140c0301080a030e030109020a0f1409090706031515020705090901090209010b0a171306180f0f170a020a2901031106130303050903100504020105121b07 73
    0x111030382440c0e44403c1d075550007030101140e828204014848501d0004101c012181d05151201d441c03647d080209014200c2c00038001e40101c2900ca011440700c90064402c4292a019044da211213200c01c420040320000c1643c4d05040d82c1c0200200f40001842a00414594a0030440d4202119a10f650341c0e44040c82c400d40da900181c0240106001e03d01c0c08802054000014800030f1001442030f800041d00c000c0188a0300030140d40000b80c0c014a280030380002414504185004a21403400e00c01c2d20851240504044030101c1c41d0811140015442e42080e0480c03640140802440b00c1c030381d41d0344400c000e00d0140c00395a11005003000c240700d2401d080050280c6003243c0c0c0900114861450501c0200c0c1408030007940e05c501d05605080d1010410b00f803103045a402c055501415200d1f0004034046201e0a03500303120a280400d0048207143d00171009054000382035003120b420741a9044084212101500c2c002d0006800b040400002e22140081d507401040c840c0c00d09004510100d0504039640c09003404031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 211400935 1250 211399685 211399691
    0xd08070804120305040905010b03240a05060f07020306011d0c0a0509040c030b0a0b0a022d070b03040b0105060a1b050c0909101b0c0212010e0709090b1003030f1b0b0a 73
    0x480311075051f01074103006080f95403109003541850030406207428480c503860312507010300c2411144582d0302c0394020130040102600d42944c912041000e03c007140d02c03005080e8028401c8100014010718801207501c3d41c0f400140c407180030358650b540810039980c8040c03c1001004014007160015699034071034203c1260700c5480c00207000008209014208442d070340001c2464a0911100f60055002b107006901c03461800c040400d0b6644039101e484408200402c1900307640700e41540406c1b000c0d03082005500440c065406a4079603a031b20002c001c00351007901d03500c3c0001000c40000e518400d0494000120321449401901c0c4250b0308000403602030203040740c0d616860303400501c8000740c2e220306100e8a400005419444407980039406406030446c0d80a00d00240104815144510000c1e020342c855410b40030068181e925081e9a44600b0010b80408401540c0150718000407681c00d0351118101e800700d0703504d61140158030b600c51405981405091880c0007503002c10399010400240103040151040890482c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 211402185 1250 211400935 211400939
    0x4050109020a08061815120703030f1103040b0a03180b07031b08100b070f1a010302010e01050a090506091201060b180a12080703090b16110a050d0807080412030504 72
    0x20609070b00a88074034040d078104610035180300340f55103d0603402080320380d5a001100f000c10200b4410281e41000301c0c0302340079082c80441010b61014031041000c18a5507000110070321a592203403684650300c030f206092070040000c000e040f4000c0d040402c1910040c1c140310548100c0b511480002d4004070b5034100044d50713411250003820080c0781d60800c0d0002c0740c9410ac4c17144c0350204412048100c01d024000700440d02084000c100410060987d911580c062008144004044113911041d2028001280840c0f15194200d059511030400e84103c3c03122941d44620481c03a107070610040b2361244400f56040b00a030710300310074032180034052180181040b01d84c5a68500c401c14200550344440082644a610303116810080200601100c0f24259000f400040d65003025103030594040701c890740800016000400e000305150f580c0306001141c0b81c0140381c00d081c06051181007108105050083c660300c1008084c0e00c00c0400c0c00c04c40503141c1603110b8081140303483e0301d40c4c0380160700c006d21b0101180001c40010782 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 211403435 1250 211402185 211402187
    0x9061202210a1a0306130f080a0809121206010309060204090e0307020a0f05010507080a02010b09010e040506071404060c1104060b040f05031f02130b0d06061b030c02011b0204050109020a 82
    0xf5002968810808078282d4840010000380c172402c2c040e04503200ca041c400000303028441085030600b507066001c0c510540d5801e002e04e020300000b100f107034032059038000c0851600c800c0512404588400615100e80c00b5240c0c0c1e148015802070400c04002d5034503d0b0f0a003c00f0507902968819002c1c0c0c1040c1c00010f6807182c499104029202c9019045100c50b04219401081581d80140c00d48816a03407150606850340c00c3c202d0308030f0040c03218401050b4401c00c1403000103181c0301980740a80c0154000c0301640c07002d5407020401c0d506801040e01c0c15511400810003081510701c01c4258011080c0701c2d0022901d13481d81140010103a03212a0400a03a8460006c0d08100810821645000518007074020b003204840007465040d03442c2c3c00d4200380c3e40a940000740075008a941d58400d00150212030030594483d4080c2c50a2001066180101000f20b05e00303541502904584052541101e54940e03170b40b50038803001d40d00454104d2403031020711140b10300c0c4051002c0140d48a0007100d010f888009001a1030301d180c5c03a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 211404685 1250 211403435 211403441
    0xc050c031b03060c0702010c0b071403010303030204170607020c100c0b09011d0109080f07211808010605060405010309081926060d020402030903040e090c040605060a09061202210a 79
    0x100081c41000100100c1780140d030031245140b5001d0300b041c0750828a68a840c801e03106c401d0805905061014000000b1003010b4041c3d019200380c5007240c0d801d007490103000200581e992380940d90840580c0c480c08000c101032526801d4402c1c02107140c0381c030307889030101a40c0303144d22000300b6508107609035100c0100e90500c081651510400200190083c40003c4103500d54410a06c10028102e40030b110000f804424400d002141c000303c42e4801003d0754030b041c1d80c403d0040005640d45c2c00e8401d4810510400124042e0500580701960b070001e0415291501e00700c010740c0146110581202ca84400f4040c2220302444101d40b03482c804400c0c0c81d98101143c91194801080c5803400310064520400d01c2803161070b840360449044c849905650050ba262100d44859145009581c8211481d844160030000c00301e030046042e98140d1010303281031159545503403c103c0d01c5c0c0291281c84001844404040103814803802c22100143c814110040c0b404c0c1c591004494528100a2200b641d003040b8400c1c0015005c1501c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 211405935 1250 211404685 211404691
    0x609030e060a080a0506150a02150105220207020102010603050718110a0c020d030527031203011a090f0612100603062904091407020f010c09060c050c031b0306 70
    0x224090b1905005200240500c1005404c1010003a41e40c000903903192103c1600c502d604000044071511108100b41c000c4d65410706104070071485440e00000110350030000b150402c1c1c03665198803070fa14007201750039000080d0000c0c1010f0341151f49611000000c20024040300d00500001c0b07140585000c02202d030801940d0000a50f940c60300020006a011039030300c46000702c4969030403646a0ba691405080407501802407544c0034545140c44400c40d519201551181307082e400c0b0560940d00d82440e48280100d01d40424815040e103005072001084c1c0210440e03008095010008042c4800010810003060441d04140c80c1c0c1f1448080b000103100c0c444864030742c007000501003840c09004044c04d00900e481130f0240214415201540c149000c4000001342d0103a41c003034210b168080102c001601074011007110306661480140c003907403640400310941800b030140c003048181c480142c407501d0014212901c00100c8815101405034101101c070f550b605001c4a410b451440031038131a011101070825046c4100a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 211407185 1250 211405935 211405939
    0x110904120e090103170705150c0703200d0c060917070204140405030901050a0201060503240906060607080a02010e160611060f04111207150e0f0d02090a0e01090609030e 74
    0x30b8001040080c10f8421061030000304070065584408140c507005203821006a0381c0c80f03007a5104006c101c000d80c41030b00900744203030080c0d40782040c05420b510320030544400c12001c5100790304981e44410805000301c00024801d031145800003651808e540382d11640a08071607628403d282e0004001c401c0d403030076000780c8441e41501c5c44041c2e414202039640b5075803482800800c5050103004109012098000e52212008000c0541502c80d0360303291800114203060402c480006030800344000c201d00020005049203d601e015103890710b0000c0c03540ba203015035088005220119902c4507254111800c0078858001040d0002440004040c04e22401821002181c0d4107200b10350301c024104800d008403514016003040d000100000150000800701e5040400041010440d00c1707200c000040a4040c042ea6955115282ea01c0b462849920000c01940c602c20190b1f895100c401300d08500058a40f07400d215404c5051000005036405811a10300c1c29103c00040540d181d0780d03152081414182c1048441d0300f00d10b41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 211408435 1250 211407185 211407199
    0xd17060405100b03011d0a2306030304090617011b09120f150b03010c05090d0209040c030f03050a020c010c050307150204170109050f0c31050412031506020309010309110904120e 78
    0x40701140c0c0c88d041901d207290688004280404e8854034244100d03405070900010502202d034449058080c04141c0c80d4445045600e407120f0f00d0525210140c4103e80c5800315560386500c64684502e0656010b00c01c142a102d840d0042030060004d450030851078202ca0801c0408110241240105070071901c01038100001c0c44070400c6251000d944510318410031650443d81003510303440d40d040c0b40c426012245c0004014161124a110074103401c1800342c802c0d0f155aa0848010742011001140c40040200e40104164824886c50000440412101088030a0f03c6001030800e40e440f001602145901203440341d059550741380c0710060003018044400c1d00656a0f005040782259980403c100c0601d140c40c600c100c1407200106080726040c00e1095015130500001401142402e04100300d184810071710741c402082c40c01000450b000c80b0074111504482c030030b0b00034608065100c0e0043d4013510901c00115071104054403401401d5403400741a038000c83c06011a000800c804c500c4c090a14440101a03d02c01c0e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 211409685 1250 211408435 211408451
    0x6060b04140402030c1303080d1b140a030f0c0905030606310b150a1704150e0c0315042603010311190303080601020d17060405100b03011d0a 62
    0x1e11025031120741c05480c0141d03269038080c0022542d0003100603000c8110b4211070000301740214070028140521107400108144101e00c0e03122080702a0704074103200803524002820a201103c0c001030326aa42aa0074041840d12050240904a80b40c045103c808034620210a0129043c204a06644081d095030000c8402c01241030700001c04586e0250100d0031301c05100c541c600c070145900001035002c4040d160309400c1614604a481a0708008040000a5219020354004041851140e801640c020101c50820070440c0f58030000781c50811040c0c2c1040c80388942401c7c464408002c090213030b000c190700004007401c00e07103000d945103040f00c20003500701d4072041d030a4400c1d4181c1c2000c4a045941c001601030a00090b04045010300c00c032a644003039144a0f04800005042d00144840d01c148c40c00d80c01da409084c0032050542d072075010103003208017041c00340c030010310306081c03507480035070021000801c40d80e03556a10458001542d000340c11028800c10154418800c28217040c00c0d80d60050780462003800703041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 211410935 1250 211409685 211409699
    0x17010c020111071b03062901020102160809030718060905010806010308091c0602070f051e0618030c030307030c03050105101209140a140d050c191a0f0406060b04 71
    0x8003c1820140020040c00d00030031180600001000007140c2c014814052100c900d1003482c110309a189421a081c1c1011401c44090b620600c211920050110303400018149a0b480c0c035a6160800d1698907090320480c4000300e80340b0240415540321041c0540d0204d5001c0c2801036800035540c2c1a4040380031540400d00500009441c1c00607600c1003038042e94241c0214014003140c0c003c07128400b41c06001c0b02e10014030a818040078128a5528a0054080318081110005040c0c1c082143c80c1060500790026008201c41030040c0000c01500784031300c1c00300c90600708007620a50039640148c4005003ca591801040b04040e01405494014002120124140c254251003d065001e03110100a021596808000c0030000c00d07500d00004414a00200e07000c0e2129480d249081c01055250900148203041340c01c10401d02c50401c94000760b250201804c5c1c141d4100200344c1d04040c02c40002c507000207620b070b00280160711100c0103510030081c55032243e10604050400030b003207640316040450150800c01040c03043c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 211412185 1250 211410935 211410937
    0xb010c0302030d0e1f14070801050607081b0d0c0512090d06050604150b04050109120f020108040f0f0b07080702010624050702090103050105271519050117010c020111 73
    0x12018000004c40c80310b482d11201400d1404403c041c84d04204004031800702218940d0086401d000d001210011944a18105448581c403d200c0c003a8403070fa00300b080030f001911802c080c0c0300e0406e0205038148114010b624403070030054884620300000d0078234076403030080c460104038804085651075651464240315002150003600707054806050143c44001213103c41d122540100b1541020141c84035445031100c0e10414603030700c80d11030b080c0010520100800c8848406c00d1f07403110780b0391090b840b50161560b81d00645e19102d0081090b00d00c49038840690b00032609280e01012640d100d01010f14462400440c06001601c0c041c0c0030b4806c5a00d0424240400c0390b04101e610200003a6052000c5045104a0f088406100e4580001c3d040b103e00e8000104125054000a0103086194414110703954a06540c4110820003000707210140e20a00c55000c05030004c6880325003201021051040070031115400006444085c0d00450304100c03190101c0a10400a101d000300b451540e100030b010041c00380310038040c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 211413435 1250 211412185 211412197
    0x260601021209032b0306090e0a021005120c09040501060e180c0d0f05180d08010501050f0d020c0601090c1107211202030904110304030f0c050309120a05010b010c030203 74
    0x100400510b50304107660402c00042140700b2090402c480050302c0c10010b90b140143c405840100c1c1c20802d020484030070138040d105900300900001c2806c41c20940801440c0500b8011407030901c202001442e28011040c088107100384144246203580310f0b80d0000b8841241c07c140d00c40801c114a0100c0c107029640c403201c00c00d0030320071000800300c0c95440b400c13919039462091100008055103001a84820300c07030250040c621030205240003418918040100f65140e01c1c0c3e0007829400240d001c4014041c0350b000703c0284c40101d45025a01d81085101c09020b41242d01c00c444490080d44094010000415507001c0d40000e23580514044180552103802c5959031080c0f405100c100d02503d49042010303c6891800c0b0821903000200003001c5c000850000e522580040406030140d410880b176070389082d0f407190880e80107513816650042034007104c3c1300480312003072012805c03100ca010070044542c951b5190395045848115480141c0000c2482c0c0c82c001d402c40d40d10603842c46c18800048402d401207600401a074103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 211414685 1250 211413435 211413463
    0x603061505040b160606050409050c15090d120e220b0f031207140106151b11040b13020a030b01120e0a0b040303090501090c08150603030d090507030b010626060102 72
    0x8010703409842d209005d031035187c0005030458501035004041c40800504149500c0e001c0c1d44140d0400c881810320300441c07091560440e08000344c4d940f51400100b0601b00040341140070f01d0005584500080010488680207910550201e21051792205804080c85140840802100c548004120142c00300341c480742d6800c00b18a50382c401240ca002441480c11a4007044100d800c000c10030b0a481d2914181181d03a50620000010480d680200101c841610b00540c055040f0100321120300c04002040050b04018a03180d41040e40c0340f4849101181d1070010704500303105503e0200d821403903840014060003c1d4200450600d0a1404034001290089030f180107070341c3c114a01c2d412a40d10740c241500039094142c002410356203407640000a00a5642c100c600340d8442c01300fa01c201310000e0300c142100c0310040d40d005525400400800350804074503400361702154416020303a085155243c0340c2098001c400d9000c5c40111304d002d12070150001200a81c5000c42e802680490254108100000e54a48070b11450724 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 211415935 1250 211414685 211414717
    0x4030e090103080d05072f0c0a0305070602100b0306060f1c030f0e180a09080705060408180105070c17072d0b040e01030f0f060e0c030d0c0b0c0d0b0a0603061505040b 73
    0x8108440144138075060323208090000c84820369280350a950740c070039a00c80d56006009031040d00001d50450300404916040c020020a5603407203207070801c8401d10244424590101030039444100100003074245860f001e0003a04d80003980d00030314001900612580181c18414201445070160f014124954a81c001c3e95010b000109200c40e0b1038242014030501c203015241e440740700200420400c0420040c080030802c00c08600d4030307480c114015650340c000c030034000304801e01101082c401c14080582451000c40844102e690050365440104003000e840459134150001d07004180c3d10070494080b90304001c1625070303034803031400785400903d4540c6d21041c0001452089040c00321000e011000521100d0182c02002c208103030702c0354969043d90383c0107240051b80a406440398000a4034000d5524220158100e80302041c0d580d01d0f8081904d055000c201081481a520030002005480306414a4003400d003e0b180003a240782080030342180482014061002c2003010001071241203040d105403111150185092 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 211417185 1250 211415935 211416017
    0xe090304080a0606050f0d0210110c0a03110f060f04140f1216080d0c03030f24030510020301060909020702010c0213020405090c0406021504030e090103080d0507 71
    0x1141188201d0303100219600c261100401402050b5000900300d45c82201c686034040b24640c140036000c080300c0c40181d402601095682c2d0114081d8001c82030b410643c00940701c8d4195a0000990003a684e0782041d40d606800c01c9445205080180102d003c0d5038003150b405007021038045181c00144568012405070300b0950011600540305d840b240d241c102e00c001c11f40c0c0c14144030b845030340b40c0d1942c4541d210b140180c00c4150004184d41e010541c40251132196070390360030032002c0752829800307003140600800e4120f964418a240c44000c01070855184003024640190552440c2403151428003070040c210241481000104003c6400c00100c01c01c40d500c0030009a1680008d00060717403d99602d040180d0000d17114a0541e8652007198024025207c00f01c070301982c43d4455403500c1700640581d00035400503901c5601c4103c0003003a000d02a80d402840791900c0403c601540d030101d8000e003000ea1045400d00004035004030b440394140902a4440b11602e400081c032440300380e418030380e103a00d20000c09500d0000004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 211418435 1250 211417185 211417201
    0xc0c010f181704120b1501031a040207030c05070b0316050306010e1314010b1317030a05070510020c010906051e071202120408040e0108070b07021917010b01030501080708070e 77
    0x2581c0007032845000760055010079052040308485c04403071540d04078014100209096009202d1204203c88004a000c040c407029410321000794400d0a0035001e10140c0321100000a8081100401400c0300f00070050302e0f801c1c03403405401c80e2141030b41100180a024000c2041c0341c0d03072001050300e109800305d03000c00368520360804083c010003c04008240550404001051088550008084045180744881c081980d01e0080c0e07106884441c1c640811a0410001228aa80301d1002340c90081d0185080e101a140c150901808030784c030088485d04140d45030120307802442060302c28503a0004640c072242c907008076006114540b940c0010800410302a080607019140129a815601e0301c42c00244054813500301030070300c1d0015402520585601108400012032402c0011414400711007e000072681080700660070858144c002240c403540c02c42c694000054030840c0f01401e4943c682210000140172811403000605070345058100360510741c40510108031464001407450304582510308400c1a17900c0b0084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 211419685 1250 211418435 211418437
    0x1050c19020607050f070608070302040b04050904021f0305040c12150f020c12040e07090b0f0d110a0e040b040b030c01030203040c0e04210c030f0c03090e0c0c010f1817 74
    0x18020342288a098203043c00f042000946c02c09aa840307031101d41e41c55484440440981c45140240e0070217145c2440200500e062600035240c002d40700919030300504080340780c034101101d07160745400c1c002034a602c00e01050100800200c8040e02d2400c0e41b044084840f500c0f40604d2540040710703207011585d607180b00c4000b80402d5040e1842c0c486030030140e0f45c0100c1400541401500b0a0140402c10b46000e17011580082c042d001f0101107810300c200c02810104418a61101904280e449802c0715454100c1c008140e2502402844101c1c4035407102140c0a030f00c0000c1c40704403620902d1303a900035403130030f100000e456070001040840702c4005d02c1e0140e62640c0d02c0ca041010101242c0c001800002420140010415540082c040c11100f40c00c00d1380d440c481d210802c075140041607201401068500140081d40c500c034004440ea031034001d0400203989507645c1520307e50404200c032040c3c50000d022448141ca25402e0244800c2c100f003103d0301b1703c80c14640c0c0109142d00101c010000f802102021228510105400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 211420935 1250 211419685 211419697
    0x80a0c1e05060406020c01020609010e0718061d0a0b03060411061b06040303050916050d020108041b03050102090109050a0e0a180b0c030411031f050702010905030f0a020c01050c190206 81
    0x14203032649444c1e81c1c26029580d1074803000024050700034440014000781052090108400b17a035070090195600d0300d45d04122101e2490260200135450b5440410ba100703211680c013422038000904540f003071a004c22040100c1d0b007800c202170300c07030340240c4203010100d04010307640250610100e444550300c45c0704040d0480310300f002d80b0081206001346802c1209043e0140d00003442209030380180e0301d16040240c4801001011401060f511006505465015500c02d180c0c0603030241c410010766001190940341500780d401d00f903100300d426031b400081c0c1252a5910115507001050b0540e00c0032041820550090041200100b2601520355901f100780c4180888a80707904002ea080035400c07140741803032021840300d9807085a0640c1e116203200414541400c2c00904a40350081248460b1044122916900003a01b030280c4124115900c0305d89403c007050040c40200916814401d0b2246d5441c2003500203424401d103001168140a01400100701c512004200c94000b0400c0c8a43e40f60b01070743c180b000032024041c00e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 211422185 1250 211420935 211420939
    0x110109060e0d090515040e06040207020405040b090706020d05030a0207030318030e03010605120319030608070e100602030903031921021e0307230904020703090f080a0c1e05 76
    0x7409804030760010407400c00420465460b206210744880500070b130140b40038006441400d00300b00c10407038210350340362903500400000d001511b00402a000941075600c203441c15601082440300340401ca031803c00801c4018800e80c0007400a44203c400050013501004004507503ca400290300e10802d0300c41d601138516128a08040c40d4803401c0d504004007001c01094900f4001e40c60020041080c2c6040c5c800c1141c241c00081c0210b19181d00359040b0b070742c030410f00c0282401f41600c8040100b0702c00e1080c88440d01411503a01c40c007035603140c007419080d0088031540c00102503400401c14184151004001c480f00b041d0105189030b508445070318100d07100e00c00a03402d80804184111000340368201e80c1c00901e0412203103c1d25903034210380314840c030416100540344a00405d0355000d8400440c1c204281b0385942200d0b00342e2403400c00302d2500200d401d99020305001c80008510b00814085103017080c4210703014048902c010501d81031960b403843c11030921030080103250190309400341d144021882802c0058440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 211423435 1250 211422185 211422191
    0x10e0f030301060f080f04061d07080309010314100608092a011101060501051c11031509070903050703031b020a0803090a090207050a0314070804060906141911010906 73
    0x180144454580d0028003400380010002030603c41e110388103120b51030103105408a1b070245602d0360756908004040300b00741c0ca05022414503000b8090181800600d0040c40807602942da211041c030001801c80d60000364030706000242d042442084d60b08180c00101362003481c100110135480c0d03400c04524000e0307444a485a2000301c0203801951510058201041c2c640a8035003280ea0a101c1900d18281c070040d02071030340000d4060021001800c08a18032040024140c040024a0707001099804004e6004564074401c20002480e854103909101c1d50380d0b80d01c0004e5190803000345086940d1103446580500c405420004032900106000c013401441514881d401400c450400f0b80d52101141c41c2d401031b58660380705200c0c00d440060f000807903001b1104c81030b0303000002c0c1001c1041642c0c02d0358003081da100480242202400341c0300c0003400c54401000a046581c40301c00d505460300f03900924504501c00c21042002044c08030070f41070000d1425100b043e1509040c00011018500c0c49d040c010941c1c020040c3c05035003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 211424685 1250 211423435 211423453
    0xf1911010e0709050106030516030b04020403050303040c0509070504120807110d0516090207030905040203070c020d060b0924040b0f2d01172a040303021e012903010e 73
    0x7000903041045034031074441403215a9964506508a0703a00711081440a034074807025800041c400d134411048080000c100600303040d12a11114519001120700f1105014044005d100c00d24120f410f50368000101d1414034075050a150010040303460a410040c8001c00c085911800c0203c206459042020b000d060500c094010b030070116690031403000c1e9080d807590384040c0070400601c00d00072154559016115824014034080a12009500082246080103680c03805140180c4e1681203400c1c0c01c078007450000c40c418500c0001c00000c4140a8105205031030808140c50f0075640700054440c10760021a80000c070751290710085902e401c44110310b1907001c0c0889080310158840e03140d400602c245d0038a49005000007103001903d412110714105c0d0404146400004d25a141e0055000c0ea1903104903060a007484480000c07603181d81080d041100035070042c8000c80d6051588076a5000f00c60400b80003408801540c0b6200110042c4640300148441c1c00702c51500d1031a1025040008002e03440011210505 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 211425935 1250 211424685 211424711
    0xb0a02060a0c0801060e1210090f030201050606090a0506090d0602030709080c0a03022b0503071a1e06010302090301020906030109060e01060908100c0c050708030d110f191101 77
    0x104680c01c0d0021441c003081d4580091040141d507050b41d00396200d03955480e18003001c00603682600d0481c05218820103a0003460841c05010310b60249100f414071400c40059450041e0950700018440342c0030300d4081c800e0402c559601c2468504580c401c0c0c644a0340d030024100410501d000703011026041034000803c1c0a005a40001c3c818212440c1009075041503c1000c1040011b00031440040c0d8050b19070004007113088a200d01c00402c4d42e1180709800030b00381c082d55a00703055411801098484d0301c1a01c03c5038911010103250b16501c5010020107042c0301e0050a8003445008001c2e01060400d40d005c56400f039541c609504484c20102c00512541c2c4a41c0c0d10501c18001d002c05018080b504200b150001030310238002c0000c14160794000d409084561101c01c0c40300000e14411301c410f420401a04800c001003103007409150050706071040955590040c05010788240d40000c61483c030344c003c0421450b0305507990300090758260010100d81003560149400200e484907030984480c10799500c0c24945425403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 211427185 1250 211425935 211425943
    0xa0201110102190918180b061f0224190c050715052502030909060d0204020a081503072304060807080109030206060103050609130203100f090c0e0c071b0b0a02 70
    0x42d00c9401180c80e0885401705c00f442511401c40f0320000701961070310b04800140e41c000d845648040701034480d43c05030003115030b03c2d807104803c94600c80158018402c40c901c010b850447c41d107281040350030040301500705014a500c0c14000440800c09480d40d428001c0003c5214004403100e0b00e8000300d0b00d0030240c00c42807015005000a03101c402120300124811210780b00601d40108a07402ea0b07070050f6040010f404188944c610009080c02e9010002498140069440d03201030800340740b080d60360866a1401c098418040542d0648088c03207640407440401c03044002c003150700951070080300c1c3c3ca40c2d0100050041005082940c01c240618054102c01203414a4154050350402c0d009078200e51003030302c03a88019011a54181c4501c3c0e000380c031440000303110403440000e43c072110b84054100c41c0303034894003109507088410591101d0251515210401e080c0410445c046d4081c082d03d601000c0103041001c10b40e4074920404500604d41c1d41440e0b1800610011070703640800a2121000392981d540d0205030007511 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 211428435 1250 211427185 211427189
    0x3020d06090e0f06010f0311220c140f04140604080715030c05090904030c1b062001020a02030a08090102130b04061707050a030e030910020c010906020d020a02011101021909 76
    0x680b050031411043d90b040014072034104c840d110004075105095844010910060b06e40d03140c1c010410600c1005080500090f088403444586000203900e0744074840181100c20300480348a40c14003e00019844c0e0440d20122405c80c1c10b0080015030802c510b4002c01c501e80a151301003582d6001d440400662542071031510034001840766010040d10100e0b800c1170b00ca6024202039140c00024000c0000c00103406076500d2103a01c1c0c02605020307201d40d4143d00200f9605480d03081180010742400803482c02d40c102020054019225000a6051042d410002075803402600c10b04010000c0140104901603001c1d8125001c5c402103491038100c1c01c2d02d505030f03159968094401c010024800d07034000c19030b6540300d21000f4040c907030b82d41d140c0c0d14210b0f40701e8048000d86015681e06110b400108070114456482c2c22240088040030b401a0000702a4070300017400c009880d9004105540080c1d844031041c90b4081030200c1400d074242400c1c0c0a8000405250f4024000d145031245680c03183d45200040c0d503007180000d02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 211429685 1250 211428435 211428461
    0x2190b1b031009020a0309200102010f020c0303060d021c0803060922020f0a05040207060504060b0d050d08041401020318010b0a0302031002070203010e03030a1e0e0c040c03020d0609 80
    0x501094036111940d42880126450a50b20000301010320052141c1c3d001011440040d02d00451800a00d44440c0c9008440901050144240c81c10540d00b6580a0041a40c119000700c011410565280b8559859100050040d403050000c403008808640e100e1230140e500e048540700142442000380740c03100d5941e1054a42500c50108680043d60744000702c10040582c1485515a00d08100f980e800d100148004828841e8850080c5002140c0c903207540c805000541e00510001c0751604103401c0010072502c4403030005000300c5800c2880c1000c204001039207842541140b034045100c1e079035818450180101040221101d50001041c8403110012000d5440d00001480c0200b050b45c0d405810000000790f0752000a40640245009a0728807030198040c01000c2d00113400414000ca0364010b0a0850303200300c0380002510f6403044100c51111440b04a02c010a0743c1c0d182c00c00c8002c400c600d0040e27649480522851280b0b40300c680c000c0c51680301b034040e20020101c101c803c0c000b0b182c0b101c0340900a0300040a03105 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 211430935 1250 211429685 211429711
    0xc2304091802030a060c1b03020106030b01050405040c0e150409030e0310020c0705150d05010303080708090105010303090b0c070e0108071e120215130603020417010507050307030c02190b 82
    0x100c62025070307084910303840390b004000f00113a10056032040f0107030a421a01009004c403100901c001c1240c0c110030590300c28030070350001540e5800c62030051b100c4481a08410b000d41d20b403030b04000c00a80700c070007604140c0d4840402056190ba88000380c0002408c0358112580041c100f050034020507401c121000c1c1240e104605580c102c41034500d0403800c0b0301608032104042e80c489142000030781890403a40700e80c00586d4450b0b919140a00502005a1340203900460009020304104104d4603448143c407600052824003d00507541b4689004260b00c445010320001001c00042c40031203075408000c20b01c000c0984a4103040150fa48551658441041c0d12418010390000204a0000c1551130300c0c1005603010810380e600c0016040d024040300345042c600c3c01c1c881e0a0204081840e0b50302203c04880185000c1e03401580c1c450030091582c5c0c44c0d1900c0310004404bc0c0c100303c180722401e500942600e6102116183c0040c0000c880c010491a005484041c1d540d0082c54540010500c480c4403801485680722001c40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 211432185 1250 211430935 211430951
    0x40603110906042702180f16031404020913021e010f1e4b08100303030e03070b01081501060f022119091403010204050a090c230409 58
    0x800141c0310040c0c1d0f0321280300750419504c5445144c1080725a0898000703001d00144601e000303a21a1100400d84030115161078580c01c11944010b4820103c14003019850b040c03202d42010000b0400c00c4401820003417040b19880c00203403d00951948001c521900105512a40200c091050200c02d12074603410b80006c00704601507035458001c02c100c100d40700d05500f503125140d8420070200c90882c40030003c120140c000e003512040341b6102c0402c11440e507160300d01c2d20212500110303c101e01c810224286d00103004080f010030860001d070801d000d007200c0d0507023004988039035202e03509415841503503002000d0402d100c2c0003003150b942c001001160b86100c50201c2ca442d0340c031450140c2d829000d807034007400142d0040d0300b620110383d80100d24242d01448440344d60304000b44510b4803000704516280000003ea4405c1081207014803001c1034654421041e0021890b140c100303130128610b8003842c02a40742c1c1d107850300358082030544180c8085002c401c0d002d01c07956201c00000100a03082d03109124025000341044c1c2c41d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 211433435 1250 211432185 211432189
    0xa060e030a020f060c0d17060405010e1503011e051f0e0408130302090103030206040c0f14041104050904030503090708031207230316090b0304050327040603110906 72
    0x1540011400050081201c240241c0c01c000c903812004105a8020f441400107038074081c0c00b04202c034200b0189440341582480c0c180c1140814260003072440b4401c90070400100004d158403290b03d50444801d07020207808280c954003003405412002c500480721060b041e5840c1d0504103a50009008841110b5404041184003585142400e0b80b4042ea1500103100740c0410009a007000042500d41d0300d000b07001d01040d950303400117081140c00340d0050b405030304003d08101c1000038425940d0b020b010500b00352840030b410200300c00c4401030b59482079030045a4030031041c1e9840b8080c4007680c00401c001801a0346a240a00d03005203d60819920960a40308240003c944a1400b205883d02100d240258501c656249017003242c0b44c4440082c0442152204880b60403851900002113205991b103201d003840441c0c5090b001414084503a000750002c000a0050100192000c0201e604c3d035243e524003682091546500043e0004800c8100d9501500d8103034000208105998540198041121b40034159964181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 211434685 1250 211433435 211433447
    0x9010b0a0f210f0b06030a0215092103040b030a1407200604050c102c0315060904030309140f0f0c011403010303030c1b05010605131404080c010609020708031b071505060409200a06 79
    0x804541c850b00180004d000342074ec100c02456100f25406408641c141e100400060424810398130b00c070006030712a403d01410501b03080b050034940072000041406140a40300d5a40f41c00c882c403540c9124030901403d5401c0c440c481d5800024a030701102008001d03030560b1400003a6001445c0403e4003900900c100c0b00a000580e4090500c1000e003d822203141b9a265074086000707190743d51045452114001207505030a40030024070b224804010300502d48140c13581d030000c3c40c103000562428100708800800250300f031580c100b900d04481d03041c02e002c039151603200381c00d4a80c80700f01c0c0c0c3d510507800001c0d08400240714054001c001141c41c2a502c0c61780758a003440c0c12000351000843d030a42410021030110b400605440020a420004080001031864440c500e00b4180d0740003d006803040140441400301003070305c0880245007505202445ca00e0102d4541d0340100810700c0c030788a0030400c0d07034130380005040751143c0d0800a00340d98044407020034040014401801c10f118a81d856009800810010504600a007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 211435935 1250 211434685 211434739
    0xe06070206011505300f04140d120f32011406071212020f04050a121502033d0806010506040e09010b0a0f210f0b06030a021509 56
    0x80e031450314007103017025002c404848041070900386208001d001d241d42c00c0025003641c007800d203001d5010920304280c1015580361400030094a4160800b034210311040750418040d620a0140030404140751f51001c1c02c480061012481c1148014000880000f480d130100c4991a1005070810120403180d0326041c20201001415800c036400070300c00c000303410110744101010420710542e07141845090407480d074800103170380011500403903c11000c00d00703200b640b804103c0c090182c0203411010300c0540140c2c43d1a142c00100541a4640650020104540304000c0d0f00d100c02c500742c00e0040c880d0304038900d152a00360010500044600101c04030000c5a52100819041d040b90310041c07000703080c01c8c100540000512405070040b1003a640c1d4501d51002e0781c81d000035640080004045102046250610b81c98a054514000619540c4211803002c0010702451103001d10301d0f0041c100c080140e80d0440401d10b40901072601a51100d04800000002c560910050064007415201850f01030000c01d1034903031480e8a6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 211437185 1250 211435935 211435937
    0x70807050d1d1806190909051b010206010b07050f060403120f0c0f03021b072c06090f0a3b0307020904120504090e070f1d1909060e060702060115 64
    0x103e050803030100580390843c0d0848401000508840d81640c040754502e286070744035503203c1d6152100a07050010078000342d5210003000040c100b000d031071100003d4944005000384444104086030301d005200080240350302c016003040c11900c250802c2e040141041c0f14003490384a03c6400c0481410300c1c1482030082e181e844103240c4444444c426683c009402a41100840c40401c0601b60118040c1c090300f008004001d02100d184000c002204c000040304080050525078880401041801400d44547c1840c680c031030003110840d8415141c1070f40003005007000705601c8000c41c50821186d140303070b0803e80d00c4544024001000031900300200034000d032203010701c2402941c003041d454002000b0403109180c900d45050a0700d000380c60300340c80b0380149040ba070b6003c20700c0032a40c1c0201c205100004440b8103940107884401c21205035024651064419220300030001191200710b950341c2000580280c006001440d4490f1081c40b900980300b0440f540e40008445500062040000000d00d40800666040e252207607 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 211438435 1250 211437185 211437199
    0x60e090a0215251202060702160909080c0d030e060601020c010206040609020409080f0403110402040b19090902070b04110409150903021627020f0706090602070807050d1d 75
    0x501e482c400b199045031003000a402002110342e4000c004440d160b00000784115008450305400c0c05009250513001803d541c10741d03121000800c0300e07103601034114046891024010664044929180300b080c061070104003010f100d403800c800308680e0180c000c403900300403503001c882550ba2041d004903035401b203d0007014090f130070a030f0201d001704000303400103400c0ea4000381000c114004140d0b2042c210768041c5011a1102c180810103204000b00358410302a0701e01c1c112015401c2906260144102d0f104094082640040040c40080d2641c01148101d000f815099400c40d02d400302410000b001c010700304c41c00c41d0017041c40500042c0d2881d151260801c0b0700c1d0001c0320b155807030b46d02c80209402020030482c01d90035841101d15603005220074503100c10207000c450038800500740d41c140072040808071000d43c00310b51600600c00c0c10f505100c6001600c1034150400f2011452941d2810b01c90000d02c201c40c006070000400080b04c505018001030944003001165440e605a2903444144900d5108080da825500540c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 211439685 1250 211438435 211438459
    0x1050c0a050d27031e0e01080403140d060603050a05010e061e0916080709030203030a03200a0507020901091e0207060b091501180f0e0702190501060e090a02 69
    0x100c5600941145920440005488000f1030900f4904869268a4404900d1038003100010140c0c4a02e18070220105400003040089042c0e1001d081282c10034506410031244000050601d0712601e500308040b407022070b41c1540c0f00341814030080a456075014404c0402d0405000c41d1540c03141d8402d05041359802144041540c60390801c1190350281c02018003601248410108080e5594120b074501604070804070100b0450b4181024140c01c10050004060000740b010410260f1008411100586403625002801e80c0d00c2c5507003100500341000c03c0300c800141c00710f40460419048801466200d0080314000c010342ea8524090303054860003d810003010240040382c03d0780904a4014124061145c9030100780d1901c0c0d2004506281f03c00c40d8a0100517401044000c03465030814034816900c51008102a000c504120010407641201d12441d081c0381d12400000f0301c020710a01c00c07d4038980e06802d080b95504040d0038070798081c1c1070074054110b0072103900c4c011400c5180c0000301e0307440701540944000c521070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 211440935 1250 211439685 211439687
    0x30303020903070f060309060e1c0509032107210504050402030601050702040f09060c1d0909070e100f0f030201020c0f04150314060c092202040b0406030c0e0301050c0a 74
    0x1401481d2550307050700c030304000850440b00322160070303019102c1540d0000d40d1507000e08090060f508c0301c580c4011290040041c21700880d002c5040c0c0d000300c8100c3d00f0020741c0d500d8200003291608040c101d1010744070003d8111a0049640030000303004480c0140e044010a84581d80205068260030000b1408910700300310410a0303050940246038000414140706060154540200701603e03120004050055a1031385420200119441012030702030103440c00c0c0c400020107026400c50641c1b140882445070381044002540e643d030801030315014080f20501c1244508090001c64000ea400d801858146101d80c1800310f24284002c416000f00d0390140d0080441180e10010700002c50403401d100da030807a8642e18600080c400d2451404010742c850801e04d08482207003401c660901c84040e114661082c000c0010728100c1e56500080c816000c1519070748035402a15070503401c004d20030303684488064440400e000800380e4043e40078045206aa0304d600c282403111000705070803941e0403100c018882a09210070541e407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 211442185 1250 211440935 211440937
    0x31b090a0f060e0901090b150a030b190212150303190f0908010e15130c15050c0601030f0209060a06140c01090c0b040609091e09020d1709030d02030408060103030302 73
    0x1d50340e0400300180c62602d80e5070140c2200e20440300c07061640e440b45400d004102a9083c602d07400140d409112158034440c10014901d240300740310192030061072134081b400c43c1206038201c0c540701d00070307110031035490a0040c0c12043c00b03d421034411480d0202d1301c030881e40506000c0b00b1540e00c0701e511008000700f4000c08000341c17100c810b006480300811814550218a0000074803c1c40300c0110a40002c1c188424140300d904040c6030020015000b0100c0120144002851030328200207030b03013514440700b41000450390211014010130020a14510518000105010001d401d80d042c8500a0700c82942035036441d014040544d00c03900c100f400169500301500e0442c2c945201038042011600300210302c004141c3c590850015041d00480c041303080c0001c08224050700000002c00910f80c05c01d0a0026191000003243c040e151054410845a02c0302c0da0b00f000c5680700440441c25690020560110301e1030b80d0000d20441c2c010402840c080d00c144141c002000e4000002e94040f148240000e003c16821960100c001e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 211443435 1250 211442185 211442201
    0x50103030c02090a0e0a030315080c03071a070f0b0106090602011812050c01020d050105012606010c020d020907080a2301050d081b0a2006121b07030e031b090a 70
    0x10f01350380c840d420041c5003400c1c08141d140d5802685c0201c1d80002c850000300e5610a00e601422840c1e0090045071880d0b00e01180700c0040390030246114840740014441650141b00342c0070010090a004100c0008001c0c00c00a43ca05035030a640e102924162560300c140d08a410f0401280391002801000e9000240c051210340040071507407801a040c5004d08020b0340c00c0ea08000c9500400648450040c840b5580c861031280c40080b81d00509258103c062210300d00545001d082141000a030f503091b43d0039525070f044580200c69002e000c071070052800d1040200300120a940085000d81440c8040340300300e50b000340ca2412610803080c10246c5034640020450401e964000441d60385070203000e03001001e480380c11080c0751031010718080c10030810617141c40c030030080e003415641800d1502903803080847c1c1c68000641e0700f8860144580500c2c3d48484000392102031042415141c0340b54001610300401d41e01c01c86200680405030102c840900d010640c64203224104150351750070020750b03000210401c1d826000660 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 211444685 1250 211443435 211443451
    0x4030f060f02180f0307080109030504051c020904030305060d0f080c0106061d0603060d06091406010f0e010501080a0b030607020c040b0906361006120608070605091f0e1201050103030c0209 83
    0x82181e647e40d4000c2e0941d170200e1002c0d0040768010504118074180b0f140c821410b1040b040c000301c0c50300752950010b0380340d020291014041540d90f800080894035160f0620352040e4120503980c250856516021550b92f20000b603108a950170b1420004245024220981030002d40000f010681c900140c1848900c2e0001001541c0c0160a500400e02040c0c4070712524510038010b10f070b02c4c001d001c02940a40e107010811f03406000020007082c01040341c081e009016030b040d128241b8000c07403aa2900d1071885c0c00382c0086a00142c0c94090082440f0754250002100c0c1c8000605503020f0080b200c1e5039080105400701110720310303081100300c1d501407034440035603004203100090070030103208807050350a9200c0c41250441d0f48104021840c1000d000050f00992522140e680600e018013070703130703041c201500d4079010f06114643c1449000326520100740e07141c0c011060f0260100c900d2400e400c0012000804004480001a0041902100b140315800e81805080d060703903059201c40340500341035828400340500c000c103908 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 211445935 1250 211444685 211444693
    0x6090709240f0f06081015020a1401061514070b04020a0b07150e0102030709030209190e0303160503041a0a0e011803270b1e04030f060f02180f03 64
    0x1480c00446410300300c01a10814281403801070510784010161040c58010f4828019888204003414686c0441101543d03103c44601c1000842c0f40c2c0141c0c40c100c0c0c02d400007004c042510307130418035a010541c0f00100302c42418000c0207001e403840405441d4036115080d011003501c801c01031000807584903100c03603803c58401703094182e02c1c698660240209802c0303480c04541030786c90b880d58031340c0311051401003204031840b0b0b000852441c1441d1401800300c00701c40c44001c0c0120045030005100b621501e00303080c0c80114603002400b6602941180c41c2d180d901c2119450b40c1c01540c1c070280741c412032265055912a40d807010f920040c020040b9613128080100a0110010380c5c0ca1700c0040111200a00030411401c850040b00440b100507440c000e080300c0c80100121540710b810106504411038280a8003084400b840141c0b0398074070504031500384448003c2c0a040340800b00040000030881c1000741e020480d07004401c204000c52814030507030b080e4860400c0c00345801c078101804e6189460f20700c4a072030110310014200c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 211447185 1250 211445935 211445981
    0x12050624030a05030316080c070b040206090604090605030d08010b0a03020706020405041103040c091107080c0c09010f030b0109050c0f0a0e03011d10020301030210080a060509040c080f06090709 85
    0x6072402c0040c0300c00315282e801c04401e1181040300440400e00542441c14031085501d850144580d050160480103000c0303140070804541951502d000310381698030050051aa02c9441c1c0840001415003031060b18080d1081d010280910b80c4a460401d060380c0304000a5407074201000c004070080d410001064a80326400c100014075540e6910401400005100c0c10f640c036450b142c1001c103804407130390f44031050580c107006949010391070700402c880d240c5500c500016190051b20b5400c0d407514198040f41c41e002007000002103a0700710215518801c9034450209540507a0301c80e070320501541c1d01603581d403864480034415901d01d4504031010300401240c61402d002c807201c00701c0010707003903803038152701000d1442c00f81010f142801d4040c0400349005420407002c0d0701d154510740c0421784040d1440a02400c025119011940400b40364110300014500140300203518103142c1402070403448030b445101c0c003a1250715864400c84c203011994920610700b0401400e642480d14900c08003400904440c000b00615500c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 211448435 1250 211447185 211447189
    0x10512180d080a0e0a080306010c1103010906021905073909020c07060e0d02040513060f05060a090b0a0b03090c0301021b01150b03130f05010219080112050624 70
    0x3030118820715540e1204518180703100c0c0c440440e82201580e00d000d8110f11084c20104000100b242e170448000c0c46e0001e14429035083c4121000401e075170f5103506500f048094028043c1c9500606101070984442e40500d58141070103071050f200e051001801c40c180c20002070a000214074070301d9030005403d81813214268182c21100b052401c2ca0f00724004042c3d01080c6148035400070003541e800b4154604000c0d84c00d15424001404040380c0444c028410794440d4009040c072401c0b01d51a50085030710102c10f004001ca90305108010741011034a46010300c20f00840000c0c14210340c000c080003c0301c080d14030700b2140d0900c03640d00000d510040c003404181c0304501c540a403644007480100038120700000c0d200018200c01514a083d1402e41c1180c01d400c416025003402104a401d00302c035003180c84001e003410030a25a10b80721519180048000d855135202003034580081e00106c42c190103039111541c400049a0b29101902d050089a0101604941c0300000048070386010885004402291480341402d007155980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 211449685 1250 211448435 211448443
    0x5131b090f090c142b06030b0604020c0304170c01120209061605010e0a26091c060902040515040b040203220203070b0a0c060501140f04020703140c031c0b01051218 72
    0x2440b1000d1040889040841320f0498032841c45c101c1210809000716865511008640d82026012502c0303550300080d400050b25003001114010948182c407801015143c0c04013a45581c0e031800413034049001050506400b494500c22100c190714004c00e014100ba060072102c8180e400f4000c4202c039299a2000c0c400b100010030000140c0d80c602c214001c1c51014980c420f900e095002c0d179400390380d06034000d00c065603c0340d446162031065000c031490300b04800540f0b81081c4002d071842d9040a50064078100901114504102c0001301064080e9400e20035a080c94090000700c0c40304881c8003460035400760640c0b0f02a0107a010018134107000908a4005c50348941c1c2c5c0e82c5456204100d0440850f000011010400803180960b6005017202e4584014208160000c5559212001140c41c411036000a82c4010117000307141c0080c3c4026003500d0341c2d0300ca42ea40c42c480303560381d401214108004c00708101d0022020f105805010a20b1030180e540b5030400c44074034040400d020020f80303940b130614040e02e8000c00401c0c00b04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 211450935 1250 211449685 211449697
    0xf020309010e16081510030b1305010e0a053f03090d0206040201020c060c0f0f0705150f22080604051005181e010605131b090f090c14 59
    0x1d000d40700d56080c0b43c90078180c40e640072105a9441020041000c02044400b440314003000710310b640b42d1341c203d2151203456450300b0007024481c518080c4807000001c42d2041000c2c501c01c1000300100c4841420941d96081102c9000b403056002c01c8a6115034040001000c001c041000c40d90002203048203c429286c03000e116131149401d00c0401000140f000401802803140d20600143c0007078186a00002d460799401100d0703901900000841101000c01003015940404d84881942d0b500e190358902c684d142c040c40c1c89900d1049031110401140a1201021681840c0031030f200c95207031901010300d90f440000400c1d139500006a5000d00000c3c40b01090140ea4400e0344038801a006000c150200c00d002ca4401421843c0201b0003c00c035221041000984142da144101c5400000307040c00208541c050805900900e420982c1120b5030f03004c0b0030303030341d040148103580c0d07050300f0350407450004411610700c0c94610400025032800c01040100006982c4120151034081c038007944103075081110320115a21807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 211452185 1250 211450935 211450951
    0x20f091807260a15091b0315061209050304050d0305030115080c09092203110601050d030525080412030f0e0a03022806120501140d03030506040f0203 66
    0x5141000040c80d8020003038041c0c502485601100c60481e00c2c1d0101480800403c010107082e5168210007007040b250403081d00516800d001880042d04e1090301c9030f403c1900c84014030100e401c021034024120040e480341c07001c0d40c070181c7c0c40c4955241c1e0783c1408005404000810b40700e40c0410000800d0f251200242003c1d1039000c0e4442c0c40e541d504d88035000a452031070382111009c010b200f2090020003440c242c2201c0ca1803400700e074a400141c4480f080394010698003e40300440d070f064080c098080507001010840c00340d1405040e01c4050382d072030301880308020381c58800600080c0704000c40348402403041e04040000c0c0c034103e90041e440030160741e0500366a00c03179000340408108403140e420406d031380305942c3c41541d0898600703600e00b0101c0901040c840006800000d01c241054640344030256105040403a010980c0001e10700700c0c81c1e40d100e01508903c1c0448914003007604050000c1180f4503613004544401102030700001240e40d550300c00f00e00501000d861558041d444410080072105103002960003850380d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 211453435 1250 211452185 211452229
    0x20a02030a110601050609040504060b10030b040b0307080d05030a0e03040605040312030c05030109020906210601020f0606060318030d09140705040e0a030804140712020901060c050c04020f09 84
    0x203001c0000d0b0a904180b030801040d5030103400180110744840c0c0c1a112080d805446c0414075880d28a89500a8000c1c0c0e07200a40222900d0031490303806e03034140c200090081c825501089a0000e0a0a040c1c445449010310500c03548040c10b254807483c403480003191700640b40080000c081c0308050065096a109903c41800641c003c5818400c0c4500c201510403911803909040100c400c08510240c41c2d400144941424a43d02103403d100070b880324011150300076240309000ba000c543d482078010004000741c0e245401840703181950320f0302c6800014501d01409000380070604550340d00b80c079044101c180404030380341c46c0001d0210300400041401a517038030030710403143c0d0f854503585600c21a26200065011610a504140b2022100345011802940941d01031500001a95480c1040f100703820800e02550028443c842c1c00107240012003880c0d403900d070b1003180d280500e82d0740c866044420246402c0f0181c01604040d0100425107040d43c028001e41c006603542030b040100c8880080e11602c1c0310481d41c803203889 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 211454685 1250 211453435 211453447
    0x40b091b13180c03050f04030e060d1103010807081b300615030d0c0b0703060f031209050108040308070305071211131a0703081e040f02090f0610051606020a0203 71
    0x8581c0104464038191380341c104030529002034010301303080020344007900f0302c8020a60810151201011103080b0311721201c00b408010210000c9400a50091086042900440a000ca03640350007041c0c100c03002e030910b807013940c800d0b402c001048230003002d005240c201140e8011203078003008855840e6000106a100240c031051420701c0c1d0a40845041d80348a61087d00b1031105907054640100343d800329203400440720409a91494010350091590303420145454090384000401c010260240001c0c1c0223081e55024070840c3e4410042d0394408080e43d004003c2500d500004404c144242d1019604c103915141044040d07010030701001c1154101100c00c00403110000d08180c8501d003501c1590001c3c82c000c520404020481e201ca040540141c640050410800fa070101d14468641556421440744600003c0e2950400d49049091103212074801c03400340a400340059003250035544181d2003518068013404281071280b100b00c030315600c04003207290140c035030350303d1400072911901c09028101c80680085507600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 211455935 1250 211454685 211454729
    0x608150702070f06050708090306010b1c05010609030212070302060f090405010803120f090c1005030a0f09110103020f0f030403030b030708010e0c1011150114040b091b13 75
    0x44000303040030305542c40030504000e401c0c00c00c00702d002180d00e42c3c40d00c00e4580b001441c01901c20300c14170260039418412840041054000c0d540105004011030303614000c50700710700400c80c0c01c0c3c480920820010682c1c0c3c103010400340c1861036411558041140c00c1c2c2d91801d481c2e5002480c150803100c0010082100400d60301c00a0820344199809042c4c02c070300a6041400c007030041c0d43d00400040580048102000101e0700c2c1d040100302c5070400240040c01c1c400c0c48050510b0007401c0741c10460f030901403e828203030665130348015445404402d507002a424550045100d0055010750300c003418a0100740410416101d544002201a6002c3c130b200350303004100c5411850030140b4208440d086080282d1508510f078a0303105000442c407440708000e0342c40752540b110802050301d00c44200208210f1a009404240201d1141030211074103070307014941c10b18085900ea03410b000c21150080c01685d080300024010840c0361040c20304001880d812010684d140510103503491880340b04030760080a441d005604c0d00c1c0c260f1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 211457185 1250 211455935 211455973
    0x91401090c260c01030c0c080301060302030a061203090311010203120a050406061706010323100605040606030b090a09080c03041203080a05070f0e121501050f0d0201020d110106090608 81
    0x2c120090358101c508074012032440e180c01d601d407a0107040c50307941c06100316a58098102001080c0e0042c0c0401c1d103942c0d4468010b40654022100c40c1a1146051404200c0c42110406149083d41590752000014219a00c00d500b20551401290651000f4400400002e070b010282c9845078030004000300e224107151805e1019100540c02407180500b10410000c12004006809811260442500e01c054917060000d1a840350709074104a206d40944544070034803075074070340008048801c00d4400b007042c81c0c4d50342006c03001c4460101c041a407200822001ca942d81d0345a8008001003030261075128070b05550b407070f07000703145501c05d501c8214400c10000c451814107401c24dc5980c1d11091843c420b0200d864010b400404010803202031105200304440030700300d00c0d1a0b6605031011414807200719150388060b9610166040024420988141e07104400d030306c000e04018450080301a4181c00804a0b03500700441030b40c1040782c03903c90f0701c050365840000258640550041d000102a044045d0500d044200140040c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 211458435 1250 211457185 211457219
    0x616030e010f09110d0305221d0402090609090703150e07060809010515060313030e03062a0c03030112031e0905041a03060c0706140708060a0f08060a091401090c 71
    0x22401c5c0300f000d8140842d820034110b07135210004210340704141c00036016590005801d5000100041050750000082002842500340590300860f4141919a01c1c1e10402800020803113103d84990041c8030100001280080c181c00030401551002c50500404550640303450880e92000300012444001c1c055082d000384140c0d604192016a107081100c400d50100710a0b00c80035048560786081240084140b40c41b0b46600355102d00020b00760303180d80c24466005030500c0100c043d24403500c620315411000507030003c811540451100c1001d14150ba2801c02204001940c812054085c40000f40c200b210388071079031401c4108101c682d151103201c3c074107200a00c400c4510900034408134080268008403da070700007502c164040f120381d02880d81c4032054030b000c402030f03c24400240318100001080c4080c2c81d40001c1120702c100f01c01d0b40c02c1e0042c590354105000c4140311900c120452034110002240f403200ca0b03608024016400340f60f02079040c1c00740042c4039086032071420342580c540484100610000300305601e0000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 211459685 1250 211458435 211458439
    0x5130203011a04050d0f06021b0706030e060f06040b010c0b0901020d060b0702010e0405070e130e0d0503160507031709010b031e120c01091202010b030106060903050616030e010f0911 80
    0x41080d084c4004904801400c500c007034104c81d498010501007161703503012144041ca0400440720070b81c2041d07101c02e94848035805441c0110f424003080003840c0c00009440c5101d942a003c2c00000f0307454540602c001482400364103410003200c188001e001c11008540e95000301d0800d4001039036103400b07007900c0080312071a80141002c004204100320151380c3c01065042d0003c0202c5000549484411064030411030711000d46801585c040c200001c03014a036030040c1c681d40e40300c1d0103550080140e002c0480d0288400c4801d01c08081d0004040014548204050803200e40329091134504000c1500c115640b10908807031105440e074542c0401c20072800d083c00004001030440d125060720300940d500c00e5444a4144038010580807011070300c0c04589400750001a0801e401c054054603140801100034080c244022206000350b00308040014072911a240200480c2d403c100030340196226500080b443c0c1c0f6016000600305900c592800348640e80a1040c5074000011000c00031f510f0032103180101002c89003854243c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 211460935 1250 211459685 211459687
    0x403021203010b0d050702030c07081b0406050a06031e140907050103020c030a03090602040e09030703110604020603010608090c0411042916080408060117100b21010605130203011a 79
    0xb040b5803d02a66000303203010034080b80583d40d2620072031a50003100554034081c80766000003e0007a8001c0f4521424503601c60100714a40140d00901050700d5980c850640c01030b0095004011240c4660f1001401400a0340103804494130702171048103481d51980d07917204c9a0036203428000100300c10426000102401e0805604110750010165200d0107984080428161900c0f580401c00c00164119000381c10b07040c101c0c03106410800889035903030300844411000305034070100104140070b0005155103d15801003d0030b00c2c680c00c001c0c003291420b8002d45100068450b0303440980c4180c0d182e0240401840001082a845529080c203807064924502000c2103036007404032a584038101c00d00101ca01d000000c05c103039044403c2c00e15144041c0c3c49a0b030701000150203140c0021503603950400528482c049078000b191000c0200480b1081104d09000049a0240c455003240c5940b150541c9405034034013159000041c03143d44c070800f14015825400a000c0b07003030380c00001030014000c44001c1c040e542c142d0112031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 211462185 1250 211460935 211460939
    0x60b030c010e030706180f03080415091802070615030303020d0b040204230a09050c0405101805090a060906030b072303011a04151e05120609040c050d0308040302120301 74
    0xb013511100140204001c01403000c00c050a40d6607120741080080201d40c0c1c1d07005400e65641002d0440b81c005001e6446080060b040440205200c2d11358841603c0700e02464170100116251224001d500c414021640c45480f01424220f0052542612005500a480240c0d444000c001d081c001c5074154260030b407242d841404188929200035411044e0031001c40015002c4403c1d400c00500e03003100a07400070405900384010840e510a90303101910440302c0c02c0e01d10700320403003440ba0191000032a4401013480154103103820841d03880c00740c0310035800000c0a640007422030789414a24050303407545d4101303440c41c1e070141040c01410b541c0301c0209600b40b84101354035140c1a041d0b000d4226184010710030403030203907841184c5502c03202c5114101c41c000c01103403041440c0d281c0c0d0100c0251484031404c003011603001001c07807424078440c0035004a82410802e048100340d1552000100b280d1450f01030000d0f14020803084020855455699040641500a8407090014030380b40c60004e00d08804841c1d00101c2040c14001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 211463435 1250 211462185 211462189
    0x50703020705030702040509010b0a060c02010f0c0317100f0b070b010807030c0b0705030d061203092709171215061810180b0711030706140c0316060b030c010e 70
    0xd071134080394100c03004500c503250030324824090300914031141e0313111241e034a000a409030048100c1c00d020740300380c8401a80d091400010381d07080c0300d001c0025000c90151802c41400c00c0300c401345aa840300c4050a2018510344481800800f10300c02d4100070302d6840009118005e0240402541d8010050722004000150656484040200b4a0710618202d10404551142005014400d440782d040f00074108120895503401941c0c4400f07800c010a03000b2034240800890070f09403030306030320514801c880c1040140c0b004180321403009020300c8605030303015480740050b1041040511b0050049a804140c0a01d4a04103030256520b0b03d14207480b607512031002048205400010070019504554089a10401002c0301d20002d42d15810a0960791a0401c150000451680d00640141102a001d0002c0d124020004018103a0f52070003406440d02054078028961401034404000f45105c40c40035003079a0900007071420802018000c0e02e002c81b4080c2e1030b042d91404a084c100b103908495042441c1600142c001400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 211464685 1250 211463435 211463437
    0x160f0501091e0504110703120b1e06040305070803091302090d15020d05010e09010c020c030c090414060405030d0f02090a0b0310170c01020f030a050a180b0a020106060305070302070503 81
    0x2c1204040840020745030000d50340181201c0080038042c00030f028480c01e8211107055680200780c01c5001c180720810080c00c400c518031a8135440e490107080b2101a89510800307000c0000260109948503500304404000228144191402411010011a21150540c0030844502e445948039a801881070110300300956039054001c2406030010000d4003900c201d044204064824006c030701e400e250600c0000600b06001241c0f4501c1155034000804c40c20011000407a16200d40f88211517059102500301c0c03000e0301e44560f42540051017001f042c00907c03503080c0a0b50a22504039020780d111342002c1b07010074050210b401544000d18000d8411881c284002001035515900e1b802880f4402d40040300250380484900c4012026100d0080244200fa00d044081603130f42120b44941ea005000b454800d042c0200c0000c1078030349510036500c8032410619801c204031a07001c0f031502903000c42d802c1604002030844860b00100749070079240e0300101c1d641d42058409015110041c011000b054410043c40001c114040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 211465935 1250 211464685 211464689
    0x1e0906010b0f09041e06050301060501022814060421020303070c0303060b04030b0405071a0706020c1e03030a0509070609060c02040b09180609010c0504030f150e160f050109 76
    0x54801034550041101d80d0b0400d014840025030024602081e00301d40c1c2468010b4403080d044c091105004641c0c681e0705042c2618194070816001d83d01c1452003001841c2203040c50328816011090900d030480c66606c0b01080040301c0341c01a0a40c0c0c00413418030043c8003002042c6100d5001504149002035a00400299a403000801030020051840300400c1010721a070440b40091604003081c0c0e44583c2c590412400c0d42a0a880440716885040000110303c203103661100c50580c0400152800c0008541741c103006035109006c554454004d020024a010703400030359442442111200540c0c6900c0e21121032000c81d940070704017000701d9002d103a04000355903120117000300303446051809000540007440400d02414070400c00a034000072407401c202c03042c0410700c03900e10750100c008103d4440c1d456022190707080b20b0b8050300500008400b00020720104001421140c403007481140006088903140030080c045500c086100401500031480c070700b07540380200340d841016200082d0b0602c00da81c90034002034143d039214 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 211467185 1250 211465935 211465949
    0x90602072103050a0c21061502160905060a0b0c0a06020d0e0d0c1211100204080114010f030f0f03050705120d0b030610030605090708030705071a030f06040b0d05151e090601 76
    0x200d41b100003680c03904072100405084031084444169140301075210103515103560780c4070701e80d00c0380016081210f004060240720080c1000760194140711840b00140d00ca240002d0181c441c00da9a000024000d10040000c221503800c0012501c03002c004050403c00c0c80108a0200410b980f0084046003c4040c60548944182001c500445002c4115420000b05034040c00409101040003c1e20030170640104510409000300a0082d80e07c6100e0707003480d10454040540101e02d00d048000c002401d00b40650f01280c0a41061420091a070350703000c0c900490f00681066000300420030910031000b50040c822104800c8000d04079038688035003034401803d054032000c1d2925465101094445100f4070018000d0311445003920398401c4135040071603a6207450310844454a60f000c0c031540910f0080c206aa006001a08480481d40c441004000c003a10152481030740c00f11071070034550000741d810031109450360b60000c94070005190003040500140c1d68030181d1071120700060f0401124040c04207000d410f42e410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 211468435 1250 211467185 211467227
    0x30903071404060e1003031107060e0d060204050618030609010e030d05060118080a0b060a03150e1e07030c0602010905031e0403022101060b0f0706090602072103050a0c 74
    0x41000140039000e80c0d0f11035008044421300788009148a45070880a480c00391305d9080c41030359010525541c94110784075050004142d84071030703152484c0c0b036030b000b52200c3d0107001c01500f440d85031400152280d000c607045021088042d091a16107003400d0000781e90180d08000200640540c03034072040d03100d1007076109207032101c0c1d42c840005410740e0066094192100c00021222300580d15031101c1340d582c44081406650802240c8001030540c0b070f107403c0c03010650b5400420840820012a8507801070604940128402d0044080b8456060030401000840559440080001034510300b41030002603070316000ba01c21a4144040c0201003000001110203030000340014a203444880990141540520340000354004410b15949090000b0941078080c802d10355002000803e5440b48040180e205106415000f10030912860300030422550081d03c0c0075008250151501c0003d5035940400c1d01058105c0260103c000741c5070728150391604c245a07000d02907041c10089040807a9000d09207068081003aa58407603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 211469685 1250 211468435 211468469
    0xf041814100303051c091a0a06271d0309040614010c02060c0f0a03030c0206070f0210020a030b0a03081c09020307090902010c02031507020f120306190803120a0b0303090307 76
    0x40070242030b910150a20601b04a222082d2502d12400050301d19504026203d05c008642c4805140c42203034101d074103403515603604103401d0747d00d200c81d1024055000c4185660702058101c41c0c28850301c1006890b110805107590720054410041160907940001c4400450700c1e1540a050342c21500103000950100d17203140e12280580e10140c0340ca07844c0790f440c62150083c00c24500425070540c014408201d442d40940f0007550701d10070200c9806503042500c0700140d0111040200035201d5500400f4003903074071720300414004824004241c2d038115a52040b202d0702c00000d1203039154415200ca2000280600800b440407052940000c0d50312507640c010a00001c0c0c0c1c803035616045a020300d01a4441640c045d0a865460108401c0801312040c1169480094090341001d4101c02e1404126a48801107114070030f401e5444800c1400b10304000b802c1302440140f000fa6000c102c0c6501080600720740c4503103849082141c0340200204040e00c181d140058041c0c1d000788160003d0ba030300440c601d400d442b41c8415844443ca = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 211470935 1250 211469685 211469707
    0x6040201030905100f0f06170a0b151c0302010501080625120906051008030a020a060c0908030310080d0906080a0c050904020a030f1a01090303050705030f04181410030305 75
    0x255500140400d603864200c1c61780f0320394500e030460004540d108100f00501540d51030591030510b14002c1260164105901da10001021800802d801c042852070482d1100152004502604d1b0306050040c00c41d5071802d2140c0400d0343c24003446000d0300500028106608010300145071403070340071040c5880a5001d4400610207403090400c0b8580c041042002d2212001c0d074100900280350aa444035800c107200360002c140d840001084400c4421355500800340c821441e1907030002018800b00303140030842c3c5500e00160600c020030282d030003203040c040103004a40ca001e0306549800c0e03c1c43d1043c001d02023840300800045402403203059000107038007030100301030f90626400c407511b04c41c041d4480d034094404100030300c00907803580c40380b101c2d03408251081013a0003040815500d50000402c000c0e002401030441400000c0c0708102501c0c1c8284a2000c81b4106885034210f0816900180c00280440200300d410f000c00c010300c3d000d44048551403c0014203542021001c0454441042c003014052110005504100f6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 211472185 1250 211470935 211470943
    0x4503020c130b01020607180b0711090412030b0315011502010f110915040b09121f0b010e010f09060c020f0301051e0a020a021f0912050901030c1106040201030905 71
    0x3410000c00070940000e90405038401400d20030503050040c892000082d4072103026031340550940c1c91b02000304258a1038980c0e4003a01d6803109000701c44006083c00704940648500030403d005502c075a42d07810001c1842c6070b00404803400d00040d42e22943c041603001407038503400190305054580070708061800e5440284182c1c0901001c550000300b0a151400c03c604820101018009218045611a814201c03402480d03c0900644c0204c4d48802401c0001003043d15200c01c06e0404810030a003600c0c56407007540c05041038a20110708112600340c540b5030b21103142d80d0180380341c00071041c00d003071a6201c060387c018000d1084040d4040c00081c0048514071030213541d1039031100c042e1600c005009001074500030450b00c00921121610742a910400004140091107034000c0d48c916081650050030001c20321307103491920f0840079900000d02603885003020045821031840341d007205032945485a680841f44001800c40710720303030304000030040d001c403100320049004240b4030f40050f02444c0116840c0c0240c20582d0030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 211473435 1250 211472185 211472203
    0x40207030309210906020601081504022106010e060103140103020f06040308030c1213080f1303050a0c05030f0f060402060c010e030a08010504110c0a020d0813030303450302 76
    0x15840c03040701240f003543d60f0b0f1090a4464015510301a4a81e52914180e071b80300710a0081c00c145030030122090784505051f00300541e119000800e0680040c0100782800707203040d5a0210500145c11007801070041e088601c500c590820020310342007114240781c50309542c40c50010302000f0320030107103110071241315640c0c0b0050b50041c0d600b2205e060365070b050080d0080344690110314404c4200d049400000c40305408401d10041c03070307a0000d021500d00050002412a83d0b4000c08514542c103145810210101d001002080909482210401000c60a1000b0149040d00030000e0300c3c04c980c00302d0900020350402203a44d6030000e81c1606c0d440d89400c5043c82003809001c01807800a0a40300c0811125030595000049504803030081e1030810500c80c80c00d18420300d901c1126455092540302e1038540c001824010942032100340109d181e00e04010b10030080e22403040a607801640003980b590507490907400c1c03800303403d8040841c2d402c00e10b200b4010b0a240354854644090702c0c042ca001c00305101014140284189a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 211474685 1250 211473435 211473443
    0x60a03090b280b150c100c02070b030c0d110706141005031209030f0303070207030b130812060102070807090204030b090705010912050f0111030403021510120204140c03042d02040207030309 83
    0x2480c5c08180604e160765050f600c4504604a082c5848000101c0c00490318909845410402c0c42c555550400714000711750200000358003040c0e40702642c0c02c1542d8003d0140003000c0c454140070615003032401c01c1061f0900c01605003594401c0c52402003203d50b40c0002c00314030910050358410f464648200000b403d10b5081030305181c00c0c1c0000030801c8400e41e404505241a00d20805219078551168039407001c40e6025050020240720080142e402203c2d0740d070341800d5111205204880140d40c0302d200450400c09075500c138661f0150045000d1080200d0320780200d9010202800602580d40381000081001c2ca8511900803c40e201d0702042c2d050190a001e030780020301c5000300902c000211450814002c6c0c0c8222801d030010b0088008445211410821907409401e50b003c10101e11030400d1078848500f1541c0c2c1049920035520020541c0c0356000081d59449030750302c481040e44902c0c10f13003400c480340b82c1130030210240c20110408600c031907007124446195060701a02d00607158000c615040c1d00806660070094 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 211475935 1250 211474685 211474687
    0x30f06080606090702011407210603030e0a06110a021c050111070201110102031e0a0e01110a1808062a03090105040c05030c060403120e060a03090b280b15 68
    0x410310310380c00540d0310700442c010303194030185503a43e2a0403402c8508090684904d2400d10010a080d10321414501890603100c03043c1060008a08103240c0455100b0751046001c282c4004a104030362030040d010304020521810508100c0401c071792456115503110800a20a240d40551a00224240f110003030788035a0010080204500410044009400c10f0008034001000003012402654060094a014043c640700ea4075100c6107201e442003a60b6030090080380c00702d0744c60382d400040d4003007401400c6200d01240c40142d600d040e035400c002d183d17001c030b15034102460040b184200081070340011f02c16800183c202d00301c20300408000d00214202c042c01d043c40342240020040c401001010340c00b103401148284558080c6a46d078801303150300d03030218010869011030180000c10111310f07000b695a00c55801c510305010220b02c0c0c0c800280503a045403441c840040d40c0c4a08030700070066116807036600724078110700210b4011020007040000e43d8801c030340b000d242902c2e5412111140c440701400c20803012154182c0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 211477185 1250 211475935 211475939
    0xa020c030d0e040b060414010309020310090f020a090c0207090510050d0b1915180f090b01030c0902191b080307261e070903020303070f05010f0605010e040c030f06 72
    0x40990300b28400d0b1903c110300d452000c0c000c2d40f522030200d80894403090003100c001c0148400541c0201013140c0183d816001da0704c4e1440380c07407105201b40c0861b00e1161600c55002d4907103005001004031141c002e001001d14110080303000700c1d000a04a402c0310000b16010880365101c000d0305000e0741d410740c00203030488450000641085004160680316110000d91020031010081400c0309a6070b0f841040c2c0024680c160f014001d43d820007209200c95955a01e0201d440d8480740300d80d0042302c4031301200781c584600e604018010401c120f80f092005000c0440b0640c10000181c8085402c1c51030303071800c2070030300800030402841d418180c10b40d044800d4008800eaa22031500342000342c0b8885810f40000d05d000c030b03180007542d07aa400d0100054041e0b4008141304803179580c0c11f100d00c07007815805040c0f05d05110380601c001005a600b04000d024030343c03003032580410107041c5142c03880c03d5418446000c40e0050402c0818030040e680801c031940058404c8a0110b2550002242540200b00a404101446081c0400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 211478435 1250 211477185 211477187
    0x106090203090606030a02221e0504021503010509010e071e05040f05030609030a080603030403050d030c030b0f0d020613050d0609030206011a0909071b0c050a06170a020a020c030d 79
    0x81c6220315100015035070300c1c1d80c03041e08040e2500c2044000a41c420b008036461030b516103a110100c240c96802e03180008003250140c0070b580000c205a0403000701152a2801c120071420308003103038a40143c800900e03c0c19941400000b500414050081402c2d141c0070100041d03074144265100121514400841c80302c4110480000301154458091075120f08550040014941000a6540d05c41c040b4000034500b004120103044030032000180945034144007d1002002041b014001b4a010028079100000c0c948424200038065408800700e80e4072031260484800745a49600c2e4015660540c1180c2c0300d0b50f620742c041c1d0640340b1001984c201c0781d0007443c800c110108000c403552010bc00ba501940844403eaa80e4254001d508007461908445a0700140844102401c019148139080f121508040d8800d5072051500355030050000e00941c0c07000c0d0803d00070032032810301030700140281c145450407901c000701001e400d40b010003014100c13005541d4009a0a01054824000354102318001001c1d500010300317600c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 211479685 1250 211478435 211478437
    0x70e0c04060c1502030a09050d050f160203070302030714190311131d1f0612120c082803020405030309130b030610060305010f03030c060504050c1201021201080a0309050d050f01060902 81
    0x14211224400c8027040c03001c42d8050000e884050500c6241e2038644000807141d13280c0381200102c01c0381c1500c1003140c084016a41401310601500424901110380100e4034100004030703840c400b403107c8842d0203c1c000d0001c1810b1804d12500c8100c1a945907061130300c02481d087c02405007200d07210703411010307030300c410303c04040403d032a05001581400d4050310303001c203140101110403610549002d494001c40e11400100016050240d0b80d1190914080715250f5480b040344681c86a000c03c0081200c00c0403000460703e856202e021314a64178a8214285402c200200b543c2c0e1040d14580740c03080d4110fa210b50f03100880da07000040b41c0107002d000d90303c20f07040c9031101c000c820b440d40c042ca1000c641020000702d28080300c0c0210408494242e40c4000b100c07012611208002c0030301601c00d45160003000b20411040d1102b484807c201b4900b00c00040c4e407465001100c001d107240607040003c00e0340181c4c0301070700800d500c1911101980d45c1110a999107150314034240f841c0110913082210f4550a01d24001925240f5078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 211480935 1250 211479685 211479701
    0x10609170303010806010e13230f06010e072001060311031c020705010f3c1b0b0c04180203070806010e01020d050d020706060b0903070e0c04060c1502030a 68
    0x105500c0603a4008210356512400240540c02540e448540100703d25140d1159043d0000031031107500e000c0303810307640700c0010448640340c03501300d03100d407012880003161000c02469551822403005080154101b14404400d00070241c030f0803040295040300d00080ca01920001105201190004c0100c940e8a1810310b0100304da4003e00740c8a4010180040800d600524202907040200c0e40036103241401c140040d08d018001420f440200005880c800a029201000070340c0e5001d03900410400b9802041782c20341c0a24040c051103001c02c502d11503112403215840303120a80c0254088944440d0307039941c6e151103006003d60350248220b410b0280b40094000980e60056014800c10f54401e0004e0b1b40b098015149140ca503588580160b21020020038094400c00282c43c40706004480549064000d071643c00a40768140c0103a440114005071040307840c03804104080c000c042402061001d13203041c1043c2802030260748501400d11080000401c02c21030210343c00c82c4041c4581c04115143d080200340303600204400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 211482185 1250 211480935 211480949
    0x130302040e03041206021812061f06020a1502070213061505210405011e020c01050106030c05040306050a27020f030c032a1f030b0103020715021e03010609 68
    0xc840310411510000c01150f00343d5160007411841142c1ea552250000d6124113402400082c03d0396810b04541d5031044940070031311040e001800c560510907401d031018190001e03030521034040340504000c207940100e1a0100e2135008020040c030a2100b00e61f0b103001c0c0c46200340080d4442d0084074519002042caa10210540c1d840005280e505001201c003984e240c4a54a100702c0407825030342c0f40744510580101c074144d1162103900041040c80d0b0380c0d84100078010503d01e4075041c80c0e03000700b07481c4058182440b440e03004100d145414444070090b21006000382c0701c0d0780070203013516440c1e000041060b80203401440c0b141500c2c64661300d81c1140b046c4007151000100c80101c0c41007904040c081c0070b80c030b000a400203074040020013904580c44031146000d80d001d0382400803c50300444288541680e41c800150f682803074035211001c0c0070307400c1569008080315501c0e0001c0c0d05061060002c3d10108021400c0d913400c1c40041100107a0324000c07101ca0030002111050030b080f00388000000450225841034001c0102c84035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 211483435 1250 211482185 211482191
    0x201050903070f060216120b280c0509040f0c05030f091f1b180b07020126040c360f0f020c1002040815040312020301080c1008040312020309030c0313030204 69
    0x700d0201e58942050385401a00c8c0c000c1e07483c007040c04003006400010600d0404420a068480c105113001c003030f40d81040000000ca00302059405a504150041c4070b403456080d201040140d840c4007001d801d0740005800c1181c110440000260181410410420150101030150884134181140703003020f007618106850200280303c0c483c4e00110f006030b0042c04c0789090102412b01b498100224883d42d41c10900c1c09a04118088112800b4102c0100c580c014541c49440c60441ea8a09824204102207550780a0f507030f50502c8140d406d8641506010340f03403840d944aa15000c0802c0302c1035409002d090034460215032a840c1441c20001114903900502c403003030342c4034140e8800d5401110b03503000b01d001d00d20941c40c1e00c0d0841c400d030712240c03100051850f600c1031003070030100000c09a07200d040003240c009030424241c5900000c00b2104034a8841306220080c0e0070361420b0070262a0a5400500341103440804505058020010420007802401610403100e40b5100700e03a1581810014014041000c1c4016805140303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 211484685 1250 211483435 211483439
    0xf070506040b07140a0c030e0105040f0308090f030a030e010806220501080624060d11070515060d0809090907350309010503070507020a09021b06060303090d0201050903070f060216 79
    0x141403001d40706007100c036456940b06caa440b91016590070f00074028090421000700b001284030014040c690000c0c6011391000c0e500d4004040070b2040090100000071712991000d40ea100007ea4051040c998040d000c2c030300099161034910120b07050410a50840301c04038a40d1203051401405580814101d5141c4000c035101600c440e800e803802c0354140e42d03881600c841c1540d07a070411401c01100400b00128021400a003aa801030700d400f40d070740c121401c00c9883e500b000b402c044011103002000d98104000b02d62010528035a580c0b500305070711840a40502030a01c8900064052505000b0b07100200ba0104031180742902b00403075800c03030000d074600c02074641c0407800e4803c1d8162030000c140e910710481030710b906145440300c1ea01aa03071a04101c00490b031000b4440700c00310f890856400a010b000c3e401c003031004010150301c580c40b420850300400b068043e0303100740f045101070364038046c9640c41c07241c0a0808998407103406011904040785908281042100c00200040081d0300107110702d40b01c00e0b5142520b810075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 211485935 1250 211484685 211484717
    0x305060a0b09010b09010507110901030c090f020a050306040e07030210020a06051006020d20160801050f0919030c020607050724121d0a0303060603060504020309030706020f070506040b07 82
    0x2c828018071001d85000d01c51a0341a500440007845401e0055a0404401c4100d10004891006c26081140d11541e010800c10000d8840c0c016140c907034415400c1582001c1c10148000c0040c080146524806d54a504110141d0581806400c018580181191501e400d00d1000655a0340301030b10111081458540011140d1110806040948a00c3c1e4040d12076400c0c130030000c035044a0402c00003004940122a02415000d08110f54084c8480719002c510035985082442400c48000034807020080501e21f0800461801c0880c0d00c8004550501241d090b124150070b0481e11800b03d80700080d0045000150300b400e03c00b0000300030049075014201106555050341702500c84182a00d8510040b0b81009480000c400e01c540003106c804030559074180d1403480c54001c251518005035000d07000709503144014402190305014100240c5026581589503050200640d07603640f08460300900103542c01314044a04940346000c403a89207070880c044840717908150400c0302c440074043c2e0b006008101011808440c00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 211487185 1250 211485935 211485949
    0x2c0405010e100b040b09010f020f07120308070e0a210b010902090301061502060a0504030e041b030f02070305040b18090a0b040507090305150709150801031202060f010909110a0305060a0b 82
    0x256920980c0181406c08501c0103407804048500d407070065004035804a0304042d0100000030042040840102d8080c881d401c02074040c00300a01860b0400c0001131041681d501c0d0146d03580c0c225801d0341d41c410340c541c030365021852201840c0c0307c00030204205000005401500c030340140441c13a000700d0003001440d80d034003428800c2070200c405001c00b6030054800034400005035407040364424001e041a411410240c00085d04a03031a00b0030108540d81a04203030004558507200305d80d082c5c1c806210452410040703490141403030040b8440c0d0b144c4071b43c00280420741c08000000031744c01240060110360440c140301051320083d00064803420301541c509000142000d204810f2841100d4000d406001a60060703100e824400c60010966030a0211a06001071000100c1c408018025001d0b030f5118150350551030803021690041154a08540c408420b03c000700c0d001c0311550f411a0403d000004900c8514644140721610015090b07500044a43c000003e000c0c1c00700d0250b20800d8901030400000c29440108220 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 211488435 1250 211487185 211487189
    0x50c031213030f0602071203020a020708060108100e032101060f17070e0103090c060309021c0b07050c070302100314090708060705160209010803070b070207062c0405010e100b04 78
    0x30405081e2001c00204010020309010396000f20301c0540781810b203071540305100e954800d00000196001a403101c0c429414810000901280000707004554548003000e6a602c2c02568064405a61015031601402003003084a585181e0f40c580c51102c01070b15014100d810b48240b040c0000719030110004030455215483c0d050740f01039422043c0c0e40545170948111044903014031414141503990012102092041c1c900c18020601c994020410051900c144007540c0400070421400d0b5020f2612100028035800380503601216501e882c540f14100c161100745481015072020750807246d82e0400c0140d0f06c3e4103802c43c1a1006509d46403c041e03803149441590359501c548100e036000c3d000100802c044a1049005040e01c0e0326030b6507070300031600c9160000f0307401c0202a405140c0907880015088100103140030f446034010302600251100b2403810802034611400200c14205c84c2c3c400d11401c009a08c03000c1d840c1010824064010012980c580f42800c0302018141d0300d44070041c2000000140c80f981041c00c03901 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 211489685 1250 211488435 211488457
    0xc17030105010207060305190911150c030a0c170309071703070201021b12011508011104060e090c0403061e0f0204080712020607140a1a01150c060e030403050c0312 72
    0x40c1354a0301208400500010745400407280310b90b03010b810409094050050068010000139864140c4c41c030812140707011000031114882c0007400000440c000c044140d03000070070b150400d03842c1e0308024940098080b542801c0141060740100a0102c06d51001a03200c054501ea11400003800d07d507460896942e000752880240180c0c07108800740216040b503c8254042180a40882c42d0003d12801d01429034103111012412060756003010414410702340101c02040303618180003032525044c582c0080c000310f003441082e4010b03004c1c080410640403c40c804c4800071504440c1c100700501901443c103654040a202d5003c41c98142009628021307010310840741141c0714000200005071519917041f0a201c0c480d0000d03644100d050082c81d001c00c18007003a02c4c2d1645110703000b900740310f0210b01d460081c43d40c0c246408092840c0034001401440c0841640721000715041c140420a05500c0c54101c014050704200041c41d8000800c00004011000451501c034100880559818004002d00300340d4078040c8018241d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 211490935 1250 211489685 211489693
    0xf07090b0d050a060f060b0d0e01050a11030f06030313121101030606090608060409050102040f0f1a040b0315041d0f010b0604050d050f120c0105150f13060f060c170301050102 77
    0x50300040155108812120540790086031b500d0b620000c44805810424030009403a8448418911200d02886140c2d8482c0380c1c3c03d01080080680c0e044c483c0c050000514030740c1c01e0300c411000305540d640e0420585240f00300f0912102040c503224810300b501d8030880c100c1240c10b900c490a08400325030180c010042036400075541c1c116000c1c503002c000c95501602800070744c0c00654035100e074404914280000c00103031090303030303188105140b8110400403d00000d90082184400d010510700d0514a41d00841b800c030f5003400070b21500d03030b25110381c094940030070441c100d5842480e00d120305029401c03103c880c00340744d5118004c1d1640400503c0240b0309035011500ba51780d00540400080c40b80f0701c0c0007070742c0400140c01075040318100c03a00c1404240c40c00009aa20140314034000c580103c1c002401d000700d41c0d00000d801987c054442018003c0380480e104012480d1088980d003a003000b01c000c6a501c40401804814440701c04aa518240030b00301c1c04c0c1ca0841540d590b100804402005901c00048904031481a4018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 211492185 1250 211490935 211490953
    0x100501031a1c0206040b04080106051e1305070e10030506030c03010b0a03030f0225050a06050c07030b06040b04020301030f03030b09070503040213020d0c0f0e0d0308040b0702030c0f07090b0d05 85
    0x8000603240c2c145040341d00c00014400499400507040250029042a100000c4d072942803004001d2446610301c6a030700d4800c03082e008030610361207024402c03058403446140855503032200c16003034510400740010b50390014030691441020a80c150003d9020b14001e07001d4607401c0224200741800c0e500b023030300a20b81095040d4001c10000303210b9040107080310020710544a54015004088403404030351031952102c0c1030005400c0c000b80c036144904600421050801d9071904c050000e0040e2611460303c00a001800644005000f0fa1070f00e8200701502040100304542d25a140c2c50100030384c0407103000c00d4002030328061001082e404d0030310300c05002d00c000ba00c42d5411a5180da081140b043c01c18209400225020301c1056200c1e18180180440c03040151208000c2000b03e1500604441c004c03c071051040b0b81031100240440d40008080f500039402c000729003c0ca5986d54016407841c0b1034940048480d110f00003000303001c400c02040034005c0d18a1464207010540c91360301084066100d000f00036105400c05865 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 211493435 1250 211492185 211492219
    0xf0c1a100506040e0c25030e01020d0c052104092405030c0102060c0310091103040311030307050403060b0d020a0621020403150902120f010603030206060306090d1412100501031a 78
    0x60f183d01194800d00946e81c0080411818000d0502d001c1180806e25181d820307802036030117119082151140e40303040300c8601c445466041e920442c404194002c3c20b01c4148076034107007002d0000c650250240c0001400300b281c01d1050300d000314040c07801203094109001c2c00403a440c80c01007004054404160700900180d1141c1c0000046076001900c8450b0001c02000001020034a80c040c41c58012400700b41c040c0c5034602400c0140094008601494280d002042008401c903042810382c4c054a030440303400501c20700d000011802001000b10f0203980705c05d05550000e02181c0c03008003030200c00b00201c1d440c004500050810410303030045000007002c641026030b038008016142e0b44101241030000301003260700d0050b00582800c005031410b55200c0390f510f404090084c1601000b41540040041c0e0060410789030075000c154440b680348962108105904d0000c01d096907990f42903d12400204030704120504082b403021124082074480c050100c1d040004034000d564a07051450702100340034207510b540300c2101c09 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 211494685 1250 211493435 211493437
    0x12030203030c0f041d0108010b0409170d11030c04031203090201090501081e04050c120f070302090408040b030108070f1e090c0203160503030106140f04060f0c1a100506040e0c 77
    0x5a0803d242c0010304c0001174041c80071500900da400f00580b00310195041089060a58008901c0940500d00307042c0640b00160090f0318060100c4030200885445c0c03181082404090003444a900980e05408400e000b20740804000400c1102c2c801d0307071400131064400006800356011128082c0c00b2542021081219502842c00c0030740c400c180402010400c450405440400003040e103003526258020016a00a03082003180034a100612a00800c0d0155008245a564809500009024480d4070303011a040203001000d840182076241001ca403250784801600744e40b442c0c10704c10300300e0103c41e0a40010366440020010940e1190f03107080c681a490070001040040c01001c815042188020130482d03758220075610720b6400b6202c1d00245a80354907009008002101441800e266a2001c02c001c0c480000420100c4048507401d0420740a9581140e00550b5100340c5482d01904a0524a9200400c030300c0c001560781c419444140410101c0c1c0d241d0007448400c2c010350040a808800f1100400c2070864040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 211495935 1250 211494685 211494697
    0xa030510020a0c060e0a0303200f0904060509010618060f0203074e0e21010b060c01091b120204180c170f0c06090409030c05070b0c01050112030203030c 67
    0x8180342c0141e80850380c9900494030b04c10140e0011b0f8000c048090700301541802507000c1c248040f984c0c41002400c10300182013910810011110041c1d0004041c0990707162908420300401e0000c19070036281d0394811010b800c1c401070013102c4614605009000c2102801590308015003211036000707505150069640c41c0941549020400310141220840551300c50318000c0041e680a0044005800107034040a0020505200c900441403001e01d56032254a510341e840401f41c3c2d2081d0b100c8441b02d102152551900604111b0703e156042403000407141554030341504908100c0740700f0107c01d00c0441682c0c40c00e00d00c011300c0d405000c03000036044c8480e501620307050300107544d01481d003501c240302240c1c00e07602c585421708164408004504111750b0303514200300501c00391007400b0304440581340e5962160002034181c494031038030724030841d0354000950505100f50b103140040359120045515858031042c2c0c0380300030380010445041560030a400420301c41910b0074030a400e81c0c0d260300154110740b1030f10000d40541c0c00031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 211497185 1250 211495935 211495937
    0x8031b2106040906020406050903010605030c1c0f0203071401020c030c1018080a050a050601080604020906060a030f09060f110903030403030f0528030c05090a06141b1501050a030510020a 82
    0xc0c0f074110041820b1348014002021503849280c0e507428004141429510103034840740c4a504058902c0e40141c68044421021640b1101011000c844925101e44103550f20380000e5094401c5020214482c04410541801e070b100076006c460007044040c0805036549060342400c1c1c5c0114260101f05a0280600407030304d02c840c1121100c1d0005034945074450f1800c6400401510340781d1002e0a62410b0000c20700c60180544a4178000e02040c1c64183c011816494024040a0042c40009908181188a82d120290703400c1c1c0744509200640f42c03810070b0b80241480840c0780f00b640d1314181175501882c858600301e401c00800500514181440c607181500d80c0d00c00314808101303000c4100244184182d1100356451481c00e0318a045031040c4080d68001c1c2203d4054490710144103040240400554412964408903140c41c68000d05107500717480f441455004001d5492a2118014a0408142004203030748020060918040d4850307030342c8030200000c0500b24440604243c200c1c0d81003019040554000381500d8131a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 211498435 1250 211497185 211497191
    0x150e100c02030f1509160303260a0b0f0105040305060c070519030201050a1a010509040c050f0f0304021002010519090c0b07141e250b030408031b210604 67
    0x6140c010a083c000d1601c00c071442a040740c404070450413100b044264002140c0802007180e41c26000240103070445901014050000000406c10303001c3e0041d48400100b4401b0381180e40341d0a080c1c2d801c501803d41c80909030302c41e8012140d410150b5106006442c1280c3e0000c0c010403a60307c8642600c811035100e1802901d0300d00610301e011035078600c00800c030602c8a10950000806103014056182203503020103480045507a00d0880500f1a03a024054841c01f80080342e000504c0759120405941c2c5201708080481c04480c007081c00201036a11102440c886c50007a24403201004e80300344224200c0e4022a4201002c450500b000b4041903015480038494501c208244840d950310788010686a410421086905141030000280d44070b0041c4072004104032851781031103054601c803003280e03203400c40302d0000301d41c0c80402d0102880c0200a004180000c10008040715601e08007402c12007103a5100300c41c28201003114035000c006c007c170040210303054054282004010340071070305100607800b04081c0c0382a5026413 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 211499685 1250 211498435 211498457
    0x31407120512060f09040318090c0c0309090506061e09031603020f030606061b0a0804090606200d12020c0d0e030d022109030a080d06050406150e10 65
    0x205004042128036480d80380c854640b4a603448040d02c12000408042c0a40444402005070f501d070f5801d4140c0050b17040c103041c882040b0030356003400c142d0010307030080c140c150804400d048010f4000c1003e412090190795003070b94071500d4503030060540d4002c2d10b055410400400c144c1040c2001d6011a0502c0c0c081018a02e04e0080c0c00000285059102540c1ca00b4203803200c42d0400440c83c1c400030718503100000f41c000e0001460001c0008a5034003a500f4110980403013280390501d0100706202910416a21058494441d921050035000800d914003a20003c541003842c0d85594103840881c10a100140d400105000041e091040395000b5a03608020001502409481c01062090208401085459440449080075801003600d00054140b00d0030a42d04500c038650406454031030341040100c940100c45d640c82ca50703040400c1c81c0c405451009090080041105940d00e043c03604407000301c0b18201c074248441925100042d49400501c520403011500c00c9294204505240e04a89a08445403c25100e056 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 211500935 1250 211499685 211499693
    0x3160c020d05100b1806010c0320030301090f0501050a03050316030e0915040f090305090904030513030b010602060106050c0d0f05090a030602040905091606050c01021b0105090f010b0d031407 84
    0x3041c58800119000e403100c44c0c41c1c403d810214404103001080040b4101e8038103080001078040c107000007000c2d00700714070180318460701094031150b008003a003070000312a83da603076a1011800400d050002d80207440d08000000481d4038012141c64183c81d04213015510305580c0034001c0000131610f000c2241130101d000b8000b5407641d0303201d80644c07144225030807041e0b00d84048000c1004070340070800d405180504d416007480c0403990080940d07150803819101c03090740b6250340c101030f5030500034610ba0700c5c0c00081504001c020444000ca4003412245244c00302c03002a41c0310302c2d09942e94050080c5c508042d80c0b00e1014812104d11900d01c01c0607840641c106145802c85083c0071410003400c1e5002a40d07841d40015080051480c00d10a29038030201841c040c04030704048126080031072002d0b11803142040000b00b07490030505400e604845804000030480b100750b518000c0d0045c00fa1200f105d80703035014080e040107000c0400040c01240c0d0400d0300205543d01094060390141c4c1c1c1351342c040044050401040c4660380c002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 211502185 1250 211500935 211500943
    0x50c0c120706052a0f010f060f03020405190c02070906050904080a05090a03051023090a0803091f1b0c050715021501030305131a1605101a0a060503160c020d05 70
    0x484c44102c003501500340040704550a54150b004174519003494501e04200304001c0b10138480942ea81100d001ca81612401c10215030500c8a20603c1d0580d0300c0c290b072107074416070001012402c49000300c1061001603514010401521811500544221020411440810b2094008100302e200c02081200015200d0315454681200003490359503181c3e81e4550344201c0007403800c0a040c103002c02c0c03400260b1450140591070702c41c8001f40c1c0080132500c01201240c0c01000901030a20018003d00e0f403e111011505190800ba00d580005c0c2042060b0155800400521988003502050f801800030050240742c545103541c802d00f10000c0320218083e000f640c148048101a07424001d500980c0c0d80e588404140c08103091000741035106480200000040584000c0c42d08240e40d10018400c1c8052001501800c2c51400c11070039841c01c046440c0382071815450003981c0341c0c090344464000e89010910356220f042c25586803105036000d540c0c00504046030496248940c284028040c4040d003c0102c42a00d540d5043c030f4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 211503435 1250 211502185 211502257
    0x20702181602010f1b081909050c090601031a1005040e0a0e0c01020313060804020f090906040b0a2915030109021c050c1602040b030d050c0c12070605 66
    0x30301c0c035041c8046041c0d07941c24000e0262100c608001001407500c40b9202245041c10a1010014045a140092003060151492004046280d10309004004051812a03150800c14a182c2c0c4100072460200369154420b02c1480240131982403200c80c00d000a00400c5000003600850b2000c200040102003608200054054003a41480d8400301d100f411140040341005e46010b003450441d4400d01510304d465142d064840221811828400300c5615140040351401c0350080d82e25402100a40902c541c40f28000b230b94911a45c0512118007a41d01c1e1181e10205a032404071030344458061490380421840ea00c6000c0402c1648010202c80500010508030017140c1c100f41c0c011198180e010400c8115003c0d12001091601c10b580800c01c40e034609408c440300c0c02c0c090080d01c200c00754400b01e07001c011912280e00004880304024126540c420346035100800131340c01401c00344064056800c60312460700300b200c1040c140e18420b0016240c0c8500300102125640c000584681681c4900a846501442d10b10a0004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 211504685 1250 211503435 211503451
    0xb040618030312271b0e040c03060c180b030610050f0403030e0f0d1a16050f07021813060b040911060f1303030f03140114060d06030503030c040312051c02070218 71
    0x513800d030040c940d490090217070760701c100c400391030721403c020005110180b07440a80c0e501010019281d81c20090894842e0304c207081847c075252154001042c1d010400e8041c52050078121018407854044850032202070080500d4140e03000c4040c0070504c0024044c0802440d88040a4880c80801891000040070002a644282e07900c0c941702400130040c421030364040c0d501941c6030301500c3c401900301a00401c507104440748462105004181c40c0c0455407010072401511401103030b0b601003400c0540644585022001d000c4030300b41d00d8447d2000381400d041c01145461500441078150015201042c06440e0b400002000315030750b0200010009a0840e85042c40698084d0742c0e1035001460620004c2c2c1150010034400c8541001c03000100307c2d2030414181901001d4043da0400d8480e03451094660142c2810340000f4501d001c0401041451b00c00c06015200700d034019401054205010002590355101d101c01d09407400300d00420000c1c024019800821213544060008640c3c090450140d4007110400d80e8005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 211505935 1250 211504685 211504703
    0x40512032203211d01050702030106080f07081204030209061c030309030e09090a080a090305060c0a0e01090b03150a1701140105010906080f0702030c06010b04061803031227 76
    0x40103121402804008108032055400c1c01c4800c051000b4007090141d0130b2041000c0d2400a10180a0b4856030030b851103c0e41c0640280b20407921038010545649007054084524481c40c00005990072b0001503c20100300203420701c2e4507143c19a02400400e0800404142e0005140507075079014050410300b03024844e01aa0300010409010710f4000c0000c0c1003141514401c2011b1000e20094840109101020560180200c3e68a080e64203051311450469440980540505c9080000d5800c1c1500146020b00131031f41c45142e5494414010b40706003146004078040160180700141200075103071180090660300a2001511580d070703078114000b0110390035058034182d465840700310b42643c140111502600003420000c402c01d00f4118010304c001c1d0010b20086022107075901080c0c01c0f41c02801250b41e1040c40e00300340c0700b1035030316101c0c4548240d2003841441e0004a203104e40d810f607401800301010580b94155100c0017100455940000038202c40314178218040d007045188a5510307400110000c44a1007400c810b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 211507185 1250 211505935 211505939
    0x3020103060506090310200d060e060d0b0a090807060c030c0923010302090f0904031806020d05030103080a020c030d0309020a14010c0210142b110405120322 69
    0x102581c0181d0700c010b00600090010032401c0e0b4012400c8002801030791030019083c0b40c03e481c203003210400c00104890325540028156008013091f040541924450000400144c58500c01d0007154400c20708083c012750100c20109500440c00e401400c01329004001084c01c0100f144c60b00300c00ca9100001d03200c0800d0f036807402803007459001000c100007840e40c150b684002045440001c0440303041044940d04050f80000c0044282d69640a003400c031000c06006400186080d1070003510500c1440c640d0f5225450590001070b00b240b0015800d00e40c2502c650ba001d04591071540c4070700d42500011200000e5008410b41e0a4180d14100a0300d2a008043c1c4c0d80410301117400d005001c01c2d880b150b040381e205c4400628074000f040c0d130400b010071b01c900d0f0305031480c1448000f03c00080302c0e03900f142800d800560741c00058150620020200d004408480e00c18202da40c00c44108401c2c085900c07025040350011414082049585010020040c0903031810040d645404040c91001e4000b548200803041c0c1d45441e10341c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 211508435 1250 211507185 211507187
    0x1201090c1b0203060a0b04150e0105090c04050f010e010224061c051506190806061008040c0306020307140d06061b03080105091302100e041a180603030c0a0b01030201 73
    0x3060902442524001001e04607801080d00c0f0540244543e1100303803124107001e00c58480b680b100c0072060303450001d49041e07511150031080d080000c1c400c0601c1109008003056004401d001201c045800080501186c110784a00546005010034001810747c0500505641964901541c15031555a1420040d03180c0c9005410806c80000b04645c10548070340c180031850000d42d0000e0403040c8030216030001c6ca19640c649000400d4030508043c01c103084260464001031950b00050018018a4119444140b0b00c114080488000308201c40151600c50106010404207400f50300441c0c01a800d4906502d859000076004140c1c3ea118507841181d00c0d42d29407040280d550702c08002200b4080ba041c000749950784a407001400d055040c0070300d510031901100410a0036000b6105150140c5d8058044003d091107104003030810221808910301590500c0010701c0c0c2c200c910070880702c1f618030080001301030051124030304445202c0104159050701c01009000c141100070805d00c00c3d03076072080312911640e40c15440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 211509685 1250 211508435 211508447
    0x601030201141210031b08030405130615121a0906041d0f15010e01180b0303090d030503061801081509190c15050f2209020409090b01080307020306011a1201090c 71
    0x1b010040603221010500c1031503404012a03048440860300d5a044170700b00080c0000414059200000050148a031034032100e17007112210281c0c1001c8a03042250205807208081e02010910174154082181070019540b032800303620044c45c0f030000c0800f14000802a9020303614100e003520b1144c1c0c10303030b00105503031074001c480468250241c1071351082901c05514059203007109045030074100e000e050b00c0328000942030b1010426124015001440189480035600b409003990f4000c4d030700325009940c0d41600042d02c1074400b060f03604030b4090300e0013004882e0181d0060600a04040e0800009008450103c14000e200300400303054240070b8000d070703505c65203400e0001e610782c1c410040040c00d106082c0440100c041d4481c003a100704648602a44820350440c200110100140341c200340d881c1031001c100071038060800e03481003606d91b200c0c4000c02e070303142d8035103540ad0307524003600c8002075142d03000c04018429044915014002808011556410615503007580c01221100f60400e5a4541c0c1d01c0c10081542c0e0b40c13082c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 211510791 1106 211509685 211509713
    0x3020f030f0d0e0705011202180909030310090504030206010e091c120c080103020a14030a05010c031a0f010c030f09030c18060501050c060103020114121003 69
    0x205560340004044041039490194200044003002901e90180c40c01611070b0304040c7d0700b032446903000c2c0d4040d51500e2880d080c0c841d4aa09a5190708841901600282c40a180c5a15180002c40f5180302240d02904040d07080400f030101207900131034114151039049400c1611903680a080c1807501003c03003041e013000400c0341403111156501071480e5203d02445041807098400800044503185028000654411100d9008104806030b45548814000000d07050b61a12206a11840d007100d86411114010039181c80c2545089041e1a0082c940d031001240c10f54610344240d40020500400300f2801814030001a90480406015030444001507a11061081042d03031903e00038000c01d100c604011030541e081903400f203025801201520308580034a0001c02c003680c650b40044488110381284180b0a09040204081001d01c80e00e19501c206040700144514034070354600403036114800 = true := by decide +kernel

theorem cover : BRFrame.Cov 211330935 211510791 := by
  have h0 := BRFrame.cov_init 211330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 211330935 ≤ n) (h2 : n < 211510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
