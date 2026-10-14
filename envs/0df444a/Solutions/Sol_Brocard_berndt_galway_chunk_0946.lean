-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0946
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:20:21.586141+00:00
-- url     : https://prove2.me/submissions/80698033-5e65-45a7-96f2-a41917918701

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 169964028 ≤ n < 170143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 169965278 1250 169964028 169964071
    0x71a070312020a0e09011d0609092506030c02060412050a0c0c0603020403030e04050906181e01050f091606121d0604030801080a03081602070f0b040504060b0f03 71
    0x1c2044041c6801c0c10955588210181c002c0c28940b0b4018224400c0403080000704010a2074490388042c0585203569405940714001004007110000f0850b940070b2103030709030b5401ca600e403039103070508107041c4c14420000355420700710040d007a01d52031030a207000c55020808200100da4561240700c941d40880c1071003561456001c03811660b074580c010025280140031200040c01c01d5142d0300600c201d9020b9a102d4801510310420441903a03015100002d10b90700c0300c0e0205600381c03000844110241d00100440304685803520003a00c8811500e040301005035500c40801103030350031099103194420712020240c01510300d01030819641d03000c02d0040108200c0d00b4001c075180d03452242c2c44810138521412004480c3d04007902115a00e507401c60b0304500088203000001640040002c0f810f081c0d95040e2520038555540c881d170380410441a10007501144030b1000006540070304021a00701600c0490155543c4070304040502040da00aa4080c6035898810421804400e11800c10350780c202c0d0b840c560500300741d40c214 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 169966528 1250 169965278 169965287
    0xc0f01170907030b0106050c0307140102092706010c020d060c0c14010f0b010e150f0f07230c0a0501050306010c060515041802060412081e1b071a0703 66
    0x50400052400c020038440c000d44002039000c00c4038802c0008545503a02d41c903084800d40514102020b1917403082c01180002815482d00c0040b031000c1d24001070400d6102d000162070582c41c00942a100582c40c00c03c079080140326410250710940a0904121350095a13001c14185102182c000d03290950f51100b207580c09220300d8681c04025002080d0782028001c10b000c860003080c400f03071512411480c1020000c1194010990fa0818410040c2003004082c1072140c0d00c142a8071100d13440c03034080801c110100360101c80c90007804016020728000702e18500c804204000e002000c849201e00d56014680071160781c1e58441c015000e42e2070a1a200d40c480c0c81d00c00045ea18008050340c0180164180f0f0100002d0010b48201200c1841080710f0501050240e191482100d06403a0300c0a90494030812042c0304019141d08150300da148501d044518001981001d40c039694141c4100c3c00302c1e40000505036132145000c81d884aaa20f4034680500b0b0028a44100d03220328001040d444201e48a02050080916009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 169967778 1250 169966528 169966547
    0x1020d11090f0d0305030109020f0d0609140109050906160c020301050103050105060a06180b0a0c15021c02190f05120c0d0c1b11060702060d09060c030e0c0f01 70
    0x1025010321200a80c81680203041d009030051600981e80c49820303585601e41000041011505a2900361a42e402c1c0100140a54000a224103200c001000100280d80d01c0e84200d01c0184940f807000144810031405440300404180e102c0a5918101024405c0e078171008160541c0019030f02c40b154086102d6004141c07000b0382030b4240a5455480c1100004c00d02c1300641003d4401c0e4001c0b1031a642c450385034882542d000f01074001c13071840807054020a00001c0c0d0000000c0002c0c09990411905041d010ba40307000c0e06546407568800507940200d903d0080c0c05d03550300b28090070b41c0000700c15400d01402e020790a02c886841d1a1550800c5004841924a540607804031503001103051f0410299162000041026520200706586c0c00c0d440e051100452511805601030000c241859042103d4003a4840507001d4103407049907603001900308203080050742d54070002c1060701d81c00c25002c01c00704001e00b444411280e202d0403000605040544601c409000450500302980040300c00c210359807114030048418660 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 169969028 1250 169967778 169967797
    0x15040b0a09022a03070b13020616060b011d0607030e01030b0307080c0f0916080c130608041208010501022a06040b1308431409010807120b090102 64
    0x30005080303618180080f0030716440c4a60f00480d0100d0103050b03a407290b032072141440c00b40280d0b41c0d10011481c00340040c0c0a40d40341c03d000400d080d003010100c64080b5031039000d03204200c440b143e580355144810350700110f601c81004608540b0709138805115001c19098456000010704006414440004603800782e800308008010150031610300750346840441d03507511806400503108180d2400074450614000e0078840c03051a201301d02003864043c0f100d0544045001034800c0c3c201c3d100c1440078500004c030902d10407005010036a16040ae42c102070410b0303020302d00c0e40036484080241c3c04006000d42d0760002500c2d0b4826603a82c0095207102503007400782803442e5490000951101d0b0000c4c00050f240c3d20100640001200b100c80160140d03940c114482d41c2e0152030000c2c010011701c140383d0301c08241306000740301ca400011100c1c0340380000b00307103015120098139a0001d900b0007001201c1d1004d28144050050301400700d030301c014070715241408141003214940e0980205070f81514400510f0103802034040e07904085 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 169970278 1250 169969028 169969031
    0x150903041824092f09060c120a0c11010809060106120e0d0e18090703030e01030e0a1407060e060708090a0b040f0315051b0a0c080714060f15040b0a09 66
    0x5844600746005001c4207a01c405000c450614406525484c4819a400c01030255151903d440212014080c880e0070020700b105541c040c52245e440e0700401c50008240b403034196075410484090520700410322940050405040103610010000c0705880054042d065032154140344074a034980300d62010240070880fa0440c40c030f000c2c02c40360103051900207105200c4007608a1b0704407202c6c9500442d07180084012640d80505501580741000405d000b01c28001d01c104040c540401e01a030302c1c09006203000e00b04a0115400f4081c4c182101030040b080c4110b201402041c0380c0700450180c00c100040840c058550003500b281400620b522840d03840400c3c19005040214030280c03500d507a01e01c03a080c00401c40c881602c5004035104400d443c21014454984140d071000b00303026800360031400d4801280c00070402c900602c94942e440f9030109901d10094a82544584844400a486201154200b03000500b201c60900e038400309001c03c443c1ca0840b850500301085d280000c08000031000208401750a601c108403d5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 169971528 1250 169970278 169970351
    0xb15040b0405030f0a1104051305010e07031106040608160507210212030402100c0c0911130608190218220c052a010e010e1509030418 59
    0xa2200507108031141101070f510b0001094400d1601c582d448840188849170052000d02e0070718041e44002c1d0403554911284508040130303502d00d400c442c50300084501e65800780745c0c00c0040004024000e0300c14602526502e003071a1030300f08090458603015000292000080c401850054030400540d421290029078450074500e1151012100940355880e0324014010200118400403452048a00841c1c4c007a0400e01038079405202210808124207048400b40904000019084d00ca0b025142c8a1b01000088540d503641c40309065a20882940c0114140098582000050078680451881515880300056070390380c1c1985c14000700c81440d915080c0e01c41014400d0b01c1000060091f03102a210005400b000070024090b17040c0e8003801a14580041900c0e0700042c98280102032048008401420b4008074641842c8041035003580c0c0403840d003070010390285041550700c8408040040c0c110742c803140a03510b800d00780b45680c021040303c040c00c501e2003a100c107504007960b06107078840c444040c261902e40200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 169972778 1250 169971528 169971539
    0x503090301022205060304110f130e0106090b030c100f0c0204050412110c06031f05041107021309030f0305090a050d02100c020309211015061d0306010501030b1504 72
    0xc20000c1c00f02444508002c407010a590401d0400c603801240c1200d14900c0240d60340e8200303c5455641a143e80d0001002011800c1101603030082d450071013a400000700705241014007070400c507064590141e00c2584900300c8810540c8450400104040c01d80c64416180c181d1a41d081d5421402da1600a401070718050410080c060400d0301c41001402c2ca54a6030028417a000703c80380e0b140d02e40c071301036548200100081091410707407d040c0c200703801d4803100038580981e84c3c3e400203003180c03003c4010b800040400641c031011803918034144a2070002a1000b0000d515003605c004040208030305000082c180c1d9400418084e085c1080071000142c0e010040300d40f03c8040590007502c0d405102d003000d07241400c10f200c2481c02400481500c003c101c0c0900044c038901c41509000601d03004140510741903028500211400d81410b0040c10100050115120201d40c9400001440104000150f180c20406544c2c000180e0b0341c00705100c0d046400901c0e000c61400d000c1400605c41d43c2e003c10300c190720301c100050009034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 169974028 1250 169972778 169972807
    0x1104110705030304030815030307170a0c0501050a02030703060602070605030103020f0d050f010e010501050a030b13140a0804140406030803150f0d03031d03130612091211060606091507050309030102 87
    0x8146040750803580408021f02c18591381e40940e80c2d005114101219880c0540800701c805000d0394013071482c001c4c0210340345d03407151804c44d1003d941d004c03d0340303800100700700c099900340c02a00014000341c03004040492030003000410038041800000e100b40c3c41c02d4110b110550365441c0607001c141d04242540c1000c0c0c1d0340140b0f58003e02c81950348101035401e003000010700c0e1610b0307403d6038101c0350025810561036841908140d0502a4103000f11107400301c5040c083d602d86000c101e03d030710703184c401c0c00c440da500e508002c5064000080742802900c1203080c0342c3d003480000c04101c152a00682c0f00c03e0300c241181c40a400003220160600702d003a0304024103280c000300341640760300708448025208907109150400d0350000ca40303900c42c240ea14440c01c01400410024107105c0c1405c4213903060002d0700002c013900180c1e13882e10040c3c4200c20708400107060101e00c1140303040500520f07410410131217003580741106020124049415000b20504203a2012a950040c40028000c4440c81c850080086580e02c0e404e41c580349 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 169975278 1250 169974028 169974031
    0xa060201020d0f060807030215070b10030506090106050f01260a020702130b030c06131e061701030c0b0c0a021201050405060703090f062a110f0a11041107050303040308 74
    0x5550701e05100350070031000003500c25403080c0ca00d0200a002047d0450f003d0050700082c0542074070825204010300c50110304030fa540103010781c0c01d540780349100301c2c030b517042c6185800300252401b101a4074002040180b80d4920200c0d41c420542801c00e42c10035146d424180c14105002d5103085d021740001c10400400714a0766000f0410548219100c030180c4104076030380008c48015046664050380501c650320600d251801c0a00b80d080400440780070300036101c0c42500001c200b00300b000c2c40c5200300243d040c0190340d0082c60365142003164644c550300941c035540301c5600216042c4501d0780d55400000354407a4900080c0580a58150041c0c050120341c002915940e0080404540c2079503c0d0040340c0c00700c1c3d1003e100e4000c0085250300504040480544d41c0c4a40d0f004201295a5417111601c506078600c11009500103092198100c0c0c80300c100307900900d906e150403d0801110729009822103d1083e0005000001681d20003c00b0340340020701d003184411a510b1845503150190662102100300004c040e80701c240c0a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 169976528 1250 169975278 169975297
    0x150601020111030c03060d0c12031e0f020a02040e07050301061d0705121b0c1c090f0e0a110f0409050910060e07031a041514010f020d0e040b0a06020102 67
    0x20003001c680782c60708104500040d11075058010f010000302e4110f00d4220002c40c0200d0040710554920386d590703116140007d106407800c4001c00c4652602845042c1c00007008001000141882d04400c810104001d44840854000910440d07884400c051030080810055000d040e0190080100c280c8074181e42c940c400080704040007240380c10b07001805942c0304605172165032003104c050a4580d00c0311490324a0b1070182c0601500c101c0018054034055134070810450320b12100c0c030905101014013014008191030303065005040710380c0484204001d102d5500b4400750f40301a66020010b02e40c4100041140715101c0c001c0460140000810041358000c081d0b407140d4041d01140084a0000c00c884001d4800c3e1101c80c07241d00700d040e0340c2d800011010750281d049034484110030390110780c0700141040040c00700ca10318111603407034a15850080c407004a03090880d413340c034000d0914442c1000c02c0c2000030758030015007664200f04031070320303040040d9502d031034112201e001c034020281c1a01d03540301e0034002e0007508018100d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 169977778 1250 169976528 169976531
    0xe0601080d050406020709020705120a0503090c04020c0a0204091a010b041e050109180f020c1f05151207081002030f06040902100309080405030303090a02090c0a2f1506010201 77
    0xa81c55424007540440b821501c43d81c000e41105480c01000d1002504640e505603030b00c5c01040c2008a03808503030001400503001b50307103a20b13841341810003185142880125840d80624410400c440d05a540000d080303606540c1103c0101d4100b0517441c04a5031f20880c4c00d14000120042e0740049107112441c0e024100b45e840040e0380e0101038409690101414005d840340501103481c198040c04a024540300d60b481000c5180008100c000e40c01a8100c102c2e03104801459894000640f51107100380c02d80349d00054400c0200d0180503606107009154100303030306280708500c50b110548510307030b1201081c00082c004080c81ea00b591002824155040040c2d40f08448648903041180c000800f580350911620200d01e1b00a0300001d079040c990b42e4198020000707807000360b50389034083c000014641d408000a51140c4400c4002e000140400c0c130511802c1e090180481420f240113100c0d04c2c1c42a54401030090380113144140240101c0b00e00e04212a403109600d80e058442c1c00381d4003a0101c00615454007600a00c0c0a900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 169979028 1250 169977778 169977793
    0x60203031b1209010c17131709121b0409020f04020a021507080402120604030801030312020702060c030909010b071208070c060c08090d112505030312101d130606090e060108 76
    0x107500c00b1400007241e070000c07d50054980c0101060340303101e1205a01541000c9030b8a803401900000b500d00702280c3d9001c3c0355900545900f075520400c1c8403440d104400584042c0400c1505500045042e44501d0a207800f9030f0340032034029a01c5101b0424030103601d0715101c00c51715605000c14000e000700700071202640591a480900e920691000804034802d5030540e4035004240d08580d01222400010800810400d03028001100540da0f0781c1c008201031140309000719038854500c814010b00e80320583c4a146030b40414006074003c10010052400003409174607104080b0b6649510954000d141d82001414803442c141e0f601d0744840e00003c8050003011520200e07002d00020403822904070400e079480b03100c10341114000c0404049841c0741c82e20380740080d0b0806022640c481020074610f41003003200c0d00c05c40d841c09041c0031405004082d81c0d00942100c071144000706009042080b00e54170098214103000000900401c1400b06c198850310160110250030b009090040d41202c2c1c0d260700078055034101e401000b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 169980278 1250 169979028 169979057
    0x40317040e0f0601031d010e0706020a120c061e1d010209010504060c11040c090f05010c021008061906020d08060405060d0b04030c1e1b060203031b1209010c 69
    0x10603201201c011a10003800780d07540c0c5440d07400e000c00140405061540ba12a941c0c00b003174401005143d0000307071400008100e4024071000345011b43d142d1024083d17400c43c0d0104404901d220290809600301401c3c034000101d2a1b1170814014680b644403212444801603503200c1003180f9801c0b201d812070310320395400c070b00e880d825510b24200d2040d0784003e40071807000c0008000c61070240300000f15050160058500381c5000001140564200071103810000f804860148011a071203003074900948002e1030450321154695011074203104000c801c68040c80746280014005650b0700403402d528504501080341300e569201d001075a1100071040c21008039020b580014400d0401d403284038880c01c0014803011680900381c6400362033180141044e820024403407035080109101440e1450314049103e1640324064a40c00d00c2c0b408102d4203406001c8003013203040308101d1603a001042d6500a0010250b00ba80801c5c5081d031244140b1880076043e203011428001c100c17000d1300641c0a000b4959880d00d5610f02d4110300c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 169981528 1250 169980278 169980323
    0xe03100b0f04110d0c050d050906090706020c0105030118151e14100503040302160e010e09030705070b0a02030d0609050103060e06010b18040204091b020d020c0f130612080403 77
    0x1004541c2c00b66001d124906580d40c4e01d40007079074404140d0618900c2d204280a500041c0ca1044843e0302c00c581c40780040c820801c00410010f40100100d00c0903001c0c00c6000d0000030b00c184010f20423030380d030b0440003041e036011400703558400c210700001654050000d640e1806294803c402004e0050f0405124080004030032081882c46045141c006080045c038005498044d41c007034101030001d5045118241c28101c0c060034070103400d00542042c070b02c110399541c902039841600040003424010580c0050250100140340012100291002c0354589a200d25510b482240b071400791441c080c800e1804d02d440007906420075800103040e0b03070240354103215000400340700c195101c10a00c80c5a52401d010094490540c0704502794044420b00100050b00c4d10b56507040e04070a403a400800c01000c5600301414482c1c40e50100700b61040d401340d50010b0f04040f00100005084c600c42d00304028010a00d80200716a82e4089034000406000444502c88520b110303820071121541280c00100c9400400005590001819 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 169982778 1250 169981528 169981541
    0x50a0e07120803040f020a08030405040513030f0c11060f18010f050a030f090c0303030b0306071107030f17040605070c0b0301030c120501090501050106020f1c1e0e03100b0f04 77
    0x140c89101e01044500d96840d01c03540e20081c02a641004101c80f500010b9407141c03200c400801c1608003d43e11241440208801c0b138034040c0a0040d2184410600d03c0060741210811980d924a401d00e204607050702e08040480d00400d030310751a1b20000008cc0b6101c0701d01104003400c0c0054104804a50804041c401980e6a41040d0024000301d03170144003010000f41b0a03009014051040f1401054003202c655404c0d502024981046000ca41c44240d41c0c1e004c0d05040281326401a00303132500c200b0040c001901c090f210525400064000c0c00d0008049080c0403005260b071324000702100b50703613a40b13a5440f5001800c0d9001080200c5542c2403818002070f048824500341ea06a9410a004250041c5040441040013005500403038265496140c0340c0c000c18028072890b8028100c40d0050800343c01038244a078103051856a144400c14003010081601c568880341401070702c8441c10900320001c3d1007010660b109090010382c03030b030b2510804800c920400440d8010100b104025940504540711003400c00098502 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 169984028 1250 169982778 169982789
    0x150905060d06050a240e0c0d02070c03060b100806060d02090f0306010f0302011112040b0702041b030b04060b0c030406030504141b0918120d02070219080c090c070b071e03050a0e07 79
    0x103c0d140403c90122a0380000c108d03d00c010003005280c4942c41e9102e5018081a500a03a80710755510820516807c00c402c2c03a1071010f12901d4049920315040d40064910301941c0da0f0744a00303a901082075906070b111510940080e44005007181e08642e0340e4038988081d83e5043c00f049000400080100c02d110000050107000d6051445003d41000d003424030b00760440d005490141d80c0070b511000401818000c8101c040e000c10030540d8086100030240d0300780025104198041c41c9032080411012401e14408002d450586400c1c8c130b0046142d407500c0c100544484098546000503008042944c0000040c516012031400010780302c42080e6540c010701c005950761403010ba6803242d00f010030441c4240b138108005100f101194040141000d100341c007c500350703080c60020110840c03070742481448000010008440c0c140c4044035070300700d6860149041c092500410b000189101c00c1c400100b4603603401802128150b07030301483c2e61103c180800400a02800040e07030001030152601d04a00e040c01c0c1e0102d1088151072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 169985278 1250 169984028 169984049
    0x309030301030b1302040c03051501020c01080a09020109150306090b0f09130510060e01030c050f010212090301060b070f1104050c0f0d0f0c17070201150905060d06050a24 75
    0x70700c0c40d200d000384914010710140c0f0020502e5034444c0181c5d1144200015003c640ea40056949000d20040525125103010b8505640c070490040580f82c1e8018091680051038080100d48072000d440140ca04400c00d4000700366055140d12007481c0d1641c10341c041c03000c44880c40d500340024031203401449084a03414020319040218000004c0c07189140f03030b080e0884180315804035000002c4c02d00c50075084a0480e02f14039014040c2c10010030034084d06020000140c1300440d00540c825000c480042c0da50308030078205c041042c4001c100554031759020741c03100004000e902002c4c0c2d590341c82464181d02c82002c0e00d000729618401c0c00021030850505104061040c1c550911076441d104540100c8402d981140b00240c506c1626003840d00914000e40c0115030b050000c40d02c400151401001d481d13200001700400c0c4100f16850140a10100c0d0441e03907420085178461000081d9685070790700465003080c81560040c101c141401c080c003111a0960f0b12103040c00c0b411a001f00410401d50383e50f41540703032a921a148910 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 169986528 1250 169985278 169985281
    0xf050a031202070b070c020f030318090603030f040e180a0c1d070207050f030304031712071707030c0c06060b040503210702010503090f0a03080f06060a020706122003060a0b03090303 80
    0x2038007400d0703068031a1f40018413508003010203c0010746158401c4080c40c910846506081e00c1c6400c0445569801606c114040e5003082110340064000d80540d01c100088821528089000019202030003000400190b00b43c42c030034800c901300106948400d00c25804032145000711144d41c40c05801040d4003440055015124481c68401000b0b454103507080c1103949800104000400502e8004a8194504028204a89401040d00c03130003008a0024800c905000804138180c0018509044595001c0c0d05414001950413119504889001002c0e1004041d540342c0400802c0102c1e450f00503004417901101110380a619002c1070410f0884285c100c910504001c0c05204015801040a198441e900904407407200380ca0080182c0307882007055054000c00e81030020711012a44401d0602e501207001e42d103492821803d224001d554042c5407084030100003040242d461903044c950803c0e0080030204441c41240e0465040244503a40244d8007030b4821304880340300003034040305841920f200340102005107003507 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 169987778 1250 169986528 169986541
    0x70f031503060f0f0f0605010e0303030405121608030709090b030c01090e0606161a16050d0905010b03070f05040501060e06040b0706060914060918100f090f050a031202070b 76
    0x140c0945600f030319005840781c1c60358049011501c01d40d581502c44002c04142145080c00140c9001140040240603030410400c20020480000d0030700304c107040d4078540d50340c0da075003019942e0721445aa020007030001d80300000b880521540440a0415180ba4010800c0090b00d0070080650b5555551052030101d00000801c101d554000c883d0298000c40140003140303003124007240b0011b81d68403800121540002050307064184d0340e04a01242c0e10180070582c2e20302c44040c010f4058410301401510b07480e07541c0c0724140c100c1004400e41000c034000c840038089401050301e80b0402e00c0704c9000b6003c3d050141d49000000107605108200c071155461018251520b0581020b00403001948010410f80d0071980380d950008120f0040e1154042c25002e10942120310704088042040702d882c09005191905054000c0d43c034160004901c2a580005019000504226815170000a49140340780508542456048101070100106114155034880c2d0b45080c5a0314059002004074061300002a0848614070005040d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 169989028 1250 169987778 169987781
    0x1b0c130515190f0b03011706040206160c08073201052205090106050711030c0913260a0f21050c16050d030b0111031801050c01050906070f03150306 65
    0x11140c1e01c050b1410a0582c6039081000c081c0034a0f413120680d40000070040103403555503003940a21402c0c94004d001242400c0e00040c406008110384031120b0007105298030300300101d03441204001e03c1c2010507030307250319512010303001170614852104c0303202d4070041c1c020801d0040382100c10b0a0b251050311124204121203040d490703225041c030341e40c9103219611100817a0550307030301ca42d01d4024801c41d62819035944d0f80f032610813811500010058041d07404505c5502296071340024140c1d001104034584081c1c1a21810058000d4808101542d058001f0000414001c2c08074401004032010a84400c020f092499404075a6040400c1c031100d001c2030594184000254a900b015400400140e18142810843c0402c0c0100740f117200c1080318980c0c4284110003a80e81c040c021403824000909207402e68024002e00191a445103c0c9000480c1031084111302c0d01e68007440503504000e0340e8400810080c40c29000503030743c070074003500c0000100d490035210015041c4203001700629808400d071012441445d41e9100c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 169990278 1250 169989028 169989049
    0x61e0801030218130c0e04060b0303090907030b0406120503030406060501020616080408121302032104090e01110a020703060501051c151107210309050703080f1b0c130515 75
    0xa480c4d003c00440d9102040c1c10408450241001541d002c3c0c0c54100f5140000845a0920a840c0a0340085c050341c40a55544c03000b01e5481130090030040355940120000400508031500000c2003556640d4210040c0b100000c09140b0940c4100c0c42003100c01e488200680c0e407524104e6441c035445400307560520381a0300c5100c50075002440ba100c074a04100010452502e040c078202c03079845600100d03c808005602c5c040016030802410715400d118061908030700c140c4544118003c140144e911141e6500c0b60b000300754040c1c3c030300724049408903031610815034000792629481c0c4000c0d198107040c5000840c4519002c01e2a031007035400d019446260700340558400203180807903100124140e980da10803c0c205c6e00c3d00f0707004090141c401e40b1020703a6541c5805081c88009072140202040518018000b0001080080c0322010f590f0080d01b0203450300d80f00c4406059a10403e03800c240c5440e140303e140d090404000480389030354001218035001100c40b0400704030854100300c1e204a0035140f050741c40c0b035071810510f1106 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 169991528 1250 169990278 169990291
    0x100e010308070807060f24090b13110c030a05040f0e01050d02010c0c05190906210308090a08120405010c0305090c010c0503040f06050301050102071a042d061e0801030218 75
    0x4160121700040361b6040381c50320394140a646420041c400794000b5000d501c10040e16020000708103240d41344020403580c0540d880010012030391881881b407070040c420199505002c00e101100d60b661500080101660014450b00001600340040803e007901900d41042c107840001d001c0f00740c00603041d001100c514040f980162041140c090011440d6101c2495614440346450130a4485500e0081418101c2e00141c0c0400d501084408901c0c40c0e88070081400d4800ca034061409290b40e85035250b4660030308503000001005200e0020b03007010030701c00581880d4460b90240c0020080803185150a4003074880490b580d41081d04600b040260640c0030b04035a0310803600600860b8205510b03071018291003101500050042030300032004000e19a81044103030080d102c9050a003048086251829545000301c3c001e1003403a50041c1c030001401600c8141c94a150444103004074007040e0b442002404400d101c281c07840d108072000640d045002d00412541d0f041325809040400800e00700352183c514000041d200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 169992778 1250 169991528 169991531
    0x7030216060c030506031006140111100e0721020a0509150303070b040506010f030302120d09061503350309010e0706170709030b060d0201020106091103100e01030807080706 76
    0x14000465071600c42d190381d5408a480c0000c2034180a07080520b03200030864001c00190602c003003408001c0002c610b8055a940070b003050a11500900d9886003064101450858100d01d01040e40f641c1510004e614400c0b81c041845294455501c000c0b4071104440754034002c1d401c8403803440100710178200b20300c40c0b5503c40751151034052220b4031240060f04603800307003100752140b80040050005005007801042d0041104621020003545140d070040d40703821114989407065080480c0d00010078070700d50040040c090744444101b2681c0900d42c3d201981048a00007980c0003031845003041c22020b0400d440305d101038102c90040030b207403440100c410300303990005200c12510754a402c48200c40b07240400c03544015000640b41d000402800c600040a201130082c09207003008a0400100082003101d440c00782c02040c01d607150342c022801400142e0141c16554040c02076a031514101c546007601000245000c0c00003240c050b0704d1290755070768100c0003180a001c0a45001c204011010000324100000c0c5a041d1003480c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 169994028 1250 169992778 169992817
    0x20102031c06261b1c0303020c010e010605060d0207050a0219061b030c0b092104080f0307020105030c03040609081c050703140601050a030608010204060c050d0e010206070302 77
    0x704541606401c1a40302900e5894001c00d0002206a04254040c4040a01e82d40002c00d4410f80c00c9903039080003504500782d5541408986440c0c2c0b10b542015550030a40140d1a00c1d41d4500d00c1d0080c02584101ba08461951800b0580c00042806001310800c0b214000c210b039060441743c0e10100b00a5200400860783c3e03211348185000141c40340d095200d070880d145141490710780d18140c005822100700c500d03002d0103940c0f54403d880c002a0480301d010305c8590448019550360351444801882d2048809038040805003c5058070782ca102c8800c010001d0710300c00da00f0344549945060043d42d49019a600c001e020480038000920300442100195178080c0c028000031804914507280c006155000403290f041410400c110b0405100950040c107400c601e043c41c08010002070420700000c9084d014150b681000303400990b00c02c1c0c41d84250090400340205000855031940c1c5d072500940900c0300d0060454850103820003003c41c050080e003e00440c0003060300513008070b95130621704400a500011408012030345100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 169995278 1250 169994028 169994047
    0x6031023091609050106080c0d0221100e0105130b061b06040c051e1201020f030a150605030c0a14190806040e1605040209040b032b03020306010e010c02010203 70
    0x2103118050054500580107218100d504802c8040854000310300c010b0404004200c03c0d540440b09650050714038040540b162840b58405000e4811801440031000b03400746505044066202c1580c0520050122800050354591001d146120700344980341c3c0c00303500040c0a19004580340c0281d46c82c41e00086c0b040c0d1a0201d012000034000840c1104801c02d58003180c10041044561100c10000e48000c5540400f0b040784940c84807010a80c05003014011516003a10400b60386c2c00750103507040035542c081001e80303910b000762030a0001d20340b108418002c4450950000b902e9030261080300e0041c51034681c080c2c5000340c40103066450920a03100c00c2d0702c0c800204402c4030f8005440e442d204d05041c4a41e070726521400e14008100985440c41c05a005a8001c8200300140301d001440540498809035009030b220394020700010010310004607019018092a542207410480f00b02c158810104000942c013054503d03a90202c0032800102c0710180855094480d82c50258011060300514510500c1181d14004010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 169996528 1250 169995278 169995341
    0x920130806070201060e06040b03100b041e02090301060b0f0a0c050705060301090e011a010215040f0b071115040c0302280801020c0c030c06030606030a09020904030c060506010206060310 82
    0x8580e4030b00103035034503c01801103145488215420200403203040c051295124002510b41d14052901c1404580e41e4501c0c0d0001c7c0c64941104450b40701c0c00d601c060001d44000c000300082d5104004e0320340b283d460030074086040314040b01a20f4185003401180e50802411103030a0310440341040e010764072481080f90008065079140002c0d0b010382107107c0c0c003088224001b030b4281c0c255013aa10003907040c0c0d10503d280c205266400a181c440c0704101072000c0d0244d0301c1d10309100c1d11900f64a440a480c900251080050403904803140140040c0044111110b9514040c1d840c1601c00302601e0080003010000010005881c14801008010400900049030450380e00303002090300310154802c010507500420b000c61a0724007400131403440c0000794040d0224610b0305000a1162000808161049401002188074503a241d07010303c20380e950190028400b03080501b8068410000b11004980c0c803410400012002e5101007211801101c01030014507085410008010151019580150740e40380c1d103144031030303500310304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 169997778 1250 169996528 169996531
    0xb0703020715120b0102060127060b0a050a090b03060d08031e090706020c15040e22030e150705060a11070b01030c0305120a0804030c020a0e04060509070920130806 72
    0x229102d6428100b0100000010f13951007840d6641990130600041001e544030103038818401ca9048440b0310045080050000140700541000c4031441c404520a80c295422800a20f08064581c58030381405030f48060410241c40100c4205401c1200c9a02c0000081c62060146400040c80c0611100c00c1e1044466810034042c06c607411141c0f44d000c0c0b50201303c696018400303084e00040c15644a0480f000c8964140700138031640c89032000d0b0f0541c49000511820040004403510340048221000c00d03c050305006080c2c4032910740a07441601800107017104049000c00322180300f51b125014014030b0f5200612240244080d010340011321030200700b040001400340b801e00d4040c51040e01e041e40f42c0c41c19030422928250748102d507010000c000700030700c01c460b9402242141c0c0c8141c1c545080c84403a006840031034454542030784003a0b080c4160405000030032540ba00314521412050046940e80c6644007a410b0a484008620516500c4001d0300c0c5030034080714a00a1440300102c1091a074003580d41c08140f46020310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 169999028 1250 169997778 169997819
    0x170a0b18040320030717040b0f12060f0904021e0a0b0309010e030408060f040203031b030c010b03061005011b120c0302010c0201051012050c060301080106080105061008010b07030207 80
    0xc0d2001000101a000103030082e90203407660520702e200031103004a035581c0c8140440035240401d800d19103040d00119000b2500640291913500e500c606213108040d040b0b030418400800c100c000301e130014280d418901100d11070700300c00501c503641d1a00e42c0d40a101003000d076182d603240d45210708005011182c41340e0022038020084078501075524038001e032805085448022038080d0503002008200015071002170020b4118041210040c1c082d2218400249507224440303010302480c21200d0030102c14400840540300d4581610001c3c0040b00281c3c0806459510449410403907514440f0140030300d51240841d000c0c00c808803c1e00100d0f015040e114201081d10044400001880d90707540b400c00c01d503080c0103240601d103841c002031005050400c04085100c10740c2c05032001c80314203101000244541000070408114000d04603035600c6d41c4031000c950207081280201c5003591b007400045040e40c00c044102403c00c04480e0340320700700c590070f24142c0041c6d640078100580440c80b0310345022915081007004d060700f000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 170000278 1250 169999028 169999069
    0xb1b1905090d080a0903031b0b01062703200a15030e0c030106030501050615031306020702041506020304151d0f030a05030406030902090105030109021305071404090603060e03040303170a0b 83
    0x521b0740c50300808461a030900c1009510320b0b0a4640005009540f540f4103640032424807511066081c0c0318801c03120402c04540c045800209000810301040380c04548902c84d007440800f200d0b50488090200c0303080e0610900b60110036030401450858466480001b068030703110f0039a84d1011000f000242552915017040d1b440341d542c1c8050200902d031005498005402c8000b00d14158540b840580300908801c0c0405400b40e600004d0000847d070304c03540300004418100028600441e20350ba4021740c0c1382c002e409110b00105065070003c00c843d02403290042c40c10241c0c105000b00c1e150034414032400e9030002d0300894140c071516640e04c1c00a4000d20280000c2c0c07032141c0c0c0006401c445801040404001070340418040d906d070809440150303d400212843d04030030600d000c5982e0301ca98030200c0391f08400d21a41640c07010302007400310300c0a9540d0040340840b0b00030201400701d20840003c03980c1fa40b2a501c0001e0201e9031004142e500f4418403954140d002c003440e8000144a102000880c1e07005034010302c0858801c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 170001528 1250 170000278 170000297
    0x20607050c010e010f020d1b0614010302030d020f0a080a050c1b041107021008090c040f05060301060914010e0702160b072f0f060d090b1b1905090d080a 67
    0x1543c0c80100d2040d0440c0034604500407186020029441d0059100000108a0820752009210301c2902c0e5604d04940d001d0030800c6804041e0700400701001080c0070480c424024929201031b410b00c0003d002080b01c034070030007401c029030390f96540c8000e641c48178034150280001231050201c221420310210643e10785035039054400ea44900c2c04c110840f13270342c01c011501c00c65081c0540c0e00980c4030351883c23b444583c1c41c145500c07281c842c2c0024910b000c200915090f4030500b0f0a103143e00d40e01e455045207003e45010350080c004070f510b80352110141c0d80c418090002000d403050041028942c84900244c1202090050302c400c45100c01c0d03e9060381095400500b026030b000101401000050310310030011345000400a0344140d0021109080c1e4201031001a02c90012508040001d660300411641d50205500701044081c0f11841e0800c00d0300022500610b680c1d4060822108500d01c1e80e0460300204540d8071410401010340000746d070706070032500c591034100320250309480020b501d4030003c2450140d03507241d18481 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 170002778 1250 170001528 170001553
    0xe0403020c01090b030703050901061a040608010b0c2503171b070f09150807120b0a0b01172203050c12130302090c07080310180203070c0b1302060705 66
    0x8020181c484103040058803082000240c4d40d100680750030081614001c249500c54102103805420305400503440240e5007001c00c450000004020000c0b03941584030680700740e036101c035059203038000c1029030086504180c8031103403031008102d011005140031024996080c0d4683d15a0301c0e0b800303544480341c600381ca070005248040c1c44009100d201402e0307890700204020750400c840d2004000d1148035248046445034880500c2500351034002c4060006a41220b99a96032000a505288480401600c52a14490214100f44424045c150b42c035803042e10740020304d03c0040c41c02008540010801099004862442c0740d00c1042044006c80e081d0107507948a8079440046035481c140914160802c84040080261400880a203080075080701e0b011125509941d48244040115120303202000f441d4960001c1089904641105420291526034540c1c1c554802004145800c07031006aa007a00481c4040c002c120000d82c84801e4160b111881443d0101c45548039030104808c0c2d00040c0c02241c05402c0784401881c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 170004028 1250 170002778 170002783
    0x311010e07061407110f182a0a080f0613020a0f020609150c03150a061e09030803180f0a030302030a0c050403020105220302060a03050702060703020f16110a0e040302 73
    0x825114802c482e442c1c15110740d1740d03a0700d80c094141194000d40746190614000c0e5116100b40e550a60582d030750001c203140191255907040340195030200401644e43e4201906401d0406456049495884080550320b032040006604140140002e5100203200741e808d46524542c0044c110989280e00d0f050700f0304604500c00ba040580040111309d0652080b514580044020114190000c0c031044920b66203489101e451342e001d0510484282c2c012166000000e00660700c10382c40d0300f60007003001c0312520b200400203040760803607010301c00500180307024404998400d02803030700180e01d00e802d5803c45c0c82e0f0700c02003002c0c241071000e49103055001c2580801000348d002807900a50b40d030b01c4800d2a0079480d003421a40064281c2c0113084000100c10420600e45440301c1c080c20344000034640050190362200c0b403c40340100070384000c03650744005028980c0880c0f0000c0c060700035500c2c4001c55501c5a410084042041d120140c000c1342c041d910035070300d0b080c640019195902160040d00ca060301044051800d818040e2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 170005278 1250 170004028 170004047
    0x30204150e240a17220206090a03030807021506010e010e040923060906060102030a0f090b030a020315030604120c06150e06030708150103020906010c140303070306060207030b0406090311010e0706 86
    0x746031070120010480f0b0011144404900c955149041d414800b2040c00487c550b400b56940d120382005505602006254104000278801d8180d81c1c22950380510a205c1d18118243c00d44401d0f02040b518901d4074015030169500030308910340504006001c124030303120510482500e03000c2103058400c11003013460a03101403101640c45010900140000d0620341e0000b5564071904100c04100301c1c4403590403039510721851007440123142d56043c0075102d08000040b10005c0d481590700a60412810942410340c2c2008116188141d07048900181511801d16098a00207a0342c90201c8025545001c0c040c0f00900c4140500003034410040841c0252a024051503c1c094041c0c01880599204055015150100c40e0680341903950554100e560342d241c903801691403e00014000b0441c03040c1403080c510054000000c3d601c55a032a039014010b1035590a0301380d07100c0c0400d000260013440e0183c000340110351240c200d2602c80388285040b545050100b01d9581c00c41325880b80d640070503004400100541a4000c103890b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 170006528 1250 170005278 170005307
    0xb090a051903170c0105041b090b0a090507110717010e030414040b010509030118030f050a2007030c09020414010e09131509030306080d030204150e240a 67
    0x1058220300e038807954400115210040040c04061480f0003410f10107001d44030151500700c002e220500b803030303d002504c00d4510340801a4400304544001a003260743d02400c072102c500900380c01032460806044102601c0700074802c1c0140032846040c004030001c10031010008001c80e00061002c40c141508990070340c2c1d4030035441c1c01142c0c011700041c80a00b40c0380c03030400b20740401110000b601d4030129005035410b009600d10b16603d5446d001030600d080c80c028481400044c030a5586000a41840300c0503642801440001d50000f1110441c030403c0300d1481005070000e07510700041b00d9516540313988281c900e10240d0000003030a6000b14042014882d034000d07420b0040c0c805d00b416103103c0e044101040105034014113445074400c1c1827103400309106d692a2060500180d02c042440244c6840c06c000c1c0180c0130600c2100785902c2202a02d0314164400d100b6142070311b40c0700700006000c1c058120112040070f100180d0507409030001030409211011881c0400320710b540c00402a03151600e00002038018072800194 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 170007778 1250 170006528 170006539
    0x70506010b040b04061d0d140c0109180e070302120f0706090617070c0b010f0e0a0c0807080c090a030303050a1a06030a020a2003030603060702010903020a0213090b010b090a05 77
    0x2848482143c030f06036800d07255a4034280780d09881265072003000e140f01240d000e41110112400006001100c640c0001c0c0b0390107001101d440402100c01180c900380248207500c10220082442010f02c44245c010388a8090940c0440701c1c3c2c56100d400056403ca80d0008041c4203030301c1150028005d0005005500090480741040d681052070f284010300407201200c0511070030002c00c00000c00300d41c0142001d0044641101c80c2104968607492020304004950181c00d18128007400040c64108042c010400000da055981c20219160b07641d043e106004003415001001a061010b554543c4031402100001c501076500401c0500305550482d085420004582070f481004850380826915200216074025109070001659005003c10891302e002c0c004480d0b05103802807800c107003140c20703000014601503801142035540c26204e200d0141d00300c485900700100545c2001c0002c9015240c801610340d040404010003203140c009550700c0c4107840800360054900350102040300d901906040e070480c00540800d440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 170009028 1250 170007778 170007787
    0x140f01090501050f09040624300807030207170705040605030f1e0c131a060c0703110112020a02010504050610061b02121204051c080319061a070506010b 67
    0x4209400d4031a440f1314013a44030400410f0401c50250301000340c6500340e0070000a000c06410710483d0030201d9218844031004101c2010010a80d000c08020040c9101c119074074440031590351b01c0110b42c1006a00707405500581c0000907034401c2915079200101c0a803000f43c5241c0e41032000308400c40c3d110760001802540039500d00d060490001848603071140040121101210140c40c1c600d1030700c00c0e510b891940081158040341000b900c980c0214040741d0a0441c1000100c1c542c1051142600aa01c0c0d1148503502082d020804284400000d0004000c10b161003600b821006103803100742c0e40030070b0032000141c4d501c1d1304001c02c1c4681400340603005662140b20107103062070721f00010300420f08220800b22800240c0d11a404542d146075103e1074003607035a81a16140c890400c400d00c100c3d00540300d83c60044e0028032040004a815041c60012954803451040c02c54a900800c5040d6900d062642030f0681e0b900d910110741310a40d0342020b10400441c2d00b080b5524161850464181101030344486914a000d02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 170010278 1250 170009028 170009039
    0x3060316080a0b18070305010906050603060919030306030b04140d0206161805040501060504090f1404080706112b060302030c060c0102040e070903110306090601050409060f140f01090501 82
    0xb50b41c02020790000140710440e1103992070264610b0340084100098400d65200004200040d04110903040c001c0394108256070700c0c4400c3c19216802200c2c081d80301c0d000705008940310915160241c0c030040c0246000501750307890369035840300b8400690b400e5a4416002581c440030210400c04075202041074800b80800d401d014540c2000d511012044005000a002c038094910320130390b41d500000c24000308140501d5039100c038040d042c0d6010703008415a9508001c401c01c401440340c0203c520210701240100700d960390740e4070383c40e181d5044120202c40c82500d81e900f03c00100f0010001e80f10b1220684802d61901003080a150b03843c000d50062811403600346081007015a43c0461801025101503440e541d072425041c030124024400c0f81c000c022000700388410300070350742d9118000b0000d9900c0740822a081c40c5101c401c15030f072040101c03400d44c01540004014441400c081d004412140d1180b8404241c44902110000a8500d4254904c0d40035109408211804005c00000360042c49449401c010650505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 170011528 1250 170010278 170010283
    0x1e040b0405030c100e0f0a030504050f0609040207060b1002030708070b34030b150304031103071209171605040209030708030f0304020f0a0326071e0c06030e030711040207080406050306031608 84
    0x80c442c0ea071007403319032828050f5407103443c111840040d00034011035580c001c0d403030208020038540901d28056000c446200d00c01600000465446c00d4010080c01d0600707020b9600c040c0e141c10f00502d5030141c03c0403020a0000b03030110340c0c918003150300b259170300840c0d6040001006085034480a0001d200b072040164180c152a02c060031641c0040d01071500d5030038092440303401071661050b650028102e0030a2603003402550f91006225094414101d41c0c115111242c805140d543c01c04508902041414042e04002c40c1ca0264000c180310340014051702d03d4180d0301c00c2c00c01d0554010602912909100100300811031506251100c0340c8801160b8040d509030458a560403001e0698079a50130284403006544181d091010940700280ea0091200c90010b201b04070b5803c47c1c171034014045880f80300740400800c441e0700038002c0800400708d000055081c4500d5444d40b40810a030b521019402a908100701808036048070b0051024000540303590399203040210a00d441c03c80c0700c2421a070b2400c4101010300103070402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 170012778 1250 170011528 170011537
    0xc1d01090e0109080403201e01020c090f06101209030509040b100f0f03061205010c1101021912020d050c030106020c0301091707021f030906051e040b0405030c100e0f0a0305 76
    0x4807c4441c0001c80c00c1000016000344001f90a0348201012904107401c514010b00005600003a800d4a2216940344103000584100780c81d0b0070700741d07084500014520b080031400045d60040c2850141803603d880d080103000c5582e1070405400050000074100c0340d50a150282a500c03500c00d8a040a080b000600020079011569070071000704100441124141d902c20781001c80034280380200e884404150b49803490080c500c26402d14082242d100413138900c00c80c1032080e14101d6021048844002d0b03c18801140e20104410251012642c02c0c8005081459070b41f20302885040300400c07581e03903541007040103032400c0d580b21080fa20907810300d00100c001407842d200041d41c2c2d031641442151641910320010380e1440d40e2520f0003480f446c5178909080015071507041003e010380a80d0341004240c844002d04406001d03518480c100f10300610b00860001000251455406030250080e2410188010651030608010750b40e10700c2e000ea210200b0003a8581e06010001642c44a44000c20020545a0b80030f00907004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 170014028 1250 170012778 170012783
    0xb1003020105032a300f0c0c10060e040311010608030409181506090b0f0603010e0403020a0c0305031e16060e030f0f03010e071d04090c1d01090e0109080403 69
    0x2d00007101001440840d001c3c10040924401c113a48036485410800441c1000c0d504510120842c0b004150041a0b1144a03a000e00c00441e000c00b04e07691440760300741d03031a4048083d50800e8400e090b9090740c001103c5c800e4201502c0d20104031819410681001480c4105100340c40c0e807941d2506004108030400001203070301312001ca0740041110448050081c00c0128100b102500c038008040e061016149154010421307129403450801240c003104040c4202201841495900198108014000319203244445a417262280c8103da11220302136079059000022544102c0c1d40f41c0c030110341510700c1d504000310380d0b9003043c1c0d42c030f11141070252404017440451100300c0e002d4820366a51340c07040342500c03040c070440e80d804a89424469495403c4c0d452604a58024071403140101e400401050420b8452032004555903032200c024107043e11200300304001004c105404440084092000143c602c0480061511b01e24a001d0500c0b0307290300d020141020b44131107000311100741c0d14002c0f000c0d0001c0c030031000b62410b036074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 170015278 1250 170014028 170014051
    0xa150206060d02010e0603090c090a0902010504030b040f0f030c06140405060711031b0a050c03010605030a06020d1503050a020307150203040e09011d160608070c140c09130b100302010503 82
    0x20b14001a129401d5160a480c0c005d9000000c00c00320340800103001c0351514096a80c03810607a04d40848100701d07551240000d000030707030412041000c903001c40c0760140c000f8003070410a92428030564070445c0c0d01d03184040460104240300000350a10600b0b10894500301c0f014070350303845546800daa5003500d6042c000c02d03c60034000c00d5400c44017207010410680d5049032008040c0d0281241010030540e495108100c121200e01c01e401200138142410f01a48040b150301400800d4660342950301c8001a401c500581c04020703a480000004580100e000c0c40000c501480240c00f00340007a005060900076640c0001c00d4402241c1c0c03070100b10590000031502143c211540b40c80058030385105241c05448004080c509841e0354203101c62415130041100c403110350020344805106a51503201fa02e450004803020804118009502d001064441e108410700c09800000c0d180d108004070b002640610b01600d5490500c1034501440f001c0140200341e41d1b030003c1c0c111007100d40080ca180d00003061440020182da00302ea = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 170016528 1250 170015278 170015299
    0xf0e040b01050d11040501091a04090b060904061803030c1106010b04090207030e1f020d090b030a0c1b11032103070302090a180c0f0509031e10050a06050a15020606 72
    0x2100c04144c03c412820020002c0c4003559580426001a140300304051003c01c4011450400500d0244116040140d00182c07004055a07140100a0b0b0383d031005100780e400315142c40760700b0351007401100e4031804c182c820b450000e401c00d4030100040c2030350b00355080d11f404c0c0d50100e401809542208404c0c2e50445030310a001583d643c4451904a603010100c4580d0342e008200c910180d203443d84104105d48400e10250b00321104a80d40e0f40007128030b00e2551081c05074a40007040031075881c0c4540d4008031003885860134000480006540b14130741d40b03072544906640314400d4010007229442e0501003404101e03612609140d0b4608440d408604504c030262546040c5540050012400d4489198003030082c400f0540c1c0030764001d5090141c4c400340c100098070343c0024504c400702a4585010320140c5a040602800400703485115140034003649404003107c0e801441501040549500700e4004c0340e2140807004004500c00e881e11080c004425041d0300040c0314803034914141181c0a0b4000f82e140e0740701e0011613601001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 170017778 1250 170016528 170016533
    0x120917060f06060f030901060510080106080403050307200c030706090b180a080303090c01020d03090f2004110405030f010618090c030f11010207080304080a0b09030c030705070f0e040b01050d 84
    0xb11311526a030940701c850003004100159606610013402c58406480703c3e00f000250380000c41710440c1c03d00446010503520b5000c2f03404a4410400b440e403240c514107000f510340019001004000d0303039086484080794071502d14414142400d1150303030f00400c000c1c205109458140b01ca40c0010b402505016090345d50b55003580c6c2a0765980f030500f50014203076001560398030f041040e00740343c6444213101d0260161298001070344c4064481d04c1007640440c0c1001046020071020f80d00d54026200610340984400c07143c08c20040c40359542e116181c601c81c0d003484560354551070541410b003403584a2041800316407508004011079002442d00f101000703592000010103880524040c840c40015400c040e001030403003030120302044610300100394861713026000c0321110707507584004658070303c0303079000d014820382154a1010020307117452a030a070040710100c00d480c1840000d420301490754101d20300075180e0343e10540040019010b4021140081e1100580c00c0449142584882c01c0349001885441c2c042d10484400009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 170019028 1250 170017778 170017789
    0x1030f0c1e05061e0a050406080c090f060c0a02091915210501060902160b1003050318010c02030d05030115050304080f03060f040e0105060418260403060504120917060f06 75
    0x8986a044402c68a1780e5030040c000303010390000e01800700412100b4010800d04005402580c54042d401441c4c1c801e031912a00c2804000d40140b80c1407d09441002044c0b40107a4561000900c64041d00c5030032070402d03030b03102210b0003540d82c4600741640404558070103000341e68140005514080100e000c0842c010880e14145004103000e912034881c89102140004a11854588610340240a0100140583c5071007851000e482c800780b00080c4540c1c030400009a841400c1444400d55100506040c1117000058021034180720010021030300281c4008011300030f010400c004440303001017514009013146002c0e654607a443c845c064001d40c2220b8040000751a42d03403036031007074010841c9c05407044c007010149610450191800b510328503c44d5003480481003010b102410005501d80e00300400d201c0c44080f02d0b010201e5100c014800781880c05040101001180c030500844e409548101181004c4444480c0020070180c0c0c1070708081c00b40d100300300b841141030388009000c2d074100d1042502c2c3c10440d1540300c001003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 170020278 1250 170019028 170019067
    0x504030503030f060a0602030909060f040e010203090609160e1f090c020d0f020c0a03080a02070503061807050111030d1505031f060b07050706081302060301030f0c1e0506 75
    0x308244000020841e00240d0101050f000e1032040e40e15043d02501c2d80d80507601c0703024007030032650402e181c140020344a2811038800301c0300090280001520290303883c2c4a5003aa84200e6030758080d5030105c8240300f00340740f08016044e00d298910100c042a83d0800241010030302000d8854141980f078003000c050881d80d0841100e00602d030300081001042180c0e0f602a450ba1421114030010507083d07040c0825950020a510010460040034422254156070f07a0304c010350010240b8108600c030b003010104407900c08004660003080e40d14141525070481080052031b0440c583c00c214104422000d200c0d560540000a59003005000301004c10038030405100600c00c520f1550000383d04d4410203c5c0303154070345000400106000d2507103006020880c0c86080d510024070a080008015a0081d03000b00803d0b442020141e802529043c03149175009215000076a03d50000e820594450002034840420400d03404204002019900f2809104c4460b514651941c07007900c1c4034480c000d4100103401b003444807000d08080c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 170021528 1250 170020278 170020283
    0x703020306041b0f020d090803040302040e070b1605010501151b020103111c0501090b031504030c08040b0c0c09091b060c0105010b030601021204050604050112020c0703080c12071a040201050403 85
    0x3610f002654410003071988844086260240c0605c0000c0d000592140000c031041d100307040000d610f0300c0d08d55424000100390f0758007100c501d40600f101c0411a10061801440130f650006200d20519075241042400c43d401030740103030480e03182e00114440c80c075000855007900004150000d50311852a0005030090805480075150210000811040c0c0600015241039540c078689410406680c13242407000c200d03404103e404c0c0e81980900c1402000400140e0f08640c4144030b444d2160644d445590754480c660002c0d04401c2404002180100048004202d0b072003201c0411602e8001070300b8101445611603610b412500300385000c0160349181038442c042110f07000c58065000304415030f174038009180240c109550303480c014098581da40c05401c0c0c80d4025107050f201c2c003c120743e190600d0b0000545407012480d2101c0e900d50380a00c0000030445050101030000d600420b0100d0703807000310404e0903060142003002c10700703050000d0100350081500c0305011011040340c5021f01c0035545650005881078041e96000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 170022778 1250 170021528 170021561
    0x4080705160b190306290415021b09070c02060d0b030604060e1203011503050a0e010e01060501030b1801030b06010509030610031a01030302060a110d060305031c1103070302030604 79
    0x10700b0451003004141c03001d2403030300c1c0009160054034101c0c10f0703419502c44c180c41951001060075017a180086080d403010204503c0a02c7c155607480b0b90700c884140d01d051180035030403100f802662149803000700702ca10803080340c4802c07003840c01032409045080b290501034083d44000c164503858845c9940600c50404000f0700304c407007600e024948000540915003080115000d00c02c03000302d03159140381c16030781030307580c9a4064a0180302c015412001040010a814101900c9100c8120b03510000c0c4150505266178200100c1c015003018005410f0b01c85000341d042c000c010035180d045015003216025810b481e40300141085544440004803400e0184000556040c0590000d015898444440d00001c40b0710070038518482c0c80314445440c041c840c0910000d009038000c540080d5500d16251704c201412002100c0301420001079a448104803070441d007045803d07510001d0000001a00c187e1642070078103a02c8814810155900c0d652081c03400080c00c0d02d01032503000b001160300760380c80350440821001c56116 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 170024028 1250 170022778 170022823
    0x30f04030c03020f0406060503070807092114060105010e010c0c0b04080a051c0c062a030b0102070515040e040809270a061511011113050109060e0904080705 69
    0x1411020201c01d44002c900c00c600c8054108030508280c02541d00315000d60303eaa82c115a1aa5426101500000d01e02001c00c038114101044100b0742401200d114510400101681040c1d458841d10340118020784041c190302c40c030010400c41c0e80c0058103449d00c100a10382958148014a00848030644a800c00c1c0c803102c00115000c50340b24000200d07819003900940844e0140030080081071402c000030109100001d040c1e410f05004260315402c1448045145a00d101e40740b00e03a00c0d615140340514049890000780c60360081401c83d030b8100100070151508035080d284c0008150b52032402441540700c1d05c00000d21460000b000d01485400703803048035501902203e13000340b004a080d400c00a200683c1e00c0d500c405580421030494803440303039006444030000c041c034000400103400c3e654a0001e0a40b9901c2d5034072143c100c0c044107000006081c1c00100044401411401c0800252543c00075820036130070070030b2941d02200c140d50340403500b40e0001d412010142e40c805050610900742400407460680b540c80614 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 170025278 1250 170024028 170024033
    0x6040f060b0c0d020d030b090a0203092401060e010e0306011502030d11030a050c0913020912010e15161b060b09040f0618030e04020a1e260603060a0e030f0403 70
    0x602c1400e6043c1582600c02601c0e101c0b03402d13001c940c008100303244c20000040019810044c0c0f40c1c0119080a80d175012540100500311452010784154000e2100905410b4010045581c211400840004007402c0000c10070180c14086680d0740c0052268150030000c00520440f440c0c02841110500f020154062001c3c950725944031602c1d0f0310a46101e01101d2800001603c035000002c1030383d0300070000501c1d030000100d400c40e40c82c0294000d00d44080d4414144841001d1101003481500c00c80300c0040c000c0c1208240245240d0602c40000b03040d0000100000ca40348006944090b20b8401d01d0b40c20f1106002c1000d180c18598010041c401550341c011011074148814040b141c4040d43d521840703403906001ca80c104030341407803002c503a2040040206140262000c910b1030309401500d091105880c10341010300f8072880d901c0d9882d500d801e00d5000704003280504507003c1030350107084034a502c18151502c40381c00d00f000460b5640c0001130480c2c080568800514526032020f000300e131030f660058540a9115516030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 170026528 1250 170025278 170025283
    0x60c0915070f030e0105071a04020109090f090210080405210f12150a120204021b0102070804060201050c04150e190602030903070906080607081302130209010810050906040f060b0c 79
    0x400c069020030004d00d00150291300c600115180c0c2d9600101c0e400d80c81481d41000f02c40540003800c201d0501c80c000c4008281035480d40726401006800010205684009006122010405901d1041084620810040803c1d03000440c0284d81c400310705024000c00c000100d280341801203c1c0c80306921503001418400d038224901d6810b0081481a0000e680b03038100304c08001d00c0021034400c0301d40fa0340c681c000c40c50251038980d01802d002c108085502c003c0e030441110785402c80c0e0110000b110300349004074040c000b8543c244146a8462510510203180509044c01c80107605064081030b0b0402c030541e541d03004641c40e150404204008004c0250140549036440030f9100d07007000f004c441c040e209403c400a0480700c640507650441c0c0010016082d940c4680400300d4a42c1c0005022414080f5030b034a10100580741c0341d00131a04021110700058562403841e00041209030094030b200b081d101d04a000303008658031112865000300c1d003120001404070700300010b14007034000343d4043e45907184080307590a14450302 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 170027778 1250 170026528 170026553
    0x5040e07170403081f030b0c13050d0804080d03020903030306040b03030d0501090c0e060310051c0c0906090506221a09040c050102011512080702010e2e090602060c091507 75
    0x6484940e1441c80b05d90300403100f880c05d00d00c0050002000380f80414102c00440300281900c00c001038411129548920101c0c0e2410320000b0101d840f01e50000c0c04201008040c072038140485c1c4503103402d61425425000184d540c1c00b002d41003c2c4520707071b0384024081c10303030341081151618142c00d80103001c950b9595030310800a201c5944030101250542c5940c08041c54480300312071040040303410008983e41031070103011001207180030300000c61002194502c04160407248580017800c9202e0041459030800c4511011f451000e06941c0c0220b0850343c0d04c05664061401c0c886d40c100c1034100010314008002c1c100701480800b0128590003050010a1100303000c801704450f4180c031820b80080c84240031780700c00300c21510154410003c00441c40e0723181c240002d031504002c0c202940149003001c00d81040000040603001c681000d0350010b56000c001c1625401034020010240301c0314105042c8107071030240044d44400006190070307294400000c1000b115500c61040e4241121402e22558641200345081e0981c40c24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 170029028 1250 170027778 170027791
    0x22a0c120c0117090c060f0306040f0c0518060417060f10060914012a020a1502070e0c04120302030d06080d0507020d030908030c1f06050105040e0717040308 69
    0x110003155004400d00001d10484150040e501d42075800e0792081040020f00c0041d02c8007480d4002d40c60384015540c1e4800182c80000c520240d542da880c20288204401c43c0c070010002419035040460114141d030704501651040605402104007043d5200d0005000d88156044580160788a00c550505480e0014106204e09001c00c0224101e40b501c280c80480b850340b5100d0303c1d0008202c03210500c50031000e644c0d04002c50506040001c00d64041201010000301e1080f090501a0740905003038055162503420304000b041c44e190361040082d1064402501c034003442c000e48602400583c0416a44100380c01250300500151491f003201303030240d1a000b500d9500030005454101d05007140455001c0011aa44000b07a07882c2e11004d18100c0b00f6402e1000e41c41c100d40041d0b0a20054040c0010920011703c000c0c600022004041c001011020340c124403030044000c4103258503442d1020a00259811000302c0d401e81d03500c54021040c82d030303c0c00012030308078505010180f51702080c20180403c148d08a10028090751 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 170030278 1250 170029028 170029039
    0x103080703210e0f010f050c0f0c0f03071220030d0b030708030a0512090606010c030f1101060305030901200c04091707060207110405070c0209061207030b010905010e010f0306022a0c 80
    0x90086d02c80d1026030790152581102240200402c015007030400c0300600b0009001030035103054207641c810040c1107401900702900d03035450110380c040000d54402c034940078007120480d0310580d204010300c810390b0b00d010300620a00c456603a030381c00080c0da0745e003041000300410384c1d10203e981d1003598440040541d00441c01c001820158280030170105000031840d039210300340603910030b9001c1d012910221280b49015a1035020701403a0010072100c05000c0c02110b01450180004581d95104000010704c01c5403009000c02a0384052603500c0903000000c10344106140c1c0465003c100c08040d81000312040a464003022005240000c01308100000c80d0040c1c04828003500706038400c2443c440511050b224116007a000044a2001c010300500c3d01d80e00041d00700e98098015003029103042d16091500201c3c1d04150b5000742c0610041043e01402c0c09940d0140101e420511180d501d4416050f4005106002c01052185c0100d004141e50310002820714001899546085908403050100703a203444140042e603000c0e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 170031528 1250 170030278 170030291
    0x91518150e18130809100c0201110304060801181401081006060f0f120618090209060a08120a021c05070303060509010b12040501063201080103080703210e0f01 70
    0x6142c801e12449244144250444441e40c80102c14144400780040032a00c4000c148821840b40d11144001c00d40c01c0080e440b00004003220f0300001d85150842d041c909160b60081000380301e115445811681100c0c0324818910002540240c254013801d10003c06e2480101d281c4000600c07203800180300c1c610700f0034040040040340d84a940440d2541c0c000e1039690040f0b000d138600c200c01144035003030000783c01004400c0000c1403611110580d0050603503013001c0382050b483d192070900303500e00128a1a04030708100d40000c81c840c038241c501500d4107c2001c0b41344c03940b4808204040107078005c0c8805944694102140f41c4456203000000e446504044020340010b4580301002c81d0508020540b18165103e51044501b01340452142404c0000d00510443e00f84d500c1d1070300010302c0000c1100e1440c98006206284801c492003480c1442ca041c0c070102903d0411448400400100e04501c04560200e1b805107007504a40c0040e04d1800449110001007480c000e1420400c425185400314082e035149034460005d0044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 170032778 1250 170031528 170031557
    0x71e1101090303081f0305010e0304090e010c02070b0c03040e010f09050a4110050306070306060c080702030f100501081e0d0e0112140708070201090309151815 70
    0x1c05030100901040000c40072803c0911404c00d0040b007071510801c040b448a86a90307819007501c59245021116600100d028410f0308824065105140c01d03000c02082840b80ea07503402542da15140c41003a4896030001904182c1d00b0007402220040d0245a54070305065075103926000c908640c03840b443c10b80c5458900030a012103101c5c01281c040862444043d00000c04250051600c0980d00080604890b10801e151006141c030041c0a440340b03010f0503c041850b03103001d040c1810b212004000c03008140c9007540c1803000d560055510180326812400598980007e072003c01c0c9000e00304652609184240724903407410300c8454102c6c5068401d400b040c1c03140300c1000c0e400740000b280c18010841c206d1b0841c01d02440178a201ea101c004940c2c02c1490003048002000c11150200c405000c80c0d04100c528800400c250070b50400003050300700006100800000c80e06442c0105018868040e0416011000c0e58a20305a40319007103400c52040d41c88a6103182550307500f128890f259445a030300c00070a8a03541d21800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 170034028 1250 170032778 170032787
    0x501020a170c09030618031c0c030b01090b04030803060409051504060b010e06030a2003041b060503130f0203240103021c1a09030d021b0601140d030305040602071e1101 74
    0x41841c4050020728a5440d401d000904100b11b0007004040c1d40301c2400701d00300180c5040c81000240c01e20710800143c180b000000141942e0490013410305002110f5420483e207108481201c0440f0780000382151a61140b038000f4014001389980a0f20520550070350715441c2c0c000b1040c580c0903a108100400502d002c400040d198000742502c129481a010b00010361042241d0700404130b2740d00c1c5501e05280c80302e00c4694011203600140d40c1070382c0b808030407040c002d9006200b60314078010f003502e4200342d421864040e0b20509010003400340149034246036001c000c2151010020000e100c0091840c1c168480116010150100c0c024030050344950141c7c1200443d80041e00712407001942c200540074110304061007601003040014008441600c4101f00b9600a8940d5101401c0310300c02000c83d80044196a5842500c0c08106812021840c0d03030078000c000b416a10020101082d65060801050079580c03400c1c0310f8002c0c0103661000c0d0469440030034184800214100c0d06c280c1d140720342840a41c00210100455 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 170035278 1250 170034028 170034037
    0x2030a08010e13030e0d020d0503030403140f030c0a1106011202041805060c07050f030f040e0a0b1011010b04060308040e0708070f11031306120e01110406030c0c0501020a170c 77
    0x181d0910304103c2c81c0480d00ca0000104d40150251030300802220340c0d130124010807070344071050f03d03680c0010090000701540400c00304808060b8070869800c0081407d81440140300192000d0070b000310000d1100d2685000c0c0c0480626040110103503440e540c1d4440740100100d1545034100d01c61460400b4402181900c0c1001d00041e07900840200895600c1c11100c4445a011400650f910320810b4040741c0409400c200410b480034105c2d41c19034459241807110303682c0c00c9000d801428802e040480400483c0c40c1c000300004070b440540780111308800003510103401448206001d507005402c2c40c501200f44014400104103c8642d45940003a40e0b40340c1000f12608001500c82c0d8001440741c1c2c100201d124812448051a58010415a0707d0305500310600310303180305a640207101152480d407540c84c10804034494210307182c00c1c01c0000d010742c0980b601507001520440c00741105141d0342c1c41304d060303030740d13100d0b400d204545a400002156244807681016242c655406003001402c0c1a40c00062011241c040907135 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 170036528 1250 170035278 170035291
    0x1201150f0f03110f15392a04090c031a04111e0409050f060709031a07110a0503071203110306040c02030c03122710050402030106050a0602030a08010e 66
    0xc14582d002c2001300210030a00030541c007104034807020405140c1032000784044804828410242490031400746504030055076100180f1310041d614624041d40490310b0910041800c1002c00e110140c43c00c0d8030100150b00391055002440c150070102005400140c003030070b4a000d485034074a40701c1500c8081c003420b0401c0701e008200b10711640182c401401c1c030041030022801841415442e071400103010504884c82c20400b0394a41d44405002903070207a0900c0000e4008103245464140c3c0c0781540c64040c1c6400000e6150580040b9074000903000c0e030311903942100100000026265840942e091103641e030340200700107440c1c00310301101c405500d90081c40340c240540c041500036425580d84800308802860b002400005600042041b40f803804003c2c4020650309102c8241d04505040544008401080070780d0f00c000c000d041c1c1001800d03480c00004084080b95010340d80880c01c0d6441d0b101003405412030b5404103070030a51141000c20419000310107405140f00310703610103c982c1c0c0d860482a4030300c030041e903e5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 170037778 1250 170036528 170036543
    0x10f06050d0c0c120519080606180a0302060f0c101b08060307030b16110102030403091205120a0305190b100f050919030b07090608010e061201150f0f03 67
    0xe403007582140c22440380031616080410314001d41c0e4a559000e41145800030f0300040c00001e24000102015101c1c180d880100c1c0307054581443c0020114009100303003010007610000ba4480d00c0e106d6907603664a00040c1d58058002c41c1c803188900040341040d000005455801d02804610200300680740c803a0007400e82c0d82ca20145c5401c0d840714020f4548981c0a000c0c0d50301800b6446010000c03960207800c050007008400128001c0c01c80f0407100800300c80d03981d1208041c0741d004006010100b540040c002055483c42c0d002e002c131024491402501d413307481d003000310b042038010a50169468241c0d01c207d2080458100d82255081c003d082801202d040d00c0c02c4580c030040e0305103498504e42c4038070b8504500602c6410080e20344080030340000c06a00c128541c03030980303080c2c034601441003106503586d8a0b000300701030074103d0690b4180000581071210500401d42c2d110400000540c1695412000088070701c9820000c20400012010801184450380140064105074600015140390303440d042d04100ca401481 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 170039028 1250 170037778 170037787
    0xe0f060f130510020c0102091509010f020304140f0d1e02040b0f010215060105070204060e0402040c050c07050d1509030e090c0408030d0b01020c03030408010501090f0b0d020f1201060e040506010f0605 88
    0x402000079045119540c9056500707100c13601650300c505021407a00a1807010480d01c2b14001170004000500011250302107400520040003400680f0001d600d608030206c0ea0802c0c04507602020070840012030300041d001c02082100036038419040248403031054000d0720240804d194910038006001101c552590060340035a070010101e495500d00f058005405140c41c41c80c1c140135800042c1a90300035080488110984400d0004528252140e114100020305045003000060300c2d85540b030b41003600c01daa0068003003111040c10080941080080041c4880c020000d088044c100101103000350003603203000f070403900e01040d000403100c0c1c00e88045031000001103203050700410300d0901601300c20b007849056100303c1c3ca004500b643c091029001600001c800000c0943c9001500c0040c1c644000c3c0d580035072440c0002a184649540282c481155015500080c1d0540e00b0310100b0280341405011941c254a0868041125036280c0071007405140100112113540c1d884011200b08a1403921407840030410422 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 170040278 1250 170039028 170039053
    0xa05010516020f0411040b0c060a0908070303050a090c09020a12020f090427080324010503040615030605100314150403140d0213080f15190e0f060f1305 67
    0x740741d019404002d000807880400c000005c038055000360f000a6841400400d44c6120000c013000701d507501c04056281400f40d00e440e40c8803150a0310a25201400b00368440001515003e42078010f070341840d0780326089205841e5a40c00d0072009400005050000401c242840a0140341074002d440d070045074001c1c2145010102c4003000000c0c4402038280d1040492400040e1119410a00d41c0b80d40038010303564075031b076403800410609106c1005d802e003030311099034152940d0260764840709407a840350b40848001010460403c0749051400b5907400100941c0c01c0604004005100403010000ca0744204004040c401c080b004660f160f842c80b08280e0047c800c0000000c0219200c3e8819098520780342003440c0ca004026800700c8160703030001c0000100161341000400c0102c1081041180070b60000e40504003460164509403096170014107850f4894000a0000e072500000750700c14819000107404603a001c400341191182c94038000c4035040c5038100c04c1c2002071403141d003040b0440071099114010304000e00090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 170041528 1250 170040278 170040289
    0xa0b0d0602072001320c03070507060f05030106211a010311030912070f060c020114061012051f091505190308030c090d03090305010e011104031203140406020403020a0501051602 78
    0x1022170450700f49101d201c1c1c610803a030729009102c4200510055996107055041051a00c1d802d5030001c400c0180c55000404010b03484010340341503960341c0c40c0c00c0c49002060500007a00040010411480e18544003045003038950104282045000a89050082c50700314030406c20307035000c12144890f09801100003a0b0500340404011b01000d4401d041c1c5130a41d501585902046600d140081c00c0540c0d951119045000c61101ca010741c0481e003190516058a250b01c2c000788400392a460420000b5180c0c004a8030120250050140345802c0b255115901951392a0b91009040050180703410407201c13180100700c0341411044100050b00e580e90018400d440c0da954100340d944001d0005500300810b006040c601e65800c0c0e800b5000798000c0d0fa40d00c0846056080c0365007181c0f81c5680c00100c42e85044146140100c444059900310fa4000345807440c0d800c0055001e42c003401e1034946d5403d900070044c08000c104291940a4402d5a000b50307481402d50381c40340e0041d281f92044042c0c01c0400c40b03885420500611b4074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 170042778 1250 170041528 170041577
    0x8070501060b0f13052e140c0c1203070506040b04030c02060a030504140f1b04090605091b090408090607050709110a110a1101080a0b0d0602072001 65
    0x18000001d140d9540342200309881d005448000329603007000441c501001d13040705084010b010200d40c604030061001120403001e10100c86a00030200280c001110340d24000d04001c82080b401c03540031960b9031840504a81ca8042c0301e00410f118481403030703154401c1000002600c4a00345d01c40010201601c1e01c1d2120640b0340c800070012010001070080d00d10068880300064004000c01d61130100d281c0c2001e00d000700c0442c0322502e81c12040d03440002d800a54190005204018411008500c8420f00382a000304e001342034811005400070f0700304824071803010b00002c0e9203001000802181800c02c1c80e02020030804010a0728003412211050040c800c007481c01900518400d1300c41c5040314065030f40c8101c1d1800383d41001403803804900d07000c1110101190418440303407070301004e14094886c0301c000b42d40351544040b8050b43c00e410400001c0000340160529403010440704001481d091104089141c02006584004002c0f5180c8881070086003c0e03008440e101540b160b07058403400c002200c3c02858804600d40c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 170044028 1250 170042778 170042783
    0x5100603143c0316060507110606010f0507021806011106040c061d1201020912010603150b06040305120403020111010b0d290406020d0b0a06020d03020a03060305030c0a0b0105120304030807 83
    0x6100c40701d4000c4140c03c000034004181c4521321075004440030708041c002c60303800601c2134040c814030454004079200003045a030346c03242c9c3c2420b280c0130104442604489500a280009400c4001200390204040916000790311031a001d0fa80c0410164550004945036a020f440082c0303070b4000002c0911410b40030700340800411400300d900d41c0720301c030f0094001000c0740e041c00305d070705400d075800100c0703100509003040e00d844800036000082c800f9030700c0e50360360707140c202c80f00002c6030b08150f0784015402980d41c90744100d800454000e0b04485550001407004d031282d40c4144422400300d10304d07038039082c103240c0306003d40c400410b0002d00c52100842907448a006094120b01002d680804681034403101400391000039000b58050540141c0315526007a04c1c404503424190001c2c400d02f07021101300b00d90703640001c4450509802d80f40140c4c6803403240c00e0540c0035203a1030b00000c0c4a4040440d408004500c00101074881c00c0c0030300054403990b40e84005000403002d180039140704d250001c010034804154510010482c582c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 170045278 1250 170044028 170044123
    0x1061103190c3215060d1407060807020c0109051c03120213051003090804090b030709021c050a0e0709091703070f0207050102120304120c0510060314 66
    0x484680e5103201d81550070381d03031a004494803090b2003c002c90404010b80c2d00302a901c0241000840304400180601005020750300c20742c001032209040000c544004200000d50804541d4010381395000508100310403600c5000502c076215151816600c6078218904468003c0c0456210181902440c8000211740505500344154007003c600c03a032140388010210902c8622003c85100d003000100000030240c00700083c00c03d030500350040701003030148044400300c1d10b02003000200342501301c001c81d040c541546e0018110700d20200700d0761614044e490340c20a06a0f2210000c100c9a81c0301100d0400702c0303680ba90344588aa000e00d030140900d07411503010701c00c0503016100300310b854100b07a4100c2080c1c0e4821100540081c1c040030320360f00101c1e010846000540003d00103800d4601c85d10a4803211800020005480c06428030804401240512404001203410809680300340700044600340c051301451004450f00b56128012000c4080042030341c000d056075400700e60b4107488800605000035102d50f11440d0050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 170046528 1250 170045278 170045297
    0x102191205100b181906090806010e070503010b070f0b0f0a1805030418060305070602150702030906030601121b030e0c01140d2c01050709140102070501050d1808070b0106110319 78
    0x1620b0f17201004000c11542d81c5007100c0c581000d80c02824000180d0021181c4074200c01482061034105040d241592542e010b00c5485041c681020412054005400340c01d41100780207010102c101c01d030429201d044518414030823032000100301100072080b084043d1942e0030038041030104503410b000d500e040c0310001a000c5621070316500c0e80c90410342240c0c40400564007100c030328030300b0020308180f80740c1c081090700142d4240791207040031410034400141440e04001e402030b014076803142c2c6640420895094480580c2280c2d09521002e070080030a0fa1110001c2c2c4680e800c0c07076110f907114941c261f508880e54907803282000c84185018001e446011450451185852a00c2d5124001040900103041c0310400200c3e60741040c3e030b8080c01e030202075005210480401c40341d8100300c0c3d03000903800c1e0440f14203281c4640c0d02c92207045810000c00c0a00305110040031501e207041c09003c0008040c0800600070030104bc2c41e0399843e0015103010703c140d1078018103900140500c080c000b40c421034210494030703d4107000500c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 170047778 1250 170046528 170046559
    0x7170307030f050a0b1f090621020a20030403050703020603091e010911090c0304032109030507060f0c12050702071a0c0f06010b0f09030102191205100b18 68
    0x20f603901111806400e59941d810240c0c10700c2c0c4002112551402c0d21105003541c280e00e0343c010854107003800b0f91f109205031014081041c0f44224005000c024617180210740365003045d00000e110302001c0590404403607040a4079024844080211401c990b400801840700500d5607091040b241c1000303010000034024010110743c40c680f007502d40c01913042c081000062580341d9241c020080141220143d010b282e8840410901049560403a03420541504195403c7d140e080308400c03031603124000030b800050400010004241c2c1103030107440395500c43c3c00180301c01100d0b80c450704210b0b40b400c0075850000d104010300d0755040d10030303510250700708003144180d852140d110320240c54080524014820504e0f00050304002c5501c051041502d031700c0b002d50140c00075500d480c901480500500d203501044007400a81010280c0d0254101d0700d81294205054106120000d0701514400070512003903aa14100360000784400815101d02003950140c46003a41000840440940301c00203c581c903503001803013209507440703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 170049028 1250 170047778 170047781
    0x90513021906080c1204080903011529030f0c0c0f0d091e0501120b0406080607050304030801080105240d2102121204030f02030708040305011b0507170307030f 70
    0x1001d07030000c034180855152240c000d080303e000504c1d102020000307004074200f4858103800590065044030405072075075a9540007a0041150b0f00b11715024001035840051300c0d01282e10480e1603e0a840000702a8081201c140440b9101c11a8000c1e4407000040016000702c509901800120b0302640849450020340303850249420178104000000c2280e00c40c00f040a040f14030100c407411048041252201303842d001c0060440822002091021501d03152903840c11f40304c0d1780c400ca000704520f01c22078130242404400948035074400d64066000071b146200100b4100360501600d4040c2d2540c1141356882c115005604441500c007526050b840941c4180e183c3c00701c1e2030071b034a40c0c0805200110702e000c10f02e450000a032400500c840c2151101030144050342c0141410213503e68002d0300340c1043c440340f8541c0d280403400d520881400910040000c00c0100c00d20405600c42d50085080b000300c201d941032002d000340e07840d004244004020840700e0680c07001c5020040c0166800c03040908011800c000802c81180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 170050278 1250 170049028 170049049
    0x2006040206070c090f02270d08030901022116020703080a03051b13140d02011202030903120703020c01150b0a18091404020a06050c120a051201030302061008010c0909051302 76
    0x1c5c1010b4001c55403080314041d521400d40741500801c45000c80031701c1480030030360091101d00054048840400021440c080c290120b421020140c000f032402d80c412850301d004480019107800040100d2140e50050449c000078581d070030b6a03003280c07019080080b101c00840181000a02420035506e5140000d0303400100b03400074101185030328003550100740c00c000c1c4000c1c1800c0b508519501c10184c00402601503604400c030241c0303480f141031000d0380d01d40d21f5018403480e5220b94039400c0c11201c05101001800f80d4107601500106250000902c51064080c4200364004410f0194a044100402c00548054000d80245201c0f9084450039400d00d65214000b0303046541500e001c0f81d03419103600801c011031800c00e05010107882e0038100b640c200121018250303540c40b0180c00340410342400007003111f110f40c0900207490420807100f0307004100e9a180c1c81c0094803103200751103086012180013004110880180201d101030704942e91981000d0346000c0c40e0802030030000d010b0000030616220098056122111040c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 170051528 1250 170050278 170050301
    0x405061e18070c0212011a0103020d090203061e060409020f040b2407030e120d050f070f0606050108060d021c140d03020405011e0e0f1305070305072006040206070c09 73
    0x180f11007455801842029500300c0030120450345002415605002680e40d14402c2d4082841c0050b112a08000220010008800d011f0351612400b000c1040d0804001000e00418140c0703e801003494481c1018001a101021402507000303201e072001d0341540c00c199002e21500d000c0208a41904088241070790180042c5610400c0e00c84c5000600000303041d0440c10000c4c183c2070580c1c203008401042c01d45a80c5807210800001c0401c8000100310000065603c1a6a56260805d5910749108080d25000d002402c940c03081da8041601c1c000020244c0c5091610b01855503000350000792221600102e0100c411000701c812202210004441170007043c040210456201b2151001640c480c2003100150a120401c10400311408e0010040200c00d40e0100b0105203414007694400c4219851300300180711501c1c0c0f4000c40c02928a0101000132a030f42c1500114011049511441c101c9030b00004175040d103011024090042e41d010b840800c00604001b030050490300c2c007400c44c4a20103600c800040d020f850111105 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 170052778 1250 170051528 170051537
    0x204110d06141302030405030c010e07061b030e1011030d0903140703050403030f0507060c09060315030c03020904081b0109020f010306030b0601030905011508100501050405061e1807 80
    0x1801900c003054859000500b0345800c803070407001180400950f12501924019401d240c010010400b0014100b00340e9010401e60002842b0b00f1291441055558446215081c00900c41283c1c031100805224502804540c140c0d950140301c030182c0c2c0900505056840610040100b03015070500d2704072060002d4480c440c06028041030b803403d903040040810b98000000040080200a0708001940107821142100d6160070301642042100009851a026280340944141d04068148602e80e03846085e61045d90082e803020001070603e03c0240700740780e0b4a400000c149110440d800c0c0050b2911100c4190302a204050300d81c80c00030300c2e00411002d01c0c0c0c00c0e518042240e440c1c0d910801180340c11060031910000038602008800d02e03548400c103a81c680941420b040c19911085a0144a0207411400d0a12614009031000c0d60340c49034a90303907400d14103814041141c07800001040342d107400d008160150340c000b00451309891030449040e496803814516a0307403200088030220040040040f0746031207107481d81c0310b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 170054028 1250 170052778 170052787
    0xf131418060108030d091a010905041407140105130308070b240108040b060a03051e12042412050106080906070201050f0c090301150b190504050d0206090d020411 71
    0x103448000180c000e0055003900800018090362000100742c4160f40318166000c50080e8080c140568540100b44a000319802c5410002c03ea000c101d0f008140070764851441c6800d04150307012811349a04c1076000d0300031103581010018000e0b602c240007801c1e2008062000b48409692a500e089299004460489014500d4020000a03100c800120000c241000030b180900d055202d00007030450768001d0006008000c0c00000c1889074070b880082c0c0300903650000071a012200303040d40300c9400d0b5000032825512841800d0704002e130920001c066400700c801803413082610b0000d40c02c5121003a1071b0384d8688410425840c1044d456007075a401100e00904c45ca40f2440702a0610041c102d060900040039401560b0600003171010702e0209800e62544054000501390325100e42d280007902620140603804128020000d001c91129400c50041641841e00d0b2112a00e03205c8400040c2e81c10300075481003a40c00780e103d0344130034058184000100124031004040700320540080c0d000500f202d0510010b034035000400308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 170055278 1250 170054028 170054041
    0x9170406031401140108130816030905151207081b0a090303030f0203040f061a0a0f05010215150d080d0e0a0605060a0b0316050405100e03070b0a05090f1314 69
    0x10b40d01c0c00b400132100b048012000d07000c0081c22051000d0324403103030011000c10803800d012880c406c0e0380141005524800c0e1100c01401c0c018034200541c02410f2003441d410482c10088466102140c0c070a0070014005201ea0b0307100c00c0e060340c0544004005000380c500d480c641e104002400e1000340f88420803030301d40000700313420350400800301d8a5880401c030030340380b0400a000c085207094000e074001c2c81d403110380400c6031060520300c4814030110101c0f00b034000d042501d0228803124a541e01d08280d40c0d007a400c561000001d1920f8000240f000c1d1241550b58031803011500c050b04014034544075540c008c0141a26000f00920414100c0d0524262280c0e40d4114040300303410050715001c0d03a1303048002251071000d003e0074901e814115200c0507202140f030b9000c41c2031040003d40a007068400a0000401700d144004c101034000e001d13410152160b500c2405109408105066003400b41c68002c01c0903550b045c100b41d408001d1024a031000d207115984812030054183c80c588081c0911100300b1445010b5440b60704201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 170056528 1250 170055278 170055311
    0xa12021f020a021005010612150f0305010b03010e0c0a120305090604080f010f0c0e06030a0b1203070b07020d0e0607020a0e0a020c0f3412030302030402030c010e03070501030917040603 81
    0x941c4c0000240d4140001080040c0c0e1101c20319010440c0c07040002410180300c00c100c2212655648042c10240c00041c0020034041c040d800074600e190140d00912100c45840241038903141c203409040d0741700c2105a01032025466428001c20240d11038242513150560385c800082040c0c0143d80581a41d51240e00000c007042400c1c000e01c100804013180501c400600b07031601400c500c0002d0310142c0680c2e80800040d40c0d0314540e4000c0c1080d40009000002c0412460803034a40702d40c0000016602c00c0081400b0a1341750784000307034041c4450900d6a401a074401003804001655210318070581c1c0c030003070615010035100e181c0640140241500580141e0b50343e0b01d84032140c1002c02c140300403060b07a003001078402d400c400864803108007156010101c4000a0914001000d80c946941124004200c007400c4581010b030183e0003580254002c40c01c48004448450044800110f1b00c1da941b078041e080150704001c0d55001c4e81183e40c030580b00c1d0325501404203040644280c2a00150b10010029440d0781c075042062096 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 170057778 1250 170056528 170056543
    0xc0a140d090303140a09030609050f2b050705010f0c08090d1707050a0c0b04080a090510091802040503010e030d0632280e070207080a12021f020a02 65
    0x6080c4062280d00c0c2d5200541070102d0f040d481c0c180c100001a200c2d110500c51405000a141c2c001c00400000c90141011651041d00c10803440f800d10990031007601c0c14500d400c80d203044d0001100c0150151203001d004417881d0300000c004403455900c80c0302d605040a05805403c1d1407410136902e040452528041c294070349080f01c440b450a0000c0d800c1020b03840309043c1c00305940019103082c110303a40d801d20700c01103d1012160304040c10100c0140144410005140300820b0900b080396120121561a01c0400440300d60800c20180414201c000070450317802007991228034243e40b84001410f2555440119080d01c4044000700b940b9040000d411001214510540000e030503040034403492200080241e00211488640d114121003140c6281a0a540c90350840041c51007500d2042141c0e050a13101c455a4071902d009a0098000b40e83c00101550320001c1d01c032044a040200a04aa5060381c079140c1151882d891035008500401082040405421400980e19a82c9410042e6a00003100000b07003003080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 170059028 1250 170057778 170057803
    0x50c07020604030609050a050703080405031b030a0f020a0f08060a1406010c0b0a11040b07050f0f0307030503090c180f0708100302040f0e01050a090203010f02040b040b030405030c0a14 81
    0x14410800580c8500055a0981e60311007000101d00165040440c50802a0390700140035124000000c0100100300000e0300c01c070f40082d0119010100a00705052209030241511501035103c1b503020f0780811038900341901c1c03090010f06840d0030151145000016903034560070140c1f440d40400148580300391603116441001340b5042010307200303040c4080000c1200f8085007028002844000206500d00455400707209040d01c042040c0fa070710b565580600c0210b070051b140036255800f075503104800101000c16650205d03184180035620300111550262603d800142019000c0c1c0f081c0c0070104010707120382d640c08041c9050881091803501e4050300ca5500341c0c0c0010000b1040125000c24041e0909814810206481e4121004a004008070101c42e00070981c05024044c250300704010301c14150103c1d07005028080c0264001c0c8040840a80c000e820b91196204409100004000800510403540c001c3c6070080e2061701902d1a10003d03240c20740c503044078140241c0300009200301d0081c002c00e0410560f0710301340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 170060278 1250 170059028 170059051
    0xa1e0e0106050a09020702100f110102031501020f01050c0d150e090105011703070309050405040503070512130603020405060906090d0503030c1201170a150b06040815060102190213022b05 82
    0xe86c1540841c424504451011060010807410050510300801d020131424419000842d140c1ca401d450f01d4145045030313603009025015005010300c805006006943c840c81c10119641c0c80e06130004035040081450b401204e500d203c10315004580c03040303094015030003940e040c800801c0c154140348001c118040b00440003d04ca900400c5000d0000380c00c803000c001210000c0718006176070b50b00c905220f41076110708440204240140f010070100809000058503030208142140ca003155104e0600750220f1046001e440d502610921100c0f040789003110003000c0c041d030041c246c0c007048407881c1d56040c95030b0030a540030300c588034000c0ba00c107003021450402c040c01403400d0b10038500031400040c281515440320b440302030403440d0000c0d40c11b402c0c0c25641d00080110070014000996450b6101200c0b6100c0307892211000344142244080782203988001030190b60344401040d40c5500d03000039800c20000d50340601c1102d80c00c507028807221150044c400180034122045000a100717404d0006d0b9000d084800081040c60003d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 170061528 1250 170060278 170060287
    0x50103110a0c02061b0f06010303020c01052a0a140f0114040206160c0b040806090c03010e0706050a03150b07020f01021f0504020d06020c0a061b080a1e0e0106050a0902 74
    0x85901c4440800c0c010f405848031503540740c40600c0d5107013a02c036089410107188601c900c440c140d03800006107e812603019038207031202d44003500c004407402d1007020200b4140040e42440c58918010710a41402d0910300c0404030b03200c50f54196500b0a40111081c4180340b107800000c0007030f000b88002e010785050070b0040041460185003a134002211400b641070801000401302e07910f00100b009004480c40a8607022903929212640c82e13014540c0da010440d10664035014004030880b080c07c050041c6820072619002400c0c081e8148402146c0942080d40c00c9001c0540301c90003200030710300000c0050b001d02100000241d480500d40180031900c2c24810003070341107500480c00c40b54075885030340000c100403550600101d1192520300003d041c410307036070201925041c800103858518a50020f41c4c80005032143c2c600b40b00d210241e00400b100700481c0440c203808642e01d5000241440703e590b00101085c85101e080142200020b0300c80c0040701ea40560850701c40c2e6540c1c0060160f132402d40d40302002041c0440d000e41c6407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 170062778 1250 170061528 170061547
    0x110918010821160201120e01020405210307150209100c0201030e06010f060c050a0803010f170606030c060901022514040612021210020d090308060906090105010f0c0f0503030105010311 81
    0x181c0c4201ea18100c000500c0f070f00b004086a200300c10780c1c04420303d4000240300042d10f80418070f00075445032162074490388414800441c400c1c904444030f4000c0031005c002d1406d200030303500d40c410240d4100c503400c25215400c0118521942c2e4000000c5803c81c6940d4a03606154801d02c005022990b03856140c12070780e840344004000352400c0b0901c29007642e44619254480a405152151400078071200040030800701000104204d22051585004c83e503205484040c1085400c8200f516402e0545400750550000380c1d086005080403001040c042e0018411102c000b5241c003009581c80110210301d4501c001490010482405060352411760b6090489040110a1825891818490004100a00400d2840701e0201000006d01204640b0100324600b0365603400042c4d80c0c40020145024210045007058000c110380303040c11824544030380009803840c50030780d00700300066401036103100c03140c02007080d1100e2020000e065030075000315881c40f41c401980c4035410040058142c6104000c00b1203240c0040c4050a003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 170064028 1250 170062778 170062843
    0x60315050f01150903080d051b0f03150a0e040b04120905220e07080a120c0201121109041a030f03120403030c020a02040e060a110f0702041109180108 66
    0x454800c0044200c044992074401c0d142511a5170029098440100c2e61100d03190542c1c1086200b00000d5009040b4841800d04030b801c1c900031241002c801c080140700184010407401144440c00b8001088000c03150ba580b400b0400c03642080303504585070500c580c180000c00449250740c01d0004960f04003819218108804200500c00c0d618050380d81e138024149684002d0620b0744800c40c190040020349208903150781d01e8a0b0340c0e044810048841c00c031003101130211142b0503076040860540c140d481c4030403151940e00290180c541d0f62002401c004081203102d03060b036a9442407036085c0600b43d078001d880d44412008c041c144801d0220342d10710740d0003c0110a0343ea0084168140d03200c0d600d418006046540404200c2c42c200618400a40040c68404810840540010014461102040309108200c1401c10849071401121226008a8414842e00c4014070b45178102d000d188014420700c030301382000000020348000703179490621080900f22005100b16a0306000071459044145106440034660101924 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 170065278 1250 170064028 170064031
    0xc03070e01050318010c0513080c010903080a020c030304140f090103050c0d05160e01091b1202180411070b0c070b0103030f180602010209030c0d020307050f1206040501060315050f 79
    0x60402c84000005510050303140e850040342e2811000820a039248991702034940d43c080100b86098a11282c800920f4000004000e0403250041e520125594034503510112542c12207080030065010740200b62406880030806080100011501040d244042009010358001c4024605000d60340341c1300140045800001c5105584906541c06040070b25103040241c00d004811141414148000d1030005948180c01c4070f0354162440e5050420025000160341c1415030010320900010988440c0a81054169275003d42264513800501400b01c2c0500c00c0000c040701d98000303500c0e800d4040898110240100e4059643e80600c0c2c0c0c5440c1031801140e6200d81e04030990512004042003014500d089405101d4440c5205409041d80c09441503030322644064046d4126101503806403003216006290b502d0a6a011025190060058250f06041c58180a11824444401c80e0041c1c00b490001c1c0b82250104002c900c41d9006100000300340d030552414607005010b1041c00c6401c542803206000340074009a407040e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 170066528 1250 170065278 170065307
    0xb27060906151801060810060c0c0509271006060207140402030c09090a06051509010c060b0301060503070801060306050612030909070e06070303091101050f0a03020901020106090906140c0307 84
    0x428214507190000f0343c0c4981010707507001110324180000034101c1c1e00880154001e18941440d03d5040f41c451800b200c0c200d85030759014142941c180800c200c0c1c0d041c0365450a8004001408560781c12204010a901d00d00e4142e1952056a0248810911001c05886800054661403028001c2145000060342c00070b0440c03803185100d1030340000032680c0d07820048121584660017418002c098941404c1242c020710151003003d0043d10f01c03e4142c1600c8000310300701c9a02000584a00340003400d01c1d121032000342100c4a01c00e80665913003001003810399081021000a240404c0045107550440c900070064400c05401240564141400c11951050102c00d075200e1110903035280b90035984802c0c048075900724003014603070481ca000801c80203060b415040b514049000320056000d9008140c011113042c4520144021011020b120443d05140b00341c0003843c89440510022034003e46410040040359414001195031310303a01c41c04004400c10860b1030702d6000d03034120000b5040d45040030b40505100d41c0712500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 170067778 1250 170066528 170066551
    0x15050903030706140a050c0f07320f10020304020f0904050c061b01050606090603040f080715020a0f030c0e190b0406050c0f010501050d030f0c0b27060906 68
    0x4812068400700250b03154240c005005001035840001551210b28050311003d06081c1080d0000d00c41c10b04210440d240e0140c030504140c50040c550322400d40503a80b0040c10001c00c015042541d228407180358000e400f00b56480051f0241d0101e90306a0b0b49401c003021010780042c5e006100b0000569558414480d0072031044d5801106a078551818506000340e5a1040360322000c080388006629016404040340386c40964020007080d1500010803040b0b0169040642e0300c03220800014002520201c0c8030555284241041c80c10840300e5902c10705400400714100c0d11031580411204421913000c034029440e01c0190508201d105c1040400402450129000714001c0214100d100803041d010455040207002c46200301d500e5640b80d82000309036510142c0803036201e1042450403e600c400621906040361002840a001902d0301c2e81c083e103003c5039400d048402e001d0741c0c0b00d031070340400c0500d01ca60303101750000c0314034031000030722280b90807030568811a078014140e111008008509600040c3da64101c00c60092 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 170069028 1250 170067778 170067787
    0x1306060e040e030c0d0908070605161103030d091b1d0a0b03030403060e010501052d040b1815030f010c1b020d021009050103050c0901020d0806120703080304050f01061505 75
    0x40051440c13203040f000e94998851003d09081540e803011041c0151000c0000360b5824503a510001ca03101c2c010b0101d0030304e00290158400d40003030310440305800b4000015050f2410526a40405001c94070b024005640800308218214081d05030042740784060000c5a1401140304d4407140403a4000e40000e2101030015a11100002556010000c0d14000e551051050008402c01e12000d03010306001e1142034024080001030144001010b07865011442001d0385207805a400c1c038040002410502100c1a004650b94003985a01071001c62018411891614002e26081d01c0c0c4e4180b5207004551001420a41d01d000542000d032a40441c88001d80f4040460030000c41c0c0d094000a09464041c0c40001c0d8807110100211341d40d950405442800ca403801d032000c02496941f00b00b00c0500b44100350000c0d005801020700d282510f8040d040c0e454000201a2459505084103010b40d40381011070381042c0d03180e5401004020400004006441100c544c00c0000c0c040549800791006420303201c0610101480400714 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 170070278 1250 170069028 170069051
    0x9030f02010822050106180203010602030d020a0504091803020c061918051807080705120424020a02100e070e040803090a0b070c1e03050901030b030106080109111306060e04 76
    0x24202e103c403c0120b200d616040c805182041c0244030a00c141402144d4030115076212002c07620030b1720f048881a402440c942810b041600d4005d6106118a0091003024000410010494800e650042000c0c00010080c03a00700e0402902c1c0a40e1002e455110383c070200500e0040a1151401401c10039441c00e200c7c003503d816842000c0350710103039040300350001010790200c040e1000c800419400b420032071325400507a40f510841285d10384502030644010a50000202d0700041d042d56245511003030071442e00058021020391340d8189d034492041580107a0140c4140d0740094904c1c4a061311400e6048001c04c0380340d1400d0f18000100c80002c0001e0603485001c800110496014844241102c0e84490500319614115102034462010751105892228048420100308010703801d040700c0441d0143c503540d06003402200110003501d039a10105400d5500c440d00010403500c02d00600c1c103d50711810300d00791440307840001c1c80522061502146046811701400300621900700103081840c40040e50045a021400b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 170071528 1250 170070278 170070301
    0x31617070305010f090218010b040b0d09050f1605190302040e2b090b070b0f090a0b0a230f01050d0305091f1d0312070501060f060503061009030f020108 67
    0x1ea00240880d400c0c140d252004900603030000600c86d200300c8182c602c032090500c07043c400000901905581d044108824411089103401070503c0c9a0745c50004520f0304641e680700c0d4240b102540101030180d02400189181b540303680d0b40300c4040c00c3c050300c030300c0c81d000d88282800403150300b01e00c0040d0199640c2c20300186803a100380a2407103c80070b0800c80300c02119001034421421021400307240005083c07400c01190f4000d02e5800c840040e90007400117511074480c0d41c4c804208240240c600c1e0300520800701c900c400614907959003841000c0c808400102c3c00840c4206110f010810001a413000d40c0d0001041103040e080860541554402e95954040301014a015039140c441c0003140790380a01a0007406c581c0410001c0c18101800f81e1381c1d1900110b628a180862915070418205a8580c00003a29a8011a841d40140c202c0138090800403940e20303503550410500390b50359001940010b10000c100041820800d420080910b0b480c609006120703d1a101c461101c3c406c110024100103614020848a44c480d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 170072778 1250 170071528 170071543
    0x905120a0212070b0406140403050d0c02070503070602010b0901080712060f150308031b031303122c0d08010e062206080109020103050a1a0105130e041a06031617 71
    0x3101c02550b5102c0c2d5013812031440c602281c0807121507003024042e4100024506840b40103c0d45522505d08100c00808602d020741078400311901103200f101c00018090340c0c100200d400074403080c1c0002660b18040e500344890078205030001049035102070310810801e003c084245840c150400c50005507011051001d0000d84140d4007201d0305400451404810f200042d40254080d00304100252100d0b00030391105250360204541c8505101c1c0e000d01da5501080c05038130909580d03940c42c9400140080c9072111042150180e82c00c16102d1080c541040d016007108001e042284031150603d04092344c9066100107041078000e01c102d0207a080c0610110104d041c0c1d603d59299001c0034402401901c1d00c400da21030090920600a0b40002d0a01012406c3c9458911032484801982e0300700c04030a00781c820040d2910383c020801e0080002c8080701c00511070207400308940c00340748650b1404200329a6200351010320700001e27111910030b0f0804002e100c02040540294003c82d1110b1101ca5500d521a540032400c0c56030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 170074028 1250 170072778 170072803
    0x15071205031914010602061008030d020903100203010f0e09031e180907210506030601031101020a0f05060f24040f0609090f140d021f0605030f0d020c040905120a02 72
    0x1001418250340f2241200c403816110594200d900d01c0c2e60346603001c0c20315412032050100d2500f003080925030101c616002844000d602034104c5540741080480f040c01c0342e100345d114540d908400c21090020b100c40d0100030703800c84d49940045003071007101030780c50007038050000c40c2920300100020111030500030024038441500d401080d42104d840d00c0c5001411100148140291400d100c0e0b0a40011040c0341c0f00741805810042c0003002160308560b0ba1385070794000ca901c4107040d07104000070140014190742801600300c2c41003020741214241959140340c0c403200a4800007440001c0000e00c001080060002003860031b0031200868802000c2544200912442d001a06801c1c1400b4180051082d0031078148800d81c4102c2074610002903c26030300742c551850800900058114031550003600303c040205000c801040c2400007101680ca5001a1a0440d0b550014603140c00c2188080c84403a01800320200c61274059405014540c0241e031001d446000500480d158140c0200d100042c09100f04003040b450726 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 170075278 1250 170074028 170074031
    0x1201120c03081308060901060e060f15191209030c0b07030e0f010207020307090204050604060e0a260607090812030405120307120506040603111e030d0c02150712050319 74
    0x2c0111103840040300940a201898817038800410b0724aa414460801101e01300b003401451520f036130041054030311503803020541c00503070107141d00e80104401d8001d2001c0c0c40403241c09035641585010181c545420011030381c0c0b42a00d4140b000001c41e4002951030000783c1d101400300c034690340e00c110a50003410b020301c5114044c85012115a8142030550007000040d00860407540030303a603190000070581c0708500410790450740500042140703038051249500d440300c0080c01c6110f080d441e03024910610180484c04d00e0000c0d51503145014000041c0b040580040c5580f80980c02d0f9401e001d200b681c3d07613041004034070003e1000070020b400e100060200c04000313060104807503a07906020030020700b0181440341083d10309152201003025840c141c4200c40c2266400009807044061071420060340240121007521442002e80f02440c807541c09010a410b8a6001d868808860f2121300501c03941070004a046545044100842c0000c2000c6e000b41c0e100c008124903141ea9a99201c901361000751000c0c010020a05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 170076528 1250 170075278 170075287
    0x30a0b0114130509030a050a03060b0307090303031b0f0f05090301060807080f03040f0b0702030a02040603140c0312091c05070303080a0c020613060509031303060903020d051201120c0308 82
    0x94600c00415404140441e881c00b80444022201000c8901c00e490080c41a03004010408075180180c0c040d100069850800182daa66149600800c541c0101c3e090400a544500280109a09441414240c10020048036040c0521031005072499096a2018061104a4082e014030301e1168007100d10011000d8000e2050079540c50384c03603503980700c28050300c41c440c041e259001c1480c40c400001e480440d080c5540c0c0140d424030700002c183c000d0340103000980c0c05008140000c1c2c05600da41c0110350066201d1081d1400e00d0302414030041c00d00c0d90640360103110303400400318440035a82c880c00390b460041c8121102101d0814030810301e400c090040701b00a001e801078a2001040c960044565031042d102e00c1c000703000c1906400d004a8840714100c1c0c40311107a60b01e0200c0b03900411200d5020690003410b10048030b00c1c5c2107080c50180300e003c500341e000f11000d03600e5000d1001016418040300d0a8030100d4100681012000c003404c2c81e503168140201129080e240c0985414031012802c0f5500443c1c21030f40b92703580c0c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 170077778 1250 170076528 170076539
    0xf1a0d0b06150d020c0c010810062001020c071a04141c05060a020304020103060e070206070c081e04090b0d1e020109031a070207050306060a0b0d09021c03020114010b0304060b030a0b01 81
    0x207034005e6500000e45015102140c402e81d40582640f0313204603c540702000c1500d05002e42903900e00991001100161940c1207803035a0450300748010b219040e010070040034480c1c54030910500c10285038503120103101083c841000041b03841d61401e054240100c0300000301580c1c41c01132038609a281d0201410b00d02c1624240006229154002c40c0124003c1c5c0c1e061241c2a01c40d5042c2e071000400b686c0300700069200c1c100003400c09100e2403031890000c5c800c5e10701d18640340ca400608444603c2c44041c00480c80b20000d02000944421300c40c92610207404e455045001d0b0302c07500c0341c1511402c81410702e5410601a038200c000c42e885802d01c0c3c1d02541d80400c1d0a20781601c032505c03814100e0012a0301c1f00252040c107801041c14070f400583c442c480d0f00000d080741003090501e005251150095401e41020544503180103006a43d840d080100301400d040c00505600254140242514409900c3d5412501c4240040c4081400c1c2d40480768800e030403020100b4401d0308000860303c2d00304003000150070240b080002144 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 170079028 1250 170077778 170077781
    0xf090114070501110a031406010e060c01090b07020c040501081209100207030c0603140601030504120309051207050303160507030203070b06011b081b01020906090120030d0f1a0d0b06150d 82
    0x1031101c00c0c3d80c01c000c0d11143c07a0107c4100e560544241d401b0580c0202c0e1007940b0318180c2c0c020001d01900074004280242d550b039500c28048000d48002c4090b810095850b460b0b4103117803165600501985000300146100341010740000d1041060310390140400c035560300c40b0140200450030045910180d0203400560f140d070002c0003400d850341c00a03031103002c1c1d001055196100e405885e0140c1c1c0c1044500140200021041d0018074400e2011109801640d803207150340c441d080c0151504901607400345549283c1011510440d41c445045041071240034004070307010035800415100d4007540031046130803079110382d001078400610200c908204040400720800801c00300e40050080c107103084440d0f80540315414641400d0340220380c420390300100e09000d00c600c81e45c40f500318800040e407425055488484030000080c1164000c0e14031807902c0d41c6070b1005541d400840d115038014a20071000c80c41c440165100022410b01c40b00380082d0103d039025010542d03564502e060352a00c080e80c540c0f2280d0385c1070000758540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 170080278 1250 170079028 170079037
    0xd03020403030f02010c0f0305060409020618030d02120d0c03020c100603060605041a060703030b09090309090601050301030b0a050c090303040807030c05060304021003110d020d140109020f09011407050111 90
    0x8000810718203d648409005010b800344800103500c94140e03151120104500a1400404c0d0980c807e072906034050141e11100014030115032400f280600150f0b901040c14942111803d0350002c560000500d010010f42c10816144c42e11540f031008200060301c02c00480103800303546004e40c030b0b6000d548101901e60308994058404c8a06c035031000c0c04215070b103900308000c84031a0001050030715200400c01340e1a20b051070040c800c2c0c51290600056480d810310118405402c201c4003224240e100141c0b40c4101d18091290b9507000c81d007460414510741c110703540c405103140040c064a40c0c80c5e0b154030220f4911480603042d503141001c0074003281d4a8035600e00745c4070782c1e42006100945026071400000f250070705007070f002c491180d900a04900214520f0310011001401c82c14003404240505100e144031402d070340d0008284441c1035541c0801d44103100c034656441420103034010b00e070b11481009035071010308041c0140d4480400908242803140c0b0f00040300c0405200b9420000c102e03501c0d144926903804100005030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 170081528 1250 170080278 170080283
    0xc08040210030b0102030d0f09060c0c051605060d09031e1d0f0f0d06151404050711060117030f0a030203070210230601050705061815040b040206070c080d03020403 72
    0x141a000c0701c14025001c40d494111a94010307001005400604055034004a0b01112020300010388107403141c50300400c4031902034074540054104007012062003c10419210300661541603420b005182100040b25403240b035111101007521054400d044c1130081e014202014042040c1d410003c1741003c0041c00c0340407500d47c03038000c40d0a0480d028001d0414016041014002511804185490400700120420200e6084915076200c550304801701c14444c0790035000b829414010424400504100f005640004000c1d07000c01041900300c4030400400112241100c20400540e46201c03100c0c481e41d411880380800312101c540d0006200000c0580c903900840c41380203a9401e03920f01180c1041564262480352400a100014040031400901d01542d03201e0380061301414858074240c0c0e2035880e01e0a2034411201d03024480101440300e051010240030070000e40254000c40c0c8040c0c42c080d9038074002c0d0180a00040e0156801080e50010031044040302005442c10600325090401211802000395000d80402c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 170082778 1250 170081528 170081539
    0x1e030601020709050405030f13090f02091002010902011202090307030209040507030210140315040906090f02030d030e120307200f10050c0306090417040303080a05010e06100e010e040c080402 84
    0x9242500341301d0b86016070340c00710241d8070703240c41680140304c0c9030804440c00d15021120031000071a440f0794440c109150180ca8030240c0c580d0355850403c88024000d401800569040403414401031303a0122066500c40100c800061301c83c0c5841010074640110303500020f4001007504140010300800041050031a4801c42e142680300794500c0e012500000142c4a01d01102414808241c005240d1600306058100c0034000143d20503e90b103aa42c25102d01d0340c02680c9800a02415030154141408007802551041c28180710207065002d28944d07821080b00c030b54410354008008915207910034070302e40b1a4001e0112202420004c001181902c0303420b0030320143d40d0f40c49815482c08a8009030b0054a115451407121241540d5403141070000c5040c0041003103644a622006450700380340c4900160015500903969543c2070314190101c042110b1041e08801c4240003084100801c690301d275524654407002e00e05d04a2185400754005030340309c4500a003040da119040c48240704002c0c0e40030420340d110718002c842 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 170084028 1250 170082778 170082793
    0x18060b0411040b0a050901020a0b130606050613060c02191824050103090c0305061006091403070303050708090a120516060206160c050d0201050402180105180a021e03060102 76
    0x200c240711481540b140540f00e40b418001d2112007400761000d4102c064060040e01c10741c1350543c1e02c80320765041c02c41e40110803011002d0000c0070b200c214800c600182c47d0964a451805070002006900d40c0c40340d00c511010440304803010070840d102c495013540019481c0516500305070711103c0c0000301d411b1104100c0200e07450002051031110242c440303901208048406240e0b4603042000440143c0740128091310361042410000000810800003039101c5d1074042540307a41c080c14001c0050020304154401c840c003010f01112040b00c2c0d540030928204032a85030a1081c0c4d14820791900141a00401450550090b003115000491f880017058078031003140b0403010b03240c04481045c01122060000d02031680164001000580f50f1000300011a07070000305401c090400d204907640301450702c0c13605074114006075160801d000860800340720910300234000001d10f0007658101070109828032071403040f40392600c6e44040425443c00907541180c051106852100c0402c0e5000f0350540000e40c02035404a0040c0324540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 170085278 1250 170084028 170084051
    0xf0303071e03020f070206030601110f1b010c080f091504090b150c1e0114010f1a071509110303030a05010609080a030e12010b0a060206040c210201030c0318060b04 72
    0xc2200d04500e145913409003405110b80078400c103070b00000c01403810310112209601e11400100101c0d078501500700010005542040745401c0e03141d42458180303051042c08105c0c000098100c0c02078034880030444a500d03885001c80000070306e00310103080c1d0b0a040700b03000180c0454014240c0d001011400001e03240c3d01d50304610303040c44034124403d605181060b50050b82400c00c4007103441042c521504425000400d00b004c1c41503081029490a901000101c620000e0800514600c02d00841850940001d0582042515119203880c140c41901c0c03000703000c0e038481e50300c010003507120720340807040700c000d01101d4480c500041004005e040038080c110224000c8170001030041c1c000141c18a40c541e043d600c01d170410104c0760500c0042c40c450b03c0c000007695220b4603003401c10340b0b9450045000f0959940202002c1c149420300c0c1d02800201d80040f500c8220030080440310300445425198100c1d82840c00182174800d03101c00310018102e03400075640c8611100194418468560450f403107045040710104280c95191 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 170086528 1250 170085278 170085281
    0x1a0106180315050405250e01150215041a04030203090906031b011803020409030c0b0c1e0903100204090207030e030f060f0c040305010204032405070504050d03020f0303071e03 77
    0x3440002c010601076040700305142010741103250800d105004555000c42030b5841480341c00800b0140117599800803604200c042c04c1190594010321441d5903802081700410b4009481c1e03100500300d0390f010b08030040810304003c242e00b03045000d441e40d1010402c0c2803c0c2442c5c000d44a0340004d80b43e0b0321514031840422120300e8003013800062100014110f10012024000640300f4204000d105e0051110b070200000160301c65010340d0840707612030f40d00c42d000c0781198504440c0c1110040c00c0d03407040c10703030a01040ca03540c4e8900c0400b5074054403104801c2e40b104a02800030780b030a5100841008001c4c00845c00080351601d0f42c02410002e80f1a40b01d9101021001040c0344d0b40c4c22002900101307a510603400b007450710003081c0c40036410075009401d0525041e00c81d01c609003680e00541c42142c5200e442403501d00c0c1030494500701d81104803a600280401d05102000410b240564020903125000d008518000c05000300042921029010103581e12450903180103030030702e040d82041419443d4900801c1e92101e209 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 170087778 1250 170086528 170086577
    0x1303031b1d0105040305100203100f030209010302010309020319030207050a0902030f0a0905070b041e0506030907140103091a010518010f030f030302120a0605041109210a1a0106 78
    0x19503110300d0400e400071501c0e0320080a881c030300ca0510a0422011005c1003052108440c0485481009039030390400c0c044001c0500c0d11235110195086904100748016507456880ca81100d0b02468007162102d564000030b41132140703003418221000c8021400c4c504158011a503402140d508481d070710146c9907101c2c0850180d100031111810020404400181081481ea2000f0302c1d0a00490031210050f071641c003c2445a070003604103001c00002c100040c4e50003884001c100c006801e080c0d45203402c42c03d148000d1035444001d40a904010002d10400004991290303114a1507150044800c02e0352500e0070f1800041240c0a0041c140910f54094040f0080340071802580d0480d20b80c11452200f6610b1912a480c006181c04000c50402d50200301585032401042411402184d4400001612516183c10403044869104410b4505031003484901e40c1a92000004980c4512610560242d880040103aa00b05203030000c2c000c0c8110008a0740111080d030300f00130613044e9145c0761903203007140501001c0d580c5608034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 170089028 1250 170087778 170087831
    0xc06050937090911040504030c080f030109050a0608061302010e04021209010b01261b0f0309070f08030412110406080607030b040908030c0a12060b0a0813080417070509130303 77
    0x449000310841405c06901507588240a0b20b054000c036084c42e901e1840a60002d50601d0810038080018070100e46d030b03440340071307000382c80c00104000d081d24110301152075000042039170780b151060a40c01e00969008180d41e41311061300030b004541c1c8034032000354001e4a94094950b0501580b80c40c94044040d401800d2240b019122003850900610050a00c0481298018402c201d103040e03000113802180e842e0f2029140510541c1522501c0b441e003800301920304401640280c3c20b004c480c9101700f1004401104903001d548052441c40b030b04040d6410b0101d12043e603c102542c005103441030010300400d0204519000e0041590f081c0b02c2d000780e8004200c151602c46501500700f40c010008a030b0401d0145000746000c1026003044610001100c01d0350003118015804191024000560510740383e80c01254141e000d00d000070f0850110009403145281402030f8052140394000354a103034410f4140c2001001d0007020002c011083d146070410140700c40c06500d01c82240480c0c01c080010084103a2141802c0326040b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 170090278 1250 170089028 170089043
    0x9020c12280c0203010c0306140904110105090a08030d050106080f040809040b0d050a0c090c02070b0301030f2d120f080402011b0b0a0603050d08040c060509370909 72
    0x1400310580481e2041020404024040c6070481940142c80a014003c1030b442d403078a001070000e240040c900604d500b10185140302c2c0128204100c0010b1440344403240c0c0c04428600b45868100c08004207c0e107105a8001289522020564403e0b005058000905a1b44941da0300001d540b0f64800b01c1c1d421610a440042c00440f0a124000d42801d06500c418850b810061140e03520a0307280d01c03280e080004441050b14050f004c0714083c4092201c40c0240340d0051124401002440c0c900b01c0e06800c80d01041c00020840c24440c401d18051000c0e42040303080c0c08103185204241d00c02043c00440688d800681c080b502c1401014100f41c00341d004241000030300a003038170f50a450b540c9680c011130f02803100303e0040c04c40a2600401d00d02007804580c1c0355100f45004d92001502608506010b4645100446040c0801a10400708030003c0d021211400c11a01103003012500c40c5c0301000081d080c0303072030400341082110724450300308070120b030900300c80584002100440007010346070004401510b44101c030141911 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 170091528 1250 170090278 170090317
    0x50a031104020f0f0a020109051216110a17030405010e0d020607170f07050109060509010c0504091109060a1d040216172a07060903030c120306090609020c12 69
    0x24101600180040c140d85420f603850082c011440c40c0260308084038400043c0c1d9500504010400700b000400303000480f10f00b41c40d0030300c8000d84040f518481946801049503a003082c603c00a500c415148070007920301c4503024884508181d011036602e802910517240002c04044aa610700c0c20040a50750445401400031440c019007910740385e403040700055000240c2282041600f5090740302c0e00140a02c5442107001143c0c02019040500990308094010745c1c00c2d925081040b440d01d900042143c00300c950a00740480c0003e80d1810900c0180103040c519038000000148a502180d0701602c0324540035101007001d070740e001e247c8081c80100c0c0901000242a0300703148100305c000c81d004080180c0052451840c151a10f44200041d5034500180a96004090010404603583c1c8600b4006040508590710702944101d2642d00d00400c00c49120001a11280c040003824401a02c03e0700302c000034244040d400c0c07006c04d90390b044030310003548410440442c0740251201a44c42d9800c00046916100c0c800c890218030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 170092778 1250 170091528 170091563
    0x5060915010303091211150405041407020312090309191d1012060e010c230901120f1508060907083d060f03030e040e0631110406050a03 60
    0x5001c01e1701c0080d1a40c4841050008080d510140703088030301400d0310b40540c4c90303610f84406c2c441500c80020950f10050384d9041006051580041aa20710051002c01901c668540d04007941c1580700700c151a5422208283e400318650800c000b0002c112000407112001d1111103040c040382201c402d5603030081e43ca007100710400c040030100201c803220718000d09002508800c04c40d030003421140c81e45601c0000c01d00b9030f511140c100d8400071202080d1200041d90a1420b9120f4000900044892042c0340403141d135200e01c81c45583c9940e00c41c0708444c5986002c1c05a140c0c4070500d00e543c1e0781c0304866450091003841c40210341c440300410040080d0003c1010341800d41c40c4030080c0054014146042e2010402c3c281d22001d004400340603000081c01c000040003a00c6086040003026040c400c40218020707810098181c00352040080c685a0000c041f402d58116a51220790701c50f2143c404192018040c02407800903402d02c107a00c441240c480d00100d41c1007046a0b40e4009020000110b48009808040707030381c904050707 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 170094028 1250 170092778 170092799
    0x910020a050c21010501090902010e06030106080c03040f020909060a05060a030807140102090a0603200a120c0e030a06020c010b0d030203071104060f120c0614040315090804030506091501030309 85
    0x810f00000b903621030f40e00300601400c540090b030000500580720211032040d542c00115100c030590065424600d190f041800140c050440034285022159000000505001300300000d010115402040c0d0040b03401c0c0b04a0b01d9940f0007080e1107600102c2e2400002c0b40042c5400f400d44421a41e00403a958100036542d00c895840800c3d44d500303010a55000c00011110341d031101c000001400d01c94500094102c6402c071609200ca50491044a02240800407035071410f030070140d80f80c21404502800b0640da41e00340402c4905c0000c08050356018410510f44004000250b0090112050418006c0184060a008020f401c00c0d1190b40900560010820030000c55044000448010400fa10204800d42d4030310411510f159240e11224480740100c004508120040541e280104153320380489110440c2c40203070410b10030b40c0f10082200e000100900f8004c0890b4001d520460380140c2d240351519507a003041600c03003004803004562030045002c000c0b841d42d420b440c00d03410b0f41e030180d1342d0450346400c2c03100746030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 170095278 1250 170094028 170094049
    0x7061202070c0812040603150b0702040c0e13140a0c1b030207080a06020c01050f09100c020a08030c0a0908010c0f1d0d050115050102010908070f0213110910020a050c 73
    0x81e01204592008600c3c0803040001020350300604040a60b00c9140001c010212400412812031014141c24200031101052050741c22132901150b0020b880c0305884029600e00710851052130b00118880d610700201d4902c0c0c2e1100031503130100400001e083c2d980c0502802151090341821011400f24045444003901c2c0c3d00860115a1003401194401a00c510120345403050300d82d8100ca21035000100568000c0080c01000d401c078940200541c4241000060203031100c40d130000c04907003a5512032481074001c2c82009404002a041460143d0b40c1c1400b5003e00629405045210042490400000741c01d0f0414420506603200c0e580e6000c600b8440c9420403a1a1040030846050040070070a40540c90785c0c41c1066110307464400c0000080410400301c034108207100c50380c889415a49044c0e001c0011518810486400a40c4403503812890006880011950114810100e101914000c6042068102500180600041102c1c3c0ea24000d2007143c080fa41d4000c0c0120003803094003c5171803080c41e810440300300d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 170096528 1250 170095278 170095283
    0x2010b030a03081e041101200c190f08160b1213020a080303070305060306010f030c0315090c080309040b150d0515100c17120106050c120703020a0b06030706120207 72
    0x100c1209038040c20111a842c2d044d241983c03074403402100e0104a42e000401610740701400c030350823110f184241010a07201d07244083c5160046801c00d043d0031005031a40903c0024141e1216041202d03616900501e54408403920050300c415010040030550304629000d440454800d520615011b40c5e40201b0400030782103140e4100d811000d0428042040e440a101840c81042140e8000a141c5451b030105461b085040c0d004144100c204001840441c81c0001c20790180c1c0d030444902d1102e1641a0705210051211150107040b1540e903441c0840c42c50000b0005007555001190140a02c43c1200204120440740034211182c40b1010020020746103400c0d04500e80c0000ea040c4c140300101c50715800714188025244441c4005441034a40d50b003086206080c01414084401005041041c424030701a0140c006003d00f6043c0480811882c800380d41c03c004802e403a8614074505070322100c562602940e9400b02c2d00e0101e52095640002807218100011924110381c615960800840300e011401c030005d40c083c0b00103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 170097778 1250 170096528 170096551
    0x90105070605010303050d05310c08070b0705010c1d09072f01050c0313020108180102041701051806060f010e030d0e100309020f060903031201170d02010b030a0308 72
    0x18034003040c560312845000354002d84841303a0390440c5000550484a005001d0301c10101b400b00c1540d00d01407400c4600c0f103601c0118034808050345035400c280156240b158030060b064401e0307100203e912030f508409485018413410080c800300405400076a004003c1c1031941000c200220000300440ca0420382d01c030340040050507c00f500070400700c2034103182202145c0b924854440c010713088000fa1000d2003080d0780120502c60729400e600342422900b4a03180d101e40064100010706000c101d070054080650240b40b05120002c41d9141d40d10a000c40e020140070541640135447e04000031801c040c03401c0d610303010f0030b2108003130300340c640d9060108848024240005810440b2161000481d6101013004555010f01030b128002c0004000d070420610760382c3e048010f0708150404a508005865960840d030b607a000855115440d1101500800d11754020010315146894092000140c124143c120030b000d010045001e8075200c41551200740e0980d03c1c80e4001d82d800d98420190100420302c40d005450300314819050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 170099028 1250 170097778 170097787
    0x60e040c0e0901080d0e01030501180e12031003020913020d12090b04120b01060c1a060607020607030f0e01020f070e060a08030328050c0717040510020703021305130602090105 77
    0x2c03810010098010719415400062041c100c13a0f042a01c40e0300c490003d280500c01076041203101050400d10160813000d060f2129900103c0900030b020421080d100060380a03124070f00502c42c248962070511042c0d002d0646a80800c0c1401c0003200360704200c2c0d4000e0880152601c0942e200c07031498100c00c4450041088402c00403075801c3c060002000200520b88404010500c1401d00d81c28450307040e8010001c0c0072002030340900140781d03141c19150002c69a5a1441190f81307043c08240f040c401c0c000c0080d444180040c50000700741c3c000745140c504404a5540b4403009903104016030340c4050090704412a40d10442c000c101c00002e02405c43d9001c4405046441000e940c0c04009141d504180c646044226508110520300c180d80c00d83c40d01e000104200030b000c43e0410380d00e070781000d2240e050054050a0980456404182c0c45801c5400804028008000c54400303900004e45031034560100f203118030624000c0c00d610590600610303014030914800d0844007802507035401c2c001d502103101181402824070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 170100278 1250 170099028 170099057
    0xa0c0f02031c030e01060b21070309080d0516140915090406080f0d0e28030b010b0c0111030402090105010f12050a0902130501140f040e010501141207060e040c 70
    0x404090040041e0320049056070040308001d003501d0781b941240b90000020b2000d0a0942c9107101000341502801030150403c0c4c444460460180810140103801d421000840c4242040316601644c0b15018000b003400800300c10301d00803659005c098030440003690090120b41c90a01c0c1081341c1c0d4411b03400245544d441e2190080104095603801e07802402c85411441001200c2e00080c041c1c0312420071540b0305143d0a4000b07030006040034103024040b1908140c85600c600074003422280f80b001035504042c0207041903030759051140300c650002c4408411542001c1c8084a2290748000f0750340a150f00400114a1b0783c01d00c8011240c04002e03d51540800c44401d000c039265007a0391140c030307010701e41c0540c1c00304050380c06005220700500d0b980c503080340c11860400108000e0100c0e4280740e0b54840b00b00d035000300c071004a00005e0080c1549440c02c1605510f404000a0640062101c98508203030070766441100c00c0035a1940b90b00d50341c00f4820000858009100d00c40d09103450b81c081c8100500900b40350090a0044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 170101528 1250 170100278 170100313
    0x1b0c05160e19021c0c02150708040b280c090906050a090203061c0302150108031e0306040b03010e010506040608070f0911040801150503120a021902030c2d060a0c0f0203 74
    0x7039000140c034036900d004010240c6d5050144030004010042001e2441c10a507400030a100e000400c00f414030b080c440c0c0480e0354080c5144081d07104002d543d100280c04440c0d0a0352a0061507400301030000304400c550000f40449181c01498201d6000600313414500d0316085150004c0d41c8010507c07644804802000300c0e8040074072095000c86030281d4011b20784000380320500039004006030400d6a1039070040c489003866526070070310b650541c040b10b41080d4507511040085009405654045941075003040d030200c0c100003055100038482e070320480b4188029650b49005a80380c840e580100303200c0700e2603c40144900101c940008203036641c1d2082d00d600d002d644044441c00c555140b112150300e240c214004201e14542001403007800100909403034030b001c207400c1c006591044243c0e292079040301b45400220555406101120a100029103100c610480c039815100919401000c100d5002807012840c03001e40c00d00c0d0058800c00010b54560142400c490b0b201d0000801c140b210032613051060040c201c2c090210f5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 170102778 1250 170101528 170101567
    0x6030c041206050106140c19080408010c18050a050102030328021207080603010606020a031b08030702030c010c020a03090e09070320090609040506040f0302011b0c05160e1902 77
    0xd042c00191075414810028a031841c811441442c1490611581800c40c002140600b11414040041c03c0454181e240140880c0550703481001c042d443e1404500c4603035000354403001c80408007483c200c1c005448104000009005001d158010303801440051007081548113000e00000f0040f5100c903a134020380402c44203a83c800785a024220407241c0070b01540039080290301760400400c400034800141040c800943d260442c1c4005401c0104801080001d4a1064180349026410003c2c0599901c2e00c502d000c3d40e2644109008a000c1d031800810304403041c030100707c54080983c5680d4181ea06441c105082d141100068010f4000b4081d5041c00000203000c81500100951884956040c6020900400204140c0141030b0f90007016405c04200024402103007240d40300b030b0b111001540101c61030030121b005108030134040b440345080142c1403504c9900182d1061810348100308407070011294034507a000040b00d07442414082da84103800b0031051708805840b040701c090b1a000040c24680000902c8015903e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 170104028 1250 170102778 170102783
    0x903020d0f1a0615090612010807150906020d030b01032a12060b07020103110712050301052d060906090301050a02041706040b0402090402040e06040b250e06030c0412 73
    0x141c40000401025840340c0d4a41d0814500c00e01d041e141c024041508668005a80100c040000030295000e03520342d82500c060703080120841000b0340e1203000340c66a0340080e00074640f44104a0801c61042d034482c01d03542054880702c4c0e003d4414440c0d40c507810780140801e18465410b060705d13070005000501a22450300c02e020208009090040c800010107051119400e99040f542400c144050110205140c11541c106a080c13030000340007911300c014900c1c14000c1030401040301c00340c403041c1c40105a000e405903050f1013045580e6a44c0c000300412080c0750403030304202c95610720560507681009290640180600540207802175203030003101c81c00030707084881c00c6030311030f1400394080303400e00405698070b071140400c000080080199003019103400500032002040280300c2e9042c400001d0031174441d40c1200718104400c0c4201c41e0309003413514103030a50f004100c2c1c1a07001c51007070681400ba50941c100401244840c43c0e19084208940d000610186510041c55000240400c010004070607071080c00f43c050090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 170105278 1250 170104028 170104043
    0x806090c040b1309031d0f010903080a030e06010608040b0c030915060a08010c1206080d09030602031b0a120507090f060507050c0d051506030106140d0203070503010c020106050a08060f0c0a0903020d 87
    0xa001207500e0f00044100e04d0306c03d004403054540300a1903600701d201c07802520340014500ba11082240401c402a0425010413a02c03402100000295540c10222903030199114804c0501a0307030711450a44101c1c0822650000c10303a00041008048280d1030f40807540100c1c0181043d00600d4651500b00c0c20345a000ea84000090f040640100341c203142480343c440a0b05280021b80360707400842100402c4120b40b400050b058590000100c1d8858210000350608a541315032490745941150740c3c094210103886024100c01410040051400e5205400f00300c19105051101c01c001380c149074049400b50410b40d0304503030a01c20042c0401c0160b84500c400b200c094441c000900c0c182040d540401140704014212070701036810b02005126001c2041c2034021080410340f540c20088020340000781c6003007200d42c0043e815510f0559483c075542d0b810340141003a528251812a43c4d03e42d51304e40903913104004c503007040c0d2110711000490390b00aa0140245400d20b85481e00c104d80303a40326000280845412078007182c058 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 170106528 1250 170105278 170105297
    0x40b0a081509060405150a0f050106030614091b0c0a020414060310050115031e050114040b0303040e0a1d0601081507020d0903170f120103020a0806090c040b130903 72
    0x15144001c842e4400468805490a401d2a6440a5440140d10072904d03055240000040001d03030140d100000400003082d05100c079507541c3c800507000f4519401140c1001001c11034190756814034050160113007055440c0100c200f04407102204ac0c503040104007407502e0040110003c00b580d80c80c0a551100e554500c0d00b803515042242c2003515225610200b501d007182081d00401003a110001c001d59201d803941800700e94102c4030800d00410001c04600c02490340e02d003400104025000700300640c100c18003a20100f0468507243c04165503409103220300a02510381c0000281a64807580202421400c10003a428100c003654865a04125090f0004102036020488510600744405031082d040f20b03040c005803040380400f0400a000c03d0b01e0340009003405030b903094941d03a240260780072030b0040e0828040c6da0352100448036016034006001e00c400e80c4220049403020801c04804203d15020340b10f08001801c6401851041c040a00404411540e00200700a2800519600c03801254480f40c42641c4d1500790 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 170107778 1250 170106528 170106553
    0x203030f030a05180712030c060c0f0e0102010b060403080c0a0b04030c03020712020f042a0504030212070f0909020301020d02120a05010b03010810020c07120c150c0c03030c02040b0a08 81
    0x115103004280344040c80703180c0900d0b40514401700d204010785801c0d42604600c1d16103401c06441c042076200c0001c00e100d02c3c055405040542c4640c1c0c1c0d0001c480c071030f40da1114000c20000120300f0394a54488881e8001c2c4208010000145120001c0c81c1a07141501624032445d990f481e000001d52040781c066001c1240e024a540c20994180107100c0a801d00e141a0480d4215030b030081000300c49400f8007140169900c25200e070030840c1c0d03c042810680b02503500507a0a20080100904a40007807104070301481040c4c42c009078a040c04030322035094a080000709000709251460442c040e00e02c0034803e9826550800010000400600003040b07205000301070140e4a0600c00b051a0481d00168000a2020304c24801440481070201d1311035510401440c002d80c685d40303158211400c0005c168401c165060700810b04104001403000090b0851304001401705103000f030117005031808058001300134520a00e81801f840000c0c015010302c28110300280000620400f82804194003010303a402000d0150300800703d0840d07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 170109028 1250 170107778 170107781
    0x8040c09020c1e06010f030b090f0f0d080a0635070f03150506090a020c1c030509100e0d052208010204050a050303090306070819020d02090a0914040204020a09030203030f030a 77
    0x110110355000130102d42d0701d08111101002d841c0d000c010690100c030f6021628814080107035004408411041d602044d400c40180c0350b5550701240060007007541d034000200c0d4800ca038410b51048507180e000c84004e0f44800d480412a80015a10012204040100c680c1195008104280140500c64803065400c2d0960a28004400d07040704120040b070700b400d08000f142d449031180160030511a4401507250f124252849043c203102e400001f81314a03940841d4541c69605800890284070503100b038907801c0700d608000b203080d224080c2c8402c69031b500c140030361500580300d500200100b961014070842040b0501003c4800c9444541c0328500caa074010074140070620f0041c0340c2e140104000c900542c6447c246d480425180c0d007000f006d02c01445020000900c0752000e0381c900950082003039404554036101507181000940181e10154007513409200c000c201d0361140c0c41a400460542d8030450b1140c0d403140d00b048040d501042c420020482d8401f8000300584040000d440c2d402e5601e80402c1d1203180c040d04220 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 170110278 1250 170109028 170109073
    0x901090b03070e01050c070e090a0b09070303020a021017070c060b0109050109090225051b0a030203061501030f1401051008160318150e060c03010807050108040c09020c 74
    0x1240010400501c00310b16000045203c5604080c02d0060b11840c01d54030607414240c0325031100342c101003103404001100201040c82d035070182c86010440703c651542c0c80610307030b90002400f0080150340b250340b0b21405031505410a03403082140d450300400500800081032081c6905480010118101c00d1100c0100419070050140c44403003031170045a40b51070071000801e180030620070381503100c0d400244190041c204004000400304010b020042581e0186045546c0745001514528104207440450f43e1626060580710100c0c0d40040c010b15181d00d6150000590b007101008403414940d0700c41100c880c0070514050284044017450010724150b1504d4180700414651850103410800c0403403c0103200010340342d4103500b01485140024102c100c1040c1d44c0c07000d5004d24405001d800303451a41c0e01840180350040b440c540c07500000d0300d1203525812120304a60000707001d107007402d41113190140000d501c150386065010b401350035114040750395004004101d9000d4040100c0d42c1e001350000c881011342c3c020b440c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 170111528 1250 170110278 170110289
    0xc0a060903050a0207291303080a180501020304060e0603090a02190303031b020304170c0a0f05040b040e061b040e070e1009080303220212010b100809060708070c080d02090109 77
    0x1030100c0d0f801c9401d15003c81d82c408841b00c917604d804142c500b9007000c1a20100042d69008490301c1d542e0210903800303040a041c2c0d2114140d48843c82c2d50100341135201006580480309a070712007100c0451404e04100c01600300520850307103403040908090241ea104402c41c140d040008007824049825414001d058034202c2e004016a03440e90141410216800001c50b81266415085103034440082e25106041891051840d40d21840c880004980007a040075500211981140c04100710141d0009000039214685d040a10310340084c0c00007161200c41264211404440b810020b140a44851054018031010b562800006101e201000c278181800c0c0c04100b52110107050400c182490200410f9a920009015424058003405020500706176551600c07500d0794003c0c14010500a000400d50003401d0511720141300e2491720302803001c1103014903403081c011100c0c1800352070380741d903a414159000710000e032080f02004182c014060100301c5060261503090a20103000d07940b845400001000c424a64000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 170112778 1250 170111528 170111549
    0xa0201060e15010f050c01020a0f0e01080f0f09030403060e03040302151309201b0d0309050c09041704060305060a06030204080c010305060102030c0f030405041505090c0c0a060903050a0207 83
    0x2485034400701d01082e075000803424079140280078100d0001325241e01400280341040d43c000b04038a1185034009505401013041e0303a403007900f8250070038011a50080282d43c101c243d940d186000c10b0380f1381d40078030300c00741e02c007140c8421603103081c0e40d960700c520840340300e0064004507410116080c400c40c50b091078420383c40440800300703d043c0f400700301032010990854810251455503c112885901400949840210301c10345013088e210169200c0701e08503903c2510414a0751701a0800204104d80a03105821602d0341000091100c000318405001070711202500075280078981449000900c0591001003003e4a01c96a020079141072810034040b254845070041800e250041c04144000710b07001070f00ca00c405000f4a170102d502d4481c01e00607800e61084848040b2907008020134000c0511000006000f105c0050798100401d0806010b4001d04405902407203501050110104901d400c0d1140a410441c0e03a070020384215190303568842085031918101280803440203c0c01d0b9520300d8044c0030700d500815541c0368 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 170114028 1250 170112778 170112781
    0x301050f12100507020703290c030108030a0e04140916050d020105070b04020f0a170709061401120e0102030f07030f092a030b0c0310060509030712020d0203120a0201060e 75
    0x80040d01d481c5500c4010240b9035490000441d401d02c204400c0d0011908100225940d650f41a00101f40003155040006014050340210700411040d0080b03030304a81c0020055800c0440782041201c86248103070196501c40c0d04d030400e41304490807418550703008452590040655440c00703150000042044e91081c0e12070f4405c04401c0c00940d0700300b011140da66a0106122401e552280300044044000c040700c175400c018128404215220f1110824280d40c5044c42116241c3c2c0c2d8030102c20003a2020b601805100707200442d484000d83d406540b0400c00381010103000310b0100f145804450880e0012142068800008010721480e503802d0310a85640c000c030840c0500c10070940d0b0300d80707a4642102407518810200708284182c0480400000e10300555400070b0120303450704001000060300c0d0803d07907143d641c0c01d041c5e41c8005045070091048a4035040c01401509140e8905071007001c4a4800e040c060340c00c81e00d08184140180d0b001e00010201a030000003d60720380030750034402421100315070001301004c0d2502c1e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 170115278 1250 170114028 170114059
    0x20706080112061d0a03091a030c07030f020f0a0506071b11060a020c0d0b0912030114040525090303030e07080307060b0a1502030304030216060c11030102130b0301050f 74
    0x60020030364002501182c501c43c411100a2080811015605207006400c2c1600416034030204200c01c48c1c00044094180002400e486016480242d810002c0d582c01000040c000901524499456202c0390040d209400800c0002500f171585100d02200d0642241041100300b58000c00c403c2c82e0000c1d89498a00300c20103503525601c2d0400e12002c40c40c4604c201040c4901560310030891001031444c050401b02c0388100f1850000401803040e200304455000b00c400c49840e52042405580c12200318058a50300d4803d06800d00008282c00740c000350034919085004108046400d5080884101c02d603a500e4100e441cbd418010100c801c262003c0d21035400c0b921081004090010a54060b150401d00c000f0b05044a04006030000c5807a034050446000b210906105082c4c02101a511844c000d80035100c0301c5a13854000b0100b51454010440850b074022741e81408a100300b001000380c140c014000500d0887c2c540c10302008a003441e80308407a10200040140030b070341064a5891507010060703a051301c0341d1300040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 170116528 1250 170115278 170115299
    0x50a02180a0f0219030e0c30120307030c0909050f0703060501021c05090d05070b0d0c080609041101020106080609010c0e030a170328090303050709180908120a0c0207060801 76
    0x60241e001051b4403103183c0401c01c1024030900c1ca094000501c088940c0c694908002c8080d11209024001c13421120810208890085200502d140c0c514503d28655501c0c9102030300144400c00c901404c10201a4010458103c180700c0d05004640103444c070341c454070b040a8020182d488503081103046401c03c54082c04117000c00014482c260141d03040103912503d000c00400c1c00000f0307007400503160340700307441e000540e00c0c44000052044903548202440442c1c2d4005040d9412001928071641060f0014009004500d2204013454602014800410f5541e50f4140e114501034007070f214501c041c1d41d14011001072076085071904900000c2500a02500c4219846d10b001c0d064001c604070040d02700000010f00211031849808140a0205c05002550b00701029881300501c0a220308a01107481c2102003020a4020a030120440710849100945c04004440540147c45001d500300ca21520520030070703160682401c0203c2c8a40c408074400a901c5080e107030000e1920380340c0e43c40403051002c00310040c0910b0000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 170117778 1250 170116528 170116567
    0xa0609060f02190b01030b010b040b04122108060315010b03010b0a09031a060f0609150a12110304020301150f05040c05041512050c0c060f04050a02180a0f02 69
    0x15424400007000d1112820790a100709800ca1407284005040840100b0418a07245410782e40118100c5003540e0321f48010000c98030450180200940f8248010403a50300c10f0340e40060050310486103140b0302c0ca103c92229444660f039510050128980c5020091941020440810860300c0035032010031035450481c1202c0c0c04d100c107010f140c1030480002604e410640c003642e0b9401c02140d1100403804415451756080804003020b84003180700704c90380000c070b02192422030140d440445000b0b00305a00c222241c015008580d220407506014080141500e00640801d03121340c001ca01c0ca80e03200a46e0b03a02d480d20415003141d1860f17101e00f4000e1400c0e403081c40000d00800c034040c203941c0f040d0707000181e400d0028001e845c50700840d0300205003060150946804a0380c480740c0c1003034035620702c882880592208c3d05000824051000d0010700c44c0e0051001900d220300a412142d0018001c07402d07a00600225000308a030720300421403038800781e4420700a0000d031a28034856418014004142141070404480070300e501d8000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 170119028 1250 170117778 170117789
    0x150b03010b0d020f060c03180a060c03080a0c140403030206041401140112051e0d02010e0616031a0901080f0d18061815021e07060e060c070806040f110a0609 69
    0x840780c10f050b0300c9172030704401c0310752a0b000101200d031160306042c16226208159150b1038024108030307d0000c0c0240c0109103030078009038591142c04403541c3c3c2d0321544008216100d08403040007189610007801d290760400410103036000f035000d0019440c260400c901d00c011007019806050303150262504d8a221146080c0f410b4600b001d000320035400039810102e24150f44a10404901e001c040251001150300041101c0c94003000e800920440004c0440340c2e8640b4012240100042030117000d420710f903482a48205020742c411501d0819800c10f14010a603c00030136009282581d000c0804a040e500b020451800383c0080c0c1c1c80c00494841e4400d01d4540011018880c0c101404110900349100703000e80160000580740703080c51681441d1f0f590780d00966490950009650b00c104490840c100c14030085810000d6404a46542e640700c5940c900f0b101c00c03580100c0f49030000340034245000c15003c2c0c082c44814000c0b401039941045c101c115090280760740c80d0b800d0340640f1a42026108200b90394104003482c00315203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 170120278 1250 170119028 170119039
    0x6150306010c1a0a0b10030504080406030207060e07080105071b0c180f0504080a12020903061618060309060605040b010804030806010c02190305070b13031506050d150b03010b0d02 79
    0x202d64075003018102075074010b00c040c0c400b40ca8204000075003503500004441c0c0c0100c51400b100a00d0601c00e03411554156000b8141101c10081440802c0c0641c0081841c5881124006284204100d41c1418890140c1120315613075100c10900205691001c101d400401018080c03001400581d968000000f40300d11032016101b2611810112000c0c481d0302042640144100512491901e40b0703046229a0050100c180441c410300002e94111540b03200741c44400070050b006203190703251844c10325040006002c00c070003000348000340c01d030f82a800d00182d80c00414041e140030030020020714114040c0d0303100da0041030240d85030880e4000f1907130f400880650440c0e058180540d80703845001c0100e0340b4140c5598040d42000310004801204596800600300b143d01a05c1a00ca40c01d8843c8650500c0384180d20305211082070402d814800f03d540c41c0102d402d1000c10041c0000d05541e030308042400b0003500740040d071b07140b02c50f002042e011070402d002e0f6042040f0f00300c00030024504400000388004004680103806403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 170121528 1250 170120278 170120297
    0xf1d09070c06050412020f070f05091305031303050709020304030804031107230405010e0606030f15040e030c0105090c0d0809040f24050d02060409152103080615030601 74
    0x141d019404892a50390400c8041c0110301d09800c142c04c6418600d40c0c000c2c010b104510f2860707040b00001c00d4031820788696010320715140786468100511550094001402c0e2100d41c144407001075810001080002d41040c00311102c68918209542003840c9603000101440c0104100310000ba4881c0413142d1103a410700f403444200c1d542d1482c1e14a00517098000a0324803042d80382548103040c46440a804100084405000981c2c031250485060300301a075007650000d80c144003050b03040550030745565100c1444000c121070100b800700002c007560020340c058080c5800004840d07010b00b00138011981d2080039800107080551b0f4080100744070744400304025102580c0071030918000d503619081020780010003202884001d99501440d0150715496203050041202400700144da0b082072120340c0b00c8a6002400b09080500d401e0749500902050b08200d440070095900104940800c041c494419107145030040291262920f4080d02c4070002a01c0d0728454582d003031200000091000403030354407544c20318203500107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 170122778 1250 170121528 170121541
    0x1403040c0305030d0609060909020f010c11041515021c0f1205070302040e01091413020102010902030d050c07240e01090f080d0e0103021204031103070c0b0a0f1d09 72
    0x1503121540004000d80000103041c9412001500000b098a008034410400355030354000c2c0d074040300c110307260003500159403e0004c0d58541c010004c5d8581140125204807110302d5903000a800c884d1841c00810604840120501c40c00800040003000040d00d40000e14848015901081d00049040d10f40001c000d9800030b5001a54440e84501c0c1c0713000b403010001d1241b030500036000b401075041800b0341e40d1540d071820300010740041240038008600d61104d07030100c1d0a4480400880410b05251401e90541d03488a55400040e20108210314045103030ba41c815803514202c52025050401d00d40c08900d02c00e00d2035650b42e000245a10a020103140e0301c1c1451100c001c1d2510040c1c0748180941e02c1440c4001d118100002c1280021a403030301e80c06d080e23640d200c400c40741280056089000d01094040d030318842c980024006401601003440884104c02103c0c105151a61141c11a40303c030380004000300e0380442c81c0600140c010300c0c0c042624400d0b0400c0506a041c080e030441d000c0701ca66170380621514017000407400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 170124028 1250 170122778 170122793
    0x3090a0e0a06080f061e010b090d020a03020303071a070207080303060409050f1c12060b070b07050906070804030b07022e02190c020306280b0616050a0b060907140304 73
    0xd001440a989102d98010f1884d602c030a422100c1c02045c42c0050201002c10051800e41c034180d4000d0401e0070709183e0308806201000d003103840b003240c12211124011000d654100003811b40c4a1055180c3c6111a580074030305a10180060045400e65200306424081c0e0a404070582c2d50103101910b002484000c0b90800f06d18142c4042d5018030640610910300f01c0d03085041240c070f106200d0949600c9c1500100c60501012a01d0512850f90000c1c0280824000101417405594021842d46011130900960400245407584940c3c001c42d40318400050400030025140d20503540050703180060b02401d85658950144128008408980140c00540076000c0158640c156250742107219502004d00c017a90790003030140700818000b030b44244074800002342620120320b50f540b03150000a282e207108640090b4240c014241102d8065440781e411300c51001040101c21103500300038001e40080200051b00d0070140030380e04025025030300a1302240100210f00741c00c41c0b005124031040780204c0c0d40d41d83c1d603410005d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 170125278 1250 170124028 170124041
    0xb1201020c0a0b191b020607090b0715060308030c1b0706020309100c0c030309140a050a05060903030708071a2d15090103030f09090e12130b190e0303090a0e0a 70
    0x13018240784c80050b9000701280000b11411085540840c0d4440e203405c002600c403c102e03480340380120401080600b0015002c0f194014012610700000302d0309603102d03a20000c0d20740080b84c44c40d01000c004a401d5040552032030300a03890068a0780a000c0082c2880c000a45074842c0a071054007607800300c081242854803030744406034441d0304000100d4030551a8a030051000c1140e00c078041d46420411081e0b0341c54504003a60300d0440d8030080c601c40d00c0c0b030b00c0d0405220180e00320030111941030100740a814042041c490007003464078400c501c00031382103411044050076140081c20201d00340e801101c4007503824000600ca0003149004001354000c5942c1c480500c0b0845600c02c0700c10b82c003c1c8100000004164100380c2d4852120305130b4590800d140d88844c002c2c01102d180110038820b6a1022500503002064a4000c140740121803408610171038807008090701542c000a42ca0642c800d9911719400c0e41d581c00340798080284000c401440c86c001940c40040c00b52842805101c0d10006200f010906000480d40300b00e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 170126528 1250 170125278 170125321
    0x3030b19090f05091b13060905010902090a3602040b180307080a02030a0816080a020705040b06070f03030f0b03010f090506010b04060206011a07060f0b1201020c0a0b 73
    0x4032155a11910301d5005048000c1c2000340c40350520b40415149035010558000710501d4800315014000c0b08820000c0820030b0554540a0b196189030100c5c88e01075500950b406881110307405a901d444460034440d101c6211780c440054a0032101030030b40d01401c0131002c4169017140c00d00c031022000350084040020702c40c035800b0450b5018001a0320440710f076040b115403000c82d800ca064078130742962007074003980b00c01e083c2d0030003580b5401c10140c40740000c9455001d003011601c648561034007546241e4403c0d20a61201421a02507803001c10100f110740b4141c06500145101641c00c141054641e5036032a8000e014a2001000e258079040303041e1416150b03901000300014001d0003405501d401075444001429124416550f50050400210b450680c200807503048900a82c02010240c5c40c20307aaa842c114111820440c0140080006001090300c90103102c0c1c1d8288110400540300404c5030800941c2210104505c5d001c0e40140700c503d160440208400300c40c0c94100e161580b455845421b200300d403404500c1c80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 170127778 1250 170126528 170126569
    0x6020f250e04150e01020406050904020d140106020a050d0f0e010c0f06020301150801090c09050d0c091b123803060a140705090906060c1e0102181203030403030b 71
    0x30001408110004003407203c608540800408405620141c207070300c2a401543c020410400900d46641440d43c002c1581e81d94991001a045d001008910890303182a801080140d20280c401018460140152030443d001d909016401450300e04000d08501c208040450502c00418415810310080e40246001982d000a00b107503290384520030b601e40803aa04550500098401002107110750240c41b82004204658036080b2a0610740820852480c803410803c0311070303448c801c10002d290304140c050b44884045045800400c0450f52600511740c4402070880c251103400c1450941494074611101228802c415a400b611b0800c02c8030041e10303408100306601d4141c4100000c00ca46003903c0d6000c4034206038420781d01d410703549070900c040314140141c240e4141d1103510240420f65078941a0300030303e51100a641501c101c3d42d00c00b0300f81c0900c102440751300c1529940020704041c81711001824102c0748101246c480c1076003104105501e9490000901c001e00381079840c501c03202903541d800c0410b0240c82801d8907 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 170129028 1250 170127778 170127781
    0x2103170103150b0303070f06020c07031704050906030a03170907031e110111060a0c0c06150509130312020f0c0d2303070f180f0602150106020f250e 65
    0x41c01085080b46000c0c034081585860281801468003004550070780340c0000c01114108140d0315140003d46c04200c040e0f0551040100000000c3c20f600c400e440e81c811385030406600c0d00d240800303110b0b200d8070003414103101c0d4000c90a2000020380082c40d800150740703000810704995540134107440c50b056141e0009003200c5601600488040c0c8a00c81c0d80d00c51900c80c80342280810403401c01503c0c614012684030340141c04c41c1c80021402c0c68030b0b90100841d0395045c544010000c1d6a612518203c80b114140741c040080f2488041c0034605060f40e14a030015880030444000c180107880c004c01031408008840d40341a000111904240d052a0503507903401452000e031008030000c584c0180071082494004100203540e00b41e0341c2d0750000c00301c0c280d03482001d031501d07071005140f81c01d1000c41c2c1415078048260241080c0384404540466038803117600182c40a900101a10251158203400d6498142e0066045601240c4140e448040110b18000084d00082003407001040780c8850100188507904002c85c0340e40480c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 170130278 1250 170129028 170129033
    0x8152a03150f210d03110417010603080309010b030606010810030318050a0e0702060606041d04020103060f0602010207170a020d0f120c0503150301061406070204110c03030712062103170103 83
    0xd80020500f4101c1112502031071040241d0968800000e02001d40e80f05010420000404207007480f0440a0100001141522543c9007000c5030002d440c900d200c1e030356510080645040030407040b8ac00c904242030240340d606c0c180413501d020340000e000c01401c01182c2c0c12144030740c44000e420100500030044c80a003a80c3d4a900380b600840c2000c544080040c491480820164103100d004c90f01580e040384d02c001200100241707c0036a018000c0e00480c10595285000902d107005121100081c000960015a560304182170105100700e0030800c4519080041042044032600001d03403080300c0c0c041c0c5c00e1107200300d00804c0301074880c0d20305a91141402030500206030035480d4010b00540c81000c020042c102d00030340020a0500700c1d0224020340c0c1c030030400140c2c3c600c09031170048003420055100610200d049818040b810a0320340124035520f000e0f91001c030074451082d4010000500040810320104106031400d5442020702c030f4011122141034909980d00c8081c18843c0840b1000c24415903508001541d491 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 170131528 1250 170130278 170130319
    0x90702010b0118051822050309100801050901171207030903031202030702100b0f0d05010603060b09090604022707080405010f0605030703170408152a03150f 69
    0x106020380081d0156881d840903c0c1c1994840f4182c6001801c1c01c0300140c0341c00401c10400341c0290407010100c2c107458034083d0b4800490203004405110b10042d5031106004801c0c4800088100c4941c802d000303414005101700d45070580c4142c1128240642d4075040c0c42480192810003c6540f43e484100c0c200240007010305800810314022a4883d41c2c1c3d44d15222820452001280025500c4030010b8100e000d550500d401140c0003400101001029030f1541d0305c03103500140786840081b1088890340d44618040092061601c234010035008103807040c40840c9000e40c407042d19620020002403040b803855000c07588260100c01ea00308161a564091a180e092126010740010002c843c1102c441d824200759810b1890580101d2045410180042c031140e411a40c1e0395030906201c03030307c20a509501b8440011501800c21034020f000074208440362143c2000000b50034081d440e84042403048100103802c00340d40c80107174101c0341c2c0711b000100e4020001c10108001007401c581903d00640c8200d03194510160b11011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 170132778 1250 170131528 170131541
    0x51302040608070516020d1b03150b030f0a17040f0305211602060d021e0406090e0f01030209180601142e080703140c09010807090f050f04090209070201 67
    0x560b11040580c0d9611001150b42d442001c840105020040000c00c0050800604442e1698460791b5010500104041007080c2030010f41c2c800d981c0d00e0130001c0381d108a00d0451141d040d003243c0590103080240c21503090541c0c2d03403600e5030340244088003495500010f070703600105407000b41001c40464410b507907607800c0c5242d89a00030b8055130132008010125024a03e1003030b086407042e000200c56180c200385d0070340030400f0070b40290143c0e442c555020410b1020b5006440300c1c840c000c0c555200303c9611581007020061180c41950805212101480240580c0342114860941100e9044401030f034281d40c1c1c00c030640c03900d06e9101072a204a1040400100700c0e04d1000e0448194880c0580f1040c000c840070076010030f50080e240811603080000001540d070418414100b0b26400160303410b02180e600c0090580c01b032800300460b400089600e000c42d080c0440d6901800c050341003115864032900071400c141080044118600c10a8443c0f030030046a040c1580f61b07032b0018041103400408054040c540400041d001c0d060703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 170134028 1250 170132778 170132789
    0x1e01020c0a20040501080c10050708030403030903080f0127091209060e06190c1a0c0a1d0112020a032705062202060702011e0914040c051206060405130204 68
    0xb088112292400d1500c1500d048442610003444400b4444050144140c040c0c06810108001001050701080f0b61000039070059101c3d0b500050200800c3c14028070400c40039155007216840400104a01118100350240c4020251003100c00b103002060500c0061148040040202e05c86603045002550004d50340c0f01100d259841352502e9008690400c141440395241c00c0340d10822000f01090614030a80a50034a07a100c9ca034440d403d010b011481c1443c1c20012500086400e0740003400c0c200305907100c62031010104007000c04054019007000040c01c40782c440d51010a481d980880c1807443c2c10b200e60464280710604401e0045140d44090614400c800c600409a40911640011600d2800124002c110101c00603845c0380321844031b0b900b0807442da80845c40030b030b04100ca42010340a50700082c0d0184c0e021000b01e0344030810307518900361440c405881c46049061185182000c1078040e41d4010b01115800c1d40d00d00160a496594800000c105000e03130b40200f5000b03400405101d901c520254014000c4e00c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 170135278 1250 170134028 170134073
    0x6080705370e06030c0304060b060403151d06040f170a0201020304020a0b030c16050703021e030c0f060d020f0c0106080304180c12020a1713061401081e01020c0a 71
    0x100c907041d040d0b514020503258140c100008000045a24000c2e0028540181c4030700f0001c076801d00740c81c1c0007030010340054000b40c0d404001c0b00341c10144c00f980c510074100d00c0b04106044014a0540325406c030b450341070060000e0070320700484d2800410052040742201da4200b0f1065000d844007a6400c00034003d4004403412809500005230215115944206480c82104074504003860140840c0300c01580500b0081c007104e1603c03500030302200607030311480245c07100b44e0040341d5031064131a050304051030003402c003c0403805158410f0412a0a856220031035140c402030141c0980d5034074070001118420300c06c211400005500c1c0c010003091915005c070083c42242d040301c1d0360019000c1da00d0003101c211454902c1300b9000c07030034414090b02c19040c40e402030894030b51a81011201c2c0c0080c1000b000e20911700b10350440780e610000170084204a03441c0700c1c0f003169035a001e5a040301ea40c1000b44455440a0341a06041031400201c44c014440a007501180d081d07480070000d0382c07181245450300c15242c8001c1410000e13100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 170136528 1250 170135278 170135377
    0x1060801030c051c0507090b01090816060f0e031506040b0d050d0c0515010806160212032e0e060310020711060c21040f080f10020901030b0901030b040b0c0a0906080705 74
    0x11600045882c0c80c0c02d0414884cc450a25102c03069800488000c004801c0c000345410380207255800b80003004800d50b02d100c00900510f00300c8104000c503031210b50414807880700d121003035010403030001e005440d003030090406030b190b1020350078600d01d0400201141084001c41800100c1d040001243c3c0358003820312010114103189e00c804060340c031a02000c1110310500d80500c0050780803410310340c94003030f0080c00c400000e40900c501d184683d401c01658122005440b5201c0c00d020040c10704100b08a0480341e2203804608000441e03645904025150f054a80b1941006c507080b0f00382d840601060900c40c0e141b1801c0c03140b8900030080c090403904030780f0540001400ca1103000650000c0880d9170b40300b0640e45400740000b98049100040250402c3ca55107040594505d0b0341642603c0d03002219000e14015078401406180c01d181440d2910402002c0e81303002c903401d024044010703030403509100a446c802c0c00c1082c00d9035586241102c10b03000d480c51440d100200c0c8081565481011a4600c0701c0060152556184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 170137778 1250 170136528 170136539
    0x2301020303070c17040801181403040302130506060903060106030b0109090b0607030809010e0d09080c061303060506060706091203050610050708030c09060f040e01060801030c051c0507090b0109 85
    0x12404110703002c40102d04007420340300000c2d5082ca0102c200c1c00201c0e8a103410143c0b60000f81d030846005007061240030b001d03005001d00340902060689402e04140006520305429a4081100400d5005601441c0e50300c407004500755503114425101000382c040c00315001580d6681e8024081d28003401c0315401b04000f20300120b074460150250100308130001d0701c10751410300c83d60b40484403c10000c2400380300b550b0741c1c1458600c1c194248040c5000004941c5c0e0002c1039400e21803418101410008500d108207010442c92050000160310039044030b4009100080039980c51000c2038092003406401000756240081400c10840f0040c40399481e900d20707603010001c9a4410050104031102c410f0200003041090002200003600040155404600c44580c07500741107000c0045241c41c4c01400500303100d1b903404242841400700201042c1d0040c0701a2402034855451515024200c101c90700075103004407100c8000c040c01c0c810590004030490351000031200540d689048080c010403542c8850303400501c802400046 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 170139028 1250 170137778 170137783
    0x9080d06090c05040302130e01060b0901031a1f020106030b04080c0d0905091603090506010806160201111e1b06100b030f22050604050c09070c0f03030b120106230102 73
    0x38902070f42c440368a05410f6408110300d00c0040c0d04403098098440680f80726002080c02120018010281200c2e01c03024501c002400366601d1200c1c00043c459881e05030700c8640d50f42d02e1813803100da00c0ca90083c41c0c0c021240314103c0c054103842d040030b0300014501c0300f840104049a0010f01c0403e20000c2900c5043c10ba0142c02c0b210315200f0b20885500a90344004107144465085444040111030b09001664810541e1041c0c2001c0099110341220b40142c010024400381104000245400501c000c01040c50801c9038141c0c1270280f0590342c0c0d00c000031801c2c0420b15103c0c030412030b12406001d03160800d8521002c0d003810354402040724aa2440007030411300142c0308000809690185011102090590b5503204001c01c2514910614400ca01030741c12083c4086031040c002e480c010350181014042e2001400d0a01583c680c02030701c08410481503420610200d503143d250b0b400071030342c14900420081d0100000599034199000c1520343c82d4a000c03800a54440450038010080c5c0102507404a410030590041e078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 170140278 1250 170139028 170139041
    0x702030301050103140f010b090316080307031b03080c031503100606090b04120602130e040606090c0f0f110106090c03090209060415060806150c01050709090c021510080109080d0609 80
    0x686c801584801805041c0a04000e001c8107000a0121644403400c070314080d1910171981c0c4400996003000800c9424968445a5020032120040e030114550000d0340c2c008007903682c010f01c1226102070100c080345c03401e5554000408040341c01808c0350341800e030840780c0000070500f0740b2038200840e0485e0b0f0000b90b813041c0720301030b181200c491100c441c1d42042c132070b1030b600045d6101d4440c60000740b14195010400f0388808401c14002c0c3e0041d50001085401c159029080320901e07046242403015a20050342015440360085a0340b204c07503d0041d100d00010040e00340540341d10b400500c1483d06082140d552194554005c40005000311011286615450240021a2040a4a48501c004c66002844003038042c990190704508041c1a40011100e0201c0f1000f140d0041c01030001c6c1651641c041c80749196110201d0000742400c10300030083c0762035004001c0e42d83c0c04100301c00e99211904d2400550360802d03803c0e400d00100180d0000740071100d070a141c00b00c2a41c0c400400c0c400742c2d0340713860350206921b8454071988 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 170141528 1250 170140278 170140291
    0x11b050d031b1b0804080d09030c0602010b0603180a05061608010504051519120c03020102010c030c05030115020c0d05011e14071407050a03030b0f030313030f0309090203070203030105010314 84
    0x41400f02c400d690424591948614292007054042000041c0c0010400802c1618000da40c0ea00407100e0030342c94110030860700c07035004100310fa0501d00d0013480703913035400e0803641c00046032180750b04a01549c001c243e007010b050301c0c40030780580258801c000c0403c14003001503000d50501d07030f40c9003826030300d41c0c040208039102038031522071048e0300400310240c0d41001014040d07142d050250000700655500400603071243e41200403100250403400801c00c65809004808000260313040a014501a0b03801c02001e50005128000c540000c46160405940c028000c41910000280c0318003e102c01b5800d04901030f1080d00209003810701e1f50b01080b40315140601c0303040c09243d882c0810b0203c45d2561081203c0c0310f140580400c0c1d21107002c10a41000400400980426511a84002c111b080110040003941200400300354001d8108014030000c078181000e00c041034a9100d086c212940c0858101160300c1101034000303980e503500c0041445034240d0004060350480f2001da030188054070503881084500d100c05d60b2078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 170142778 1250 170141528 170141537
    0xb0a0501030917030c040b030709090c030b090a0f0204081c180303020d050d06120b040506071404030206160c06030603110a0311040f020c070e060906150a0509011b050d031b 76
    0x481c5480f10903c3c011900074101c100710509040d00d92060384419403040c0e8600303012070560003081014500074020b0100719101410b00704001031120b40860410030b8001c0c0000c0381d00d6a103441843c03521450780c0c103031005030180c40100c80e4000c05100b04030f480940800c0c0b04002050002c075444c190b0045022803101a2079040e40600030711404030101751540c2e000100c1070b8030b103540c58040100300c4160f0080014078803400f0311980750381c40c04c0030300b805403c0404c00707091a420800201343c03440b0031400d0002190100c99046d40c0c003a666220300d40214031404a0b13040d005000300581030303000500703940c150002d00030b6074052403c0000780107a0000300200d014840c480100070003184103a881e05407402d548200d040c0a4004c80140c9040b20600e0040c1c10440135402c0140032120020034000c40b41800c0c080310394000000e07a5828680b000c1c196070407000d0300404103102d00300200021805c0203a48520f40c03a03100c0703503d07803e43c9a100c140c2c10319009441c0c002508040d00040e1600030f540404030482a00c0d444d0310200c0d07888 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 170143884 1106 170142778 170142803
    0x702030a11030a021b040b04061d01080309131e0c02030c0c150f031509040606080d0305010f050d08040b1801020f010204030201050a110a0c06030b0a05010309 70
    0x4140401c0d5000380600002caa800080c0c0f8407031a41d80f0062007066503190350000d005080e01d07140e840c1e0403078201301c00010302e207961380301803c000e0000c40c400f02081d0f0f880d119455a030b4000c40b81000e034820200380d000e00202d11190321445031100a669040781208a01c800401551039101c031100c01079000041c502c1d44240180300034007009104480e102071000f001c82c1c40d00c1d180c0c05400d0690901420000100b01e41c100d10f00b0080e40c007012b014124898618003424004001c080c2031155484a02070028001d220718842e1080c141030352880074580d00813078141000d01560005d450011980d8001c10040458400805400f6004c499000200601c199000600090410904402e54400741c0c0c0144024030040c0e800000355948007049117881544e0600102c0340614094a03c04080c0030702d84400745c04152030394141c000d0304a1002c152020103a6683c1c0303c00450032140303d51400783ca4520100c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 169964028 170143884 := by
  have h0 := BRFrame.cov_init 169964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 169964028 ≤ n) (h2 : n < 170143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
