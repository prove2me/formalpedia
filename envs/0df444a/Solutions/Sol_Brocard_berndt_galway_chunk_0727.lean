-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0727
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:26:33.512451+00:00
-- url     : https://prove2.me/submissions/624b2caa-3b46-42bd-acc4-f182c5bd95e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 130575539 ≤ n < 130755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 130576789 1250 130575539 130575547
    0x31b0e04081b0703030507080901030207050105040b0402010f3603150b0306010b0301120209070216030b010e0a1116030905060a120b0a1406090d0c12031e0504060c0314 74
    0x20744141164055070002e9680780c485011070000d00d8010507902c0440f0b6041d00c2d8207103480499500c500740d64200070030049c18036600380010008103c0070b0081c0b0b8407580c41882e038085203140520024003a0080d503207160342040607603000800818654000c0c031101c1c41d02c4c2800e03100319046d05080c80203403101780d0308005c26012201600240c1002c0541101d506440d0480644400b6030302c40301c0c901e110f40024842c445040700d450441402604002110b240c00c203007a403050300c1100d43c40001410192005134022140550b00800421607030031100c1e0f240c1d400420511040c4814181c0c00006000340c000c03030350f2014104503000b081c601018001d41c222001060301406480d110b01c1e144201900c0d807981c5884400701039052912a0225103040800c80c0c2c1514101200505407003052001d010568003d0b0030b140c2c0d0000d54100503040441c2c01130030804020103103041d01640304c0032140f800518440001d26032984031241e94010211158101c0103030340a41c2c007540307480c81014041c2e040445001e09628440030f50702500003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 130578039 1250 130576789 130576793
    0x60602120a03091b0303020a120507020a0501050310051c05060606071a07020304090516020606010f211d0c012c0f06270a06050313111906021018020a031b0e04 70
    0x890001642400341041c4603400071249c10544d04c92246c100000e40c40600e4120500c0a580104081d41d000200488808415034032540491020b03400604200e2044564210006c20480b08000d10b55110105448050900341d881e134800c6800d66500e41202d010481000c0050b000038400c1058900815504005005904064aa409552451588041c014001e41c40000d100e5400b840c41d40020703140741d0352002c1d0320440c610b0464552100d0035085180d42900c503941c40300e101038000d4000b03907201c0900340030b4040b40c80010000f400d42d5001041c1c190052403036000035a104509010baa1910340030585040b900d084608000445a224022a1502901e2501195044a08508404008420103a9020b0b0800c2c1d218a419145e501084807542c0c030300e0152103400400101c11102481c0b0303807100541583c9580043d0760340142e084000da000f400050303000e000980e80038a007a0240c000f03c000000d40e00041085140c02080e49207000c2e0101a214011a6420040d04e008080c2440b00400704070890310f209013024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 130579289 1250 130578039 130578043
    0x914060423070f2d080c07020607050601080105130803040f08090607061a0402180402070c05030601180f090b0a0e0f0a03052109101e0c030f060602120a03091b030302 73
    0x88a85030000840c41041851024602e1400c2c0718202ca0190100f000c0201d0070804841c0341c00000d00c06451b09605011880050b2100e80140c01c159102c0c1c0040c00c0f2541c14082610b00b1110010b0049603031030312900e90200462000c40c11030f904a600008074407400e8080e4181003c40b0300c07540005c55000100001d112040c40300740c1d40010444002c5c03208215aa1080758108020f0b8062489170320700c243c1401c284449249081c1d801089210311070581c0c0c06000f80e5600020303003014400d902212101c0c1c520f0060268051082c4038501d02c3c0740f0405010003203109a51911080781c00c00505140209036100f404080c0550b0422500349641191012545091030500e07004007190000c0070511402240010480b0641050460071031107110f082000b09065064900958058138094008268480f100c01c02000e04101c036004090178040c164a0100e5141c444422840407503580e03900803011074214682c404900c03408442110b0328a5194078000c1024002420b1110111004200100b82602c08a038008105900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 130580539 1250 130579289 130579307
    0x9010b07020f0f060a1d0402030c0a0206070c030806040b0d0804080d0206090d140a050403060f020c0d080402150c0c03060403360303050c0f010c02010213091406042307 74
    0x402da444641e50200036060064210058a0860b800341080c0310510301544501c0701203034448040c18888008192800c045000c0303034015100032090ba00c0000d4255003003074042002e81c0e0860580d1504003010b0741981c800500700b0310301801d000c0c80703903171204c0182d000b40e92240703035180781160080350b42130703545944500304c6a803110900900400b5009a0001039070402011910310403600050f1140c180c0204024024142c690026000300107002c024172010000c2600780c490b80241550380f400060b82c0e4040c1e000b03514581284040e4440801480404010042e1240040c4160908528000c0c0e0b0300d910700d1182550900c008150620740601c109005c00041c03581c044051451007640c81504485825218000c4141a00c0d041c103008a00e00314100c1040000c2c400c0c001400342103414800e076001896428880340c00e4410103240180143c1d00424568030400c3e40400c3c000081c4060801003064005680c8040301d0041d00a00c00d40c4515034a08410464040b595440782c8206502a120714003481c0c610000703407071003003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 130581789 1250 130580539 130580543
    0xb0a0b122104081908190e1201201305090c0a03050612030403022101090309030506070207060914011e0801180513020907260405010c020a120804050c09010b07 70
    0xd00101410aa480708422a001d0300c096030042c1200002c07110341a03120704503100d411500a641041083c0400719008011600e182480e51280024061242002a40e682d2254004402d074908048900c2c0200031202220040b0405550300d40c80d6003244001d515440e5560380155042058a0108401580004003d001040c00f80e101000301c0d449460901580100d0b040c40704210364000c21040c4003516003030031990452040e8044205070700140300961402d40c2d140f5a400c80c0819800c980500c00c100c0240302c0e01307a0040c06031000b81041450000e0042210700503200703640740e03880aa5540c04c0d16901c81c940c42440b042c01400350b0900401031610040c0300708000d20401c1d80c10906040f01c454208020b010340ba0284040041c401411050f580811a08500160801d814408044202c0181c80100b0580081e5541150f10307848803850709013411030a440c0300700841004c43d04460580800148500c0010900b04800d240198540d503403031030003910700400118140d0b0300c1807410000060f582c80150041600794 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 130583039 1250 130581789 130581823
    0x5010e06010b07030909020306061e03061005090a27050f04110f0f04020d0e190209010906060801030314091504060f02070506160302011107030201061a090303070b0a0b12 75
    0x60b80c0c80741c8850341406042c0340100000c1c2d555000304030340740b52500034603080a0001c4c013036842c10104803a290315850040602e08070044000c402c008451910601010704182035081c01481c000312480051005041070041403201e50101148002c03c038070600300da45241c500203000b0803040c01d0213034404401c1c180c02c450271170b0b2701e0365090040720301e508200103104004840600b086034910340e02010007001e034000a40c02c4440c10b0369401d24141c18201000b40860205c144800d09480c40d9140c01031060200050300604822814800108040e6501018030f604480d01480c100075950865141c4c4100352143d8030216038001c2184981c52814500100100304549003626000b0540281d0302003030382c5402540c8100d541c449070601c40303031041c044000e14200c4502d10a2000003401c01082141c40c00c940c2003600c05030010b039966107092015030101400c60261450112200b41840400c074000f80e5644078152000b048850708071301007030514009401c650081c5a0007411405003480c050740d2103648410310380100c4114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 130584289 1250 130583039 130583041
    0x90a020a020601060c03020a0f0c0501031a06071b09060605030f090f0607030c020703060f0615092318040311160308071709090a0606031109010c02010818010905010e06 74
    0x10014a10031205104503903000b4100703503032074460160b620380451101a02513011707480305203000070b0540d075a00c0c513a02c2c810904016801d013000001011a116501076008440240460719100c1d034882060307521640c2e01c6a810755030304041014900761040b941d88400e000d00d08001e0302161140e08480070354440c2a00e092201c0300da5441d81e10460799407014030103020a07900500c02003542c10f48070b50001600c0800314011130354002d5581d92407008403050703600c01021841c4d41d100140b003207440f199000d84102c12140f4200e25224141000344011b210f41c090b000d890324503200391004064681920300c0c5130800d5982c903070354928500b82c00c2c0078004011401c080711241c085d0902c00e44100f0a10241c54050381c0c2c00c018001e05060352681d0b0aa2044200a2401110401480030b00125500c0d1120315202d160100404103140345841c0002d000d03103502400341c8400340e00c00e1012101c687da00194141d180398092070010800e407104500a440100841c0501d906542020300380c0c003d100d0150001d900c00d000841c215591 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 130585539 1250 130584289 130584301
    0x10903120605090403080c1c02071704080d050d060510030b0a150c020111010f020a0c11030a1a07030f050a02040609080f0604150b031b042a0c060e030c01090209 71
    0x4a4000b805007540c0000c904022902282c4110720f080c1d4408540d0044920b011803104020510300e40b400c3e409103a446d000220b007000c1000001200700000007041c030a0307040c141405078081d00c600c108800001045001b0440d05036000150304500020903015014142c507105000c001006424003d0096008541e0f040c000641010f45c91503010458006545031540310600740c0c01105d840f50805684100b43d904e4040e1003280d1800c900c0100902c04c802d80b03865840034060700e0310800300c141c561440e92190704240201004258500080441d00d034201000c00595503440c0300907001011400c40f0010654540010802403900a5004000f0f0300c410741c440d824180d9580c0e9141c1d03503039012541008000d420900101e400112a000311000c500c402e50008504840074401007454615000c0c0c058082003512a40c14100b41898410390265620b09114104682d80d65807811441c0c0f2581c114540421040c901c500c03091080590212118000380c40c162940c4244940070720307010303001c0c1e080241d210b0740303440c008508 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 130586789 1250 130585539 130585541
    0x41205120304121d031b010903021806010807030b060f0d020d0603080c0c03010501030210030213030f030903031e0230030901060302010f020d1e050c240601030605030715031d01090312 81
    0x34013480d0080082000b40b06100d41c04045c1c3c4141407420381400b0710303154040010380e140c0040c4101c64000120700c011614001000410440003c0d10810034149064070100881d1a41400c80300a02c801d904010341d601c000001c0e890007071040000c60008140317000c0002c01003110020007400481c400404450000300241d003014201d0341d080c07100a5100c008440c0c3e07840d0403030094000d40040300804110b001020b0b5281c80c1d51403040503101c801c90029144000034001c15811903c0000381800380000710000b044003c0c0060754139074203480d59441d1840c005124803c6d10340c015400700f01a8071084e40041d20ba0410f450214041d096600003280400c8108840b0424a4030020309105001a90b40c0e4036078641429485001001c000c5041190070020100415811000c1c01c000010092600c0764601540600740020408445000f0b03003d181090b081070010001d079034001071404255210700745010390303128002405900a00b981200702465020007544084489010342c001b50480b4041d03202c03600b103444200c420344 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 130588039 1250 130586789 130586837
    0xa020703030306141315030507030302150a0e0d0305100504090609020f03030a05040b030408040306092616060b0a0815010e0601170a02030a0f0e07030213020a020304120512030412 79
    0x107604203a540b50341184042283e001811b081001c0680603520300d89070746580b41003080300d42054015074045442c121006510464643c0d108201c84020010342c0903050140d500e601d8641e030400c0400d40c44070702180750102030003070010041c540100100101641850b041001d80061401a0721883c425040200c5608010084440380c9029a56481c5000e04010045d4200e40001d04240c401c22400d10021000401910440720030724042d08400010707a41d17800685820802c0e00401c0d805005091124441c050142800d038802650b0050b80800c0815080d4045070025040354440d4820748a01c0241c619280400840d00b416508200c043e09140d0741c4400056591020000035045a0008a800540d4500c1d050b070155800007151f400205c3c1e0082010204800d4031014170b04520395821805040045151074203400304003648815040d400c2c80c0070188041c0d12401244504480c41d5441015170081040078012000351031040003c46880742000e0604101036604071b80c4840100e140d40a0003801481091180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 130589289 1250 130588039 130588079
    0x1050a0608030301051903050d0503060f041b0509010e0d0c080d0e13020342010e031902061303060b150c07031203060e0a0b030c090907030f080705030a020703030306 73
    0x40d443c503483c000c14032031840101d00e0000a920845840400054024001807915110540d00d960300c038100501000208284c000c902032044d8540305407101d9819120255041450301070610986070002000140d4050039181101036004012004003420403045a22900580b401101101c07618444281d081d1145100d04070360350b60212082580c94042481d80d0003e592001180d0f54141681c00702d00c13440f005440040e0741d00c806400f119118960701c0f510280c2c1d400030711102440e03c480000c00400119803a0503800c400759410000801d40d003010741d16240112440b0702c100d64410096183e070f80c14510000e000d0004d070301c7e02c03c02c280b1001d40c1c49044103400355001c0328003281c081c1a00c0c501d1641c4010038801d900c900b01d000c0c55201d80700000e9010107010041c0c451904440003003258902002058100604100c0061241107c04144030041d4000a50307101036070380c854000912007106090000203070044000090240c4030014102c45219800f0480b18100e9210303840a00005481e440902c07840c0140e4003070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 130590539 1250 130589289 130589293
    0x120112030e040f0b04090501060501020f070b0306060d090803090f010c050702090f15060c07030204140115030504050a20010906030e0c0402030a020c01060f03140d0519022d01050a0608 81
    0xc0c119803826910031083d945050400040c800c800f5808202039801d111410364150355148410403065030144020800040e00741c0113010802d040040140507400301420150056001041e9801085400e5201c0340c01d480e0803a54154603032515418030b6944a206c000201665403c284145900601407416641e100ba40100072407590b5450125009a400f0b0040c49221000b0525540e440f03540c56180c001c00324140c44001403c1c0003411801808143d8400b4080f13000c40c0360501004010040c003000307200326140114900800c071707500c490400e2031070700d0155038020f030030398280c680d6080c9000100c0d50441c10014080e240c40c01015540e8400740d00b120b038100f080d0145900f210002c1e440e1450580d004640c0170301140c000600700140207078103030b0031140d240c4c104c0079000700019014403d101d03e1005888025981700e009102c221600e900c004d101e0300075101d4032610020304150451125000b409804881e00306001c890203104021034101142c0920034005460355460200800c000035420b014201c143c40072240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 130591789 1250 130590539 130590557
    0x91407050607150504050a08130812030c040605131a03010501080a1a040c181502060a0e030406031116030f12090c060503091006080a14010e06010b03180a0812011203 73
    0xd00380a000f008200b2a20f87c081c1c0c0e959400000c01c51750181c0740000715920341c0c0c0015400c00c4405454082e0080709104001014000c10803a105038008503001d07030f01ca62400a48800c4414078640c0d50340c405800903400c29851b1110b8848101552000d1412180240d032038000544800104c3c0044806500742c1c021340505001c44844281400c0e005810181e10516001d0780140c05082174103a0b02c84990000c41070750709000c48070181142e040216a03082801d00004100c01d01c01005150359038841c0f0302c500004d05441d034000c04076035101c030004e48910003904050040f092031a0301c3c00500185190662602244204141c95141090380c400c4112550f440f907c90f0403807500704001542d0365000182a0784640c4601140070352001c005000b400c000304100710081161480301e243c404641000c1c0074850703500d03a140595507540c1d0880026124119070302814066640c0c1c9803003402c01c0c0842c6d070300130b8507a040d440703450740445c10001a80c0003042c40b1100d1101c94105640ca41110700301c01840b6043c041d00080d0522 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 130593039 1250 130591789 130591823
    0x21203120a0902091f031b090513051501120b060a0513060303030501060908060402060309030c0a0c0612110a0309021f0c060609050903040612090b0f0603060c030106090b1c091407050607 82
    0x22000360a0b44e40c804410395415075140102400d27100201e4030b0311820240801110100801041900d490303044000040c0d61940c181420340c155250481303c09020040c1a00205405454203e007100140c040038055142c402c60b800359100c0a40042d02c0308070002454500002070321b51086c1c1d00003003a01d2101c0050300303440c2c0300c9030200481790300301603ca00c8650104104040340080100a200d8629103e111145c81040c500a13001d06071000781200054080e0401d640c11440002e0b807404c0342d034946500d080005500405001007640c4843c00c0800351343c1c031400410403000580d0040000a400c9201e84402e00840d6201c40e2010182c0340d050316071311a141c0c003e00c814040ca50081580580755024902c002a0b0807c542d22401c24440042c0e03041c2e5415071a90041c044182024440554842c42102e81a4910b5160140041800409100e4841c10340d1020440c05815140c54945140f0a50013550034812a031080c201100c0c01c4100e040800c03482d100343c40c0c002070346003041010744030399580269565282020b14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 130594289 1250 130593039 130593053
    0x213815041a060d0204090203040f05010c0e060d1d0f01020d0f0902090402060a0e091806060d050c06090a1503020319050103051207081306050307090905090604021203120a0902091f03 80
    0xd0320003c1e40300350702071201103100c0c1e00510265105a02410703c40d4031424190a02c3c60071030300000c0c04441000783c0ca00c11800280c0740c1c4021a00c15804e10700c0c0028000c0001d010341c0aa002c40488680c00a000f100031800d48400150094401d081d0220010800c00f004164124211100b4080080d0442c10a200060262500740064210480b440c14a184007125100004008690440b180d003140840c031091400402c0d01000510f074000130075100e2080300341d01c81c0c403229644d07100c11500c039100c0c480002e81e05120783c40e000e00440003013104214100080406078006006500100c412300345c2c01c0420130107074400342c0442c00380c0360480342c0000252400100c16111a801d59004080607688007004002c80d803089d00c10005248010304c441d035a05038903400c4c0800c008100440a40c4070145048c1080240596841c0c0401e032a900b1960480c3d8025510700300c11040d608501440c400404207500c40c200b002402c56440e0896000b440c82200e4400c601d9a0300b5119000e00190154005501d10785003105000007550 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 130595539 1250 130594289 130594297
    0xd2406051c022802010c0e121b0609030f0c090c030408040e0606041206140a02070317090705190305101109040e030415110106213815041a06 62
    0x41c0c0d00b2614411000d400a103c00c01070102c40f03040051707540348420400c0942c048450510048100c6030000390500a0640c0c55440d81c039400510b000b0300c1c00c3c04c00d460031a9240011600008000b1301030700d4580d0155020143c488030a00312903800303084800c00240c19890801c0032203116aa000c4401402d040c103000c2a04110540240040d80105041101060320034140022013016845200e0203e40c08103420100c10744484040e00c011000c0307006000000000c0d421050001e650a11445982c0309640e035100405e00e0424aa400310b0741090072016001d184180a0900c4020f981c003450840b6252a80d5104080403241031400c2c031100290240701082c290b241607001641020403400c100c1b42031645806901e0507100e645802900882d03241c0c5da60301140102070041200418001100080c945201080801c6402e001240200006480c051080e940c03040f002d0150441c072040d0307480326900d441e0061554a40c40c019901c940103148940e18140c02403900703011b46100e0079a000007202a081e0b0240a100c1e042e08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 130596789 1250 130595539 130595557
    0x3050408040e0c031506040510050d0213060809010b030303070903030c0201020109060c020304060201150b1b030c0703030e0f040e07090f0e0f0d110303060906150d2406051c02 77
    0x4003000700240404541261074007a4040c603000b00da90382800000c80da07000e56000851400b50034240020003840e6144140e44551040a00b0210303580c0710309101940091040300360301402904070305008a002075201c1c0a9520920401740200700c00c00d4031130b0400d43e0724042102c246001656816080c00007902c100c4c509268144107000209180e1101d82c2c2d9001514a00100d080c010ba0010604000003075090003018400d000d42004000d20701c1c00d000300144144101310161106000103030003120140010004c403000c40d4030600035074035400d440780340003000c104640c12050320a8802e034503458200d00e490300c00d01062046404c001c050551030140c24078081d08030341600d070000c2d99a5a500c81c81788441400f5503203600c90660058500d403a99080007a10035407001450210783d9100380200710703080c2c41c1c20780c82da50020070031182000b0b118403541504c0510302c51840c006178030f2030038815001c4061420705400c1d04c2044050751071000884e11080c0480c1ca80c0211404c407850458061100034141035968001d1078014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 130598039 1250 130596789 130596803
    0x120309030201091707051c0f050d0e040e0c0907020f0d08011d1608060a0e09030307020114011a070c0504020d150602190209130506010f080724140409180204050703020a0f030504 78
    0x2115228162386400180b0141d8107138226120009030154171800984804100b100d0400200c00030304070065603048040402409101d15401007410103000308292220401e421341220340c01c1d490075800034425102841038000c4140c0c10751400300d441000c000418070070380c40c4d0085180fa116800108503090344010302001d0708544007410100c2c2d109003015506100b01d01600040d962800e0100000742100c603041c503240b0181c180e140060004c208a80c902c6111050103008044c2c54010605140544e15800d61005510910001d041400240d40da008910542c8140c0011401e41c3c0c1d5411007640c50721200c480401056209074483e60051810048440d0030920913021b01c250341201c4d669181c0740c510283c1018040d0b400c1c04008120400082042002800314201c5e48a0b45c009000c15460f06255203110f54001e209807030800d01280741d080025a0001c0400840a110480301e29450003210054440e059018608100010f0391f814001d000715002d040407561404180d540b4a5021802050003900c00c840da4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 130599289 1250 130598039 130598089
    0x30614132409060e06010206060a0303080c0d05012d15051e04080a0b1b0405060d0b040606050903100c0512042a1401080c0f09030712030903020109170705 68
    0x101c0c100a180003410300c544000503240e00344410034410f810300602c0241154072410030402d00da103920b41514100e03541350401c1c02650f220b0806185450144032215011149040c0000030003088169500c8110018485000807812610810003040741175070003880c0d041640b810014800c603101e14024041c4403180013075111065103042c410708956000d07a0000b821035002d112008240001020160303008a10741081c0740a548000000e41c005000360303c98644a00804150096185216088130b4600c40c4020300030014191a0344001d03120b0741000c00a14003a114001110004903458460000403603400d48415003008060400803034403040c0100120380f103040b441007000804134808490030f18512507503500e141460034038001c40c500f4552403481c1410480d2031014000200f030280d04503150b100070b05008c0c95030340701070380007203442d00704998002a9840001c408401c2815800340340700c1c05403803003643c84110883d42c0312547c41c940000c00d10007280b00c0d0011401008240350849282c0e42d00403c000d0b585542e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 130600539 1250 130599289 130599341
    0x23091507170403170301080604020907020c0d1b0609080613051c050d0c03090b0a0e01060305030706050907060801030c140f060d060501030609020c071a070503030109060603061413 79
    0x504903021420103a41e0402050030300030490001d1600c5180c20500c44a00c3c210740c9061451661984042d001900500020001c00c0c200c41c828400898085009403e50f418403d1524003002014481c007510844004800004a5413920564100f800c070b40c1414010080354464070002e8107071001c034050840b0315200b4a11054482040a201b00d45860120780743c0f66245c0c100ca07403003a402d40e0003034504c9a08151515803900000b400000301180c0100000030700240708103012101a0041c65250400f810500c800b28500003004030700c0e0841c0703100d18990400e070350340c181d56001c081e2401c010a00009184511141080c0310890022a4841034028003e0008908801d181d01107680c0380d200d03507a045200ea07250f440c00e001a58040c0503100c002c10443d0000c5291007104443c1944582241c0240008188140c00340600c3d4800c100c16500296003002c192681c03035a41d000500d0040142d40315280100341403540c0014400c8408818040c62030000d4140003881c10703c0c80c902c50040c155018104544010f0b0310400070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 130601789 1250 130600539 130600553
    0xb030a23011b030c020c040e0a030809031e030612060405030f07030905060408010e01060b03100b0306040b060c03030109060608010501090b0306040905010f0b0103180c18090614010623091507 84
    0x2c204000c0e14001640c1d40384040003420030900b214900d02403414801201031043d40043e500b4021501440d00258589508445074210f02c110907061027600c050354045000c400744000214000c5001301c5110fa08212280c500d5a183e250031100549550003d11240e400b043d203050040120394400c2c500403201d9915000041c400e500241c112503460f039540e840e104090718092250001410390062054114a0142c40f44900011a070103030301407450020000c25080d44403600501c2a1010080604e41c461101240c4595260424880c035264136003400000106640035010450503208182d658101407420269055403a52020b000c5680007540d60b40c032240410360a1140c402218009480820010074010006080c0c4003890085126290b14002900c009420761303d43c0c408403680803c0d10b4980301c0d8003001c0440140801c0c034020b0a40e03414981186182010380103200e05a850340d4036000840240c0500c41c100f08413401c107031004c0e0541e0402c00c6d52030900e0442d058825001c041010340780340107255680c400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 130603039 1250 130601789 130601831
    0xf0504050d140d020c0307050f030304080304030b040506010b04060210020306030c0d0602130501090f032a0b04051c0209040b09070306060311090606280e040e07090b030a2301 77
    0xa0350005403010b40500c124810320104072002d64520081c159043d0f08400284c8a060f64071540344038200c0f03040e20112a440074420b450007004041c040e252259901e003000b002c188400c8030100e403103014002c0003007007400d0490261010b880c0b050f07008241c14030164080700001d52016080941c1407049041c000705942e43c0c1d4904c0302001d489a180580c450001940c141e462440a800040c18091454424490000140d206004036034002802c06107000c0d64066101c10107000488801c168240018045407002c03070f05004008880341078071000c1c0c449140f5900c0c02050340c104a4025802204c000105020075840c14419411603c840203440200b5030b01d540e4001140d00b10ba00440e40ba0281d1101070380e1501c2c200c80c510361310810980f41a803a1401e204001d4502c036244450800c1d002022103011801548284041c2d000484060010030896a482c08400d030395102c141702d440621800c040b00b422060401040070b01e001360384100c441c9024210030440811140041d02158915980c40060b5100c4d130101030b07424 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 130604289 1250 130603039 130603043
    0x501090201021608150a06081207030909022701051b1e07030f062a050d0b040209060d050c0705030a080f0903030c040603090212030409150905070f0f0504050d 70
    0x144011180300182c10301d10884101d51144007145004c0200b442c01182c0440000790001c154903140d600c200302000200425000540381d072141540845444c6002401841400e00940f01d00007078540d1402110107030b00c01c0f081d00000460100c10b9009000d4103400d8844003082c01410724030305210a420700c1c400d500200024a0400e070b80304009228400000d882c02c0304401840001400483d03003141c40d9100300e100303401c2c4014401e50b0f0314140c2c84429840241a00340003c0c407814000030028078130700010016001311503114844d6260241d40c002901d414801c646100801070101801c0c11590b40300c41d8010000281950f04051003006044006102440204a0072450b038480711403d007841c07064a600044001d0200405500c00c0040c09166040bc10a54080310014039001c140e060003440480d00004072840207800c0381c4008500800c0040300c681045103205916008150a603645403100c40540b0029108180441c45071420181300c0c40c407810070081010300b10b040c600e260070f41d04c42c04207041c40c0c210281 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 130605539 1250 130604289 130604291
    0xa0c0b0c07060e060106020c06180d08041e0807050f040f022b0c05040e0603150109051f05060304030503100308040306200a2f0f010e010e0607141b01090501 69
    0x50002040303024450240f0058540000706040d41c105100070b90f84141c4c01c00c917a885103001240c4542e207801c0107a104010944003900007a0003025902e0034600c180c2040c000d20142c02c48040c0015022024100c00c0c800b1280f44a0051640e01d160006210071116800b076002e4210b52101040ca01c0020a40000c080781e2100c2250940c00d00803002400f007001d83d1a04a0344807c4c1c3c1840c12241e111a841800e403030a03909403881080568840c400000e141215034412511040400d00000894402d1a44214460012800707192056541c2d840c000e01c000c07086008145d8020030500c0070401007841040515842400344001c0d0201e41d84a884030305464100341d00886002d9200d89040395140c20500071415071800e10fa08043c24601c10030000341c10b40c940c0000000f0035042140b081d5810724032074140d41c00d40c601c00c0c0d400da0304030448417104240a01400c10f0305204641c00d00320000040580041c0c503512a00596807880030581203001c40c09070503441100568400324184401c030350441020f00c81e42103140e1050300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 130606789 1250 130605539 130605547
    0x9100302030c0102030a080c090109050d0b040201031112010b0c07080a06020a170105030a1401021306030b030c01090f06080403030207060606020d08060306070e15070c03030c03020106290a0c0b0c 86
    0x810146401c0c030381c0c0c9000e41190006e122070b400c0d10340c10441840e0000c400041140e115445100104e4440156a00260b8000307601c0645006000721095014000c500030381c0c052200c0b05d05035100304258410344840070b40c0c4403509001000140000d00181c43c461052400b078400143c2e9aa44040c9000c84004040d00e409a00103400352030650020f51100f5450320007001c070134541d850710700041d847c0d941c1c144001e03040c000ea018403010021829412038250b1240420101e44803602e80d00020010400148114040e104100310300032a9805803280c80100c54510075015803080c1001c10844003114007403c203d0905800b40211400100f6a02441014104503401498440032b00c2c40c004013440805001580260861010700c0b880341d5100d9a040300c54280bd0750701d1018454200c00c0e000d9070b8402c62601400c0c52540c44c00100400d603000e80b08100c640e001c0c0e0b00038000c0d60f0300e070325080000f4070181c0695007480c00e91203031240c50168081e014112691050904200c908026125a400310350225080064000002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 130608039 1250 130606789 130606793
    0x30a08070801050301180204020304061d070906050301020315120703050a11010206100303080a09030903020d080a12021306210c03150b090a0501031814010f0606020606090a020c010b091003 83
    0x400c401c0d00500045009204041055040060450400070041e000e04c0d0000001014010030381c0040c0481112200c001c0003a030000314065031940600d016119801c0e00303000b80020103140c140245c03401041b04903004030081d203462080201043d00340b080c90740940984800000804c9090150141d80c0e4021841c00b1b04800000c800203041c0640180102003500980d80140b0100f94440155503008890050005e55884142015140c1041e140e2000350321181204243d030400040401628a00c2a1911806c2c41c0c504010f0011050707001c4c0c400b1001007032191041c10001584101229001c6103250650081c0066650b03090f2000d9400d6001c65401080d111052101480c600c48150340083c14415041c0d428000000006103410f40b00d403180904041d01c0344000364000058030100c15080d94024401039407a40d0b20a100c9001c0c11942c40b00004c04c9160840000c0c0c0540040ba10328031070b031802441034a240d501c65006070000d4000b20000b101540da00c0b09030700666256244500c1c001d240d6100010308070b52643c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 130609289 1250 130608039 130608047
    0x9030f0503031008210f07060608010f1409030a050d021b0d1404080c0402090109080d03090c120302060f04051006060c020a0b0a0203180d020d0624080a1b08030a0807 73
    0xf03610510059201c01708013905522100348a0240c20052480f003940d070381680a8640040c01b07181c0300038103030500e860400501403030154054201c2490152051044805422030140c110384110755240064000300f01003c0c40500c588010110803007000001401c00580b00552014440c050052005c541d0011442c20743e440c3c1c004002e50005c0c20b410b503019182a081161860b11403004914060290b9008a807001070b60380aa020722015000540c100c0307805046900d00107000c1c1019034003d0704c0d981c1302c8410225181485d10310400010340c164006004940f1a9401e1028081000b0000e0303456001e20080f9041420342c1d03001e000003d01d9240d5a51407081507500402c42501040c0c2d00002d00b42c8010080a447c407600401500c16040e050b82d54200e52400705000b10f081c150540c0c500a600440c400300580c204001c5034004020120b52500c050391200215144600e4501e0358003c40b0659400446140700284903900a8440c500c211101503110a60f04c810b0f992035500105100004242cbea2030400c4001944 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 130610539 1250 130609289 130609321
    0x1e030801050402032e03060509070f08070e0103111203040f0914070c03080a0905030409020403030f030504050c040221012409140409081e0408071d130309030f050303 73
    0x2141e045186041c001e0325012050342074010030384817041618100c001d041d040740e500360081d500441c00b03100c5450020341050711008070340204000a0030b550340c003164141c1d0001d000c4c401e0341c0e8000c2081070942d007191079109004281011440e070012a050f0700782000e640c14000b41006101280d00c8442d0b9031304241c065800d58070441c1511024601c200c003080342655004864601e400d41504207201c0a031940d00311500500240705015065200025002825001a174020001c6030300a503640300c1c1402ca0044118150340d811b070340c040c2240d03211000703140007860141d0007403103240f111482c0610500c0c404110080d012100760710040c404002c40c5100307a000b07400040032103841841854662030490070400c07280a40fa00043c2002d000701d40d100c1c03140c4104181107085440d1440c050192000581c44400384002c03a41c010b00801180b800390050004008010001501d0b0310f40034407107081d1080d6203000c0c02400310800a8410341c1041740360400040800c2e09003040006860154020315034900d0009400803540c02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 130611789 1250 130610539 130610549
    0x3061a0c0601140102150403080f060402030f1609030218060f09040302101505040e0708100c140711090c1e0913090501270b06031f09050a1e030801 65
    0x4410064a00300d031201080c400d06550303441c80300070b20740b040b06030040303203070240b90843c1d00f940303103a030100380010b064012030f02510440c00e03001d00e100350303544182c00d205c241d000c2951905c00300c01c041d00200390107002d04c0144007a018034520b44005801c1d41c94000503442621b0306503503070140180900b4080c40307051051094200d04c400b80d400c91040d051a0398002d43e1410100c0c07885030203940d5100f0401e440d0010480090080c28014018086140c5c100d505c0c68842849204412092054010350707081c002c4540141c01441110341c031810784000c0921100e138400d40c0030300c20485008504084042080d1748000e1514002c0d0b55020006440e04040b44035601807170102c0c4100f40940c075081c0704e4400d0541d125a944840071134001e03030104802810385081c0e805011124004604658440312401c0801c4e00721103003186640c005c004144c450b44505050548855050f40003074a090703c802c003c07070303800750658020440030b51080d01100e048003800d490301801c940300881001c01c1111700301d404900307241d88091100d0247c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 130613039 1250 130611789 130611839
    0xf0a0303290117060613060f02060f090c0105030c07060c02030703020d0804020a09022212150605010507240c0302090108060f0609040f1404080c16030201051b0c0409030306 76
    0x1070060030020303003855141c603180140c00d415600090116242c0380300f0345d003240f800041900700f40c5480b0040a007002440180f4600144200800655a804820020b6004000707203000790160b410070700e004691a500092602c821020100034803c0029002e100348403106d0110b60103941c0391240c500d802070030b15035011440c404004d079400501000d0380e60040c42707800312804202d0060340d5000700e141e01c8007444691503500c0401e0807102d00004400e52400700440c8203601c59103980c000c0760300c06004d52080300d60500540740020814081000051050305881d441080c01d41002e154034820926a01e00b0b465205210100098000c1002d5603d56003101c41c6d940c12420403200501058054408039030917005060a40344540d0f212520030b000120181d0100c1c0588142d210402d20914090602980d1640b09203034110b210306c103001ca941561503850b0000e20030f480e0305940d810f181001c0350078040c0d42904002107102d018064090424540d990344d201e0840383c1c5111380c40c0421068035202c2c40224030001c40000203144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 130614289 1250 130613039 130613111
    0x30213091b05190e120d0207090e0a0b01032a03080904050106030b010807030c0e18100608150409110612150a0b160305042c0717060d050f0a0303 64
    0x1c00e2480b20103c00042c00c0d01c1e02010000d80200012a00740b005c240118031402404880c403001d690200306c8505984a6580c28070403003840c08199542c800c03214401a26004500d00188006002075401020214040080b07110681400740300013300754581e801100d0150340000c040d507950501d40205c6e801050349040c1004501102d400182035a00020000760426036910100e0782c600c0d00600c0703840800c000140c507180300402da001104044102c2a101e407110001000c100140840c841e040480c452080807291211916440e170900000d41745041c0100d980e082054401901a16400064514220721000f588010706041000c2d03022881e4210903580500d0031000c06110301c1e0440c40464080d0758440080380f44003078403030a0483d020b01441e049411800c2203542e102c6100c90102c00904418208580d010010b40c441700400d88010704007030324a601c81c0c401d090000c4c0541c50502008101e10b4081e000784d40321400c070602510b04181c981a8101e01083da141441010024000c0d03544008805101d40c200c48 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 130615539 1250 130614289 130614307
    0xf02030115080601121406031603020a03080903010b06070f020103050108060c04050603040606080a120f020105010f0b0a03060801020f0a11030a1713020a0b3610030213091b05 77
    0x81d40803804000c0e01071205a1010a199034421520343c080009400c40802a20700c41e034401c02681c400646500d88640304080c1100f60b5442c0c000034000032264000c1080b0b008a2079960388541a810400c6015495540c070604406992100001001d070544078100c0410888802d20000d800c41c6c8040c2c01c8042194011010071011062510468017904d0080300e40710344950380c5192410180c82990000e00d698050351424108000d0326004070071843c4170680352072620019159040f400c880d424416644801208c0504000035040710001308010b0301c251502041050f06c62031074078260b901507001d030002c804000400702c040c540c3c0900300750311302c007140700155261910742c0d00c0040c03030400b00101c3c2d01d0041e035805010a003000e80b41d4074000300742a0701410000e40e85a5946480106401c03229100443c80e41e44161703508221424241580d8408404459094100f010810701c1045000c1101000515500300306001c407803010f150700301d401464103e0010551459019908200c02c00131008901401410301c04004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 130616789 1250 130615539 130615559
    0x20c0d122412020409060e0a03020714130c0e030a03180b040e0c0c1903080114010503040f060510031a090c010f080622090303060503070611100203040206070210080603010f020301 79
    0x1241c00000c02602c180d9641d00018000b407600303100003004c50b0702c1c1082003c1c01507804105070704040d000750290381c07183d55608101d6020740c1140300a690b0014801c403211260284c65440525284204d14140294418510101e40b5051180c241900401c0303075150190640107100c0d1640c0050702681403110308151030001098820309010303051100300d1034045102c0304118410084051040000e203401c03d005055400c024120810a009001210055214000e060750060f01100e004d507920142d61088902070b0b441d910024034010706414030b00d90a0040003c08560008e01041c2c844100118084840c1040200309141c01c0307520700d00740c0c14007040066000880c0d402c0441c0641c4043d00351207052100c00b9070313901e40e840c4c0200c0da00c05a1a807450002e650b000e05a25610440940740140c0484102c1d80c2c6989080c0e0b41e80c000020000c06682c000a0394046004058010719001480034091504200c00e80d40000c129810010795180080c1a050802c0411f00d800d004000804042440840c0f4650409868203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 130618039 1250 130616789 130616861
    0x1006090605100801031106070c1d0708071e030e0a03090905060f06040b0702010512160e01020705030d11120c0609060a050c0a0e0d08160b0109050127020c0d12 70
    0x58103138106c041e00711403d51039030b1049421040d4002c40f5426007940b11207505070b1804140049a04803010743c2c0000384003a0040c070b038450295103507480300d10701088c00c0e500403554002000d0387c5108060300c2d00304500609400300036081c902c034802d85484e4005d50512030401c0807940028550b034440c3c150800171079003d07207540040750180c13411520440d0340e445507400180d95900c5401c0380b900701d4200000030403811030308204c10000040c54950700d8204184500c0c004a130789070124010164560015907144c041c9500031007842603d8451101692841400c10034802da1a41000c540404540c104001f0403d0045040c03000c036500c40b24544040006040940d0328201602a800282050020360240c1d18029030300c8a2562034101d034071030880c0b030b07482107103442451421441071001c80350358200c1400400c25481a000e094180da84500c40c2c0e110240c410380d81c0104040f503402c90b54030ba8a40c20402d04188803402d2104404000e016100ea0466003803003030805084130703600201503104441115000500e0310310b0861310 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 130619289 1250 130618039 130618043
    0xc0a03030f0207080d030506030d08160f031103041410020f091c060603050c03100b0f1909050a0510060e09161b1110020f06040201080406020408100609060510080103 73
    0x7800e03404000c4001a450507043e604420114813907181034009103a85a00207030310400065007a290000c0c001d00d0207448a44c81a10343c400801c4041e003900c0d642c03500c9211b148445210714600458101e51380810000194016076003030321204070309070808000c01c00410003510304040c400011031600901e035400c5070f01c9004000c142c9200e00c64090410716aa45030008800020f9049941049011394915000e9640c0e808044001d0007030040286d00a0564041d100d010060400500840300c012500401c101c101007250050f09003422080b8000b140c0700c28240b1500b0310400b408a80059a82001c500101801c40c0e0796210504214a075103000700c0d10f84900018070380100d404103020a440102e42d100b0b69400300d07040c54481c01d1301d044039080024440325031540101a50155400351400b80c20200c00c82e1180e54282000d14158444030105006510640506500500034180107080a8960906504000d014401400744545580081c803000d94580304800007044201c889038070004c0481009000007405203c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 130620539 1250 130619289 130619297
    0x13060b0d24030f02010f0302040b03100302101701051c0b0906040519080d2007050a0c0501031811010c02040c08091c090911040906030c03260403080307110105070512090c0a0303 78
    0x110106c3c841c000c1d0152401362281d04600c9440b0302d0241d80e200034405951005070303c11440013070181c290a004254440312625950301c0b40300c25a00700b60900c5810341091000c0756002a4086074140031880000c03000b8020490030014000a04050801a10b001c105c50f0540c02000c0c003030450700c400114600101e64500002d40c20200780e03805600e02d640c00f90b55000c0c1101c00f80010024500c801c00401107001d04c8000d11580800b05200d403a02c0c0110202c41c11030b129000d6040c20f862020b00440d0320701c070f1005142081490072515000140d030228080d180307000003050214542c0c41c203220486a043c000044d0155811126544d0318802440080c44810310b4880c0000d01e59a40350090038480c4041c0031038003e81019076044c0300050b6685400080210a4442a07848810840784089a9800310041ca0340e02c11010600c03d04050440d1501042944054024402d005a14a5250b5164800e0103000d110300915111203440b1240c00c00c08042c84400186801155004420000e1071580d419402100362a01403130 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 130621789 1250 130620539 130620557
    0x91103070c120215090a140102070507050130050f06030c100c050307140609060a02070c030206090f0a0b04090e0118080310030c14010e010305040b040213060b0d24030f0201 76
    0x140c1603051034800f0384400444401301040094040b030002c0e07260100d0784203d84841c02c114013058698201d00902c030008005070800d090810896205500d0070b4040c004951541c0c3c0c05019404114480810314896a00c86580310702c05c01c6041590007600c00da101c002500600014010301c40000c00d0b00500025000503c50010500d0b010f0040403c162a40680c4c81110360340c0d80c680345081c483d5030391812190a045d61081c0b00010750000541e000b92040281c0c0008060030ba03501b941c0c03c021003600100c045a401c10640c1e0610941542c0302554040188160705e142c0f541c031405d108075402581ca907280c842d00d10f40e0500000700c1c452061030700c1210180740c118903416120f8445031003060b414150b9a0000c0c080e01015900814100c1c400a801041a03c098a98050314000c0000540546d40d044074040c04400384440000c0c050309242c0e60301c80030700e0409040014202d40301c0c20f0700207150b00200b103000c101655502e000482c407101c45804815029840c0b001402161459a803032444200340400241000452a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 130623039 1250 130621789 130621823
    0xb0a08061302070b09010204030209071707051b010f060302030d05070506010902071b030317070309200310020a0c0b01050411070f06020d050103030c060f0209010e04200a09091103070c 81
    0x41d0640f04060f0b030001c100704007800c00e428118082d40107800180d10401c0d0040201d800c0d54062401039051000b401c4080259a8a238081a1210f8211a61415407108200f0001e19040820f1240c0800c1c0700800d13400281c02400e500501d031421240300d503d10240181000514082400080d0381811581c9840c00980d40303d05600d000183d8002111684040707811030b610100405401001c0d0181c0720641c009030089594807a6401c1b03042c1e404020340076008108540f001005003484060300c0001c0c88000d03048a114500892100d0100d80c01213107a8000100d9001a510420035106113a500400c005c0f501884a0401e040070402c0310312a0a4000303101e071002c244e4840402140da01511250300e011581000f09603542d0502401c074402d50309048941914025075501074182510980e0010101a5074031140e0310100804d100040680000d0003001816041c9280c070404203100041c10700e0382c0d036982c030001c115140c000700009030303241e403030b202c900e1514180708101002d540552034859003608020b01ca48505096 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 130624289 1250 130623039 130623041
    0x213030f060b0d0f12030b0d0201030b03120a120e03070506060907030f020403060e0c0a060e0609040204150e01021603030527030d02060711010e0c0105070c0e0a0606090b0a080613 79
    0x16501180e00071001000c00e40510000981403013026016605995450302e0340c0008a040312000b2141c9544402006a2135026511941c401d41c208000a8202d40c032100d020240c00440f82c02000320400090030215070b08030029680c3c02020b01c1042e61900071070038603046546d6292154070080441c0d015800700740c00510603d110750001c1c000401c8108085550342c2c3c5074200840038290591110749a07200310b001c3e8183c5403d1114a07001200c01c0c90b5900b00da0b60450f0000c10003182d005001081d4030070303020b210120780c42c40840040c0724606016180c4405d0f01c0344420002e0b0501056003c049540113501401300042608841120020040b015180042089182c200e0020405c242c00c0c9030303050710800d00d500d4420b03500010b141f070081031961140a0903001d07200b506400d035025454500303400c0c2c10008a00c10554040d0740500b00c803610401e060707040c980c1c130351200c40d0160001711640203007142c07911401c120711504042000c1c060804c4008162906160340009003e20384058800e0b0300031640344880c6281e045003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 130625539 1250 130624289 130624301
    0x302060328060605090f0d1709030a0209090115060c0804062607020703060b03011a09060406120c03021915120209040204030602040e0c1e0306040908042301030213030f06 75
    0x100c1c441080590745504000300540c00000d41c050042d8000002c402d0945410b6044800a80d03203c02403807a210b0032200b044c83d40fa0001180150140708260101005988003001107100d91000000094010075a0070300c002240425402642441400320311080410110001c9a0170350b41e090900f0320400d9071202d1241002c0304d81a404160b00f2000000b070003007103940451028216030042c0e0080c002100104201422074408403580c64403013541c8a070180c403a007007081040c0c0d803002c002070001440d1955203828582c0d46d100000100c1c1c0418040c8020710461404002400e50041014682c01e111410b10f100d891034480105401d40a024000d110b0100302290344c0c044541c0350101030410354a6a98078a08030003c1c0d0018003500e043c4858010014009005001c15994110100c91040c001c0040b5045220081d43c80500340c1a04661111003a83c08150810b009100512511345480c1d240c190406d041c04006c40c80c02000c0f810140104041c201500c14201c0b042c0c00d6a400c02d030124281d003060325001008102c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 130626789 1250 130625539 130625611
    0x70b091002210105010207080304090f060e090303090d02161701090501020a0504031106090303030708040618030e011b0302030a0f020f190b010803030103030801180e16080f0703020603 81
    0x800007500542100315655051010b204401e80c40700240d80f500c0040e070300c64085000781c01c1543d000788010012102e0540140800b200c2c00c040003d81c80f41c88000011550808039140c00a5620000c1440704e507400400000f8501c50440c07004c0c1c64010421558000f00030f40134851100b03c5040c041c0d040800030400e6010001c010f43c0b103c000c40d42e030700e50044c0107083c17904644400d41d541c1c00c40e0b84072074802d8184001206c4c58035a008000d1455a910400c0995014002030000d03103555544400d041441081a580c41c07401300e00a4461413580f8500c400010800b01442c00c541000040e51501d04000036000803d446420001d420f10100801ca0034000f2071802c501e840c00d0321700c144503028280f14180c1030440b0b4048900c2c060000001c047c0e0321446026603a110a20000b8002000500100131031040b4081110328811039844c00305001100111652400400c40b8010814503041038003040200020041c80c04081030340300c0900760070f40c0b55800103840703400001c0508107409800400c1111552852030000742c507403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 130628039 1250 130626789 130626791
    0x50a020c06010e100501020109110d03050d0f05010e06030102090f10021011041a03010f03080f16150608070303140c07080a05010f110313020f06090a08060a050a02090303070b0910 79
    0x1683d40c00084409000c161624a003110380a607010900b03503c18010a020603070080910089200c0700e5052009092a003102502001010700c03114010342654041d0356a02d51402c440400c01d541400c00d1440d0780070780a40058400e82c810401881c4c41d40f14000e405030b078900112800b0f0704002c030014080c1d007000e605000c42d202541c60701a0640c2c200d10b40402500503213140b041c418a402071480d0114000c3e10003030043c002040d4030038408000254140700144002c613503859002d030400d207013007010200009522b0400c442d2000c4891400e80682030340e01c5404003d12540006260383c81c80c54401400c00382c1e440310181d43d4600e00040c8588a0282080100c0082c072070401220800646410b00074020140790340c0024001d4140020700c0c04180703e000680c2d0141e9039031340380d00d50009903ea00304000715020b0080b10f03410a00900103072280d65240c18171500203084c0d4a020b00028500a02c44e2022104001d02c03540e200c038414041c2d0100c1c0e840003c25a140d05500008494a07a201d003507106203003810700c02d00a6005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 130629289 1250 130628039 130628041
    0xa030201080f071e0801031403040f0e100932070e130605030a05060a0b040902011b2123070308180c03031306020d1418010918020403031d0a0603050a020c06 69
    0x503551001041b4104da02410810944503640c0c0d00aa4481c03003103100381200340c1080c0c0024020a544810041d4000b60300034486004140d4404c100025211040282e00716204050384030400b8211100c2e0350048280c1402542d03149280c030010240c400c85031481050b0080000380f11101c0002c0e0103901034000f13484000c04503a1101c1303103450003941d43c0c442154a141d8403810055401f030942001d000e00d03030000d58140c503214442c0c005040354003c5802160b00c20703913103600740906c1c082e10414003000860340c1c00c1da40d60704e10182d18031480400881104903202d80103c0417080280c0301c082540600e50780d801070811441c0308186145014064a0710260030000f942c5404005581d030241048000808111507054081c0e8101c1030780207000703441040c3c41080c0a400c0d9031301080b460210340020141d50010140504003860026147c025015451101c1c6841002c001c0e40010188141070f008801548503000c82ca85540520503107801050140900c0d00c5440305158840c0d0200d4500d5143d50183c1d000d0910340030890b922 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 130630539 1250 130629289 130629347
    0x60a0c120f09170a0c02010503041b08030309120c0607030e03070606120c15021b041104080307060525140412050c040e0a0206070219050303030108010e06060a030201080f07 76
    0xb4003a0100448040c007a04400d40c0001c4500c1040d281040d5080c2c83d6041540c009400540c0e150f48020411584146101100c80102d00d04940400c0074103042c800858030303172500d418582c1c603116810b0305912120400703000c0c180b020361002803090362011042c500807810344000c0302d0302c0c3e00c0c500411800414560030040082205548000100f94440c003826a50484581e180e0030b000c901428006820010b070014000c0031160300791854441080107015100084620710f03003800400d25082a0061000c035000003603050103001e2180103041c0c1080c2c0c94044a40074112041c102c02103088030514110521100a1503951104620020b070781c001e240503070040c500a03000303150694480549992a0380300b81d20b80700c40084400d1000980f5225554050281c034645140b43d000c0201144140d00c1d51a2800008000800c5948090001e54000d110a000100d800004150454244903004140c41c0c001c20000d00200090713070748010b810742c1150700d42c1d810015039142e002c400c5a64801c800c101c48000e200040c1c41d520 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 130631789 1250 130630539 130630541
    0xa08100b01030b041e0504110d031e080f2805070c05010e0106140d020301060506071202070803030403080c0a230a021005010b040b0a0e04060e070f020708060a0c120f 73
    0x414400c242c1c1d04001c0708481c881044110303840d0a01078001c109480b46905900c1d025648016001400340b6900d0039210804400140c000c600d8078422000541500d14080d07001007020340598042e5020f091613401da29101030b05c840c0c0b07a10b0061401c0080c0f0007044218901810940d0030654507045490309101901e4800000340504580d075804070f030f15620b000305841c05604c0611400c001e0300c0384549003c603502000c0041003891074881d803060703a040d5625200040c03150b9601c8010005140304400240b107180c0300c007401a0401140e0fa10907001034008104100010b503010107481da2056443c0c03040740c3c8400c140c1208803109020f020341d401350140d1036241e0741c91a83e01c01000e030005108941c201c900d0307004000030640c00c2c0d0f542803203001e5254606000038003100c0704070400390044480c0391405140d41c02040000506172022580808401480360062141c0c040e484201103090311100d000600e0000e04d411100c65070380c00024159126943d45a103c681340c2d51041c070711940d80481161003403000c0030707106803c0d074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 130633039 1250 130631789 130631801
    0xa0e011b020d141b0303040920030a1b020a03020c0909010b12060a1d0309010f0210050c1308030307020c100c0b0c0c07060c030f03090602040305010c020604020301050c040e150a0810 80
    0xf400c54411520301c81c12034210290b0041d03441c0c4c4040c028505140c5010a0304010b0003215031081049282d1801c0210542c0f0f031000510b105815404000c25113111800c600280d078600300d00c8403030440d080b500c008800319400140c5803420040c1a581d0501a546030f00c00c460040070403000180e0303c404600803002c40020002481030051040b06410000070036501d014070104040d00c3d0802000d9042404240c000350301078425900910030a0054032012080a2841403c07a901100e54800c0404081207a4450f8078a1300c00c04d00150124034010f501e10f00b05084043c6d0f81f0300b0301110b00e600c81c40d8481d206042e0b1510820302c800c042c23503202800107003a0034540b048001a070001d070881841c5106036900002e4040c403841ca84052603405448500311602071032000c501034568030300305440540e002c000010000d8024481c0c442c8810483c0c0c05000b45090a20406080d200054070424166100344801d1007900c002540701508594400b145c08040d5140001103080b06170503074405401800384e00c50016002840360010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 130634289 1250 130633039 130633073
    0x40f05010c0815030a0507051e0925050403030c020405190f061403030f03040605090106181b030501050a09020702030109140601030c1208030a1a0402030705040504050901020a0e011b020d 82
    0xa484540f0700f14050540c0c40d00c101c0b901401d9503014a104004500f000c502c1802038401400c41081e0320344401c2c010030840c400c2540d007001d60a044440080b02806100400b403086102858000e16161464400803c440c40206000c0e102d02d80d82d40211b202d06212113281c004101441d4802d02480307503c0300040c002050180700d800c800b003000c0740c1c2c0500075103030200032522002040741915040d911603840304001088028209051507503a0784002c94400c00b1180180214068a10007240001d100d001030609650754602e480c042c9410070006011076519240510203448500c1c800588030807507400064090706d20b142018140502e61610381e040036002091650503240180309400c1d0081c1c1e281d46010b6112207c1070060329498040c40407a0409501d40c00020001c1004219440c0d00010000003e00b20383c07040d24141c02040c0001001c120342c1c2801d01980e0781c8041d860000710f0805c0c1c4519005400c444054070520b04106907900300341031301c8810903000300003160094880140300d11585050100f2174110240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 130635539 1250 130634289 130634311
    0x501121124130509010b032403100207210210090503090607230f03121e1006030f090507050409022b030809030702100e06120f040317150603040f05010c08 68
    0x10128241c10804d400a040300e00c40c214a6156a40b08011804542c40125040e00405a050941e0000799010840820001c0503810b0050f6a04210f24000324074400160303200d003a2440046440e0b4949401050000c1a048544804a0400450310f4200e080d0302c20741500d2a403107580070908409002c0e603402d10804141c2c0c1400201d07411103003004c090756103c104d180b1044e03a60340b00b080101a030103111109150001c3d15101c0d500110840e1f00c40d99044407108490745008241c40d0402008070740c2d41402503a42003074981c00100904981511040d0301e9010781d0082c140116207980d041c204540b60300f401c00690500d15084030f1000f25076250710000d6180c10400035800103681c800031581f103080c04003c64104a5005010b214143c1e0013010603515081e000f000103034004002d1140c0c2480c041003800103031081c5448124010035290514015007440e02207020100049502010854210072440440424030b001f2144a03899a550f850600030804840100800e07550a2003e9040c01e20307005001c4038080c40e12048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 130636789 1250 130635539 130635577
    0x8010c0224061c02040c03090605010b09030a170405060a080106020c0f030c2116051c0b0a020304050709090b0708090c060715240e0a0501121124 64
    0x4016041c0314400440030040c0000000410010f15110741c41c05441c6007a1420800d4000240d00050f0442d206000300c81c01103a01c50f88140300700442c2d0720843d8003411410f044d42d41004180000300c1c4c0d45900d41c00004049840758010806150303a45c0f01a100142001000d00f80d03a508501c00041461303031b080c071450b009032140100003891407074201001d204007200a070003000c43c00201c0c0e0412030803d96410141058071180036080802d100c050203249404107a41407241c10b507070b14000030f2005c0b8601c09204400801c101c207000e400091980c11969822042c80c15001da00c075191400c24900f40780340c942c00070301031504d410f210301c08214402c1c40b41482502c058494900300d603181204191289480c58070103901020800c00c0d0000100c901400415400d040d450001e60080c0340049640100711074805060155096041040141030146d2102d5102d00c44480070b04c115450079903d010142801a002031034003248004164694480c8031000c1c0103248091082d185000c4030b40590101c07503101600010058040503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 130638039 1250 130636789 130636813
    0xa020f0102030610030911130605010e0315130816200a08120d09020402120402210a020603060112140106020706090f05010e0607060c080a050a0b03070510020102090402030108010c02 80
    0x8420b691040e0030251010303401c0040e1200807402083c00c9101140c403d112288050416103402039501801080884001001c50a0400141c0300e102a41c00e114031a13401251003c1640070710003070558205070303158104100342d10949000300c44c90181050a1407902e0458844000f80b103030506d540014000504182c1011046400134800c600445d03000300e420a60106086110340c035000d200410b5a942407040018040600364000303020783e8400c001d10310300000148240003e516100c0442200304008403502d59280c10040707080da4030380c0c80c564004bc0c4035840100c0092460313400f031420100c02205240040140300384218503040408800c0c01800018803c4440202e56640100a0081601c180300716086680e4a03100044414807003032100c01e90401000d0249000143c000c0c010900728242c00c0d2541062803801031285403c54000501c02842c407403c12105102d26200450480c0503a17000351800640e00e914054240d0191242e10003203a0001e100000006050740706600c5840c20310034a07030980c1c451080c0300c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 130639289 1250 130638039 130638041
    0x1e0b0313140606011e05160605060a06050309060c0315030d0315080304080303010b0f040b0d0501180207121103040515030604060e070f050c280218070e061810050a020f01 75
    0x22100c2602140c0b04031024a081408102102d2417a02549040b0f031070051425210b00c00600c3d4050304494003610f071000e0001e680f03014903200c03001e001c241c60190b0940c500340c0000390740c416019203030101203140000824851000d040d107008401001800300c0d134031013400c04001070043c00c11070030401e00264040400302d0030b4000801160112403c20300218110b07400d082d64640160f000071120602c03007808000000b0700f0740c0310401410389a8881c01000446600d000c0e0b03a0038075441c03001d5004642c0c41c410030140e00094440340c2c0c03109492089141109540e030b81514501d24501c03580c1c00c07451307014a080c950f0b2203285a80400451007414140da0610015654003c529141e0780103892030703c0410440c003040501c1e036205501404100d145502103964802e42d0200303d41042d02605200080400e03c06109015270030142e0400003100e0107450b4000d064030700500010301012041055a106e058001100307d010368140d07262415001009141030b4401e0076404001d44660300024408000d401140340280402d80c0c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 130640539 1250 130639289 130639291
    0x9041103161407020418051c030c0e010f0e01030905120903100501080a12051e0702040c0e060d090501060503010608030a110109020f0105071b1e0b040308041e0b03131406 75
    0xb6800da142403406030307030030070024201e10385406c0007000880048101041c0304204d82c0303070008407182d8016044151500014207444070480d174001404084e00710040543d82c0500700c0303222452503291482a800314400124042d040d041d90181c854411041170340012001c02004002600d011001c4641d0b12590900082c03c0c0c130000d20030111030303070032141c4183d011500d0321650050010b000e14006207001c2103030350301c100b013047c1501028545040200f004001c5080501c150144000241800c60700c0d0398520000503114410300303943e505416129060300c02040001d4003d00c0150100600911940303449480300ca540b900b00003a04000180400c81c00e4240382418402c55080b160040d00500489003540010f55483c0c2c803003082102c104803000940707401810224a400040c100000032030542041e00601c0025421b45a0448010300b40c0812040002841d2b040c01c0b5822905440c0510070044003035007001000301400d0340810032410000041021011101e642700a45c284200e0074851000d0aa4600680e2200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 130641789 1250 130640539 130640567
    0x11a120705100c0c09060611061902160203100c1707140304021f0905010f020d050414040b13050a0621110312040306290a060e04020904110316 63
    0x1040005200318102100403042e403451030b040034100d000042d560004198840d501c60a030041c3e40303100c2808000d6001c1d01d000c5201502030001c010a090401c90468a4138400094403001c1c0d9001400c948036802c600300f40c40c44250000c064031071222019000101403d00c0c0c001940000d01c5040d580c0341c0905480032128001d8620f9a00e03800328010030f002101d01544094010781e4080340c10010210103841c002c0e015004071540f40e5600008901e054009000f00650904c3c0ca07044d0340054182a84655102007070b1411150340300b101490554418000c02c1c0201481c2140640010310741c500d000814205400a50040c6500348040110607074445004000045041400c042e01000180241c04524040540d038946940101500e00e00100d80c118110a0f5100c1e0b40201c0c0c0c9140c58045030345071100f4000c0c2d2041d582d454100a00824a5150002940c003107480c040c203420720400b240001d0040c5c551f07034107036503403201c0140c810804070145500700c410780d410444200145102c0c903104611000c1c030031001d65052407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 130643039 1250 130641789 130641793
    0x41a0d2603010e0a20070c0308041d0906091f022a0c040b0901090905070f08010b040b040c0504060c0515010609080d0c0804090b060f070f1a010b0723010e011a12 71
    0x21501942c0e2140782d1b204003c00d031200e1040110200c0030030101401400105048005c5142d03c4201c12860f01125038010300c8402c1c1c1d5000b04041021040c000f00e1048074144642910711004a00e04940390001e01982410380d41c140b1000e1854212a480c0e50b0064880524031000c07907001e45850b1703080006a0740f8407003200d81c011918a004110004041d004059a02d01c500241c41013240c0720380c050b0003076503010350103070780e01d691203254448440c14503229880d030072907007940e06000c1c1c104c03a0307a0050141d02c2244103040810040d9018401444414440c0c1c0810b0052003548842c2035030b652070000d00c40c1d083d5000e40107680c040d43c0d8640b00c103140aa04c01c007041503440036100303003042c0c50400c9180c0181041c41c05250000010032a542c26261440000d08010388030300f0542d0344005241c140305014014044400c00f2100d04000144004034400b42034521003940022400c81c0780f04c20007601612441d103111140d00c95800e000c440100d140040d00714084400000c8a5500010140c0003040290050010581055 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 130644289 1250 130643039 130643081
    0x140706050a0309060e0a0507050a05040605030601120f1202070e0a0e0a080c120f0d0e19020f010c050604030305071404030317090c12061005041a0d2603010e0a 70
    0x115000e5080301c1c0c95113004c1c0a0001e209a186910300741007a43c0114110742ca42c002c8407090040c0d01d0004c102e100076110030340302048030380d0901d00825600c400c10b016641100c24050400350400400d8070421501c0d40d07002c0e400d0316840a181c0c1e00a940d5010324003d520b110204c0d0000a01140d0350781c4640c20b042c0601200030078100c01c02d6112003020394842000300825002d031041448601c0c02d04030040400d0382d41d030b00000341c2d45d104031403000d8100d400036484450315410860012114402d10000750428680488005407100754510044e185002c0500b00106580510310420040c160541e0145215800d60b03100c0c04001d00b0001e02d410b05030301c618000240440c01d00c64048928a59080c0c1055014100c07030101e450120048001602814010101e03529070340c01841002003407079103c52040001d0100351014800b8000c40703031028802841d0310301c00b00c0c050b03c0c90103540010b07c000c51804d801041a0384590105032a00f040703032000240d00900070a0004d41509008c01c03003104486c860319103c140511503501c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 130645539 1250 130644289 130644307
    0x3010612230402061b030304060c090305150a09060606030e06060a0f0b130909050703050c010c150b0307031e141203010b1810090303230306010e130203010f0314070605 74
    0x4410300c007502c2660003210900c44003e0600c80b01340c00c4802d00c28204002c540328034041c42c1500903598191032079401c2003200c1c0c004000203000052444400a500814180c1c241d0760030003c64014501020301034004c03810f01d82d00007613a0b901944404408d0b5000c9064035510380d030342010310500655610901c0d03542d0100600c104560030a490180c5100d445130412018021707524089981a0b8003010010f94407600000b500f001040b80421007081210401c0c204030415805a4441d141c034035000d05d0200d03a80c00e032201c1d224000340d54140000d40c059a441403600710b0030a08200004071a030000282200c11442d0100c0078141c40c1c400080040039404145109842d581c00e0008111541d000140b07025407401907a60308402c11b9645a0340580c02c9201551044000383c5503040c01810400284100400d42c0043c154001040b1400f1f000c0700d6000f042070802ca41403294a00101d14011209405018103e00c003000100b10030034a6a0403000301c5e40140003112084a0f0702600076280c88541c420340e00890401c01003404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 130646789 1250 130645539 130645601
    0x60402090105130e24090705090d05010f0f0c02030f03061002071a0307090e06210a080d060602010e060c16020f03030307030b0a0b070305040b0f040f0b03010612 71
    0x405098189022070070598101c200c40b0081c0090b40100b610304030310760101301a44100c3d01c28501c6212064440c040307511140c9001c52506c03040a407000040100004072003415880714200600300700e9100c402080040c052a103000002c0450300428890242022501c0500d07508c004150380d940340e43d00b12103034550b0300e0743c9007000a050241c0042900350301407e000002c2c0040341c90f240c04401c081707540d80d50360742e4501454014407581890f080041d40d13001c1b1609105003a22034403100d0203603412041d0011f0f500c0c0020207005160000001c8000c00c00040010018001c0c092034221100316042c1d0703002804032200c0c500741180c5a03c812100001a10380a000780e8030134465480d4035210550000d441c01604d01001c03000b203415540210b03254004a03032aa2040b610350b0611950f801700502a05008909003901030fa0010402e100e0f9100380b1107045008181500048080300444008050b500120f20406035a85040c5042e90002d21812001c01e00e400140d28021b041070069074402d2205074806180080c1c005040c070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 130648039 1250 130646789 130646797
    0xf0e06010e0907030c080c01020d030e0a0f140a06020d0b04050f0c09040612030806100e01020d1107050a1d1e01331815080c07030e0303030c070b0907030b060402 71
    0x841d0520803d04000049549001000701809040024103000d601e8000064540300f00310702100101340c5000100d4000c901d02003042c1c1c070200d60140c00d074580c00781d0030308004c0c80d00c4400d10f10b401840e01820440000f080707906d80c02480c9090100e6030610220742520304000441710304680c030080402000000030f05d0300074841c0c000d1008080c004d000180040e140e00d0015200352041500720041041402072200b28907103c40e503129200d40034071346803440c0100b07000001d450344c904d45030300004e000c074200040140800610214000c0e10000c0d0561440c07507510780756000e0740101e0464010800d5000c00208202884100c506040d564801ca02500c159203002c841005450491405410a003080f400704540503c020000806c80d0740c076980d8017001ca07940b0038892403c6080c2035001540c1c03040c940c0090b803d999048030b002e5a00c0308003480d00316120329890070107a0385800032080480e89030000108002c0710040d400003038400740d40590030358002952101c050550b41d110307600000e0401c41c1c025000030720340c2c03900c0e0b0010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 130649289 1250 130648039 130648051
    0xf0c03031e040f0f050429060a0e030f15010605040501020a080f1204061d0c090a050712060305070e01060507050a06050c0903060103120f081506070f080315040f0e06010e 75
    0x200d2410703507642c803c0c4081c03508940014280d4034180504000310302d02030042e4040200c8840f0703400002147c9154880012131510385c440d0060030040f03064079a04e0f000341424142e0070760140a940c0d0b0640760318061519040c1342644182030707950041c000f080c40e900c40d01c01e0310251401a002007500c4a41c60703d601c21641c0001c0503512400c24104407100480c0c1c000c035045030046225637404122135129000400145500300145001e6901c080210740701981c5650f141a040381440700300203020303210000200c0301004107088600c0701605041e00002004000201c0382c0845054051600c039507621403400700c829110380c0002810710750049840c01c1c0410a241c4c003040e007140d6818580c500d069503146c046410088243e00a56600580d04250002c035508641807903541c00b854607010b00685050b450b642c13018401504460b0041c0404150402080b0070f403544500c0c0c02d0703008071230076841c4c0c540400007900201008414500441c1400f11b12038000d2080e0003481c04441010001c1e01d103580c01c05220a8002d440203000b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 130650539 1250 130649289 130649347
    0xd0f030207150c11060a0c0509100921021e130b060d18050601050d080406030c12021206190f1701140405240f010e06031c0906020f0c0303 61
    0x20002c0c05265511500014035038a440b100c03540342e00d40c01d4207420200010080c900c401c2c100091082d00319401b608a502c00d5038103d801c4e484c2900341c504201c42d03110ba1504030321502c50003a55482d460403008500010030034800c03240c41030324100b084110500b003a210308483d45c10540400901000314000d030001144402c001e8810b5080c020520314500a03100100c4440005094120700d0006120b41400101c0c0505016240c602c00006242d40c0ca1500e44a10310605082580d100342483c1c4281c46942100c2d5510043e000a540303a412040a080990109446443c8070784040c0101d0f02495090740c3c0c07400c08031000e90701580110b6280c144c40b40c46140b030070544026107541e648070035044600c1c1ea0101c140110b000b5801028644024625020403402010301c00c00301c0700b007600400c50b03008501c20002e815900072800c469841c0e2a800d000c02d1920005d1004160780240d81c1c2030413176409511070503142c11202e01e0f9084803250050800f10a448100c94055940c05801c01c00c0301240100c030450602c1100350320030341 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 130651789 1250 130650539 130650563
    0x1909052211040b131415030709090204030804060e010e010f030c020a0602070501050105130603020609010f0e13050a1107120c030c060c020618010c02070306050604020403020301110307110d0f030207 87
    0xc07401c881a070260708104500e4202248071103028240d250030034041e054425102c0c03150944200010000c1035151400040d0540c000001580c191091000800800000609544a548900e00b02c0701d25009030090200103200f070820703030b0440d6204003500b4032312a4068480704482505080201c1c003402449001c10150310079081c1d03803000a00c40c0d10050035154040c0c400020703d035040504004d11130070b0040c4050074a500b01142400940e42d4002220500038003402c01c2629611269002d0343ca48404040e811b601c15288101c0286040d8103030041841070101000401600c211b518102413680900503010300802902044c1202c0540111040f0003103900034106032044600030798413071056480d21b047c140700503080501408992018180f262004890b190000c2c0202c004580300295203424500c80a081d1a4076000400d584e80c40d117a04441c00b03941c01034001e009030f000080c4c08100581c02a10b00c0000241c50305210310010384046054002408150760307040904040140490282d0450340d420798101250740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 130653039 1250 130651789 130651811
    0x2040803070506060901080a051f0b0301021606050c040311100e09130506010501110d14090301110301050f030304050d080306030709091a012102040e0a050604030519090522 76
    0x1920728244104000c0c01541341400900004041c1a40140c46540c06802e1660000314003042caa000281d00509001d0910002181c00c1d010309041071420350154800039403d41071482455140c0c0405000f40c406000f40c3c2c840360041030403440b80d448050401090480c5003030862a1940001c1c16500d501c1c41c0c20700c188652240090120030307041d210090b011401450180030450140906030040c102400c0c10824000c28518513602d40034029450720070002c100d40c41c03010b50b07030007001590a82c41c0c0c00360080180700e4441c48030395907035442800b400c0c0c851804100c22041340d2800104035400da80c4050030b40c0100803c141e90356916a0009015a035050052610120710301b45184034000312640140c200292154000f00f081c006907a068101c17008a0700c06001d1004581c50b0090840c1006a05840028007180c450340e1041c2041d0222400410501860051000f8140e100024040c5050700120218403940c1c10700003981c11030340c184500c0e41c015007040c654914122401c4031400041691420120300c0f80c1c003407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 130654289 1250 130653039 130653043
    0x41b051503460b060a030915061401080a02040303020309091305120304030e0d0506130c0b030703020406090605070b0612030d05090d09060e090609040c0e0702030406030b04050f150103020408 84
    0x848400380da02c0010644441c0220124100c40c004040820001c02c8849100c8010484910401108005140e19080b00320200300200c031116403e41d8080c142007040b9616141ca64030740308940c00007a40064129070124400e8141e6100700d404907030307040c0c00440c64001050244025101c00a00280e030800303410078030201154040c08a400c1c5074020039003203640c80c0b50914028020b440d80790300300d038042d40b181c0c07043c0c07400a40c00280d4540c0200c052420b600c402c020f145401500c114403504106140000802449040c40d0540c001d442919150b40ba005005074841d00d040310b040c041c0c01c201070aa6540c0c6c40104070f1905042996600c0508110160303450850722041d14410b4840030f40309d012056000f0303d820081c41c1e13802501c80010b0a218a408152910308000040c0310031406461180700b0b682000100e02001103001c544030080a81032000c440ba450b000740e000e503c9400c68031843c00428245006048a89840c1c0304240c8075044500c1c401180d0349a01203e88890780b92194500c0c1895420040072a800c1c0d02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 130655539 1250 130654289 130654351
    0x3030403150b180f040308060303310b1201090f020d020a09050f030a0b0103120302041a070204060b2506020904020d05090106151d01020c0a03060203041b051503 71
    0x80d8440104411a902090042d045021001d03030b010f0300d400000380540c07081541122a0000c1d09841c01301150380f280800a811481071040078000c03490301c030320705126805144000ca503411100305003010400366102c1420b03c01744180c182c107401c0c20041c04014002d811890344100c01d28000400c0050400c0840b014510407070f4800e182d01c9002ca45503003002c000d1843d010380951003540f000d03030240c00c201c0141d40c0d41c1d80c54404103010007800c843c0c50098420101d480f0b41d058034000c01c1c005100700752040c0130b035551030380b41d9002500c2603010310f08142c40030480c241010308540c40e84511000005212028010a02800601c0031086a601d90208940d5074a5a5140050b0140405820700025a81005495182120b100790303c41d404a100c07151414001d143c1281c000c05040451040710300e15801d1040041b802d0102460324150b1001b400100482846010341c00f440c445e0f40b041000549400303040a16414211081c492654400f001440c10b12000c240c25002d560061401101c1702e5030303030320603580c001030a042d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 130656789 1250 130655539 130655573
    0xa090507170c06041d090708030406030911030a030c030201050f13020d020414010603020c070509100e1005090406050901050f01210302030c030c160f0f091109030109050102040f05011b1103030403 86
    0x2540303940d480c05d10b28508803084e800c030fa00a001403050f68500010103403240600c0c8035190500d035599847c14240700c1d030b010422842c8880103090310f0520800380781c090900c006241c0c054005618000020304e0001621020f9030140d040589650f010003000d0b420001c2101e03e80c1022031708661501c9501010243c80180b09001c0d04441c0c40140e241c0c003031600034a29204c4198001d6229040080900000b5940b0645000540b40300e20b15071011603598640303003005a01140c0c845908040701c40300300000c1c44004c0c2d1100e030150007070310000e01c02c546420ba442e031406007080c083d0325841c01c001c800c8426014001c808944200c2d02ca4015241001031030719001c0d08540000c644e0f603e80707812030b4880c1e0714098007598031807010300604040c10600501300583c1c1e5001508500403200c0d22550b034600c030072100040788151002100024024001c90481c5d103407050207034116104046150200e907601040541c01a072010040c03141c08000c495911100b078894000302210142100d401d800100404404140c8845568101d14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 130658039 1250 130656789 130656809
    0x1090212010e0c0102160905070507140304030201031a13051e04050604020406060512060f040209190e06150d0b010315080a030206060a08030a110106120b0105090a090507170c0604 79
    0x9051042410320010b00c3c0000d0464111140089082045100107000d44040010001d07d40c0d9482106480e81d02c2040c0300540200d1a00000d0078035080c0010040c02034074400e0740c05007c100784030315440c0461101c0c0420580c0c0014501c2001c117604580d0350000d9400041c0080c1c000e078282c025240701800300c400361001d550a4006c1010881542858010900201090b140c11468040001240415886c0190a092007020216080180b55035241c06455004c0c01c010081c0340040301d0307405203011810325485400545268280005d0740d608e081d10300101c225521180441c60003090603178200081a11446442c1890350703071740d043c8205c0c640081c034410181c20503800512a01d4410305000e80703004802000c840c440d8076002030903c00c081c8088203403850316081d4181190650100010140502038035004900045040b030044401e002c4900c2406040703400076504d804003a15101440d1090340d8840401511540c8010380805c80800644010407040c80c03080241c1d2107160b00c0c00000386d400d50181d80039032020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 130659289 1250 130658039 130658051
    0x6050403050c030f0d0f170a0f0c020102090a0501080c0706020f03070305280c030e06100e1308041e0801140405010b01090608070f020c0301141009060806010e090109021201 76
    0x101c1d04000c46905000100c00802e14215000700e101e40d24010140603d0402034201c581600b03590060440320001111046048401d24141c01201d0041000510040103641007640a5510070b00600c200c03071110030090404401241042c0056540d210041c4c08400549810007017040820224406000b6070000390101955904100000509a64001e000d940303c0440b400a12003111040702542424a01103a00104003044100d8017a00100050040c44455016200412601260200f221003e4076991403c0740c90548465136500703400601c008004011050800043c000038107078840d082d4107402c0341c21540709a035449141343e1342510b0503103100542040c02c400520007003207000e018101012a0a00c0d12500540c81c084008010110180a0300240304910040a480c2842070001c40c94600b00a0000d124000c08560030a901580031954105040f901c4031000c030b00c1d650756001c1e034000c8515050051002e64285901a9054100a043e4043c02d40da0b81c0c03802001038454a0110b800240008000110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 130660539 1250 130659289 130659293
    0x3020907030623030a02100c140f01151208090307180b0907050309100c02010e03040e0a060501020703030c060203370c020a030c110d050304030b0108210d0506060d020406050403 78
    0x207858110648007511011900c3c01c29190f850014041413507640454003014660500041500c1456200102a046d040a4008030328039050004881c1580c0f04010001c0000506420703031000313590110301540d201c03c4030048404c8041200503014081340301009069134803159480b00d11202800355800910700854541e20714503800e15089074841e502010078102180381d0f1620350500e540b5240b0440c010070744650342d0300300504414401d6024a00030504c0d20110380d980c3c1c1c0c442c10104040134044a192300e120b8141080030035207500c023081d12002c80b48c0c162513140f001c10709544c414010f50002404101420520b500c0c41904603a80450440203200c6002d911721815003841c00801503a4180c003c030b4055500500d20040040e6103d40100c2c20030f9000b0011142c0582c440000075100340040c40083d0540c80301003030100034054864003a5040364002e400325424410340359155000303200b5084188641c0041844584500d00541e0091680400e00502c504d1410000f816600c0403a000740c0c0280d0001140402c00307100b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 130661789 1250 130660539 130660559
    0xe0d020f030f25060302040602030901120612050f0c0a030507180f06090b0a081f0207170304081803060423011508151305030405152503170108030301050d0c030209070306 75
    0x80c0004c0e14040d49480c0c14044007941c0da10411016a0400010300d13442060880c245e030100000e841c10040e00d042000c224140107649a034906c0a80b05540558400804d9078508924100116540b00019040b26481c204d0818800102180d040070141d07285c900f0325981c0280c900c6400068480340200207428a0050706000150344282c00c040340780d0348410070815802d07006884003000da1400c00f80160f80e40a981c80c201001d00454141082100c501005101c2080110005001c00c20342c1507504042d440062008c26035524020f403000380044240b658128104990540c0e01014041c550b400450380c0c0214040070444120298442201d50f00306050f1044070110a2000d250000e030b030366000e44401c26060319500e88910452084602c1200d6400302da10005150b01c00b51800040c01c640c00303215030042c4031506844a110701c007045000601c0442000c1001d0341080b8842c5c180e60000f0001c5096a0a140c1404110b25122005031026111000b0010050355110215486406165004240c0a280c200042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 130663039 1250 130661789 130661863
    0x3120715091a160504050d021201060f030b0714030f13020d21030e07050603041b08030304060b1806010318050708150603120d09020a03060906060e070e0d020f030f 72
    0x846083e100750b0442c400c0d990102c291420345004443da0f800c50003840c4009280342c0e5400c504001103500f0712800180c80c446900c040c4045078006c10003d2001d50328034400703ca031450300e80c0c1040701c103200038000f040b0b14a100c58500350f4414070102100c004c480340754001580800e2020411103104041c0031300c07605c0114041032003900414403030405102c40354040c2031030340c0c54003102c4c050389000c1d11380070000500740300324508074400824002c00071001b12600d8005180d243da004070380549400e03051181c00340480c2800c1d40300c0316018140501d8007403183c0307580d40114090001342030100d03100c007444041c98020640c14086600101600700c004c240c95401c07502d03403541410004100620a0300070010f00426000344108407114071a4081d4002a051442d02c0001c0d82c400e955000641502d141c21030103c2003007019030000003528907440b44101a03503501d40d02207590445428001d904403143d030b108a4010300344a1514401c051004054410182415800925000200d050301520815030b410902131440b00407020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 130664289 1250 130663039 130663051
    0x30118060b030c0901030b0901060b0a0c02010207140d060f0e011d0706021f0b01021204030308060f060c0c010e06091f0e19151809020d050f0603120715091a 69
    0x26103c01442040000c0c040b0382c3c14840641100e20010018641405c20361110000d0011109603035200d4010728401405074610503801c078058804c0c00808030b615101908400ca07030724801051884501c0f40c5a442c0c20160113120a10b50740280c031150741d659055028003606006035800e2401580002266002618040071a0302136029500944044906048071301a0140c012920240102d481003003400100d103041407154210f85114000704d004010176078400d403105d004410441345001c0300d035602d20402c241481103090041e81540040c1610485500414400c0d4101400400041c103042e04407010070743c40c1c05608444c80020251a2101e284181c1024554214220035178014050101904501d8440e8040717009900c0680d110502003480c8900c586140c83c0c40401038210032500980e21004280603400ca41c1058240c0e0781010002210b800700f144405204090040c01012350a185240d03104255011000a0307901c481d4400102803060342c03500440040c0392045064905094800025129451001c5c0c03031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 130665539 1250 130664289 130664293
    0x50103050d0503070c08040b0307031407050a0c1a0c0903060903071a06060d14090c010e06040e18010507020703060c080403021c0507050708010510080d2c030118060b03 74
    0x14804184001000c2502800904250341c0c0c0742c07140c02c8192001d03108041300a09000c000100410042c00302001781d801410b40d506d083c008854006022001c182d8125074100008405006c0740040d00d00c00d20848003403d00409407400005d08003042120209c1044807047c580250005194040e41800c0002c1c03540040041301a5041a00c195034942030400038144401c0407901190119000e40d40742d03401c440c02c2400c095800c0151000100e03100001d0750040b20820329500403600c10781503550207210f0903004400010203d51905003000c10412240700c0160108800c201d038155248175260092003528040e0082e42c0060a03554a0b61034030380d0175100144055400c0213603503018400001d0b0001030500705c682d034a81d182c100c09040104203c486000341100a1302d140b04998002a8004c1c040d40403500aa004040450059840c5c048017541d1354520040385001405070440c8104048010b0101d2200d995038a61103030038141c0800000b400d49200101c0561905030040f010380070800d040c07203031034160728003980 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 130666789 1250 130665539 130665541
    0x70c031a130b04150504061401050a030b0c0c0a0f06020909060402190818070e04050d0206011a0d18050c01080a0c0c030e04021905040f060305010b160501060b0f0d0b0405 75
    0x81201e0480c428034000b00144080070104042108410400390a09200c980030080c0e4078207070401d007020340700c4000c9130b16041c83c0a07000411641000c8110701c0940e90007544900c4241c0700c84055031500ea1107841c41038103500600280302d00180e00f8201021041d4021400981c6545004080110312040038152520651042141c03000520008030215007a0040c1e04110345556a40405285112003c042500c0d181c080c50340081906e210300015103011354060002c031000ca810250090717950f000b0a004801c2e8500d8803410350310b030300e41580004014041c00e64502013000da615110390755490310402e03400c40d2945c0040e5282245564022806030784850504014807481030100b4018021075050140602001490040780301c0c1d9403035075012a410607020100c1d16008010b0007800410700d82080c003600704400c45031200050034038401e021341070598903003102c0ca600e000c1000c5842c0b00c9507582210110b680395203c00700000e60600b030340c01a10040180011780c0b99208204228a0103e651030f2201d988900d10b048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 130668039 1250 130666789 130666801
    0x109140105010e0d020102070b0318070b03100e090309041a0103051e0c0d110304030e1809060112030c05070f061704080f0c030c0d031a030f0a1502040b070c031a 71
    0x514103040c00f03000d8400b0302c0c002d682c1d800100c0c140b810541000746c00000000c207000740a0f080d07031144074000905100383c902c07540c8c40d518446201c0c4000d41d01001401c1642109002e600c46056000343c02048140c11680f914242802042c140c5070506000b00d02010352200c1c00f0f03080d58250241710f50001c0c013078180040112905505107181003025017a1040c0c0710000c582403030030a403958801d900414512032030640b40d241c1450000d0001100035050790041c268800043c5032100e880d0035007030040c1c140f200607002e11b82c00c001c2506580e141e084000c0c3e0030850040d401101080e03003444100090042c0d46000b002e03c5040c41000b904106213451508120398580c800c00011400d1541511a42d405500c152039444141440261030f5005154900b003090040714074480c461b0341c0540c041c5005940011a407000315034a501050345030010b40300424802e420132040207000900b00000285280b801c0440141840d0719500c541100360018441150003091651003401030002c58841e00700380071000c242c1c84400d0300d014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 130669289 1250 130668039 130668047
    0x108060f040303020319090c050307060503010308040302060d1d010b0306010f0f0b0306220b010311070305030a050403030e070303020f12091f0302070605240604080307030c020406030b0f010914010501 88
    0x780050101540840410443c25040c0c01c2410311010311031040c440135000d8200a1200b58071841001d1091003008070000301325020308143c0341240d4110301044e003018556000d1140503440b00c1c1200005640c0c40c08818041c044020032503442440e1031000141d80c4080d0703c1030629120043c2c100b194015802c1c00300304041510700850000b9034a0304e59110341c40740c4500740815050b44809070450901c4d609032000707029101180d440b40801030350990741030100540c1d10146000307e101e00880540080e5003000000c00520254101c5900280b0a240004050074240d00f10303070410240e90000c0340160424141040000300c10403002d00d02407885034160349005921781c00251035030402880030b1149240c0603c0d804403140250706541003660024824005860700400c007400c035450018032101010720303600c0500941e050020a071000e4500e401d00651a1070103644003500c05920100c0101d071300580300d03070000c0b000900141c0c1a070300913044010000500e506058101c800d4031065407000008001c03d4004211a03030f40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 130670539 1250 130669289 130669291
    0x90510020f090d140105090f010b1c0308060f03030c010b010210060f03020d06150f05011b0308070e241b0607050702040e011d0c040e030403020607061d010e0c090108060f 75
    0x403990f000800240d40b5202d07120402c01c0c620074019501c0c000030031002840200300020b200203c5002008030110303400c104908000c041a0780c43c10100c41d2900980064028000150403000003842e00200741420780c002840c5034402d105045899440702526095540c042242901702c2000703410500003e820725403c1c0c0c24455003071101a225401110054042c49542c4d40504120b52500140104035515a03020040c00005441200c0c0024440c50114038210841540805010b40c075070307103c1081c1e8441d034004891036009048c2440c1d0082689940034070138242d6030780301d80d4206100f170b1000351504103a41401180605c21080d0781120713041365040015041d0300c18129110035074101e400259040107499810700500c095802c0d89550540780301a00c603114400580d0400140080300c080c008550080c3c8a00d40f640100e200082d0894410700c0100002041030704610071314008108060540020100c2c05401c0d82c1c800205103185400813403042140d401c0007083c1ea8050070415006100e24180180d01d4200e00304 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 130671789 1250 130670539 130670557
    0x130f050f01080f0a050408130f240207060311090306010e0403030605060a02071505040e0907180b0a15050f0703120506062104020a080d021c0f021e03040506030a090510020f 76
    0xd07450001408200e07c0409890706079524030392071101d40b521b40c425040400d02c0d0303004085a110714041c50001040c41000103008503441c65000c0e0401602d8620142c0280c0806502100245401c1c044105c240d2010041c240c020154081504114101b40c2000340842d030903504031900460041281003011070300040c80304100c4092068801d8540c054010484090041c0d03000101003da42c941481090035000402105aa01c041c0d80d46189032001030043d411190803510a581000c065841040380c0d9103001c9501458843c1804c0c01490141c0408040c1240d901200080b00407485e0042552100311403440750641c4260251010b9191041d40041c40c3c0c50104508a100107040e00b600000d004c5443d45a030004c010880c243c2250115029140007a40b40c0b5452003002880c00b5003200104984c070b1003419100038080c09038020f005c402040007543c2c4e6004040c20748136101c510042200254035195140110701c50041e20074001401c040d03515140e820404908149403c0d00d0040c04002c0041c072845084540c529 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 130673039 1250 130671789 130671791
    0x3080d0603080706020304020906030106060c08090303040e190c050301030b061201140a020a1e08070809010608060a0e15010506160c05040906050103030f260903130f050f01080f0a 79
    0x1022494984080c02040d0001080a00701107803040030440d094019500580c0300f100c850301c0c940d440205150072601780388503140004600350b050002148401c4020145990080c09891034140c43e90440e503480c0a007520441111248031800320141c1030a84112040025035150451543d403450702c441c100c01e44003602540c442c201b54002507820740000d41c44030030a140841070007201440e14903841c9001350054080c1c4000300d500c07408400103205a46003000388015603604c4054854a0b15502162810001031030903149669406000c101e81000700400380c460002818049200d05c040c010003810820000c000780c1e1414503003001030210341c0d1808150703000801d69003041e00d03000405051420b26202140c3c8115081850003840c002400050340205050702d0180d1035884054581c0700f02294040100b0700080d00607824402d0550050342c00c00c14440c1c212409204590405011209000104400c1c0d480460025480241001942000c84010707500030307002d00700f03410589840c0032203150481c0c008065608603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 130674289 1250 130673039 130673047
    0x21201020f1b030c0703030f0905030304120611120c04090c020f060103260409091103030f2d120108012936010503060a050702030d05061f031b1403010308 68
    0x1c2003c005039440070700c0032000c4400056507414040c04010710790400e90300050043ca404107517404c0000c22903040b1003c4510044205141e5120800201350401404845240c200120700c080d603013140c14280681ea50b102c0060340c451070a04220102c2d0314021000e0255041485407000058010403c1411240c200e017160075402051905081659803a90b07110b03000c0b0740049404524490154000b8002d02e1140d900f908011500504042d581d00840c40108000a0104515040480407640c0c034170104400840540944800c40310200c801d0b0001100860340d003d202c001000b0815003401440c8088207c01400b0900c141c4440e1408840081d100403540640700b1404403c100c00e0000b94001c442900484201009402020007151001000e200313040c031922824022428040e09840b03400e01500058005500d030041207446075018220051070584c0c40401c00c1080c4d000b0300002508201520600d942c0018403001156a00c0d031403450640c91281044003005072030703100c200060126415203411521603603c1d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 130675539 1250 130674289 130674337
    0x14011706010c1b0b0405040608030306090406020f07060608011a0910031b052107090213050f01120e010e01060e04121805030a0c03050615061e1b0a021201020f 70
    0x504030b81c0d07614510100c50750f0310000603e400e05201030001e80790b040b68103200c004d6440c50056564041500d4a546c0115440c002ca000030740c0310f81c000c201e00740102600900344900c9071645012600158400130035030b5113401d05090020382c030100c8803500a004aa2050040c146042082024415800300070500c0f01c6014003500c84c941c101d1918802403000416240403038203406031020000c0d00c0481d24516a105030907010804071000e0003076514500d142c1c040001d143e450703c820803d5001440e00482e042c480030001400d94000c2074051150910f41c410008261205117800f85070854100c1e40c05441044076440c1480002074012074000b43d03188161600041c10755014107035001286548e03000700d60610800c240b40c42041701c11920107080300d006000355011a518000861100c00c1c0245015910003004c014404040da0a0310010020031000d10714607080402e070b07945020300c0c80402c44440f0786d550710000c40d0300118035101c0d6810219900035402541000d6440c482c60040b4000d0315050040d9111001071052 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 130676789 1250 130675539 130675553
    0x109140604060b0901050d090f0f0212070b0a03020a1704030917070302060a031d03070f150b1f020106050402120603010507050f04030209191b14040b120a02040f0305060114011706010c 81
    0x141c410340240c85201114227510380000602c034020310480c051110300045d03101440021030b0240441d49000350040c51318168880440003540700341540d2042c0100c1c03059200466100358003451160b4407036220313140501c0c10302000d078001c840d070340c42500302941c03016006000588075a4141c1d0081990307401c000c5076405803050440744a0300060300002c220f10001c00c5880034001650903000300d05001d110b40c10350a5503212288015035200202698101071450101c1e4906804024001d211350120300c00010450303155000a0280c0c0e11404280c9100302150040c81410300c1c081c41465000465428101c1c03500310071542c0c001d1240118170019200380740b8000014803480804020484242600804105c4900e0455440310095080c1d040c280c00620a400c2c0c0700c0c0b101051000700d9080c1c2c0d00390101c1509140292000c840041c0d4000c201803001a02844005000020000854081c5209030090702080d8108900140c1c01c102c242c0c182c1e030401040c032052420074429030200e990021803e00e0007101c102002d0601d04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 130678039 1250 130676789 130676801
    0x182c1b0f03030a0c0303050114090402010c11031b0405070203071a07020304180203040501050c0913180602121f03121209020a06020703150614060a0c02090109140604060b0901050d 79
    0x35800d40800641c080c142580600006a81071280d00c2c20405c5076200d40740100303140e0090510340d81190804000c600950700034544070543c00e116488100b02c0e4a11280440d0400900d006281102044400e0b1b241b040c1c5014001e0942c85601031006605005803500c9510480700008011480000a000031401407071003482103501070714403040004404030b0031300310040080d44100c806035040d520b024045012913120004544070054003c0c10072403005008800e50004058480d000755030146c00705601d00014402e800034003c01201400b13200258036001031340d005000302c800c00034034004a050f8018400208101900c82c00c460715407034943c484820034000380f4010011440041c1d4030040c035280004409034006151000d0300c0c4980303600c014460f140500103043e52a54083c1040c001c45040d043c0342141004000380545515600d4061550010b039000302d4106002038000e60352203a15050980030650f08001103075003210081d10208145403034800b5842d9580220390300a4100100081c10320203100003a0404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 130679289 1250 130678039 130678069
    0x807030c08031302030f012c01060f060c030207091b0503040201122406030213050d030c0c090c0f020f070513090203060a02090102010b010c0c0302060306010504182c1b 74
    0x840c0d5242820024000f0307903a1480b104078400d00c41c41c03620501104040c05142581401c11600705540803c01401c070701142ca50302485201d0b5075070b551000070300c20074085080000388030361340b80d40e010b840c26400c0080c10f01031150484200c0d40d013881c10307112000320702c01d18080c6402000d180c010340305e40302c910040b1600d18000040420031030a003012101e000034007071344541c02840803110240c003c0ea9100c000b81c050303002d02000c10111b071034920410012420103a0101058511900c1c00c4014000140e80d1440d0b0710181d5004410202d5a82d9010f43c0d420340c0081103041c2c101c800380010480c1c40e0310040000e60750107103400780502801030412040072140c00d6800010720180e004054880b6442e00030b0521000f500103c007014015824850014050b5000d21b02d224492070308081d030b0421036400d603004e00c1f500783e02c040c1c0058100070007000001031000001060b50164580c41201103403601003e1004e00c601000c00c0f0f81421060026610707024482e41c0007603903280030402c2c0e14140e10000101c0f4001019030f9006110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 130680539 1250 130679289 130679303
    0x14090706140c0a1211070f1a0702150a200615120a06051608130303020306010507120e090601050a0203040e0c0409020408030a0306120b0708040501151203091401020304030807030c 79
    0x1a510070001c02d241300e8618405156284181c5800201074956506414895103036140c14001050280300e6180340c20000815040d8040c030f240007201e0740810404606150f40071400c10001c03c440b0310251b804214007030ba9004014810944640701045207441c0c61026003004202c0c803294020002c180ca0700d01d07040b11000400d500755244d2050a080c0703e4007520f022261003151580030048984051b008000040c002d40f42c00c2000c4c82c805019640a40007980081c10301d5061240c2840480001000b68402900a0700c1c50b945000c00780a402041c0b10301c50b4006041c0a05000b0180011010250700000f0303601219400024503103142c40b0031340c20000600c00c2d5001b1020342400000c02190800300000100b104041d555404c1103c25680c401e20805038400c000014900301c2210042440140300314810740e0414001c2d400015040e204411041c00b0308195403080203464007441c081401c0c10b03000b0072404002c1101c940c6c01c14420443e000001c0d12480b80d800300410300342e000320300f030000d0600c00c03000365042c1c0781d210342 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 130681789 1250 130680539 130680553
    0x10e07060302070605010e09121e071406090f03031f0e010902090307060201180206030a0219020601060f170402011b0b01061d1c02150c0a0b06030114090706140c 71
    0xd00100a58004081540d6141c2081d0000410483d0101c1d0035100381c12001c060220f1000c40c41c1c900e607283c0d0141080800c0d50318030030560707451588810014107216110b80c44041e9041c2008241c941045001045440c054100781d02c490a48000402202c1d4402c01800b40114421003440c491869127507150805504421450004240b2041540c018203c84804904690302540e65400c101c0c00e0340e00310450325408401d078420344001030030070102031500400c1400c5c003d03003480c0d907400ca409140f10344610a480164060302c010021180c1001850020b04e141c3d2512a03100076094201d18140b0001a0000341000103029002c040070b004042c280b0842ea900c030282c5400b95139965401811200300500c102c038140422031000b5a14a410200a804c1c0c02d0010340f200c443d15866000c1028800d03a15000303c00c045001c0190301c40c000b17814092981e100d840b4450b8522541000b50900d400c41d1955004105480380880a000b00b15030000781110881d01285017001c00f4180b5004282c615016410180c542e603c070b071340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 130683039 1250 130681789 130681799
    0x21130902070209430215040302030f18040f0606120209060f070609140703020f0a0e06010315050310090c0b03010605160507030209011d0708060a060e040e0313080c0109031a060102010e07 82
    0x110220450f44c195030813034902c105500c4046506590603a001005a8002c002210215949001500304c184d103180c800410300c10118003250503121032804100685a650750140703e6190402070301c180c6022000c20460a081c03a002c040744d0300e27124116020801280200340c0c2010030903030350462403059900164032901d00c25410303500c2e070740e0346030301e010481c42800800d0810a150506c0c0718600308845038100700002c1c54a490006600814001c0e03511030440f0360081c4080b40c02e0310708002d1403076001c0503c6000203059481e41060142d0038a542c00526110104000410089510809440c00e180c503519210700d01000a01d0190b1a000303480d80001d402c400f0540000031071058644200c0342e1034400321541e00844e91036107411945a0022541315600005211062120f20b1261560000c20329002c0c100081c0756120a0b80c1501c2c5422455000b0303c0040320a8061002220a1044001c08503080c2851310f076150460f9a03070228030442c090100c1178600c0381000900103a00c00d40060105030200c60903680010f03214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 130684289 1250 130683039 130683151
    0x3150209120d030f0c0c0308271b0a1202270403080103020102060901090b010b09030102040815061201051302040f1404060b041a09040b070221130902070209 69
    0x10001c000b0202e894900c6010100707050f801004e11200031640e5040c1034500f9580c065070700d00005014540e030b002400c0e04034009103803103c208034150300b2900300800c0002080c0581078006030101c00c10b41c0c01a04201000c100003000c14601480e5258111603901d400b95251440c131650031119213000f180d172100c3c10301340710905410100d524140d900030790a03660645e0780c02e2802402e0f10403c0c08000e141c580d1201c01000f034030300804081d00c2e8005000b400545071030782e500b403500c0c58107007026421440c4001c018141b1405260801683c0c045000a400038407081c5010008d0210056070b405000e07000c0c0f51600f403942c42410080d40030743c0c2c588101084d112030303130704007030605c500208000b817420f50085180852454105002075032841000724010451041503907669104800301501030000010b40c400c00d090301501d5540020b08451511001c5005601c8075240039035806212210780c0500d540ea0b00c1000304d080540c0765803111035409800d00e501111ba100c0720040c10700c000f400b4051404903001210030006290025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 130685539 1250 130684289 130684303
    0x81b0d0b010e010309020904120507020915030d020f0607031808030406050f2a0f04051512010605040501120b13090309090b060a081303020a020a1d0c030c040315020912 74
    0x1003a030b80d900c0740740c020300015003c40c2ca409030301940c0500d0ba0030015000900408030150341c5015443c05a0912450740d0100d01a10801d8801074004000324818099500701000500480310492005052001128490315101c0354058154810951543d000078031412840540d00d8040380d000c03107015074910f010304141e8000d100035541031006c00c07071702008151542c01400c404c1180804d10301d40034990078a18080c10007203500455000c021040240400903003541e806001c07842c15038240e020703d40d41c2c1c10001080c49482e10141c01c0402402010b0000744801c0e40c1c802004200c48148050000307489040400041021120118502c03c40d800c040c941410103511405100848082000c18400c2d0b0720b200c0c0401016020f12480781c4005113212000901b490a0601d1054015010f070043eaa6210b50507004a80d0148081e0010248154882c020780100a00740150903407091150b5030320350071400c1100180c0250f108520001e801c1300f01031195804a00c6040e41142c3c000312005004102683c1c3c150300d09502c50310 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 130686789 1250 130685539 130685561
    0x2a0e040b0708090c0303042c0412030f02040f0b1c06080c0102010e0d1425030e0f01140d02070503040503030301090c0f02150117010b0909010614060910081b0d 70
    0x18000012070f194030400905080b0713041c4020050350405080031604075041070694544620403d88901c0304000480000200c1c0c020fa011b51402001d628420381c001d410364140e005101902803040100b04000d0305d44540680681d00c501c0001d540e241c0b11450018070401c6090040ba140074036203000018002000034079244550020b070000d100e000511182079485040502c12280490300f440c0c501e00107408505e00800a078043c24205400f42c0c1c0c03007501c0701800301c8030105044001c500e088008444610341000900c1c0000340034a0001c00ca0404144d281c004c038043c00702d0500f2903075000f180701c900300175040c0199006003001900300c940365030395050081c019101d0340f0320030008210b01c001090130700b40c40404d40c5400600c00c0342c480c6029074a03208034843d01d26510040b2007000d5603140c0c50740d401c5a032207102d40d500a85a1000104a0509029500001270b26559001307104000400080c0202c0c0c1352980c50100d1340900e800c05040b075a844100c010b0001030fa50b144401c0301003002a00143c840380399480209052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 130688039 1250 130686789 130686797
    0x220b16060c120c03051b030c040902070807140c0906091e060109080a0b0105210606010c020d0219030b06010201090f0605130c060206010e06040905030712050d1d0114042a0e040b07 79
    0x30251b4201103100aa8078090302d00c000704030500506045400400c51644100002c82c90805241c94400e81440404c04904050b0805200b0f0102441d003003590715000401220001c030103041424001000341c6006120401e0070722210009202030380074100d0507000f44444815180e0488031454030311081070090180a100300c1010300e01c0013500e0082c5510b081c07030064038400cc2c0829120000151100c0e0b40c041c40c02c90307120110b08080001070312504c82007981007584900c001e11943c11031404804081c00140900e04680c5030403d40400310b810b400d0103005c02904400f00040d15154810750007800b140009001d401100b01601c0003805036800200f06040380c03c12241208191131703600420090322a05480601140e20500034000807445003126001c3c0030b580e030709000313203031485600c18102581d481000240c0304031403203c4540c040510a00070b035410804694800c14003458a80d4403c6003100c500340b400c03040b02a0003100d003400c0c441d080303051002810307400705c03a65801c3c505071900300390041044074050005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 130689289 1250 130688039 130688071
    0x1e020303041a0105012001060306110d06050312040b0d0f021b010608011b03021305120d02100504020901030f06091703041208061005090a0b220b16060c120c0305 71
    0x30080b030122160503907005035145214450034000103100098801540d280c5950b80761000000a03040d0b1141d0ac44070811004055101d100703001070700c0c080700d900e40e00c02e501a4211220000c80c601c00c01c1c040b1403d032110b0303180c0b00f1b448880001c80c41008040d90394803144a50b10004e600c50031076040c00780c9403902c245214024072070561610b1626081c0c0740442030202c100040140c40e0a501d074040e8000d002366500345a5041d0031141c1c0c0f5800500c5594031281804820f400101c910140710340d0500c03201020800c280310900c05410302d90b02061101d501440301419603403902a55004002154110007512504002a0000e04441c4038070840c2d00e0b801520215515080140294215030041f100a8840c2000400c01e00e0030890207103060300c1c1c1c1d5014107a015031250111002158084e0b00d10040c1401c80141030091241c10085e21504014500e20382010050301001d00c840d140a00c480c010083d05968810800f2422160a1000b510300340143e070140d204250405284200700759160f0700c1584603148841c00d401070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 130690539 1250 130689289 130689323
    0x7050c09130201090e0403021c05210f010528060503060a05030f060402091e0901023a0f02120916090c050d09111201050726070c02011e02030304 64
    0x1c9038204000082c003141c2c03c50030400184044114a951190080c010f86d503103034041842c00000300501071b01000c0070580c040381c1182ca80c05c80610742050311b0f07031801c441032a500b8905c1e010300c00c0f40c81c1407141510440140d10200d40200950f0656258441ba0910f01e030500c0c1e0b141d0b00c01038416082161914000d6182090014951a00050008a412542c005003949440300d400740705240030014003150549070810f40d80c101c1c00302990449840b407401c41000588070900c210b000c07040600e41c07403110a034810420640c0105034100304400c0000c002c1d07407400007071180c03030416182d0041d008a21030306a4443d10902040a2000045206004214004c486035803498030750482d1000c6461074258280010824081004514050390000450a028410140d0030a420400240d1300000c03d51695813207075190800c0c030056580000320044203025203800035161080404e58074041c008002c14075001c101078100c0650559003c0c003c1450283c07203690718100307100c6c501800a035482e13005850480c0e0740b50381c1401ca620 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 130691789 1250 130690539 130690561
    0x21040317010509191517010b040b1302030403020c1c050609030406050d0203060a090507050703020f0a0803040318051e0901090b03030913020c0d030504020102151b0d09020607050c09 80
    0x41030300c2d802014000d2644030550100700c4c401e201a0643c500683e81c0340f01580482d84a0070403c002c08428400c030f040707420014062425101c00c0420140900d0a02e51002d0301c0d5075400361003c00109401c1001601c941e00ca080480c5480010541241c00c11180c42c1c00082809880d00d20300b02c020300580c11900191619400240d0f0b03031043e8466040081c40610072400c2c012082d40085810400c001c20201c9110380301c174200004c889094035200d0105a00183c064201501804130034400802c0c1405098030143c66140e100301840020302c014204290102c520308000d44030404013001e4000500401c141001c0140e4511904e11802c903100d106010342c200008030aa15405003150710a4081e01940c180351a01040c0540d406004111100098080c020140754250805c94441e07449059507010030719081900019051105401d0308001c5081c0e40c80800880c003e01340c0c120011400c1c01e800c529552a8100c48100040132107010095003d0310008090003404000541d010109600316040710042d210400c00340 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 130693039 1250 130691789 130691791
    0x90c0302240901050a0504050a121a01030201122d0f0f0b0604030303020c0703060203040602120c0a0801060e031518120a08060105031e0415180201020c0f0621040317 73
    0x80300d1410400c5084000c0d40300e03001400c5d544400b81416410240c50b5400214414060340210583c107503001e80d000f040c0128900701a40000c040754001c4001d50440d000205228600121840c28a856254403d0f0a29107c03203180b000c030301d00c0b51401c401c0c602d41c3c50f900030141800130910002075003880c41c0180000c0051040c0e140e6460000c1609141c507143d6581030780079402051105040b40154080080802e081e40000d61040f40300d00b80c0140d83c1c1014580d10501d945002e025115078200a00078040d025811050150540f442400e00407640104100028980f10014010800b020a0941844005542e0301401280c8165071026903014505951111607a03001d04c10320480041c00010115265501a9000f981c002c034010780144904a00215a0801c028003070306d04450f40c1240c8407821580c0d5005201d440e1001440c0020708200e2012900002d41d60b40d441c0300e40034400c4a00700035195207640d83c1e0b81125200d5280c403082214400d460548802e103060100e8042d800b00c0c115440c140880c1c114000302c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 130694289 1250 130693039 130693099
    0x14040203061e1b04150504050307060f050d0b030f010c090503010c050a0512061903032609070b0f12040b040510113c0a0e09010302031903020c04090c0302 68
    0x103840c250f07240d141d40c0208200381c03a600c00001000f0080420740611110b4405001015074a5481d521842c2006161a212446d481402005580034240c0405540601100d03504904030002040d4255170b00700007420074041c2e22258003150300c0c00d0ba10008280c1c1010b004012a130044000b0840801454419501032007210000e80001d541045080300d45246112140d03005a4054907034140c00e180c25100d1480c6054035081034021030004260800810340e0021000301c04914403045a0140c00d1004a899032981c0c80d000e030b0704c0350040100305400c06256002c10380b01c0002e00c003031003c0078608050600c01120203007600c05070360a0150700000d0384150520b00039546000840407203035180c1048a988a0f42010000070400c4071101041900b610400c0003058807040300d2000c1c010251b5503d01518044c182c1c084081d0114080c4090000420147c2d0b00442c0b06001c0311031002082c031241030b0300d1a040b4105004503034080d0f4044e24054401d0140300c040704251741624425070b4144030b600d01c0901851030555000d802 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 130695539 1250 130694289 130694341
    0x30a0201170a1b1e0c031d060f03040602040614070807030e0121020d0605030f030d0216050105040602091513060e03161229061c061404020306 63
    0x2200c814481e0030901154046070642e0000349548618045194040201c00b00000060200169481200c60400c0e0031003401c402c0c1c10031420400301580c0140c00740756000c8005055100d0030f542d2041c1500c485c01118414511700050594900e854a8840c0081d04203002d13200015241101900150b0020022200b9807500410803608000c150f5808541403403500148030304000302c0d844100304130218114520110206210056221009403280f40f08461040d84501d100c0d034000c1c1c010030305409001c01103c925108881d40540c0c2e5001c150f1000101525081006203903620b031008020a005d010743c00b4201d807a500f240e110a048107010048034190140c0183c9070750045066404000c1940200f4441020100190030b840350165152400b20784102140c1c461604039105030368050030800e01c181c20307075182104001049015090402d81aa01f0318000f41141d0062a99901c210071503403180e407030010700d03503400035090200c802140c024003940709046e038007203001c0d206e2940440c8035043e008901d40c00c000c0e20250 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 130696789 1250 130695539 130695557
    0x905010b0c06220b070302040806040506041101051c0b01090305030a080a05060f09062b05010501050a17030a050304020a0909080717043005070608010f08031206040902150d1505030a0201 82
    0x140c00c04c107041c02030441c6092507820807000401d45010310030148260b00802c00340000e4500ba0030070018080c00030050074100442000035504c40380c0d4000c000040040d41400020b5500081c10041e00e0160080d0006880c0b0320000c1200b03586039501102c0c49121717503e0b0840a000a0300c2c6d44040c0201780c84042081035000b950b900000d5101d081c4003c4034503030310180031002940b41d0124640e10680d059969001d5501c1d946902c0184540c6c213042c08000024240d1503d075034040003a01d0201502c82c0a10132041040200c0000401c00307550b180c4400801402d180e070810041441c0307914106546a100c07500807201284003880346c130603c100900c2510300f210714905402c902282c9440d004000064855003449000140384540f00c040358041000a0191915444080e00341d410204103422454007540403840b41e62007003002000514401c41040d40007001650041600040e610000c0e0b00e00c60400003947d0000d03404202c442180100c0c1c3c10241c1d0092410386540011a201c005140d2100c2c1a004040d000c5040c0709 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 130698039 1250 130696789 130696793
    0x306031208100306050112050601080606090402090c0c070e0105040b0103140a020d090b010303030c0809010e120c0f060a020d0c020601080303152e120c0e090c040905010b0c0622 78
    0x901c0030b548403200b00340802c1102d4407541d845044810a03001b000d01c0d0407944071201c04000041021034050804000140b205281100001c0d900e548010301c028050407011000c00c4d10400d000f0156000c10b41218240e03410b2300d40f15161a03600c080248100ca10a5007000100c14855002c0c2c03144400c94003071034404817242c2c1e60307031072100e006580400e600c498115035030494880482c91003d081800b03580300b0342e8003003800e2102c800010440a00a0035045259150142d030711401c51001070100c0c1c04034040085c0d140c883c49c000c00703450704015010f900084030780581c000304000c19010754001c002c0c80c2c9031400c081241c0c007645d010172030351010240907d01603680200b021980040610414a401a000911a0030780c1d04035020341001444a030b658461245800d080c0b003c83e800c1d0020301c180861400b0b408200020003010200503c002c2268070104d002c0c040d5107022440c812441710484000c0d010f800e00502c660b503075468070403141d81d020000000c024001c0c180401d9112088001c0c821110054441e40001c00034a6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 130699289 1250 130698039 130698047
    0x71707050a1101020403060e01060e090c0409140a05071a1e0f0912010c08010b030f0703090201020316080c01150b1e0904090308041208010501050a050304020406030c080a050d03060312 81
    0xc07809074082c46401c80031552240700c04d0005101541c031900c0046820804502d074036003540d020780c0007a070b620003000b001c10040030300004464443d512b0460f00403980d5822828404011032440c0500d10140c000c04a44009000740000c412003201d007030f4100040d489d03c00c003040354070074001e0708030304c01d0014030102076060407000d030b4000f50125403502c0da4001c2c40d103054400003407000308841302d4013501a5160418680c003140c000c0540e50050603211502c07803841c5420119040101002040c00f801e06980314100303015a44204203640c1d80030360810510a01c21a20308103400c00e50010b8110984641c02c10300c450820070081d5a45c2c404807584105080d05055105114030304ca0b01400c55641a20042844162000e40e81e5000b28042030340640c03688070180c201802d00f9410088490340040a00c00034400400c0b00f66445400c03500c011145151aa40301c1d2550320000d0040e01d4650720240c00b034042100003207581000440d5154103144a1011614914600c030f4055041d01d401d840080d01032002910300c1c180c01405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 130700539 1250 130699289 130699297
    0xe0717060f0d0503040503010608060709060203090f04050a0e030d0b0f030102042402010912350a0906060308181002060108061303020c21011103010e04060e0307080d05060907170705 80
    0x468000d585c109900d07040403c1c2155150f03409030500c0e0740000b080c0641c0b01d03080b009c0100a808144007551500010202090b450189011303020f0146c0e54880019030612190b6115244020100301034903034500b0700b4801400644070a0170002d110701d1215400c81903d10b414400c841c200c800200c0b03050000410b204640c00e003010701001315825035407691562000240000400b0304030290720b0315058035011815034021710814905440c4403071540407070304a1515825444134240e1001c0da548001c02c2da40300f80d01c0c110000e481a40e0006002c11f00c0800d0b5a24900c0011940303562446d010703a601d0f8600f8400f140700b20f80d140303001c1c0b152142c0d03500100301148072524208114180d850080c01121000d80c070b4000400c014800c5d403941840245204040042c20160038040d103054155000ca10508550501003000e881006c00f620003441d055a440300060749180510640e603440307420070b0480ba100d4092220100c040e00f4102c801c1c9200740070b03000015090038016014400041c1c240c074203029050352600300070b540c2680 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 130701789 1250 130700539 130700543
    0x20c010f031a010c0f0c06031a04020a080c0a03021608040302010e0d0c03080706060e1015030b090a02090a03020a03080405130c1b020102070b07030302070b1003080715090602040e0717060f0d 84
    0x100404101080c0c98800d240d0091500e540d00080007927001d8000518058070414103032142c0d0040080720216075200046030b030042442840030b55141d83c0d108054000384500c2690018103081840e02e8800d100711403000d041100e000ba00d60a00c03400302c0c8030400c145500070100052591004400a1010410f01c1020380f2610b4403601d0001a01a141c444800012a049581803824400b01130280302d2131019a002000035151400e080c800400d1090005204540c020220000250b01145800599907180d420000564024064007402e9449041ca210b0079409401014024000501d025001c003840c0e10800c042202959654000c001e041a80030b02c5510380745000b80d045129010000c01c41d08071400040907054441e0300c0c010b954210624000c211020010400c1c0c3c403c800000e02000400c0703c10b4229000e440c1c0c07120741440b095a00e4908070004250b1604007402091011030f020800e10b039110349081c042c54158450b045090040000505060001c442454002251078105003c43c2031074000300d00494 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 130703039 1250 130701789 130701803
    0x5060a0c1713080c1e0a0302090c0d0203010e011e051c02030705060408031201050d02030c10110d031a0904110d110312030610050403050d050c0319020c010f031a010c 73
    0x5a01000c00b2051421103030016901030300705921440151920002d001402c050041c1008402c86450000803005102480080e0003203480c4800202a10280c1e002c9680032482004219241d507120015959000000d00031a80c14221a01c0b14a040300b4100714200c003241c42c0100108041407100c0c1740030008070203403c401c070380611820201059940e111405000078000d000e00840d150821008002840a0f069020b5400307001c40c0002c5030003680b80803601076103481c01030700c1c155200d0102160441c0e4040030081e56080c0c90040d603491404050f8503402c000c50305d0010142c00d0014a01120400c03211600503070b00100400d0a00744154220f00b046150751a6950084c01504600b41c0b160002c00d0500781c0240c0e51442481e4000100500c510b00900422442100307445c000d030401d070640d6126079480b0303122460350060000c040f880d14080c600410448020200c0b000305100045000840a582e42403d070183c940855003c0c01c1e42d01c0200e10910500c0d0781c5000c299401c00c541ca0602d00151803500d0865001d80b046 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 130704289 1250 130703039 130703047
    0x8160c1a191709100b04060807050108100e090c040c1b020111070801060f03140708030313021f020f010606050a090302040c14030c0a020d0c051b0303040f030305090a05060a0c17 78
    0x50420020395200f560a540a81440204100b80c0b4080356130030f200300c40c412803501c1d2050000c841d0011364402640c0003800c04170030700e44032074100c0b040c220702c2503004810b05044801080a00f40010805860141d410380f401d010212003020140c0301036088142415052900c040200701540c840c840110450515409a40c503807500c0320145030a450a582043d00c00d512400c1e420410454005500c901d106500805803101074141100c403034407444094842146c2e10344c003803403920540d642d52000c443e0419240d550000d0150710740c000030351035004c28124240c895291000001e001401601251403640165403560401030865007008020102221500100980010101d104040b020300940c000d4550205007034440c0b003508402460403800099500801c100010650001140042c4110185098407e400c40c1c2d4041007000c0fa241d4011070f0f011101207030102c00700100b4113400100800c0400000c0e0b90020341e0b02d45a400340310052040603201c0c40082e24008017480410419030300c2d00b40d20200c4601d21894 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 130705539 1250 130704289 130704317
    0xd15080a033002190503010e04030507022b0302010e0c030a0201050c1005070512060307030c0e150301050c070b06060405030d0809070906060305011508060901120302010908160c1a19 80
    0x10010110b2000008039900080111034a8120107164600d0384040c0f410030314542c109045c100c0b4a40020304010244400810360000315902e00380080702086c7c040c0358100c0c0b0110716107400c000c9100c80c02c205070059446c011050080d240007240c0046100b101400404071200f9a900450305030b80000341c010302500420004600014884c001c190103800c00781d403600d45a2811090225860300c020b46810710a60000100300001441030210b10300312101e80b03601c1c1415541d0480c1c01d01e90301203a1580c561b0700d946010108020b602049011304007a5001e418001255521002408501d00c80c6020b0581d141d440341c44d0b60440c00d44900000c6500403d103030107075140b4940d2254490141c0e0001c2c1c11000200b0b071587c005019035991030300344040c10040351600e80d50608011022650303000041c00f0340289040c0b07861315142803600035000280002d500460181c4c0d01d0b80211941c00382a554150103d0303000c40d0710000003800148664402e1800040c03c12940c1c43c04545091808609502c11440310a002a010030420 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 130706789 1250 130705539 130705607
    0x90105060604151b0c060206070305010501120e030c06010f0f080c060d05090f06040b070f0e0109090b01020c0d0506060a06210506130c0f02010b030d050403020f040902030d050d15080a03 82
    0xba00c14821700491508011000e41821401860002094a000c00400c03031a80d00005101000c2c0f071503000002d0007682c01104905520820040b41c07614801c4400008070641e03860396507812200c8100c50342c0a40394035411519120520074014580c07000080c0400c020308030181d8410303500260b05c4405c840e4880402c2d48d0281c1009401c0301c0c1654100801c00070800c80c143c100d5071504c00e20501d441c15880c0750031001c2c000703041340d03d850040e036003420741e90608040d950b40204241e41604800500703da4002c116480c025a49071001c50300c840c000c40c941100068203034082c80c2c050020607005c1c001ea021100040189000408000b030845500801120416485001130300c61050403c5c2950359070400015520006400e458020301020b020354840c1c52181d0000344c0c003030241d13426658100d68154181e91103c0c005030161011090107076050080c01018075541d40c1140041040c401c400e041886110284c10b14001b9070300e8a4821003215030099171400002921a0b8040c4040403c0003d06188940001d4101d003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 130708039 1250 130706789 130706837
    0x3050a0803060108060409050303041b09020c0f0f030307090905040503090d03050903060708090a06050a0917040306060902030606030103030e1516030207080a032309190e09010506060415 82
    0x384504600205008031540e02640d41c036440007007614203000ba50540c1d82c84959900c00203101070440340107100940540c21a03100c8101c01072000c40030030754507580c1144c1030648400410860407032520a050320140300300c1010090b00d200d15240c0e12513070801c074035104074940601401041241d80707020400005195607140f801c4080064080e0740d03116200c42c100d03810305103400e42c0905845c0038000340c8003c1003505c440008200c00c4096001202003181d0712000d032504081c1c0f101400081c941240281d900c484d4031a02c3c0098000c99011b883d00303006042e039a042000403880700351619a00400c2c00c00050010074050520481d00c420003810802650029014024260700b094441840592a001c918810b05504000c1c10002d00600d90240c14040410340d0040c144000f40110b480320018440305120110000000b0745445040180490410441c100c8014180700300c103001e03003054800044e0224032103070380511502e4401c21025054620785810220a0001c0c02d112038941030401080a00303446076803915107201 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 130709289 1250 130708039 130708043
    0xa090203010302030c030105010e0a151203030509120309070e130b040503040911131505040e040308070809010903080c0f1b1b190b030a02042303160605040e0603010603050a 76
    0x503180c0d411441014180081d807803050784240e04200c0107008140b0030034410380d00036001d21000100c46441d1141c1e18040e01d00d0743e1000c801488840001014941c05401c064071400c1c00030151a85d084d0662540696400b05984490312a03100303402c2404840070482c011508118003024820100800c2e0341c5403104600100c50481e6103810100301001148200d000761000c042c000c8488901300030600c4000c8041c04550311034000c1e510058a25445403501031000c950161441c00d0f01d604081c90a410050000c0740b003500c0fa14001210f0b4000100703212418800c12012a51660780e01a9589a0150001140d08010011081c00008104031160603800c04080e02c03600411601070010740d0384180d0500c5419002c1f107440b90240009400da01511424820702c10241e8060b050001d84030f49821650000034081c6400c802d0301455078100b442800461184a0440404200c04032040089070101e41c0c3e0030342550384102404151700384420710021001401c074546c0264050000201d0756a2900c1d0145482500350f82 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 130710539 1250 130709289 130709291
    0x10602190213110c010c0e2d0609100f0801060807050a0e01140d0902030709090206040e2814060a08030a0e133602090a05250203040608011a0301120f020a09 69
    0x11061068000b408014090800c45a4903881008008c079021006000901300142480300040004c9550711075086c3d0790610b41c0076000640401c0500301c003078190964298010046032503280002031851240b11098440e940995610f418011010025140010310a0700b540c180140550b000303001117050320103480c4c110200400801d030380c8110700505040c4200e941200c06868202001c410258940000321001c4440f0140101d01680d128025807000e18900d440140a0114030714102d41c000740c4036041054404004000c819164490104210540580f481441c1c4550014005544883d010704a04600d00c3c13009403035540c040c3e0606001c4000c8900c5503100041074031110450b104c015042030000102104081a449410741c0c04da000100f100c10001c14204076a07841e500000c00f20340c010918234034243c40c201c401807150400b40001949a402c00d00070f210008007400000528081501f012031003401180d41b19a03c0d5034200307100e010500c500084150b40d01026000381600507141c41d080f00c4010084290 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 130711789 1250 130710539 130710551
    0x1b020a080d05040f0906080a0b0a111903050601020a020109090b0d060c05041503090206190e09040c08010b092214030f0405041b08070513090f0f05010602190213110c01 74
    0xb10104c6501e6280c0001401c2880c15409010300200014105d0000b030308010313042d07040d60324480c102010708098041022601404140401d500703880b855405420403050b02c06200c660707101350049030313110b50054000e40090310315481000810601c0c1d00032100008090172910301d5502c152600010344040c001c4642c005000041e0801c1130b01c40084001940400500d000d000758a85a000110f45019101c0554039443c008210503c02c1e6020700c40d64005140098203c10440c40e00c0e04158002c0b05062003140115400c1040c0c0802e82d14140035018800c1c481c80c2c0400501151998061002c0344d130b102d104803412100e8210107100d100007000a05402c1082d061490380da1401c0078140019071720141c10100c14006c0c0341a100540b01d0b000f0920700e5202c01940340182d01d80c80030b0101c01c00032904507401150501c2c50144107064007025608a80700380701c0180014080c60340c0e644c1080340e41c1c82114013040302d4034602c0704001c0014508045801c02041d060900030524440d04c1c00c00c940107500c08220134041e030b07640e07070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 130713039 1250 130711789 130711799
    0x303040611070317060d0204230601032c03070507030507080d0801060f0e0f1306170c0102060703150f06080613050705040621090b0405070b03071b020a080d0504 71
    0x4040c0d4005904085801d5061070748680d800307490300b030030340561482d05014140020f400743c503107010400049800410600c075a09c8180b4620240320034260305c070b0700c03840010030000d10103502038091281d5400d004900b40c80c18840d00c00d8041550a00520f0200d940c1c0400c101e4000400d80403ca0b100c0a140038101810b1450b02c0c2600c2c183c0743c001c40c61040d0003400301010042056680158115800030b4080c00d241c125550100c000400c0b0b510b414103015403100e0010464115811540d029505446082c078108010301c0c1700070b0402da919141c0002d61401a0b01a2001515a038402d070041d02d5400e500c400703c0b01d82c141d00c8503580f007a44800758104000103000301c02002036519100c0c40e030810303500040a04004c0b0b81440000145288900e00442042c042019a44103514404095030310480c0d4030721500b001100b001e450b1801c0c0e084000d64080c2c49a01c0340240c003103200600d200480b40209603075100c40451190011400e40e604014220503640180d0250000580358800d028150f410081555500d603114244 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 130714289 1250 130713039 130713041
    0x4140d1a09030a08150105030f0601020a0204050c130801090f0206070602040801050106120507080105010219081902160e06090105010809030c060a020a1107080307170d020f07030905010e010c06050714070503030406 94
    0xc2501851405da45952452079030007008482d00264080c80181c1d40381e42e40d40045c0d203030a00c5d08070000d4029250070304007c0d04a00399030250940ca8990003895601c00d550720021400d84c2c0180d0b90290003840780c1c1c5410401032030400000e051862003408054107103941d51601e42e003114400d91048000c80d010b040714601101e02d40c80348540c0641c2a061924080d414800001d5880c5001d5480701c0800c2080003110091203112070a0340d0b01b40c0540c0c0300c0c4560914a010000b03454003407000c00d04003017403d0100080340c41c0b528041e02a1040d2030140c402503844e880c080c01120b024002400e0b0f15054001000040052402446401c0c0300703020421000d660b510b03202d4070003000c045204005040d150810202031003110000300442e95010380158440c00e904680050f800307210b11440034042405840000d0003080540c1c00b82c05007410754060303184c07031030a150b988005503140900104658001070360814000f000928650103560040030a14100003d000e02c0082940580d224480c255526400842000104206 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 130715539 1250 130714289 130714291
    0x1903060605181003080a020a0803040c0515040305300a03050709091107060f020c060702060601021e031614160503011505010503070c020d02090c120c04140d1a09030a08 74
    0x400c41a0448900e0101d4202101c4403250000130180040007580c03040c5d6078405c001c2d403c00c8982200500b52b603402c0c07603d030481d00181e140c49628062003014100684058140381a50f00316904540505660030303822040c00c903600751501c03c00c045180c407842d6900d022130f06e05e0060320002d0b00305e460000b00c2d03051001e40500740804c3c03070384131040650803c0380441c00707500008140d80019a12200100c0e8940c000307411540a40101220140d4038401c00c401c1140c899400202140201d600381c0a4814054060b8840b1803c1e007602c51054130b182d0300070042000200030009004001500800ca8001c2110349840491f0a00f0340c1109a002c0e00e20500030184014a0f080c46841c0403d1a6a600381c40e4540c94100060101e00000304000f06000c20308400205540702c007034802d02c54a5000304215900c4c941254403d01581042800090b003400318400100e81d90040b0003200d003503d0001a882030905440d400b00101220081021603444030f80445402403480401c0c1228020300f2807401540c1c440750115002403140340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 130716789 1250 130715539 130715569
    0x207030c0f080f040e1f12080d0b0303030405060a0e010b010e010c050f01020a020703050c120606011812080d0f0605060306040911120109020108070e010801030803070c0506070f02160e010902091903060605 90
    0xc002200300084031180100c1c5407d03a90048031113441d10005c0300094000c1031f04109150b0940400070400040200104000c0d1040c06c150b04100700210142020340d0803a03040e40202e502007014021f010680358000c10000015920440840d44d150b120907084600f682c00011100001d42d2182405000700501400140311030740c81030b9100030a02e03440800716175071040090300080c1444a1040c0e1101c8118100c44d841019202d00c3c522260700485c1440e00e038805603c40400d0805c0030b0310b8958050264600c0b401513100f118002015681940c40f504c003000001c0400710f40072100042c98059040351a00c1d080e0b08503040c0c008010000542288500024010f482c3c0104003604100311811814034036a00b00c1c01880c1500c0d00503001a460b90355002090300c1100c025880038000c0d03c202402c1104840e07100490403944960380e42622845560030306404c00491003800b0b00d8602c0600c00006002d0112564060119004010104020203241d41c1200c0f0b0183d0b0035400a45405445a2041c031943c00d1100c0d0840d5681 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 130718039 1250 130716789 130716841
    0x516080307080a0509130507090f09090506060f010201091b030605011a0726071b0f0806040816020a0e01060905011d09070509060f0d050105040207030c0f080f040e 72
    0x18038640e80e520040c82002d001000b071003004a804945c54651141c500310710020f040007040582851000917140c0710b000d01c20a0120507440c680402e00c606036000303024102da4031100401c0359841d46c0040003c03a60745074500c0c9045645e2a441c80011401080743c032042c030442c5c075011406141c01c0d800d1600581d130058101e8000c0c03480d0008400c1d0b0025090003110021034200c1d090032511504000760455003910a411005500c0740402c1c0141844904613104902010702c2c01004441540c03110540107080c21489003980702e40010300040c012580305c40040148003003e031500106aa020b070300081b070206150b0080030598142c800103001090b0064070140241400342803c8801041446060301560b603041201e0303004507410300210703030114010415a54154001031105d41c41b0f540541802c1042e8010210002e0050b05007400001c0c03034240340c42110b104580550b1284056407040c0c841400310f00b0842c80898591504000b045403c07192074024002500d0135203160304007401d01d4002030003140d40d08641640c1d48 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 130719289 1250 130718039 130718047
    0x9090a0903140901051209160504060f03030e130903020d0206070c020d0807060f02030a0b03011107030507021905090a020a0f020c0a06030c110a080c070902040e13110d05160803 78
    0x7003504044000764804449802660741c62500d401200c003400381c03c2c000d44800030550103014210b100070451700c0031074503024030b40c9100daa51a0304000c10b50343c20341f064000700c2d5461981440440d10030403c0d00c1500d0b6001d0310b01c090a000101c20001210950001600140c20031510030703e0856060010a40040d91031611110798080c9030001100c101ca107180040844000040c4982003080c03540004445241542d0115140c0c1740a440c0f41001e4075010140c036100e5480c2c14050707001551001c064a41c0f2641541e509070414001d9424081c14041641c2100d402c0d011081000400c1d075100d081c0c080c030540745803c0260300d900c0100409000000d80e40000400d6401000b040e0407241c0f184000070086a038140340101d05900c0b0b40d030050703456601d0080307061072038000d801c018801d00c103400f00100200401d5104852040341d8401d0300380300b2409103003d040040d007001c00200b40125801400314078118001d4100c3d200c040710000c0003070000300304030001301c035581c02c00420408042d40110081005100041c017940c98 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 130720539 1250 130719289 130719293
    0x12010203090706050309160303180806010f050f0105070c060c060e1c030b040e150103030f0903030c030f050d090b0405010b040216061503020a0303030204240e040507050c1209090a09 80
    0x2102100d000e25803c020003c40090085d0100304054140b1340d04a008201701f01c0d40382d080042a4501d015074141c15503009500000324010b0000e2290b049817035466187c06854100f0b810041040320449020381004030610407031012401040701c0320014081030700d41030110340503450100c0980303189546800c50b0341c101c070386207001440301d15000c00c2c0c10100c5840c00249502d20200003400030842204c2e1100070f0701c10300540d8481e100214083e10705985c0a0780b140541c01d00f0003a011142020f003804000c00141d8040c03005000a070040b03840258a0b941c0703040160030014420400000ca59410006850b214544024030060040a10410321074420588055103004141641c910501c1011880241007581d1342e09100c42007400c241c6d80c017018540c000d0000310000d94070b08005010b0f420a014017600c0ca00718491091400341d000b121306140c4103032034a4008551080f8410072004010050281d01840420080d8043d42c1e07005011031029078070441d4505448035180002c0c401c41c200c0041026208614024070400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 130721789 1250 130720539 130720543
    0xe01050c101d0f0105040b13150207080415050703180f0509090f010e070602070f1d06010c020a06210513230303040303090b090a2103020408060103111201020309 71
    0x802086400c045600e19442d000005518040039040c0d00a004480c600ba040c1c140640182d8000e90150b0301c000810b0312100d110f0b8283c2020340d00b00030200f80030290504149401600074241c01c82c001e91100e4141666440094040b10740d4010320000102c0c002510f4080580011011001102078550014440c0c20148503c000c0c18040c01458452140c8100003541c84004100d0b40c0c80e000d003420024000c50f17038a0001c07035a40e00c82a0140b580940203141c8003090601d0340101041c115200005002c039030080d030404000c00610040e0015041100400065015854000c0c2a8000300955560811414043d4001143d041000307009030303003168100300038884030807000c08032151841e0300041080b05c07107a0702003103890410401c0368980c07829010110800040c150107a01a0310514001d50100200d542d4407803045860300441ca200070803c0c0e4a442450108150890072070a588000382001450b094403400610b01c0c00009a00c01c442c400c0c551003030aa0301b800c140000d10301c2044103a00030360031400e010341160303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 130723039 1250 130721789 130721803
    0xc0c0f06320d0b030f0d0801051806090708060409050d020609152e0306090606050405010603020a080114030a020909160803040308030105040c050702120606010f0e01171b0406020d0e01050c 83
    0x1410030b5884850f60841554244003510551040c0021183c0e4092201c0010300031038424421140b0484417841298102240e1314138051190b100108101c4103a40d40c20020746110801814580e0800c0d0307500c1c42d01c00020001c0001100011058000f044146001d050300362820303492542408584000c01c040c003190200c003842c00404440c11100c43c031070005940c5400301c09000c1540c00581181d0a2051060602c443c56100006a90041d1010702050782c0b100402e4059204080488001800880040111050718186a4441030004090307922041c01900041e4030300341e040c1c0707504c00c054204910548050410418450007031502001460809286444803082400140b1034240255252820034014078854400c0b20007a0390b00402081c8484112032a003a0380300012644107000c40c04194400011718005d40d540642500705179240c8401e80ca000c40642c0b00070b1005021380e1107500500807100000ca880c900584041c01007039009095606a408001b080004540d9815040c08000c10143d446a0008a500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 130724289 1250 130723039 130723057
    0x390108010b070302010e031303030e09190c021207060605190e0f0702031308060702070b0f070213090204230708190b19060c0b09010209010804030c0c0f0632 69
    0x1c1ea2510440c0c102a8050040700000088600000440a02c0c2d260101c1d1000c0907a130003035484030b500403211001d020711820241d070401c02088880ca10402218090b40000c180382d540361054416201034401e20440982090200300c48407a11080b00380900d0914120f183e002410708800d0701d091910300204183e00d80005440c0003010b0385105e0000740c5082c02081101e080d00c01a60070301c00116918010183c0303810090b10244c005008403980002e180a0400654503100c8011514030300d428169800c10280080060355603082c03d480390088030140ea50b134031403241081c0250a0507220190401d00b03017000c10030300504200a22004030103102c01200b1880c03032404903131469000003401580040c00140154070900e11120940f461030004500c083d0b0064013004a41e1103000c00104984400c0d807258242e0190722080b81c0003440380030014012a2094840c0c0c0d81c014001c08a101c021a141c2e610003424400c141c0090300480e03d50164242680e09001c4500441d034118004682e00403e4000f000031544584496 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 130725539 1250 130724289 130724309
    0x30c030609070201090c060801030506060d120c021315050108090d0203030730060609081209010c0f080d050f0c130e090f0601080705030f1501030605040c050339010801 74
    0x8a03524000d500442c4d016812181b07145546075608001030402e1000d010488140c010103000c00c4003410180c1302e2000c40c035405210b803482502d2015003141c522280c8402680e0081c50000d404502040d148900c090b9107900782d40800509040c10009452900042c081e54050b82c00000400b22142c1d0100035690041c442d450f010200040002c4404a1110000103102d001a848500000c81e002c5c50b030710442c102c0702c140c1c03241890259101c5249444984941d00b40c6041c60003080b2407071181d84240b0003914654031a402e00e102d031640350313207891303601d5044800610412540c941c188001e0f40082c002c21a40500b00061130303032070f101b0406034000080409100707100a2001d02c0b0080744401c3d80a01425060320350303a904590280d030f911402c29940303003080e01c52076009020b20808500d0080d004100b8212007201d40303480c00400d034611343d40d05008000c000c0040e500b2a59485011503207a606100e1502c03200011148140740b00c01c0f60a41d1849400d044485404000d50b03038408503044c2e41c00c1031400e8112080040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 130726789 1250 130725539 130725541
    0x7210c0909060912020d0f02120304060f06030c0b040e060411090108040201022a0a0b1905090402130306021c0605030c0607020a050a080a03080a060f090b0d0209070c1106030c030609 80
    0x3400c0b07405000c92100003098407805281100e0215400909010700301030540d03c14007441c502c600c0581c4c0741c4014117440c40c91040200001008070320150004040500703500000100c10740c3d070352200600d0041ca034001c140941000507042040c002444000d6030001c0c01110100030078809205402c1180c031801100ca818807000a000030150b81c0240501c03400b110f41810342170340d8040e41104404070000b02c50200c511600e000400800d9400400702550715402070111000e03142e840e0080181c40c680c01003100d0a50140e002c100820213800109171010045d071082c140987c403038040b000ca42d030a440503510004e011a141c01000c000c25a0f0004060303403030040c259171042c0e0380c1d0340351b00201d50401207542225810072036502d00015100e100081110056001744da452400e0385a20340e82c0780503600b07144a030300c0c0007008910b01402110030a50015141c003100820403c001021540031485d0210115020b10110b01742041d000d082c003641c044043e5242d034080b1030051942c070f01402010700381d00024009074040c152101c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 130728039 1250 130726789 130726793
    0x705070b0403200a0201091a03010608091014010905060f0a0506090a090c0f020d0801030203061602010f060b04050f0306060a060513080316060b030a050c040e10090507210c0909 78
    0x4000390901c04083ca440060b1900088102c680d82c40f509213080340003c02c00d000c0005ea0100340f07170b082d142c0a400b00f141c0600d907900c2c2040c12540141e019040e407515000e40c246107455a1030501c00d2094240c1e030080380c000d0320740c5000844021194018243c500699400e207003800c0356982c034100542900c10840343e4548070601200402c015052640140e07900c076207070a204000c3d0795004442c0400305030480d400c4988486e000a401c0320400804c3c800250503501602c0401c060394000707401d2440e000014800003901491494480d404d0b100190b210101c003010000b414807403800c1c48040c0c120100015401050036003024408141450024490181041800300f40181c00310ba035600000010460001100d03141c0000c0e800141d984c000300c2d0f00464003146412079004144c14007061810101c1c1e00301c00900484000c0c002400041c002984036030509019803684203500800f5407086040c0c99000e030000b813990364105503010300340001142e40700c0b1101ca0030195450002e40f81c2c4200710b040c2d40c00340d000859080054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 130729289 1250 130728039 130728047
    0x130c080a05061e0622020c01020c0309030705181b0d0507080f060103020408061602030c060c0409060e060607060c031b11120c07061b0605070809010b01050c0d1b020d050706020706080705070b0403 86
    0x2110052407d9400010401c40c803880c000080e04442d00d081341034401141c0d549042019924061161110543c4600000340c0100c1c81904801040000c4d520024940000440d9142c200d50080341c07c900400c0305031091041c0311818902943d800b22081c02c04510f001d003004442c0d40d42c0e030001001d6605080050b04103000742d5100703000b40d9101c4006030313048031100c6c01e0916080c1a160807500656040c9840c14034000344160791718512501a9801610142c58118a515400080d0881d00200300c01e05d611400440c112441050a203c4a2840c617500c40580c4228040d04905010501c06421503010003441407240003100444c101c005c58455080c083c44a41a085a81c1450b8803e940302401c0d15160404200c030302908071082c01d1103015210020480000a80c006584502032500d11040c607a004001180286000320b00c0c5212010000080104054551740015080900408221002e4011410030400113804124a0300a4645401d00c1c40f142d1038001c0c001041c0f17009940001e444504040040b03411b06000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 130730539 1250 130729289 130729297
    0xe0402060409060b0a031b09050105130f090f05090d09060818010f0506120105040507060c02360a060506120a0e01110a140304020603130c080a05061e062202 69
    0xb03100e00c18407000e6620740c00c0515a4100c9a1000046810100428182d01001c04602103500203a19150b00709818a001101c00c0e270801424080600c00800c4003081d108503451904004180d81031010031440c01b05050701003542d40181c10001c259129091803408640c1281200b010748025141c03200440c0c2e200d445a07146003035201c181407410752802410140341c228a802c02880f4050503581c0141c64003410036241e08980f03007298003800c10381110100b880a40d01c6801c24485044c00100441810001c22a454200000e0603040b0481040300c8400c41c0c1c030008504003620b40c4810302c0c000c200415460000450610311900100c98080d01e5500002030002031715070320407100d840c49100200942400e01351a81803940c0302481c8100403c1421010080340380413182100e201d160301403c21411521403603c407900341011003004a5821001040208a02d40c007001141d007524021401440c490808404100c000e0202040008412040800b004600c0e03d8031403480100d05030302084000d089128404040083c09 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 130731789 1250 130730539 130730549
    0x305030307140d09120807050a200c060c06070305060d1203020d0603050a0312050c13120203030412060b1e010813020102120409140c090a090b0406050406080a03090801020c03040e04020604 83
    0x2140c135400605001104400d400e1000090711070381e0442d1150320b000e840f540203000e25180040d0b44441050041036603e49001c5100407100215211814008002030303ea0300103802d10803655202c0010050015410301890342c100030103a0b900f60840000d40c41d0a40040d4980414105054000a41703d0840307045a1281c00159045020344c1c04000c6d4a150042c005105040042917032810302002c01c10802d00c10302200c89034205410172980e42454403050001c0c003000c00f0300a9916001c1840b0028241c01d000218071007185c40381c640080c80070f07440d404104080002d4801c04502034022800405980d0304183c0c202d400401c0c5000d9030040d16901d02c0103e01d000307000c00c103413005d900f00450000303a555159004203110444600d400e407403942e919002e0100038012044100e80c07102c0188410481540309030311012842c0382c00327000480c0e00e54035040441c065513150350005101394404400d02c0241039000c2c26036005806013000079450104003040c0d40c0c1d664003071030095007252202c2c00301050031541c5180495000344 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 130733039 1250 130731789 130731791
    0xf031219030b10180e010602010207140106060e150c1207120903080d0203090708030a0c060e152701060f090c0e0a0b0c01020702090f07091401080a1a03011406100503010305030307140d 81
    0x9031312a10009d010b500322100448080b03038018440c44d840181070080e2000d4984070380d0b0b00088941031500b0400b405140424880095404010588c50354809110700d061100100d8440741c2c0d20707001c41c0f405402d803600c0300b0b80e80010480340c180c05100081c104821600c001a080341c016803031341c5070112541d0600d40142e00120445c84001b4a03181c809070030408001d05240203810820144c200010341948560241305c0709011441000d001a00c1030803140c50506400c00780751001044009941807041c00c48205030841c0711113061060042103840b09501501c4043c078107624002e031441201e9400704400c17075010f00034020102c8010842d6480c50100354107840180e81c00500a0070f0030306003500807244205048c0d481000180182002140c058110100c03c000c0d54010f951f0404256900800d02c0000d1040701000600503980801110309540c0900a087c1211004940340f11181000001c00118007240d13404001400400d00c01000800e5000c4180d81d8008036600704480018402c5680e0140d620800b80d8a203086 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 130734289 1250 130733039 130733041
    0x3070c06050d020d1a0103140c04050d05032502120c0906010e060d02040f030b1305030702010e1c03030501060905010c020f090919060e01140609070e0f031219030b10180e 75
    0x140049529151171042070f00e0421507401d0450032555501d000319003003540b8210030003040081f400c00110342c014050041c416241401603888901e980100d00150941100035000600001d40c5001d4603c041020200c100401440078420042200c00100510140c103101700104455015210300b4104d4000200744e507401c42d65951502400c07500c003050390100740c03000014070b40054401080049103a6103036400000460401c1e07096030044039001c0f03000310b80030b4103c40700a8160803030f51803211070b4100c02440f0792030100e003640c10100d00a121035103590102d03042040c5408038002685412103400c07a015400d43d00c0c101550751300102d90745403110440d9640481c2c07000640701818400b01d40d1046540d100c0e454028004846032000340d09a800e0182c5d17003541e02000001c0807600290180c0740c0300c1d200d407002414035100580c100c400a42000700403440b400f92014000340741c80038085480c1c800c0c0c0e1100501d0030200481c001d4100400d6a0841d884c40110a11003440031401e01c41220004201c01030980c05198420703 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 130735539 1250 130734289 130734311
    0x50c0a05091605191e020708070306050a06050604030303330e04080405190e0903090603060409020414070903030207150c081b1c0f080906071214010e0106090803070c06050d020d 78
    0x29642240702c0c07100e000c802c0c17040e074968248046103480403502000d00a200690558490500500028000d417203569660440040d2035201d85016000650003501e0000303105e1009140b003003090341d050204401c1c2c010710420f1511b0306150079400205880c2210034a0f1115940c1d450b100000e0310580c6c1011303501175a00030a1102050406001c4010360790a40030f06500f43e1a000c0700d150ba40d009641e01580d120409000080312030400d82d0011031038034001880450030041001c6641403c54055856000003601b1a030240181501000700a00411500b0900b001c001221940100070341403a00008100344400503005900008201d6000c10910b6180b080e00c0010443c14121501403810900d404040f4140e2900d10070711901401b0728611038541c440242000c0e6840c0b1718111202e031075140c5000f10541d542c030400b4000c003400607100350280c6201c00812600b541051006410020203605c404c515902c20003500300000c040d880c0c400200c0300b050801c0b90301c1d98480c860540223801041d1078400140d00d44242d00782 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 130736789 1250 130735539 130735547
    0x18030f0309150408030703110c040606032412021c0b010603060f06020f1011040b0c06010f08062e0905090d030b010f0801050d0807080301080703050c0a0509160519 72
    0x4080411114110a81a007082000c00b0740154494941c480c1c00501146022900444101c00e041c082c3c1002d076104c1300058400501101e600d50460b400080c2e580c0340c09030401040c5244641c0000180540808441c5007004982035000741c0000240134000390202c1200c1d241181020005403a4419840301145d84c40d00700040c000c0155200720b0011480d07000001495500208508094510b90400b6103d20090008143c1c084d01e044421051500070402c1700140000c0b15101801131501c247d405081203524240892130b50a00f80d80281c1c090390020000d01c01305000b1030180a4034000302c50032402031100901d58143c082c02d0b482c0c2c01001c016091070700b0072418480104203208030003010b4404105c800300d66001141d005610b41001c00100b1000c41c0107202501e0030900c419801441000601c4c58a0800d958480c030310340080e4000d20003940020000e10410500788150b00c0480001d84200380070600c0e0400150b0341100140a4800810602e41108800340c401e0080f00c0551004c00150300c00c003448060024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 130738039 1250 130736789 130736797
    0x3040f020102061012060e0f030c01060311041404060513020907030906050903090102030a12180803040510141501030905070f080f0a1115040306060e04061805030301060518030f03 79
    0x7070040c003a15000441c081c0c0c031508030f801668240d2810102088180e5100c400038045040e0300c6105102c0d510702c031304405508100038504201d00c0000070507118034511b051501c448030307a200c0600ca42c0c1000340306890700e40c2840840d0340c09508124049000d4482c40d8400134840666140650400905405c100803541c0542001c01d1982c0b1039603007000250b031201c420302d8981c0074130100540180c100708116200c90f4410401d48211400319540000c1c4100014103c240c511844402101c03520700c080100401e02c5030900c000040311500c00340500035406041e03110000c1c090014518084002444d92050701a4820303070101d100300794007400311030140e501ca8204001c10b8001d8484d2391f449110b5218081015200403c9603104158040c182d0090340300040104880c0c200c0b0a14480000780c0e040c07000201244480c003d400040c82c84c0840004c2c6403c0c14101202902c5000341034440d100060404640001d44c0042100d0464a45144c184c1e100d900c01004a0300d07002e400361070250b05114080c070386810103801000078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 130739289 1250 130738039 130738043
    0x110c0c01050d0e01020f0c060702060103230705031c0809011806090303151e0902190305044d0a050402090f04090605010905061e060f04170609070b1e07050f0303040f 73
    0x9400b595103580040f62f1350b4600b400001c02c522a00003041800f00e103c2120640500c3c14074050b6242240ca6101092130801030039200c1c9000041c000c3e00b0f08020b44c104502e1508034021034000e002c0d003041205014101c0e00103500040034540c0c4c2e1a110424944a40d00c11024800c101700d44861880c1d842d00302c04580c0c1ca862010040e07038182c1300750000e581c860910031194065003c1c003c3e5840104d10a4054005040081040d80c03085100c40c100c201c4a01c07291510040b0310300307184c0d01040c0c110801c020b60b04400341c2c0c01d600d6002c20250101d50b0b03200f9034031560400c0c00c42d00d041700d003d0b03030b914206004a4110600e0039034581d005402e041140d420090940c1007507041e180303900400c01c90755035508100298042d4090540d1404112001131074103d0030080014180048110443e5103031a81d108400581a81d520344000107a400c07100a104d03100b101030000700c00500d1044480760600d9107241e00d00100c10541d01c03ea1240d16000209681001004d110010142258034241c0b80c982c60503061445041600da030342 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 130740539 1250 130739289 130739293
    0xc0201060806070c0c05060717030c19050702091801270203010b0105040b07081e0703031a060301080d0302031003050d1d040504230a05011b03110c0c01050d0e01020f0c 74
    0x203049103116070f8444c0d4420341c00400801c540ca10745002c2c001c0c1a03002080585440411020012521405500541c00362280070780259596101080c0d00c6440650b1407071200c20418100a43c0703025035180a000d98020804118090701007222040060050500748880c684441d8104000505141548085180301e40280c0c0244502e4502c100111124401d0f400707072594240041c480c64000c644c2040c060042e150040300201700380e040751080641c10b5040160220002600c5100055015588000464580c802591042d082d54100003151340c6a110f83e41440080550100005980105d00900c0d080115040400d2f9080b650709480300903e050b00520b80b1081d1060380c065003500c070303042c00d20960b48a150070015140e0003682d15499410543ca00400c10200e034031504400d0b002089003840354880c075442e01560205400c2030850060113441c10301041048240041c01b15400032000403a465034070302c1c1d0910b0015941d01102d00c0c00002885000c1c042c070381941c07020850100045045009100f410800781c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 130741789 1250 130740539 130740541
    0x4030516030507171501030602031e0f0105101803030206060a080a1e150f0203090f06040f0308040218070203130512070302090a0f181110020705060d0b040c0201060806 74
    0x49a50341000610000380319a00c19a800c01803c2c0034001100011011441503540019072920000c025540070303002070b5280c03513001042c005008030501100105ca80b109075084e402d86403801c01505610414440c26001ea101c00c800111910f108100512005100303950a010558a07030400030369415040b540c44d4002c11980e03002051800c0c0c006100303006154410482e44410488181c010b580012245c400c644a010681d00880d49079001d009004441e040d0460041e12450520361061420034411445000368000700207200200c0d0b814641500010341508201c181500c442c404252034540124001d0301c80401c540600908650110041c08407034030401c04002aaa124000c014950040d140c1c41c10071607101800c20001410400582544000d0003030f400108440c00d44841001c2c3c0d000c0d5089050140b0340e80d441d030320410101d08070140310004c0954021586018860b4040d540320301c680917161107030074085142c1941989075005140914400f40047c0f00e035a404140190281600b401900e0407400303950 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 130743039 1250 130741789 130741813
    0x1b0e150108010e09060a020a2a05060a140a0b120d030b0312040b0a03090201020f0f011401080c090a090f3824040204090606050705060601020c060702041a09010902040305 75
    0x71001340581544c1c2e01500071a100c1711a1400203601c40b10394541440034005e0041181c100c103141c0d40011413142504641002c481c0c1c5856412305a00070503c624043c82c09145e40d0980000307100d42135101441600004d815840b8000003140c00146101540c00c1d071059000651805034141c01034230001c5d4003601100d000442044002c00e02d13002d940251105042c0600503240100c1c071a4100300d0101d4018010f0782c0081124811150030044d030050720016070381d1910030010180300d01d1008240101500c002078881c5240c07800002e48111406002c4065040c0c54048101c18850645e4260440c10384c401d80030112a40260502640d4144100c010503c038103171501982c00303141910008511a5040809101c180c00a1442c4100410f0380f2285031500301d50f0034400403d0424152003402c020f41295200ca649030b8403246460b903c0c0c010000c2070740341190400181c07580380d84c0391081502e110f9941150045888550068102d40d031b400721141107a4800141000040d2050b056801001030300c1c020810b58284001030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 130744289 1250 130743039 130743059
    0x170304170d080105030a0f11010c0204150f05040e0a0b0411060a080109050a06030201022d01020f0c0706020106050f0d1103250e0613050705190513080c010c1b0e15010801 75
    0x14800350007490f0300d0000e41c00207110b4805148d1040700c1418081c0e401500ea801080031280c1c8200750000b042d110800a00c10344540110100082031300311030a021030075500c1c0700d00e5150b0920030720081c412031144000c2410042d1414002590751405001d40380ca80c5c0d4548002020103500784518440103140501103031180e2518020481500d03011b030001c02d80400b5000100415540404024400103030501c040310380716600780010484600c010b0101074030703545403030300c01da003885110b03803140e001d41e0b242c1401080a900c035000c001e03042d114200e4621060400c40d082080004a0400c0d10f194035001c0e80c00f482c0304030b06034003605e5500304c800c070560000b580d92502a00d20095405441195202c0091540108400c03056042142e100d0160316000381003126010b4181d0b58010418421000307e500401c100000f6064143e2000040c40258010410340f18004006010114008000740c01c0d8003002080200c1040c2c142100001805103440c035030041d18002c0f803460611244059194001828200000354008038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 130745539 1250 130744289 130744303
    0x40609020c0703080a020f0601030b0f09030c100c0c0b0906070306050a0e1302010201091b030204050709060f18080d03050108010e010902010f030e01140a0c020d020f07170304170d08010503 83
    0x3500c4001c1a103142540c642d86205e8102540290851140341650b14003203006201e40360084d4030030000407146040000d0000706400c0000c0c4854400c0d4010f00405440d03400028405075118043e220004510f40045070480c0c481d0942c100c00341c41054031406110480c880020304600c01c00d40c680e000c0011940315400c10801e810309e4461903180c3e010940c04240d4211000e01c80407005032050000081c8001190382d040410310070114924000c14030924100198100b90081c543d1040180c07900d412910704251011304060308003101c400420405050341084607420101c07180280002d482124500001180010b01400090040c0c0c0815400c1c4280d00002e03c505011340b54845a05031034260901403150b500b06c00074501035884144940d2a0304009001145080800e409141002c50200c5c41c220f403980007030310780b05548506804652010410358440070380810038105460244000c0300b4004160301840780756000d1a0080d603056043d02201c1ca0441800056650541d94142c641e20142e83e0784104140d15402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 130746789 1250 130745539 130745557
    0x60a0b030d0e0a050901030b07080907050d030c0507030804082a010509010c111c050105060307031520030907030203060906070c0b04020d120906030e0309061911010c0e04060902 78
    0xc4640798900909000318959450b1041c00b40c0026005950703040010540b170420303802944c1c501c50741c1c0d0600000e00e44c0400c0c2d2591014980c002003d0461601c008100d421741f90610180c1009a0300c10b0783c204009080c003a0f5801550001c0b00c00d51a10740b1004581c0e280c41d120a600070004100c249009034020074001c0b5000d000b801611480d0620100e070380152886900d001084944803034071010f55000d555641d60b100e209a01c5401020341c441c0141c40c01d2421150060407041c42548105020000500d0300184130040b10790f060f1001c101d0101d00c4030101184a030242e41c03030348800f001000b00f1045001c0021800201c078000c804440b15601c840c490180c0350442910142c000031418030b514000700c0c2c05198825001840500340d441060002d485015a90029090440004130040400c00003a6810700a1007403580302200958580068400010140c0c401c0780e140007a410110b008110394580116003202d11080d2940c0280300748646854000c0880c00d6a900c0315100302d140c14000b1940390700074425035030090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 130748039 1250 130746789 130746793
    0x60207050a0e060603060111010905010204050a0e13020114070b040b06090f07020a0818030a030305010e010902040e1f12081c0504050316080904020c0f011b02190516080c03060a0b03 80
    0xa1943c40501c507076680000c01d2a8140802c0180c10034000400744104903003d030045000603255401d080401400d03512a9020800d1980341e802485500002c850006c0d0440d942401c221107501c1c45180c888040d8081c400000d4404000d0307130200014803844c060154400c01049440c40c031241d455885805e07407400c1c262210700c0160320000007000000d5942008012900000d054490301d5a1440d00091400d425410b0880c0001c1e01e850040140c11000d000841c09440592010b508090902d095035240c0d50004000110030b80314a1072400c2400e01c4041954050300214100305400382c12410014019484901c250340407131902082a20300310010f102d0240140c0d807080240d45466100c2500768121000079509403407034102040600c0e800c0d510362004050031800c800160903468071440030b140c2180c2205018201d0022141150a8429030125030340d10502d80444851042c00d545091280c40c01281d94542d03c68a40d0850000ca8034640c00200070228140c124201c5260340e8581c0040000e031004800410380603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 130749289 1250 130748039 130748041
    0x311040203041a130836010f081f030807030206070c1a07021e0a02190b07120c020607060b10110615030a060603081e0313170909070801060207050a0e 66
    0x8003c8504060708800481c4020103802c485440b400c100e90f200601e80c0410907420b07100c1d64014a08441e901c0c1c801b000741c52558101e0345002e000a080e070640f0381000400c221100c00018440d10030300b28546440002c40d5810800241c0303900e0058843e51100605801510032040021101031044805201040e80b140c3e04070541c0c8070f29071005818440250801065004030004406074280d5000744900500c1e00310000c20030b04507030b40103120302c00740c03000d900d40000080c10b8000e00c0407031006421a986c0380d42c00203454241740c83d100300854410b0304121000303604c00302c0015101c060000c55001441c80d50300440343c1140008007560240c1c0c0f0f00d084450716403c55000f6100117011400110a00c09846d48003a0a1301c610402c550f4518084035241d80003281d9104021601d070395101100d40d00d0303500d100784c1c108610b455400c1c001d400c032009400402e8000d224224200510920b092008240c0e51f55a6024042c00c0013401d02c44406000404240200c200501c1a0781c00082ca600d8204801003c4558500d40383e011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 130750539 1250 130749289 130749323
    0x14030703090b161a0a0c0e0906010f0203070506011d010b03040f080a2303011a0f1e04050d060608010b040902091303020a08030c090f0103020c03030f07030b030d020601031104020304 80
    0x2c960400b40307481d083c21101240c15004111150a2207154082e403078204890b42c50406111000c4502c2d9030031000c1045052481007940d5212420b401d904844c007400c111410301c2282d20100d185100b00d1038000c1507030140781c1c00003031003503030b000040500c0c4100c1c10420b070130701c0ea2144210400e50004031405420441c0414101002c10010304c020540035070380c0d281400e001d40958804002c00e600349813600020400c0040100019000c46c080b801701a41c54042940ca06108004080303c81c1c010481b040508000c043c00b40f10700e400c25481180c0c010440034200c8201c4541300e0070b209006001a1140364595400c0803491051361a2501c122011961700500301815910b4060301045d03521400d6804a0961046417483c101049610001c1c40c42090300021190342c5a20304000d002c3e001c00860605030506005114401a460700402030360fa0041540c84251100c0e031380c60504a0180c08003102898040c003d80c046466120707404240345068a00030b00c1c00e000c00105071400d20040b480110340c0034004200043c403141c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 130751789 1250 130750539 130750559
    0xd0306140f012709020a0c1101030b0102030f0309011803021c08190f06030812012102010804140a02060f1e0f310905060f01080702120a050705120301031403070309 72
    0x503803c4225007020000e9141c18031007040b41d0080c210707000403540b540410340030060042c0801003e10380a217428040001c0c0070001030340c2e9000b0071103e040342e04004000190350350030075404105034602040ca80345034034126080c00313510381d0b04103c00340650745442805202030358003400f0360a005691129840d0740104107000c00a00501901c89124041030311074030004041210f400180048410b1000121401c3d494882003c1340300032000c4820391580e009403103004c00f43c3e82140070036034800d400011200b103106c0d266010f14180166940000d50214010400c149100c1c82d440c060002162150803c0850201070101d800e100d00800c041d02c40000d50410400e1244400d90445028038035140d8400a00310007107210140e440c200607041172003940c5c5e80303404003c01490002224545618203007407011490038070341c0000307444c0d43c8050300e014502400000d60300b2846219170206c44003a0340000c15284120310701c09414280e640284815200034148212403491690040708451a10341d25449050a4500d4428444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 130753039 1250 130751789 130751837
    0x1050c030c0903011118030f011a06071a0403050c0f1903030c050d290139060e0303070207081203040209070c0f050f0d05180913050d0306140f01 64
    0x203405540304d07480b1104170b40150002d032420040e0078900c6000c284006040c0b518209031005010f106a0400c01060122800d01c85c509200903000d941c100d90780c2020b0b0030401541340c000d15400c2ea140c00b4a4003000b0034503078000e01400e03c2018200643e06120300d0b91a1190361040254444501120900c40c41c01c00a4002c1c2e101c09071540307640c10014141320b40b11880008990400340307410130301ca44c04010800c09d03000d040742c60050101d0909284098201c03080c3c030721011002100081c1c130018400c403001c0c101d284400d0807004180c1d50105040c04034240d02d00039941c40c0d4000313071405405442034603000701c0c2c480f8010403a0391b91400300c2c40c042c0741141c0c1d450b000c001100202510200600502c107004e440800c1c17850018182c80c40c040e900600c0000031011980d0b183c0700300240342008000c03023400b1940c45040e10703107682c28642e0811034610342c15455900c004003e172040610001d00b10311400d902c01072071039096040351b001c546144a1a005030b409200c1444400c60000303508500003408900003003400c0f10150425 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 130754289 1250 130753039 130753057
    0xa0512070606050907030b040b01090b1603030e1603020901050a0e190b0a270203060a050d1104050702062d0f0a0905100605040501050301090c0605030405010e120702011101050c030c 80
    0x8110103a076100410600101614000006034840c0c0c420b40003800d00340200d1034500300c01e18016000340d1500381e0070251401454641c03804504240e37002c0050610a8108038840f00d210029641d96500002c00390040d030000e440100d0240e4035490000605160105c05041102d02c9100e801c070b11541c604544d485411200b5950f02a6281d0325003416401362a40f24941c0b02a011020350b120590240c4290114015003003107000c00014010401c004054841d0b030650b4040701d006407070659400c552485c0c400045e510001c0541d400510301800c00134425400030f400d034005c1c5044988040806003000d98018450341c040710000201000c41c0208143c0411421019131000c9010302c000390380e002580d80e4a06141294940e8058983c9418041c440e45c540b03031041a0050500301e0080007054226a5000c0d02c11002d480f91805118000c070000703050000c2074001600341201407003520030700c2400c1130a0784640c0c2c011740016030020321201c500049450051050038040c0790088500e81c00d584d140e82c1c2c013811541c0603840c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 130755395 1106 130754289 130754291
    0xc150501060e300109060f0213090902010f0f021e0102090307050301060f0b1c06090207110f1806040f0e030306030d090303050403480501020a05120706 67
    0x2154070102c42ea03c00c0e028070200301102c03c90040264010150850b030400202d041c00700d10580c018025100d901c041070760702d0b03501c8402d042e040f1400724100a010585014080b45017030b000f079a4041d0a07210f64030442d4800595252501e807050f62120400c106607401088a010b240303402c0c00124098031054000b00000b5241900004040c0458804c1c1e40c0b0110000034502d200c0c0c081c1c48010000e0302c411500c1402250342d10581c02c0f000390702c40403050792910721030500d1460354600141c0b031081e820001044c00d410b569814000c82d1030404043d02c00d90340315540e02d084001c2425540581814052201e018580368944001418102051030007218100720802100f0310020f5048000d031015240c00100351501881c2d0003180710300700d2b1402230300110707100340340700d58400202c00c02e46d442103410008000c10225155503c005aa452140100060007608608800a0344a881d0300150501d00c0c061a8 = true := by decide +kernel

theorem cover : BRFrame.Cov 130575539 130755395 := by
  have h0 := BRFrame.cov_init 130575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 130575539 ≤ n) (h2 : n < 130755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
