-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1586
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:43:04.814066+00:00
-- url     : https://prove2.me/submissions/dacace24-ca92-4741-a70f-e1d91ea1c0ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 285071942 ≤ n < 285251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 285073192 1250 285071942 285071977
    0x7050709050c070b07030606050706050405070803031302030c0f010905060a020c03010f020a080907030c170f10061e08060a020307170103030807180f090e030421060f0b010e0105 78
    0x100345034815104110345800288401280c000203001c1140041a440685803804208841c2044000341045c055140b02405036640c1c0e800003010018104440b07009400420201d82e168038020141030364a28801d07404038007074080c4085428440c00e02d503a0750300c0c16160503142c1e903000ca400c00b01408450741048130520110303c1210081c4a243d1401c0c0f0450038500b016500150340d03a4291140a010001c010b403403e15103034400d4078104007107640e40090070169450344407003201071140c0340704c254984202c06042101601506c019003c1a18055200904444500b195850341011b42034040c0071210292107041001e40081c4001004094180c5c021944400c0e5400c0c2446500c000d0b802c00029804260070840109500800348000f03d6005609505051192505162468100410084200414401c100c8050344a0100d01c82409062055401070010343c030a03e0f1030742d00a000220b143ca050348106035541443c1016007a061003180c069100d0192040c2c40302c3d1034a0f2049401100d90740c0c084804281c484501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 285074442 1250 285073192 285073199
    0x3010b0708041a0304020a05100206040206030604090b0a02030f0603030a020a0305090a0914180d0221070f0b010501030c050c0604030e040b030304030309031103030406090b0702150c2103060d08070507 88
    0x801604000c503110002c500d0713201c0c5410b1052201e0144540c101902c10b1010140c0c40701c0c200e0b1f00080035503200b981643d4054894079008089000781c4840000146070381160800c021001405502540c40741411410320415a19a9410305440b4440c81025000681000501001103405607004081c6042c001d084200c1030340e07489404500b1a10610b1081191000c07900501c440340980d00303030050001c9a1400a0030004d028800081c0d80c07440180f2507c16014004407a5440c0700d60840c0940304800d400c40140c0110764060700c0e05440041017402903e010900c1c001e2840d0319184a801610204034041d00108410340301e079181900c6254035801c03050b6101d43c0307070030001d0300a460501c00341000b54440d4a0340c640050452a00702440100c40407035038083d070301c01c0c0802c0103a15801040b16045802004a103581d80410b4004124030358a42c10341a0141c200024001a4104001500d0040d0315843d1110b0485400001d060100c1e0344425100d4640c030602c0700d413600b40071945507402001c1c4917106900b1182e50035074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 285075692 1250 285074442 285074459
    0x21c0c0f08010c020115050612270319020705130b0a0503190507050609150c0312040c0521030301210c1203110102030103080304060203070c0b01080706090b03010b03010b070804 78
    0x465003101e071441e51115150150507409020b0b0440c01d004a0380300ca02001c2c20500414040c0c0a40a94001420204000706011003460020f500c0d0f8488000e40c0060015060150135540340c0c0015181d4120220ac01c1d00c040c202d070b101282283c20383d079000704030100000340c107107440024204016640390b0007084000001803e13a0104103140014201216030800295142015170506c151036001d58040c581c20882420a9900c14118180c40c45c010304030161203036105a402403450007001741c105412002d005c18403040c02a0b001c511411100211050401826180c00c00c40c4461816510545680e0091005210b41030b6100c0081110b04085000221100082d80b01c0e5102260a0b0b0b1011400720041d100c0181031650244001341460412070003540b455155948144051100400c060820341d808804580170038410410040d280d42c001c01404125611650702d591100d62500c00c10000c2184c1945c0081c0740d040d145c0a81e4100c9224402c1d09040da03103010b01180d110741c4040d000721200c0c50100008601e000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 285076942 1250 285075692 285075719
    0x301080a06022a0609010f0218060a090306140a0f020703090e060f03100f051303140a0c0203030c010f051e04020f030f07060e0307060c1509020a080a050c100903021c0c 74
    0x60f00303440140958100700c030340103084441ca03800d5070300d58034010061034100b6642418149100503065034600e0751100d03050000c441c0081c09800042c155410526500b40f40d11002e0f5841e4020300d280002003051042c080000700c01c038851280001d001c585c091900700001e0f00c0d2800c11583c08180644202000c208a10009003048000881030b40d0841d0340d180c500880c01171620810f43d2151101302d03112514469a140a4052040c521140c41d99110008a00034414400e082f849451039000d000c50761216017180d8820301070984c0b00c40c000c4141e4607240c001140d0a420b5107240c1000c1d07000d190801510b46030b6800303024180401c201d500340c2600c148141c0c0c04690340e040040d0401070446030380781c218000700f00c410181815503c0c0d02003420450a042034501050505405884a6404803000034030600c0a1000c222041c2140d842003451b0701520714054207000000c11403c01c120320886d5103880f181000c2c1c03c10f581d030b01061300020350040c07480b2009003039a0f0002c10280000500800d040195103540350850700888 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 285078192 1250 285076942 285077017
    0x50f1f0b07080c010c050304051f090c060e10090b2719030b061f050d060803040f06080f0705040e04062a110f0309061c02070c080607050301080a0602 66
    0x15940014103c07541c2100780f2a00c01072161a2400e1844c0d800c1c03139254169204103020089840258500030501281c4c0194410380569500460200303c15984d208040c001c42082200c10f40111a4100070001c1c0910610102c002e0300c8500748482c1c03c081c5120801d06480720361a80184900c0e80c968100c980e540d42d40c81079120202214050001030b181035103045441d9001c050091400307601d80301154142c1180d2400c1c0080948aa441d0264503040c15902800162095038030911440c040003030045116600e0f081040141da1094680805503120102c640c07075204030843c0c00500040c000d0006101d135400c07811900c2d0b040303070040101007114058000b8000564428882a5a07250a007117000351245030031851440403050f2100283c00d00000381354125880c1c0c440c0c0907000c0d02c25400000c004801c0c1a00411020910050050840d110146440c150307007610424040c01c40d2a105000000d42aa840b840c11281603501c80d9001e0803d04403190340b800040d422070510608801103180a54500c8880c0b064400c042d07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 285079442 1250 285078192 285078203
    0x504050a050d0e0a211b05120f0a03140403050f010b0f010c0308010e0a0212010b0301050424030f080702060d050a0e0a0c050d05150702030913050f1f0b07 68
    0xc4002900d482480c0a03400507180080c069401040f01d5a907a901c1c240d8801c40e10000d0784c82c0c11744002c1c1c2ca0442c0d0040740400000b000c00e1840101c0e0f400e018558000c0d0400d03110140d456010750a007118113284d441c040040c0d51120350b0f00400101d0002803007080401803140796120081e041c1034680da40c142c144000c0302001011695503108020715460010066160200c003801d203844a050703161002030061405008240d04200040c02241079000c441d81250300804034419550001d5071140391103403241e8020304c00c5900c180d0401010309000825003129080c1c85455a4080b0f018514503070360000d51078034840b801e40d803a1000348031100c0075803503101c024500b03911010400100c0740341111811088403d120b0302e81e00030350304c250b14060010322814902c4c1c040c2e48007200c0ba000101c019240040c034006400c0301696150359070806228045400001928100804454484440400c080d2f28011200122882626003004c44042820340001c50480b88000f070900105050701503c94100c010325a1018108035403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 285080692 1250 285079442 285079453
    0x70c03060c02100501051e030f0a1a0a05071b15050a05191b0311090a4e02150307090302031506010e09130203070906031e030912050c04050405 63
    0xc403560b0501c148280c5840c060700130007a55041101199091000303100c942c0d128500d51003030000c15030f410042440150308e50070458148500301d240c000555071000c00280008000307000070401807601c40c0101441248241c0c0c604140844200340800d544248800c00d4655280c40c485a075034404407800782601c1205482c60201e201e00b0042d1803c1c8001d5404c500d0110007503d000c1c140c0b6031240d45592034801886c0c0307a250102e4080002d02c110001481042980355009501080000e40c10012203800343ca1210307000c02071014800110164054140b110b1016400e8003010182c010444a090045e542c1c0280040d0041c000c0540c42044a0030310b910613520304001c03a00d040c00c1001185010000c0c61400c840c004041c03035080c20540006003441c40c0081541c0d04c140c040c000042d0227644d0604101d154590010b048460503aa6a0403400040145000a80d100380b15102814180c1c1e40f200b60003440980d15607102e01c0340134504078090207000002001215030740920410644142c0c2c4501829029502030b001615 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 285081942 1250 285080692 285080711
    0x2030c0c0d09060203040b0d180c06110c0a0b070302030712020f0706021c111603062a0c03030c0e03121815040e04080d020c151302090c0a05070c0306 66
    0x3807a1498151003042080082d940520001c0d03030220540e02244d000310580c9417500031000d00200500780e0304110445820701280240113105500c00410300315141e40c2c40c0c00c1644c40c07030700c0f80203510349004200303a58000300c6c0d5180411107185280e00400ca618042d206481c02c0070141d03611106125950140240140c0c000c3c2d4020903c011705222610090107940002c00c1009005a029102c91340d1040c2c0c003100384809800340d20b40301d41080c8100c28035070328031108054585440b86040401005482c4000c0c01d0050350b08100528445085500c84000d0019100c1031007500c031503501200600701325440c0c5400c0003669120320540c1c1d10100481c02284844202c1d0b107031181c1d080c03106032400d0085003a02d60300c2229000e66400c24240c038034044806940130542c94070f0495a07241480c24543c450741d042c03402070390310000c1c040310407190109520000c011003618070f80300c3d07840d541c0c06c1400014801301c01035071000561020802c01140080140800700385820305500b04481501c1e0350f2150a40c50348251807503078880f035034403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 285083192 1250 285081942 285081967
    0x2210f22111507260a020c040209030a050a0c0e060402040501020c0d050c15190509132003150a05032109280806070914040b041d011d15040f0c0902030c 67
    0x1645400035040559040025280c0029550b980c0d8640d032a0088d60f00203140e1440341c07000e00c900d0300d541e6004000c580c0180700e14900712a0310f01c0e0600c01c08181960840100c1c0f540d20b0036000f150b04a4805a0091a40040500c10403100c41c0408104450728861a00610303000d48450a140080d0240707403030400c0d00e401c2511400109809450384c0c4030100300c1c1c00c1090101954443e01c0c01c1c1220205081c0c0080c0c150152903101c118010749854041e44884044100a020310311406814002241a100600641e0b0743d4000d041d5601812880c0e096050140c0b000700016400a0000d0004002d008201000005041c90b00709500781e40c904090202d810722000901800d034003001615001002450b0042d00d2a1400e1100c1c40450300350041984120380310441e03000c40750381d10780101ca4800c680340005265080541c80550003041803400e81d0010301064400000c50310f80114420140310081e25808210f0354030369a071b402c040032210700304035140d0b6580c800c00708100702a44060361080704d103940030941c1e03101d071080c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 285084442 1250 285083192 285083243
    0x50601270303110c0a0e07020a0503030115030f06210c0f03030215090c01020703060f020c0616030c0219240905010207020108011502150a02210f22111507 68
    0x43c000c8913400b802158280303071100358007001100c040d05982042502c441800701e00b0702c0c0e0414000790140c8404000420030150511400f04c81e0174103624100100c050b00d01300a82958180c0c4118240707820811158064801545a002c07081c51140340d00d2400e0503191f000c2480c401d80c403500150700507400080503001c0118003032000c940001e0300b98010b1040d075610400003542c980b01c41c00001c10f855200c00800003d8041e9406945c2900114801d035181c2d45000c040c8124a42001c1c60301100182c2000e41e13080819002080400c2c43c00448aa4036003041540e484141030750000c00503a4038401d8840e0200c00960030540f00e08070449110b24000f50f940d00040c0001080090107802502d6144502c07180354820f030760000f502802002001070b5040080e84e801541100a0158200d440ca021410416450312940080c4c00c50344101e46030039818140d5156221180c00748480c0a00c240e05c01644006031401103503e1000160080302d00800d000e000b0180029180440e0308030307050446040e02100c0d060b205c041c1e4910007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 285085692 1250 285084442 285084467
    0xd050d05090d02030f0d260103030c0c030b07020627030d090305070507060e0a050114091e120a170403120309060f180b060603090307060e0708030a0f110a0308010504050601270303 79
    0x200347d20b414081c0d0740003148110040c03000070103100440b810201000303510b2110000035070b000214a0a98034004202a450740c808944d07071844100890b000d11014400100030701c0c00980c807238000b103003046d08183c072490081410450a81c14411b00703010700301c002034003000038601502d0702d81d0f41c41408008900c240032041007d900700d00d06026040d03212806481c10b01c0103580c21090121030000d00300c280082440494106a032b01150803129500e41441c41c08030020340c022942e0b104210402e40041c2c43c0c108007045020383d000c0185006100303441010003500c02d4101858150156400151a5124900a200302c0d000070907010fa00c0c0242110a8091000c00040c2c168059802c1d20800d18616104e1715084c0c50b480780f0302c00100305c03d0f5a26020100007000300548006050000304499403002c175240013070f041c0714008981c2e10018048588a0024810204404000c16410740f41d2000380e07401c0c00b0410000e40b90083c0032504000c0100a03805510311201c0040106102001c0484030b000c2c11418018940d1101c0b60 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 285086942 1250 285085692 285085727
    0x106020d09090507082202032a030d05040e180d09030b0906011a1c0f0e061302090c030601021908090a050409050a03050f070b1f050d050d05090d02030f0d 68
    0x410881c3c469000141c0302da004c0300d00b400b86caa03c0500d10b108002c1310001d041019400d0301c02c0c0c0020340307103801ca13000c0040703211001440d003900c50780114030801d691b49052254050001c0c90501c020045001a4040d01d0703001884501026460030b040076030f140c60072403408180707000a154921700b001440200d000c02600500f814025149960501800043d00f4110f807002d108003501c000b450110540c4c01ea40010b5400c0c0c0c0c1ca400c240403000c0d0b642900b0000c4d100c15070710442c650054801003043d0051848030b040240c3e9000d04242115952804560415000107003401e040d402001892000c0d040c4401c074907610240714400c42030f1150520380501903c401d007504164040c0740b4269422022460004110036126850300d0520341e41d194000d0802468003c001000304480899400d1000d0f17088485141011036180c48041507509036908204001e268094201a049030000701e48203d81034414002000810406021040c503208035071b000c00d1500364400110501e640001c0304c850382a60384051251403105000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 285088192 1250 285086942 285086951
    0x30301030b0c16170906030f010e1815101e170f1002070f150605010e04140703091b09050901240e071202042c01080a030c0203010e060106020d0909 65
    0x4001d000703080c1908400605400d25088441d5a924134500854000c084060701076910707810102d2041000460070300501007245a0180024030040303c2848180070184074100a00da101308041c48000c88030009028040d014250031f10201d80c80f0080b02868424210001e440b0101c40e10f041e5440300c00444015425189412a188025a05038009200160b0b07401c1142c0040c0c0c1c41c402c2e4a000c26402c0030b43c070801440f040c1c0c4c030300901c201c944640d4880400c449080e205c0186a036840020002141c1e8102030042d4580c0c0103001040c0281e2180e8010741e000d5108221440e840d10b111464552a0b401c40d5110f058040d4884c401c2101a903428010b5000f81552030030340340240c009401c1c0e585140032403409840c3e4007024000025008034843d5411212012171200c045507103e40303d08000a0107101c42401d660505961140d00303402e540d086100710b040703411440103416403554035501155990b204481c01c0c0d030702d9901d85203d05801181404440d000f031196400030050200000409003e0305c14a5000900c91441d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 285089442 1250 285088192 285088207
    0x1b0303041701020409050702030a0f030624032706110424180303050301032f060a0e0a0608180a0b0a0b0102011e1d0105060a120311060702030301030b0c 67
    0x419141035441c0614011419040c01d4a0140240220761118419a0a090500481c90b03008002001e10360384554980c0d4400b021800141e06903400c910400e40040398840c40102c410800700c44086480c091440e022030084000a100c041030b401078007600310711030940003042c0100000e921a40003400b040c6440917081c5850030700c44150092245000881d841d05000320300e000035218003d80700f88011500002880140c99041c02402ca8000740011038800d03040d09004c0640400146000f01d41846901040c20990209000e01c2083e0b0080709103102400840002c40d40d03107a40e16443d64014103160360340c3c001d051601030307000c0e2107031005862116095004070001030b002c2000c400169500980c03100c0045035138089800100c1c0181580b94540c3c0402d400e8102c2c0b110114120b80106410b03594004180489101038507140e82210340c1030b585141d0000f00680c0400881c5c40c1c9001e944c214a000e4242982c0b10003919903102d003490000c550070750041e08000700600c100300b541c03001260032040c1c1001044c04c0008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 285090692 1250 285089442 285089449
    0x612071d010206090613170408010203040317280902040e0318011103091e12010c0305070306060e130b120105010e071d1201021b0105190902150f070f03020f1b 70
    0x50802c07800645407046c01c20500c003c1286007035000c011440304560f22039655151500030741094904900080205081c0034030103c1c0813105078000c1c040b0209036020415a40100c254880c00740400f80d8400d0386807103042d030160b91603108000b03115122070007955403074005110001001c1650307040f6605100c02c0800344d822000001080d604007110640344a400824400c40310250203c4660803039511031a07040840c80b510360190003801c0085e1003510140041c1c2c540c02029015030701203004d8100003801c00503408100d80745c84030070809000c0c1510700000b6820990004036898190000c200045a91904010071500e200412003d03440200c3e0304c2e15400f007461210150720154a005803c1e44100c1c00d0380e1a0000c00c031802c0d4115684280c07002c51f80340003522040d01c114003a0004a800140c0342c516007c110307220180134018400d5180c0c3c018481041d25142c2d41e0440300704c0c0c2000001d00d403145814041400010692080001c080b40290003c044098180800d07520b0040d00703600749420407018681e00921500c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 285091942 1250 285090692 285090703
    0x180207080708070c0e070210060b0408150a06050d0b011a130b0714060702010905070b0a17070302040503070e0402130902030309120a020306070e0a0e090d0c020612071d01020609 78
    0x1503000b00541e907a140141010074199400b81c110400000800051001c05a00040d1144428006000030b20803256100e075504a18091485050b919400c0340c044025590b04014007241d0114400300d0020f0308940300c90100d001c28499660442e80c0d44081b1005020b1004140810381504403c442485e10306041161f0380381d9444098840d2003620800407445c07108000c049001010524012030494a0900e03210b03900130b001e0310b040901134a103800792a802150041c1990704990340024079865455045130302c004d4103031100d00700900344000c041d400e11011440e5a024040d420040410600500c00c504080c010403040c0001ca1940840d85450560f42c00016200031064505070030085600c2140050082c1400303040c5140010000d42c07500804041220b1242c02c4007074211140002d8581c004026250343e5089005d800030344505203950721000ca20523809108071550790780035201411007401c0200c601c040c2e80365942d0540340d52010940300d418100c240c12410100341e0520000f44014010b509080740c950b030320303207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 285093192 1250 285091942 285091957
    0x80718050601032301290313080705030c030a0801061b1b0512030c151509060a09020d0c030b040209060d1104230108130b130302071e18020708 63
    0x680e1603800107122607020354003c2a4401040e07032513400000d00104a804003039024051480c0d44c081048400000d0820a40414041c0d01010200303450341c4c49480da46a801417003075000b191343e40001c2101000295090028158001d0400025510b8a81401300030f407407030303405800c83c00c1046101d80740740504145100c40c900d00c0396001010311008841e8080a00480c00c80313500565003001c602034803d0043d1800100801089605005403080115194035000e0266400d5540c000c843d6004110a032451a0541c6c04070f410030300c010003a242c8580c0e2800031409a070401d020408d151036451550030002034060003804880e07941103800f14503290030100061058000d08080c1d05016aa03202c4400618102804803005894030103041e142103640c8a12000c01403102595560000e0f41c50340224043c504403000e484035484d40420750f8401551488541600604010000d404501c6020707400600c07500800014040c0303c044020b003501d407038100110f00100c1c8010b104440941d40c8100315100100d4011410b8440d81e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 285094442 1250 285093192 285093239
    0x2100f080105011422050301020f03100509130b060402160f0b0c041d0c1624020331060c09030203060f06010e2e08040605060f0906120703080c07030c0807 68
    0x2170903c141c5201810110b41c0e003055401d5840006c1e40307490a08403070081c51117480a14809220036440d10188100e00c5c10584044241c022001001000900355001d0a170748803401810040c00c100c580d2403095091001d032401621a503107405031000034010007059080c0c1c8a03a142c0555494507203419550b0745568070b13400d10840700c480d006001c0348641c01c1e000c1c00c90706502c010400704000b01a19060103260710b448445202d03070440340d082c0d00e420600054001d0b00c2c8100400c2102e038072462210028901c0c909115520fa0703185000e0302c81d00c1d000259a6119464103000b807503a40340b01990552060510340b000140840d0f661080b000100251aa0b1060f03001046940503500e50358072180445040280746a0030300c010f2100400300900c83d0107a54003c0740d02c1e200324024582448240c541ca414440d542c00c0c00e4521a800402a80008050f400d100c0518a074000c0528221480307150b480e2204450340e0040645ca241c25085a0010014070688030461009850550003408116203019903146505092030001d900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 285095692 1250 285094442 285094477
    0x70215070e0102070302090c09090106020a020603070c02010e03100c020c01020115031211060705030610050c0c121e010c08220b0c16030207090f090f02091302100f0801050114 77
    0x41da4800c1c04010011035004d4043c540500b0b1144005010341c0188629078043e54030300000103000c610004103030302d9042c1c0240260740303184c07a010001c40700750401e018281d040c0010301c044604039803020000018048040d0400140c1001c40d480b0090511502c51050703070440e8180351190300d4811640c801c0320220790703004520709c9041c0c808080569a850042c0180407030b5019110400c542c1541040c025403080ca0101c40001d80c60502c1c05050321103024415001d012644900b600c0607090818010003e05080c00b0800c07200c10b182c14500380182c926482d034400b240740c1d4640c0c0503540c003e50000c01194000e552518540340303101041003012a00f500780840505100c9000001c50000c00d078042c01c540d0031100c03040500244815600380030355949400c0c4903003041189440584180c01c81d8a10407607800903444149600022050340810401200c040c203d0364001c82400707100300040c0e65060ba0304520b00c00360303213441c001110a4080a0000f2005138461414002c9042100c0c40c00c2400314103c41c10051031520041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 285096942 1250 285095692 285095717
    0x3010c030911061b0d091508010602030306040e010216110406090501080a08090402070f030e090c09010c1b0807170c1503060d060e03030709031412040b220e0403030507021507 77
    0x309803102040003010f40a80c8a400b901598084100c10590f402c0d07407c1101468480342088540c0c000034856080180c0044c0040344903442c084d009000b024802c1c3d00094201807800030480078241030017030308079020440b464030711950341014004c48006140343e040c03c001c298581001c0729220307060241c0003861004000b4001615543d140d068544e01038100300b5810680d0f085c1d00d0054801042080e029201d00c1c0840c00081401100f02c00300d442091040c0c0d5080e04800003541c864083d654504541c12200d2902e12000c10030340b9081042e10000d080c00b903000000175958030b200034244150f420394a0b0140d54000c0d2940c101c0250300044a030003105c00d460042910700141000d40040c411080f0111007400000144081c080e44041d005042c3c84c040ca210000444480607003070390f68050070344070501011040c071040019200110251041134046902400003e00310070041e075032010550419109502c241e802d100c1030662604c900c59204d8268001011b60725007034152044983e000405010070402c0560200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 285098192 1250 285096942 285096967
    0x8030c0d1e050a08101505030603190c050609120607090f060f0215130b0103030323060906151e0d05160909020c030d0e010b010320370c0203010c03091106 68
    0x28401030003200c00301c040c3d14401000c007c0256000340d8216200e440740043c1c00c003c4111100170245900d44c0b041540c0e00031890701c0244003460300000c420a40c8a9002100b0002450080c4480e40c0310711103541c1d40d1500b440c10030121801b0141a80c105408105450079904e030b0300381d000150340c0c00e59864003845810313030340d500c14001194103803803100100f219034982e000004143e0560070101c00421510010050141018100040040100c5400303a04c220307000c0c0030a0103030500f12442507043d01d8030b1051600d405116611844142c03100c02c0c503840b6100b000240c42844249038869550044d00c0d80441894806103440300822404c09805294141d50b40052659a001070400440703040501c0f480342440074041c2ea0ba002c600a00203124030501007800d0003070320000f203250103052400408503890101e08040c015028864901184a200701074408003d4004091100c08041d40021070a40c1d81ea00366424403d205140c2502c1d581d81c2035000345420301b114440040c1030035403840200d10b03040e90246d0715001f00f0000d9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 285099442 1250 285098192 285098221
    0xb0c0d0612051f090b0c07060603051203060a0e060d02010e0f031002071505241c0f23030d020d0914070905010503033108030c0d1e050a08 61
    0xa4044035806450740002c02c80007064114640b0b80c2c2002441403800b0002d03240094681100006001c0418a400a00044821405004030b20301411000030000c0d00c81c3d0300e59140ca20b0300d503800c6811200110030001a480c184007000050482c900411089051034804200c0c58504540020305100301c3d50900020750320f449102d0040c40000404640240c40a204010300a501020301030350700100038030000014031041d004440c016010b40c525504101a400000040c0010704503070035600000102d600d000c1041031010314900340f801506a240300f504e49180c10b081c62401e141120141800400f8918031284000c4262488114030000250341d40c40e00e503c034000105000d400050680ca0340d83c1103400108030000b05441501c0701da0b8010000e0703907260020103a482c015085440781c41500c903170500000380c6401039442d8189c12481e1502c03d02c1030720b034007440741160810381220420790b0042d00e001038401c0d485800f801280c0d8148000da0142891407000400341d2084600c075105212002c2c0c0800c1c3c1c02801d0701c58 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 285100692 1250 285099442 285099449
    0x108060603090a060c03020d0e030c070501111009080315030c060a0f090b07060b0901120c170c03010504050d03060e04020306150d050a03020a290a0c031401090509070b070b0c0d06 79
    0x90170459010a004042e000703400044410b00d05500d0704850106240d000401c4500c0702144d04002d200030762410004403240540d4403030b41211800344030341c1e02a5010040c06006510703442504480d0b00c030b103001a403011280c030500c01100d20a80c440c43c0182c403543c82c0c40c0c007220286602c51802403155a140c0302d01b0b40c0d080c1d440791f1041c048803000040300ca003406101c0e1300041484204880110990b40d880c600300000c0b0441603c0a8032002800104201c0549044130300d03509880f12406841e03416400d42e002900319001200c007540c0a4100d0500e0304103260703052049002405402d011001743d4180b680100e6587d480c0200f040302141103181483c00d969840503241c2c8070b5640c6c05030132203001d141149002522050076030008c8441d164100d03100c1d0341002c0100402c800d000102004102240e6070030283d00701801c0c6412007082490782d5000c4941c012055036203041e0213030401d000081510f0904000b081e142104a60041c50207a03000e010100024010018503034111480341d03449038951204c5405171004040710b50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 285101942 1250 285100692 285100703
    0x503060f09130c0605030c0406051e0d051603020703020a060209030115090e010605100f120b0d0f020f0609130902030c18070206180c1c0605010b0301090b0f0108060603090a 76
    0x30010b1861060110340b0089100c0c001c1062036555800301562540003d40d03180c0a0f0400500081c0f24035840f40f0003501040507003403003140c0100f036804410300c12548030140040c102d98803081040402600c400d5000c0c01ca201b54501107103040b800352030094582c40d002e60300521131600068503150759502500000d44d0140000709000005503070708815002489a0040c0222550900c800007801d407070041040e1001140f035468042103d07031560402c80d40c038051011540c003100d9030380c47c3c03101060f10791440000c4400c0c4a0b02c1384852401403401006140310071008507511a0b4001c004603016030b240c41890461001c8c101c1000b080380340c450b200081c104880701001b10f40009040a20030081c11000041c113004844540030f603103a80d22412103d2546a4118500e103c850f88600341011150402c000d90003208000d009265006a02c6566807000307592003a4050a0b04c1540803006000700c10b903520504030000412101c400c114540840040d01b1048010001c920820001c0001a640d000c10b1200e5030300c807940310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 285103192 1250 285101942 285101959
    0x3210408040f1707080705010e0409170307050d0605041a0d0303020c060f0105040507021204170f0f0105041e02130506030114180706020601030b0606070318061d0613060503060f 78
    0x34403106204044030118000b051013a28800110590049071201c25684180d64213190750200340c0910000c2d01c42440b0480c0c0307001c9015a040d04a202d138102442c000c04072a41c91a03560000002e40d102981c001ea00303c10b01c10351070710119a0b0403802040314520303622000d60300100e02c0040c90509500a003d448a005150301400d42007000381415028030506030745045804100c03944a100040b603455060609040c0c0826081000703000325642c8044001030040c4100441c1c0f205800c0304505070030300c11286a180103e0707455609010400161880700408024111103140107004a600006c940580801c502210700c0da640c03000c1342803070f2020f4001182d40c5590180e21034544c10f25001c003140d2000310100007141400f0b040340100b1003a00c082030180c100e80d0041501a5141c0f10030042119684c44031504a0a010104000c0100b4040010b005001002d107521080c1803420700403005a0200400111580300342c40030400070b20100f0001e00700382d066500515181d0f41720b540d100040381240348004800ca900140b003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 285104442 1250 285103192 285103199
    0x6021e03131214150f07050c06150a0302060d09170c100b04111201051f0215060607020d14010501141c0309050a030b0a0e07030b0117011509020d060803210408040f 72
    0x12840580d0007455005c43c0c2d05501d80d0b8050040b901c5005100903181980c011740d020504d448001c1442130610b0078004d06007140b044e82c3e680050f500e58082c444128081c1d4649500301c09000b00c00000b01c0703031800c100d81110715003081d240c5029100c21108494200550b0ba43c0180401e42d03d0340d41c001903460000c0c01d912641c6d5540700c929410115001d12510388240701140c0c081d400080c084908602d5210260011b2010140035241c580c0e500100815442d041704080c0045c40140e540d10000c411010302540c425020034104250150039500c05810802071030001403161203103502c03039200403216105c10704154403001006143c00c1f40c20510541c0041d40c000311010000c414000310243c041d0007500c034402c00300308213412207a11701e841e0b8005200190a0f0507081d40100100c010300540d8178655680304000282540c00b24882c0f1103403c800c3c4d080900ca05901045480c0005041c0c80b070b040c00f80040200450030440341c40590f2400504095094034004c2c5240301240c05c01c134400e419107000d04507019082c01507d46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 285105692 1250 285104442 285104473
    0xc0a0803042309012414040308090f06130e010b030c040306020d09080d06051e0607080304031218230601050402090d0606030f0201080a0504031b140706021e03131214 73
    0x417448005600c45540e09800b04a03014100e01a68920701004403070405103140ca8500c850740113001140d800a50704105c000b000da86140007026000038140c0c102c240310b814142e103111000e0b0160400d4a842c20200180b0032181c2d01101079600700c0f40d00030400741c2c0c0c824071100b1100141600110080c407045000c120004a0007150f00302070103440c0151030820280003561030401040c10410102e5410040400c42e40020640d040021507005009003882c0381840c00540916045070840c680301e0100107800f5640c8010000031141141c3c00e03a18090081c0041c0030307003c40440c0c1b01c1070103124442c8036940c0040c10000c99140d2881c00c140d541c2e000401004107669030b04003548075200700c0808900090691000624200f064482d40340038641640d9058074882d0813910440c445050001c083d640312811030600c00780780004115240240150364040c041c44040398614100920074031154100580040c0b21a01c00e00d003021068004403041c046950400c035560781000d80528400d4080d56800b401568500540d141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 285106942 1250 285105692 285105719
    0xe0703050f1501050d0f080f0304050a020a05030c010f080714190207081203040204021c050a0624020a0224030108010504051005010303020d110c040c0e030c0a080304230901 76
    0x1d038202680c068055440040401d68000d000b516403001e0f03c1d0f03110307001107462820318000c01031107031003002d00d000d09114a803800750b04121012120341c3d0182c00c80c9821400c0044038513000b06020340040002a003600f001800c0808030110711020841c00034000b0391a40c3c4100c480e210451101c850403035076102c0b2145070704100500d90328640054828070600141869000444072280360421082c50f045880c0c5508100107540320ba882c00c40d84403500b08144006d02c40c01c0c41903500401103044d001400038075004140c0240c000c05007600845c092088007212520ba0040b031042e0066904036000c901c00c42040040100100d00001c0c50004120b010001049000c01580308a024600843c00c40d03400c0c501500d00701098070002d001c020016000205c84918ad64001e078101148142c610f03007a80c0789401c000300032034112100c112840740021166014441d050a00b4050308620206c00d490b082d0142e81007005039075480c0f0861185070641b00c14407034038580d40b40e480821201002001814a0180d5a50700b411b19282c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 285108192 1250 285106942 285106963
    0x4060e0c1804060605030601230a2c06090c16080d05160221040510020708060a1a040b03070e0c120f06031006180209040f0203010308030f070201060b09130e070305 72
    0x5032804d04049414034002941034102c0e0481040c81c00c107503140300050a0b8458003034100582022501c50702086081245000c40101e041e808181c120300a5041c10380c00c806c28001d050b6a004030852801d002c0c440000b4000c640481400114840d60100280b82040c40d0b4030410720076007040d40c9082d0074000c0107000025100303200e034129803c441702d00b89202e03424640441e94400ba101c00100400c0200084d080074003a03188040b03e5801990299070341c0304491400c05004440d41294103031740700358450994120072041d0341c18150a450800c08100403074082030b502d9081c0d00a11000200030750014400f20115022200f21001041d00d12055041c80c1000300c03e031320010b84185100c0d00540c0420000c10344984208800c441a20b410a046e0285180c22503000350302105035650056210310308201e80354032030b000a500a61145000e20b5482c0b51080070101c032400b020b40200c0859050080c01c1007c40c0315441036880c006000c82d06420035058103204000100341284000c5501e0103180700000c14090b0114051040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 285109442 1250 285108192 285108203
    0x209040f0c230d02010210060602010608010e0c0a0603090c031505040308070c0203071517010f03050c010503090309040f020426010c0e0a090906020c0604080901031a0904060e0c1804 80
    0x11989034103812205603059000010315030b54181a54145140107a040f4a9190041c01074400d494214140001920740f00d41003038005d0307915500c1c10030a08409218044007504440050052050303100002005013056103d802c0816072202c44100600503c1d100030740040d680810307a880c20104400000014100c120b4095001c220035a0000b9003850041d507201020790740c000c2c007a114160030024003000c2e00c20710050035404c001c207808200700c0b050840c2c210b16010702515034000001c80d2441c90503500c0c21105851007030410509209100c0101000070035038080d00c400712804901007141380f420900070f0040394480c42ca040c0040c0b6180203041d1305000d00d9080c40142c0c600038484410585010703100340200c4201d0607000040c0140030404402150301000b00c5034800d91000d031078044c2d50000d903840c0c00c0066500b62005030001070304200399038261284501505600400c07900b48400c080000d0301cac030000280054013907926904201e0440c1014003800c420500d00904d00c3c0e330102814030880409007000c41d0200c7d82c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 285110692 1250 285109442 285109463
    0x50705011202092d0607051e030403080f0a05070206030703050601031406030c091f08070611010c050307500c0d35090c0a06050a1404030209040f 64
    0x9500410b80201e40c100b86015104591602040e82018009075141c003c04040010444a0210a584810040051038001c1c2c009114030740106201451541d107064070142c6a1b0700400c0300700b00055242c81a02d00c0002440d21258841460150a88080c4103000340298000d1b0004100124141c00d0744c0600e00a11003079a04200c0716107141742502c40420103441881e856070003032404010604d080403015922642900501404442015a450811074103170030210b4a41c0044070184001640030000441808200c4c00a100d0303460000381c0a4600d1001070a4041001806050404114045c4841d00b01c2d88200b0400c2c101c0c0c01842c203444241840f00c603c040d10342c0103100b15600b140200c4580c141c580030301e02c040260440054445e42036603101c81c2443c4c9402008490601d540c400c60ba4007005817010491300725900a2443c0218615042c030124800c02c03031240000a405200b400d6006055524000560908007006c202c0c040e805900303805150300c0258000d0401d01080204800c8400b001403681c4255400316 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 285111942 1250 285110692 285110717
    0x60305060d0803150a050d0303020408120301030f02121510150203070503030a240e06011b0b010303110f0a08070b010522180b101a07020901090507110a05070501 71
    0x501d04440001621004080c0701207502c500b100351008811540061402440c40d6895022038801c1c01005000d4001c00c2c0d01040400c01c4030018030018180701d00e0761104a1035036055039a0706202d1802c1c004040d01402c03080c20116840e40e810001001155411003440701c0d60703c0d04e001132004400c00da0103099001c41e800102441864000002c3d9134505a11002560031561250812401000c4240c070240110524414042c0804188241080a8001801d40348a14900000051324281c40f6203000c83d1f81c580a450720f00c022500707007110241969450320300305140604098040d0720340070035103081c009540039407602c180c2000301c0d0034010704079903114900c5202c1684c2d07504100440008030640101c00e6101c2e200c900440c2c540c40340c0c041e5000c4640030b014082c3d40c3e482603d40310711201041312003810301d495000003801082416000100504401602c2501d440f64039404242a01418450903100301c0c0c484000c2060b2134000d54418211010b440d0441d01045034500300300e0356503441d0b0310816002c42c1600c40c045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 285113192 1250 285111942 285111949
    0xb09100f0f2303010b0612010303031a1309020a08010c05121e011401021f0b0a05041b0315031a07081006051602010909061401020105010806250e03010c050406030506 73
    0x5001c644440c034208450407456910a0155020342d03900307030380c155070750b000742030807551020044c00002c03c401140d619650704601d009421a083c800c0254103c141801304101c12f60345880140980410204c004510301c01e40d44041203050b40c2c07580108000e9424003008900d855440405000006020300070300006450744c03640c02c0324000d41c15204107a0200d0340001840300700100c1621228515045c8122180c03561400710031800c204202c9081ca01c4603440d0a5921400e1811403064405084c3c100d03801c0102d01e40032078000100d114038000300024151640034a0f0101180d01008900640c0c00c4000d4500c026054454100c800c002214000003050910340450403181006108100ba14516140c162820200240d00090031414020032410800741641c0441d520803503029440003000d4000143d2a4400d084002a0a54405802001042e4408820071407a61818a414091000c14203002c100d107454140702281c0e03540390803d240d038041d030030200664001c0f58048000d0040ba4800c0d0360800c20f03030b240d42040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 285114442 1250 285113192 285113219
    0xa170727030203070e0c0c030d050a0e15060f0a09020a03020307170403020c1509120705120109170a0504090203240102060603060703020c0f0109150b0607170d0b09100f 74
    0x10390958024413060011641c0c030010240c10482104810707003000d01c001c00c80c5185510941c0c2095040c0c0c0c481c4207004182d8440e0250314504110640038002400c0703846844c204d40c000046c6072a10910541207108000e445060446015107000c6a09564603050500060040e601c01e83c0c100f000100383c174002c107003840d02805010303005541c0356003d0820030020b4010001544131150b0f84400007003041007444107980d03c19031401c808014400141403e9440c140c10040c03600e82002e40c548913070f41070015000024bc005403407001d285100e9114a43c480c1000c80b021911401aa0800e00800c0e10000c01d200b10100301c800711f03c8518007402d5588030743ea10494012a01c42000341e03211501544402d010400c03503800380d005040350f030749520121a03034440740041603400d680420350107994240c0710000ac005c090f42c56004211100c4416030b903240c5449804d44e07410005131100c0d00201e003480800300342c1c500e0b60110b42e00000c0145000800c402101e09207d0355500304601c6034481ca500c011240d400000744090020b14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 285115692 1250 285114442 285114449
    0x90112030f05030403030b041410080312010b0a020102090a030812010501140703110f0a0308010e06060a12090206040e04060c030b010f0c060b0607050102040305061f050d06020a170727 81
    0x101d981c8695140c0100340e031940c002030411800d05440c0e040c3c80100b61968840c2d141c1c820f00390950b00c0310300c1c20007425074440913015800514464004000c5802c040241450042c11644e005100b640d66512000c0100d0090045444455003c011071200005110046003d80983d40f03214070008000d980e101c4c0151000c0342c1710f2148001c07092050105c000400d001e08081d05980800000360340304100c0220010741040e401c2641180400c100300c0040c08a040019581603100c10160f92041c0b81801901000e441010503140c40304e0b40e03945484e0203070b0854030b5403001d45004040c0c00407842c40c0c0f810680790440141101c0740b52200024546414403050758800c041d0300704594219140d004100505403203003405001030f44061900400104071000004d8001d10050009501030f1b0041d0502e41040c0c0c2c111003010080b24284914005926000d00003559000c01c000041944201d0040c2d4950352640c0549000600060101c000706030f003020800c00035000041104104e5011030121041c80c03070f021240580380310320302 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 285116942 1250 285115692 285115697
    0x7030f0207030f03150906060c03080a0e061305030f0d1a01020a1e030201020c060a020a110609100c0c330e03041a12040309030c0504050405100c1107080c09011203 72
    0x40700c02c0a079802503000300711020140216a200c5911131901c46c00340c40b20703580408001400c41650905160380050825001010050b049c8481e41040300640d41c2e03250b0140c2060700210712540c0320810800b04008032018200301e900a541c480c4061511480100204c1111620308000c0e404034220940c4046101c199861303009602a0b840300002000040400d01c030501101035650800646410312010800a0f200b41800480584c0d00c0c040080d00030581000c50b210822168000700521411800210340c52545001600e8005844415084100d401e1a12418050641e00442d41c0b20300800c44101042c500c003a02e000c80075900d250000540008880e400c84002ea0241c2040c482804a02000710020300101c0d14548a981807d41741888100f4805068034202d01207079254004004001e6440490b000030581107e08204070300c2c054440c3d5454001085a64100c982d840102a00c16801402006e2604254804544400b070301e8031650b03940c42a240d40240c2c480c60034140000745c1c000940c0080002e01d40d159 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 285118192 1250 285116942 285116957
    0x308070813140111040306090537060902100210051501051206010c0206030f040b18031207050d0c030203150a03031719020a02031903020406170405010f1407030f020703 74
    0x1902c408218411500c40ca59041d5281c1c402086801c00440c0030f0000785000e000300150601c6a0300d0018601140800383e0810012801c90140c1020074548102503411032108a0b1003042c07025103440030080c42d459100a5200c03c081d81d8030a146580003600071403030f44ca40301040185883d0451509800800f282d820b6000400400482d2032a07143d49a216800c402d060421504111040d4006001608119619070101d207202040105022400044680200d54113008071141d8444a18031900e0344070310084085011004400301d50500d100d10100c9050b289414410444c4200891005000e944183da00305031108244e06101072a1510101d04c0c01280e5160311590924803800c41c10100640d00241040f8043e0402d100303002c880a9103000038086c0c95216400f9555903007e20004490586200c502001054418801030210b0303600180303581d6803221820000d924079075562034410b001d020481d208001d00c50511008220240075001c566009003d241c80502600340180c8014089000b03c00b40640007175042d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 285119442 1250 285118192 285118231
    0x90a05120304050d06020409180501060f05090f061503100303112e09050a060204030201021e030a1409030a0b0613200d29041113060305060a0f06080403080708 70
    0x1808075903090505c188000340c182983ca080c8081150201a61003640781144070701d080800c81c00b0b226907030103072050134030640a40c0e0810020946d081d0004210800a8104401250b92a074a003000e40244e01003840c8010360700d1400c42a100b0b01c01c40b0324070007140441c1081921002c07011020405442c00301d01500125000314001c40e00d05036000181490810b0782d9510302d403080c04184148110002d040c0141c0025070350b540707544002490a180c2032025500c034002d00c011500000008400c940e401c0d42c9a01d0304010008448a4110403486100a2030f603062240c2220345c01000800300c50148070f1401160700c818612800038001081d1030000300c1d4038128000d07038201012a200711360040c05442c09005400951100c00b406040700c1c421a0603181226001c40c1e200143c001d280074000c407074000001c040610305010108034402c4d40d680c5030b4040e420500da11280010540d4850724001303002049140b13004030350242d40c3c84010748040000e4400350000382d0305000140c800390048000328040c5000462403000f1945 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 285120692 1250 285119442 285119449
    0x90f0306010b0906031f08070609090e0a02010315210606050d0b070311070602030723040e06101e0c2001020615061c05061e100302070c030803010308090a0512030405 73
    0x100402c6c441820080c5a4042c4013161801c280d100070f00300d50b0004210550620b0009402e29505034421460203040800d6141d8080001c902c0c2c4007401d034203080c04a07108100e80c07410f40080700c2e0358115000548500d0702c101e100044031041c81e1040f5001d0041041116154000e110901a00f40c3d80a00400d00000c041000d09202e940b08081034038080d00c280f42440720750f503150820782c2c1c003c1d16400001900c422103110310045d921388410204d00c110344010310305071609040100c81c581c0142110303c6030349000c0440d0031a42c0100320707150b01d02d103401c050300c1c01030040c400300074006250352882610b044607008081407408240d0300e0003014261058000b050955160071440544111104295070002020721500c2088000b00c3c2105901440d2400e0205840c0b41c0003080c01309005aa0715280000b04950350599456101d2294641c003101c1140760240c1d03101180e08101ea640c0d0f403140e00007080c5000010001040c0320980c0044c08a001d41145c170705001c5030766001041011503c9000c1e19031590401c007c00c002d60701c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 285121942 1250 285120692 285120697
    0xb070203071a250c1208061018051c170405060409020309010f0c11190314130503030d05150a08060c1c11031b0406120f150b090f0306010b0906 63
    0x441e102c14400b414541d18002c0419220404a00c00100b40014880810420202038083c081417003031804810901e0410009106c6500701400d02c018040b0041c000c0409985504c02d00340502030190141d0103440d2610203042d8140a100801d5a0701e90a20b51380c0319003440c0040840d403c4803130080c601d82c00c01d07091040a800039440a0580072056503915401042000c3c1401640b003101015140c0c0306541501c4a042400d03c3c0510800005c2c68010100041c0040d80111940041c601e10040072034480e02c08887c50740c05c880710b0307030402c90381848040b0340d00c680300d2100c0d00850310408031a40142c070503994043c02d006a058180c00349828903044440081c101d122031002a04003440e503003010b42d55110032040001d00711119210011748005c4000100000207900b003400340b4482d40e000352a24902840d080d4021700801c106501003001c40e495141a84c0c009610707400600d61002e04012440100d540d0f40c1200c0c0565010003040e500034160182005028940824214101d8030b43c0740c07202e8540041c440400c94140d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 285123192 1250 285121942 285121951
    0x110d0f081b091c021801060e01030b240f040b0d0e0c0d170702040608010203070e03161809050f0109140109050703020409020a0e0a0e06150d0f050102040b07030c0b070203071a 77
    0x100f1480588000b5a9520300441d44c0701d001d107043d9821a5041050007441d60281c120303c6c0313040c1810003580e2212529004a0240006d101803140194100c1904943c0e0f0184200e1460880070000030a0108510200348028401a80c1500040100139034030162542c4800c0d5103da01a1b100035164010404645d902460320001c200e108a072503c2c0c5549680000d08039899a00300320481d0f9800700400c0303406030304160128080308040b0001c0c4125140803803860501c10082c094640f100d1210704086030783c030809800211003151310405a40311011041d03451030090400c0082618003145c41e030800d480a00c2d0620038140c640b6001006014aa8255000d100140001450803030704034040950000300c007101940342c0d0b0b020300d416440100c2c07490305030480c1a281030005410070300910916090000aa6112181502c0d82c9070f20405041c196222420014024007880e13110083c6218005205010160311002d08070101c0e2082510709000e880d450412a5a8041c0303003402020146816181d6001c0c500c581462a8070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 285124442 1250 285123192 285123229
    0xf030204080102040b0903010c2f0c041b090b0c0304171203070903030e031c0e010909050c042c04350403020f041407050703110d0f081b09 61
    0x101552004501e08913400340c2d0040e031605401007001c0d405484d003070058884500152405118004c0581c41c4c014020201e6440e50180c411121091094814240511070700e40000030002c02050040b08940daa0100381101e1a100107401c0880c08120080b01005070740c0c02030400030043d0705017401c00c03001c0b00c800c3c421034511907094032460520fa0300208103040298810041950b880c0c40542c0346240162541103c02520391080d0090520321340380d841d03a014207241700040d0f171404001c8400820010381d441c075070541259080c01e042500300001c080582d80140212080b18100315a1030007450741040c000703074807195a10b0a86d50340d0700c00b0074089203a8100c8981102c48011400d4203c41d640070320000b03603007000030b0a03691108010408205501d032600b11a002c00b101901c040c40034800c10b07440c0190340000102094140400441c0c503500f4584510710300340c900303007444045843d0f0051101001c4c1c9042111000d58001491200c00500c00860242d946603078014940c280c1c03410060f80800300081a006840003003c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 285125692 1250 285124442 285124447
    0xb1f06031a040e07050102100207030e010e0d0c06091e0305330106080a0b09060f09090703050f010219140703200a031709010c0909050406020417100c080402100f0302 73
    0x101d564075031080e2441003e54000401500c0e00e00f03000a400c04480c0514080024414041540866001809585001024070340740c2c0d0b002c403c0a00055a10308071b00c8007d80013550503038010038119044011001039545100d202d40e203102e03c881c0240c50b448404d020082603500200300c2a017041181e0b03100b40c0d00c04805119201c000003007078000c0c110100c2099004100051070281800b040350051f10070060107a1064a100c4100d02c3d040001c55201541410300b1030144080c0d000250046505100300c0000d03581c86810303a1020ba0080342d00d2800b0750400e000c44602200c12810040e4080e01801c3c0542d4030b91400c2400506160b2152070a445402180651000d007138215000868215400c2c480c1e4074100b4820b449061075584100d00041ca9400000c0050146078548100e21081c0c0ba08241228101d072036603400070400b80d45a10344040039000341d81c8200c03480c00600b210070f21072030300219516801d800c03114010800c015502408030384030401614082c0d00042034000700d12045201e42504e07500c55042742030161 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 285126942 1250 285125692 285125741
    0x705031801080a06080304180e0a030e210312150301020d0501030b0108010507140f1201080d0908070f0b07050a06021201080c04061d1005060c030a020c04050705250204090803040b1f0603 82
    0x12b0070007001d490208d00088580c81500c10700d02e80b12000a551002e00900003101c0c04010b9405581d0384151144d54542050500c001024000281811003081c0340240c02551a040c80b070547e08080e04007804200c0b0100711100022511400501c07075184507120381d603141c110840b00c50203205e0f4598071088070b500000c403080045100f040694018180284417800060511a26441c4028044810758000c002c641d0040a01000704c1c00c001403006c81070f51b070b0256542d607441303085141091a100310003074003c01140c004154000364002600b081812a66041c0540b07207040565002c01085946501031440303661034962903440c0c00c803002c00c5920351025600201c400340d2620380d4002411174103c203555054907440001d000c1003c46c0d05100003803c01d001514140200d007031518001d0050300964251032071001c59900300031034002c0e20f030030f01c6900720340c014004120030070541c180044580c3c402c07507041c1c4a1030351700d0020403000054082c140f01903244e0024074017071103400c0c89000c4024089003080100c0c0d0b07801c04d00da402e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 285128192 1250 285126942 285126971
    0x170a12020403080403021c0c1a040f060e01110f060a050a021201031101120911010c080f040f0f0602032d04030204141f1a0901050705031801080a0608030418 69
    0x90001d0741c050300c00f16484900e148100100891081c110011001c001002d846c0020f11108070101502d00148000480c092695030000160207a039200d40700300740241000050b01600552110888002a610700e4a070807031544c2c1e07282e03451244400095840e800400002d0920180c0d601c495004400c60744094a402a0031129180c104000e800035141112000001d500641c1c00001100a00700313220014004641a5152441900d40034000710781484840c080d0141007100c24000c656090314000e00098a961f1103006075082d0712081e004a0410417010780010400c54000402e072070b440ca603256000c1c212080743e00c1406110407090012080400e00074800800141d0307550141541c80c54501f0603480c06407034a202a030001c0c40e41c01c1000d038001c02c4c4a81c0e09102e0300704041a42c1c0c001101c484100713995210041e004946a114442d800f030500d020229904103200032820802c10204001d07038880135151900301c0e4200440340c0703610a101081d442000200000c20a0307805914a250002d180010400d1001c280c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 285129442 1250 285128192 285128197
    0x70f14070f20030a0803220c0f030204060b0405030d0e1f030b19060804031116060215011707030209100302041b030f020a08070c020f060d1401050d170a1202 69
    0x100d80081001d40065229181500480302c0040214020241c3c03010303507103400006200150101540c0710450154204202c0c41d5045001941da021945404e0281c0c1c0d01071561402e0100d020482c071071401d010000130f4031b9207010300351000e4880050182017a00b0001c0002d41d080740c3c0e2000040c1d04040e022010116041103400b4000d11600d2a031800704603c00c012041205c0760f40000311020211025600510071940d108161075882130f41402c10580802d581070000e480c002d1503e145424107d041140464620b031b01141006e000c2c03d04442004150340c8508910b00007c096500203801c0e940309142c10405890035620f00d58118040702c1c030b025102500c0343c001c141079032119031341e80f100050b42000c8030141a900d841001d6201141d0a0308500304074078900e004010244c0a00340b8402c00c403005066a06540d2441410607400380003e044c40da440035a07098200c05010011241110742c001e900000880c0e0420301808003409038411100e4a40202c1a80720340c800741c00c110001c00800c014881c1058560009100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 285130692 1250 285129442 285129473
    0x7080c1e090a0e0f011d010c021905030906030106111e120a03020405210607020601030f0807230714120703080c03070f0c030204050a092001050904021206090906070f1407 75
    0x4c559900c2c5641c5e0700441080041400d4200c0e072524081d0301019901007098a4900c00f02c1004082b0418079061442c81c600902100da98070480000002459542001c0c0c00c5a040d0200826035410299518461401450360a07684c4c0c45900b01000b50207541d003041001b050301c81c056080c01400c003500c4a012036980c3c00820b2040070340746014111030421440c10440554442914801004030b5810f503503610b00700c040d40042c0104440760201c1d00d101000601e076040c08038064031501101e11048140e03400f035650441403050407121500210700b2031719410140c2510034145103800040035810302d180e450410951000c04581c0807400203204d500002a080858864031074010026000c107103045004000403600080c0101c42500c1c580401400010007040c0d91214144403101d65081d80d0803484016600c03441000c00725a4003e00c005120b800c15011660028007030b013401e455280d0300e580c0340e449d0700c0da88101c00d80e44c500114060481c0c84000610031980d0401c140c40080d00176041000340d85d11111056075160 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 285131942 1250 285130692 285130723
    0x12100603080a1425030e04020307210b09130507050a080a0c05040b011205060402090a031b0605030606031605040308031e0a020a09030f02041404030207080c1e090a0e 73
    0x5000c940769a404550320100001c0c8010300c2d0f10b0300b568119005810201d01075562442e5441e20304130000d0500031030717030f05c207082c203015005542e2490803800041c40c0145115000000c024030710a81d106000e00c134440c0303455581340580b1403d90703912646604034441d200980200c0b000d00c6081c001080035100c4129400003009410011300e0f1144131131038220400c248a400c10740c0180e00e0034030b111459030390081c1d0710403016680b2100020b090f01e885011030080c0c440c035141c6940110700d28000204000c000881e10a0801c1803032000180781d0303115032b4101ca45220a83d42907902c000144081942d8241c035050b0001000101c3c24440d24040c0d030780d0340c0d8500680003100c0c0145401448454074200304042000164000d8903000c0440c90700c049400c0c003404050f400d000160004010520200464645600c000381e02c50300d80c6030f1441680350910300290f1346d154600808a043c007454048a10504280e440c501d0718480e98101d44181000002c00e111804900a14550400d61a0700d899042740ba402c1c4000300c00c080180c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 285133192 1250 285131942 285131947
    0x3040909050d020d140f03041406090d1d012a1b051c03021c03060b04090204050a170c0105090409150b030c01090b301603050f0f04021210060308 64
    0xb0380103410720403c0c0074440180711060400d030859543d4507080301c9010b001d42c14003a48a40b04e03800c00d5007041641d818040030300d21480050040180303000903803020490040d601e03003500541200300034101d2071202c04400d0200b40710304904126044401c040801c1000d00b92554281440700703072100400d00e0700c840c26000012090340000e2001c0e05026005000d8050031014007440342c1d8043e60001c2d541d0701c0f103101c040d0201108507604804e04bc030a4105400820101d10003a4846441e00800002036000748070300f81c030503021007400040c030b42d451803ca1101e800803d80039250000c56200150703042c1c0e0101c1001c0754801d0742c4040100c00103007803070302180b18250034100024034080f01005142c82c004c64090402e05200b10139004204508100e803c03200d0185242511a18000b6001803c1c0340d000741c01c10b004030b0400000d86c20002500a03149445500301c030195014072003a21341d6144100c800e00c0903240c82040c1d07410600020050304140794070981c041c038a00201d5603800c8001c1c1c2d0307000072207640f0b801c11034041d00d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 285134442 1250 285133192 285133213
    0x320060f101d041b0b03010914011a0706091703090703060c0201020f04031101170c0d0b010905010c0b0705041205060603010507321e0310080c210304090905 69
    0x8803400a01410040e28030258060740c1410b01102e2680007040200002e4041103540c0c0400c185640000080820101c06074981d40c6401c01030010300407044001d101c44d15201c0000440c031116000c1c80800d0103151701c2e407614142d4a6120003000d80a404015a141d410f4501d4090f81600700c0001540704042d40382c00380c000c041c218600388069030307102c00d0300c4000c5a0050102c01e00800310074085500b200d91000600d42d401d1288c0005032056140e804049440c0070f0f0080420985200c0179008060020701807508020341c000e11030066030f40c40400e000b00350004225001c0c19000400410b14a42c0100c030714200035003400c0d82e07007e810200a0708030b2000c480c581c00071001e00049042c04d01405401035600e0900608000c3c1462600904242843c0c2111030000529036680c0340300c0f141d000300c0b010704841400c2403000ca0104801c01c2995441a29140c6156107038900003d040400840c5604201200900380c0a0100d50f11000900d00c444400c02d02c50180002c100c0000c15403494860248002c0c491805484400072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 285135692 1250 285134442 285134461
    0x8131109090f0d05030c041205010b06210702150a0f09060f02131a090607060207050304030f2102100209150d060e180604060e03070204141f0803070320060f 69
    0x440c3d10801840010b0080c04500f09080065400355940c040003d5000c62542c1041409000000308198214500107194080d41d49040448099144a00c91200b03a503112074500b260750b68103072000b40001d1400d40f801708031400c442c1e80280807119280280400c1d00c0f00710380c585808881ca003442000e0070300e41c00a4a101c0d0003501c00d08000040c5000180061419050f000b004c880d8810030625a100321400113445080120650523915450b030081c0c11643c90f030b5107a2601580000c0900c0d811340780081d00d00311410b0341c1d0128207845440020030f40d0141002e400821a01c2010b0340004120640c401c1604105841c52001d04015258025940b40085400c1c0e1501700419a464006042518110010044603890a100007a115001644000001800c400c01030b0001c0c00c5014050000b94401e0408030680070300400f42094500500105490286034130101c2e006a10360308240c468074519401c1400040042400b03103000300d2040140036420003030700308c0c4403a4041c203000003250460010b00c0001d05100700d410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 285136942 1250 285135692 285135703
    0x82716050f0607060c0c06110406111605120705130203150334090f06051507021e121002071e03050d09060608010c050c010506090708131109090f 64
    0x16998200c2200010000c600ba600c2400300162900c0d40360564002d817584122901990903400c03d43c10004a43c4041008026600c940300c0e61001481103106000c038201d010400031040b2500c260707944401450310301808074101000c458001c03540100c450028040e160f01a4007210001280b00040c0e59141a248207a88820941039483c043c0d40951400d503001009070300c007003684940c02018034079011400c0b1400d003d403d1a9030800030f0180c0c24a1009903c10b0030036003102007955021a021402c090840181208a000749071000e03510600b503806030a2500074003421080751900140030010b2141c2c44002062504c01c910501081c1141e002540358248115401311684000b0f4a003640c2e5174050194a005100d401512840520a90f81d00c41034020043d00368490402480e4510080c40001c50152018140303800c02c44007003000b542080c0c000340d89460801300941c407901413501d44010320303190f0351014000011003410450340302c000130042c3e107203179550345404501c03880545000b0002281d51016150914 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 285138192 1250 285136942 285136949
    0x4020f0a02071511061503010603021003090605061e090a0b0607050708060a231003050d2309090106050d060504090819020601080c0d03030f020d0e120415082716 71
    0x440d4007102d280c4c5440c4003054150300048a00882034201034140002801444680d00c000d51104010120846079605500851807060080d20100065035030b4809022141e070140c100114040c00d41c07070b031a44007840d10342540754012902840001d940040140461000d60000700195915849400f0402c802501041815405825402e052005091a42103600c02c95500080840c0142403132000584900404141200543e00070301151441046884090021074800c0c090507003144030290a40c014030306080442c1c040b0000984103126aa2a014040b12940c0026818121058507694006440d5507a4081c0d204050300460b06655244401100600c079030480c030030900305541054004018010011880f42d546007003e0b920358005400c1072801314000d04200652006041c4003250340f190003c102c1e07010381d40000084c0100d41000805880e185c000380514401e052000400e00d1001d60319a2041c00800e81100000d18681d02c150303842c100c0d80c1100d030340454119241d980b081d02c0350555170100c1d440d03e070001e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 285139442 1250 285138192 285138197
    0x606060906220f05031b03070e06010c0c0905090d05040506031501230a1707230c031b070f082a09070e0f0a03081209070503030301030807020405010605180f04020f0a020715 76
    0x20002c4000842d440c0c1c050703880b441421000200016079a2f034040c80c000400d590344455945a0f040c2c54214030b40c0100410744000440d485140003d0b00d5090140c2c0c211415940c0040c8a541180e5901c84000382c1440c2d840c1070b85040010380e224603204440c0601d182c4041080102001e030725240c2d1140e0040105080000da40214000c50b014040384036080b0082c0b0741c140340030940110001903003c5100805205051640301a840001005800020030a01c41c4150850070419600745c1659070b40c210030114141e00030b1034095040031080c034a500c640c22001d40403099101507003000b204901000035030f032804211a0030001c03400b4210f02082520301010040c00c034001c2103401740703a12070440c0c40d68001d500440755242c03030306400440461006002081080000c1400a046075641c0da10782c036240c203113504241d1089009034103040000c51114041d909884c504038084504440c42e129203020000501094440740ea001a1b003044181405a040c1c0c00600340c1c50b141b600103000841c640080c1a482402c02640c1608 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 285140692 1250 285139442 285139483
    0xd0e030a0806030d17060d11120105060a0b0403120c02041506050d11190302030411040c021e0c010e01030902040b0901090b1c0506061908030712020f0606060906220f0503 75
    0xb49400c80360446d004141036030240b501800b41e142102c00306500c2c0410700e500142880703581c200340205403c400c1c801c800c03c2c5d500400103995005d10301e15030300a80c00010700354800b00c41c03816182c178810780c043e100d5640001c00203d480c4030502c6030000322401c02d0f0048800100002201c1040381c01c98040c050740d0000c124662032401581185040b0880c000402c1c1404164000010074140420700303213441040744000740308110100c101d0202a40e0745c07007d003180c0f000245885001d41105440407030700e80301c14201a10f90219511400004400401c030000b41264401c0e41d9081480d9a6102d40c20401d0292414a000246586009007001660b01c40780780d082d160400ea41403080f0000d00045000b85d00031005a414040129490324078410908090704060040d120108088085c090440614100b9031100d800361450b504030030034050780b0707001c0c1203810703d4215200304211285d609010b0001c18001084a4420120030140710502c1400341700c0358800c80340240c4c20b44041c03069240502c034580744004100c84018 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 285141942 1250 285140692 285140717
    0x10509090a030e1309060212040519050c09131202070602010e0109020604170a0f0602070308060306092104080304181b080c0a11010c1d060703140d0e030a0806030d 72
    0x504100711040010300560080900d8100c13400d0b190021559168420000c5d515414040c00030281540c00301ca0941d642d00c01c00c01c1c601038503078420300c091210700d410601500c0d040b0100c100b40452150040e01c10242c161751407010101040b03c8050000c454891343d406402d02d2454480c000b802d5501080072005030340d240044030001a921074046500726500609035480c0300c000407200318140f00e04118040c04200d107412951041205070360080000358441d031a981555210385080c155070314421108514141d01401540e41036021040420310500800164140350030780381c1041d5820354106500c5079005407103510b1351101183c1031740261540d18000301803d01411022150050203148094030200c490500000c03184c001c103200c1c902201d5400310303100080c42211315003603000b80454035260707111210701d140d484101002d1404000329001582c0682e10304103099050f03285900290302c0404090300c2d407645d9024521003807809001030010000240c55800940c5058003e150400b50108800003c000c4440050b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 285143192 1250 285141942 285141947
    0x17011a040509070201060803030405030915041d27070f061701030f02030c0d0308190e0c040518070308040609050102070506040611160f0302010e09131704050a0905010509090a03 78
    0x450841d601115205216115024280d00404198005810a001c0001080300344000080281080041076560b0020310a0301c0b00e403c184c601950062190444100c2d4100090400710765140350401a801c40c2c40085948084540c8005011001c0d6107546401000d4100501303074400300d20000418290070301d90302d10304d41c6600070454128140401490400d1f040c0e603e000b507440070000c807035003920060254120165981070243c410901190071060103040282143c01c40041401044054400d0700b00502948059008201c064800148501d05c017524420300800c00035001c100d00070086028202e160b9556081001c0100300d4607080d0059810b66104910401a13a01d0744000c803011039510340f030300e007440a0809120314100311000000c8010040309604c00304200c80d00004080441c1d00c01d89820175282c4030f030400e10203810011221002031644004500d0003140c40051145022440860b58510f4aa10f410000f40652142d030800d010480c1e0b43c1005004a0500390300c490b400070703400d400410800c40180d400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 285144442 1250 285143192 285143197
    0x3060a020a1709030f030f2512090f0b010e042a0501120b0d08041d0c0d0c0c05010906060608090609070311030a06021b010606050c0c040b0d050d17011a 67
    0x100c8201c2c0e41c0000c000359480364244141c404084101002d1580c03418194601e0211a506440c1ca04031400b522407424200407488111007040c20301612060004507807503481c14014262140144c400c4c2103441c100c080014408400313103000e03100c8083d51020505107810082e01c180e01d4213442da202019420a101c80317414042d45042c00301ca00c240b030410b41000c9024039002c0074205102820343c018013202c084104000200b00a0008c0c1d8156402d01103c656412002400340602581c800c41480000c200c00010f49055422050500e001307410005201003199071510b084800030b01080c0c1d00c3c80e90390001401a50390200049400c810001d0060040d03082c9901110b44035215844020403203a86c0d0301c0d1405080c1c905000c201111600720008540b506c0c01412440110600c100d00a001546000800320300140a14252400203442d000102105404001404010100f100c00c0d00d82c02000901c135100020001c021050242c200d99440071741000d4400310808a112044c0c12221070140d4100101d401d850003a800e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 285145692 1250 285144442 285144467
    0x60b03090303431b0c03060507031104090c020a12181a0a0806030c1309050c03010204080a060e072402060f0601020316140303010e010e070e090c090f03030d0b03060a020a 75
    0x200f404612044220555400e0200c4515503030340c25241340b0100c2400000c62084048070b01410040c88650303070700b400840489580c5da00c20001301c0001c2c0000d22002280fa4480d4031511120300499807407005603141c04419940100c07000000035101a20b0100c040c05003084c10700285104001c200185031320304a00e07401405141051400c000300800040c80c9907504010722a031500003e007503048040c49845041010f1b040c08007041e0f54a100c0c1c00c05807101401c1c1442140c044520400103484201032660f50b41c0090888803454101500c25428045003440c0482c01b10501c0c1300d054a00d10008080b0500c0107030400900030f0800d802190400100105a40c0100031605020141c242c810a070322850302e0f240450702c440d0344000d9210312000c0000700c1c4964204c0c0401f8107131064140d00b0006036460110480307045180030b8a250b00205207001056400e4008005400903803001004803580301c0b40100800c0c91a000445841482d58981400c4891350038288804ca8201e4003504c015071421342d00d184043c00c5c1c1042d200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 285146942 1250 285145692 285145801
    0x3050301060e1f03090224161a100311090601091a04030b07091a030412050a0c05010f0c1d0303030411060f0a020c0a08010c0f05030901060b03090303 66
    0x420000103640c030b42c600301d112000389a0124602c3c1c5002c1600030010620001d04074052502030580d600300c03154100704a103445030f00c040507034500041c1001001940420143c111640200440103054407034510001c03034401c4908005603501540303142010000c54804460303a500412845060111590344000300c84203503440d00d1018034200740d0312511004144142d0740046c01032508035050080346079001c1c0c0c50320211940d645d400708040d005000f41000b24030055400502c80400c08600030b1000d40510041e08154209041035042000f06455050070740d000d03541d210079169560402031040030740084810201481c02c81d00134030b14628110110346e45e0700c00900054182007407841b141034266514800c40340284d030002516a12504804806541c03080307041c24651244000c01008a8511014440c3d804905415592003140c0c42003240240d80c50792020785100c070b040d52035200c0800d9180d159801075003c1c3c030f8001c0041d642c0c1d14144450405940d54600d94030490504d5071710503000849018100b21a00720f224 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 285148192 1250 285146942 285146957
    0x51902100f0f030e030706090f170406051602041b090f0828060209061309061406030f060112060f080606010f08011406120414100501050d0b041505160e0109030305030106 75
    0x5a4140317245000340e40000b44035a041ca2042400c00a1204242c41c0051090703113213054140b0305100c04800c600480c09184001401408101d500c0c4100000a070140c1e8005040000e9031020340742d003500b01c4a00200c0003c0403401c0d0b800108003a48003410b110300240944000340031121901c00d0004070415041034005a900c04042512040c41100d0f0f04503852210020407290f43d48039005c0203030010100500c122842a03140110009818040071110a1204030080840b07240d6500d4001c0282400700207010035042181070340f82124069043d102c2c8a000d41001203607050483e2a2000181c80c041c0d0082c42c050400c00354070044604030b038000300c9031ba0658000360040a050240c040105e0380c1c07401041d80b50303040550510113200030b005034040c22080c1d80b00703e501900c0d15111340428031030540742c00707210345500120901e0001001c240c0284050350014401d00750510312442029411098030700c15554a56254090082036800e030382c0240c400c443d00142800c280020a285407400b8206020502c20141030000d030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 285149442 1250 285148192 285148211
    0x506010e030c10140d0504120201060b03011206090302010e0f0102091203090105190309060f060801180b06010f170411030f010504171b100209041109030604060c0903051902100f0f03 80
    0x4c0100340d5201c1808008100264a4079080003203007000d03550901d0015500c0c1000210340d0503222421039058a46110034088101c1c0c444c3d0380c0400601c601001601107540c1c0b04a11481520244240d0f2000c1420b28005600c60fa152800c00005408003000908582c0c0b080082c010301c0d0340c01a09807281c82402004007801004418010b030302800500d4402480c007440c04070111410724042d440350080e50314074002000b60310300701d10102441c00d204c0c81c00540104c0030303c00050b03010341c407034000301d044040e84d803503c0d15680103500c1d070300240300d01c0503181200d0064685100960700c0c1010021103000c13030710300740003130240742019150b129054126001101d190880000c543d0402c05101e44a0f0010303020344811140b02032065440a0001c1d085124064400c03401c0c8080a5040f01e030820591702c800c1c0d00100034048540300c0743c0e680070003030201080c10024002c00c0343c17000020a50600602985031058881700e040100310703204010300803e2509006040c48500011301c0350f842e61050960040303010324200000c1c001003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 285150692 1250 285149442 285149477
    0x60506031c0203030406180317070504030f140d1707030c051207090830180a080303010816031a060a0f181a010c111903060506010e030c10 61
    0x800041092204054400c1c62504075400001103124901800040008801c5040c060004440c80500a80098982443c0c2d484000e00150501d400030050300300355242c10fa480d035454490804608041e00d0b505103514401d82c080d2000c0c882140340c0c07446031802c0b400c04902c04011041088015046034100342d03662881d602541d008904175401c1a22120000d900ae240800004020825a010340b108074081c3c810260684548038082486108620007080f807841003203000b6040b150031a00c00700e1800b81c0203484814481d1a05070040f0050106940035660301c1d070400860b10720706041e000f810b0129101580c001c1011680d840028000ca6151290600c19911440001011440c2503008460a170006410002d00e443e50411104c1005608030b0307081c46049441000f61144880556a60340031400121145000030b90f44400d1039240c840c0180300d0f0300103058070030968540c3c5045400407144c1c15910341c248080c82d03802071160007020400b01c008208080545001c07588815580500030280283d034040c813401e004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 285151942 1250 285150692 285150703
    0x610050a0909111c060b010813171306081e041e06110d0b030c19060c052404111e01030c09120807020a0602060f060d020303120408091003050f0406050603 68
    0x3c0041c030358444400000764800c804a903500085070301c1494602c03041115405110124400d0310580385142a00c8035545036101803080310700701d10840010800619072041c2004401c24003801c625640c0021500d0003003d1520895044281c00400d0440c40d000c2000280c18820612400300b4241400100b03500580380c400064a0301501c418452800403d80d4172030441c05501041c016501102220042e1404900b80700d80c011100d074403880e0042e051001802201d025054200b400c900c074408a0f08000c40140c60340c0c400100d00701550000c016090217100901809440c803003880c19080f500704d0440104a484007007050075151489040c591210700082d80e15004002e007100800003070020744d0000b59146400d001170b034441c0e1000ca00c1903a003d9404261a031000403807d10550428800aa45440721000c000d001a52058100d0740340c8020861011041c1c10355540d40c0c02140b00e400d125490720444010012094030400a1204261a00040002c0d2082c007001f010740240d000140010142c98a1001c00e0625 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 285153192 1250 285151942 285151973
    0x2160c0305010c090515040509090a0f050c01031b0c02011b1a0106030e030a0905150f0a0305010602100207050a061a060a0e09060a050334030f050610050a0909 70
    0x1460140008180701042d045030801400560b10540c06a86a8041040b442c2c000d0503d03043d4010f0511040c0180c0c01c0c19810705800074407803800c4070404034213550b64580145800b001101e15402c0040d003c121960540940360307011720070280d03050104c515460001d10414550700040d0400c002e591180111000300002413200541140704020007440c0361210000c040310038070407000040c1c901000c4101d0803a000c020707606561610f6585443c42440c0c102003005044d09c080307102c0c0d01391408110040d8603c03000c00003400e100c40aa2004205d66142c400068200b042c00b4406440390b5004201200000b1400300b84512020341c89040065880c60310628031041040e9000c040750041c1000510203681e6410402c2000360030400c41c1d0003501640c4480c24885010010b204e62901940190390922220b8001c405034402010b40c03207078020b40706038144020035100710658400d803100c0b4030601051003400b2f014086940d200ba203e00611403064900404582452802c0c800c0204071591138043d0810020720007d510300c0d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 285154442 1250 285153192 285153203
    0x40312082503020c0c06040b0a0507050102090603150906010f0e04020d091e0b100e0105060337050a0c0504061103090405010e01090c020a020319031412220f060216 72
    0x22042048000d4001d42c0408940201c0c0e200c2c11102141d07500e0106d00b1501502c00038040c0c1030411070209810348003904030b102c0464107035400b0b100c4a11142c8a00300075502c0f505107028403c414500d4003051191203100901050304024420507040c820b01e03001100b400380d0301001d071001a907600002c00c0b128020115072400500607078481401c80c003150014208500040e02842d015000c6484a05071540d1014840c481c60f40600400e4004100e41d16200c80a10740c440040b11280d003601080b0100d0b000001a003054aaa1200007106a606911501e1182c1035202055950070000741034801d40150480c01103104034420001e416406511041041c42a500300582c0684184995619155407681c9000b09000d58507110349411b9110100610010b40c030765416070040c000d050542e514044c51110328604180130717070501c17401001c0140211110307001849004401a1041040c1c00e1402c0360210340054030101c000050f15807010000415846030302441205d07803240005aa41d0f800c510702c48500300300e62601409 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 285155692 1250 285154442 285154501
    0x1407020d0503091e0d0303020901030212090120121807180209011e0903110f130b121c0c060b04020712021603030c0605040212030a0e100504031208 65
    0x100940003000e0140f000c011164601032418648002548030000d551042d40311000f80074490100c0d010b98000e1424200600d00580380085802c42040e400304240c9161a0b07a0303664800c0c0958441d4014041d00445201d005201d1500b08800c400d6212840058242d881c1410b414180e0b5811b61000c104000003020300952000c6401c0c26100c40d080203401204906012980d100c420048289185040c0514084151120610303170b81561180302011854010064208102c104046030954a108981c1070707808074003601090300451403080c8507800403039003010b26466010148043c92190400c0c4010034242807445c0038000210340b820001e020b01406958107421910000c1e04005100c42c0880307440721042ea075008c5030010403e15070407070740005203880082c001410b0040b0100006255412a61b0040d000806c1300b11103240b00c1048a045070b1050a00e1000700f0740f1100300c401c46e41040034458580003c9414442e09003450b50b1502c0c4240040e442c0f40741d04014140c030005040c41005040344c040c07028820b17441c45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 285156942 1250 285155692 285155719
    0x6010b03330f04020703080a0506061308060a060504060324150602060901050c0c0a15110f030a0e210a020a050f2109010e101419080a050c0406140702 66
    0x42400301c214a03164010800d09854415500b054000c440c0c2c5960700d6076403640b1541da11b0004d1401400042d1449a10801c2040448003180322081400054005040584950b08007c6440800c4a9455000ca40204d083c240c003000031640c40035030340c0000e5602c102c1c995440502c0364551401020000500b0000240c007000209419600007030340c9200b0200c2c0700003004981c0b644c889204050051922441407940724009030310004004c0d1101354416844d020001c15030310f58a20319208590400ba020004101002c010824003820601440d2135486082c2302034442107450724401c46109509103040c041d10000011104090751080044059042d081801e80340401582082c860311451001008070f03c012403c151200207181c1c910840340900c07016100c1003d2040c2250074004071801e040311920510040d440c0e4041118295401000c0c484580b0072004110840c0b000081c104a0303024194200c07461603d410014105c0e9a0301c1120180c1d40c6904180214028060344840a8403500c00002c0d00711210501c8807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 285158192 1250 285156942 285157021
    0x30e1009030201050a0603110f0a1505091008070206071b0f0602090a06020106050f120708030307030b010f031503140a05030c060f1803040b090112090506161106010b03 74
    0x300c40d59071007580288815251100064141c6003107000241c08a0441f51030400c0c24070b0440e25410082d40050305200380290745441b01c040b200881d40b0120089440001d80c24440d152545280b855030446051203e9507013840c640003981c0381e0f0020540f6045c008945504808a142c0702c26206e680f6a00012111202e0118034000300607410410b00d40f800307901ca400c4003042240c0103005002c01e861005d868525048188010858406020303c0c0c0c64400340a0303800e01040303012050004500c074811948020440070782c518001001c1d80280f01003502054a000103032140c0d40f50117402d88040341c1d0440d1111b000701c0d007200442801e1100741c03c03001740940300001d0440400e003030101c0c26038450311050521391842d40c3c52200c2c0039905810303d0480c42c01078004001c148410101c160103032100c0780c018905050042414020f903000c94900700d0007690340b0390020381000310088000ca4102d4407018a4074025000305104500159950010b002c0c12884010101c0040c0304002c5000b140c003d110030b5444400c05541500d000d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 285159442 1250 285158192 285158201
    0x2030102180a080a0203061b0903060405030a1e1e140d09020a090527010b060d1a030c060a0e03250f051e0d0f020907090503011a0d02060a030e10 64
    0x9242c0222004040003900140100700d2129554010700600b26690f03888011040c0d0b40301288001900401c18803481d201c13600c0c10456548038610403c006c0d580d50001030400b904c601d8076010b0701c0720400c0c000c0548451440d40491664006880f030070600030281000304060b07840d41b01d60004894004404622620804190740010801e01e0003a203800c4402500c0f0042102610760480da08180100036803400d5036440c4d0850b80320001078104030000a505201c1000041c0d140c2d00001c075a02c0c20315124100b181c5d2480c0000d040340c000c0c2c40114001d1103000741c044080f0340a401814071800c20300056241c0402d00f40c6050003c541001c620b98031188640116980d413000130b1030035020720700d0010a588008038681c1495800740c01003440e00c1c1c990010360702110080041150301c0c103004848065511002c140141c0724952030794000c03900e83c2c585000b20b9081c90705140c00c6500b4100426405610468914000e44440000c0c070601c50b0140e40c01551070b01d8208098010b028007100d80e4401c0e1042850300511500e1a031300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 285160692 1250 285159442 285159487
    0x203160503060d12260609010b07050c0d08030702011410121a040f05070f0e0a09050c030d0818071203050a05130902040e060402090a090b01120509062715060a0302030102 75
    0x4425003240b02c0c459405817110b01c00c40c1e80c07a401001050050000384030384000303402e03118442d100f2103000810030004501d8406002d40c085550280220500041c50740a000e035008503156144061458680310300f040c0441546481100d050159140c519418441c02c44c00c0f0000300d20328032403d20308a040a150040fa045c1d0f07406c509031043c2c0030780040480c40002ea000315000b151000d1190306160340300c03c0103604c010821440d080310b903445088049015518180000c00140c92982c50b40c41d850b2070b18104600c10141e110400c1580f64102c80c0080c014000044071509400b42c052400729140c0324181c405031810321075100031031030000004000060200b0f59800070400e030fa08a400e00210f0b074403038805010036030080c03008490340300100f40e01c18040c8071035543c00802e072814145426040300704400900c604481041c0c0702c204094002004200b458900049043c0000e0403251445070703048001d556464135604402c4014111b1500c80c4040391003562985140c3c0b0203990020001c55842e0043d030b070341c0c0240c40703420070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 285161942 1250 285160692 285160727
    0x90b01030803011d01060503041b1d0105030601050d230c03100917070f02040509100204030506041101182c0f061905010504120204110307050c0c040203160503060d12 73
    0x4800e1300813408600030705040710450744a42e4203580b80c0f46c0d01c142c1d146900c0003402400721900c200001d4150141030a1080100160281801e15414101030504080058202d5030059002c0c2d0302c5c20380010007a4081e02d9480e10301282004d55000d44820725410505220300e120b0307043c8241070002c100804541d0000045c04d21407001c4ca880ba10b52110741020343d0141e00303400350071091850450800341c10160422603005585400761500030300101200000c0b60003036003042d503040d0b1107903081100f000a07d0f000c1006e00082401c002d14480c100842c500c484035490700070b04809084204051181c002d10000f100300550100382800c003203160100b541c60210008540742d6100740303120001401ca080080a2203800d4400680d1800e1070942071142d6080140401c100890700a591482e00c4000e81050340050350083d54241d0301e40c0c0e0b40b40c80807101c1a02c0c046080e41d450f40301d00d00c10800e00c0300740200c03085620618492410911389a644450000340c8135003001001400d002c950690090341f523644040b9003515440f481 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 285163192 1250 285161942 285161969
    0x3030703050709062c1c0308060616021302070209040807050114091b03160f0f06030e0616020118030905120303010f1a04080708100b0909060601050a03090b0103080301 74
    0x300d4221030000e003038825140400c50f9000e00c13805815046000c0c950640814002c01d2500c03140c0c001040c41b0069001e0024094a0803220007800c160f404903803150024000c03280359090589541d80b010500c000c01000038407801c11a03200102d105416016a01119001403c82c00c0c0d0340b0f014105400542c1c0169003c440c507510380186400c1d660503420b8101c6c0607564901c021700030340701203290b004110320700315101c140c0c07502c00c841075007400d00340e40d2011202610380b4441c0030009a103041d00081c40100d20380c0092007030600780303003072a1484600007034500d5000444d00100041035040120681c014050620100182a41c85180c8000e240d0040507980883c0c030300344e400d000380402c02505a5141d0100303006000142510401c100400700b00c5107601d1240c000c4a03c00c0e00d10305a594680f0b18901610740d0302c8000b0301e4211003002c0e403030740754103200c4c070030202070250b80c00d003c140b40c06803480e526102d0040c400b42c1400030218151f5800c1e4400e03400080c0c0c2c0c0750b01103505119542c490800c04429003091240046c02c141e032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 285164442 1250 285163192 285163201
    0x1002031005090403080708100803310b07030807090302120d081e0a090201090e01061e030903020c040c0302160804050301050903040e040305090105070c2d05011b050c040e0303070305 80
    0x90b01c140306a405a844001c1515001021291400060002040078440c100081480c1c5004d2008107440f40819001d4070410142960301803070f06520f81c41091610701d40d850100010005030040300d071700d9540341c504a045030b034071030209840003841a0000f94000b00c400501d5801c0c0000001c81c0d03601e51160341c03181409a170360f80d95600c140b645101c00840702020441c000c9884554550440c000c45841410318110440d00c0703014140e02c80f0000da104400148501000e0103080c3c20301001c00c001000149030a00c0380b003055880196480c103901740340c0c0c3c0c000c1d6650040751000d00d00c680e042e82e030411480c088000038891a42049078281e0050300404c0d1203946802d0119454200000c200c604a481b140d00040403640c2d00d44003a10b0a0b08117a01e0b490502038100500300014520b0000d5801900340c0308892603c0c0203903004459143d0301c03000445c101d2111404000e01040c0e8201910303000c103645980105c004042e079441c020b81004c008801040d085800c008105a80c084044082e5114003155070b01040965113 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 285165692 1250 285164442 285164449
    0x2040b0a050d0221010504050703030806090f0408090109172103010e0c0304030c0506040606080f0607021e0c1003091b0b0315061215012003030109090c03051002031005 74
    0x898420303140e1002c4584400c03401410b02013040c848840e01e0414090011500130301550a4410840b4212199000315030309200b05038100c1c050700d401107400d035503101c0145400f81e400150600090f10282c0b66090104402c82585c3c802c40400c8054203902c4510004000040d01259a072042c0c4640c030748400905003010458803040105a80c125080701c50102c106032200c00e4000620761010700160100506042cbd8003000c90000c00c0514081d510403400011107514141400d4108400181c4030350254018105028100b54009910324846500c0d4180c1c1c0701da121191744003031034090307840d021326040340b0440152a0300c290941d111203000c81c0070355141c0c42c07400d45000764402c4030220380c01030300000842031012800d40e03031620b24040055030018000e80c1c60b0000440c080010344600726400c2d04a60041d0749035000303950b4000c0580380a00c002c001000d1114031080b00b110340300e0205014002c8a25583c800580511000050310001507410070700381c1c0d0202c41c0f03e00705080a0b620890307000c3c90382d00008000142508 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 285166942 1250 285165692 285165709
    0x3270b0a270506221508070201020c07030201030518060c09010806010c050304030308040320010915020412080c070f060e0406120b040209250e0a0f060507030f02030d0507020a02040b 80
    0x70003001061484034200010400700d504900d2540300c604101101d03140c03076a1034081654018010f600e40d41d40070703c00544c00003001c503d0010840c070110390061040380581940016030300c0c292a42401c000c1516a5500e4810000c21141406488948154000c0c000e01c0d40700c4100030024100207030b031028400d646000040d41c290340003001c0103000394410002040880c1c440c1c883c462b08980709140c0070520b6401ca20b440820400350100040310790b5511803141b01007100c0c3c1c030809411b1344049003066003007929003003003100000110000640010400280303503036200401d20402c409003030344035114000242c41f08070042c90904401d02550155180081c0401d42c41130120848864030380c807221261283e5200c1c0c0c24011030341d0000c0c180039803c8401a40c10441c41d110040ca0b560b02e0f200d0759603900305540180c0b0400204540c280d00843c1202c02c0b1150500030103501100704c0700321035003604090b601c040508a0803071841c402d130940e01d00c040d0324010600c207003507030701048054980c0c0c002c407000d1044d03460b00405c108000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 285168192 1250 285166942 285166997
    0x190201020c0601050117043509100810060f050405060703030203240a17010e010203100f0605070b061c0203030d0c1701050303040e040c0e010e0106021614130608011d0f1903270b0a 79
    0x144c4e60755030410dc400e01c103075a445000ca88601c0c06034149075842e0080743d1a600b0001080b00800d0300482004082c176040c00c05110303491134070b000051b4050100004a880c5500302c1c014081e400c2051408000011400d4104c03a00401c2203900840d9289021005185e4045460141e412111110702d40020420b10403019140340d69080354000449440300410408004000c0744142c107100880c0c0b42003000350741c05201400700142e91604c0410500c401d030030028980641e0111071080d4100b0000140000d071000019181a21030161101107592500d04040d015501c02d03a1100d0005101d02c0004104c0750b6a0b040b9482c100e0300d02e07408946280448224031110401c1c03e002d480300410030aa400211440c005008404c5007000d1500060f07a9500c40500a00f51182903080c1818400500c02103074100d0410004c54104121b0701c0003034904489024114440303600048005020480080824026900181172004c1400c0e0403810302c5520726926540314150382c00402500010070342110842841c1e2240200403100b6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 285169442 1250 285168192 285168211
    0x20010203092b060615090315110c0303010303051e120402190801021605070b130e0408190806040b03010b03190503190201020c06010501170435091008 66
    0x41105200a0250032110742080c40c1c81d010509100240300c402180b803036840c060080101040036400c3c41044010058070614000800525050401c0404c4403498004411903510030041510398101d04030707580d5801108144045404000000020160000c0c001c029134000b420100d4880e088001301c02196002e00c0d036140400d442e52200081c01071820300c05c244803144689611201054840d42e0740d50891300302e02801549490a805008240301e010411203000700b4841c1c0843c0d1814040c2003508101c910180b0034400e00326604000b0804210002043d103a81d041c1240305461148043e04008268010980e1001c2c081e52038510110068101030041c05015880078000381a800c0009503500800b41c5d0094007500c03030340000d010051502c01c00c0c01c640b240c107805c03030703800561500d0510b186107040c404103038803030fa06102a00700c008100e017803280413459005800039040d104d0780700c18860411003503000d008111001808048401c0c1048088005070070f04074415562841c502000c0704c0107036103940c0b0a8510000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 285170692 1250 285169442 285169447
    0xe101e031a090309040c0332010902030907150201020f0d0c08150604030308040c03060509070905090721020f0603010b040306060b0a0c0b090a05060a050114100905040c1803060920010203 82
    0x483d420140c106c80c00c000b1040c680060701d60040c0184805404034220000c110784203142101051345000c906550150904004c11455400c100c1034517540c0c4e404520801c040301d880500c407411154000c0d410345c2c954046804d1368641d80e40c641001040102900d8845101041107070b004074000040d8015529900303400a8682480d040c2151030544040034024001c44022034074040110000f403880c010700c1d00448884005008150802900e002a60300003020171990350f0101d01c04110420300640103120300702480c80140c50341100b07400890410412400841d030032020000002481410702002001184d000e0351040182e103403600040f081d540700301056000007542817a04034022880b000500c81e0440700304c10855802040680d100380c00d21208a8048030240d070703910010040c41c90602c0500c00c05804c119844c11a801d0b1004024054601c5401f5440c019940d03000300f0600140030320715014030900e08030171801c1c05030798a01d070a10187c10aa8811103485541945007070b04051400f450f43d503071201c140c02460 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 285171942 1250 285170692 285170707
    0xf06030e150a24060f020f0610140d0b07050c07140306010306020c0f010f0b010f0f08010b0309011e0c030b01170a09020406050d03030506010f090501090e101e031a0903 74
    0x2a2114110608000100c14842201c1000043c0f41d9001070549803901001e5010048000e82440c01501d0001d0b1150410810000003500c1040100e0941d415030803020030300c0c0e174644c0c0403801400e50100024814211401031020342c43e0000c1c003030326800c0390040490300682d895030f65900b0206588407207513801d070b0711000060000400079006841103208842c01c0f9180c1d405078015686c00e540e01340110703981c0150755030800c80071540c0c46842603403800c1d020305100c14943c074002001040c0030414441c050302940c0100100d581e0704800e4101c0d20004000e0915a0309030300a400154009040001c400c5000c41d183c0f49102d216540030303901c200d40c4d640500160b102c1c2c0d560348183c6100034140b41752089078065503840000c200e50b61110344035000d050080d6000221403400300000360103145025252820721841003000c10841e03901c2050b200945803480402c4955403078188114440e01c1898100030f040081022554488100214142045030300540030300e0240b883c00107030030b40130320020344002095400810288 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 285173192 1250 285171942 285171961
    0xb010b07030e1522030213290f03160914060a061b080412111c06090f050a0503031603051509100e0a0e0114090a170909010f06030e15 59
    0x40c0845101c61209440c1408190340d001051030b5448407505804c00c00c18013030065003400711042c01d0040c1c2403081040800104070070010381d5200d91481d0103403194209000800383e1204030720b00e190a03601800301c0b0444c22742428254400750003802030312070f00c5252480400c210312040040078010324003c0c217000d0000d0305288041711200c4480214851802030700d0682c60001d400038000b003000301445624880c5100035407901c0c0c40b1004450324031900c200000304e00901d007620b008001e061000d52008000404612626110240d000109809071550050858000604c80080f000710311810900341040c036901c2c0c00042c05d60407924180c0c0c80e0380704600064484101801d20f0408240c00c10500c00302d281056030340b15190b00c000c90702100c071001c0c01501c50120b1043c00109000b10701c9201302c040a03030207842c900751404550310480000041c0c11005034014031039441e0ba203107044400c1101d010f000c950013584c40e88000d1f2000d84940c4500000245851810354104401060045d01800d04000ca03148580313079681350303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 285174442 1250 285173192 285173209
    0x415050109060c050114011203260604020c07090203160908010501060e04020c010f1b0f0323060a0902071b12020a09050a06260c09010e01030602031506070506040b010b07030e 77
    0x22102996a42c02e820b0168081a01b001e00070f2a440761011140342030743c0b800601c640c080f4125a00d03118548410500e07000078603a00390303a000805940040c0c131201d2040c20b081c0780007401e5000403100c51001080c4644444d10342032404029041d131f1510424556214011030807602f0074030850000a96580300c8100ca4070302a001000701d096507200200e2402d8501c810403044548141e1803603c543c280a071448882ca8010074180440d000e81e0400304940c403141703e40c90b19000e180100807010408031a00040aa6035864904005000c004004640b962203d2030440d44401140e0880102001142c000080115594a100300050b038054030010103141340c0b0102d4030281501070107c80100d611640c000ca0240500200340902c0c13401c0750391441e0141c6620504606000c20041c2d02c0e402100ea03034005029001010201c00d0460303620480050f641e0356400c0c0341f461a400740340c002991250740000c402040c400001105409180100410344941e46c0e036130400f00e1548a01c01c8010b0104281072065022031070140c0c030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 285175692 1250 285174442 285174467
    0x90d170a09061505040c05040f0302060a02010204120b010e1005010509010806220207172d0706060824060109061b0c0b182e0c02060c0c041505010906 66
    0xc049598800e9aa90100f40ca40ca40000c0381002c2d0301a4080040346003500170003001e03200d14100360349821700300b5803981d11a2102d400040d0140d2400107074662801c2c800d504890082080700b644041d50f03682803800030741c4c603042803180b06205410800811010f20a0301100011264140c43e1300d0b2034004000c00648940300000c1c0080da104032070b552030303144030f00c02d180d507440a1a494500041c2e450300b0600c0e014524080b86042c42420031014400709010001c201100422600410014015944500101e29103441200c10080109090240c0002c03803400009220503102c0a8089003410050440c0c01d29140000448165000071001001041900e000d030060311076550041e0b080c12086a800e0702c601d500b64010368090704074164002060300382d0114001e0380d03441c600d0342203400000b03170180348000d0000c85079480c140103030f1005000c40c2e20480314001d54164030115400740540d6120b0080b900c2c2c050316503130300380303003160090b070418440d10300e19901d40c1280015600140c488140c840c0c02e00004a500309000070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 285176942 1250 285175692 285175711
    0xf03010e04210e010206180606210106030c05030d03110906090a05151e0c0601092a030f150b0f0a12090b011805070e10090e040515090d17 61
    0x2a060030710300d01021001c0d8501c01c066100c4101a03c2c440b40024606017008002c5d800c050420650a40c1e04000030604a8020b801141c0c400599801640c070228021a4080c60300010341c81c1c10400000c1244400e044c4086950440c103566001c9901d80b010380aa501c005a80300d0300d0381041046400e03134a000d4002d07110390000a0141c000302034585000c1120300005460141c010340b00482e00c0300880042c160b1149500030601d40103810b2240c0c0380f66686d81c071001805815601511180b0302007001803e91803904c1b0040203c1c2c1d00c0c4003c0a030b5054040e00926a05003c1c0030b51600380064200720380b000680b01c0c81104d0b200309140f40380100ca81500700913038010903080d0702000f024031140c180c407501d03e0181d03c03551030152008000035450426220b115503400840844030f14142030030045484c0e08084840310480c0d0940c0c1072519511032b59400c541d118001d0300100c032400c41407800e000074080005002c402c0c0c040485061846501c80b040c203265207440415501c00005c4540344003a0b0340c0404800714541000c80071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 285178192 1250 285176942 285176963
    0x702030c06012702040f09181203092d0611040305030906071a0109020301090f09120e0307050a090f050a0207051f02120903030916051011030c010516020f01020f03010e04 75
    0x25180002d0345d0080d4808072130301403c00b90a009184680c13144911510244000182c03c40d2a651040c1c00c080c0a8000502810f40c0d54016005000d01251200034021260301c2c1d04d00088079440c00c01d10031b42181ca9042d52006e24280c0390840111700c140480d42581d4208000750704002284003080305a82c0580b604031070ba050040038100a01001070320326130107802d101c0b10150322503042407840b00c05c54a2030306440015a00b40304000021954800740054060054580380d0000015880420300e440d07a154022034104960590020f60703802c01d80d014020041c90100c041c0019110049060241e000c1c814000e40260441d00c07421100c5494a245180e441c041c5c618054180342c4001040f500488040b151031080380c00000412990103814040c1c9860b110014070189800e601b81400f01c0c80300000c481c4031105001002102e00d0345090200251100400490002d10072450b10f000c030b168075421484032040c054411441d4498684506009548a48044180d440c1c1517038a007008003400082e0281003a203060484 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 285179442 1250 285178192 285178259
    0x80a1209180203090f2e020702010e04022a01021308071a03071101140603190809220603050c100807020606010c06090204050a02030612031812070f15080702030c0601 73
    0x900040d00420030220f0030b4110b0004000c1c400d2943c0640a046e280460320402440005030782003000100020b00a6900685030031184e0071151450800c170031040c4424204ca1003000030380e02c05400400d200c5d04809605501e066031a024190ba62915002c0e0044814207501c50710703551014071016540c0709d400d40c80e0904400c500d60807103508540c200b04c607900c1d2030b55400d003c02c0604e0504100c1e910b144238035031540c40c0407624561501c3c0d0450042c015040d00c1f8441a0703602c11010001c40034582104600000100402544c0f440d0003540d0350711180c549801800007140c0720224500540c0c40354441c6900d0f4000d80142d603030300e10045856482c00783c4202c9009954034040d4000d078860b841014820901c0f1140141e4a0070003a0030000100034803254541554002c0041160706500340b0524400f00e03209681d06c00040500365401d0303040c81c0d1189c1001c0080d501d489800036084107070310358290303000b07085840307155194461007012a102d11501d110100c40b988a4401040301c04004205682946c11201001027460704 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 285180692 1250 285179442 285179473
    0x150b010c080307050a090b0a090b03100f0e0f010608040f03180b0d06090608030702030a1b1502030306010e0603070c023a060b04090b010e06060f04080a120918020309 73
    0x7043d103400c0c000401c0802c0ca190b02a17001070034903019210310b00c2c00505100c1503060080500c01c4a001c0c0504d0802e020020175141000b450b07203140a060070042c10080c60340c454030410403642c02200c204c5901c4c80c811000054560140c080780d4082e13074001d0f01c121007014191700c05079410014040003d400c110b0707080313000620414140240c0a120000711010400900e458001c40664000b5089003680303400c100502d50040c3d500290f0541d4044d8003518400602c0442c0080d60105080c6a20140848611038440b101d4140e02000842c4251026250554109182000c0c0005400f003112604041048002048094540500c54004100713030104403034101051104800c81410801c013a044000d0402200c84040144034000e1508105080c1c5041140000a071600b0452079018421101c0806190010030026180d10301140c010f4400108669a0303190f171041c43e076995400d12482504c00382d0006c903074004403503c00c00e48031085a0440014000c4c2c00550720200d030081d40050000b00d854440c4401d502004c94 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 285181942 1250 285180692 285180697
    0xa0912060c0e010801060512060402160503041505030613020c0c06190206090109030206130606050d0b0a18020105030c0c070f0b1b0304150e011b061a0d150b010c08 72
    0x103204010201d407524081001800201e5003201e8281803010010062208943c02020358034030010f075010380340a07500e40c5004107000b40700d202003204081442044100c00c1c4903000004208803020034800060300301c85840700702c450740001d4440546c410311485c004c50040700e8640242c205100c098058500b448952302c00210a54000255612100d004111042c003443d014000143e010481c0c0d40240444891550000d440303101c0103219900b028002c1c4066800d120650340600054000582000000300403802c01c50708008080f1001ca010034188418510804240c0c0c82c28009540e06031100303825911201c3c00c0344216081700d03524503c0352040080025111841ca1001d80041140403400380ea505c1c001e610720341407084076103c1d1442d80da000f000200200c00e20407031100864080d03450020511801c210049810282071210b1301360b00407625180f1020f228031540520068617500c0311050302d001d03c035030a0051a00840700d02030601d207402800e28403400c1c416040900d014405160542c01c0d907a090783c4008094 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 285183192 1250 285181942 285181979
    0x14030712091b050102121e0706060308031506070c0303080a20041a0705070302090601051b280b06040e01060b45101806030f0c0306060507080a09 64
    0x40415000c0101c44240082c0400c0540f4080c80a018001d5044503a01094414a13a9550b4905400303100c00c1244154a0261110a5400341c0140181c03613803801e052140b0b420648400301d0041c0c030b18a5001c1d56103005401c40700d51b60f910404020705c052550f1000d0303944001c024038420f05103843d407241c9080c2c20b408040b001c0e1039401c414049520340341000492900300d041c9210040e030050701000710001140000466000301d07a4120f401403070542c3c0b02401280d103800360f10102d0324000103030301030031000b0800481c0c43d01211030003207081d039152103007816121035801032250040d01481002c4041001341c100340e00072040e107004100000c41c8040c1c1da807800c04250760011003c1d40b120f600c0713050615882c0303d61402c03400892400300c4a01c0c1d07007040815032280145004200f124424035507415580e251a000b082d1180710001c044001164030381d500c0002501820054450300b05451030010035004aa020b4483c0d00e060b2a003d545081c100740080d45c40301099808108a00705128511500252142202b445c40306003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 285184442 1250 285183192 285183203
    0x124021e031809040218060f09040f14030f04120804030b090601061b0b01050f0f04050c0c0708011104030f0318030c0e13021e15030a02041707061403071209 69
    0x4a00411050009829003402d01ca440389640340b0900016940d011000b80000c01020100c20064450700c001a541c10080d0000c55044441a400c01090100c4410b0300c0700428090f1945030b03041d040841d1015103d12545440804048041c0401c2c40a040d0340c00702009664484c00d107840c6415180d0b1500d080401c0b013119403806550200c0c0060104661101110f00c0c042c0c00c01051000c101c1040e610401c85a505000c2e01d070140c0031100281003542da07500720000c100c0740f018204200a050003800701d00180d204a5194806101e00c1100003850700051250302039444003040706074101030079a40d0341d481c0000c41d0481941000750b45000000c81c034580395240401103225100303074041546402d5082d540e0070401001c141e00c0d0781030828080090384410303803050740d009842009401c94200c4400080e04128000c0147d0a241c50301000b00549251980d00402c01c5e10b081d000a00380024905420f2561020346000302e0b00040c7c41c00b001c010000d44120051500aa12401c100e100714000c04070003004c5480f1206d06951 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 285185692 1250 285184442 285184447
    0x2010c0503030a0b030f1209010503150409110103150e040b072003130e0708060103021605030c0a0c051c06052707050910210606030503031801060e0124021e03 70
    0x390345420005100c03040c14140c00360007010307980c150020b4113003e00c00155051010002c0050005102016002081480140100203081ca01d0400700c0e01c0e0302c40fc400d03450110340741440002036820341819803c1111400080505550f6860b5250020340001510340d0081c800c83e8119035002e203906c0c140001070313009000d000755100c0103919015005c1c131400358400103003858048240085c44c0d80c00450a54000c50a080169903111040309045060302040400350550001090102c1160008144850201c0c0203d002012054460081040f40c20f40b0f0b01c500d54101003281c0c040000500582c00266010300c8040080022101c00c0d20307241c503c01c82d5401240819084098180309a00e081e40443c0d802c6070a00c140114a141809000300521409040f0740898450500703404040010781d41141e80035552107070030b50f074890a01510202030100740010080c503d50a0120100c0c610240d00341c1c030f904031800221500c3e0406d4a061080c10304402e0b12000c401103003c0c154040010b02d003410301260700100282c00440c1d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 285186942 1250 285185692 285185711
    0x3030a140a050c03060f030709180b01080312012709030c170906071e0804060804150902090406051003080c03070c050301050103050d080a090c090501030525060c02010c0503030a 78
    0x5600d1030014074600109180c241402614501081500c0c1c0c0a03030243c4d000a9991488000a481d20440740e000c20400741c20309141041e110301450740b52510a04c00c01d0b5060040e40c0703075441651207000d01d4800003001041000104607081041c22800440140381002e81000361804180c102030314090390007034020944406008080041c001c011204140100e9031003410002c1400000351036206940c1e010380b0074441c8414860703850400c04050034030781da8000300184e5038a544140c054482502210141d0310046003019140004481e40101140c9650090507030f0710030343d55a40d54030000c0001400c9120440d10020010002400f220001d100345103008004585844107807400c03845210700c5820990080e41018010000107600042840c0002840e0920040c25a9055121001000c900e00d02820008002100240c207030807582c40181aa80500705480c01c0c1d0480c102081944154200d0841c550000ca11341048541c0c40f5054994640b441454a016698030607120946540c1040d510802c3e0141d07100c8240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 285188192 1250 285186942 285186971
    0x406020f010501030521040803030f061912030c231c11030d1112070e090708060f0603070908060f060103150305100b0609100c0203010c18210503030a 66
    0x103503850292000240030035819541d501e40c4414409000e45288140e920130003140001000c03d0740d002d0180c0d001101c2d22482c010314404c0a2000907203110380180030300000c04103044100406a02620b100611014104020f56030888040c55045001d03641c691346403c140d00c040302c41051001342800b032035004002c201c840c04642481046007600c40c030140200c0141c038902c1d00e0000b0080d141c1d51035000000180890440f009541e02d4072924101d989085250300070441d080b900a40312140d0100f040c0c940c0740c0c80e40c0da02a0b0944000d40155042c603482003129a03040300a19000000b140d00074001e00d414034003540d071511001d18200c0280c81002112862004000c00c0b540c1c0b6203e4240001c07034500c1545806071454840316103d020325144040392503250b40b0010b08644134041180c220300e00c0030702503d4443c4640800244007441d0f88804034460350920054868a51140c3d0356001c1e00440c210100b207109160206080007a624503811030000004850640d000c02d200344041d521a540c2c18102254110310320a84 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 285189442 1250 285188192 285188203
    0x90405131b030c030b0a0204030506041203060f0b091e040207111813201305070906030203010605040509041505010b1b030a05030610021002190305100812070f05030d02040602 77
    0xc19201caa5950400115420b0111803007244c2d006042d40115403074180002020388142d0300041d10301e205500501c401c012007617981450380d030b0701070783c04006494907617203001011400c91242142885040c00200502c0c07824040140f51802c0c421604090112100041030580c2c200d48419601080325010711629030410400c4004c20003103e046400c810b00d004440c15031500264400649080404802c00c03203030010780c80c0c0c0150391010007071285240428030010800038140880708000000c01c10500050154080d0003920b05075816902e580d030505003420280007d40d60020000d5808046940750341071441e4441c41103a0290181850b0302d40d8903804e0410288010710b51036400c03600c65104202410007264801e007906c1d084101120320220b0000c002e80100d1034010030082c0c241d03c0d903100064000e116010300100000c503070442d84092000b80d50300a0f454040309141c0c4103803402d94100300d450b50603411000b4020112644500c0003940c900b41d160701c401d0b11319003150b0500303100554005000e01505804120 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 285190692 1250 285189442 285189473
    0xc03091415011703090a0e0717010506040510051306020d090806041e03020309130606030b0306060303030714070f050102040f1220120f07140109081c0509040513 71
    0x70864500c400038a414003680512484a03604010881611845003c1c0202c910700f050003461141056283c0c2c840c11040107080d5681c402041001e50804524040002c45074102c480041440d070605150105210f800361100d0f02c04420847e04009400692080152700740c0545200d9000780320144a200020f01800555080148241d0003c0c04002c0040d540d00f6030791010015552400c03505c50302900c2c050b451030160b84441688404d049061540d14207041d40b00000322640c0e03503014880b5000c91814141c40d08401d0380c0458254008000007030595000720440e2006038480f90401d8a000c1d4162641a401c01a90360111916500000d04126520a012061002e03010036011b039031204030913548003002240041d080c0c00e01620b00c04414000d545e030301020060011003001c1078900705660b91714591b0300c94405000e0070449541100300401694443d60644050320b000130020000106000c040b104148038841919003000f0302042000d113240c03903038018035016060481442d51103418902d0001240c0d5000c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 285191942 1250 285190692 285190733
    0x203070e0601090f23040209030303070c0b010501030c121d030313030201050c0c030909040c05130b03060c09010f030902030705180901050702010c1202070f0b1003120e0a180f0c0309 80
    0x10f005210b0078143e44417016094004000c070750709160110020038007034003d006049038107020200030082d05641200c09100b1007440780601c412240c0e02c1d0b000541c225980924000c000804000e01d40103507010551000c541002c0904010300c80f0031009901d5072941e40304445420300c524000d030f140030425409020799608101030b40d03000c0d414001540d24080e524019602031600c074000020201d0240003804003040c014100141c410744500a0300a402e501500f0012102030091049900051591510605031032402c04165100c10b032080c0541011000344c030000c40e003070341d240c0a200b00009a50303603101100c503916036074030f404507401d890007003c02400c40320010501800d5904212a44078226409812111020b060040c01615000c0034203041e200596000c5000389560b510b1010310a82e004000d8070340c01101c1c4a180c07a0303211401e00c41c204448110b540300342035400540c42c6000307108085290781d000c07098102d01000014000351007580d400665000d111540d010a54480c0306034280325000896100a92518 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 285193192 1250 285191942 285191969
    0x60b01180b03100329160512070e03010f020403052505130e0d120510032406080d0804020312070f06050406020c0d030510050604030b0c031905100611060402150a0c0203070e060109 79
    0x2502400342d10403181000c02d44501c2c24001012270703018082c00d907030501d00500200b21008400440000030341c881d000c251050700c00d5000080e96041d0906200701c100d80401c0f420003100e441d01c820300000b05200840f061405891340740000c0e00700b40c200120b102c0041d5075596a211214007e01200485901514440c120030b4403074010310102d00750440f416000e2403080d5010300203c00c10039403c001041160802c50050081c40d4000c650141e205050500442c000c5042d941c00e181540d816800501ca40382008180c41d090780c060348041202a445594454040c600c054541314141221a0401c40383c0654030021035910003d0103081c0010014400280c0401d4407028039180c02c6490f4000f44100080c07150034403001c00000940700b000d949260340840c040080040c01982021280d10520f440240a01c6000480c0328690010382c00000034613a025a070050070708241183d00000342238195005000c22410b00180e09846001a20100401c600404030310503401c076981802d100060100c02c0590000181c4c4026 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 285194442 1250 285193192 285193231
    0xd050a050105132c12030a020403030215130206030601171611010c0e0d03020304050631120215090a0306060e0601020601050a170106031509060b01180b03100329 71
    0x10f484503008010130080c0c1080030580312042003440c020300710a8003038160768088140482c88020780c001d003040c3e034420340035501e401c22110300007090000e08890007218039400d1840e002c0982803084c0155080030041c540070b04c40348644003620b03103140c0d01a28155940d0070601121038681e42d212544500c0103800c540240300c1c443d100c00c001490309003810b49180c8a080c82e00c2034801050b0080040f00c000f000302400c0151926a0042075403012045458006200c00058005080c081503964040e025100d944003a425039000c0381c2c080c054010b01203c018002400300f0801e0b408207a55011217400114450b0001181082c10301740e60400c5040c0203003a04e419540030500500060b6121003e640544061440022a560988600302c0c0034003882e43c0054001c12001200100d8652160041070034140685003e01c00781d40d5234001120090510607001c000c0440801e814030120854030300a41c0c1124501000c4c468260300c980702c4021940d555010329442162201c0318007100d690310a40c9650040a1800000c100007030b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 285195692 1250 285194442 285194471
    0xa0c03020f0f13141e06120f040606060206070804060e0a02120a060f06050a0e150924090f0703090c0306050709031502090d060e0102070c0311030f19060905030d050a05010513 77
    0x1850001d0044584074005185a20388584007a500d940b2100c2108187e1410040012000000b00b0340d02990110f092620200d042400054107d004008680e81c41c049942c0700d03181c8400400b0010700c00b12041c011102003c2c05603590b411054520f4803a00301804d410380082c60b121040720000311a408241d070821a00300015500c980d20b0004a5000d503410700c1e1940e645012180e00040925056544010b40f50148400030003035070070b042c1c505d4017208650985203492108024114404580303085d0305042089c0007600b03940c825042800110300c40c44101c01940d84030b60b102c00540d44212500030004103000c0b410828404403000c0b220000b0010217007103207003c01120101c0c1303200c0000710b00035045503121107000801c081c00358100d80c40c207074000c4240d5802945030b25000409035007030001140719100d2a8084a0484d02c0032682d0b01c20410005541c49816500f03a0340c10003d000382d01000d40d100c0c001488402e10350300b964010507109544070000019250304082c00c11019410720301031241518030300031000700c1400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 285196942 1250 285195692 285195709
    0xd090f050f01020a1424130201030e030c07080312010b0c1207020105091f12020406081303020f06010e04050d0311070f0206041508091c080a0c03020f0f1314 69
    0x4100395120041441c807500180d10307141e110040180541418000d800152801061100345500300c01c00c10010b250307440d41c01040782d460a5a101000030b0862850000540c000d9124000d204c1c038030320a80307003001d0043c0445800d01c1d001d540084141c3d0000031340360b4400807801d00d200380507040c0c40c1c1096041041d8203840980d50024110080c120250001c6c0c4c2d4000d40e8040c0059542e1400000d003400620b80c5001042c4249103580f10146000c1058014001e40f03146150003990309549980c1d03100c0c4426030b114412110400511482078095009030030102003200402e004940c043d0408030141c0902d4105441c00d40e00d00190002454105464454090003a032002c4d011290440d40004580b04000414000518640f140e0b0340044806a044680b820700940c20420041c4651468410303282186030348414500d100d24140684000108280700045c03005203103078810401009949401400e0110040f492101a48620b120f440c2c000004101c00c484400b5043c641c4020700f07100940c00c0d0390580c0da20302180200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 285198192 1250 285196942 285196949
    0x8010c180b192a0501200a03050601030207080a0c060b09130b04080d05041b0b0a08010b0a0e061305120a030e0111031603080414010e0d140d0c09031a0403080a0207061503050601080d090f 82
    0x140d11100807400d44cbc0c0c800c0c2c040c0c41040da0010766141c0d4070700c00c400c006000b80c03090305811240c10382083d50068403890003644c2c0c18400e000c521002072004401d0740d61082c420070020000c46459400348114000502e883c480c00e441248100b0410719079281c8000c242075501c445070310840505a0030441d861030b0075402055a4112019280c80c26110146030106032414454519865001040860103403d1101425684801c90b84181d80c0381c142050b480d090161940444400540440c810090300240c13544a6061200d0907120001940c3c101403122032001c11060180340150001000c0f001400305000c5041c0d420103070304440d01c008010301801e030300c0820f450300c0e1400340c1002446540841110760f580e01404a820b05100b120b8100408250340c2e001801c2032125001c1038071030201000c519000701d44a480f42c1d5010b55050340f142c40460343e0b58406e4038040e40c003040c005c54100b500c885515140d00d4210f0702e4500994400e8001d842d4960512860340d16200501c0a01000c00c42009000c0024000048010090b07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 285199442 1250 285198192 285198197
    0x40309050d11040905160b040b2b060803070303180b0106210e06011d01060815180702281a070e060408010c180b192a0501200a 56
    0x10440c1003021030031140c000801d07002824134500700100304021540f0020b403288038014012a0340c48010a41d04d50240c5d0282e2a00303004104040020000b1804100072501a1000c0030260113034140d00540c00e84230143e00001e8294008100e0100b0035816010f00703c060710210501c0c5029001c182c96982d55094188100d4042c400702030342004c00b80001e1140382c880141c03405024400510401700041d42c1d5a1309114165161150344600040224030011140c101c490a0b602c4411980300d800e0b1100c41520f001c90202c0d40902010641458000d01c030040c1751050100741c019241031782c000ca00c034002e840c100c210481240c0050417000000141448125000c03104006801c4d11030b0b03039502409131102003802c1d016551103440481c0000d0100c40c1500b040916251a5485070132545d07610342c0ca200007040c28001da4035032910a0002c0c2c038010764412f4140c15840c400b0300e0706a4042c81d103408440c0072980c0c406002c07140e503180d003184d60042c04024000c2400819081030400c525400c484407902d1507000d102c246004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 285200692 1250 285199442 285199459
    0x12a0204051b0c07030b06060403031205102d051002100203090a0c0b04150816030c0e04020406120e06040f080a020c100f08061909022a0604030908030304030905 71
    0x207400741c03070103040c41c0da0760110403030b0b9030320403216003c25510541480704940c0f02000174002074003030400c4402d65013120340c581c0340e82d50034004215108020306002030330552788650109000407036150040031310000d0245c10091811040070f520000402100c5604051b0103080d00104c00001c41e64001103140d0350104800c401a181d84862190078204035554501819050381d281c0d01085100846005008a030020716152404600c080c000b544c0060085030005007200d88040805105802a040141e12000d1403a100e90008e07082400202240c00039084100080c030349410a944180d0b0500c40c40b82d01c2e0340c5641c01805c0314503260340d03429004407002d180141540004104444d4290080006840c00303000204201c4141008070001001d1051403004413000840d41710100e84c850403d00382130f5038203980080503d1074541c101103e00c006584036040c03102402400b201085d034141d2040080c4040c40d80404e01920b8a400e1a0070018004d042e0b0380c00c4042c10360810814400001d030051045403c5441c140c9007481d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 285201942 1250 285200692 285200701
    0x307050901030908040e06011128020303120c040504270204020c07080a031e0f230d0e030c0c0303120f0a060b0d0e010c11030301210203120306012a020405 68
    0xa016046140f0000d0a040021402181890418104070700c10f060130b984589200011034a52a03442d80d00c40c2c50800c0381b20510700b6004a1703403a11401c900d000d60014080f00e15080d4603919041002c8821540d185207014041820b01852426014440e00c40c0c00c40002543e00c6400000800c00040e0002c10081c480d039400103007103240500c1480490001c0c9410400d40c3e120000900780034041540608299031080107441942200500400009100042c0b0b655000919032640c01e020181003414400e00000300c1c0c0c2440301a9a510150040415034a1440d000e035885001514100e40750141c06c0c44203e110360014481c0030a004003462007ea4045844140103209071100f01c6080001c02032074100381840540007880300e24051458000a23a00300289000708a1410b000104640c4078000b5103410050350010401001a1540e840300c88030301c00070280c2c01929042d02580002c0c9849801c864101c000304000c801c11203507680100b41130503440103040c080a0800030035120a405480c407100020703c683c3c0c0e11000301c1d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 285203192 1250 285201942 285201947
    0xc04050601170405032503081609080a08130b04080604080706061a1b0303360d09090c0228050a0212010b0a1e05150705031801030e0c060307050901 65
    0x200b00d0000e0894098a2030416003441500c0e0f0740040f0724012800710a61a8000e080600781d0920049600f40d601c41c405500d480c1141e000f4501c14892000421101c828017049100c004d0001d00380603031003541e510341d840047c2400500ba0720415403044d00300c40001e1004000ca40340220710f4076405035002c4c490380e135a00c030b0350b01c3e00c20300a001c0c94100586805065a03114000e024400050055812101512903060103114009a0700d20003150040d5102c50800300c204030480c0128a1070b0031154a90300c040b06445d1039080264900081d0610641c0002d40002c0c080201f042148100c4071104500c1c4064991320700151800f6140d10140341c00f081a15000c100f120091181c10f011000710107078000c0c10480c061150400541c01303810420800c600c208440600000c028510101345445c080701c01d9031881d0501c0c40c190420102901c07450040302d03030610422600c03001420900003841c920090541e444e00302c109100005007100c000000106542d4000d01d000b080658032710094a0f031040444c80c060f5a04d42090004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 285204442 1250 285203192 285203207
    0x30b0f1003060f1d0601061b02030703080d0203040b07021504141c180e15060a0504080a06150e100e0c0c0111040501180b03011404090525060507050c04050601 70
    0x1c1d041074940101102c0301280b030f40091940481d0845413550000c441c801c01911818207118000c0400c01d04a1508000d407800032088400754002000e60f0b1480c1d0b900e40b0340c0784260b4450140c044000d507000040004008401d00314039000390722480100342c5d2960b03518a000b01d084010b0800703080380206081260318500c013000500140841e00180302110080701c04042c040d03580108110003044501140410340b840c5280901d4070810780d00c0e845a595124020505c5816840035002c4810804d08001c045100b40080262540c018840c00c4006051004880c1c08031030f2030343c1038209012040c0c0c041c0603c002039920284a07401d40e9080940c06410b5200d4600020b0a0b21a0000c4070b550740d4200200d0350044042500070b0700c101c8000780c940b1120130410b0640642e4a00c141c1c021341c0100c80d0300b44014018050031035100c4a000d48040c00000d8880ba15890700ca00c0e0a4103000d80350716a40103210303081031410012100303400501890804506242d0141c0e076658031241d4841495000d0355480002403020ba100740710 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 285205692 1250 285204442 285204449
    0x105190302120703020a08030901050f130b160501050a0203041203151a12060f0d0303020a0e090c0705010e03031e0415020316090f05090114010c0606150305090106030b0f10 76
    0x71030782c03041545014050310380c0031500c000e9201d850701312800500036070080b04441a80748140c4d02c0d146002c41409450700580c0204241306000c0803180c4010850f03050120080c01c2c0240202d01208102c6414500b40e800c0d1030340106281c606a006001344800151201c1402c40d81d2012400c020507400d0303000300007158410b1250301540d0301440c2e9101b00c503a00b10010000309603d8082040c008513340e20041030200012a01c440103400100c0d2a840401080c840c1d03016203d840840c0c58100801c980101c0094181d110a0f00c00d1200071000165043c1006002d1060510180440c03001c1c500790328100c45400000d840e1081c8061708040000c001608210881030500808031400c0800c646030b050400920700d40c02d41000c0700e04045502000085080444101490100d40303004000e92801e84c2055a006101c41640c1a0340741880b840700c511000081d01401400041c00e6034880403036285444200050030703504013801421a90345001428400b0444e0210300683c80700c0740000607111902d8220717145c150b001c04d550 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 285206942 1250 285205692 285205699
    0x8090a020306070e13060317030a0f05180d030c0e041107120503010608010b0f0706181a0615030f060f060c0d0201050f25030b0109051206100812030105190302 70
    0x8040103881c64000d84022921384054a81070301e0610080403e408644903800701802030110105010314121840c2c3c0110340c810200e24000c91034492807038000c02502c106a485030f5071228850948454044108048034900856107000c0c400e0000314440500a5102000100d008a4540000424403082c400c2104c04865021703072200900000c10000500a80003806848001082c44c00002403145014050f5122020b84105140c900311b816980d44001384056452170240e80341006d0250007141c4485410345c038500c011b090720003641c6000010006000c1c10010210310f902e10038000e1100303840500c003510394080401d070340002422401500044440c05255030030046886031300b6503000040d906403c824003916128000c51150707203405100c0382d101d050301d8a800c0c0c04d04607100240742e0705920a0300075080356503040c10310090683d100c1010925284c0a003c1000581c0e20200030b02800c80c2d511060785004043c0341c000f40420510321204c0030018032040c89103500c254403051485c5400110301340d04000866009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 285208192 1250 285206942 285206953
    0x30a090317041d0406061d0f042103051506130902130512010f1109060702090c040b0703020606030f01090507060f0e0405090c031b030c06070c0f0b1b0703030804020108090a0203 78
    0x10b0300c028981a001325001c84040b800c3c80c1e03000400032011503400c402e620042d8200d000369903c164249002e4100140203903a2103c5503d000217608107030810914403402596008141e503d4415504990300e040451007900407001003000c0101011100060310039242c1701c40c40507907215143c580c18014001190011a4020010241e07049114015401a64002e0000c1b2041c03100c504002e0203e41d04c1d0003158011500305808100090041c80e06880c61071f446000e40a0140c10a070315000c4118880c2c1148404801507442101882101d26080000ca920110124002d0143c94850b0b628103454001611402051200e0110300245280c01049410307800364014004000b00d1400c001413130ba0351401919600d000b8002c2606030031640da02010b00c8091403201800a00c1181c00306400d1008540c00b261056500050303220740841c00101130402400142043c808603030f2505030740954003103450300140300c2d0400355000010400000360010342c0c0991043d02401e020700c8641c0c508000c2800c203034108800039858001e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 285209442 1250 285208192 285208229
    0xb030f071d0c090d0312020a090311100f0810081f0f0e03091e030d0c02010216062003121009060e060d080a0c2012030a09031704 57
    0x28141046455001018200d00710840340052610400d9503021a584020098000141400303403228003150301c40d280c0758a40741950210103040b600202907640004414105c10024402c4045501c0c40c84503080310100c01c0314031028009810001c1c1c5000400030700c0700c030f100010140c00190040800030406001030700d046010803000c0000b17020b504020014060301d4610000341c5d00190b44110b0030b030284941e00542c5030000301001c0001c041d84035008a0a182005a0144010b0310705008407070784040c9603120b00855003010b1002a0a111281041204500340c2a80810000c2e0b0320541410640301e0000c000841c250081d01d8160451181c5149141c5126084040c4101601c00b40e088a00b10b03811081d0820089848800c1611801010740c0c200758428600101d01c00031503100c2c00205407945490919450745c40599031850380000001007000c0200d00c0007840207010b03092801c4030322007803050400954a00715035154050300e041c42e02d0001802d8043c0d036507401104588240c0444000d016038038031032420500c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 285210692 1250 285209442 285209473
    0x302030a030c0309111201110f0306090f040816140604050c03190b0f0a0902030d02030c060601080103120e0316090603020a0b0a20010209041107060606180e0a0b03 72
    0x50214440020b2402161000341031092041c00000c44d404281c0c0900350900c54200010b41002412070000c43d5078a09203c802c05206030010001c802c40e44107840d4030f031303d4031008002c80803a0062040e4441a0000f04203c0040c1c00f12086444948841031210041c12486c104880c2d40190360b019a580c501c40d21042c403060050000f01c0c2007074410203d00b11036030548080e55218410500d0030000f0141d1340300300041b40c154405056070a6000c1264000000c0000aa030000ba1500304682c1d600f4000da000000c040c120004180000c691040080c04d040085501d50354910511000008150081040700908240c440ea0b080c0003800312844188030181c802034880c520b10380100b08030300c0220310038441c1d0f450010300d6806a8007500c000c0003403038403812800c2e4092001c00b80014440e00e96011103540c00c1190003807541e40c030b00c2080301149500910503100d038042e1a005d411554207030060740030b00c44001042e07102410703030046900559821403035005844d00e07040301c114042c051004140741c1c98022100c5103903801c43e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 285211942 1250 285210692 285210697
    0xa02120102030a060f1217091504060305060904150914010e010605030f150f04080708120103020f04140117100513032a0303020a23031e01050d1e0b04030203 69
    0x1003850101300300ca03d94400d1010001caa080c404d008014004184100201d40c0d038000c03400b0f280d000143c02c05e192504a000054007480d0301d0513400c014041c01304060003219850320803142e21100c2900c09d160207040540310001d5055442854081c0305440304481c038108894a03a02d00c4540485000034880b030341c0e03001c1c0040d000c0e06a900559009109a5001d81040440054081041e000c0300c18241c10b030707858403040c2c05d280350801001550024010480600000c08100003030844080082c49103c40b5415441044422904085042c1c440c46c244076040b07241040ca00307a104e044419800002d41c09420301d00b403690034040c0d489400000e4601c0c0c0410854023503501c8480b203820074400e90304c2d540c0408c209403088203500820340716121284021810000024007a80c020003044909003001c034107400c1500001900d8806500c07207004d00701d001101303002c10f00742600100c81c8008040340c40c215203903060501052100d0034148d40036003101c050710010214000d844421004890700010760590034506424080d43d241e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 285213192 1250 285211942 285211951
    0x2402030714071a09030c06160e030309031b040b0919150806010b0901090e070c03020d030b030a020f06040317030f25030c0e03031b06070804020d140a0212010203 71
    0x2507039000d00840302100001190040c0ba03020502c0610810341e180d0008502000078181e6016101c1040410762640d0704001542c42400c007015108541c40424000809095074641c0f118000e0b031040c0300d40440340e9804940702104c03034100c000440c0118101c1c80040d0182007010520b541021510082c072502c00d000029126101d82c00c20014482400710346441c500300f0009205a06454000300018020401140d0040c07030394a00500d4aa8031803500e801c04100305500075583c1c0000301d00420b501a00301901407201c00d00c2ca43c0c3d6420104122030303015010940fa5804840002d2141c8035401030119980c1c1c2e80b01c151005181c10500c4034641e070101200c1c00c42c0300da1060f6220004010100000b03800007511001015010f2103100d41c2d660300d100d038040207070080d02d40c040181c400d012992040101607103042001d03000700d4030b0380c0d03140d2060070008040740303420003202625500030409c6900400016031185120040c059038409203c50a100a51510609003041d8400c0290300140e568100c80d01a001500a507014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 285214442 1250 285213192 285213197
    0x8040506150316061e0c0b0a020d110c0105061212181306080d03050603060103080702040f0b220e011b05070503040b130e0f07141e070b0103030807031806020724020307 74
    0x301a400005480c54810040007e102e421100c00003460701040e60064400d00507104004940522000c0400d4a2038200130540c0c1266950f8030104007103071034541d110319500000d00300a445c26410390f030389180341445913200702c03404010080d02c01c81980c0c69001070740d49110314501040015603290b004090b115619228980c002a0418011400d50701c0d0120300c146c100e0380e0141525241110507070900c40540340804680c1a41a0340d1020300d440ca45501c088141c0c00d00a0300c029108021201120f1411178480d6074040754240c1c0b601e100440002d1040510300301c61002410840d03200d4100d131030004d02d03500c1540c04c44200b900022a000c0701d9005008523444c140c40b2107181e5a2803d81d0b4504150425850440700000001d0001101d01181c80d100300007420801c5488a0f81c021225068108410a0317100d0310044651200d04001001855800704002d42c00c410207240a0100c40404108521004a0704d08060b00d131550000f16103080001160041e6904104125107511110813a00140001d4200b150500d01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 285215692 1250 285214442 285214487
    0x203010303080f010b0901020d030c11010c05030703110324030723010f180b160b04080c0c031c26130201081f0b0f07082205010804050615031606 64
    0x2c0d900958404d4a0486c10306a0082a4521000c80101c014200741401c41090000081000303030b60900038062030030011407a883d80380c2c3c1d070309041400404465515031030781c0860701c0608c10b1006a050311440d00c200e4410810782200074003100d40c000707810400254002e200c4859042c05890060700c00e109601c41d00c1209894407612061165000e07100c0401c10f850f03a11030b44200c154188049444c84010300303180401481207480c004030302d41e510b048415081d281521074000c003140c660320024041040703840d8098180c1c0a8044984502c0b2107500311740c1c05905000a103c800105007411010080c000d01400c4201d145078680e41c200300d540d2100300b2884240c02e030300107404400003c88500801102200b41480144403007906c0341340070075070020340d0031040790000c900c442040080003040c00a0090706846840c013010911902d040b452910950761240c0c003450501903408100300c08a07401150345544245c0c181450308a0801140001c1d047c0860000b2140c0703403c031000380202e0507641c0011030300c00f21113981e4034001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 285216942 1250 285215692 285215699
    0x40c0e0904050d2c01030f060b0c0a0c090c050a08192a0504081b030c060f0408010b01091206150b041d0603010b0604120510091a16020705010c150203010303080f01 72
    0x100c0000260240c4c01240840c00482c440794031941c843c4a000c1c40542c000242907480f40d6420425900991540c04668410003075803081c4004094140001d2204850800070101c0f5014064054000c10f4025418092000001880700456036500c01c9041400d41040000e0a280d5103940c01c29880207030b60301c8025070078528802040d400b540480f8261824003004040a04204150800200800240740d4043c000c00e00700c40003070b17140d103005401e09003070000c01c0644540c02d0203851400c40304400441c0c0d0400100301010030074285043c0003c0c603500e40069004c1214116485921148860f991028409500010b000036280d00784000200180351980301405458684104050076690f0300074525a0000742000100090300311650103d8005103c0d6040d00c854454859a82049907180101550303001e07010116040d2001005884030b80c462140ea402919540341c2d00d600035a1440705005a9041c8032004103001d0520502c1181d0130942c110350507080d07589603182e00d00100300f03842c00d6441e104031014a03030020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 285218192 1250 285216942 285216977
    0x20c0c01030b0a12030c1506180b0108040201030911100201020310060201110412050f06011206060b0304030e0907170a0b0f120d030c0915020a03020c01050c0c040c0e0904050d 77
    0xb070349042c0c001084141001d08200c00e0b0303007000a00080440a203e828440c5400081803000800c00440401800050b80c91500c2d4580704524140c10340c5180c0207143c0703090901103a801c849400d030425028a40000c0f110640e150440c1391403100107189601c0040003101d07070201c81c1c1c1500150300c604003802281031001d5803605c051342071b600302c039145004224083c0070620a0100000f00840c07024001c01c200d900c00d0b001c1407001c1d401c0103400e82180c04001c5449130340c4801d014160140400800386841103520b50b01d041c0c2c500404410102400501c6041c2c0d00c2c0104101911940110070030302114040a4514109101007400a0144804a9000d000c40c4140110030b858031202e4524100140005800b407002044800c800800035015402d040c4410307a000810300f0064502501c0145181e50024840000343e0700b006894a28201c1010341000000c009100d154200403c14210422055070042035003300342000341c940b5981c42030301ca904450300034204000c0c00400a0225110750070703078644024458256041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 285219442 1250 285218192 285218201
    0x70f0f0303150b0d090302030909040f0c0f0806070c03020c04110c010506060921160e09060a0c0507030c0203071e090b090c120415050a0213081c050f0708070303020c0c0103 76
    0x507104043c030148144484240c0c1038201e144900d101384140c1e0b14003082880002e0600e0005d940690f12055114882810802410341d140060011000005950351426141c0d6984420090030481000300c0b042d5160b0070180200310300081448001d0051018011000c0c2508098102c1d00446100d0f40c2402e0100e0180c0c10300c0000c541c451781000d41000303008074843d00d8032807010608104252a0380f080c1d042003030900ea10852100c01818012605a0280c18402d40d0a49800000351050300541d25142880c2c000b50341040840301401d0745401c0003040c452a600000341022740560101c540c03c6120300c80ca030080c01d90050f00c2000c0d1010300c07004100e1b8091500c288640c04804036200901c0100c01c1090001d030480103035400703912512404c41034031039944141010040e91426a1451030058000c50401c40403102a10703810060411a0014404060b00715501095a001d00480300d00380310000034030f0410446003400702c0792141d42000805e0b0340e40101e80340040095102090310f8030140254141c0045540c8207018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 285220692 1250 285219442 285219449
    0x1801031b0c2a03110f030c090a0f11040902040f0b030f0103060e1c0302030601020d020a050601030602090102030f0a020c0411360d050706080606030403080c0306010302070f0f030315 80
    0x4030601800c0c0306998401c504085041482103142c0e640c1c8100100c1ea9020002c01c000e107101c0c9865125410030b02e414041301a0880c20140e102c0e401901090f1202c0e01d0ba207800c00e80c0a03051450200d20036100e4010b1400a05071030005810745030300054045208034540d00140101c4440c02d550304c854640d20901d12a1a000584140100309561001000407400a80200310007180040c19103103c0704080d40403942e4084041c5e40e0002281e00881045459038052200541d000d00a0028000125081e1750303058940c44140002070801c0d5000c1407102950b4070070003d135411000c14038960b50b41c1d401e2480d00650748081d0011454403850405950703c5c0c0551140060303c0b03107030076441c182400c01541035640c15480800c81401e554071185194503660542d64408032a40031a0080b0050710072107050202c010051070004191900405080041c07000282d48001c0c06c550102c01507008035265140e49004a0191003049005020b00c030440e24036006100c055211801d0300b5200e42c500300199030f10100310741c41c022901d11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 285221942 1250 285220692 285220697
    0x40e0304240c02130f022a12070f03110304030305070b010b0f091002101a04050702060603060411030a0606090f061e091503080c0604032d0f030e031801031b 69
    0x409000044c2007810207403074864008240412050a040f080344100d80180352919132006070000400c01d281c17a000700b8207003040344002c060410800b513020b211510344186440146000782c4107603040d090510841511800c01e0350001600e41d11952418010101c0e08043d03400d4402c2034540300002510f00034441104c2e40c10342c00080b0b4900b0002d8280c00c0015201070366608800794040c13203940d22034021051085040800c80c036103415250385146c0c000d02c0308480c0024480030965200005100e0b02c4d50340003c001d0342c0603601541000b05014500c02003070a005c5c813844020116401d182c004141440140c100707550a440491042011955401180003603280c40e84280b88122a615030502004000da08042e084080c4442000a980e6482c0d0780d2400030f5104000441603504410280410194080203044103049607030886c0e100e010b00008892500b5402c2d0b000e807014004090101e21543e80aa08045a40f0181c041640d0710381c110f850316103011420310341c1c996001038a4011120313580c00904c50000001702259 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 285223192 1250 285221942 285221957
    0x60103090b061306081e01060b09150a090b16050c0901061d121002040602061b03130f0c060815030f0c09040309030b04050309090903030f0f0a0b040e030424 69
    0x10410712681501d50003111202945468005ca1801030400c804001000c00c1da8414444004190006085580c2c6411000c007800040240a026944460079102d91b0300b0096a01ca0381e4850241003504d6048840c1c0c4042d1201c2d20200c0d950f0b12a8244c5480425424050011348800301d4282c41007011030003090040b0404075060b10840c3c04015103a0b007141d01a42409016110043c0110b82c1c218500115003910a4689400181c240642d540c1801100e80140290309861b084c1c0704090185002e900009184145000560104d0300500c2602120510210b81140c480c54260f03031547c00052485030125200c01042200810094003410001045001e070307101007000d0b01c03240c1c2d02d1008000e000000500180c1c1000b40013000400803c00c2c07002401d00803807040c8025651080110240b00718618008d0000d01c09400c240204008083c1002d910395100750140032841c280c0d0740c0d8881010041041025040d001881d0017044048803100000800603500e41180c40481419103003010500d5003071000300e120001d04e00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 285224442 1250 285223192 285223201
    0x4140402280c08070c06030c0801060c021e040f05060a1505030a0e03040e010807140f0d03120f0e010218041514010306090c02030d1b0f110c0603090d020105060103090b 74
    0x1107507121000085031512007000180d68a4402403030b00100350540300d000c2c0341070080054035098816100807025a040080703917507240c18005031a25146000190240034500c1807585030b001c00c0c41003080303043c60007401080318200003a10f0900400d4100c0d465406004510300100d6004240150085866600c2d43e0f11441c56591303a5052020308880900f40703140b48018080428071000401e040b40c00380c00c600d0014034155240607007200040f18a4020280145c01c4e80d1407498031926a00841c450080d05410004801200182c100c070003094082109080189841c81b0344c01201819002060300c40040c0d611001072115100c100812520714200e07516034403c0c0386a04001c2c9040d0f22002d04209541410f000070400c0e40c0b00c01583c01c3c0c0e9132201800005810005d08042030031000e1044291000c0d0500a07454090400710015000c0280006040c041c00035001100d40e08090411180200940c00750140d0384034109141c3c840c0c2e9464010080341c02650034180029a2541309c1d200b640d1400750080207601d09a100d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 285225692 1250 285224442 285224497
    0xc02090c0414151204050a0506061507030302030907090608010c020610140907170f0919050d050c010207080d061701020f03040209040f02040903210b030615010513030804140402 78
    0x100c43c0f070421000309040c004070402200300300ca1584128054400303400c4a024a1400700d007000802001c0620401003a105070201e100258162071003170ba4941001692502d54041d001c1c64049107038010b061817030405901191618043d00902103c441903001c41e0026125051400b584080c40e028450074000b848170291034a14098035810b4009999090648400b98007c1000550300011900c024090380808180400c80300b0800c0340c1091842035248454400900d0755a054449031000c8000f810000040741f0212260001e504032600b50354021146c1d80d07500c40302100d2401412007031040c01030724450380d20580c2c180740303040c001c940d19910116030b528510f640c0c650800042c92800b41040d182880d000e4881e500588036403103a00c540c03500035150f0180700090000310b2000300d05a09051515541400828145078800189040e04884030401950041600c034004955074040e140c00c5040d00c62020100000b802a08030090055460b4a030070400416400400d000903485080e10b01101d204d0b50b400c1d03c84c0c441c031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 285226942 1250 285225692 285225709
    0x50c070f150302071703041b050402070b04030809150a0609050106110703030305070e100c1e030c08070f051b04060506090f220c050310050102120d1104090c0c02090c0414 75
    0x11700c03412400d52206629420400f140e04211002c9610711003072800c0702020400400d141000b400c04030340541c0f901d2401d50344d1b41c0a0000207400107041c400300c0d50100e001a0010b0140307480008900b840b604244c035006060318040c2c607181c42200b045c41e28020000c91410311681446c031700300185030001e181c40c502e1654118000c0000500c000c04100550100f19415550f4428090f07410000c2e99660009140c1d90610f9441e2910125026010b030009e400700390000390f0080b007a4130040da044244c0070746a56860411a000b04000300c8000c150f40100c01000d29007081c1001c0b24a2028004e540411000d0b0325a010f014652046c440300f543e00c1002c1108030811840c03c0d00b0904021041ca40d4150031400c2c1c2c801781c4205440380c0d10a442c1c042070b0080100000d10f08050101c00080400344001c2103400310030858405544111600c001c0340a03115500000c0c81191001205e000742201c0c0b8040008008541004104140034602244038203480030204080071218000e65080d250ba13000440c18001c4840d01308a07062 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 285228192 1250 285226942 285226957
    0x28030b070309020418031202030907061d03011b02070f03080904020c1f0b090a020f090d030e030d080106081510030b0102010f090b0f07030204080c04180b0106050c070f150302 77
    0x360b00c0c2d00b1180c0040e1540c0c000c0c030a603009141c0618400c28918039001c1c01410700e206460407030a20503c104803c0010020b06001107512605010b013004070501e03074914044409020003070b003540c2086894032b41452100460210074042e9429640704903190060b641c040c4185120243c01480b003401980701900d042d90080c016003049000300c0f03641841500764007032003c0395a284080b0159454001c4007080c180310070302517442140814114602004403d03242520b00800305000d0290203000c111004040c01100d06808030314006089503111070f0080002001c90a00740501d40c0001c018101003080c0d468180e15111080030018107010b480391501c1c41c1240280800c803401e604643d2541442c541d10907442c440c6c100c400f4061038103d905403a1210640604520103401a010984108000c10030310002140e07084030b00b0001c5030082440040100d0a410380f12103c600034000300f840d14000100180c20500401e824840982504d054503a504c0254001410302d1141804d1281440042d0000c14400d600a0150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 285229442 1250 285228192 285228197
    0x3090d0c0c031416030606060e06120f04020612160f0e10051c0f050103050f0d0e0112061508040c0501090305060402060f13060203040504110a0c020d0c0b07060b28030b07 75
    0xc031071036004e41103c0081c3e4001d07101c00340c1c1c589040c46882d0340410074089400d01650303068500720300301c0302c450103102009124284103104400400d08554410088940b48404140681014205207a8007021781099100100c0460103c034043d00555002e94003121020f800200b16000390a080001910241c1c898640d0700c1c094180c0059900c2ca41440c0c2c455036088c03a0f00c103000040c0030340c1913140ca00c0c03800d07042c21049603103940041c03402400f090744940090210303642131034140001c1504e21501c0010342101c0e0000d2012050300303800c41115903032202026205a01034500c2c050903035034442c01500c02c1c40c00380c000540f80360031510018025080c8180101010499014020b01d8118094440d02060303000d0307005000182c2000408020503d020b00800424480400c0e02500e407a0305020094500341000304000d00540100399080c2c20301c411401d41c071009000010344250f594000c1e2408500030171258104031b1050a0444010310741010028410b15001e0801400148013415a11074250108004240c03004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 285230692 1250 285229442 285229453
    0x604060905011803031a090c0412030c0c15081f030209130209040311010509010614040b01091a091f0c0f06180b150409120516020402040b03090d0c0c0314 68
    0x11000e010f148030200c4140243c2c1c0003d80304e82c1e50640f24100900062045116010800c1032000c0610054215021907002d0365004081200600d400e681c002404080034041c006050740004001c0c2d2045111170022099139104442075a0b10f038141c0c040c2d010051400c42040e800b0340c40500060070981d041a800200607a14480400c0003a400600701580448040700000c00301111442c000009000e120f400400f0807000307100301400c000b504101e4440c9404a148141e03150841401a80d0151060310090941c0e8025020b54100980700c42c2110741c0a0138019010b541894182ea45001d1540d003108680c03c641d5456104c0c92105465a0400304141072054030b1840c0e0b0b88014641c51140e2034404039106100c0c00b2401503070b2170590060352840c212001100d00650400700420000f0b8030300b605484c3e042c000e03030402c60740f1128044035500c5141c42c2c02000030b4000c0e10004001c2040c2016802862158030044101c4205070480305046440c1000c10030000c10501c0d15100030b0000400455002c5407030b0300c91004640 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 285231942 1250 285230692 285230711
    0x309030c090c080a0504020904080d140c0a0f020c1c1509030206060901080105070e090903040b07060902090106021f1e140901060506090117100305030d020a02060106030e060406090501 81
    0x8600e0400360340700604080d030360a01858001c0c0c208442550100c10701e0380402c15460f10350003040e47d0b0000240300030704140c0002440c945505950344150a1888aa50040b129251200e250407941d4040c0c1036039008240c08000710980f1500c00079002e03100e10405042c0d0074102140705150040c24507940c00c01ca80c403246030b520f0710000700e10a10802d50940e001fa802403074113052281c24000d0209042c0c100303944c0342c2d06000030407407815044480e1a20a840c142c50f48162591194012415409903411602d035149002490200740b00f011340090030114000c440031089030340d03900c20503a9103400d00111406041c9001440c802c0745010340d402450203904c07500b560382000405041c0802113440080c504a03480f4903180a08c00005000d204450280005856052500f05064006081c190503446880c01c100401400140c1840080424000a60388141241c1c1c0b14413110220802a40000c55010010b120301030000075030611034013626401c60f42090180c6069150394486c180035029428050340c056484840c0e95 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 285233192 1250 285231942 285231953
    0x3050d0510080f03130e0f040f030e0a060c0203010c030e060711011b120605040b0303091c05061e09010915090302120f040e0f040b011e08011104050319030f0c030903 73
    0xe104000c0580107166202d0582c0b80303c2e4001d440e240c0040540101c486c2c1040b81c030800d0201c00c641c100d0740012400910b420306103022100c6844080484c1d0300070340008800100c40760440c07003232030040d4422402407025000d04107048048580c3c1d65004034255010fa0081500035014840040c9084000c40012910000f030780c500000e420312880c0d5030030001c1c0c4040140320f6244000d1044030007400048070248400c0ca00b4030300284e524012103100521402c829905c1c0b81c4803134410a929840140e204041d01c01c14504503003a18180003800c880409000c16410000d500300320180314080200e9844100158050304038020f234401000501021415442010304541411207030307002401c540000492000d07030300e5042c4171010614000c083d0031151100d482c4000d0000140c224405581510703c0c1d69821a4a65101034081c0100c040d80d0703124040b254030340801c0e00b08621001d4001d0080c1c400550455052101c0083d03001040c6010010280010b03801900028034244240c814400103030003480c00300383c080c1c0c9075100e6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 285234442 1250 285233192 285233203
    0x90a090b0c0318070506030c0d0b091302010f1b0803070e09180c0301200702010516290403020a11220203060301141b030c071b140301060303050d051008 67
    0x988070500010041080c942114100300c403a490f2940d010f07103001072400c8080b62150001400da558a1240170414203c00c41196005040c0d80b10020020510b50801e00f0404101c00c1046e40c041e07001a407030054038145e0b2801071103090301210b415007006000001c103032038801040e000500101c1c104803105050300c0882e07850fa220755000fa58286c0c0c0c2807046ca554400c1d02440c18111f07248041c00303641050321000000c43c1c0700c0c142412402c440740300a90751300c07400c0c8012943c074841c824403010b88941e80d00d6914180400c1c040d01d8035072042d5a60342c0c0da240c100c500400f444607460846d00100180d02c103016100025040041c00109408054804004e2100000c0e40c409002c01c0007840004d525404820450035182c00d00442c0556140000000171a0400700d503210800400d0b80d84280004c84004042a916910901280c0c402c0c0d401109810700200348a40d51480a9071511403030781040001d030890304252a06104842c201d0794140c0f260740c0b40075182141c0c9805860002e0214003000607640c4001001e8405200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 285235692 1250 285234442 285234451
    0x1603030f0c090608090d050319060e1302100804150c1107031407141f05070605010e0405070801020a0509040b0604090926070f03031802040c0c11060307080105090a090b 74
    0x440c0c1e10443c0c2032034001005008014606035aa500c1034a165610940210403a50014104a42c80790071030103522200b409841c81d40d1010503004203940030001014070359054603581c0c03442119504407803140c03100112074a032410741d009001044070500c07500b000c441e030381c0c08608802954104410034040081c02c460425000ea0b01c2a5848909000d143c0100001400307800040d0803000065483c124400010805044280f804120320700790020b2081c58050103a41520b403035940c4500e01f40714660315074009002c68881514211100c5c424590007045168040c003d8402d00890b940d80c030f40c04c0201c0c5004000241c1984400c85410075010000881c01016a000c0c03255500d018800c24130003020030205901c030b250440003142d84e4500c02400f01c280012218504040002e8241c0f5000c00c0d515141d03094130200a4190f03d000354001d14189003d101641c000300c0b21600c0a001b12071140903100800107000c0e0301e2000b1100c02002841400050003030385803503104c594022003449400140e003055980c03a030021050983c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 285236942 1250 285235692 285235697
    0x120c090a0b0a050a2103020f0109060b01181a09010c0f05030a080906010303200102090a060807030f0608120c12070605011410090b030c0c01021804060e0c1603030f0c 73
    0x103030000e156081996580c0020801501e6900c490740c5003190300c1d64800c5c030480402d40b64131409010030702414801c200f00038900801c18000c0212101c41d00d440c0c002008110406404160401c0e03144070305607140d0002d841120715980071901500ca14442c6840c0c035510040307005061081c40d60012005c0b0302ca401900100e580f0031f000869440340401d40140507400001d0041c04558800401400000c0c1d010441820340c441049440440d282c05000c2c0c980a03001c1c000303415170452502040020030035400581a4081c2d010b40e24100000c180400300002a80d034240501c06180d0302203400540103000c0e0030f0060040c544500283c50717140f00e815a52110a501803001039440680b16001441551481c0301000541c02c002c40c0c11402041103070070003403c406c11a21540c6c20400c80840004e48111079441101c03e410b5101c0000c5540b007000d15000d0003031144c003050980c0500d240402c00304640030000c4859000380582d001140c1020520b03100710000780030391081141015280d42e04440c510703940c0e01403512000001e8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 285238192 1250 285236942 285236951
    0x1003021011060a020409143615070f0c08071e0f050f0d2a0516030b010f08030c030715020f0301060e03010b040b0a030f05010e030a0c0c0b070c05120c090a 68
    0x7400c070429500039400c40600c640044040c0300220401d040d01c80550703141c0b54a29410700723540b490034020884c2d01402003081406945070000803696015141407080e551520b07039001402031444201c1d6a04103005004002d090308100d08404955480c540d800e4000710345400c1320142d495555182503903070045070304a030a40c0c00315000705800312091100040e400514940690f251806915000848640400107003034410031201102c00d11104bc442c0345824484413040c420b100b513036403800d8004008248a1013030310f50101c0c000032039810004003c440d800040b16000b503060004980701d410313101e034a03c2054128a942082801440142c06003e1802088241c603042111201d41c814036003900c0302d442800f481189040c6141c045950f4503401c0c01e007541d400040c3ea00d5100164500180106881a5082800d100120340c1c00e000541c421687c21226120348200994999120540b81c954010b03044001c1201c0c03181c0c60140000d0800340b444202e480041c4007101d520b2960f000c08161114016100c480384030361503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 285239442 1250 285238192 285238199
    0x5030f0312011d0402040e0a05010509031201080304151d030a060e06070903021c080d090605011505030106140d0209100e011704020603040f230606181003021011060a0204 75
    0x49000792070060210010740b40c0c0c10340341981180020580200000d20031943c601020714480c204000a01615900c40001c104034208400040e070f40740c0041a00043c092000c82c00424100b001000b03650885191509140c00244152030550301d1000c00b500b561481d40207198400040e9801308904605140501e1300090300c0d01c0c45120150400c0030040c000d0003486060803003000142c0303c40b090701103003035580388100c1e4021402d85400d114605c258030760102010f0a00001c5818009107501ca9412030729000152113500c280030a09a959010034415074001c202c032003e0007019400ba1070001d0122880c039184c011f140071154000220506100b2103040e0014080821940c03007940c1080e9081c8012518258168080c906a8000345551000600081840d20101c0c01c0c08208000c0b100424a110b0240c0924526104034110555640302c00b210b907507100c1c007030401c0030703005015200113540e01905295142c40c0d10181150284a6a41140c0207601e08000f0b21480b004031044003070200e503001d00c40c50309015994615 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 285240692 1250 285239442 285239467
    0x121206030f1f0b0d050c090c161b05090408030406110d0e01270b0406150e010902030601080f0708071107090e03040513020405030a26030a020307020d08130602031005030f03 76
    0x30030b000c090040d14002101e00101740300107107203000c600048640c000700365112100d21030369015110448141c009200c45680800c58074104030784040004142122070a80e0f90410461492010b0310041c111410410106001c555a500005840341c17000902a15140c6484141c0084403c044c00008099660b10b52545a4001c00103e5580ca0f180351142c980000040e6160551781039005440100b4003907891081d43c800c1503c00d04008010a13030648481400e40e5108200006035100b1940355000411540005840d40c446444050242d40607582d5904103a841c00c00a503000c092054100406c3d00c506000020105501c0c000c60358005205405141c50303515020602070640030001140d454140180420300140c0c400142c090702c0543c1006105400f10603c500600d1020403080305a0b65160300001002349102c5032b90015801244a40e00321a50a00c020100315204141903030501031300c030001c8060300007050a6401a503004100042c600a2096540f0002403801c2e8810907000255040810100d1071101e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 285241942 1250 285240692 285240701
    0x60c0c010905010e060d0b0a092307051801120b0909070509060a150f05040906121b06090603020a020f06071806080c0306040f02190905030708121206030f1f 69
    0xb00a0800c2d108902d610800113406009181c1240e81859032204041c401d40d03602c0c0c040d10700502d1034034001c01c110000c000d088489021841d415003885c18010300403400892056084907410908540f11803c000020801100c5150741001c40c881d505450300350b04041507550380302e04c138010303104500286205464101840614040248040c1c42401d001744c0801c0035080810449401c00f0051800d030001100406003510103026941007000707541d1a0010200700d4000c1c0981c00010280911800440e031980030054034601450390080c81c0014205910800031940260094414002a40103440e01d00c1000304004c0d16142040302c030100001e00c80d03000400c1034180d0f000b201700941800e281c83c6501d03240c501c021040074030000e00000d00070f031390301c448640d0038080980c180c82a1034241c0360012446000ca18004055507410300a1911a01645100142805000886480300880010712a083c00d141d5444040d1800d0010701c0c180d0580070791480006560310522a21a01c0582c0f2090488906007501d141c0302202d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 285243192 1250 285241942 285241949
    0x1401090507021b1c030c05011a04050604020702010903081c020705010506120609070b030a0912030b03010b0a030302330708040309050405040302060a0903110f03071101020c150d0b060c0c0109 84
    0x81d00501840030f2922901c1c031540c0704154141480e86208401e180c100d03007900601030050200d528104a018804840503400c24010030100c40502c03050311203401304400c0b44240c4000901064400d40308000299000c0081c0011103000c050615540509005840a0340e02c1104100d8142e5510300c00c1000d5442c180d04202042e664003401060740e80303810481e1640d1503445004105040c0000300001c1c00c0c01d906a0042c1c89041d501803295007015000b071501030090311342c08070424401e508229401c0e2140c204154008126905071b0700a0001c00b94501010001c40220062203480e043c402d10b01e2650383c00c84000c000d00404c0c10b0350f20521140b52505004201d01680d80150b440b0780c0c284810700001c00d500150681d0010341d900320015005085150650f80c0c0c1c00d601d0300e04003070b40c013035000c2400702030304080090010540204c50442402c240a001240c448107800c00c020380c030002401c100d1107900e0090024065100702400c0010716007580400080f0b041c5c10150001b445135212600b03411203540c2c0080100000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 285244442 1250 285243192 285243223
    0x1701050c03011805061c030e0f030d020c010c050319090306060f0501140901120608100e031201030f030e09010b030103021c08030a0207260721170604140109050702 72
    0xd65040c03500c001c603000c0940f000381a44030303200e40109209580b00a540c5500c2802000501014441d170310340a041e80500e891002d21500101c00340a00c0c0d4180443c0003084403515038090302013007041100540e0b1383c2019035020f50b41171209110601d805040304a410545491365118100414a1880c0020560b0b119401072405112005400c002e00d0342c001c85400c80b5211710307070109a160a41e10004880c4c0403151550aa10141010030008607103501041804920016200c10300103400200c41d52a0789214a030b03c07100d04204800c0042003c501494680e00a1034441d05d40b2403c59109100012a03c440c2038003d4524000008010011440d0000301c202c40050400d0795007460f1081178030783c00041e0100400070301c41181c000918000300802c40002c0d40e90318a98490103d40c086089003d1007041d001030508940c180b00c1c2201c11046a10f40b901c402d1544909aa20385100c2c91501100c00390f11400a0300c81c3d0382064a0b8070001405070500003c86000c1d000041c1c00103440d14210030300034546074500000b1404e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 285245692 1250 285244442 285244447
    0x31f1a03161101050123010309050c01110a0615060e011b021c060518010e1507050711030d020c040f0b01050409090c05091303080f060303070b0c131701050c 69
    0x14102400103603544064081c468003070700080300e10103032072403503a50700640301039480c1c040049200d40324551b00c1640742801d100d01c0781e2806101401981242c80488001c2d15913480045120a113620407541c860b4040c40040560300c0c026010303501c0314181c070181581d20500020219050244562103851103074804000d103032508140c00d000501010902032640081d020707a26400c2c19800032100300d94404078190348140100311070303d400940325114010000185a095082000001d01e005000032220304105072082005c080c1d48516006452540c0000030440c2d0040c0c4140307032005140d40c140032403854001c0e04e401400d5401158410001200c0321402903485203442c0401d41c0300c540c0d038004142c134140e5800c04030020b420406400e240350301d41e000e6408181d010144004100c40c1c6001400d02c8e0502a1182d1502e0780d980e19041c40d0524042011681150194418060751012440c0d1f24400383d000b818088a05141080b0754804802800c1c0d00d4003c1d01a034102d503104402180310034811190b02284401a0a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 285246942 1250 285245692 285245729
    0x50f0a020a0518030f1914010e06070e03190305220f0513020702030601030821010501140a0e0306070f08060f030a080d060f090501090b030a0b1812031f 67
    0x70714034000d5215440c90f6580c0c00b03c0711901510100580940707000704001312407100c1170201d1170704e2604500342c0c1c1c1143c00301e410000d07081030b00105010724a1440f007604003401c256036400300c04480f50f8a0364030f030045d4103100d14141c1d4070003900d042c4560325030386000351f41e059035030210101404a03800312080c4c41c0002034040d1408100c0700b0980300005c41941c03002c9412955031212244100c019000d00d103c042d5144c05410000030400c2100c2004000c641d040c124240e03803081000070000c0c201030092007410701040c840b8041c15041d980342c1008100c0c00c800c0e410010113620560000c02d1130100c0071103003940411500014407000c0c1d80c00950040d88600100c40070030b06180c40401003030700c40c1e002d000004c1608801007520b8140c12003070b0700014042d0550b90a0101d00b07560b162a214040c00d03081c41040c4820b0705d00280d0070780604011841c0e4a001e80c0001c20640b20b070300c82e00c01c070000a40c802c8800c04042d0059200c0c603440022000021405001e443d10807410800200000d400d4408143d4400c03e401103420080c5c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 285248192 1250 285246942 285246947
    0x20604050c060d0219080106110c06040e04081c0b0a300302030c1002040512010207030804120905120705090705040e04110105160510050709050603010e06030c090a050f0a020a 77
    0x1c06070200242c440703075103031a05003c404010340a85150380c00d80c4458032980141280d4000f001904a5005544110b448050700140d10380b145030340c02c0541d80050b410801405201411400103400c10300c20300c1c02524020884ac0b4031340900c00040ca15034001600d880706071441f8600340c00c4101c05421103544900090f22034904c40e540b024120710b03042d07045e40144198001454000e00540c0d043c040410107460480e0b000186800003540103014003032242c1d40721000b041e80c2c074105100b56030701c10b60715803240c0003162129110b00c0c5203c0b080510680802c00d89200110b078984440e014200b2841d1164005c008039400c0000b00069200e005216404210007800200407151918061981194205007040e0450040100407100c51141c05c0c0c40301c181c90400400354080000c0001c2c82c20b181c0041d00701c00c00090312761220888000c1c00c1c40c400c0c00d603c6141440184000c5074080d0840380c1098005049560760350903038010410301001201e10555241c0c4c2c0e14200000411490041a444444c000e41180b800c4200c8002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 285249442 1250 285248192 285248203
    0x20a18090c020304091116030c0204050a020a02101d15010e0105010f020a080a020115060203070606050303162d080c120304081209121803071409010e040c03150b0f0102060405 77
    0x20504800c1e04c0781e00104031b030038440c0100e0340f1184151404451100c124140a0915900c000c403ca000d80d00e008001011112140700380e50300c4c0c40380d43c1d0141c4415484d0f0200c0c40054a149447c0c8441c0c24004001c0c2c204e41e840c100f1401040b080700788420401c56141080d10141e5181c168082c40c144405111a03505040d8081904580e66500504040e161585043d00303e00602e201c804414406407114004907003540c000001d030001c0c61007080c003404107988440905440b4083c50305401994441102c01c13000080d1031909442c0011281c80d942e2200140c50390021121001c0040300f03440c02c040008540310b564100340015100000040400c40c650f09259851038518840c1c0440c96081003a01400308106090602c42c140c10f081c0c44207012900c40042110458801e07020041c2c442c0300c1d22400c100043c050500311034004419400a000c018a68a00405003d00b900001e001305c07441a05442c01100003601003a24081d0308540c1000020308124020034809501da80241d1981903500c000204800148009103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 285250692 1250 285249442 285249449
    0x106031b050a2c18101b1112030705090a0e0c19051b06090114010302030312060307030c0605040e01090e0c130b0604031101170702250306020a18090c020304 69
    0xb0525901c00c1c0031403041c00d48415010103c500f60366004103010b84c21314140b01c042542003010043c0e804010f20807100078102c0314900c0700702403244010607000f40124000e045c455011314000040d10a03c4400100300600c41e4412260031001c46c002092034100d5080c500810005043c03c51209032a43c14640b0303402e8494000c807150304041200d045000080b0030701c202c050315201c04240d220f03c1590411102e4054444030210340100c0d05601e00f81a0310000500095800e0480e90047c2c0510302e4564410300300b40d44180001d00d056010702c100a4000b0016401e2003405005080603a034a42c0c40c0d6080030002030080f0b8043c2e000d01c507201e0602d41c1c490103440e800b103480808404112803010b56070b41103040500c06402510300305c907800700010500200748550022125281c0ca003d90b1140041c0c40e12884054040c40250350764001079010303244d1403043c13030402d001d0910740072070340c0d800b1629190b40c950f140700c181d9104c5050302d800038100e10f5007180b00c509942c15a601802e584c00c41480a1422580c009589008070f10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 285251798 1106 285250692 285250709
    0x20109080d03060e1b03060402180a0b04030c06030c02031206040b040f0b090717010311060708031e09010605060f091c0b090c0907081302120106080106031b050a 71
    0x171543c49250400780803c6040d40c0b42d140c1480000d41108200c401c940140c0069407020b076580440079001404810401640d403402d42c0b92442c145071040d40424185424914809a01c0da000b009617801c0d86600c5600d000c0700d41c2c4510015020b026442d01c0c1c05e030001d20b000a01550407130301d5001908103079020380f900e08a40d25460310032585080011104494081c0c08801400080ca418240e880180d400502c0b41e4103140c603545031003406900c04e45900360b501c1b84602114158032641c20781160b218001100070001d045c9801c002c50320900c039040e00366482c2d40001a0502c2165965081d0741d00541e4014100607074000c0d5842c06d01c18405040e40c414585104150041085180406440c1d05c200d10356a502d20254a680000c1d0048a49030f08080340d100c0d010812480a09500348101c00080c60f5800009c80c413549141413103141c3e212800f01516221402010510042d12110942d100f240d4810 = true := by decide +kernel

theorem cover : BRFrame.Cov 285071942 285251798 := by
  have h0 := BRFrame.cov_init 285071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 285071942 ≤ n) (h2 : n < 285251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
