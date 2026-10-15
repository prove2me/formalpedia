-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5127
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:50:07.214191+00:00
-- url     : https://prove2.me/submissions/83b745de-f931-4551-85eb-ffd24240b533

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 921942446 ≤ n < 922122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 921943696 1250 921942446 921942457
    0x3010f030212150c0a030209030609060906060118060f03021c0b0102191e05011416260f0a15060e0901080303010e040b1f06051201060207060509150c12 67
    0xb03650850007030aa00c50700742d544100e00c1c1d900c00d00000411000400c080c11100260035200b04904026050002c1100020304200044501400962111040090b0700c40c04200558200c07034207083c00d207809034070351807400707454a040d005800c1031002c0c03801d01c841824800c4d812a03c21500c00c4c101d1031298581105140041c0c460101d01c0c42c018400c9020740408145400300b1007501d0303540121480311524000070f01070b21407a41132509403555569450039401c0e01058540036446900701d0340c01000707209214000a0200848a040300c00822901d0800c00501c1c0ba0600c040c81c2c0100c0305c00301400150f03071940101c1c1d018040e1b081c5440d18100c0960710006020b82c00c8002c01035108000c5800c0e00d07440e80c8039070741d50780e590109118030b0403100c001c0d10104011451030164035400c501e01c4898090200c0714000e00a2083d2055840030000507800240c0b003000c07864412006c4e0141c0754500c05040440d00e0218000c01c103010754209584508200c2c00240441c2e031040c41100c0c98549040d09640311850122500e1499800c01d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 921944946 1250 921943696 921943699
    0x120a0903021008040303150f0905061804080304031e0813110604060906020709021602100306050a0b0318010b010807051303231204152a050f07050f150a050f03010f0302 74
    0x1c0c84041c880071001e48841400307881413008e040200916040004000d0301001e0140340d004101101d60720303808084041c1e00ba01c518003401c02c90380e076070626150007841d00004c018902d420498803040314050b29405040b40b50019442105030704111403d0420f850001500c448181e8040000540081c0941c0c001a200f003c8400c1502601d980e50303601c8446905a01c40c0c0501240240c00012000e001407400403521026003030b1601d000600c00380c540f40407460500c06a08201081180403081140807800004034061400c000c2009009680c0c1140001e00702090140030704003070000119900002c1a001205e0034000c5820025010a850483d003150007200031b050401e505078007541c2c000d200215003003411a01103031800d48101c940e6640841007298200360a80c0d002640059406800c9100003600100f424000c0c0035002a05005140c000c3c1907290691343d50003203000303010a003d04e03a810368403151040c1031220242c03d141c0e90b43c000c4104c200c400c2d00c900240740611200110011414005105411080d07d20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 921946196 1250 921944946 921944951
    0xe010c030b1816120905032a0a0b0901110403060501080712150b011412061c020603041104020729070806060a03091e0b0907090e120a0903021008040303 67
    0x4840003404000c00c1c20201210380c8103014000f190640d81d4a03540760215640602e403250080c002201c5401c240c4144010540c0c85500204640d40c001c50181080d00035515030308014a000c640078600551220328418002d01070000031000a85082000e400c01185840e034440d400e961a5102e01d08a00140020b000c3d40c0031074031503810301052070141d10103203542e80754109184c2a80100c84c1d205031005462090036041c1001400c021400f40640c200c8042c01e6803810a4000740f00520f050700901508111078a0b0a4154128011020000d0b031100b00440307420540004108010b18060700110f8068405c0400c000c00c0a044a04105000c00056158941d40b0790f04044034851a2145401210720b4281511403a07400601048481020350080d0300940d407040c071078608101c01c0c201ca01501c0c2c3d2102e0100c201964103d280c2800c00c0102002400401c01038107002030100078600807800303050359030b140044549040410005100d078899014500340001140c1c000e01c255a240c450b518020820541510101c02190 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 921947446 1250 921946196 921946211
    0xc040504020c01051b090a120312051e060118030609140d020f0f0102030708010512070e01180e0318011d0603070c1109070e2b0303060305060901020702150c010f0e010c03 75
    0x801c1700089884040340103003c0510700e82005003180c41c850090004030240180b0946408052040713001d4148181603001400766511264070511010400041c14181005907101c60030790030000f8081814280c90700080001100221840c0106003500744106c002000e206815540400e20350004540c460003074281c040c5c03075400f81141c102d6400d0780420b480700b10120b40c0302c0c00144418100110ba50641c0004c04048460030350340c401481c120b4103000e030000c00210303445102c1060f6041d100e004a0417240e0407440118500320203480c800710903911803130000b410000342d040402c1c408010b0388003410310608000c080703555904000354054084410b241040310700c034103070b485007d50501d0030000c414480c82094a41001c00c510081c10003030180040a50b00303135a103201c0715100c103104484500d2014918400d031400a40d150450a12502d481c10003809096143e00400c4a1001a11800050700301c0c5101d604000340c9508445221034058084080034107480c0740f0b07201f452002e44005400800c82c09045480070030819 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 921948696 1250 921947446 921947491
    0x15060118030f0f02040b0d03030b012c0d080d060e06040b040c140318010603080403170a1d06090402180405070320070f02030f07031b03030c02090c040504020c0105 72
    0x1080c06100151408081104410205046845592241e03100810002e0700281000001e81020703900002940065520740540b101560045243c00b221841741403c038101207000d6005190051009103128069220002100b04102c4403000741c8401c50801c2c0414056640c48881001c4e0b4440c0880b4514461402d1414440751410711340300d2040301d414140c2d2403488030b614454190b600e03640081c1c280b0200001c05e02e07180d6aa040c0c284140303c080c5d48101031041d41d039460750614480f0000241c88030b10751a83d0400005000640081c40e203148034480b86242140e08074000b000402c113000d007204441e04240002145079000c00c1d40410000c0510007220100000d0301e5403a000c8040303498540701c16004452603500c20782c80082903030140103807502c0707180c0c4040d800c5865400700e810f01d0200d0002810766442454184200040010b001550401c41c0004503030a5165031401040750903000c0001c0c0c003a0740c400380881e40b0075099004070360152802500c255501d103006541c060003001c0481e810704030b40d40c180d103c1d1a00d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 921949946 1250 921948696 921948737
    0xf020c0d0b070806150705010906141015021519140c040509040501180308070f1707050c15090c01020714091603060e0a021210080d050a03020c150601 66
    0x8140d006022815070303503104030b8140d4903040080c00c5541c0c09180c4440520260078004002c0240500c01c10001c5103c0c0c034546030074815107408030140c0f050b0200d00c0003002003180114405104940c0c80c944180664916801c0680c1080704054681c0c000b200f445c0204202c22080055503040006000010048910140340042e10081c09441c200c0700d4000403c820021880c243c248103070003c0c003890002655081c02032a1801040c944d003c01c5021400110400100f141c22490a2900100b1810400141003904000d00030300389004040c1001e01c10045100f4030002000c212030004c881c000c01034801c032414150312441d41d4640f0a070642d0300510900c0c6004c21189582440c60364101005030119449031a00f0140e4281d40f10040312040416540704000180084400c401a0142c501214010b0307503603c1c00003031030b03941020040c01842d0410107001c0030001081c002030855030064440c6071994680240c000300720082d100d414000c40c000c0c0314035240c040b20340802c0d40000d8001c0000340c80e41944500c05150f007152 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 921951196 1250 921949946 921949969
    0xc160c0923070f0309020105090d050a020109120210110c0a141504080d110a050303011d0a02030601020d0503100b040e181902100e060c0d022e2007030f020c 69
    0x3a629580c000f58542c004d400010300341e48141422424201408081440261b10301c03015501503202c4420380c802d5580006100c806085c0c0341103446c82d003a00a4020810303591380100540104011010b00c9402c84030140112601c80c0b500070306070354041d50f892030007610950141d51550301c20511845402590821001103d040301c001a01422101e40744120603103200450000212031401429068030008070b040c0000e6003e0300c01030604400384207004800003075166000b441da41c00309204000307008150b82c00244010000229150156507a0b40c0c00024030301c103003120b600182e909500401c020640060540c1030b030744600e105545a160011400c004039a0b11403c40c0c112414940c6411070030405410541440c01092109081694030110b100011440d50b9210714800440b40c5c01295403100e107a40d05004040c0e40c283c00d0b0107500b004d10900c070b03801400422400e10b4080c0c5299500120040840400180f194500700e90800c25203a1850341001341c0016850300c2894014000c1809441d400c0c504240e1048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 921952446 1250 921951196 921951211
    0x1e04050709050a03020d081207050301080d030209010203220503030703020a060506030a03123603030608060c040e0a0e190c1d0a0e010f060b040513060b030c160c0923 73
    0x103c3c0d910716000d00040a615020641c0c00d80b1041206210b40f0002c4480ca5000d010540e644036902e6242581403401c0602035000b0301c08050041054024a0780d001080d00c40300420401c140c1c6020340441c00340c1407081d000c0d82c1300d95010301010843c174040c140c01041c1c012840d4010003003480700f0b07030b10b010805443c2c03400310500030046074241c030450300c190781d85e0b80c851824911824200c1c61001100c10324118060b414089550b101001e240941040503414010100104008001800107042030000c4201a00031802481c42c0700140000107200c00740315800c407125100e40d182c00d940d292075007036104444003500014241c90071030704588001401962040504003a08561803640b0890721105020703009000040c00d091019921400d4072a0310440e1482910018140649880c0c4d4492611007880442094640ca0003d00da18180c0100001705002080340e074819402c00701c0700c1c0da50706414100004084030340d6025004164080c004a4030404030341c0403040340a8100f2100c065500c0e0000c60546400341180d110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 921953696 1250 921952446 921952459
    0x30f0c05180d03140a0c025e11040902040e01080604080f07050a050601081c05040503030714280c050f01020703231b010917030906181e0405070905 65
    0x1303400c14001c2c5800703405544140e240c02004501c140d000944210b07484058040c103410008041c148101d40c00c07484011084c04072011044a801d040700c0d03403c40400142d202d1a208042290701f0fa140d1440f07a1168000102401000b600d039500c1c0d58048000350828060114413004035400402c0c0400001510f82c440e80c0c0c481c07034180c03802100c1980030005400c82d10044420744207408a02000540502c00d5a000e050600020803404080000302140d0184040c1d10000340f10040000780019140882203840e80c6800c00c44501245001c0c280c1c451a20540012126410440d84003444105681c00030b08040070b401166032100c6180c03200c0401c10110b02811803603015a004078410000181c0d00200f406400d00105840a1f0401e003d500e103a0a20f41c1000710989028000140048035680080030340020301000c518001b900c0e94440b81540d901c0c0f01d03c50070940f01d5003000c20740303050040c60744021741420000a4002c00394900550100d000c001001701d8114816801d200000300920300c2064100d0072608014000e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 921954946 1250 921953696 921953717
    0xf0f0b030412200d1d040c0203041203021507050a0f0e0d060903051b0c090705130603020d02040513090209010e060d030e030109080304030f08060301090c0506030601030f0c05180d03 80
    0x503103e00c0b0b51522a403c8040700901c4a5204100c28410800c0a9100e0389800d034121241d0628403080d001011110f41c41245010807400c038032680001584c05842185580c00ea6403429401d00303a240c0704c0544521840c1c2c41601d02040001039108024001322a09a280c454011140900c190b40100352481c0b0690840007013882500403803250b400c00446035001e420850300d48030103920044804507200302c001d041075110000a0005042c41c918140e4000c009241007414554070169203400200584034007410150080f410742c003d10b94550440d001000000d011018030380c0d01d00c85031400707031001440c02d91052048100014165000d40c04903071007840010b00b01140080340b0f950944184c0d040b410020b4243d9a6108403e0000e06c842005502840c00394030b45842800c0b0018004141c2d41d00100928000e03414210a0300c0041c0e14150100192031080310815226510080120001e0480031003a4105c10304207842c0030f0030203070000d0040c492580c20258150200c041e4a0910214001d141e2000740012280c07281e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 921956196 1250 921954946 921954983
    0x7120215070f0c08041d060d0b2706161e09060f12060b070b01060203070305161b0902091e28090c020606010e0315070503060112060f0f0b0304 63
    0x140c820b540b03141c2e4100f201d0003080c9500ca01c80b0680090300080203044200a0800c401c100d0400c0c0c69504c0f45c4211450150540c180d503a80300c0c8204090f05540c03c10503038107101d403660070b82c5035890000814910103c820600d07000141c050040c400c4041d6001240800f0300c1e03200c40d01080da10500c1c5026241d1070314140c0c2c600e0444105d9070040884009410000030f00d47d80d44030888079000344c200420500300801d4030b4840c04d0511804056040c2e01c51000d5500030044100042c0c1c0100c1583c003052500301c0401d110007030a04224514000b042d408036598421160003140c0f00c01140d001d40503c0714280c0319200303c080a02e11003007181c50300c0309000e40d11210307449528080c4a061500c0f41d044511024000c1c0107a0b40d541c49920990720f020703003c0e10160304a0741c100a15941c0c88076006805050407801810301700c0c0d1031511113000540c09402041000750000010311a07901580400d00d2a40c85404100f144da80d69040340c04075402207008080d110150301000094515642041e41d0213540c01c1440700fa0003032021320 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 921957446 1250 921956196 921956207
    0xd0b040f0e0c0907051606090501140708040206090d0506071101230103060513140a05010b011407022b0c031104051e0a090f08090a0801230c0409050c0712021507 71
    0x1300901c0402604000440160200c1840010658403c000c0814001d90500d4600e003911600c0c0c42d01400c02e0301500c00c000103c6d61000401750015016206e890340e80501401003210714400c0140031b4442c4c41910305125100f40d01c485003180980e1541c00811405040b0551004501900183c20000b050442d0043c0302040e400d074082c1d50010200211100804416a2010160503d00c41040d80030381050303d40c031050007801e000380c00381d1503001d107007010030115042081d19003802803200190281c40100c4100c20800c0041820310b0329010030b0900905061017501e00000301f2031246c0000ca900b1031045600904909040c0100d600800e030b16a0003d14961503662280500c1c44001c01200090f500c40d130720000441d00989500b21018018144030790341d424042c042c49900e0031141d00c40d03c1240c0c500706800003451b60b0f05030310344025100d00c2d1a0b1101602e030a800b05100d801650055241d031440d000034003005404190041060710301c682c00c0c480c40d400b543d1000b030362281448040b4807000404d800000d100c09213b42c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 921958696 1250 921957446 921957451
    0x61409010e0f03240907060c060c02070e090304170f03040501080415050c0306010806030c1f03020f04060e01020f070f0b091815040b0d1101051308030d0b040f0e0c09 73
    0x78001c0c00208540400081c44c0c0040300c40711140d104084900c000c00b80c25014089544060305d0b0b0001d014840c940341008105021980c40a000141e80d0490306224078801e0000900038092036480c00c8003820250b510079143c1e030142c415500250f12444041801d40340110350a0b80c90069803002e14101450200103440300d0000510403500440204c1c090240d104440c4200ca01076031503d0502d640f40d180a0b00054401c0c0409043e061007a4070556807012642e0f1200d90a00d03003a040d24601c0e42048031028000d6000c0d008101d02039a00716800318001c24003a5202c047c071a140074090b070031201403c4903000126140c1c0e1042c01855009440e035001480221700c0c8400a000000c00501356103500b13212420303640c440480644a01440c601c68507100e001da031809000fa10409442101d0344200c2d650903984c3c01035500f54074091641070120100da0782003d00d62650304140200300441c00d0300d641c1c030b415080f0340b802480340410881c45a4545141c11003030084510440d605003001c0740051200d120104100604801300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 921959946 1250 921958696 921958699
    0x50a1a07060b0a0e040602040342020c03040306090501050709081903050904050a0b03121206120c030604060227010c0b0402042c0d0f020709110403120c0c061409010e 73
    0x100f880000c0d011185032402c1d0b00c903d01030200107842d2400d6140c4100314000e039100120020a4005020910794080040707525500250806c0c0e01c00061101070100103406454001c00007408041400024065190420006903110343c00030000ca83d80c041c000d4599080602400c000ac0d4004044407440c154060320340062203000f410400d041503009030000e02940d204942c031017041a211000c450381ca04040000d43d00344101060154140b0074174011004440d00000d20381c4c0d00c10441c0d8802c00009400600c0201860364002d8140d440c81d14060401402940c4002c0318601c90403101d400c4141d1125a0104140034000165269401c0111589440609200c00791003030703a0150b940e5182c94101100d540c0202550300c9260b03016100000108180c81c10320480c80300e03c0c4148100f405d4046085a804640d4805540751400e00140d100220000d8440350300450304010411041c03d41400440340d00421303a840d8443c071501002d03801c10703142c400c2240c964190095104241005014420315580960100c1c00030460 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 921961196 1250 921959946 921959959
    0x30512090c091305010c020f0a0201030902132a09050f010f12020406020a050f0102041410091805150415121401060b031f050303031815040507050a1a07060b 69
    0x321000240b00310015103400140e00024030708801000028043c01041e103d1500190602940e81031029840d4003089000034101661003400d2421941ca03226100c00f903803d1210204aa5002902e03865180216022000c1c810343d504c140000d1391724410b10100065070b1000e40320011102c010001504c0030704030801e060080c000c40c0d042900417000244044c2c8002c005550003030240c0f00d00d5040c181e051403e00030200701664010041400744e400841000d403107080c81500c540700d12601e00c400c21074003501250040354111118000b03030845a05240c12070b40c02551075204031501a0182010001240d0020034000c4005101d494200f2440c1800b081c41041c840c010071040c149240c81d110500d085440300d4100e40111600802808600c0b0040850203441041c002c483e1800c40742040d00003036480c0801801d0401d0000650301701801103009111102c0d2500c0212902c0e401c50070a07142040d00c4c0c0109003d810300400300000001a07207010003250741d4401105030045460200740f51210806040e920344200d41012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 921962446 1250 921961196 921961213
    0x9031106012907390b3a050f070807080a1a04111e0c0604020d0c271104120816020a230901061205090c100809010b010c03051209 57
    0x1135401e607050241604580020401050400c5114201101140c0007549540808810300c400c1d9000b43c100ca80401c03a00c204030a20480c08034201088401000714100b070030030550391017848001c40d50410f0703000d080324041e101400d6803070038812204444101c1c0d208000030b140380c01142080703007581e10040c1d140c604490381101201003440420305071481510f0410861100043c2820321150104000341c82022072040d491500b036103589416510303000588080e03c9007020a0450341088201128003004110032042441e00e459169848200c107005604000881d508280150b0401c46048d811201696001d1500c40702408880d11000265000303229402ca05180d610603450141ea01c840c981001404440c0058600b500d000070894401c4041d003034020b00641d0008010b01c001a00f04c00c281221540803c00050266201c076181407405900b1650f10340c2080c4940000500c641d88503900912401e600710080c05000c44c02e90046680c2c14160401900203401400b840940c840c1d410011600696680112003609 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 921963696 1250 921962446 921962453
    0x18050406030c08010f0c080a051906080307151b0e270915010f0603020304020d06051e01120f150b040609020a030e0a260f03090109031106012907 64
    0x440032a0015600000040c0c81009851800d01801280381c0e40d264041c0800c141c034010140c400d0001901c000b0b5082c0d10b074000110038222075a400c010300a01d0b10424003c1c107a6034015140ca0340c0c40100c0c01d0f00d080c582ca62941c0a001803a000e2b05c00c5003040120500c000001d101d000710360a680419140f0f92004840c04e0b2640e40c9042c010410080b54420f48030f10080d0305017103103080e00d00040301d0210070b0401500c00041250100341e1000e6004c82e1102d0402598943e5940b0005805520540c0000e14446c501814094201020341844032158002c17902c06a543e40c8814002c4e2402c0c0c1d5a41c0c0c002e00d80d06400840d01d0006940c1400c080b80c51303da02001182001c0c1c01030000d825202c90382c101c01070301503000c60308800c01703a81800b5580c1120076a002412545c00c140c0c83c0d100d841d4910942000191080110203210a2111412103044041d400441920f030b01702640c4a0b400b8128440d02500014004901c0c5c1d50304000100d0030074101c414696200d01110031035000c50041e12044168050054028007d50010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 921964946 1250 921963696 921963701
    0xb04060510112d100c090509040212061501031d1c020304080106080c040516080406110d02030a02030402150a0c120e030f0a060e0a05030d0908130311040c0c0b0601180504 75
    0x4200c3c9405880c0d514010070103a80c07404d0301c1320140b088164105808550629000704203c0d094600544d00c5c2e85c4990f0359400400c440c411800c6940e411481102d040081000917003035105041102681e017402040313015141c602d80d05c600c03040200120340254950380060b10fa8103007188544c07161801568142070b52160400d084034401e90044d80700e500040303c0b48042d450103118042e40001c0c049140044250320044c0241002c4000300b0040c45540e5800c0100301e01030341002903c0715401d8210055640345040507888019400c1a5412405160400140b220310500c81c019035044c0016551111243d1031241c0f0344048205d0840d040e1004d11000d200420802c5d1014032034004404d2003a00288050211413074841d045a000d20540304a50b08039070411000100d000c01100ca11018051001c5140c5c440b80c08e0442d4035200d000802000b1880085d000030070002680c81201820804407400c014038111282d00351403949546200500701c454000024601c0d40c01104246809100125042689a20b0f070700071608 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 921966196 1250 921964946 921964993
    0xc03020310021c090b1602121c0608030a050a05030606040f031a0a0b0d0213020405040c0c0506060646050403050123010317070c06050901030b0406051011 68
    0x99550300020895030f00c404444150880502d058020840d00c182c5407505410f10201402210100000403004442d061082144a407481c034803001c801d55488040039185c2424002c0051014494101200028848030100a4078560300e080d03150985401c070003002c00c0724a1391000700380b980c0c000818803001c1070f244075480020f8041c610030750091030343c500303c0a580ca03244c50300140b0440364581030105144c02c580380c0c104940e41659041d06c103100845c1744548014040c6c00f0b00d40095810501c1d04010a0a041d07003c1d2901c80c0c51030003030040c0c507020340320314052003194840c0070300183d05111045103042d2601400e00c000c0e007003480444e07011401c5d0408504442801504490440006500801c052085c080700384074286202e111681c607030b20101180c168801c080b083c14840a0017109450034070105100c190b80c204c80c0c6140d88013426001142d1288809070017038020250960000b4078041c43c4031401d0410703224032020b84000911a019210407071108407103100d920b403080030103401100000800011210000f82 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 921967446 1250 921966196 921966223
    0x8090a0b01120b1008070b07020f180402151201150210060603020c0705030105040f1412040b0d0507111b040b12010203070f0234180b0102061803040b070c030203 71
    0x5142c600103050440324a0b002414000090b142c2c03210801040b90700003032500480c4d5400210f19281c490a0002075082c49120403e590002c00d035080b944001d4100c802c80070b205620859100c0d00c100b907503c2005070b0a014030b80c090098021600018800142c0c0c00c211102d42d191188111a1580c00a2001000380c5209a0112021a402180d0301c4001d80b4107000b6900501802c0e402004940307404e031291000b0703d034007501c041d0096224003035941c034a00046c40a40046000588090794540c2c0e0781c48040020f501c03580c407140e51300d481c09020500551103000e00080300740d0740c10000c2c02d00c00388442948030700b2541484040d50162f0303603651140d41c0791111006942a074004000040e22813500d00d070050107840f254180c100449d0805042e0024203251144c400003007096009010f01d03840798141d018400380309190052183e800c6606105841c00741c42d904030b200000d07820f9083c0c2d07410b521241d1200d4010482c0068080300c80d0018081441040e60260180100038054105140841e540b074006c2400c2c480305040f4070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 921968696 1250 921967446 921967469
    0x1e0607050f07200a2c0405011b02060709060e011707030e240105060f0f070804051c050f0712201011070e040c05130902040e010b1c03020d08090a0b01 66
    0x180524030b0011041002400d00b01d51131070f00a04c0102004640303002c40014952150000d0001c030f01401025480041070640f612904004c401d00c82741d0196941c00211079010004000000102d00d85200d030800c001091010385074501056140280c85200707140044c03442c42055500d1140000d07080f070811900840d00c80c60fa000001c0c0a4a54944052a403416008075018044c104404140907245100301c801710840358402e1501c90401385402d8401c0c0c400d50780b00e5548003480107081392220180c80b080318101842002100c04510454480c01d868810511a040149001c1d60003000401c03c440800c032480e44200040c1d495010310240000c0341c20110320016400201030000c4016000c20400052001d403c0c00400748120745080d55455000285a01440340903000102c11824aa01d044e0059031a00d94024424410501c602e102180240402030049120b400850860758444000c28100d080890305940503010310407501b40e003910442d4003d010603040d4031520080300085290900c03d64040d04044922 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 921969946 1250 921968696 921968753
    0x908030c0a032919080303011a04030f060b0f0f130c17090601080d030e1002090301140f072d03110408010e06161b020108060d1703091e0607050f07 65
    0x7800044c0c04070300300094480d006400184201c40c400000c6d04e04450546640b00700d0843e004285d09031501890740001c0411200b640c40d58104180d6400c004c11500c400d5440480d041200010454031406128409801403600c5d20002400c8443c2e40003101050703041d05042001101c9071035000d4507403608859040b139035000300c0010300c1031500511038105009214901030180105070314406845201c018034044103968001094042610290403c052481da05a1a84418030700402c8403085800200c509600080c001490008810f00313150b0505188480c01143c0100c00d04d240b0301c10390052001000c0c1c4c07005804144000150711109005070000c07011008081d00c5e0605200c11040c5881d81383c5514003041c1300b01c68001084040720314100f00c0c0b41d01e070240f030401c1064551398042140761500d00d002034a03900342c0492b07407000d84c4c00c914011402488810300711074003604041d1002d85c1c8080ca000380c180d00c0340c0204010614092141d000b03001005001059140350070031955800e60f1a086a44440e08101c0180b900c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 921971196 1250 921969946 921969949
    0x3050d09061707051b010c02071e0b12040c050616020108130b04060c120c02010501050a050f030a060e031b0a12050f1b0309060a050d0e010908030c0a0329 68
    0x11500040146041c403007034500140000c0c2c084032100604100400001268aa462002d01103164051000c8400200405295003000039101da841c3e0190305015aa0f05209001c3c80000c500660106e4002441d06828240420070150505030007a1050f6110b4440171004115540c0c5c0e1001003031118454160303440a40030500c00500000001050741503525403980410f0003240d000c604483c0d105a00038400112222249400d40d80c10280442c8007070301c5450203100c81035550701582f0140c141d4100300e520f1103803246d88100b01722400000c44d00858258100d001400e00142054003c21170a54a2005407400c0500107511401c078440301c50104025075011400150910000c0d00c4242c015451038500945032003a661040c4042e44103070b94440628040d00f20401c40c40d5402802079401403c0024005540c4103032148004049030003030007038000028070b4a1401a0391520500c550001c503540810300e682190740f0300d100752019400c002082c00605854031159042503a02c0984e40d15038400301c030a0821030450311070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 921972446 1250 921971196 921971207
    0x132003030a08090f0304150c0201020a1203021c0506010f08040f020d0b060f030c0618010210230702011b08150405010305031b37080301260a03090608150a03050d 71
    0x40d0804900d1700708010520000c0c00203107000c0500301c4541410302500d181880101d00d880c0351448058581d0400404048615516400405910105107208040c807100010400100e542c1038511710302144510747d10f44d4036940030b000e009038800d007e610204510b107460707004606c0c0d04007005012558200c014003041400c1c0360051602c0b62aa10641c0107004014001c00810f0030392003040c071217a4991000f850000d00e640c2c400c0008501005000800b40041d441499180c404002d55034000b02c0b51810300000142880d105209901514449040902500c44040400d8800d1f100103440580745007640044081961140e00485d8000d501c80e5000b0b540ea810001c110304d0b600780320b0903460003440d0010400801c4600105140d0036420390f5083c52041c0c403d251981c880101c13881c224008000c040003100014640d00c811071106602c42002400084043c3d0710b1482179102c400050f0000c0210b60000d40c00d000041c81a100c1541c84210010050b0f064180c00303000401c3c061b90350b40121155031081d41800310b110780c0003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 921973696 1250 921972446 921972463
    0x3030b0a0905060f0f220e0606030a080f0a0c020d0b0a1d060a0c020a2a090501082d0115051f050a030b0604150f17132003030a0809 58
    0x2000e081200f402d098000510400c61000d00c00c2c49101c5010480302559108100000c036103a004911030b1b10806404080700140c151a480d2850a010303003000036401e0700700804d0210802c0d0741301400914240c040d11000e00389401c982806800c0059103403d18005841700340c0c1003100076000d03100d149107900d0614030100940d001e498a6606c000000801d100803043c00081d0340d0340001941e007000c500c1048080c0100e00d0441c2168025150a03540c1e01c004a00310368201e610020303441d03c401da501ca00b0343c40b003d5140075584203105160ba141e000303c0d403d0400c0074641041da580c0c070924458040680000090780d500303485032200c240d090b4412458040000d85031104c100d041c1a00001c0c0d2401c00144070b0309002d8814020a250f110905032211100d041c03030b03a0768104035805082d851004402c401a00c0600808402c0d000031410003040e0300c00d19003054001844541e9110740c030280b10001483d141540c80e910001822144041c541d4600c00047c0d0203030350144090705584100c0d9070340780403510b08040d0f014a0207090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 921974946 1250 921973696 921973709
    0x30718050f102304120515070c0308060d050609030909060406050906270f0114010e09060f0105040b0408010c021c050304020904051005090f0709060e01031212060303030b0a 76
    0xd6070300100540d226030300000180c101c241400903100140c0c200c80303000094480050741d12110300040105180b6507410101001318060011211070301d40300310359580002c1e403e1300e5a2010071109802500024030642e101c80e800b04002d002003115a1f1166151031401c14162200c0015800200d80c402040c01d19642c6982d03c4502101d0501482e880c0002181c18060050540c0b07005011170680c060a140078245102c0680240c00340c0c111151070800c80c880302c4001d0a0042c03070b140300e12540c440c011a6115100e000940301c1c005000d45090785490003004105007a481e11641880828040095108080406400140081c00c00440c0b03442103600c00a0500202e030100c1d60700d042014181245041d13000040e03d92007039041d908031001e41c07103a00b00f56251103010b85912010500303081c10800103040c04581c1e80100fa10380400c9500b0399851704207203020703190140681d515010070000108085a00b000d1442d1104003181003050402c05400c100105a404035002030340881d40781c0f00702641a042c484c0110000703026 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 921976196 1250 921974946 921974959
    0x110618101e0c02100e0102190b01030303110c0714031f09050c06031b0a050c16180b1302071b030c03030206011403250f03111f0c06020c010b0603071805 67
    0x120b0364006141d0030704429504003002a02501d245c516402000b401c044120b01c0c041240001e641d40c90151100282400f00b140000e00304220700e40380358054810384404100c0312001e04445410b08040d581e9500700004150360510901919003000300941040380148074001c1808595100c580c2400e40c03600c02c10b007007000e01410080042000700b24000c00040c0100d0740b08007200e651020100d008403805e0240d00748107180c1e8022000310000f5401303400f69400441d600352103ea580e82b0740c6031100a007140c4440d40c1458104400c181c1d4828803134116401001e1040c4188106000c02e5600d03c1c43c0d01c0640300315041141d690202c40018024590100491170040142d034260360240b140a0340442d80700d43c901002d40341d803516100260b40390120030111140c0504010308031280001c0d81c1e4240300c1d42e004500c4107020b004800000b5845d0326070f030405505500707a25064551070002107103070303942c0f00095001c1c401c540c1d6155a20350754a03082d13a54203801103014000c6030b55500d0400300c0b1076461404401b4941c2c0035620446 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 921977446 1250 921976196 921976217
    0x4030c03200a1710050106080f010609120f02041b020d030e030a091202011e0e01031104030503090d0c030f14010c111c030605030109080415020703110618101e 70
    0x10b890b05800020b8500344141c0500524461801910b0445054291812581041c00100e44075602c00a250b00c1141c07256152103241e6680d01050b119000325001d00100241c030a42140301041c00e22480e02e064500c041c0c40080d41e0800c1003249002c2e441d48811480058210031580b40b0304035410f000b8410801c0e50305015501d0194460f40152101c0b40724480c0c007203c2d203200e128000c19603001d800e4203515400c0000305420403940301400140108019501c0d0346c003113403401d5074504569058005880680e640640150b1030400c4540070007040d054101300840c0d84040380382004c00003442c0784118405142c030454602000c104440741d01360a44012080d40c0c81005140300354100b072441d0019019020f085000c3e14100c0b03418030700504402421607904519015820318070110104071340140100111004800c0d05090f1014094040341c81d00340c20710010786580c3e07100c12140c126142c80c0b001000b840084607194400ba003d03040c00b198400c01c035441d140380802c2031241c0443e0b104505042c0510041040d00e041c1d030414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 921978696 1250 921977446 921977449
    0x4050901060513031509060903271505130b04030506060a050301090b0a0b0a031e02030d021b0112091a040203060108030a0507080d1503141006080309040e0c040204030c0320 76
    0x11010704c406059081d040e40c0032452441294801d0401e280c214409203d51411401c1c0546600c01c0c0e0901416030312210384610130707154a01c0b0041c0068030640e0000ca0700d14516410110386c00d40051140c80040c0c120a03900041c0512454018802940700303001500041c174008003000401e412a40c81940240d0510f80300100058a19508542c0820071040c00a07840110801080c10000d04d500f0080c203000d0400070154240b1440000483c0161088045800000400c0e00c100c0c0c851481c1c2c1841b40d0003034465514107615600441c80d600d00c01081800024a00b9000c1d180c4955801c2003000c020b0350310ae540402c0c48190709007802030758003404080009500e4a882890700401c3e5100f091009844464041452000410320350031100c00f0b1003e842d40d03024255120b0502c00c0c842007809002205600c150306030303065003040c03a00500307040303811700700107942020000010b10000d03002c05e02c441025402182814660780d9900e03c060700245000e4032004020a00b18a030800308441c00d00c10060178040c0802040055 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 921979946 1250 921978696 921978727
    0x206071b12391d1b09040c140a0306140103090542063a05120721300b0a1706060405060d020d05030c060c2205060d021803070605040509010605 63
    0x40c030b800780c1d000a000b0031f20a400315084266100003403000100054088000395040c1c00c09829a00c00100c2980d260141078015022107070034001c0107006070412810fa0301200007200d0850040107449420300d01d0404c082000c0340900504d106440600c401d01802d10000f0b0400034110025601c003050500001403506114112083c0c10015030300005040712030312002c01c8028030242030050446003846446a47ca03103000300304100e507034100c0200b0110301445034550b40e216a0822070350300300704c03241500501c07030b0b401ca05040042243d680140c241d441e00d224902c40d40310552104e005100e100b240c0b06a00580e440030500744070b005072015201e0b6013004180030455071104020300189904032002100c840092602600314000c1c40400606801110104200c02c01d001000340351480d120200604200044186215500150301500f82c00a40500c00c070004070809500400448200041c0040502003030400030307182c2200c036009035000640111781080a424030f41c0f1001c2c05031005003007581c10010300104d40f880 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 921981196 1250 921979946 921979957
    0x10032901090911040203070504031505060906100c02030d02030309100b100e0310050103031d01050a0804110409020d050115231003090206071b12391d1b 67
    0x40042d65090b2010400540b030000c10303010341d07010b00155124500103002600795080340c4010384011030803c0b414008124944038242c40f401c401880814184ca0300401d0007080c80c2042c15607000d10510182ca030001d81e42c00c01980e9446841c070341c0210398a14010280600f0140000400e40010381800170300d00166803280915500c058240c5441d55a5141e060006450080d50020320600c2c280382400100c00c4c141d02001d2124030f0194501821042c850380d400449142c450b03030302d01030000341050001c00c0002d141e41c54010f800703040040c4081094065500068185951002c040781c140e9501d100c107200c00c83c0c03030784040350040801c0000950200c882c40b005141d07420600b10414450b5612264442140b400780c1e1080b240f807500500f1050300d401e420b2522005541034010000005c01080f00001414505130042208440c0c0c4889801285200d542103895400701c0036240548500741d0101c0c034604c070305408900d90002d1816110590f204c85128a0350501014003600c1c2400d000050706800310480d2801040341e6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 921982446 1250 921981196 921981209
    0x20160632030403140a02010b010201141608090f0d020102030f102d09060b0a02061b0906031005040e0303041202030723120c010c20070612090b10032901 67
    0x50740c03541d41c2d01c0c084980c81c0360040c1c050040c0c031011403403801d100e905600105e009042a0000c0180f03013108402c80c030b0340c00421a0481c0105c0d10f16172030354042a100309101e9400140500446484540321110b40742021314035060000140e40c04020010580d681185968200c0300c0b100081c686281420f941290142d415081202201c0c00044111100e02000d0000002000782540401800e42c440803482c0c0760383d1000815400622a880100300170b401e0300020f840c501c2d28803000b1030f440c00480380c040c01038075000240b00c80380c031080305c580015050300d03a8000d050324070140c80e020f190360b407500b450a0000309218002d0241190300a120304d4001641c09d072000c04554569003003161075003001e048140e21f080301641c030074040c151000c20000f012100541003041c145c2503649074150004004401500500c443c2031140d0140c0d40120740170061540541150b9181c0c80511502007440b00c441e45503414000020b403840030401070851010424082c5401a40313010316080c500c072608220081102411100040c011340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 921983696 1250 921982446 921982547
    0x20f0a03050a142716032003030405010f03060f0e1b090102060609270138010507051011041401180e060a0f140103111306201606 57
    0x602c0111000f907085030205007103003260540c10740c9002d00c0a03408461b21044641449584284500e01a00b40c20103140d2800503000b18146480c1000444048816602010915582c0c40c40414240300301030541c0040e00c4003850001d40e50a00081406a9070915816403d0180007403140c50b507140e0340414082d0308110202c071000f0b000c0d21303152440c64060000101e4042d00d48622548840d6048064004940440f1448405103100800707031800c03201d4107107600060382e001c0003010700c4c0c80003980542c010b0006c0034050012107048a6044044404880d810806002c1802c0082400c02040454a2061300060020302c0c00e186599401040385030441c0d41c1f030280740e82c580c842e000000c074203499908804006140310003d2051607070380d80c1a001403c141e0141c8003400a401d00d4117039100d0b8182482220b154500d480705100071181341004c03ca03013074455010b0210a5859000000100981c1000b02c69000454004151100780c0360800103001039090040361511042900780310351802c000e03100b401080890800c40d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 921984946 1250 921983696 921983731
    0x516030e13051e060a1202040507090b0a090509060607031b080c150f09061605030a0920130e0a1e0f0f140102041406070302010f020f0a03050a14 64
    0x1d18507a000e10304801d00c007807500c81081142010710b070001d101801111250050f50b11640140801c0003146c5c09415280200074a80f00e00504113580040e5100080f41b400114007034452039101099840301156100080503008140000d141000049420040898155291005503500600b607c0240c45181007480700843c6418140100360080300c2c0c0009840c1d09450081030b0081b0080c1e221a01a103901050222240c00101c601c00b002800c6801220603a03540211380d403d510040740d0a074401080c04c0b0156407601a180009005050245501551b40d46000c20f551201818000307280c02c0d1900162849051400800c6910700c085002d0b8212038100308030820031440d00c0c915080c0181401c200504080d01700640d80c0c01c2c40b0307480301d800142500c620280d01c0300b02020309d651421b0740101e000c1d0382e032000745516682e241c0303240c40e90082012511a00002c07e0507000c0014036400c9801080d000d0200520024483c0889a8140700e281c1c1c0c0190003c4080000e50311800801114101c024a001146051801e2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 921986196 1250 921984946 921984949
    0xb01020c041d060906010803190e0a09021909061d18040f21090608071101060602061906140108071701090621020108060609061b070302100516030e 65
    0x21040c0c4410281040c04006400c0340307010490703020405011124050340b00401c111300c00100c0c3d010304172015040218142075095030503181070341c18405a64240050050307290f0540d12000c08950051049810050301d43c1a19500459400022113681040109400c01440000d0b080610b034884c0340481c0480d0b02c1d104000c000450200910300059101c58910b02c4100001c000303500c0c84109505215111a44040c200424130582d21755401e4240008102401800d0000d20f1241000951015980c0703058045c010060032981d003101e01a410050060300408100203240c640a0740345188041e851000304001c520b420105084141420440c6042000080c0031842e01849000840541c450300c60044205580d94070303034030000b0015481001c0c016034007000911080c8503052561021182c040c0c4441849680301030801900b5440300d031045522810900c00b105070f4241842c400d01510304642c00a100705810360040240101590b0b48200410000700040c0809036810a21341e00740c260315042c2000842800030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 921987446 1250 921986196 921986203
    0x6030b13050c0426010c1d0405040c0e0f10060c0807120e03070803040812030603060411150711030609030f0a0305070c06050a0c0921030809010b030a050610060318060b0102 76
    0x140010301134070301c0c00e0f0030b032201c0914500051800d00c0b40340000c000360030720030f0020380344d54641b0200c0c10010381c0c90410000c800e04154014541c428400c00130303c14035540340c880c2c8801c135507030681e071000c4803108100030012446110b000c070718062700450500c0c0060004650394061a4070490b88005d00d140c5460100c410054082e551070a05144010203541e1416280c40207141e0300c1d0424418040b1a105034692072450340403501c01c5901030640500a0301003562291507071040c03003140c81c3d619a00720303115841d4040d501002001404246205101c0c02d00e907c030841c0c081510f0450082c2c01601150820030a43c5000c400c0d030070445981100c02d04010550b42c0d100041074506003010380018103500e003000100003102c58554011000c141c0103454224415071151034840e001c0182d00341c1520b512020700c3d0148007103802591215844180c2c0e0303001007010505080400d08001c8080000c84440e84100284000c50b4185800080601000d180402c03034414044c100d540000c1e84907501601310382d03645444450a0f4401d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 921988696 1250 921987446 921987449
    0x30b0a05063a17070f030e1c080307020a06230618130c0e1005040f060e1f080334020f131d0318030c13020f040305010e030304020a06030b13050c04 65
    0x1100460340710134140c1410501c00002d00421000602c0300f080b1041ea81c907014050300880c000401c68248480b08070360b128071302c540c000f4151005510400740c0795000101a40503000a080711003054484410701c0584155829501800b141d1141038070301a40e1007410b2074000d01e1584801481541043c03400c603800d000180f180241c00c491007410300d0300201f05040c0740c040ca009c0c0458006560411902e1000c41401080712141d000391020081c00c036001ca868403030100c8103a210403c03014000304245556000c05480e5030b0241c0303141801c00080828030780e04420b942150002c1140e210022000310141ca500248045040b4010746206140c0c11851084040040c0d214500e550318044450b1441c10840a529175280c21140d250392140207543c516408904002c158405413010140000c14010030706a08407000c0d4003c403190940307202c0305000c000080b80c3c0901501407011148000f85a480c02d1a006010640e00c0c00e0b00b0080606050402041c903545135600c540d00700c440c005100040a8950311b00304201403045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 921989946 1250 921988696 921988733
    0x6050a05060f13031a01051002060f0c0c16030b0a05010609081507050c0a0b150105040305120a14040b0307091401080402120c1905030d0306060903060213030b0a05063a 74
    0x103100005c419a03061101c0306060f0703101154040000701c801e1608036510401101e1800c02d91541078041900381c004000900080704220301640c1c400d80d20204520403001040d8425151102d80d6411701c8401e4801e0700c54180075018074907001c03100c1403c0459645e59100c9125501d05040c04240001d00100e1251040d2145880340d24151010b81c409c5040c403004404059408100030f075000500919158052000c580484e41e200016000d500030754003c220300b54002c040c542c824000c05407a80d0101c104010010000303020b41513285603c0e828503980051031003d0340d41115050041c110b4000b9a02e0f80c004450690159040342c4017482081102c030034a040002003070400e90000c0030380941406051181904e442680d0080d0210740341d0065080e421010758501d4461000852900f030018008100160018000701c0345251a0907a455500e65a4207451392040b035420102941d14010f100340340c076241c142c0310001c0d00341079044034070710030f2a00c80c0b0405406030110101b02103800d03854110400440d0305401100030034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 921991196 1250 921989946 921989963
    0x1d040312090503070201020c10201e0304170c010c0f1401020316120213031401020f03010605030a140103021c06110304060203040c090608060a09060e06071206050a05060f1303 77
    0x40740c40d02030740d43d4214450890140c0034180ba00211303030400c0440010f0b018500c0d44d0b0130516143e0030300d401c0c1d01403030a040000e40501900d14102901e0710a20701d413800d902c0c1240001e40c0d4840c9040c84480c40381d0800d801300e442c0391700652041d80c0c41303a80c070040c04040c05802524450840a903480c200300a0a19540388050035400801000300b5003040c0c2300d0b2021001c2d01034440f40210f0190380724a004a102c0c032048280c0c44240b00c002800800c0b980c0100680c8212524001464130b150308000600d1504264440c10000b0070010402451881a0059201d0b003016040450140c0d41168009540c2440d0101e4100f41060122444000e00c08650010f04407440394440c801d0741d034140741c00c011300a0740c000c07907040d2400c400452000407a0b615900c1035504543c0c03d03001800c01500d8005c0316201801810206503946a1101d03030a403c607207000d010b00c3d4000e110740c1e140d0324030010310003180708199106a4003661007944001703000c0045880d00c100b107500079400d0140959681c1d001024190014002d5003028200341c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 921992446 1250 921991196 921991211
    0xe06060915030105100503040b04170f030a091502070308151c05070e090a0803070f09090c110601150804060b0406080304030303050609250c02012109060609061d040312 74
    0x20700c1c10000354142e504c280c502c0120002d180e0401d4500d03100645004140e100d41100142c0841c01c1107012645800c0c80c958624a0040d11000c034070303025041074959103141c590341d000e181c042100c00c8100d000641c001d01c000794101041074501606240e001881c4240c9000c66681000c0d03580d031150718082d581c417000c100490003030324103050095560109000d070300350014800b80400c0e6034840015841c42c0310369000c1c10503885c1d903464840032038065241c19070b91018401180000f25204001d40038910302807225560392840c06509100481c90b041d0180d004000000c000c0e504100690391012213250302a8129201003864545030f00401c0c01041d16a00910440c040401d001c0f0800d80d1640160b0702035842150500c04686615803014140070f520081e64600c02440c1074040030050150094181e4180141014001600c0c04001504100a0005051030241d52200c82004210480c4642e0b0045c001740e00b02004801e08105011003242603400010a2400308034001500300351040c1141c01c95942d8141d41031100c4c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 921993696 1250 921992446 921992479
    0x711250b0c011d030405130b040605060403030e04050f060307030b0c12130c0e01140103050a0605120a02031b01022d010903090e1b2505150412020d090e060609 70
    0x20300f0a00141e140f64a8500f03c10460120300005540c1070b18002090b92003c02500f511140c010309404100d030b41c101780c0740c0c0c1d000600ea42c0e03540d016200440c00387d102e07010120080f5040000300d0344010854402a00044280940c1d601d001403600c0507243c1c45940300c0c0580d03c2d0781c2100c1403180200800440368146130010051280d04002024100314440c550020505841301110813503502e09000d0303007906129030041c01d180c941c8070340c03c102d800c4126000c0004071941c4602c0030900c0c4c041d0101001d203260344041306410440c2000c010b00c000c07030a24170740342d01c480011090000751100f1901c440c0704c00040840180318512610010b407940c65008410007041a88001d181c0640100d41030700c80c54413409504000a00010007403070411540e40b030065a40d81c64503801e4100c5490816108d07110742070007146a02203800240c010403900c46043d070400c3e0b0007000ca2410345811074564a1500d42079085420600c84002a13a40140f0300e0425a54500d891101703da03240700100300780740144007000d80d00c0702c201c103846100f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 921994946 1250 921993696 921993701
    0xf080c1918090e070f14150904090c1d060f100512040b070809011e0e2a100207080318040e030a0908010c020109021c0206040509100603050711250b0c01 67
    0x2603d20100f500d100356903070748a02e1080c0c1751034854500c4400c43d03407085040502d890070915900708030144100782420740c1c12020404444481d202200c006410660603c503040b030540c22450210082c802e018518640003000c40c42105810419501514000320018110b50143c4103503040442c3c101d1081c0968903140c10156a2040c069481601040003600400e45880040c010300a01c04a401e08074030858001010b04001020468150500f40c020001c0b0300303403d0412030b1080c8c00018803a000d01a1035080c400c08001314194411030844c29075020741030401003498080b05071005140000c81070810300359040081000307020b450a00c0043c500002071061003c030382044420341958000c4d8001c00480f04050801d9080305c2143c1c0e4044c2d44410b0f400e0541c9524042c90707140101c141d20181401d0b081c95983e81c0881c01040c1c0560306d00c8886100351a01340314095040c0318181d0300803950320b00300641c0c455448010340c0726044403202c0e19180580c6602041400400320750b0b5401001c4001090f0340c0c641c0c6541603a0b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 921996196 1250 921994946 921994961
    0x60d050604051003120f022401141912050c121b1c02060325021e070b1b12030c0d061d0f071e030c0f080c191809 50
    0x100702c1c0740c0301c04500a14041c5001d03105503a400f02c8049400c1368864810350b481e400303111030fa13000c40c8249090300c102039469000d4031814120080c4408502d504203850850032541081140340500c99280b00c44881890300f045850403182c0189100745030f040c01d03042c1181080b910a6a01d41c02c0503030415030000c041c8000403003240310081581c0c0c00884800c2c0004001e40c00c00240b0660100c10048101c0030007600e048401590058105003044d0300e01d0900210140404180d800690091303000702c041205507110a50000080f0200c9002408100d030401a440050b0700070301d801c0301544070f4441181c2d0860f407010000300d40d2104220092030b403a85049001c6100f41d0f8012112140000d0401000103400004c0d000c61480c807001c2464400d115680786180d00301f0001c0020140420091060704801841095440d01032500025550109164802060152242050361720040c2001003500030000280b01c20001d44a540030740390b1400c01807940c039546c200c5041103000d44403000540500b400040500241d070100c0d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 921997446 1250 921996196 921996199
    0x80922140609060904020a060f02010209120a17040803071401090c09051602060c0d02160f080a09050f0d060c0210060e090c010c050c0d150e0708010b0625020d02060d0506 75
    0x70301660f40c800a12010310341c20703600250440041001403000900541e041034414050784001810141400002041140803224006044d0005e0710b0395018840881e101c40c40030598002540d2925181036140d0b03549110346100a40501d40031140249034044c29003102c4902500500e101c5e2500f81c81d074102d40000c0a064135495402c0c080c000d4030700c103064000b10300741e4415850120b0150500180b4a2560080d500c04511700d0f00d000004103911000602801c1074520301c40c092040c554444400341d03006040d0b45034580005104240c801060203240e030340c1090540d01c40d9884080465503120145040e49028021185020a0760a045011402e0a400f50406105078404c204403419580580011344100c204400050090b410103885460517003403900884a80c14495400514001d01c0a4103002c120381c09000b00c48200d402100f01003040000902550755100012290700345816001d04048030365841c6410052071141a598410040d9135030607a210303401c9038020f000580c0c0c0310092441d28009080072203140e0f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 921998696 1250 921997446 921997459
    0x190c0201060f12020d141204030501050402010305101413020c071712121b04090c0f1106010627120c03061104030c140d061503050709090809221406 65
    0x83d643c422001d0312840e454015200c0010b4001c1d645422044070b20850613500d052040c7c5045642d102d0240004000541c003910002406061500c00182030315805400c0d007607004409641071084140d41d0047c900e201004441e8850240403840140010340524840c2d08034602500000107400701d5103000d00c01010b0084819240c106e401390300d40202c0703402900380001e101c141481c0040c80b86121b96404542c600c5581c9101c41c2407980d2900988140c8000e8204500058810b20480d400346070048044c10200f0750541c0588070310b60508100a1080c0450303110001724429120014140c0118001d04001516840030a0450743d42d0718200020500d00620044a505181000d0303c61281950801d40e07080c4c0f6401600c01d009d8034504020103040102400e00107074000945241c00001418070b2144100700c03c078180c01a03070014074500b441d0b07060916552000199030b0234185000001110141141d500d028103e560703e08800c011000104801c14003011054544d03e00451464a900c2c00d103100b901c034220171200b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 921999946 1250 921998696 921998699
    0xc0c06050403020306091c0f0909021305040b030f060a1814150f10140f0405010f090b150406210c03140a090b0f0a0e07031406060d0308040b190c0201060f 68
    0x140c81d52541450f921a9081c10342d00401040148142c1e503602a4a41914040200072b440c2c1c05014100d9110356540b602d4050690000c01082c1494003a041040501302c0140500d00c10111300c40b5110740008041e000c0081c2e8071801e445040707180801e911a0250401d40307003a000c192030b954050f9150500b00480540d09030b480d001420514103180c2840c8108824203034403c50030302e0704445440e50b0480c1003980c1c1c2e100c0c18011100e402500c403841818001c055140350032031581d01d070811200840b0540c03010540140028804600d5448004e0300b120103c418500d00382c8601000c0cc4000c40340031030b115454443c0316007080041c2403056490782148040c80c5480c0000400764030384419100450300c01100003007256240c6000a0a40c0c1c0d2141031003030b4009214100452090300c10090300742404003039082240c91882801002e1a4184100300b4654441c10540d00d4038142d51184d01c0140c980c102c020300051030004d4210000e00007028604464419000c0d8120501040c0c003a480040d018240c14003a580d0440901d140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 922001196 1250 921999946 921999961
    0xc01060806070504330f1202042106060b0d0b1f020a1202010216051f0b06040902161a06090619050105090604120b04031e0f030b010c0c06050403020306 67
    0x2240d80c0140750340d0321800c0c9031905e04143c034249114000d41d0854108184992603182c1c50464003a001c100140d5900d4605001c1d581e0030150001d0700c00d010007140f851050006000c202041d0110074541014000d0030740c140649441c000001d003100e84c00c070b1010140041005000c1c08502d80080d280350008595811002100c0305200c101c2c2d0000020040059000000359000b2030324080d425072001c5110302c005841c0c103010b800c02800301c06050900b00c4841d03102c80d00041102c0458a111010072028041c244060a8083c00081075402640074800505600040c1c0301e0502c1901e400541e841c3d13034844c20381c1910f100b4412055071100c504461007402601141d0011300c0914058610301031a880050b00c18008030b042000450f00c0d5007008410b2508031008000104003d0820b55800021500c241c2510b80a031500e490000c06030314031852403c0c51000c410424600c000d41040f40e440296216103800100d202c081e10040b18000072601e070140803d40c0050740030404a9002c1c0042066038001da04407400341d03e4188 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 922002446 1250 922001196 922001203
    0x41203020f03040303150510020708060906060f0603091501090b01030506010c0203100903050d090c0503070605070503040605031e0408030a0c0903050c09072a030e010215060103020903070801110c010608 89
    0x10300d44401c108002000240a58000c02c0d400341c14844110384580c4a001050b0f81c2c80c00c1b1444500964448002000368860400000740d101508802400d09424054040380d0180303103081c402032140782c000c00001d402d070008100ca043c2d003150b6088040340c2c41d40d40306168001406540d24084c002810f1070005151940281000140c19501500514514124001e920010300c1001e2086040040804c03140400c0c1e0944d01804020602407003403041c40341c1c5460100f6150242640c032600070301a00340050b0010400c048152402c40d0402d003026640e0303595040400808848140c2601c0354821460140010301c40704501a40c89000031800400c0f01041071036081c0c1e200c110601c070082c11760f4408441c01606050030012580c01a0450400c5001c113542d4441c0c0e01c800c9488140443c001c009001548000d00d84e00844010080c50203001411038403550202e0568558002400305040c03540028280c0c0264400b00420070003020214020171000010b069408101d5202c0410f00e0300795820400040780071070011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 922003696 1250 922002446 922002457
    0x1090c030215270f03030f0c15390d0902040f0218040b0f0d060504030f0c2a120b011a0a092112020f0f0706051b010902031504120302 59
    0x20004040800740c441c510141c8891202071a504401143c001c0134907078800300060001c00079100c101d10b484840f541c885915188500b180c10707545903101814003101605c1981c002d2141031019003a0019a5100f08503403d261144416840c8400800a000251030305264403180c03409200b11414885240f010105105038010007400d240c090300c8039180d0001d10b10346548403005000d0060400030b02e205030400042c150460500007a100980c56004110805902664001003003d0904140f1007910320340d220500c508024075000d843d4907400c6c400000c0c035100c2c600310943c020300c404089000406c3c1c507440d20411000c0c080c8280c195400d406c03000d80da02142c2d400c0544d503443d08103607203a40d07183d450280004540e0b684108405580090002d003100403803551703403e204d03101d0443d8008000045090341102d10340f00d0f5800074540d071500f0002d801d102450b40311040b2105148401d44460f00c900d561294107005110285001390301d44241722881500c2000e44544601c42c3e4028001610500c4507000254140e00c1354 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 922004946 1250 922003696 922003717
    0x10801020325050a1112030c0a08011505071407231203071a0c040906030303060e06010e150a03060b0a0c020a08060702060106210507030e012004030f050f01090c030215 74
    0x40c050341104c1c41c80795a0a541130b845210072510402004216102c0710b90064804445c00721001480c08401500080ca45004241175440c50303c0325260840001d1090044210003000606040041001c000c820010b0402900e94080142860304500c200f900044911203d0603010b9005ca020f1180710082c0030060303503d0340d40c000d22019001c4070400d01d00c54003203000504c0240306074024000420000703060311620000d548030380c60001d0707140d08142482281881c010056030401c04240d9a100f03160312800001d031450030074040c0b110303151f801c1200b06802900302c5801c0344168050104441c3d000c1580301c100c080c0e0321402600c02500d000d88404089464004c00c60307a40300580d100b040100302c894862072807106045c40401070300705080a0380c40e1403c161903060322003d0010f5218004244c01603c00c0c0320320f1400c4244584200105459120b008101d40518400a0146aa10746000c030601c00c00b031094404210340c0304000c212000c45442c0c00d50003a9032501061b4001c204c242d004500c200e110004940f4032406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 922006196 1250 922004946 922004957
    0xf0e040c09050c0d06080c2d010f0201110c070512070e0601050a030905030703170115090e060612040f1718040e070801020f031506030402090705031e010801020325 72
    0x81501d140003526003d007040344820410080924401480d2040102500e0420051b040c00d001700800c11808180302400503014000045281c50003859080d080074074403034282170042e000c20403410264010320a803403100200c0200010000c0c0300300004524001074500807510242140c118005960741c8600c0c50180c1c03595800d80902055007913005501900a9050343d140204c1d210195549007400d58010000440118030303843c4200d052800030781d68142c0546942905180c5800403018010100c500030310604224106000c0420965100c49040301d25551030030f6511200c0381031624107044c0c4c14030b1440c4142e80d06014524207580342c4056108071401c1d003102003030104218000304200300003485e900e0347c03c00c9a0300c1000c00016251000380003034084100f0081a65441c1d00e401c90201c9201c3e03a440311100d200d00f004004000040c0e0311200415003004040c0f4086132242c0d585210368542505c103400182d800e51200380005411031054004511442d80c5807916020100e028031211004003181c114000440c9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 922007446 1250 922006196 922006199
    0x1e0325090911060d0c030b1210021c0c0f030b09010e0105061308010c020a1e0c030f08090d150b0108010b0307110c0901030807200a180e0d0203040f0e040c 68
    0x2006a001190602c2c0110510b102d07900b21040011040d40c4000081c80c1ca050f100c031500803019406101d02da0b040c2d681518408440040500702c142c030303442c0700c900420f103503a40440c681d00d040349240400c0150f0030340410100803184104502501c1d036060494050f000900b40707041460241454101c1038100d0b0541c500348080c6034245400c02189801417507002e00003200468001400140074052240340420640107814141007a041c94090004a640c1a2130300200da203c40c0d4001500142c420000c40745c201d0b00d0145103d50303031f140c14151403040000c0305910084e5559401d0a000c0d101c0250140000070020070860400c526005440003c401d1048403404e12080c000076072000e0003450fa0200c42910341041e100d003c0b5010b400214000c1c4280c000f90b65056021944404200100c48102c141c030106858840303081030881e0010395041158040d942c03001c60394400d20420100d064000c1080b1350045000c0d6660b22034807900c020750340d800074440c903c00c0c884c500d280007031031941f00c0c21020f003d00c0d084685039103900d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 922008696 1250 922007446 922007459
    0x4030510050403020f1510270c0203040b210a0e0618030706050408030403080906010b0703050f0705030a110c0a1a0702031f050405062805060a051e0325 67
    0x280710042c803c0e0154018554204200c075004d00814104140c1c465a8080901b41000c503090100050b80260890a43c43d06003044d01024007035400980c000c52007008111000703008d10032411401154010b00030840041407510070003c024003400f01c00461107462075030640ea8100700c0c0c2c054801c03480084000f0342051000c100c2c081c24076501000300201c800110391a05009903150000c0f070b101145c081c4c41e000008000e00041641c050207407604508070380010100c40d41403100a40d641e200350030005007440000140e68101010503002d54207456000400e49451310128a0060101c1a980d801184036000d1100c0048403843c0540b01081036405140d803038284144c4030481d00c1726650120100703a03490b00c40d00ad0703400303106246a014040350484003840840e06003000e107011460715601503c2681070350680403e00d110000841400c0021000040c0045120340390800411080c404079048181c01c41407074514140410340000c110100ca1400f64200c58503404201c02000100d800f140542e0b504108040c41000030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 922009946 1250 922008696 922008701
    0x1413030c020f270f06010305040c0b1e160c0501080702070e061c1a1303360602010e061e0f0c0d1514030d320a050306031204030510 58
    0x292407000d088105080343c0c02e483d401c09440640440c60519100300c04100c580c80d15250b1440c0c0080c000e0806202e507050951307070f51408403100d0060865400020030464541008004066104a19400b541e50f54000000000c510147c04c020103440f0383c003a2040c005a60f501c0f449044e446440c103136000d0414039003810441200c2ea40090809640426061030348101600b07100b0b05081c2441c4100b0a0050b0260301140c0324a43c140b00801d0b03c070540d1108010075000ca40c0000b4048140d0130481003001480c03948a10003402450b100103420303801c202d840300106d440740d0158840c0386c0800c99441150016075505030500710041c1243c0100c0901030881e400f25201240081c1c5181d0006400400103007400e03150012041191038007000100300007403100d010800310300c44114230340c81d0f800309030080c10302c620045802900c0340e001808540b01117003101d202081540c820041600300f8044840c100b961310f07a241c02c00104207070000d9400c07a01c01c0c0211424211803031801c000300d80803243c0c410060203140641e1580c9800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 922011196 1250 922009946 922009969
    0x1b0b0a0b01020106050a060512010801060506090103050c0c060403110f030405130b120a0825120f140f070303050601020607231b0105040b060f0303030f1b0a02011413030c02 76
    0x56640311078000c00c669036508405805401c9aa446032749510b0380580c4a20001c4040c2d01c448082d9240110a101588580301101d01c00b81007800c0208440d100c078084a0304901c50034183c0300c1d0501909084c00209a4410b00c0d040340f9141c080304541001407002045034892040c0d00c83c00340e00c015000e11b50903002d1060781042541c004001e0110b200304a85143e2981804064442150300c15400580b501c80791b204001c1c50580020605462907a01d095695642044aa588115814414481c64110740d040c0700380000584031048265450b120350b00003255040701c1d0040d02003200800d041c000001d800794800070310381d84251303202d0340c4480011340c20002840401c03421110003c1030140800c65154900307444040b102644080400019152500381440300d6001340281c80c1c64032401c152010100160313000002d4a4012500407141d003a03030b480302042a580290301c80091540f014011580a401c05d40640c0100130390181c41c07407108060f60355450340011a50640c01c008021842e108605800350404503040311 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 922012446 1250 922011196 922011199
    0x12150f01081f0f0f080d030c0206150406050d0f1203050403120905030d020f0a02100501060c1b080109050a0b0606121909080d0603170903060f070c02061303031b0b0a0b 74
    0x250043e40b5a44400061400e90300501030304010700300e0400c1000d41c100940341500402c1c0c54100304c00d05200308000e4660303402070803100072802050760f2415555190340c40000149801014540c0084042c5402441103000c1030041c0c03412603901061218081c003a004541c49194035a89602e001c50400101c400101528103041d0750500c0140102e0506520610041c10154103085c0a291600c0911100038038252541e50541d0084c3e0070280100310f010f400c1040030413400c1d4420903010110070f84620301c18103100c03641e1205015601b4003183c03500380240850321214441c000d0128001c2996070f617003800480e2040070450b042c903155040014284c001c217105c5801e401e0120b2080459803c2c003e03180c40d441d0382c0101310400b10b0984c1ea01003c00410486204034855014680200d504000c09400000d4036210020040c4031001005400038002e0351044204406207580149080d842c0e007000112068508400d003c120003182e0038070f00c00c3c80d8850158604995456201042413081c0d901c0b0300e00030b0f018000d500e40341c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 922013696 1250 922012446 922012501
    0x1812030405100c11010e120d0b01051c050910090201140a02010e061914010b07030c0503120a0c1403100501111f2c0304090c09030812150f0108 63
    0x4240341c0d004120303c08159603104982c0313851075580e490840700040900c009507406aa0400100c4141000f41c9141107207001d0006003503c8140c0c0140c07007520954034181101d0681c0030400034088150b80c4000e00920110040b00c10000c000e901c200e0446006610180c08100001c0c016500500ca00004000380311407403001160400c103c200382c9260210a2b02d000401840305820384641c54031078403035034045c2d014000004256514192038000b085c482c2c810b014041008150203542070040c07c004540c2580e2490300d200019260507c1c650300106406084080040d5241d41c1d03182c0080d5250b01a41e029001c85500301080901e440b005407032840c501c002d2540346015281ca003105000f08096000c504035a14040407900d910405035118055100c100701c20b25180b541c5200e0907011350000151401e0f03403054240060300460f201000d44020310b0781c0d80024202c080005981c00d0075400e0040c00c42c01520041603480b031252041e41009600701c5000700203030011300d07081d0004010308038581b180c0c0c01150001c002c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 922014946 1250 922013696 922013713
    0x60b040902060304050d110a0213050405120d06080c040504020f0d1403070308061513060809210a020105060a05060702040f110a021b030106150503060112061d1812030405 75
    0x4148035030404c48059030943c20003c031481e4940c0d002000002c414103e040945190401c0741c0c0010f4501810210030000d00d50b45000103410040d04200c4514078640007404603844181030b260100162110b03000d04071113809001c034140000e0501e801044d01640e07009001201281d6201f0510500c4505040c081c0c44104d9104003058200c0c805000501110740203650b104124070b410b0081c0026445642e24002c00d07040200043c0c8820f804500030201510064a012103c46e2a5007520500e40312450540c414188400003107000403440440007030140c00e456070002d203d150f41d400e0800000071000d11a058120600700801001403802c1d07401008024400c8200094410340c2c101c400e81280c20410354000540d200041a1035108141003c4200a180441c0244103081c00c00c01c1842c044611010a00c0c01d1000120116040d6802401c8085103080d800c1d0302004510313a14900102d9041071100740c000c0d441c0100c00850030220518041c0540124003d009188400d0100c03401d5400342e100400c16289401441c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 922016196 1250 922014946 922014949
    0x906020a030b0f0d03080c1b160e060301092102030409020c060615070c150e03010f1d0109053c0304140102011505150c011b090819060b040902 63
    0x9485240e1440d81c00040c0c011502041c0320400003500c1606200c0e002000d01000040d82c0320b030905520210502d401174032034400301500d0030310b600e20480c155030038080d01d81e181c2da10600364244081184e500ca10001c8998440c5820716080b5000f03901c0143c4100303080e84500703020b12070000c11001444c142c0d10440307107410b5882c0940412a004080142100d030000810303c4158a040103502d41e02900494885280084c19552409c00b441c4038070405081154125000040304d000700b0009002031000340080c0083c0b000c440041d0b0041520810703d2010420344118141401d10500c1444c2116500c400140700441000b40195000030aa20200b070f216000c03842101811003000e0407410801c0d8081c2c0c000c648031030600054008060502000b103046a14140347c50904000c81d48618040b83c8050350450444100a04220b0b40b0303210f0500c914965600b0510000070203016034881e052511072584e903102c9030949401940f61240203844250a060b442c9451080120703c15501610218400800000f0380003125030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 922017446 1250 922016196 922016201
    0x2104030c121b0c030209091906090807020405040c09060f180e01091b0302030c0418020d03030b04020c21041505131508100b030c0708070c09060308031006080105010e04020702040906 80
    0xb80c0445004090400401c1142007607aa4960400d69650280c01204005484a030000c600d81c2c6014105545680b00700741400b4460b0100c9800c20780260003030000303190505003000911214400c000e202da1809200040c5041c2c1198a031080c2d6902e1344080c440e40c0e10102000010b850340c4d10841000c0e56950134400005030600e42500303280045220005480c0c0c0c0744d8010541000c1b03040c4182070185081804bd002502ca08085900c00a40d04403110440480142412030041c00c219402035045403000920030740410700000c1080001901c0f00d141d10b2001d00b07125070803041c4d0241d841400103a40c5240f0354094440d02901c0540543c40e071f030485e145e03030003039465442e401e0b0f03642c400c080f40021480b20b5041c000551503070a0780102034841d41c1c1515103941420003941745584505030000c0c0c140354000c1079440400841c5410b00c4e008000c801005c2c0440c42e00d0342880c480307540c0152125034404421010001d0414051101d81d0704840050b140e810f020300040d01071002a611200c000c80e8007d964008030302c0007550741d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 922018696 1250 922017446 922017497
    0x6051509181306060501020c0d20090a060513090506070804050a0215090f1e13020c0d0519020a0f0201050a0203120127110301030f0203030706112104030c12 69
    0x4800c5503802c4882c207048088403215000f09046401c200d43c030107180e0700c5e00152a99203136407007145031a010510321500541803402c00311403680500d6080a0080ea558250030820580c0c400f210717600d034a9603d0341d078003804403210001c0050030b9420410010315040e00600507182d1241c098070035076032104640da001900313422204200f4240d00c440840d91001a0800c08000300004000f40c0e0120003407803031101e914a00045e1002024410508941c1c201340d06e0320380d80c054440c239148020440e40c0340d40c5140780181041c6c000100700c40454000c101c90f846410f00c0040c0d4000013a0300000d02c00c45072003041d0011101d542c0110200420340c07008100b030010002d0010230090081c00014503c0c241151a6040004005842214070348a58200f185030507040e4080d408507070440768001c10b90420510705101203403d501540e5005801d10f460080342c60800000308004052107502d0703801600c050185200d410300c190800707440281c000b0f0380403c400c4c2c0010b24025200502202e00d0b041c115518018403190a80c0c20b81903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 922019946 1250 922018696 922018711
    0x130e0103200a0b030a1a120a12032306151903020f0c160f060201020a1202070203070305030711090105181801060906081c02011119030f05040f0b06040605150918 71
    0x165116100400381c034010300e040000d4211080e414030340c01c003c4130039076031688d044c3e01401c1c6c0484c0440c0004103902a5001461860818560341c40402403164003040c8140c0c12240c440c0203443c200c01c1c06042e200c2050440d504003112055103000c0460f00c4104070700a40002561180d00c890410109120301002c01c080c3c042c22015070b255980a41c100400e080d08a080b65002300196801400314240d42078200c104002040c585400041e2100750900000e0300c0c18042c0c0e0310284c814040003440000380010705450031060a02600c0305803081c1d0740c0d4810300840d005203080c0809242c18800200d400d03100c2180c0308144000ea034400200b100ba445032501d0701190040d0740088600e9008007852003054008107003030704184200e40000c01101c044800c9065180c400c4074401155050810788030010341d402a80a07903010080312000b00002e00c2d00d80740c000b0344800405020740d4028140c0d000900d5920301070051205888014040c01c400103c00c0380014501d400000c40316a0102e41546101908800003c107144240311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 922021196 1250 922019946 922019951
    0x9020a080f121c0b030709090b01060f2c04240513020a0e012102030f0411090c0906070c050402221403070303050a051608130e0103200a0b030a 63
    0xc50401c40c5207401c610301035010000b00d00340443c50705203041c0c003a41154030b0001800803403052604000a410010990055820680341200503414050074030119810396031a52640e09041e028000706603442d102a4640c2840d11000c071840700c5841981152078001010094000b042054030340000078002010440601041030090108200038a8188429400680c040608514283d42408000c0240300200c036068140011002c8080c420f030b12415050f413117081300e100110344a0030b00c1581141d0b40f200c2607030240e41e109403404ca05400d51401c0b80140340a0a00c0c0c441041c9401c0403041400a10b412413079040d0364005214900140c9034803640020902c0b034a0740049284800380f00701c004c00100040b60440c41c000c2c20103020303e65190320700158500c02e0f00c1c1c150400a440c0e03507003203008403054814440801d0820a142c1d6002302000210405002d4110f8040302c01c8020b240c4031178a100450070244400384c041c514220300204025802c04c184040c00b140649111100d40e101c03421140541d0090341c2d01ca08059 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 922022446 1250 922021196 922021213
    0x606030a0e102d02130332010605010e0909101503051b041b02060402010507020d02101206061805060f09030d120501150210050a0b0a080609011107150c0309020a08 72
    0xc110a20b0030390b18107041c0411030400080c01703440e1140101601006241000d080081b6406002c0d84030720b540da450214101c89058000c08240318080c010910480340416020080406580b070710f03240340352140c40d0000040001c2d411126814014060404010030b41c44140e01010011900c1031200708201c00074030500ca0084100d200511045840207081803900702008080c0340300103503021605a40083d024a04540c07509128000640b00c007541c000004e50217005c07048007681071500034114080c0050815400c2040a5a1389011b40e01e440442c0428440128491414040c070728201010b80008080202d007036003000c0b07400000c0b0345001d80c001c0d088004070f50500460340142c105400303440e0151500e03401c0300c1c0c00a21301c408065a9000060b4160446c0c940f41d40004400049540c061800c40c80004c00300c88034959542c100544928080e2102e40c04c550a21303000141c10f075090821150043e07482a01c03504442042d003405070091110001900c105521140b0500160762172000d0a00540781c2c1074060590074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 922023696 1250 922022446 922022501
    0x150d08041a13090e0304140a0b0c0f010515010e090c070602030f090d0f052a1902010801143a061b020706080c28020a03090602060606030a0e10 63
    0x549460340f220400504010f0035100314200032007038400712040c1c1e00104802e010107400045400705141c0012624400c040307440c50ba890340008284c8040b01a10000b00600d07201c9801040f2089003404c203560105122041240c1181401100c190740110b12880050a203040c0d42d0300c0038245e0303009880d41c0200c842e01d4800d0100b510f009010b540421481400e02011110054002400700c0c001e015842080b02c400d019090100510447d80100f2201c0d403a00380c072000e10394104d00b00e41c104141c01c8246e002481000c00450f23151100ca264450201000301001d4050041c0d080f01800502c004110181800040c121910800100000082c0e4503114400101e00500d103803403588003411204038440215070044004000144d00452a40c0d0490703440c82c68959501c00034280f403000c1800d40c41d400d100406500110012140c0c1c04504031000714425501c2c9050a075582100f20307030390030050798a80d0f804101000460109801603012100c1810441c00b0b40d02010726100040003100e04203441c02440056a08011b0b20305c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 922024946 1250 922023696 922023727
    0x110c0610090c091229100b030f15060d05010308030618060a0911040b07110906061c18080d15120f080f1201031505010509150d08041a 59
    0x1a00c09050100184003003240000c00c0f010351840760001d002e24541c00c4000740409a11402644005074200781d1003031500d46140d0000c22003c9034050500014003c0119820092a0480e0b00030006a0300c80c0450341c54602d9029507a15848400310b9000c44200142c1e800c01d04540102d41c0218000c04002d912417a284050207069828401106070003c0203004001e074a9031001c0202d01518039034500041d021040554000c11403240b9080031001100105400d010003c000086103903070303030044d144800c054444006200d01070142d2509803141030103100131400c000c00e066214416028180e10284024001c03900c458296500030604190400c0d11070400c4120400714640100c010612200d182c40e804a09858800484042010083c454000000d80c20b034421018015112000421740d410078403943c0d00d24014045030510b00b155820300d800c00000041070303e801c1c90300c0c0d031040450760025624020940d041003018072621004071040c1505000c007095940460101c84034071903041407243c0c1c2e60030010b02100c80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 922026196 1250 922024946 922024949
    0xc0309150f140f07080a020f0c030c0f0c130f020d0f091a1b03041a100806010801021c0e0a051f050f0601141b01181101090515070501110c0610 63
    0x94000070303002030000c283e600b0600f0580c40001c2e490b280c0c5071038640e59800340c060712800400c032105e480302080f04403803078034003000a102d400c42c1101196808450900030039194202070000c55804110040d0311080d1070130036086040705008006006141a1003440c07070700203c50103001100071595489000c0f908200024180d80100c042c6500340d100c8501d4810b107184801d07503000403c1c007003841020000c1000c010120031204920701c00107800441a2419105002c4c0040320740c402c0707803914410b600000421010610807a000380601904001014100d06842c1000c2c02c0e540d00304004900c01c080584002c60304c1800320185403440c0c41160744550000c6103a01d010348a01400340784001c0d85000501c038840e80c06c60a400c10140c034902c2c07804d88903603c02100028004036440302a2040d401c1282e11549403d400f502c40c0083d0348030700390300000e10680302c004442c1c06100740215600902e00303103d44540000040080c0c51038074420000814800d8001c2c141000c0e5410090100000e82d0100381440307292400100c0680 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 922027446 1250 922026196 922026221
    0x80918040203060112020402040801091b0b0a1d12010603230606090610110f0106060f05090a06110a021c06050105061602091b1207031a0604090c0309150f 68
    0x4806040c10703000282c40e50f5041c820012551100c003282c40440d21290152002441071000030412038003e82400030842f50000c5e030006003100d203428007290181c81541521075089050f0b8800120010320700b1a500f5a0300e41c1815254090915036210b07480340000d00440000c3d41c03007181c5801c0d2400324001130000e020b5900000f18002c2e040740c010054241c65840015034400c004503210002001d900a090318003904400e410f01a03070090640160b40104150006030885403203070f03a240881300c44072804580e40e008001c1003943c4400025410040c2c14031a040103080c01484005032420a42254000350500e100c1021440400c141e1040b0714040c424035100e201c0c010075044c1c8074549400f25000c1403541070501d4002c000d20503174105000c40c1541d68901a0820b010b12420b00081d41c0d062841e040306d92900b0100d800340300007800c100b08201030a55510120902c0c01018100340d05041c00d0602e400d000c0c240414001040550f10306000000c41e00000a0300c100381400d0500040851412880031f040e28602e6440c0c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 922028696 1250 922027446 922027489
    0x90f05010509030a020d140a1419030503190e100f0c05070b1807030f081e040b0a2123100e06280f0819210507020d0809 53
    0xb45040d100460311018880d4100c0381e4580c084c0e07092405440088001d020131059106490308141003103410384011880c0d585c41822103801c40078000910f02c00008c031850080010f441800031402101c0d0300314454103101100030300071405c0ca090842e602e10303013102031241461040c0c44103031131102180e5074450501100554502180742c01043d071107281c0c0e5880060701c015400d1707900c1c403620b10845600744503c40186500c41c1c400c1c0c00185150500d0b05494002d520001c0b4540c1c03480000b07406141c1a0001c03101290100300e40b039801d243d00003030700f918201c1c4000d02c04416860108030490001605110790210700e091186006000621020401091040103081ca41101410300090001400e20720b0304507070040045600d400c0003004d000031709008004009031000c4034482005d021580c0f1803c580c070314041d610000d0403503190a10110020319084402000580321a240400032500b8001140300f007810b00406061103860551694046134100c58640b10907a009003010900210502c0e00c5000c4019040c0b078080d05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 922029946 1250 922028696 922028707
    0x5010e0c090105070f0b010e0906090706020c13060b0a0201060e010807180506010e0d061d03030f0114030304121a0114010909020a0905030a06020c0f03160b0a0e0d090f050105 77
    0x1101d01c00d845010341406004580c5004010300c145207218010b40c410020030895a58001801e09a03000303854003142400784100040d4009030024400045a4040d4018083e5054590600c4002c5007003010007144661908004200c20b810040182204142940002281031620000200142042e0812440b580001c0070403c800600c00c503110600031905980010315172520030060b00d030320220b480312a4100e203003070402c0000d00180703500c403403000c96200d00c031000c903d200070b070149840e4401251000e001c2070400005010524500a030720f4540140501140e10702a03d401c02a4160f1520785001c030341c54982819070707607502c440c0c2c00c1c0c03114010481e80046501c980a2280040c050300c40b20301a080c0100c2c0e003ca6a004164802c02c0c04400600c17010b02036808041e04c0b401c0c42d5001e9802811569614401c107003a00400d403030700004480501d41000304120740c8041c1951643d405a802800c20462652a54a0203031000c42c240003841d80200c0684440814920b04807800c4408007959020a0502009100c2e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 922031196 1250 922029946 922029961
    0x13030e010f02030f030a0605032a01030908040b030604020c0f01020910110307030e0a151e050909131b060815151c0204030b0916080601050f0d0f06050c0d05010e 71
    0x1d0300d80162409500a0302da50702e40d00818003c2c5415408a0b030b04ac4505588425204404000e0048040d00103000600e0000798200544c02c3c2d440c3c03c0300080007440200300800c070404140b00503580001c0011701c00341c5000500b07699586001c601605d907042d0b69500240d6800c5600d403407800003a02801c10b09120301c0c11401001d465403280514038028040c080d0105c11807003d42c1e22094041d015001006041115200343c80c2c0043c900028a5600b0f0890a205180402c0060068060300d49a0400425134012681c1d038841c0d0200c5009200011220805612040840016207070610710203041580e4801c1c4903807800341c401d2001d841c41080f941c1e00440c800984040308161520840d809043c060b01a1508090000d06040003403080b81d10141c1407407800d206008810002140540d80703c8010210319160036141c2c13481545508081c403e069000030f0010291b0740500701030045004031800740d0300e000b220100589a074819a14100da400a052000190290310300201c4e105071805002000d440420380d141031039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 922032446 1250 922031196 922031203
    0x180501050607020405070908030a09090509030306100f1713031b02060412140f0102030612010c0c03030c0519210b0306040b042904210903020603100e13030e010f02 72
    0x24080e00a0b511780303001451650160003124001c0c00d0300c0080b01d036681622000108140c0349405100c00580c20000403580103040001600d008410041020069034424141a9984200b44c01c4007014444100e00880c1c0c203040240c0302500c076150b10300081064000d0351130001d1035001c03e00406d001e000d440610990240c1c4810068a040e80c0d51022030202c551514104000000c00b5140f1451851061840349005a101074000d1030103094150341d44141da506248410342a01c810b0100311000a0280d03546c103011a11075003100c540c00314a800e0941c0b80c9078855055984911301e580801005c69501c40c0700340041005945a40c0c00680c29010806c0f0302c0c042000000c3e1907020203000501030590038800301d800d1000001c01204140c903280390f0040032a108602c019042c900c210390030794110504581d6009403200f1482074000325980c3d90fa4040b000c41c207503401c100150700f0180452442c001100c0012507284038460b034a038018a9143c01443c6441c2e5031b440c1c01040c0b5090741d56040e041000081c0206e86150700003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 922033696 1250 922032446 922032457
    0xe0f121c0e0304030b0919120203070605130209060904050a030e010504080d0206040b1e0f06030114070305070e010815010c1511090406090e060c0702370e070f12060b03101805010506 80
    0x1810104080c08c01e400120700c2c600030994040c140900e070030284000c1c241c1100c2040381c9a0701c25070b103a08103075840030f040040702c0300100c0e4090590307040044080c1c00244100f002c3d00001d10141000303070130305445000c41407400c6954010130300560301401c2444180b26514681543c407140d15001320b0320342c00c80000f200da88103c0180010922040f64408186c1950302904020b104104c040c0075822640b0f0306134002409000d045d98000c0106462070b0200301d0303551044401c0351095540220941207103800e5001100c1090b540c40c01034070091880122000402d107603002e1314041c111481050381e261810b58003000120b07038182d03002c096000e1420390040700105022410316440030500e40c4250300e1340000c0c0041280640d0000000b0103c05444000107101e5040203504c2d009180c03800c003611a00c503104c001001024106560280100d401e206910368150321516440340341510080002c1001c80c0e644011140c5504103507010000e01c503408205001d224100052130001200007a0184034951400b008191a407064 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 922034946 1250 922033696 922033703
    0x6010b0405010504090b0303160b10090506100e0a0f060201060503010b120604150912030212070836030c03071205120105150c1b01030e0f121c0e0304030b0919 70
    0x940c091054247d406200383d4082c030103010b980381d800d914145000f0303416007802c03180c0602c009100003000c1a440c03594424a88641c6001c1c5c01500c5050a119003a912154148141640320040303900114070440780c800200000c0c8820740020030081c3c1040201400d640d000320320a4054540500002c0031003a0004240303030000e42001c981c8500100c1c0c02201c0000d800a260050601e0004040c01095aa80359005003900c284080c00140c0503280c1c45e00c1201c44000aa45060200c007580491490004104e40003101d003444800031840d904100450756410f5421101d06030b5810b0700041404414040c03e4078401d60090310b5443c2487c500704003d8605404020180109070240b48104800307081000c6920448900a005100704c407010845644140d901c0b4000c040403e000909010f149215100c1c0080e00d01c00c805441c034054040314003d907ca005007a000184186140c010158580c4048603052190690748002c8402a40d9103500310b040909240342c0c041d02e0891207900c1222910300200e01d02501c010038952 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 922036196 1250 922034946 922034951
    0x20613030f09030512040f0e10170f010501080106060801080a05060c09041103090a0c15120207060b12031e0c03031b1c050603100204030210081f1706010b040501050409 74
    0x105022506480b05800040861143c61500e0304500c0340000070308222046107120711804d60700d614003089443d509031042e940c415801882031010000921a00e14490508400ca40c108180c40c0021803d45100f0307405007400d40d5464809200041e4010195409011040d00030300c04101165a420f0b84c0d150020a141c564820100c0c010540fa40c554212441001c030800c6055101d05014921585956810b03600f1541c044280000042c1855658011030002060362201e13012032114050b02030207544074032070403540640e503001191240d9482201c07800100d0101001151982c4403a406e80d45c007802c2e82c500003d00b065050096203134940d0000b04030b80d030151640c02803203420302800e2040303481c40c000d440520405074100051642c00f0328641c4d0150303207d02c2d4110100d800c850004072400f01207118a00002e5002440760100b806407074000c0d102d5a80090852030324508180e80410803141c01030302a003041d400060302004081d2101c60400205015044e0900075903d410316000001c1c10300c1c801da10581c480241c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 922037446 1250 922036196 922036217
    0x11040f0f0512100e0304030f2001021207030c0224030711070e070c1a090109110f01091e05030d0c05150903030105100528170705040b0705010209030f0c01020c0102061303 75
    0x1070140107850041d0f901ca88980740c52382007458a1840381d0b40e507403d030032004010b580356a90a984000b81d1000300e0f01090104038541181c9480c1103508890080e001d03608442154520034210001c45615107013480328200c203c0d03e0303081c81040140a43c1a4a900c2042903106080512401000606030f5400c4881c50520741840301c0c03607142801c46124003500c8142c6880100c4204080c1e1801904130080c0c0d14820301c0c150401104031410080650400c00c1001d0004054039020704c1101c225880e144503800c2c40078801c99025940380002842c0441d90100c15000416655041c0304019040100b041407098040d1014035503d071141e0351a607207000c14824944907882842d00216040c5c00740045911242842401800c2019a2185209031241a00b0400d00280001e000c0c0da422814100d41c3c24003454072039a450b89003900c0c2040035000b542040b0300c00d9515550800000e0543d507130030041d46800c1280741000d00b901070080c81c00a81172202032107006055401007130070810360200e0303022000c00c00343d81424100c8154 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 922038696 1250 922037446 922037471
    0xf041e050c09010f17030c0304150c0f0309061b02030d050d021605061006050408030d0f020d020d06180908032208030103060504050c04181511040f0f051210 69
    0x12480c580150802294030010829440343c041040c00d4075103580460040c010344500c115034034807c03103482c2d00085d041440280300d01d150b0a141c1054200081c9040171000c090b03030b00c91000d20883d080d001c0f00800d0960600700403060700441c98960769042405948540b080390f401003600d480300c403144042007020008a141e000c3c0c21550640781d0109602c2558100e10005150003a074940040c2c42c48102254580380008600e8802e00c1294251034070503002c0e600b04030000400801414021452b11989070302404503598800823403000d8512040c00f0751000c101a8036003400005c1c1404d040580760341c05030406102a02059508003100e800c100d20540010460300104a5001205200503000704481000000001400720b05d07004107004034000c2043d6104907911104110841c1c0508440c00c4400c1c40c12494100410480690030352098101d1401140505400354103100591040c0c1000080d04107014062000d000380703001c20b20140c881a105280e069041e900017603640c0c8081514120450744071400e90114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 922039946 1250 922038696 922038703
    0x6090506030a090212100b0405060d05070308070804090c1d0102060601051e0c0105040305030703230f0414010e07090b0f090f0c1629070f180503150f0f041e05 70
    0x1804d800140e90b001d0811b030342860090a101c3d5580381c8100e0500002c0f03181da01d460890001c0c082d60100040c0081403540d44c40440340d40085205681540003840002500c44d803d0145045242d4560307640b11524000403840d481a49050803d141198019010043c541e40c001c012252840c0074140302c18030801560052105c03500c98100700003aa0f500301418841010f0f000740c051805086952414800350303104810071a60340c1a00303040c005c41c88039010b000c0f900c801050b14040e87c0040c0a001c044020040700d01100b030039282c4c088034130310840d40103d40400100f1254440c00d804907804403804460351041100146c114140502178014040000000c81c61542c0104220b0b01c21020f501d41422070b050590500300c6104000b100030300c15411145241081c0b0a030941c515510440071354407032010103943d2010848444100c02c1103040d501410a0010460307a40820482d0101070060f1003c50381c51400c0728000d504640c014140340c2c0d14646401c24000018000d91500c2c84000c00740198080b0f4080b21709241e4039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 922041196 1250 922039946 922039969
    0x1203181415241207092007030915020c0301090c060f02070503030d1d102702090705090312040f140d0c0905280605040b0607110904050309031e0706090506030a0902 72
    0xa8522071358a0001c0c801c01190003051038800941e00f00310184500b010000918440c0103c01000520365240c2407000403401c0e0004100000035104039000a010740011a084039240c40c029100410122810001e00c0c0c0c1c030841c5d070307900250303944060180b8624100120707550b4000e04921006440d1582400b05038140b42000d200c0d0820030340c40c00c45a040601c000b858005140008a80d032109054640b13202c42090588034a1400b04d5003d4034043c034603907550404903003035000010860f034103004030500725244200d20805400a003141d0411618100d02d4503024110076480c80c02500c0c020440900182c000c02d000c03032000811038178a00c03c0440c41cbd5071154102001a1005c8101d050702943c0c41c0074512080101e58030036030682c1c000392030070000240038078100501e6000e003c0c8003c003281010005c054041c240880d6050300284101c040302d00305210640024203000580226903601101082d480d10700c11000c022000040010f0b04002c50035504080100d40d45100040101a2540d2901440740454650085404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 922042446 1250 922041196 922041229
    0xa0c170a08040f050313150e040203010302100804050115080c0a051f140d06150f03181104090b040b0f07090b2d1b060a050105030a120318141524 64
    0xb0071b01e64803400366030001030117503e540c0001281500d18103802d00b410b10803070b41a280c0080100c0388602c621401260110001481122076540303902100e94017996420075a005401014081c08003c462030003808030900a550242e07214007000414a000c002d00e103c4042c4210788030780703411800345281e06150b8038284210158000d0203450250300061040f003da07103000c1040703480c0c1d80d16440343e5105c1000310191425120b181c107024802d8090724002404c0741c882040e002c5c070090000f06480d03070b42d511484041c04080710140e402e80010401c001c02011201c0c151a400f40d4a41000000d150404107040c1c0ba50050000452801181e0440071850700460705035030200d80c03504241c0c540c0d50910b5440f810680c141c4020010543c2c8a41000b041f40314040307004050584502600a140062164880078600309101841e04141681c654160192a4488103030301003540c011103070020081e2075215905e113002803410803208009024800e10044981501a200c90a4075120303d200303e041079080007602c00440c410208 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 922043696 1250 922042446 922042477
    0x10031518050a0e07090906060b040e06150304030e09060d020d150f06050612041b03050d2a0b0c0d0906050108071208030604110d020a0c170a08040f0503 67
    0x5440e466403a10190306021a0300601040e21507120400540751290b68482d410380242d403003480200d040d648006409800b0364008500c0316558070035940036a006800040701d0211050400c0102e050508030140c0300508041041e1840c41c040e1401040c2d10640d01c000c0e445521a0320215000c1c2d40c1d00c5180340103281d0000c0c2054180c00003072404011080c002c072001c1c00480e04042d0f1010f1420f110380b0801045a4000c0c101500d0f041c41418040e410200042c005c44944041e80e0702c83c22408003507407800001e140b251005049003035044102405290140c000c1050018900c501c40f01c0101d107811200490b20740c02400661a41c4480c242c241040c094007035103c6005107052510420b1100c00e420550481e00c141046c1c0d04000e072114120500340d45405c801618403030742000804d8003130600d58040581c2500045219081500d9807605809036130120719000006482c41c54154107203d01c0803c079440c1051503c04092501d00904400381040c14020400707480c50041c48440b4050102c1402111803a07907020468 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 922044946 1250 922043696 922043699
    0x90603130605071206170613030306170a05010609020711040f200403021c0b04080c010902130515060c0c0105070204020c150106080a050c030a1503050d0309020111010911100315 78
    0xc0540c40040b0400c40c40d1340c00c1400c0003c9041c813820205040303c1120021f850256101080350001c40d4000324110109a40c0da100010750780071500403242c0d0301011f0b10180ca026040c900b07190b401c2d00c1058000202d658410080741000455551160503c0c2c0019207021940400ca4214000109001122910300403499542c5007000d250140c02841500e200700c2e021308201515003501501c0075000000140044203000100e800700d10352101a00c6012110000400d100c2002e0703000c5120840c040c901d2841c85074480f414000b5452150440208405055032020708180c074090f4056664012103441070b050000c000f13218000d40d02e40c0d130110f40c410000082160441003141d5240c0900300c40c24407910000031140004a128104240215801003809905240c119190005030f04010803610104071180b40c11640700000044051141e940c00b8402910001200c04050001400711059100d0150b41030f4581a1450001001c1403148030040d6000c0d00c0006241400c10001d030000e02ea000c1c00307404e412488910 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 922046196 1250 922044946 922044961
    0x31107050604120516030803040807050f1c030506010c02030d0c080d18051903020d260405010608072c100b0340020909120f031f0803090603130605 65
    0x8103c09084c89003088407030720640a050010751020301d010041401c1002c02c08035000c9030303409001d402d41500500640b101c501110f09500d141000202c4107900c25004c0f291242c1071990544501e981c010000c0c2451010414154000f0761228100f4568074180000020110140200c01007961198003080c0700030080c4a85030401c40c0328401d90b018040740e0f1440f400e80000d042d03085003c103072101d49504d81c0040908000030541500d003059103d0038892003211070032440b000c1121940c0241c2c00749000d000009005c0e8202a00c3c24142a081e8202045000c0c40c68092b4040c2e0110000e0106a2104030001070200e0f20340b080451042803035a40801803a440100c240303c07000604d83c01140c41c032a030075070004250b0b030000c0c1d40d00c00c1c4c110140d507a110941c507080ca0101025007000000154012030f80fa0039149900302040301c11016030040303003c00d01429004010404c207442c0040058000300c03c2410031060710740c40c2c04a0943d9134480d00e0710a60240c100800031680b0b41c10031440340186940c0c041d40c10302039464481d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 922047446 1250 922046196 922046219
    0x30a06080f24070c051617070503150c13060e1c0b040b0c090d030801050f030304031e020a1a09040b091621050c0d050c03010f03031107050604 63
    0xe0500d00340030780840440d41c01000203500c00340300c0200c110407195222480420451810040452007400341c05615040041c0051001c10040700d07080108150142c10b016044154860a10860010f5401107905114a03a000595101e040c5a1481b280b10b19903a5503582c84128011408034160b440d1a41e4008102150468010b40e01340e80161294020b880407440740c48a0a0b90390700300600001014801301c0c011408041c0038580c0403080c40000d43c90541d1220100b54000c00c01c107015000221102e00500035441d0038550482030070744c203d008605042c00d540303c4980600310840100514103800f0520011500e07029000c40041c039800d01410040c0c0e4115240070225401200014411481c0c9007500c6690703c0d088600310f0040d0042280101c20840440013501d80b0002841d140c913803001c00017081414000c0c1c6028482c41908001102034844207020400010354001030030b03241d110b00051005004041004401004483d0140741849076180342284241c1000703170640241d90494800070303000c0b85049112 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 922048696 1250 922047446 922047449
    0xa141e2e0603050c0708252f1215130f0804050316061e03110417060907082817041a09102001050a09060b01020a030c1704080102030a06 60
    0x580b070920584d0b403100d05461075481003082c01805c0020038840c1002032501c0742c4003080c081900b00c01c0c441c0f100b031050700e80310b8080c04a481840002d202001c00448180b000c0050308803054801d8404403070f0581c0d440c0b0b00c180c40d064111141200c0c8240b03c400520f0318003c41c1c001c1c0055a401c41190001d48200d802c2c0440e20b0740c010700806009200e00c0755000307518044041f1190407500c403642d4618060071b0740e202070b9040610380d4400c0010191501c45403041505100001c2000706a580c621210307049103000b000c0e04006000300301d005150807038542080400c07004104040914640495403000468100090f0f2114822100c040d00c01c410041d04a100140b56500403c00d950001c40b000e032040660760341400e50362080c900c0158000680503000d9440b18003480c400004801c03014200340720441e54680311421280d04840010f00349884000d0074082c031040c1d00c1238001012007031010785034501c0f00c0d440260203030f08d01807401440394212800a45240c56598255000f0300b4000009540e213062018060003d01340e42e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 922049946 1250 922048696 922048709
    0x30f0803090a080f21070c24020412030905120a110105190801240905121e012703020d0e010504080703030206240a03080c03090a0b030a141e2e 63
    0xc40d6096505900ca20850780c45106c0507600c0c9690b07101c0e260389111b4280e000301c00d90312130591034045100c0880214005400600910391512941d9901c40c10020050300d1254011805021074a0411003001320201e410013101703030403006000b44c4240d00d6004a07a07600c150100741c2e000c0020140008010350b4416426070481d6142c0f008a0441d186070440c0030029910f050000c0046168014208650704100c0c903085180b40c00002a03503c2d02062101d04078034500000030125640c0d44d1441070b900f400b84074001c45030310020104c5c10500b08038048d54020b0360310340400051034140403081c0c91212990703211700102c801404250080d14405a9a4a406582c525082d80c0c1c511004028200e1817490310f143c0c03219002d4100300100000020342c0f40d40c5414040e98044414407100d4001004030010315202c001da030100510090f50f84537039901d000c8403020201c440380705074a01c251022109000d10440b400110303641c00200022110200e498141d143c039002e500880d000040080c03440b022152505503081124101c485 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 922051196 1250 922049946 922049977
    0x60902010903061415030d0203090103050402061612020105090114041b0f09090314031006050c1c120c0f0e041a0925020127060e06010902040807050a030f0803090a080f 74
    0x45e401c05449280c001c00e00801a030040c4000080e0790301c00e810840d0401d00180c611031500c6079030300c050080c0755040181a11002d5020740a00130b180d50901c04c99a2000303c03440200140c48903045018462640600040d00c40e240b0b400a07014000070b8052040020702003948020300c1d160f512004e000240002603c190003250404140a8022a0700b1084030b2040418200d03104100e4144542036519800094803103540e4812040500c4484001600031403140441e42c076448141d0b55100c800505881c18910007800300411170000c42e0420782c20402903e00e021040310017082c3c3c079484c00100c1c14400761100850b40d0212840c41403002c10001c00c5a0302401140044c0201d507185180c540c2682603034410010080c280c002a0769036031001011402c4030000c103100300380215894050450035491301400f80c1012044550014081050440401c041c0008100548000d40079510750340780c0c0c0105100104000e84107d00000000d0002423040c0070110025038010071300b9841d01129514002241c000e06207401c070011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 922052446 1250 922051196 922051231
    0x3250e040c08010b0d0e0f101509020a02120a030b091e0603030a0504090b0f09090708010f0606122301060504080606090910270503210103030c0609020109030614 71
    0x38802c0581034161034200042c0380c640500303010300714024081040125100d0140484008102000340302d440b09800d11030700040f0701e0403040b6104402c1d458255020030f10395841003045035851a004104c4501520301720001c2d50b00c0e00455007090700a0f12411080356070040c0e080003085200c200108042c4569180100002400d6403104281683c0744030326921307000843c0b8140410046568541c1040300381707060140804c04a0f182c03807030105401040940d8601e84c180c004003000d01503003009202e100b01e02c80302d10300140b04003072030103c0203420580c614050a0500f074030b61889620a550007a410108103968003844203071584d5414000b40b298000e1700407140d460003001c0c081003031440d04003155409590200040c0c04c003800069440070080c001c01400c2da0107020322a58414085800580c1403806901407000742da501d142e641c00c00207038003140950844c18201c1841c0180003099105030304800341a4040030002d1000300500040e02c1c440016070000f4035040c14801d444001030880941903018501400c032001c0d240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 922053696 1250 922052446 922052471
    0x918051509070b12220c180b0a0b071406071409030a1b091419360302010b0d0503121005040c0f0e010207061d010c080a030b03060f040f030503250e04 66
    0xc080c1780002074000704421105011056480003036990150300d80b1000525000854080b890544555100b07503100a00815002e090100c540c1c02d11a1522034100a4004da00d040007000d0258429441508801c0e60017140c6983d441c0c030200701c94080c2da60098690300800361032401c490091025070041041d07070b5041040d03540814800401c840d0081c40c4190b85c0221201c00c0204000041401350318100b00212504040a90740b101c4101c07108a020b90448440d6a80c0020b040207800d5034904000326000301e00d84800c81d40401c1c00803080c1e400c0d442c40113440b40d00c9a2500450031201c00c1d46a0066503026250944200d070840e003003c81e03098414503944612101c00c280c2c800590300c1303075003611590307000c940301c0c401c226080e40c1450f040f99103d00341414511010042610b4034201a0015410180406c0da15002e14580d0301c4d00b005101d80c040100c102e04a490b00c1c1954071481c525004100040600901002083c40201f0217030080a807411a030b505003454055230200205204003441c21075024078034200351041318 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 922054946 1250 922053696 922053751
    0x61e05040b0601030e0a060507030c090b16060e030427051e0601030c051224060a0c0609061e1a01110c060306060f030a060918051509070b12 62
    0x116000200310075036a841100640181ca0302d911803980d14082c02c07803882e0005031644600390181619903800200d1555541e400f40050405800c0300e010584240a24410400c0344602c82443c00d601107000319105120381c0c450b07072942c06207070080c094800e001d0b200c140c00c3e10300084403900c00400d031010a026589510124103040320b884001e00070013a09030300c0003070340c0c03540030307070861401040e282c07500b5441c01e00d0703a249601c0034070001c1d1201c400c120140c031903c6483d81c01c0400c168900c0b81044034218502036030254050407403101c10701c000b088140c40d891b07004140059940b18851444082d0a60a003580c0c590030080000c1c44119540b620358503c0105101003940307e021182d000b882c00c0801442e0400c802001c00c011600003e11590348207400704482c40844024038080c50048034a00000300d407a078101418101561400c00e00018400b06000403000030517000940b15000d54a031101320307005510341c0040941050030b1a003200038043c90008401c02c6440b0b03ca49400c0c800d0b90100c03101206408486140100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 922056196 1250 922054946 922054951
    0xa0302072f0a081504020126061509060d0915020a05030a0509071406130b040305150c0918040309031e0c0f0e0c030a02090d0b041e050d031d0703061e05 67
    0x85548202402d2404c070f80244a0b158120307005050841d10100c5a649540304041a00042500c244d05201070044034100141520305080041104030b00b001c40d0703030001c518507000b50080c0921094030345000405100c0e18901c0c1d00105420050155a11081d1001c060000d030700a4070b4841000e407504001503901e02c40846e070141500c1070f210001c41d005241d401081090341002e00520415040d640d00050024038800040c0000d41c410400340c0350b03400c910741c024070f05042e00400901c01d5813000c10032582c0a80d43c0e04204900740745130306202401038845003001c560403803054000070605154880c40b05103080e484462091103604c107040c031000f55a210484c2091555075131260503c0001c2410209440d000600d000d1540414882c0006007010030721400101003991b010000d81d48035440405120034403130300707031000031300700b104090044100e0711140d403020b981e00d0440c00704400f09603542d0003e00041c10342d5803900b031040c9441800c0799000c0c1c1d2a81840e60080c80c1481011145002103070b0382c580c041142e800f0701407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 922057446 1250 922056196 922056209
    0x12060f1002071719030c1a061005070f0506101415092b0606140306100509070c0f061b08070e010305040206071202100f0b03120a0302072f0a 62
    0x108180c0f6000540c0da01c44825421540540180340500032030307054030b40e0308100c0345000307039908203d154490400c48030b028282c9040038540003101c000c000d401e49a1031074002c507140300c528059658020700c0c02d1070000c0340c001c98030041c0349005142c24440c250501d5404182607601c012505a107003600b2508012107134a801000344241d000610800909141c44000c2070302c1c158050500074074000818100e6628019004412108076036141802c0c01032500c0e00002003840101a4010040340c20880900c4503c90043d00c00c01e44940501030008540a03c6080c520200c075030701407011007120b007040c5070040240014a910000d0550a000011142c500c24940715010b11010b8480180700383c0b03440011005400000c2042c0d0700070700e04101d500001854018841290b0342c43c0e41c0506021546414041c040c1c80b4020003004a140c2400d0a05056a0f03000c51524100034031285482d58400404005901a018070403000d0407080c9240e21524142d81a103c0003082861200d0300004410a0341040041030b035042d02900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 922058696 1250 922057446 922057453
    0x30203060a0207020409080409020711090c031305010e010e031b070501050403060504050a0f060903090f15030e01060503010c1205011a07080d0b1f0905040504030f140f12060f1002 79
    0x6290350740550007001c030035001402c045072007095511200c01c26801a408000141d81c0081d170303d070601501d4451505035000440d0207940c00d0030806240c011901001d000c0c4e00455207070b06000c4c01001400d61011540c0204200240020240a8200c1d41c0742d4000314040c0c04001c521403049220039501140c0c500035602d0585580741400c2c03e6844920040800810842c5d26110344072a10000c14103450800c102c2034803480300400e0018140c5802804454954040c2440072010007052014203490803c0d103028152920300082d0030080a010302d4090415684041d0f055480c040d58540c07115844000c0500c8103c40c2d006c01d016617681c4590000d1081c0007800c01d0082c0c076409010f01c900040c00c0e14000c0091002e200300101d1120405d200184000f040405660300559080c1007464a06400010900040c5002c035020081894140c0380505004000c0b050b020030441c1119103c014881d60005541c01d05444030301c1c1944440c02c103106800840d0045d2495441003640440000c013500d042c440d518041081035015 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 922059946 1250 922058696 922058701
    0x3060c0a021c090801050f090c0a080c01181701140c03060a12081b06060325060f11030c1f090c0b09060702030a0f140601060f3606020d020703020306 66
    0x10602800c01d4400b0001080125000003a03c5030f003d018090061a00c503c41c45000d0604103c064039140c1000c0030301e0b0140c80761794401c0004941c04103403107156040a0a100151a0700c1c070b03035071100100b2160404035618130003c6000c0b014480543c00801c06580c400040781031501c40d0400140140070484085a001030419014070104e01000e50000d078aa102d000c20302c1c10304455200400e140c6490000d006a150320284c00c1244a240c100aa03501c061020300c00589a02d07414120140200722600030b030001c0c080c3c0c03c1440282244510300341244250301a042e40d44450b01019542d8a030080011a151003074100d001e03c1e1045902c0b48184900c880d07000052100103850880040c02607001207980300d0b480607042c030a01c8003603241131051201d442c1c4591054508185035213000a481c020041340c03041558040f0005000d225005442c102c107101caa805d01e24900610501040900c804c0141c1180d01c0b0f81d10800c0b01107544010079004010b840301c6400b40c3d011180d070341c00100d0303841d4101c2c44040c0d4181d08c040701 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 922061196 1250 922059946 922059973
    0x5060904050606010c0c121505060109141005041505040602071d0411040f0c03050105090a060f03030e06210402090a0c12050402120706200309090414010b1e03060c0a02 74
    0x100041c01d46c85401464042a60380200124110100009441c40041c0740884841c161062103441c0c0e02507001d0901110070b07400d050089140c01c295541960091100d500c0524159000742d066500900c61180c41c11660500c04100034140c0c0c100342b09200240c0705084000c202c070b0303110183c1c0c480418841d00d555240b0340c4c1c0710703265640b40c8440c80c001c483d00203684421020212403180200c0c1020441d50318085115450304003030040e0402c00070b15401030546002820f1040e00b09900900c0b046940500d48031034100340c5440001c0d0507118450329074240246280c2c40d039080581c0c10051a200314001c680c02403895680c9103050096443c03015420002640c00351400114014a0303010b140c1150020741040b201d150003040c214540100d581144002c80c41140303642c00c4015641c0031034900c0c020480c020f5410301d192030001c40c09190014100500004070426182d403424025400040030756001840141703507a203019507440d0310780f6182c260785000f8058440010b44442000080f4ad800c949a0b6000340890400d007039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 922062446 1250 922061196 922061207
    0x140609040c17010b0a170426040b040e0402040e01050906010510050d0f021215031908091305151921050d2016170a050f100506090405060601 62
    0x141c1038050100007000351001d005100c2c2020b001c0c0c03801c0e03110b1a940f20f905510240c0785007000d2007000c405607103407410000025104071610303210780c031240b12161911865240d0a96240100d8121740d61404c0040b03000100542c0c042000d90060b8000c0e00e042085035461298142a1103040700d00c20401d41c404c600421a80c24500080301c400080c6180ca41e08041c4101c03c83c5094030010507800300b00f160040354500307421543d225502e811034515940c2004035031656004c40d8888080c10814000502035000d100140700040f030844620b00e8000b060800032000804100303005200943d103000c9607603050900c54049040603200c0282000c1040e0513072541500d804940610340000c0300074608101a4480448001101046030140091098541042d03c0f10303c0c09001c16218848046e000d41d640c0316040c0b02488020601c003078410b450141000c0052b41964400c0c641c03400e61940c2c0001e180e0700ca00b5030010300782000440c40520100342c80c40103000d283c89420401003030b0001581c000d09290815804609a036000f030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 922063696 1250 922062446 922062461
    0x3060d110310050c030601022503080306010306031e0507090b180703020c03070506091911191d0a0e06011526150901060305070c0615050306010b0705010614060904 72
    0x101102d142200340d000315801c0c1c410039a80d8203140c88001c420301415603010321808280d0380903010005040c580b03012407000304800e01d11010700390750400404144a80d00c41d422000c0603603005690031000041000301120881d071804415541c034007070200003154002d0540110280d10030011b00e1901b80c00f03041c207649c808801d00a000d00091560070410708150850600250a68a0150002e8a07440c50403460450410b000303003a0a004040d0040014000215450380703030482072500b43c8400142111100d40920394003090380003024024043d1003108641101c00c0c006507c12101744c2e506100a13051282000c0c0e5034502030003102004c03200403103c05000c500c507103480e444c00864940000589240381008101c040005c1d80c09406800e85c84071050341e9400c100201c140100f6551404101600d00510000c01d160700c00c4400910064540c206503a5100b140901c0001808004059070b1565a540d012a000c90b07210b80001c86265080c801c0020f440644868480c0f444030014080910b440420702c02c210040c843d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 922064946 1250 922063696 922063699
    0x5070305130f0f03110f0108040605060102070302060f04302402030112060e060103111003020f220b070c0909080c010f0b0406050307032604090903050a0e040203060d11 74
    0x58000030300c4002c00b0b80104001c100c0c00c4441020340e4210309058012004503010203001e4040307181c200380542d031b00914150303100d174100b42e00160390b4403000d0040303040181b00e510195105102191403020b032000342e00140110740016020352520178050201402924040300c541e00030340703059416040411074000d83e2050155000007a02d8666280e030701c1030412600282c206004070b4140030914003c01c003152144100e0040840b0050100e0740c0345940e41c1141ea02010106401040d86100c103900150080d0150380390b250f040004561101d10f0305081d100f5012441120300c02c1c55228120001c0c0303c40c00b00c8201c540482c0c0000320b0320f04440c103110108002e1b00000d00125103842007005650792601080c4900c604d208501c0b04040346c5402184104800d85070325420443c0301c0c0e0081e050800c0099414001551400c1c81c49003045800320400241141c07501a07613000c80300c102d081010200425034040004e0034402515220f2a00c54001d00041c80120f0100b122000d03040400310b000040440c09d07566030282007110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 922066196 1250 922064946 922064977
    0x1b0601081513140a1a0f0a0e01020d0515030d0801150804030c0f0501060315020a0507140c151201060905010f0e060d0f0506040e03031e150619080106050a05070305 72
    0x1407943d100321000c2c0903524500f4007508909101000c00040c6600180705003c604004042410a0404500352500240ca41d201d10303660381407059a142020340558a0720012007a04100c1450055041c0c0e0309945032124492007801507843c10102980035440300343c180e4000780d101d460303816103224058074480c0d00a4400d4040c05041e80104c5c0c0040e00144445502c50301c22000461388a2540c40c01e0303040c4a0049180003109030040c012940d1081e840011307118025045184801a880c107030360711a003024507800c4000c0e00807051800890b03942d00d02100070800103e800c0e580d00d100344c1c1e0740c00d8115408522401a140041e05102010700c40030320620000000c130038000c20140c903000b000c0c4101d108840801540c20005911081044002d103054070600e015156800c1c0918994a018141d520080710f610041e40b200f5504400442d56600c0c1408003400c0c1800c000d007034140e84041c0300580c855181000d88400340002c04140000c0307803191045054504082140d1101c03801c061a83c0e500340c400d50407031000303018a5031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 922067446 1250 922066196 922066231
    0x709060608040305071b051225121b0509180d030b0901050f03011407020c120c220b03060a02071b18021c02070c0602160501090311120f01021b06010815 67
    0x140d554030410713020014200101881c40c0d035423107542400084401d0361078920034800010000484002000b0712b919600840c40c1c030044004111072480303001d450b0003a40d00701588004001d0100207064180050350b80030022108010080344c0c049068039001d040c5e150f0002c0c6100010015820080480104001c0050000c1480d51840070010502c074000c48402005078480120344804d418541c900020b00401040500100824100410300f060071900800b814010403000707070b0b449501e0551014a401c80001d058800d18240800700502035000540107a034102c5921915503403a070080b103840e10840f04064540100441c0c440754102c000e402a40e08455079070303990204c0c00002c8040c0e100911140e441207051319105030070040000c4c6008010400e0350f8000e03013140f0040c0000d0707810581e218100d80c0d110b110804080050790110b0008041181041454443d5102c021070786981074003d05103800a4450441d03a101c1c03104815561800203208a18058021031803250750012900e0100b0b40c00140c80e6000076000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 922068696 1250 922067446 922067449
    0x20301080312060f030607030b010909060b0313020a2301031d0c04020a090305011407020607020613080f0d0c030f0c09051f110706030c022a040f1d0709060608040305071b05 76
    0x460111580c00008c3d6840c00000919030300f1074910801742ca114502000047e05155088919100c040c0c40140320112112200c000c640d85c400d0988003034542a00d04074a5a0f4280e44942200810301101c40d000c20700b4201c1256400182c01084804030f280d1038002c01ca40d21400702030000a5010030b090768100000324001201141c1c090260700012480c40900c42c59624140c4030080c203101c00a440c0b6000c41d0401c10038003081c40140340420f0003072034025000035510034000d6000312240c8122011000002c1c1024904e04090f0b1f01a0301400540e850204107004050140c4411641328006001e42a40410310b034620b0008c0c9040407140910007492030400d1114419815130880c6004000d60004001036260740b41014001d81c10300c504500d11010340000842c000c0c1081c00d49942c0102048940d0003241d0700c800c101074614094005220180d040017070300b84681082e03043c150300d41c2e034503000b00ca03105414507100250140c440c080c2c0302c4c450b54244c0e49150810b01c0c65902c0c5400758040c4d000d6101409452840420203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 922069946 1250 922068696 922068703
    0x3090d0c0b210a09020d1515090c020d03060b0406081b0309100c030b0f040f06350a02060412050304050432010f15020a080d0204050112020301080312060f03 69
    0x1031035902c146901d02800b41c2c0b501c41c050314900a000c070b4030860a102180c8016240e003d02c50300035070b81c8000c0100b101c81030112807200038000d24140d003001c41075071200028100280d5000c40d413148000d5080c2c45160000200a07015500300b8400c0d200c003814100f00401c80ea40c8901c1d2481c0d00b1503007940700f11a5084c0000c800e40c2107500140d41c034281a400a074000c03442c1c101c042c4101000307404141018000c00c0e0401000035408a41c1941442c001d036101e0400c04c019402d2580040003412100e10380c8140f0090815942c40141080000c070124503990507041e15000ca000240130664541c0140000e14045c2440c02c440010b01c0d1980c1c04076240d2100303000c007083c1640c0e42c1c02424105110510403502084001c0c44c4100b850495030018100c0000c41401070003510280c0020f41e050b100c8141e036841c03050a039030104a142400d00716000c1d02c0700502044000207501960014411a40d09a03141c00d8800c0c1209043c800b00d100a1080f03d00c030364000c012504400540d28102a403200005208590300d03020600400d08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 922071196 1250 922069946 922069957
    0x9040b01030227010809010603080904020a1107030506090f0304120201030e03070b04211707081b0c0d200a0f080d0e010906180804031b08070308090a060507020303090d0c0b 76
    0x43d0950701d2064410039640088103961040064001303000d80b51464407122401c1c030a01010342d0203560005100c090450051802d00d4041c80d61000312112a640ca09240d922120107407116a2540a1101000394050000046e039080e60388840c480b03d901e088540c010f400a10000d0643c600780e003c1403113072002055620130314910541c040d207580f154055202e40343c0c03203070703503516411100c05d100207114043d074451540c820703030b81e404001c5082c58844c548900d8120142c1e519070a0881d030001c100040e06880c82800862148070304a802d0f00c40c10440400307141101c00000140d01034119030f50190341d8680110740c100d0b0411140750301030400545030016074000c05054805400704008281c1d100d00324a02042254030174040b1145014103000000d40640d500c860907442184800b81001c0d6400a190141850781c400f000c0c0102550001c035100c5541d00d1400c040250044e24207680701d41d0303013264006105401101101c1e895580200a103180c220500100f00300b08070b000304181d071350086260002c00c20b03040b030030000c22 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 922072446 1250 922071196 922071247
    0x1501020f0616020106050402030103080d2d0f0c0207321329010507060504080409020a080709081903200f0307050723010c03050d0507030b2409040b010302 68
    0x5200b6508040060309442c004e030712850042d0300c10001040403a0030360080e99005520b030303200400c00840b01084e560300c0e800132404284001c2808500502c0c204035640c0096084800c1c01c50038080c0c00c00300c0c2400d0b40c48046501c036280c4140c54071007450541c0240c1d54925100d50440201a00d804070368000452007015100c40120302c0703240d4401001c002c08048004928210310744032a0341032880314801c0020020700075000000c0800c0d40700e601090800c0460804c0d6409081104e40c21510b54001c000b0051a411080d5140c00210341d0403180419880d50115440800811820b0704034085051350354200c4250000c4040c83c680d5402203032000080d003a05000c1e40c01242d10f91801981c0b10400c500b44281021600c0e40200554809a04024002603540381e1610003004242007550018031541004e9480d48641404040040e1401007000a1036815038040424004295a1014051401c401650345c05c402018a140141014003440c1300c2840c00360080040354038180f5004d414083d90b107030788200860020340c045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 922073696 1250 922072446 922072471
    0xa08070c031b260316021203070f02121b1e180a2909092b0905010e0904020f130f0b10050a0806010e010c020619081501081501020f06 59
    0x400036180403002043d02c0f8000400c01d852081515440030b60340b40300e40980b50000746072100c880d20955444000300150f001d0f00400303603907590201d464440c4854500000481c8a000e40c052000c20020340082c80f4551900d550107070301c1042100d4400c0128800c910016208184d000f201e100b6032030303111051440c0b0040c0c110307142c180f05810140e11400940d1580c02000307046100e01d02c00e5901c40c110852201c51503000584041841d40c031100d228608260b80600b1110103014607410680380444041a40c43d582c0c01c0c152340f40c10b400d603111401180d10301c1225117500c9d40300803100b001c0b40240c60003150791100440b0042c0034440306c80c05206440b040d10b80c00031030104031598515500b80c01c0c0c148a901c5500d040c4552074a9840d100642e4000713040540d0144c0414100008803c4450700f43c0d009040c1980600e40082a442e19030002803040d4103009031003800700000440810114011a00c041c4d03102c8048081611602c049548218090001e20b00d1000e10074118030540b90650301c4000309105007401340306000e006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 922074946 1250 922073696 922073699
    0x9030b19093c03050910030e0a030221120411030c030d09150509180c07060204180f060f1a22030302063304150b180d050a08070c031b 59
    0x28080360b090196a61000401024407480081d40c003200712074440b1000c44205001410a00b0100c0081c1001c00c0007014620544a4040905800240300d5401124044000f80d0380407505d90040c003903000d514140d1005040321004100024114000f50302400ca003d001c8034a444000030000786015a80d0308e501003c640325503000d11a1019421204031a5012810242e140480e140042a4003122001e4000361700c1d07550300046542c0c042e002040f10740c0c440e0010f40941d00e4603165585a003c0c0c0c2c0360181d038031200030311342450030a04003100c3c09490202c034964601d80182a1178460302c4100c80d803040d60035a00340801040710b107185e60340c6000c1801c003401c00c80742d0a030b4000b030951802924000b005045018402d0883c1c04c1103800d180010303082c1011082c81541e07403241895007804900a0420a03000740f03d50721701d00101040e00c0340e0000c007a05545942003141d100814240c0d0038000c10103030700f001c0901070f40c0203040c0d408040f41c0918000c122680c0304641641e0718a940752100214400d0074121b4034458020703040c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 922076196 1250 922074946 922075013
    0x6061e170a0203120d06080604121818051e01030507150e060708121506031617040308061e030a020103020906070f0605010e0a0213060e0310050c0c070609030b1909 72
    0x1640c80940301e040b004081c2c270709040d180d582d10031604d05484010401c0d212610300481c2020544000200359142c0306002114080c01100080c0008035050b034480070140f001044100391040b0900c2c1240e400c0b4001c0c00c1918205170301c0d543e244910041502c1885948801d180ca141c40f014001c000b807a003d12461500d800103103030700b0500650301a09440898004000010302030381c3d8031003240e804ca04405400340207500912019502d4a600a4600882548030b000b0002850b030000c0c0654400c11088031841452881911010241086054516055800b00c0302c0040194001e40c000d24460704000c2c441410000a651800c0c0550364400d400c5031000e0700c8000401029118240d441e030071a000e00800d50034001f04420400c440d4540f4440e210410032a00f074600343c0c03a101802140512800b480092080b8036140d84464481e40c091107042c22280f007240070004101b48070742c1ca04010b5039448603005032181c60704444651955a00b48084a0086e44d5400e101c000910f0404000c600c5019100d440008018101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 922077446 1250 922076196 922076201
    0x60406020c060f010f180b0d050d11070b04150908030703020f01110f032403010c08090c04050709150e04020a0c060506061806030a090b1306061e170a0203120d 70
    0x600c0b0f01c82640c0c403100180404c0e00201d048900741c940c070340040704092030b64040101c05414540550750300400c038104a142441000b08100040ca0106e88441c4500f403d000f42040d5100b010f44105000250280028092110000310301c4403210440e182002c3d038992500a414295030090b101180560700c05049141a80c80a0046040510304048464144441c5001c01e1405120041886400191000141c002c160b000b070386825141d50060000c002d039021960000d41105015103182d141d611030040750358124070300342c01134a00c10486551910301103490100030700c002074200785510b401d00013070b540d0002c41512948041c0600050380c0c4d80f46080c001250800508a44c00075111074090340042280f8149229055107405582030709544259990b503584540c0f0740204058440207004a443d5000d0041300d40254038040c0050303010301c4080145a0380d80c0c3e80700300140e00070800c40308900343d50042002008001d100d89034000000c0b800355002c40e0b203250300090500500c00381c001390864002c140391010142c5031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 922078696 1250 922077446 922077451
    0x71a010b0711010801050a35100f1802121c0f0f0201090803220b0a020901020607030204211b06030e16030b04060e070e04060b2815030e060406020c06 66
    0x70b084c101c0c8503504140104070200c086004a80c0780000101c6919a4162101608807454a682240c2c10002d03002d28860740c0c40d01811068000d0b001d05000c03050340c561447c1d100d00e403035207500070424210918055080c05044089148040c100c0e01a015905000801c40da002d029511172568508000018085020b041650b984800c68110ba2528800c440021070620441e03821404030040750410f805080781c020402c414102000f03008481c1c10083c4041d060700754014240c170800c242c0950b249541d55020490403400786104422032032540b070310032488503400c038820902c1d402d01800d480402c5202c4a1200d00c4030900590249000a50310420903848135400d0051880384a81001c29445481c555161409100e6015001030710055450214941c0c1000401808004105010818100c1c2c509424a50004d08a5038180b50081d00d414280b40006480d402d90002041d03409030000210b2400c1440182d001500000740d10141036071103000103210001000994455881000301607511484c100300c0c2424180c01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 922079946 1250 922078696 922078699
    0x504021203070c090b19180506090c0702041d0303161b0c09020306040207170a1e020607030b0604081506100e0102030d09020301060510080402150a14071a010b0711 72
    0x14804480002c1001c1031503012120520808100039010f040001c84c3c0c40804e030401c004041440302c0c00510761b807c049690f291031059160070083d903601d80d414000c003504121030b01c400c0240300f000300e0401458103034495108030003201d442138000c950b011055461070780240d03182c0170381c0b100c8580768200b92580700e80b6004035100c4080a0206c403100b03607924030b00c0a00013030280c07007800ca4012000400c0ea45450703050740c44040d040417000400820381c01021025501c260b100344005502d4201d504c40d034011001419820060b05d6000788516902c48904400604500b4052a400300d010040040e01314401c10401d030217922440d40c900704074100039080010301c0003c0148031080c04003886854203943e8010094a0b1804030302000411240c4c030510000303004050580165034000c0f8101408201540e210608901c201d100760341c84e040100544c004209140601d002c0d640000b416814400c01c54000b44000d090118071600707649060744025040321a00c1c030b000343c005a09001e004108030090000130320301e48400200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 922081196 1250 922079946 922079953
    0xe150603190308040503190815060702011409010908030301180e0c0108010308030912030a1e050103020a09110c191a0103020307260106060e131416021005040605040212 74
    0x10078a1550096044032800681402581ca002500740135090049a9000030034000c50641c0800a820107825880190340c020f110220360881d402060030008100c9a00d2034050b107a12912480041d41c81c45260311603030906041100422002409110802c080e6010700546000da40b81c41c0300711003501c41100c0005c003903503066500040003200f440c1d0b000310780541965003080c076441d600d903640d4440c185040004900022041000420400c2565032948011607002c092007c3e041100c1d4468070410507188280070103076014484901c20003c010141e8040200b0107040070a090500c881100340c00e040c0b5912202084900e110000c59404210309814900000c2c0d201101c240354550640d0003080d80c496090241c0e4400864072140350400246001c0c03e040701050f004c2c0280302003a02e44000070140d4600944080c01150b1912142c000c0d5010b0b806031110326602d41c000030886035074076080c014101800148960640c06940340c0b80103581120302a451243d8081d140c0400c440c00c081c41403200032924840880c0c2c0030380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 922082446 1250 922081196 922081213
    0xd09121215140907050c15040c081609050703140103111c0804060c03050d1a0103152912040809031204030506180705060409050a0c0306050105070b07120e150603 71
    0x544918040710318505071110842c0d84e4801c48169414400d0380e42c1410300c2d1003140d10100d4006160402c182c8240d00c20795885902c542d446540d90790304c130f21000c1040c1c00c0700380d204000e20001246521482d07200b241c81ca004aa41303020100311362500c131403c4c0c0059078541c204400840c00d0741007400c1c0a00800c010f4201130040302e803044c0c5406655010750700510007001404115001898418003e43d03000140070801046891840b560040c8048081070300117000c03a0801100c40040e00780c9060b000215507084541c20050382c2442c410f043d403070044aaa100d884002402248861031007290468456403080300c00315507656424040510b030224030508100324690800081c0300060380400d44076044005140082e0340310b550341034028108843ca030090303904818040307000103000043d07400c054000c0c0c003006420005000410422400d540c0303c0e01032140800c00401100c00081c1703c841d903065000c9035514210f42c40c0c0e1450310110003a1031550010b400c1a911205030402038420485180d0340040d800c0b8000c01040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 922083696 1250 922082446 922082459
    0x120506010e10080d180e1e07050c07030206280c061401151107051509041a150f04080105040609060b100915021203130309080d050304080d09121215 65
    0x14641c1032146000c104117440e059440d260145c200801820080381c84050529081d18180b41040680b5481580712041c0310100b82442c0c010741c21185c54044000241c440e941c21502031000d43e610160762a1102d4000049602003c501d1042d110328a000640e1503007041c02c03050034258182c070603014042c48440e80c00c000400101545000320742d680812400d08200300c0517004105030404601d0350141d9000b55800542c203c201050030700030401e042d0112000c00c864420580340d03a1341d000b6030341e2015801500a00d40184d10079180c1003e04008240080031928007500d0b02c030b505003526000c0d00c08899150f250fa410030b080180c5409403901106c000e840c00b2018000014000f00b055206103d0700303001b000c401280d42c0b04d640c4240800c0d510850000c1d4915aa410460000740650000050a50008010340008a0b5950010803c800c0341841c60f82d4990039619180c44001251b402641300000f1207503500e1134040092140480045440841d45694801d100c000304050242e650f1004284030464142c0f84c24400e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 922084946 1250 922083696 922083703
    0xe100f0e01150309060e1f060e061c1a0415020c0a12030e061f15021b010c0f1b0609060c0605060f0603010306020406140721020304120506010e1008 65
    0x111001401c102e8402c0d07040c80410b070700816414502511441c18842c8071030405100043c500f1400c4000052a87c02d011124000000c4030214042d01da4550b258201244192400d0030554607140c1780a549110040706581d540240c036100358251222104900f800c200030700100c41072043c5100c1e50b5100c25450403515207501c6480d882054001001701030080f640a0342c60740720740c1c02144004200000c8030050f080c0042da10b0b8900e00161404000c11041c55030109528105001c4408094803580051807096440d090038809030300d2420640341080301d494a65404190a00f1520008130300921007685401030600321400d4001c000d402000600070025020000d2607841669004010780240c000180e0ba15200005410b541c0c03a144003a9021074084004002d204050380101b04481550311540c659000510020380e2034083c0c1d6101506015052041032420403500b45c440b00c44880b1441036a2519455804d880c03c2c00301e1034ae0040e50743e544600e006000130b07005400b00c1a00f00400310070101101c5d180490a564 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 922086196 1250 922084946 922084949
    0xa1401030321141803040b1803121603030e010b0901060507060b011d1519020313080a08090f03122106060c120f0c0d030902010f0e101103130e100f0e01 67
    0xc1000401d0340360303c0307440d070074000d41b4044c040034914142d60310102424038211452081d01c8500c6802000d1031440b40700c90f00c600700c0c2c2140741c08050003c2010301c01c1d14150001d00314074049400c0341d500c540000c03070907aa6001800340a807050340c5505803154090304107081110003c0d41c00da810300c40d03007840c3d82c4035460346004007a580b0304080f15105240100e000c450a0320340101c559448a401c002c6002e50f003500d13000b0000d4050200c0e0190640100c40c0c2d0b5200441c0d890817600c0000d044005e04002e944414204100d40107a02d550240c100d078002c15890000d078845600c2034100070451443c0f0748089a004503125501c0d6003140080b1022401c0000f100140b5480300140c3c44414040080001c0c03183e1902003610582d0a900c20180544066240c1c2010103405440c1005040380083d90100070b4094990280400000e6000040c6c100d682c0314003030220668805100030810b042c0f9120620070142d0501c80b040c00200030b46583c0a0300700316401c1004114240f0344080e0825110908541c00030f20415440700003090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 922087446 1250 922086196 922086211
    0xb01061e0203220906060203030105030f010b150d021c24300b1e01061806030506030106120507080d020a08070b04020604030f060e0f01060b120a140103032114 70
    0xca041200c86502103c5103003d07485410796500340800081c0c1c9a07000710196048600c02d030191400000c0c13003070078507007210619042554082004803140c0c0340c000301c4030050300d02d81220310b00040ca4040c80d2002442a480c2007001550241d880e0800196009146c005c10000b002e200045100300504000000b03085248a002d00c00f9080c100d00749018400400c0008820b50700c1d0491a521403a007403500b03140c0041100c002c00c040054011800029000d4070509080040e03200080c1010340449c20094100d02400000e402164190348941001c01c55074601510f03c041e9a00c80da0081900e00d240c0704119062011040001040d074004801c4080030174104012102c015610182d001c0b0995507610000d041c0f8091a0006005030046132603c4042005650181c4c0d2255030203400c0f5111240c1c1c3c0e0460500340c4001e80624032142c1c00c14055603807000c1000d456a0f0300b08022440104230241d0144170b6a50840b4241e01c00e4000492514006000024080c68a0310700301d2504814803c81003030449140e1450409896076 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 922088696 1250 922087446 922087477
    0x1030c110303190b150c010b0109030302031c021e090a09060b04092a270f09050c1603080106090b130e1b0a0e011e0e1302090a030b01061e0203 63
    0x903d6044a6500a01c020303000140052101c0d100c201112101d41c000c000c507045a5032a01405446641c0524050303001c8903072550007140361403c108110614036054001d102c0d00550240420b00e50307179552441e038040c15191070480c03503200c107680e0080000c40090b652103980d01d94548803052010342c400604403070036500154404110207181c5448900c02e0503d4803458452400f101500d400300e1a4032100c4240b10b0107010800704120080c503804030a185202d0712030b840c041800c01604002030b09403508031590103400c4250041c140324002010045440b82c050017100050190801480016009503170b84000d008458042824034035180011918402c49005d100c0480300ba607000110380350134a281c181c210003c0040c007191102800000a066804d07180902404140000c1d1101403030365240118440341103003035039441c45109e1110b081c072101492001511f001d054081081e42c5d03c5484200d103c81c0114440c814011881d8074100313005011516001030b980e01000800e1801000f01ea0002c04d4810f0b40c64000c016 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 922089946 1250 922088696 922088731
    0x10e041e0b010f03150b092a0a0f021207030e09091006030602040503070501020a050c040b01021009050d08061807030203060a080f06010911030f010b070311150601030c110303 77
    0xc0300c4640d21004002844140404004a140401c8504150840748149034010041100b555101c0039921492241c0b50407541e2800010348001c8001c1044c00c160545c404c52000d20500340d000350506903c03203010000440c460786444c0da241c0d80e040100b503000c406548599070078080a542c6c001d1070700b00203605c9140305503441404201806020f11101e00c048001c44420082c850b0b4038a0000c0182d00306204145c842c0c0a131403000501c95001080305c103142584680a04070030602501088010114102c415045100701c101000c0390320960f200e81c00781c135801400140156000000001c26401000744410301442905518650001500c4002d6400401d076040158499840303a001c1000e002860b800600729100b1700000d001c41e06400709145040e03a001c260103200b05503c044d2500c59502c425a801c190946402c4010420b9550720f0018200e50b030722a02d810310210110400761803820352000c40380031350380e1314510030f20030b00350b03010721a41c2c4800a050401828150255030425280e020003030000100070b100c1500c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 922091196 1250 922089946 922089983
    0x703091703190509090405160501170c07060e0d0203030a1a01080a1109060708180904020607060e0a02090702150105030d300207051f09020f0d050c0901060c0302070e010e04 76
    0x10313180c0c0010040c2c05141c1914080c01c0240c3d8808400341c525252100c1ca44012407254815805444c03d0070a102c0c0c102c1550704d0300c60840711f0075400204140c6144d03070f81c1c01c50000c00d9001400302c3c50003102c8940c011526130a096a40c03004660320184084401c0d0401c4800f000d05076004040c9580c05041c0b000e00094021507106041420312401580e1076000e1300000b040c50402003c48090f20210007141d051040c03102681007840224401078034086e600600c14020a00000e00d150080c0030310102a00030360310303205229030100f0440d440542d20b030380150b01320050140b00d5043c114641401002d044000740b201d88000100649003c03001000c5401c0219441070044012950902501030040201c0086540d8400750801c26203954554030403120060700c11320400c40c074441501030a15850f0700144103e031780c04050801c000c0040800d100884a40c0640717580d4103002d580341c1d90601e00a061580ba40c4501844503d0b00900740b90241c0c01c0f079552a9500c00c010f000c102d001c808410b5100d5400086160100e40000c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 922092446 1250 922091196 922091207
    0xa08040b0c03150405100314031c0e0307080c0703020a090b01020105060118092018031b01021513021302091c11010c1406010602010b100206071706120303010b070309170319 76
    0x1f00040e1450608404038400e004000004100c00505074024503015000c8000020540d1085c540c000c0c15680107001103404503404800a084840c842403c0700d80d07540c1e0303030f0340403815030714a03540881c0703003540d0303803c10120b240d40c0a009003980101c092030007003c480b045814545029055003d80c1d046540e4905004110030800e40e1216241a0701d5410581c6903151142002480203403901658000c2c0034100e486541d840008032510b400c9030058014200c0144000c004039030150000f4003c02c000042820b4400141c0c8071000401a40840701c000944d60b103101005006056850036906a401d070710661301540840e2005001001d40002480d00004440041c00c0c40941d561b0450074050341401140c0c0006002e0341c05600c0b8004103002034451201045901c0700581c0c4440c0119140808145400d41407030b4110421020309600c09402003030b00042d0310070700082c10b140d41c009820011000c000041c8040130b15402500302001820700d00c1c1040031410301e00f99415164011440b010f000c4030201c0508140349800790 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 922093696 1250 922092446 922092449
    0x200f0405040e10150812161b0f05240c0a2001080c0c0309090a0618020d0b030f0712020d12121109060403140c0301020a08040b0c0315040510 62
    0x1031040c04421103844605850f95880c040c455900d92030107544600040068040008541c20a4058101d008510448011301d074882103407100110841d500820010344100451071000e82c5684260003400e003482881c4981655036000b807071103400a0b1000f001035a100e2400c1580d01c00c403500c0041c2d01c0e0f0008410745454052011401011452441c191001d0303d4040c0707840c00360254091381c82848546828038080417511943da11810700303030802c2040a4103424030b480f0058103c80707404000140195111b03100c1c01c0d00030722910f07180406600002c4485800059005d09000803034100d01a1100140548216a4555461042140103100d40c22a83e00755582c104e545026140c0160302103800460a8400800c8016031080e01140c0e82d1500701c20354100704104050712820300c00035102615007400c6840318100c2d280d446600c50905c1c410494a00c8c0191020b002421f4001e0a9440c2c0301c038141054980207240502c0200f0a00c0c5000c0b050041110098008054481d281029500010240c88030354000310415250f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 922094946 1250 922093696 922093699
    0xe040501051b0427200304030e010804020f041e0e0f1002090105030f0a09050105070e090f01060e0f190801052e26120d0c090305100507020f0d030204060e04200f0405 73
    0x900d2440ea059900f45d4002e500c41e078881c0c0c0c0c403c0c40d40c0708004019030b01204240e8002c0e42140c0880c0891140e0b050a0b07101c071035580700c5008a0a020b071015100305c030507075420001c0840d00303420400e100801b0b41c9003041380d46401e90a100d400c1d8285030400c00000c0c9240001880041079079016404110508825804905000c0c0c00a000307010314580309c1000f902d040803480b1114017459400e0001060304118042d241d0603189660f036444030029049040203800a4460030456000400602c40244272080c5251381c40204125400400d0624140e00210908680034a07030011003024a2404615880c50050290031b076041c500001002c1030b0000340074030000700000399441d001c1c8070300c44071041c400ca041c8026050b4103041803400e202100c8012000c40340744400340f1008050b50302c1034101d01c0c43e0003240d170050717588030740a40f04491800d1081000940f034203401d121400e001c00d50004040c8017881d481011125032160582d4244044051202880095070b1800008407940c00007068014030400160704660040a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 922096196 1250 922094946 922094981
    0x11060c03070c0e0a021e09030f0105040c08061305030d022a0a02040f060b04090b1c030c02090121020d17210106080402030a0f0204060e040501051b0427 67
    0x14514003081000300a00a003d454110340700094070840d000d0007112076100c140403180d503210881c207070740c54000c2c0c03c155a070039454020040240c0340c0701001d10526100303d00900424441620704258242810f1000d084010701c1c503207040c07840340072800001c103c0751901c00c0101d00503520828a5901140c648490001c1c1010307000400d820641501f00007110094103000715400c0000030204c4455100302d034031607c12180c1580e400d000c2000921071aa001100c0a5005401101c6c1111846103183c2d5805135002c1c00c03004030705c4203c00c820942c200b4107255405822a18164000c0c8800c0e121290110800d214000788a102080e92000030450103d02c0f0721541c0301d00484003600d400d01900c4a900300910340381c0704442d202c1071740000071381203209045582c0250340140240130680003079244e03d560802910000c0e41c101e5255440060784225140344140301c2c1c0c0c0503030000a440d0400203401650152114191104180140400d01141c000340001d9148086004408000030440f8090070780948200a00310482c1e00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 922097446 1250 922096196 922096207
    0x80712020a18140f04020d020409050112110306060108010b031f060207091b0e1203070f060903020c0316050112110c07030201080106050412081c09031d091311060c03 73
    0xa401030b149080304590740c8801d400c0e1540b10228034000d42242001950303c41c50b0389807442401d0409600400c5040310004000d4074194480f800c40701510406c0e0b110b4040034240d0601803047c8415844002c08280c0c00721301610036400d00c080001c4c40040180a281448000000441d9030810560743c81c1408030f030707000e050300e006590f103680107074580c28144900786840b0b0510700c0c8245280039003d208160b94078142c8501d10074038540424400c0c0c0011040901c0c100780300401141c0e012817280d400b8124041e1103078030003081801c05850000d0402c140409100d0107640900740c1e4823204151600c2003420f0b0b0340300386020120410042c51400103800139055540b01030707200240e400700c402000304c0c0e1502628000c0c1c9400103107980c0d07000110f54038407541c0300790651a1240051403001030341080c001c05c0940e6103a441d00403040004d8071102c08950300d503603003140440c00108000c60340c1b0240b58416204000200c0d05c0540620781000c24030544000443c1c01020340c800f21301450140e94a030001c0c1c0d00d84000741811291500c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 922098696 1250 922097446 922097467
    0x2030c041703120f06010207060201063b28022803021e0712180b0a0905190509090106031a0402030f030c070f05090121080405060d0f0e0d02070608071202 68
    0x1950185c40443c01401201008524103005016883c2210144c8400c5544444006400c022025804240044030140b1440042d80068040b5115000d0401c00d0403100002d000c1d20184a95000c1002090700594014001d00c0010440800e09220314070841e4507940100258080441c024400c002005c0302c2c504c1d07807110044101112402030b00c200ca10070a645651442c80b50010761b052040c00d00c0c6804044045c0300305103d851803c001070035064005041888802d0303120000100c000e5186016081550703d8030b04100f006141c580181030300306048000801482c8e00319100c00081c2c40758501e405a4134503006001c5011528200f01ea4410400f44e80280c94441441040c01611002103225181d00e400e04003101041a2030b02c03640740ba0417100d01900b4000350380440e00d17003000c460b0606503058031006014072000502e43c540c030f00101140c0c1c80443c40014452002100f1004560092092078100d038000100c0d0900c6139000507080e0b003a0303801400c25403180e03502c4400c00c8920282004584c10300c580082480c0381d10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 922099946 1250 922098696 922098721
    0x109050306070c03141206041401050d03050f0d061502070b040602030a0e032b081b160606090608030409050901090209010509220803090c0d030207090c0203190c0c0902030c04170312 80
    0x1840003248d041c080340504c0708410901400a02070b007680010b1100c40310001074028001000000c040e280c125080440c8400304c44120f40241c1c1c0309039260b804100070115481e6040c00900050000c215085041c2824814002d40d2400360040b01024040c0048450409075820841d844a903062008201c0d840d408442c0b843c0c610996140728003001c41c078444003007580010940c130841341d01c58120308640d0406455164201c90381585c45004e0710080d40e202d0300820602d16a01482c400b60081c03000542d680e51512111030101c030030062115120341d241044203001695500c2505044603c2200d51840c2030300c91050303605409a140040c0050072454030011000c12002c88051407044811500b41e40c0803000041c00c0c030000c080304080c000c0041e0040c11003440801869888904032410900c101c0707081966582c03064418241c03c15010300816a04540e9034200402595140e0103030008034825421801c2c6072910140c41d0145003c0c10b00145100301e60a28800c3e2704100307640f1254013080d1884003e00b4500ca43c80d54 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 922101196 1250 922099946 922099951
    0x203180d021c14060121080705011103101a0409090519061505060c0a0b0907031e210903080a260a0518100504031803080c07050109050306070c031412 66
    0xa90700d80c008051800c403903011407514103c0d1007018983c4e01b26100b9621451001900c508201e842410a100110108000340700d40500300c0d10440e10140d890425a10344140400380d5480401c103214070186401000a03900d0030b86048445002000c0360848540c0303070040c109000c0038544008551014051402d211040c4c00640c800128400100001601c0313406003c1584908100b5201341e510101100d00007907a03500140394020b4402c81590320710340d1642d4a40900c0346041c01040e88000310f0b0340051b02449405008454048032208a03500c02c44840d140c0580070040b240b1028010b101d000c1020b070216809041208400b50800c038240070ba10110b455801402c00c01541c42c442050702d000f00050405282c0b580800c560300030b040080004071203521030100034100041044081104400300c4010087c9a0302c15038000d0342c0705041d425150000d502c0c03058545105ca130320003410080304860801c501d4801140d820f80003511494600c040641505007501c45c4a4900c880d282c0100000903102040a0811314160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 922102446 1250 922101196 922101203
    0x309030711040207020603040311010b0622120209070c33050c1c09080f0a090312020a0b0a05090a1e05010f02030103050c01050c0c0901090b09070f0203180d021c 71
    0x80600c0d0301062104a0050003130007901310b40304002003808640036080890152050000115000d020031000c9010b0350030261103030190114004103014140d011040050240c0100400d01c40c114107150009540c03410050207103010311110140e41400c0c0121001076070800c8001030810000c003420708c4c3d901c6440501d4081442e072175500c0e21012030020803032842114403030180407010303840d551340b00c001d18402400c0c864002c5594441c2007000d0005002c0e00030140103000c040f61200802c03940b5604000700b01c0102d620071202190002e186080000380c0f90014240c10038590500001d2643d80c514040345460410700c400341c1400382c40b0100e903503103686900894214030f1040b0002d0007200a91142c2c201a804280001030458010450070b100c5c41d40b007807010300072103008501282c4181081c4404a00c0c900000e03088026410344425030101e1034100303003071090380040403031038548444061520000c0d12030049401c980080d46103889500000d641c4c9108074040f954000304004500f2074800d40101a161601c0400c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 922103696 1250 922102446 922102463
    0x130e040308090c0915040f09060203060909010b09131e080d1413060e160f1a0a1d030a14062517060a0e13050609072105030403050303090307 62
    0x615101c4020410649448000d890b11455464114600b104c4845e0000000d4100b46c0e5806844100070840c0a1007113000e00070500166242402c0c400c0c443c40b0400188000110380c1060a084100d80300c940070950301400402032110228014a082140c1c81c59641000380c4080c1c1d00d48030642132140100050542c140480402c200030500703021449000e00d8106c0c0d4410440b00344c00d0045020407070383c1d08544003003044102a5036034048400d452012541d1190400700941b0b90420080c4003140035814864a015049444181461000c040c002c20580903105100052980c41d0381441d11600c08100c889030043d80101d900c03000d46181082d541d61214101c0b000742004041c05002c0305e0300035644480c0186182d82d0368801048410081c02d0760240c2c82c014054a400c22512140024040f640501e014000d80c2c2015041d0100d5080b41441850908007400c0b0400c603070048041040401007541c200014500c1c0f800440c4004200750a0003802c50184e40d1000d8028000001017100314038000c00180700d0503128841d503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 922104946 1250 922103696 922103701
    0x40605040e01051015080c2101090903230922020a02010203060306250e010c0c14191d09030910022b080109090f02030714120c01091703130e040308 65
    0xc400105508240c5c5101290311040403682c1903034401c00505010400300d00001d180500d9840003c51260241d020315112587d46040c10200355121070600061105892030141d81d0500b201c078540f0038443c21041c280f00b103107842c203030100400c803040301ca86a01c0d1503540119207450102340060f000c1d503c2200c06c2032090159000203119a044102d102c46802d8502c0074844001400f0602900c02c400d805400034140300c43c01510000248070036000001800c00785041c402c07070030110003d00008100139804015840300080003423000c40d01e8401c2510300d96202c52400c240980b106404c8078154400c2695003600005001021401c0c3c1d90005810041c1e042036204140e0401d40f91030b2001c0c404420500b05000192000c00104000b4074650003442d9440d00401a85103da0200d6001900e40201d80d0b00c0480789581e013181c03488081c98008046a20100f480300508076124406000900c10001406004203c42e5030007603401080508001f564070000a8110a00d459901e0750b4950840080842d0704030005134001d0700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 922106196 1250 922104946 922104959
    0x501020301091a0d0819030e0d111e190615081501080f060601081f06110c031216032a02040c050705070501120e011821021b040605040e010510 63
    0x28252070085e0818445420607034400c086d28500030040e4905c100301a265204820b031402c041c450f1100c840c0701ca80300d203401600c2910703d03142411079030321070700035054102c8885940b4000003140c581e000701a04d0400800c00c10030342ca42240140800d00704000402140c400c045091000062101350041c4040e580d08003681e620300141c4e681c0d034907028040700c454204c02e0201d283c40d40038501107500070f0101034200141c844820f210130f403003580c03e500c0080000d07910003401030044014480e001c9040001c1e0044c021400400c1c0c400c5405108400081107a40c28800c4803405041c446e1000002180c51320310080c03c1180040c548081062903408168810f9250031580500c09000e9011140a581d018000c0c0082d146000010340e0034001d11b40e184090141c5480c00303042c01010a01c1654940e4001295a4805014a042c80000c08404009034581000c24103c0c02c448203800280340c00031543c1c40400c043d400090140410090009544140d4002d0f00b0003403a040d07041c806400c03031031003000000d2504806540d14903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 922107446 1250 922106196 922106209
    0x130e010b090103181a0a061e090c050a1d010201092004111801140c0a1b08030403080f0304030509090a140603061b07020a0512070807081618090501020301091a 70
    0x1001841c1825070f90940c5c800000742c4002940c0007088060010308031b80e0317072132407036048442011940c1d44400300000c0612a0007403911412058907114071b4070300e04000ea40f0313070081d1004107107030700c0240c070f115161050800c0c0c1da02c01d4016007039103603200c00701a282c00c00520041000c19003140440f0300c01c070f0a02060092030001c1c80300740d40c85841400064540b40c06c6841c010744805804503903846410104100c5000e242000708010860300e4400c402d446030b800c1c01d025114000002c4e41c0c001c211642c008100400101741c0d29000c0e41c044c04109519a9545d4403145400c2c0d8051244205d081d4005030a802000b40f42c418581c41b40009400c04842e080c00c598400b0700b05620b0b1001158580d0846440c407104030441030400700900b0b00544041c01d100c0341652907100003003402d1000900d003422944001c100344041c1100384840d1006201010050044500404403a8500f8206002d403500401501c2101201c2c1546504146001034001008564950b12480004042c01c041c0d0340c0c04803080c0600c544183c1508141307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 922108696 1250 922107446 922107491
    0x130f0f180c0c060c03201e0711150c070f14010e090a09020105040503031201211e030512010b04050f03060906070513081504022106060402130e010b090103 68
    0x1030b40d58640b070303551a64808000b0189107018400301565107186d401c00400c0590600c00d81d44401e6080c0e1f4888048801640303d00010802e00c4508580601c20b141c0054404003a980100344210b07100300480d0890707181003075076019818030380c145407007241d0700000c0803415105000c003a90142101c04c0a14042c003401234070410485900550004210310004e0103614a80e4006c43c0f0152052401903e41581d40c000a81740d0f80200c04280c40007080f500042101219582c41c2120b40f001a50460000120036290302c0404995030a04807083c0c50036151540815201e4821038403035000c40801c085095071151f0304410f55411a0050b60f000c0c044640c0150845c2c81d00040c1d02d441203007220000d00300f1350b07101403040300c2c3c42e0880c003854549440000c1c00407130707e120203016200600c01d00366070060051402e40100041454a00c05686084403108403907001d4010216045920400903100540d4505a0306040c0042e180907a201c803001c00342a60000c106141c1d80c600414600109980510643c900b80c092a0030300444e5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 922109946 1250 922108696 922108721
    0x3020f010e0904060f11211305120304061b110705120303130501090507080c1305090c120f0109260a050301090b0604050603071101060b03061302130f0f18 68
    0xb0400050300188194003c3c58594038001808100c0c5005803c0000729a04540480c1c40c9000c119282c0e0001400010744a43c1d0000344600202c101d01c00c182c07146038441188107510660b884001000400344110f40d0841007041040c032442e00103607001c413040145038200b19025500030b4000c2d0f050000d12807511003000d103d0f03442d04401945c03460b211080400850111540111001d549400c1c510010030400c0c00548010840d03030300501801a085020070003108000c40b02400458640310900050100003d20410724040607240c14414444050030302c1c4c581001c11521003400d40c00c2c42900c07010407803400509040581c0d41248007118440c4460907051714060300b1800d4000400600040020340855040302e002610080c003001c0c9469100c2c00030400c03d40c01160030750042281c0120340c400d0b480c0e09200391801048101600ba023141890800600540a004218500e40d0740209000c441007140c0d100d108010700345111011a07050762030101c0342c038036400351044150503965449281c00e01c40c418018110f40625 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 922111196 1250 922109946 922109959
    0x5070206190201063f0f0c090b01030c0e040c170703090201021c140706020d050703091416060e0a05030f0a14010908120705090a080705100e09010506160807080403020f010e 76
    0x20081c00c900241111000110140a01c0a01d05c0422041c12120034140e01480341508018100341844003950007100b00a410103141050449444d0380c4220b01000802045074080348001c041d4030308590000840021001c0b80d2030f214140990141c1690240d540035100ba020b032029801602c40040b0380000c0203120002190320607500003c0c0d0a22103000700340081c0315580040c1081407968045081b69000c40d100d00c003096480c2031080902034100128503101c1e41040050100e408070803000c1c82c0c017124521848086c8019035078260300c50f6031200042c00240030081c003101e843e4112030300001c0d510244400c05890192400c5c4842d031010006001d0a40d03010340000031170346000405245050b1703040c4000c005900f000750034000f044099481014001c01411401c004000c0e5034200420044908150050501032100c3c904100b051a1550070319a4110350007101d08648503200610700702c40540c1e483c1c80082000d10002031035810070080c2c0d0041c1c0140c034002d07102c84240012280054400c14400050b0035803028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 922112446 1250 922111196 922111259
    0x90605101103070b011d01080a17160611030a0e03070b04150b210f0102091e0102030702130e1009020607020d05120408030c100b01050f0306010507020619020106 71
    0x340155080c0341c1c08580c04080364a0a800703500c0c3c05103000802e07008000456160b0140d06841c140380d14916001d07084141c041e000d500c45c0c0c0d64406a41401a82e84080018000304415800700794190414404541240062003d044903201843c05680116a02c003003c901c0c10f501e0080c60903000040ea501564842c50801e1240c9654a80d001e000c82d801040020b82621018001d040392103503400c4e001c00860a5424242001651130410f09000025483e52220f03031050181d00003994030070ba6800101005c4500b0b041d0b2441103040102e0942c0f048060103904801c9080303403044001c81c1580281d13600ba480409840e450f1411580c0a0240c03811110040d60145090005401619141d910a50000e00c0741045034074001c0c10801e02c4440e600701c3d030710030f02d2190004108221202d100344540300348180d1005c0b0401055080d0000a0507074055088544403046d40400001e41c1640950201d44080c0d030000c08460315020204041000d030381400219000550802c0d400103000f041d82c2542c1400004181c0c03040640c072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 922113696 1250 922112446 922112479
    0x1509150e0f04060912030507140a020c01200303090303090f19140a020a091e0c0221090310020a020f070f05061602040c032004050901090f1d070f090605 67
    0x440016100b910301d03030344d6001ca0000240182c00013415108294502194915021002074481c07442c0204000071418200b01000041c1d501085500c041d642c00d081200164010300c115203681c480c3d1141c00341c003622001050003505000080510b01c503044c1042120710090301080c443d03441700a80442d003403401c0c4c140140680002c0705200c1200c80d1b00d0041c000c54a0794001c035000103c850495038060b04e4a59a00c208002c02a0031100c03c9800d0b034200100b0900a400701d00b032000b9910322a00c0c8006c40001240d009100b5105401b00465a040310700a08031201c400002031518006c0d88184c01c01005441440940c030440140800c4082c00c4480712903074404110720b00305c02e00469501801204510b005c070f01c1400e40041e40c462144480d84d956607600050445900b258481907401840075084030240c0074801000b07599500c80c11203040d00e60b0b0201c08a04040000c3c0c01d00090030b070036613911800c0c000350031001411070800601c040c11104010440d80280c0d645044601c00c485c068001c030780e0040079061040084 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 922114946 1250 922113696 922113721
    0xd0915020406021f02090a0e0703112809080a0b100e060d11190b07020306060a030b040618050609010c090b0a0905191d19020f090108090705041509150e 67
    0x428002030000d8609086c100004003801216001041420fa12005001300d05505202c4c2c071f07426150100f107284c81c2c035005d05075900d005440c89015820700355021200700c80603417140a42000400d5a141164400c0c1520310b050003010004032601c49100d1010900060340609800c8054010400036044d102e190f0305035118444490100782d18142c200181b0000b207400c150100041100414000c20708a445184600c101030034050003400181c03113401c40d072100741702003034038a415290895130140c00060b041250a8460340213491502c03003e4031502500f01001a85101900b1210600c88140d4440010395120701d698140c0b409042e510350001820070301e06018500f482c04144064402c00310300d942d41c041e61021100303041707002d450130300480c48407001c04d209088880d0b000c1d41c2941601404c0942c140007518500078014011032042c94100481040420300f407210a21040c4090000500b0900c00500d061884894140d1244145800742d481c1035014654003443c0905c60098980e501c02e0f0301c03c02e80703480c0e452100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 922116196 1250 922114946 922114993
    0xe0d02090705040b0406091703040807120c051e040b0405011d091002071b0902090f0618040e070303090b071214160b01030b07090b0327030d091502040602 68
    0xa01400b00f00c04115000d0303940243c4000c1c481c5a4900d54400d007440b549219542080610a0155100b4803051016840100d0b59806680003405005444003e500300044100710550140da04100103280c02c00302d100c0d44d5002207081410a0f42d0900045542c1c00520013142c400348a020b4414000014060000d410f041025030007481200441d4410340a0030305a1040360700c03014040714848100d20800f0141c220802a186c014020308500b10f00b0a10300102040c0d0034004c202020348103060000d1000c1d10000001d02150b0003540c050030070840032070300c1c192299a49050780010350214680180008403c03207540100d508156200c000d0300030451101c2016100380400c0b80110152041c144103081c440c8c62495214035849009411454042d455828100390000003d00b01000f00242c0100c140301e40001803044940200c4e01102109151180b0340f01c0b00801000c0881182c2d00740000160341c80c540e070f910b13003110342003d00615241c2603401c20500d81c003040b84981d1040b0000358101b652421844801080d1014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 922117446 1250 922116196 922116211
    0x51e06060a0504080d08061906020c15070b0114030c030c1f020a05120315330f0d02093c010c02030307030305091e03090d06090f0f120e0d0209 63
    0x82c10300340c642c4c10309424924020300050000d4101c20404c503080c9404204c541500345904e2402251034180000291505071a4007403a005620044200000356010012500c00341d4011000a0303e80d40c44a242c2c1500e03c904070a014804c3c07090114200c1e4a260204100c101100003c1c0340c801220000a10449541c03030329030070340055000b000711001c003044091083c4001c1c400e2a50800e6075905c1d0000b111090804651410f6000e080c2c00858004c8200245842c0140f00e8441500300800340c00105070180e232413040b102c58402850012501200c0e41e41c0c541c0150844184c216444440010050341c140340303d03004001c862682242807000c071141450111048900b103441032414140c02c0ca4680c0200b4950390008400f02d00103a17440040180d000c1d424408450f4101900302460303114a01094079a941e400b42841c124816800b02172a081001646d0b44107140040c0d204116480540300ba0034100b090446000042c1d40d612841c1d50184245440303144860b80c440e800038404000e41c121502484501680206440d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 922118696 1250 922117446 922117457
    0x10318170c0703080c1501120311030405030a05010f0e010903081b2b0b010810090e071706100f030c030f03030b040204230306010311090c04050d0b0a051e06060a 71
    0x1120a114002c081d5000d42409030f03541103141d01c03181c40c2001a50b01d80807030038049030041c00042410390140c821f1581500c0d208010418810710700d4118891940b010b0b50500c5024410001c021045d0801a65000c5c100810010f6000c1041440d09a070303681c2e10003d001035000c80001d10090001c001c08905c2e20b049501c5981005c402ea184031800b50198480700c0d5480750719152040c0d5084090003004c641a000b880d1654250800000003210740c00180100101c0c584c51744a031108000041103aa002050b464243c5801c08001180464803140140d90b074a00c540a0241d0214a04840c8064401101c2c0e20000400381145540c40700c00b441604e200c0207c04040e00c1c1e206e2100941d40b1030000c0d20203001001055121a90301c0307074660070a003402e42040e03070081d000030f0700401c007241e81003200d5100c40c03809076011152030790f90703008100c410b12454108039407081e800e101000c240145480c61a00c2011020010032144d2580c0340c501300081c8046191100c0038041900242c00c0f0309009010300b081d0780c400e0401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 922119946 1250 922118696 922118707
    0x10020703080d0f0e0c012c0a0306061d0603031902150c130801090f020108070507050102130603050108011b21020309100c05040f14010c05060f1501031817 68
    0x560758603901100300c0851050700c1e1299455064654071800702446100c90041003004580000600b80400b864840c0c1d00b0004400144041040c9002008440c444001d242030a1140c032031818000410990140402d00b20350090a8094507000242403030260700300400440c2001406100c10840e104d81041150440c080c076203800841070348092000d401030420440c401d407580070006c81c0c0700d014015503029030f68981c14114071102103841c140350044817030380a1a20007129034401109440c81c1c4610070000b010741d840002c030080d9a410710a80741c400c0c3e401c0c0e550709102c3e43e640d50304098242c7e00c2d007208100401c85d2201c408108540104415410003801850388140486292000ea04a0300b0071a5802281e40080d24000c081c100700f8441c003078485400b41440341c01c180c1000b0030101c0007980b5014826080720128040d642d5603018804a44419074010102d03034191904c51002c0d5081c14050794459440141880c0c0d280d41580039004407084102d0440b07480c056a80c0c1a258001c2c00024000d0400c4059410843c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 922121196 1250 922119946 922119953
    0x90114100519030c0f0903030c060506011709010c2607030b0415090603061508070330031b2303040204060305060907031703010e0606030a29040e0303010602060610020703 75
    0x3050002000c0b5601d0024540150b08000703851100c03102280d0042103403020050002030340281888413007540041000a030740c0d032408010303a012680d01803180554a2040c04101c000c8005400c00004d00746144c0e280035130603010b4040c0d10810780b000641d4440c081c004800081e20b407442688800c2c5403080040001c1905654041c0c50700d02d07100d103900280d01c0c40c0d480708414000d121040c0100450583e003081c40208403442d06603c10340301c81140c04001c0401160b400c01401d0046120f001e000c850200c180361a40300b105082000e0020000e0421440c0301891005451801c2c0f809440c01c0d140d0042001d18201c4550358204c117000c003030380c401007040ba0f00c569242c60100120b0002c0148512035051480209145421400c1c41615400c0c1e0340741040e4807041c2040103102900c01c007003500380c201805440054894442c1d0701d02c04041c21024031042d240352400c807a07075a220b0186241140e20a030060390100800082070031607a481c0c1c0300034041c07030016074858008540241000c0d000180d000b5420310540c0e49403078483d80c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 922122302 1106 922121196 922121227
    0xa03080403020a1506050405060315131a07030c12020f09130b0405190c02010912050703020304090f0504020f010c0506010b030a090204021210050901141005 69
    0x808101058001c0118000c60307a4016420140540b40d0a251301c010161841182c0c4501d0818001c5141400c01080b880540803015001611542e10000c00307000701b8139641e20807194180700030040960303a2010121b0038024086940c02141252140034002c00c0301256410050b0103a2040080e400e5640c0c07844211076840400b540d540c200100b00ba10703040003c003914841543c0140c10701d420031142c1040c81e950001042412041008003010860f0100e00700d0f1400100209101004081c6040d403602aa0243c881d080c421f204403813400b07442d07801410a0350000e429000c00b4948038002e1004602d01101101098902841c0c90b40003240140c48041d41c030401072060030140c1c02c0000c04035400d0a480c1e002181c001d600600150b44d03445075241c20084101c0101d4003c079054035800c002003540d251900d01c280c1280c0700380c4581c001e44c094138030410000f5008440b05d036051190800582041030f050700c = true := by decide +kernel

theorem cover : BRFrame.Cov 921942446 922122302 := by
  have h0 := BRFrame.cov_init 921942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 921942446 ≤ n) (h2 : n < 922122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
