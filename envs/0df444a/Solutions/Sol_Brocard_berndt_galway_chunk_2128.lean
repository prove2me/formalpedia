-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2128
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:53.364837+00:00
-- url     : https://prove2.me/submissions/81edc1a0-d042-4a2b-80cc-32297f2b58c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 382553956 ≤ n < 382733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 382555206 1250 382553956 382554017
    0xc09180e030c0109120909022a01090c06030209010e04060b040b03180604030e0907020d09052b030c02100905060909090f16060e04090515091011070605060f01 70
    0xa15164910b2016400c4503100081940d07000d0008850a48082d48003403400021f0204130819820900075403040310b400142600b03440c8807000c8034081810380f94800c1d0001d0311034942001101c43c19076900e84c0080c0107035100c2410140010700382d60581e032242c03405206000c2601c1030129000d003070500b0902e22600315803016000101d122080420302d8000141044031a00c150b2107503031500e01d540c082100380054680050402c00964120300000050694070032100c40490b80229003040c10f121203120948101c1040307002d42e008054110202c00181500000702154040c42070f0385840c00c072207070550201d0300c0d5400d80c060141d2100003040b07030a04a1804030581900480b0600680c0c48941031442d545140100a2a0216900344000010012140c000305110020348007900d0512643c00d00c0c0c3c1c0c0700d0b0f4071541c994052904002c20344e808101c84140c104814aa00400c0e200c04100c0c2c1c541c01c110b100070307c0c0c0120008803a0300b03090500150403420107030210480c2c00c80c1070312010501895800c8000c0080b035004d0110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 382556456 1250 382555206 382555213
    0x1020a150903090932070804020112060b030a1a0d0804031b12060b090a060e1303090506030403020705030d14070b0612010c1e05040510030b04110c0f010c09180e 71
    0x11460060610912074040028025000c032a442c0c1ea415038804441e8038858042c0110f880204001031f41c010402d05d5106038246046140760900340300d9100100160b03004010a5500403042203003040281e0b01c078940b05000d03041d0020446882804000300e20072210802024688244401c10019940a801c1031001e2100844080c030a612011003030303120700d080c04041e9001d94581401101078203084c2c60315134208000800911407203080482c4c1500c03081000d0146c1d55031108400c0e805092503c1001b41d00080d10b00203003015034034100360400039501c80413806603a10901911201c00c41c080d02a030b00c0d0806140d010340340d060400e102c2d600c0c0c28442010003401941c0041291400b01c207440020704c0340416071010342d16515a4011030116203610074185004c00010b0020400050100c1d81d50084000d24a0384189000700d18010310802044c064075451001540d00100841c060001c0880814544003144119008020b041030340b0f01c1c02c0312080072a00c564402100e0f0450041c07442090b07508165040c00425040f03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 382557706 1250 382556456 382556459
    0x8090106050d080d0501170a150b0405012d060801030f03030b040203180606060c0c0d0c03021504080c010306140402070314070804031a07081521061501020a15090309 73
    0x2c6039080203200ea085407a4200094001c0c01c6040c5846058054a0401040b07140800c42808455480c80400005020500c40d410480158003840d0049100050007600c00d100a594500034001000825520411030701d80c2c08492000d203291001d14401114032a42d034159043e465600c48252a0341e409600b60109900e403072950340640c5031400198010340350700004482ca402800011420300710080c0c1460722803039003082292544100001e240f01c0e001c00482c2e2040d407546891906841580060380029000317000066041520300509000d002141d00ca0800d40302d1007500305c00110111450ba008007003120b24603408c4280139051035405015114400d0418190700b0140350701d0f80c1441c2d0806541110354181c0000d00b07008029512081012030211444880b041c0d060880f0040c00341e00d401011420990040c0202248a540310344080c4070101ca1844000c1040c0159001503403900c0c42168a1014141c2100503c18154400503511640750341101300c81c01c001c9920b02508010302140071080d030420210220 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 382558956 1250 382557706 382557709
    0xd0222050108250f17101a09150d151d0a02150429250204050702030903060103060f0204050a081c0c0f030827250303020d0809010605 59
    0x609400303049a800182205050f61066140f0401c207082100210041120200080c21a20121100740c0c0c80c4600c09000c240e0b42c40c0003aa180c001c0c401208100c041c01e2000c9481d000500c052a4820400c060307400c1ca0307142da92a00c020b03003000100300310700f0380004108030700c0404203600d034003e444580500100400c541c990400e00845e61441c100340c80c0c095070043c0d00f04c0d2045103003000c034015003100801e54407030900e40f07032030813000441c00303098007110003401036064800c50001210200c51014005606240300303014003da0040c900050200120b00030f03803514000c07400c3d140c00002550441c2000a0040c101350b800c507581d41010701841e003c04485035130240800700d0a96610388010b000f03400620001c10361010b110080107030610a01c600c60b8188107680d0403075001b14580303008107180c42d0342504080807292500c00101000f160703804102202c00c81c03d5440d000050070042640329000c68603185086500301c8641101007000b10a01c001400359014421401c543d501440c042a07011442e5000000c80568950 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 382560206 1250 382558956 382558961
    0x40506040204050a0f26071e090507030207151118030f030715062301030b010c06050907030b1602190f1b0e090c0102070b090d1a0402130203060d0222 66
    0x82017182e8180c402c4105004540034144500600104040c600d040001009429611220340340644600340100d21058084840030031800c100600d91558100001e00d00140002c009401420303046030350404038828000783c0102c0313008000208008080c090300e000c2e00103030380040c0310b04001e142c81d03051b00030001c406088040500c05081054007412035440d40566401c800c900311001c1c0c0c0c01460362040013511700003c45103002104410f001c000e00340040e9040083c001a81d80f110317050b0b0020f00241c245002c0288000c004900381c4100d0303109404058a945403800034060b03c0d0980319040005034803081c1e0000d410b41413903540500c000d0281d80001c07501d0440340c50390182d07106e440580c074042c2e481d00e080070051070914050450b8415907032001b411464915500003510740600703118000b454007001c116180c01e603542030b08040c401380d806000000f0084220381074901c0702404907816841284440140e81c02040c0e1802101c1c407801004001ca0401d42060303080003000210311020010800341c082c0c50701c08122191 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 382561456 1250 382560206 382560209
    0x20406021c0219030302030405160308040f060905060d0c050d0504060b010f080708040308060406080a050a02090705031b0d090f03020601080705010903030e090705071703070e100e040506040204050a 87
    0x25400340c000581d004a4080080a004904004542c02681c0480c00c0f80d80c2c00003541c40150b0725141c09680d9840320304080e07282104401d040824080000ca0010030404d803c0d0041084424024254941039941d400507640f4100910540c1e40001d803c00040380317000c2c0254840001c075a100d04003242862400303071090048400850f000c40707105681d81080100e40d0303080030314202c000e03c061401515034a0420780080007500003400040510120501003103450351580c00580191283c202210f0050400b4140545d90f4941080182d00501165011400003407158084922504c002801d003e640d200401c40307001254001c58840200b559680d01c588002003240c140b00740b00b41e009034020801541000002d605140c100d40c015414010b10041c00c00000c1d1700716003601101ca908841824070780e030320781c2001c1d111480340d0ba070014122500103080761864503c80000e94007450480c0d8491002480034001c0c850400c0c01c2c002150042855003a6154080c545600540e80c4803502070005030410361303948040341d0080d0a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 382562706 1250 382561456 382561469
    0x813060306180902010507030806041b08100b19111513020901141c02060f0a3b0d111201020717030106080c031e010b0304061b0f030b03100204 63
    0x381d840800c21000801c540420000318a00c0c100440c804640c0068914840c01100500380198580010407641d101d0b0300800080e000b184240036003140d030f92002040042c084890300c1040c0c40305500460084451010707164198141408408041131340c0f2400d8482003030510034040188140b0500701c4600c024010b40501411015042032140145071040044806058100501200020360100015a100024011895002d0600004484942c0007241c130601c510940d01003480380010b0b0b0030000f41d0703101c1080d41940c0440311007070707522002640001100c0007480188540030b01c15613052881c1860400702c00303170045202d00f61400c0c003680804081054208110943b0380181d40c0810b100040c4940741140250f20801c21641c14074660500001603d5031001809843c2c2d00d801c04400950410440032164070316900d0074804220960351941c2e181003070b900450b0100c1d107031414040040000300c56110860b000100075259a0110800800210020a40a044242d161180140260030907c0e9072001b072019085 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 382563956 1250 382562706 382562711
    0x3061d0f090f16170d05031801020c010911090702030f181f020303010f0905010806010303030e190c030c06021c080a0204090e0a03030e03040b0d0c05070b0f0601140f070f08130603 79
    0x81c001c00005a01c14550301343c055034120101c0031500ba076000044a51041d000a042c00c1c3c400414000503009004680d5403034200d6280000705828401e480c13a00c40040d2800320740c4d1903030660306d05104988030700580160a1041100b8000c2c80340e450710402916079000c82c050528013006585400135000107a1000d42140582c20000051186071040d09050010300542e100a02140d490840f840e070b0360300014030003d0304042d50b83c0b0542c0720140c0d0a11501a25000d44001c00c007180c40e00741485a006442d0707110403282c4c4200000c0c00a000e42c0082848510300320007030301c5074102c140329050654420200429080585500b0070010400400300d11502046040c0c0300020911070400c2c1c58003400b1510450710f90b00d0f06901c2804100008010f00d800c68446c03c0c19004003044800c02c44034165058021440d0081018440b00308011a0b003204071101480b03444240c0c0c82c142c59507201810288580f2a46100303800c1c00c00c0401c655000300310780c07a0072401c040c0d104060752490071580f252201c0c1d024009400450020340c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 382565206 1250 382563956 382563959
    0x3060f0d1e0b090a230106030f120906030b060a0f0912051507170c0a0c0c0b0901080a0c0903080723030d0b06090d150905030406050a03061d0f090f16 66
    0x2d9400b0b140e40c042c3c1c403407004020816003502d910005c050f0105401c00300b1100500052410102900f05d2401158044099610b0180b18a0483c010300780021003500001c8403200c002800c0351203405040b40b4200090b04107454034144400403184041800c06440611507680ca00040940508040014090003031001d044c081030100386002400c84064125000c0088003644028040c04401419411580303508049664001d082415584140001800380c000081584005401e0380701900030580302000b603036440342603916100c0e024211192000c112000a140d40801c1c40012104001072014900420140014014464050381c01c4950005050b800d07070000301d10000f08149601500790705550440f42d640c280b1000c240803969490f0418000740200048d08416000802c1d01d038000b0f0480740e0004140c0e03540c1d94407107201038031582c400002c1200013403900b8400039078110b002c1130000c9a0110140c041082d45c8800c036145059420240c01c180450280011415606c0d030208214070403008613514204029 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 382566456 1250 382565206 382565213
    0xe160501030509150f0a1503082109030405010c080903010c09080d020d020c0f130606030518011a010c03110a05060103060f05072708061008011b020303060f0d1e 71
    0x582c4064112203841d48040070b00c0e580d101d69140d50715446201820140000c1d0341c2c4141d00c00c0508500c500210540b0724a92001c000d000c01d02c80189100301010415220300c00c1102c0c10728007100e20495400440b03070000d0109211542c41581d42886080c0121076803400c10382141e00084c01c6594a08030f032404905040f1007003002150a0115104030889800075080320741d51040c020351101c5106e0440b611440d11207501c803c0981c1c45000522105081d00001c22105483d05009001010140c61a01c8040405442140b000c0b905021724610b509294140c41d2000403580c0055800410052003241842034405203d884080204001c00301c0b903004074010700881d413560802104403159001981e4138142440100324035603070000c41d000102d4a6000b04000261039020007000703500804e0300605a10b000b91010b01044814030814902524a800020040050100801c00142e00c0440b503c0c0c016030410300c00a6090310305100d400544200241981c0c000ca02c19030785021002c00450740c0724a200d524201e0740c2050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 382567706 1250 382566456 382566461
    0x9011403013c1e0312020c03010f060b0904050402010e030a08041401050a021b190e1b25050102190201021b070f03140f01020307021b04140103150e16050103 69
    0xc440801c0071003031402400000e410040791aa0003040d400040b68103c9107000c40900119400070340c1c108801307070341c031008446000351a100050225403081d802e000d1035291320b144074030502003114040e000341c519188820341408080c0900400a90500c100c0e01c0c141105c1c2c1c0c50507c40003602c0b0f442120318036a140d08084801b50400b07c40b4000a041000503ca07140c46103400042c60a41614405e491900c0554000001010050210304611503c2c00d42d942c0000d461880d420b50601554802012a20040e94061401c1c1d4a010315000c0380301203c6442d04d807200040b029030381415214060030015160075a42d004681c0303c5d4440b640200e005030b60014811100c5e0401d002843c11502e442c0b0094402c1914151507042400700a00018003401826420f862880404004001c55015250029900da1503d52006926802e04921000c416294541d0175106840c2900c01da00e00314402c042403400070b90840c2c443c1800c0b9080f280340114a1a42ca2880c03809800040040c80c0760072307850040041e00c0e10b00b020001010f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 382568956 1250 382567706 382567769
    0x250203071a010b252f040e06010533071406040203060c0a03020403060c02060f0708060904110102010f0617010f05130816170703090e0402150901140301 67
    0x207200324090050040502c03c2c1d04440446004500d56240250303c0413080c000740c0d0350004e0082c030480d04044802105544810071041200c00542400c5c41851408103010a03207020381640d000030340280c0010700c80781c6404044030701c002c4601281481c844078036504910401440b10f102008044000ca650030801503240d45218007900070300f0203000795090550200e66a40d502074030044a56602085c113039800b501c20307030580e4000c40d003224050120110400001c0d48549040c1e40d9803148119060020720042c1c081d03034601e4000c00c405000322007581d40d50303110f03031311000b4200f06564115522940c00d104072051600528010340701c05155008400c420809050854615241b1282c440d41048100151a0101d0b45d616460300c2c0c0000c0100d60307070360b00003172120a420000700000346500c1a088003014207101d00c8003d0109070f8030903121a5132645e00c4401c0c1d0031300d200088030700a501c034482010320b80051303901101419904606040040e03d0008020754020540c00036000240070181c0c05008c100b0a014135484d81a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 382570206 1250 382568956 382568993
    0x1205091002160b0912070e040501052508190f0b04061505180301020405090903030a0b0d12032408150c040b040e040201050415021b010f020304060825020307 69
    0x70711080d4610700505802d045100783c40c81504041414402620340c4004075460902c01401e031001142c44802d20b005d0032030b05803000d5409620740b17000504111003254000c503022900603031404002d49024000c0380c08610092811687c03d84142c0104030000c2140180030401710b50101c080f41c0400e10303109001c1103c132981d02014000750604400e00149403c035003214680758034084080002280c02e0082400380c40785070301203a00f04202604200da446400b00185014040580e0140000307010441009080e000b1010050700f0301e072000c1116140c3d68080d41c0b0030411080002a10f1003660303181000f0245041003907102c149141c00c01c04404202c0c40c0f034803460340d2380b00c210100c265050600f044510300c054000d41c00740c042c40e03200080c085025a8020802d8030000c0920801c15158a4403108000b03440c0c5082228040340d2200d25118060198041c402100030702603182d00840c00c0c03038501141200d04801c080e1000300c85008071102c0a40c3e03500018003925001055070011582c910712440d0410078483e2116521 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 382571456 1250 382570206 382570213
    0x61517100c1d040213080607030e01020405060901080a0f05090c0406080114130c0e04060204170c010e0d0c0305030f19022d03090d23010902060301030201080907031205091002 77
    0x29845400c1421003085070403030b5541440e100c0c11540882c000348100304408503c00b80c4000c001130791080000784640306a86035a021b200d017015030320321a800d0780680e0180e95400340d8103004121055104400840d4030400d60440401c0401d1640f12020891b035081c1c400c8a0aa006024200c0c61401c090081000400c40c1d2002000a1400c48120598950015017038001041500010406008403401c040f0060084180b240340941000d1424070029032092150711a621650060074000d110085400540e40906860310b00c0e0451012041250900319524219140702302d00c00c1c08004104100090f24a41c0c06021006989809030712002880c3c810200703460045501180444242c28018010400007081c0c03041c540071965a02420103085020b0307040800d4001049110a0b01440140f182d4005264807000d000c4002d500701c010a0f1b0309a949010000c2d4000000700010030040d403003000c03807aa010a00e03200352507016450303550300b000c80d4076035501d403c000900101c1c0b412100e252000c80c10704045c0190004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 382572706 1250 382571456 382571471
    0x60506040b0d0506060904021f0f031a1e0d080d0203221113020d1b0813080301171f02070506130b180f010e030d050c03060d080706151710 61
    0x1e4550b122030041026006e480800003080c00c5407101810060b42002c681d003180e1092004072401070161700107483c4800001d00b000107625011140b01c1d400c1e19072140140c210346408800074001000c0c05904402c0c950000b140400b00004108041c2c00341030542030007440583c1d01d092884442021000724501103180b070803400b5140000841e401080c000500b4240d62034030b504e0380c1341c4000300f00034001c4d440450251800c0010f010007070690381300151403000080d10382984989895014030307001d605440000302604001c0006100c4400b00c101c0c0819050300d80350031900c3c20548101c4d581c012122000070701c1241a008039003030003042014440c5039031181000f504040300f4034484d1034411715180c02502086407031025150264070008140700031004a40c3c000000d0000e08541112a50340340e0206000c40300307892628000c00e58000c649401c49000e40030050001ca1500e2454442039205d505c1858100d581559400400c0650241182030b1401401e00200365514001515002ca0808200b040e0341d001c0d1500d170006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 382573956 1250 382572706 382572713
    0x1111812060a0c020705090106120f2009030319090305010c0c030e120a0c17010510030c030b100e040c080606010e01080114061c0507020f030a0c08071e060506040b0d 73
    0x40d0554090002403001c500752114183c16410a0559001070707400400e100000702e00107810842020705100160820081c2422000d400f100301c402540c08108029892a1590740c1500a00060800d003500101a81e14054014401d19030940e220305606000c110b40034810824844288100305d1003086a0401d51192840d80e5002820050001c841030f10941c41c0101c20800c04d07100304a0208019409100800260b449444030501000b0f01c1c0c0c038a140e19801c00c00000d5100d21005081800c0720791042c91440c0e50781c110380d512000c525000300030590f0784410140004110a50001c0a030040c1d008103c07282e5282d00304031030141410070040105040c010b08c3c2c81c00e00002d9901241a03030446096820080001c188103000401c40d100c0c403c110000e41c0320000b84440c0c440140d84c045c5006100507000c03200f000088401003501c038000d185c03829001c0740220705d040c1c020600344402001c010784100310248030310903200852000e5100329001030303990307030b40c1c61003001158103140c4200f401420040314002c0c00b02c9807958 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 382575206 1250 382573956 382573963
    0x70513060302091915180e0705061617031014011d120708031b0c0901060206040b060621010e070c0203030405060721020d020c0109030b070c08040801111812 69
    0x510b01140c2001d02504c0180002c040c0e484000165000703490070709520764444148449541085681144030301d03215101d001d12000090100031640080e100b075083c520305200c03210001101b40c03001d40e42080104c002894003c05c480085101d0140505c038901c00504121a40b001041081c2402c1e06100312101c203601540d2800c00613004c00002221034013185208140745034108002d0b0381c450315a40c800420380b88031826124411400078561603045030301d914440c10801c50200d20078071642000da0801c1c0c0100d004510004286540440c0c003801072403910040040d040c82c100715013050443d6060302c1000500645808140301c40c1c00421500d4902450442c0c1e0300042c1d00c034480c034800e9500c1240c00003956020003a031b80440000f5001104842550703508a4800651180c00c8030300440c0040c05000042d503420740c0910000c2c010380707800c91880307152943e80c0101902d000c84002000c1d16409130030701c00003a141100f4095908a01d03074120b10039494000020740e1103800350302280c10511562408618150405000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 382576456 1250 382575206 382575211
    0x130303020f060c0f190905030d0302030906060105032403160e0a110a0f050702030a02040617100213091d030c010606020c03120304030c0314030103030302090310090209060d05150907051306030209 86
    0xb95115805c007001240140d451600d250f101c240c240c050310042128298266014521800b00882610b4240c0e40d407000440d202e01c801c03548030ba42d46400121481050401a188080135100602100c904a41049500c0403102c49984030b0125900600100714545e150383c09403d0b0b000b8102c85034241800c0c07100c2c402911054902000070200040482c0c10000e541d010050345004540141c0208100364440104580201d4107140b0440640300d03a003e580039401080c401c94404e402405202d81c00360303081840c0d900180203010600181403605030301c1042c04030320500c018660404428000141c076882d1000c080c0c10b0001d0008107070310a40101c601102034500030012070b640249d1502e04600041c1041c40c06556500300102070181d110400b000100070183c050740100300c070b102c0440c215440c00c0e40a020080c103881c0e503800c000f904040f59001148890030100403400140344100151400c07510404090184480b040304c0055050b88984000c002d1410701852001107000c1d0b94100303010742d904607000b280300601701 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 382577706 1250 382576456 382576477
    0x140103080301060c03120203040c08120405060d0203070c060f0e0c0102060115030e030705070801061d090c010809010207050313060e0109150c06110c0a0b01120c0504020a05130303020f060c0f 84
    0xa0300404e9042602c2910070f4481c04910040454407800d160410807c0c015060241d44064840d00d003040c01c0000c5141c0540d011510010580c07880c0402c4090070001940010340a04180201e0500410018195005280d000890320100184140500c3c94141c9001d8003216100e065402c200010f02070b41640d00038000c11300510f41004a01726413446441031440c480c3e03480107000d900600d48042842101074206000f01c6038011078444080d4880c0034185900c0d074090710341e000150311680c020380d215406441712980c4030705e42c04001400c00c5490340315182141d1007800328001742103803800107200d0035402c02c071400701000c000e1a103490350300d0034084504075580c1700400b04800c0c80340024114040103110b801209180900c48006611040d40441655440481e98421162807030358a00100f10540940d0fa929030003038020b500803c80518020070f100007540300c0d090100070020100840c0680e82c000389001030007140300758010f200100c1d08404287c2000c0c0050402001e0220400440750040148410307950f00411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 382578956 1250 382577706 382577717
    0x7090b0702120a08040602010212010e060f0f030c0d0f020a080c0109090b0f04021c0606030c0210090c08060c0a0e01020a0221070e010f03020f030a0308041704030204060b0a0314010308030106 84
    0x81c00e80c0b4910380305108a0040c954480001c0104249506401030285880b0b8003800c10140e03600ca4140100896089078800d03003003040150304600c28a08140081076480b0090296850304003900041800034060740425190440c402544d42d085080c500040030090501d2005042001c01c980c0009200711001d225a030390051310341d901801c4564508500f0b81840704010021541d410202d44010302d2400301034000f525441c070780b03000000c0881c06030044030211025940a00140345144030800e000701080202517401c50010003000c903103440c08104043c00f400030520500d0f180c68a80700028031283c01106000c1c1150003501500c40180c448500700c21140c111039000659071030348a04001c0ca803460303036400f260f01d00c24428000984912110f0001094030300a80d0b82204c48002ca00a041c0d9802a485000300000c01000c0000c0c0850718505641620010345580103103400c0e0f0780d03000a4140d550725004030b44405070024a0340b10751034252281030a03101e80003109405940c0345803200442c5010500c140c2c000d100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 382580206 1250 382578956 382578979
    0x150411090a14040f0203160303140c0c060a0503040203100905030301060c02031c030c12020c0d1404030b040b0a0f0b130e03121003020907090f0b070804031e0b07090b0702 75
    0x12a550041101c5100d082d00c820707018503003410040b50410b03a800059010703001d4401415000074801401c0300c203030b1307030540c40d00403c40400c440c52404680c00079070b0010181c010b40d81e541155903100c40080c805807240742d4509450741840e004140c00c3c00c1e00f481c01d02d94290b150000c400f00082000c4143c1e0304540da10f00703019120f0031550004c00d08081b84000340c04641e4401615061074039400d50700c0040320382130641c2d0319107410822070707440000c84c0320380c1c02d1042c06a40040101034207640b080540e81004501443c10070b0400b0383e01e940300c1da0601416103040301c40325030b140e08110342000d03280f1881c03040d0071340700c1003d001440c040d1000c40d1000c400c3c0d030482260359448803e0795801c420104105e074000e400442c42c00c20b01e450314501050040c0158082244103501c01c1000c80c1c0a188155038010642e46688080b8180314a000300308600d0358800321044801c2c0501303100010114442d062406400c16450b040e541400942c1d203428010103c000f41803406104980c04248412604001918a1198162810a03080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 382581456 1250 382580206 382580221
    0xf12020f0c10200d110102090102031204030e2101200307030504061e1a010e0a1715090f0705040c0207120501060b070f030806010c03140d0609020c0d0215041109 71
    0xe00c905040707440c800c03c840d4040e4061980002d14000041c0c020fa45105e920801c4041c05800c2c4e21074844168010703407050140718003445081074050f400600c2814040283c400346002310341c941c000d80814001c02c2465040d01c242600d000e00440098601111780d2220340342c1540d0381c0e035603d404042c00000415a45100040400010341d20040401015007032440b01c02d1000302c00030010742880c200c2c00e10102c02d01c0410703000650052100c0c40c10307039000401b0078020900706004003c1e03c1e155590783c0304a41c812185191b00000600074814043c81022000c0e00d005180c0220b064580300855009a00680c039080d4580031003070b400700c1c112050750129521258030030b4580c1005400340c8520340000b1032110780010321600300041e640b580c403166480b03034881f40305650b1080c0040d01e54260503030000e40401c456615000c021068007006007802030314480005262521019503000304c0c1c01c9440400003960000ca20900100d4040100204100c840c10b8000c125141954861092412580d0725500541c810808686803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 382582706 1250 382581456 382581467
    0x406020c01200903070902071e060209060403060b011106070e010c03090b0a050901090b09090a0903050c07080f01060933030b100f050409052a09040f12020f0c10 71
    0x4905a441c50b4190000c1c0d10041000540e0124222602c42d10030b150000503c07110034002d848a00350482c130590303810b6001181404400c041c4a8044403000c0d42044200b00650b60311000d00f001e5409620001b0300d0071181800175000d4503611514444942c001410805031661080e24030a20000c20300c3c0000c800700b001d213000c0c1e4603007002d904240588000842d50b09001540030707018207007141c2c090342c4100085aa43d00d40d14075602c15800c2c030790b030407004640010b401e11029800c0701c0852407092802903e404e010b50f81c900d0500c0141d8000304916044403140c1000d1642c01d00031038000e03102640c3d00300800e42d003000d000c81318005103580700102d80346440400d04090740c6145248000355042885031501d03180580c1070f041d410070680100d031074100d595031010509003000d1040700b07400d0785d10400a01c9036001000c088141020b45004041140c143d0400d910b80035117407102c02a005620078071580a140d041072508041803020803010f14111340c401902241460700c0056400358101f801d55507109991040c2c8030840740c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 382583956 1250 382582706 382582721
    0xe0f07020a0f061d03070506060301060f061209020609090a06032009010e0a060305070605090109060f0503070c022706040b0414010909060b04110703020606041107170c011b020609150406020c01 85
    0x204d1740130215020051041c04a04d841c410101207008204194413600030b8401e82c0200c0c090318001135400a02103082900d40c1d80104005400240542e040030348805c00100b01610031154140b0311600c03802c00b082084881c4014030b0b0003801058844c1c6e050000c210100341d09040c144151050704501d43c010507460409a40444041d60300319050381e110540f2010054200e034024481d190025811000000c5d0f007510a42041850200715076450b80b40d516134003412221604243c200b43e81c012602138404200c45c1a4220411008491070411489803804108002c207c8203202040781c00740d82001d0010911148400342d4034150340c55004006602070160400f00d004261034012103800a1900081502902d9a04094002948282e00300c0301d56036102001e10041d41c40044040d0481d0100f440314900290100c00c0c1441c40c01e800c401c4841c180380325200c0c0780d825508000c42060b41c0061483c03191440c01d40c140a07644d484894000102190904240c2d103083c08800244050080c81c0d010070202c00740c000a410048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 382585206 1250 382583956 382584011
    0x31d0d03110909010e1f0f060509040605030d0309150e06241c02090a0b0f1302070f030e030717061504090c09050a0b031605040c0207030c0e0f07020a0f06 68
    0x40d21503860743d0303441d9414581940d404248070070b00c8030980200396022452105447c800b1084900d044c1c5402c3c8191800d80049405a522980b24600807620fa1020840c2000e4940181c0d408603d5141500700340405908030001c0c180d4013410442c0740c10035000c0c002002a040306400b000103841880e5650100712031118640801d40c056482e0101494030040070a40c0b08019008854101503919214424012140c40a14854000042c031a214113185861900fa035038604036680003500e04461a5200b00c60b86100361012000b090a541060810b4207041024502510042c8151801c40d01007126495903900300a0004103823901c102445040303910717541c1100600a91180300100e5254031070140350042c15044620014852a0940c20301c0c1500e800212010034044d80072910803a58100014880075058185451055114a00002000400c001c1c00000101201c0444400a0410782c0c4a5018070701e000c0c210108642c004c00103d0301080101000038030050340960b00140c10a050710850304424040b80700302 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 382586456 1250 382585206 382585219
    0xc06070e0d08030702011a040b03060105060a090305070f08070e0405030d02030606090931030e1201061a0705060601080f0609070908120301030212030f1b010f09030c03031d0d031109 80
    0x4c60f0294054200134404010084c0101d21445010144001c540360a60b105515610101c010426800c06100070302106e58545400b00c041500c031345500389085d6503640000c8880081c0074040104100c00d00901004d041c210580c2c80a5080a41310695070340568810031203038030381c0080414456039524007180c604407000b038003004542c5404001c0500c3c1101d40f0040f8915115554034207154200302484960fa41681a242c6600b0040c80760b0610001030006484208550b40c1e5540100c3c5003900b0199039444400c1d0340c00d416660303208511745a41090000b40c1898140501c0f20f0500080c110205640d03075004074181d4104170320b5940c0c1d070001c41c0da03402c480d40415814011408602107560310000218180c0707000342c81c8400d04864400311036a40e1300c01c2c0f42680310300343e40600000c800803002031a188140400e0100105025906e010007000703d0703040b038204401044403050f41004144d09406500000e80d1090000e0780c16041c0403c2e03e41d140c0ca585031041e400c140d91410940c0c08580004150750042001a240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 382587706 1250 382586456 382586461
    0x9070f0f0e090135030d05060f1906021209130b010e040501090e06101a07140d030c030c02070605040b0703120f0603050f060405030a0804022d10050c06070e0d0803 72
    0x43c15003081070560025440c1c24095401360b81c02640c40a0144120a60402945805003180243c0e0041c2009004180d01c9041c2c148400e425540321190b100052b00d01c1e0344800201c0b860008081e240c09808201e00c00c04034400d021104055856083d4086000c9454102041607202540100d500100c0380d0031040d40b03e03142ca000803c43c02c841c0d0748103070b076495021812282e072130319400d07204414001030344201d52005061040c0500d6030313031808000e80456481071888000603408038a0b1541480d0302800340310b0001e42d440341c000c95441d6142c0213100c04601c0a002400a0b241460002040780c807860050003d0103200160721800c0510501c2d00315070750100c0007070401955468882c098040e2185100958a07445007540d4000c10310000b02e1020300595210700150714042d84a002515040380040090340d022981c1103499080b100c4040520440400000000c2c3e034040c2c0b500304000f000e0b0500c80d1424100030040c403041d0380c01100099420740241003800c03c09540030030b207800162560445030000f400e40801105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 382588956 1250 382587706 382587719
    0xd0206060a0b0a0c1a07020f01110306010509131e061403060106030e0f120a0e1017100b0a030507030c0903020a0e06310c05030903030a050606250b010509070f0f0e0901 74
    0x10090b000d00001e0742500c0110078000b008c68282d81c4d141000f0a4554800c2012071130540c002c03001004201405881164601c0b402541e0b0021034032007a5180d4210340c24a0005030040c031461040c04040d02c4820703000e0109080b008003007a543c4005000e10028076603220383c02030341c1500810101107060a5801100c2030108400700c0480241c00408c61400801d908c070194001510308060580c1c8841041c3c3e41341d07490405e8082e0880b100100160003100b02c0940b03d4008910104140c000b01488661500e003c09d2505200c3c00050885580e541641c040003501c8009000507138400362088210b800d80b500c0780c120b9450341d000041140010590000340d030160a0303641c0a042d002c481d4007603502802d11a00f048442000070f4140c455200031202111140c004000080d00a55507074170464010202609050406904812000800e0607400c0801031070362119060204002280301070070701525094400482d1418030b0070700540a0107518a608051207055412049018030030075a43c84179000c0103050354850f5a5030b80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 382590206 1250 382588956 382589003
    0x1b011506090e010f150521010e15040b010c08090f0603090a050106050103091208130b0a022a0c091b192705040b041407050307020d0206060a0b0a0c 65
    0x100d10380e6002c02040002030040c207240303241c10403640150000c54481000583c212050b038401c12000346031151500c40598000108001075010307080c00d540c229641c0c14141d002007505c4d0088080288940e0901c40050104d99000c0161200d2039400002c254503080c0c07110000d5803442c1075003502c0d6000f22003c0700b0007165010004000100b01e0054000304a032680312401141a05d016020103040351703150440c59500c1c148112100ca6214002d044508031300c401e607594440503c0380640b08449a1a000305210400108144042e90202400560141c00030010031002d6140c811030b103151807082c0b008034005049031164a80d4603c082060419203651394240000c3d11210348640c1c80d01d40c0020300c00013601c034000da40608401d00c0c0403024110240c1d60724a094100000351503100841031b0442e89412410502c00044680e917400f42e103003a02d88039100e00d885d0500900e0042401840b20071940150184036058980002000c25507040041a82e0303110318510050303819040c0c0c5071004203200303e1481c04c0c040610603113 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 382591456 1250 382590206 382590209
    0x1a04080d170906061c140109061b0c020a140307090c030903030b0108040c03080c011107060c0e09010b18040b1201060f0501030234020307080a06050c0f1b01150609 72
    0x5041650242c1c41e0b003501d4581d12401100d07070b01d070802c0c07550030182c0c050080d01c06400511441035024001d401d07402030720745003074a490007021181d468803400c1400300860080c000e190000c1e03107494000b52074186134002480d110034600c50f80000c0081d80d41c0c01c00003520b045c0001c0028250300001401a203400c410000d00030002d2400980029107841e080140c01c2d803082062501840d08444128012800c58070780d0b016907408162400b8082d9030300c4240100004c030300e034003030505140220070005078403060480141800c85070741900d6101d0b403117500040c80805070381d20070f440d00c0c403501c10a1281c0c4280074002150080c244503510a038880c0600a062409090542002042d10616444503c0107940c680054003640684010003140044113001241c0840310704140400b20618038024003e005026000b00b410016150004e8000740c111a40d40b005000300b81c043d079504042d04140f80361a1042e072541203c55400358808860701036014a102d440c03807072404d410001c0004010340d1020300380c0b6600c0310040d104c07655a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 382592706 1250 382591456 382591487
    0x3070f020a060c08030f071e09080c04020319020a0306090e031e03100501180f06080702010b01020c060a0305060d0b0a0b0f09011a0703120501060e12010c091a04080d 73
    0x5010700811114070450b10600001d034030410007070460719030101d6400c3c481c2004041c80100b24410450341c3c249a007038a400400407407107484c1c51980c103040c04403072030402c00bc00740440e024600400600c2014070f44402540005c00440d4001611007460100440140a5a034001d10b80c2e81d007880ca2804c6060750101c02420031061400307800796040c050030000015400700b119400340008140f6801c00a80d4003508440e0034040c401e90000c55059101c04051003101d040c3e401c04400a150b5070104920140c0910464903c820240000c2c0400d0000a00150144c42080e1210041640710000720302a9298000404802a070100a00c666458030003099001040c0c55594607210b07280c140715801050800c80d41031030586040070325101e0301c0c84030f5211140c080d50100d481201003026084c0c07164072800740c0d88130710b80c0a80300c95a00c00d40c034020417508000400005403c20b850076403401c07804d0b40220ba04030342c20301c0855001203840403461602482c1d050703071800b8030751001c5203d02515020740c0c00070380d00c41000a844e145 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 382593956 1250 382592706 382592719
    0x30d02011a06070515090102070c06090305060c0d0906091b1406070b06180a052d07030513020a0305070609120f0f2909010e0c01080c090a030503070f02 67
    0x10001412400e866107a4102007850005100003012810031500038107059002c0c0742107401d680c451348080c0100042c1200c0c60042d595002c510034007040004030849008260901d411b103007032070540e00d4051b11501e0240010f00c40260008143c156100560440420341d40c109608000c0694141007031207050400c1001020060025031005c14503da1a40c10a0440400580014200720b030640c0c0344c65482101405103940302c8a004207582e442404820300600c211701d100c070b001c00c090403c2419a2500c150144e1031008191250b540c20100c09008001c00c0d500c401c10745008581c030f0f101c0c00e080410804c10214044c0d00300c1d1030054044217001001a065084400b560f0716009000d0747c8200c2c2150038040703510001e00d18110425076001003000018003048580c00b615490060340ca5000300c2029010b8a10b00c14809030b99010b04000304054203204a82c110001c3c0400f500b01c0f05010f00000380301000c001c0045081c0140400c90181c907458801001d4003540c1d0140c2201e90b120003c2c00c040c3c484401c074140481c82083c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 382595206 1250 382593956 382593973
    0x306211006030b1f0e090703150f0501060503040317060a05030a0303150801200711040603061a03030930010203091b1c02061b101d01050c0301030209100509100503 72
    0x29013040480405002050001c4045007044040d110606000d41725010500c0f078120302002145d4000e9890100c8030641000090341581540c006003902d1059204d0410710005004000210343c004107142d8a071004121103422594a86000984a41450b0403c2d0b03003500c81c104420007016003640c0b01381081a40144406045c9940d030140342e099070b40303a00c0702d208490f02c00344601c45000848009041241d10800c0498000d20152002c501206c03d264015903d00c2c0d2281d2038401c2c801c5410640036003c54081c1e001d18034194881020034104804081d410340003404030f4484900e074009461a101d00201c0c2c0e18002c1d0340d60304100070fa040d610040c20319008443d400c1c07814015091700c0c0180c0c0e14000301a49203581030840406408120150700701d410341c0c182d181034942c420101c1c100180024022111410170000b4182d00941000302e204031385094251440c1e1400c01071140c2d000302a81a41e0440c2e03412641030320309558141d88102c280c0000d910803604000100180090016002c800a06680c410b400b21421039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 382596456 1250 382595206 382595221
    0x130b01080c03070b0a090306020d02190c390f030302100e12300a11071104020f1306051e03070806100306050904140609120306211006030b 61
    0x8120704180558140c0c4070709000c02c011200d240152007071142c1030901c0c0a071903507039031665801d9074840401040080e030b00061450048074100000ad005041c1c929002080c2c8140da920400591107500158158070030001a14112390b80109050f5200030510303001750002d95440d800040c5d000c141d07000480141c0610b980e4120691100c4c0b20341d0080400d650300428041000340592015540400c1d1941c141000c125950940c001c0d4254083c050b402d00f10352039080a2904d110400100c6408003040e0482c0c850400421012400130345104003a03140c11100183c0d91851640030400602c0b81c80c00181c445800904001001500040174213581021070044540020f0841caa440191004544180100c1c001102003220b50800d440721055101690500148580d110750005078000c400300c1e012515903d184003040e0030b42c90144002c5402903c500e00501150309101c00030070007070000405160040004d4150311a000c0081c50f4040007644624041e00c0c20107581b004507102408180c00700381e95540300c0d030000c81c0380c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 382597706 1250 382596456 382596463
    0x40302010e010f080105220504150b060903070b22030308070315061d15040e0114030604020108040303050c090a3201050901030f1b0513060503070801050f010c0803130b0108 76
    0x309445540c030100141e003400d040014010014107407e076104011103008040000910540b40268040e45034900364600c00d80c80d41060701c158280950040409100d483c031b01e52400111107040e01d1001c0400742d00c45201c41c44184c21605107000b407104a42e40d0400c0041410b8124402c03a0040035240e4060104500a0f580740300070f41c10a105100005951050468496000405203110b90384000c00c0140c0d039004054201c8450303005074110284801541004010708104035088020150060b00a8501032070150006031842c44000d101405050719007000840c0c01242c0780840b19011b00c014581440e080c3c403220189420110040481d0391905202001d1251009030942511115070594540d490011a140118042e0915404411141e40c84601c070180b03015802c009102003142c241e0320540c0351004005008021441c5902c142c09000302001032051035030b8030400310b6066038010703101c1342e07501641c0e5801290203401880025180141c04014408020400e02c00d0070012070045811010340d0342c031604030985 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 382598956 1250 382597706 382597727
    0x19110603040c0302010f0c05030301090614190b0d090c0612050609090d1b0204091a011a0901500c1b0d0503031e09060618150402070602040302010e01 66
    0x42c02918401040158480c1d40c0414911109181c005001105562460301e160000e800081400c0c1d1905410300080e1b035040101c4a0411080301d481e410000d188980d04203000340b42c0030b1051414400071b803082020005405c17002000c0e40c000c0c20a41e01c59600c1c2c8008151812680c91094141d05180204902d480c01c00d148500401b00b503000381c05c009030b2000094540d52032280490b88c40c4503118000101507034403440f0b9034040c0c030b000e00710044103145500c4041050b22016000205a0310181d940d80840f04036410a65164020a003094032074540c6c0524031841c29080003c00400c8020b101e141c3da886581108070f41c40504400e05051a1100c02d0b000c60320505015088540d0420b0f8440c1c010030300e2580e06903240c08180b001c040e00c02d140c001d02c1916086d040d54400c03601c400150403e03c010746d044407402c07100e141c0d201614901401440c104540000c43c2c5144135074401001c81301d0880403d0202ca5000d1024400c42401801103540c2c600c9450030070069007042c403040c0d022620102201859500440a104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 382600206 1250 382598956 382598963
    0x150f070c11010e010e03030f0a02190f08030714190e0409150f0209030f060402270f180307052404020622030212100b01050f04180207051911060304 65
    0x224203800510045a0b0f0074003a4031064100410a021002e040e1024030090000002111409640300003c0901a2900005260500311032140c144254007060b4849078400d0503540c0583c03040d9807910756840856107015003020b03a0910a030b00060031645155228042000414140c039a4441103940c1020001120320012026014445464000b004511560303c40450107441640c01400c001c0342c0300c0400c0c030f1311000c08003d4240340c1c0140240310561601d0b0910901041a10088125141d2000c03801a5140005403149a0020900d004201034403d149401c03c501140207048a8950880d41015540d51140000c000b0324002041c148180350b08048034209d02c1580c000d80007500d4035490428400841c0100095106e50120642000c801039840c64001440c0020310030007440030a40e207410000c200e03450304400c079052150800142e98102c900d542541d0451700311900c0d6030340c4410500c821401030300c5003410061850290803c0943c003000f4008400c82e2040c01008100303840009402070000c288420389018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 382601456 1250 382600206 382600223
    0x709050c09040b031207030f0809060103031b02030a0b131b0509190f05010b0304051c020c010f0c08161505130b070c0f0b01051806060d0c020a05150f070c 68
    0x100c09400c02e50000c2010304405000c032180034010b5810a0003a4100340710480001d07080a0501e0380c61648880700a03004003900003d881203515558010f0402103500c81c03070718070409048821a0566809200d01000c041e0400701c42ca54600e00003080c0d0102e41583c032004c907101c0302542582140c1135080c003014800c2c0c40015114101e103403658034a41014aa102c1034074114903407100140c590092203405401d00804030403080380d48a0401d0b28240d030429009004290783e5500313480844014507400204203128003801c1c24060f542d0008090210740207840d440d8081d203101000108010088841c18240070602c7c0190a0139900342030141c000ca01392801039441a0300c0d82c601c103280002080c410a2400d810150070305002c0d200001564510118141c10b401c180c2d40018100300404c200d05043c40c2d00d243c0c81402c102e1210b540d00d08500080d00c04d01854001075001d940c0d481480e42c80c103000300b103600301440e0401b08560580601c0400501010800c2703c01c80c1800244201040200e03000300c1c090b0844c5544100e90 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 382602706 1250 382601456 382601467
    0x8120306030714030a06020a0f030c080907050f150708090120060106141204050705010305130f150b06120a0b010801050102030d0b13020c03040503120705060f04050a14060402030709050c 82
    0xa412441d40f00821442d81401824401400280284010081c4451903201c882c030380840820040c04545c0382041c0c440a21800108005001c0380100d03070013056400807102c045400c1d003008013140d0300031300e0603c0d02d140303140e40010032400780001035001d06104002607951a4040049101615080c0c1900d008000036501007070042c0b02081c080c085e1194140b008403000f500346003041c3d0262440c000f09507001d503825002036000b40b15550f403500a00d54055a6501440d48440080d6200100000c004a002d031183e80b00d05406582c101043d0008001e0040081132251111440901d85500d00c006444000d1124038104841c141035001c1c000c01d07412180c0503000380d42002881085980a80350081e1040d40c4a01100480850a0030a102038800c1a582d54020354840e410141458a85a038580321840c4201c0103010184c00510001041036101c036144d4003652660301c40d843c100b86045c007000c00c0100305d5008050300303e810b90b4001a025100358021400c03201051794443c4400c080758000e85014243c540100130 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 382603956 1250 382602706 382602719
    0x210020703020307020a0e2401050724020406051b0606090f070309051c12092307120f0203060a0c0e0f01020307050f0312090d050301060c140105070504081203060307 73
    0x39016807802401560b20f4440d86500040b03080e08640c01031405800c60301c05100d414541d140192008110007640854000010000079295005003100100a00400d0f07a1410320940714145085207141c0c007450654a4540702d92000d40700c0d40100140301c008418908402c3d00c143c100083c0d0901540001c0d04a14180d140c1c03046203a0b0001c0000e200a00b415107902c0490001030040040d6132a556600b40c0314007541c20030701c400801106120455950741410310b2030480105440c021724030110841041419071041c1a4501c03181044500d0b402800d068002007498010306c40d03604490700300f051084040e10f009a030346207607085c100c1d895a81140c0004043c903590743c10a041250b81e800e481c050500480b810095581c1c3d605141c6101030352401c1c155000821071080c2c0d041400991034020350280080c20954203032200082c0303507000502c030328000c00961256000910100302949028003914a000340041c4c580400090500d610030300c5001014801d0780c0710760f0b03a01307004101a6802a10300a01a01000d468010b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 382605206 1250 382603956 382603961
    0xf030405010c031409030f060a060f03150c020f070f0f1509030222050406020405030d1110380a090207020f0f01030e030c0607120606120e0c0310050f060a060210 71
    0xd0390544814010851203011b0340e4200301010b12944c5c1d040091134249400b400b800181c1e40c256100d4001040680c10074400500300307102c03d0035505c842400000c0e100daa0700d1822403509107400840f8802d0301460300c02154030b98507450403606480d007190f03010f4180c0b46d544c00303005841d4040300820f000007084568240010b2030004803060106200105081507100d00080720030071200182d03000ca4005600180420a07401d0601811114007980c3c10040e04a0b0010b4a2094030b0f801950b0002403079580d02c2d0b4118861040c0c4107084849001c07014184d004c081e8289445506d851a0030401c18031656010400041d000d001c8e008481d004d607806880948030209000034021604070500c2c0090501d0303200d4540300058507042000e0309150b003045004101303070700f0003040145c4944200d5003030040203401c000301800344541001214114003080c900c0041c0c0403000100c0f66041030344c8088129454001c503821003480310980d401c914014030003180403003a140c4174101000b00301f01842c4601409600450710b16004c11320036a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 382606456 1250 382605206 382605227
    0x190f21031b02030a11100c030204031202070b0a230a0206090c060f070b06040f02210601020c090f040201020c10170c0a0c02010c03051905030405060a0c20030c060a0e0f030405010c03 80
    0x240c080b9082c6c0003901480750256202e80e62480c00007030740410704200b84400781d030200c440c54400b40003401c03c4904001d0119818440c00c40c0c60006c0c45103420464245d05800070000d0000264807802944070007070514020744550043ea140141449401ca140400340b411204459044044080144c80c1440d1075803410000d950040c50320703034030660fa03401601518007035000902d400504600c0e112800151101070802c08030380502402d04641c0704010100d019260421010340003075624a1003095651103100403450b1a040c9a81250000025415880c25a0b040f01405950903a503010700481a03483c2d00d905da540d1b02071080044000764260b260080554010101519078038041d151081c6000c03c80c80c0400360100c001035180c8000340c00082000140201400004d8120024480c14820043c520000800b9030584240003081e00c0580b0030104103440042003110041c0080c20241d40c8140350000b1104020070043c3e00b2145d06000318000010003036008002c0354241c410584400c0c45055080e1011994071118 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 382607706 1250 382606456 382606487
    0x506060301142d150a1d040f02040e010c020102040807060e0604060e01140c0d031a18070e0913020a06021501060804062310051002190f21031b02030a 66
    0xb40c58254600c000c02e90304071132107580d143d8422403031004084140000f400065003e01c1e9000841950121898592111140c100c0c2d04590024004806400010010700c0480302200d195881c105580403010f030190007500403140c0036810388082c1035444405031140000c401c2c00640c0100108030601040d805800381d075900c29810b2404030720490400c00450361a600100182505174131001c0043e03001541030060360344032006e40b034801c080040ca88002c80c0c0c11441c106180703406d85814100013061144209c4410034000348c014040d08090811000c81040c003103050900380e0050782d20f001c001c0f0b025800000c18103450985040040c15603881c024044800c040003510449800342c07620040724902049511150006040000c81e20301401e02150b0390b180c0300800c0c1c0c01240241900e44032090b48a801041d480700c5800d003810103200b807040502e07004000d01d00070f1000601c2d0148410509010240008205100c0e46064404115100c0716800c5034910303407030034034410b00161300030480d840f452441416030030740c02d240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 382608956 1250 382607706 382607761
    0xc09031518060f0411100e102106090b0603060a1502030706020a0e1f09090b0d060608031e03010e18070e010603020a090f03030503010611070905010b07050606030114 73
    0x94800700c6051800aa40c110148540f181c248418805100881a45108200c0c0c50758191024002e0250041c0c00a01f0100d1144030000501c100e15030103000300d00d060f91004004810000e019800f040000c184d1405201603072464240c0c0211641070000c2100e000e1280100b40580003454509001112485040042c0c110302060118100088190014217031000712074030307080c640c0201001404668050000401d078030041c140c042e01c0c590b5070001140b00c02e541c000381e4080b800040c0e0201003603581c0d130799078402824507140401c00a02c5107004009081504002c40304100c828210809a00503808203005840d80c5044540100c1c03c00b503208540b2004c00b0098000742c0381c506075501d1180c0100f4109900c04408a41c0000c0c00440c019806072405020f0820b0040700c4000380d085480080660005002c1d41c4140903841d91a00201c02007000f10340300410341c0f0b2005101135a151312015415400c04c15007120701d88601320105000e8513044c01040c5e0036920f0912441d48a0b610102c2c8003440000e01c9010320811903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 382610206 1250 382608956 382608991
    0x21030c040e0a0606080f100b0c030f0d02070c060801030209060d020301090f030f0f08010e0609060109080a080405120c0d1203090f0b09060f070503010b13080d080a050c090315 77
    0x1c420007071107841140c030a500042e045181030320251450f54014038403034000700741c40c0c02c1140c201e095040610544070602c44094a40748100603061840c442c074541ea0b00307411008151012010205d40040003417500c114109640340342e07101c1c411340301d80d203081c00002c0d808944500003400314200002d9504550b1700041c004104248262038607800300e1560758042d4001000704c81e00c00340745900302c03d4425291601d450b201c80990f2405501304108800640400e03c20011200403a94682c4196101000b618401c82030f600360102d1486c040013654410703c41d6600920300c5040c2c51052039404a143d0850f050080c00d1201042d2150740c40c00081c8901a445000341580c403152080450ba4091400303401e0b40c41000d8000c80f504200080c0d51622a0041104404440400801440c1544a000d4904441c00f0940440c1c940c034042c51102c0305082c2c0c98003c102e05225000c16000c2c22980118902e00840c0c21404c00c200980f258200070b000e903c00c022000b42c0642c025802903811071340c440186613004112800010004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 382611456 1250 382610206 382610219
    0x120709090e07050109080a03090e0705070b0c0c07050105040605030a0c211d0105012103120c0305152403040c03060513110a062c0a062021030c04 64
    0x301d050581040e00c0e0341c420003040c421543c10000007405040e0714801424401c120340d5008040030590b000d8200c08070f10900119584900850540e90341e070303901045160b418502020041215000107003501680d11407084001415400748040740c00f40d469941c0c0b0945940d491130b07084000341500300040c8003001854800840503141806101240b11403c1001103270b919642d2481032000c01c0070880048450740b502c4c0040140d050100c0040c030340c680d030049085501c110130782020ba4003200310314a0b0005181c102406425401e9050b40801d220b03520440ca4107161903000f5040c07002c21110b82c0030700410440f01140103c40c201081000c0d5034058403404041e681b244e101d41d1140c083e06c900b0b03510800202000b4031000200320041720b65070b8203e0310646034400143e2501720020a000d8000404942003c070482400300f9010003485041100100a00b42c5035042d681d4190003071040c41c200701120a820400020309521850100e8031094106110034005d8110100400c20141a0700c094104800300c2401c00000441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 382612706 1250 382611456 382611461
    0x506160b1522151521090c08060711060a020903010209280905040b0105060d021e0405040e0114041b1e030b06241806030103051b030d0512070909 64
    0x200700c1d142c1c4040501d1540320704600540c0c1040540f002001e507003007024040001c0c440b09031002d42c8480d291480d4840c1e03070044981604044d00c41c0601c8610300b00400d030400d204080c0d01d010120345142007260469661944101c42902000d400000c0301d8100c90080f44c40c91030f441e00075002e0f51100800040c0350240000020b44440d00c40c4200c0c0c3c20b00180090000c1184c40301c440f07444020001d198050205181955641b0038207078050164512608010603081d00c520000d5060320781d50b071005071105041c1c1840441080140c2c0007841030350300c0340d03041c444004400007043c0a01b0b40490b0b00c4100b4003106403100d5a07152030f5008401e01c52003400ea0414030004110f02c8040038a00b0319040751044246140c11b60900307a0605000034a12070003001c404005a0074402181c00f00101d08103505921034a88000115001c5540520702000303600c80030100000c42400804980d40304c180c0e070000282c08881e01d04206040d1203038248044440801c01c01d004240c041118500e0300355204c03446143c51110f0035100c501c0e1004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 382613956 1250 382612706 382612729
    0xa0b07110705030f07091d06060405040305090418020906100e0d06090b0708090c04020301060e090603010b060714011d0715090b03180601050a0506070602070203011d060702070506160b15 82
    0x41c1d0240d04108801030726807040074401f40c5a12100c200054104001e0703030b51100d010785050b001e40e0780d410010f814140300302e058400d01c01d0014007c7c00000d5001c500828400304159042e841601c0e0310012030254900043c0e00700030030b00d0315292181101001020003e6101d58001c081d14266202c0c1420000904496000780c0705900319160121241401c5a131140742c0b8070403100300c5001c2d03031040005201041c0c04c4034041c008900c085070501481e95654000c41e0140031045560b682054003c1f1305041003040c1c04000f9071f50365034207900030003c2d17840380b140c1182c411070031002e140f4883d004803d060107410200f5181d0308160f4a02c4c2002180f0982d2145a008070b030f4000c0307a6451885c13862804071100034405005040c0100011a21020704d1810100002c54502c07440303800901480c0c0c0041d000c3e046403001e4006d043e0100c22500748107000340c4000081510307100102ea9000050040185c0812180b03080426500800309407404090304008903075441e800c0010283c0164500541c0c40d0075455150b85401e4000d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 382615206 1250 382613956 382613983
    0x6080901021b070e1605090603060a090612140a02010509010507030203190806031b060a051809010f0806010b03040b07112e06090b060906131e0609080a0b0711070503 73
    0x440c051501c526401c41c01406099043c920010030145036040750b008096841161045810640d0f1752282b00c0015214041b03684040f03c40780c1803400000e443c1e080b60360781c030182a00925203182d0440728042400e49601d10140000d01140080c0410091075106201070100180b180c0112031a111640d04600030b21079100004200241c0240200141820184003010381c01450104c043d03c1462081c2c0000c2c034501480020204121000c1500440c0d101101c1d0790b02e00107000a484200f0550b11441900342200003401113004c41d111740d400000d0f84400c99005c0724462a0410f90240542d118130108442d606410502075440f4800d011800c19001020030000f0103010341c180b04940503504d5500c05a042e40d903150300810500380340032a50503442c0c0b0756100700d904400d0704860ac90b41d41c0600004480c481021a0042c003000d910884568001c000c04218070000d84080d40c495512050f0760303040321a500e40c01000c0061462903c50b0100b11303040c0c090785960f40940100815242c21503292404640707494070011816 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 382616456 1250 382615206 382615213
    0x20030304050c010e040b030c1002030715150f0807030807021224071701030f05031306030603060b060307050d0e0106050d030207090c180b090105040513020c160f06080901021b 77
    0xb0b0b40c0c1c2d0f80102030491904410360f003e0103240300b41e00000361102862a03550340900c03200304488510794401c1c41191041c0740e01c940407190010114040400030f240884c41c1c3c90342c4038400c00011038031520641d410390440d201e40c8010280315046541c0c12001d074201c140c00f00c0e00300c000400c101d0042d020a0141c25619280400760f01c140111002c402050158007030301d01024010000340080400e00c0e9155490b043d21b410054400000280d880c01074510300c50a000403203000420359010898560580040c42200c2c000ca03070502c211024401002a80d02c01910090089101004600c10403055500312a00ca80c10000000034480d03a20004140189130082d41140142c1144400b0701410403e031051000d18000c510f4059042c117a4103001980b19503160041400e40a004141d0905580c401c000715006480003612156943d912511108041c0d003000306075031046e010b81c80741d88801c1e000710180c607011180c0c034001e88081d617854007100b174840031805022040c1a54080080407050b8042d10740c84100c044080006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 382617706 1250 382616456 382616473
    0x50f030f04060609020408280c0602060a110405062a031c140906131b0609080c0904020a1403101a011215030308090f100b0f010306050d032003030405 66
    0xb01150b109810001000788184030a20801700c00082e1510f4a09000c0d0900102d074130740710380507054903a001c0c1000708542040c03500442d1442d40820303d1800394500f9401400310b01c100945a600600482c014070390005800d010b0b00b0301240000400c0190900010000a0112081c910300c3c2c0c115408402e1100e0a40d8126078949400780103031041c3d039070301400d45030106d41d641815600e8644030f110180410300442102005c95082c010201c04c200f4280140c80240040780e603a81c8030140072040c0c1c92180010700c2c0168150303140141452448140b14550042176034264070700740044040310440103010240c040c07090031440310007620a442030220100f0b10205200e0f0317448400000510446070403980031001424002e400c0c102c6012a541032041c2c0350300d42041c1a072a543c10490314a0310813065090843c41c4100034405100e0861984281c0c0c450784280c40c40000700901d60010741c2507070054441c46400925000c4070002091080d0300202160102007002c24403c1801c000b40351a40d00b00b5a0155a2604032481 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 382618956 1250 382617706 382617713
    0x1302130c030c0e011409040519020304060902010f020a0f14012919060801050d140d090f1203120c0c1b0509070806030312090c03070815060a24050f030f04 68
    0x10f011030a03103800d00e0a01750300030401200c29814043c1503007080c0900d4860000c6110341154461070401b00c4e030080c07800c40d1130346400d041ca0b4002e0181c281e41680821035081100c00c10902c0030500e005e03416040001120301001903070720001502808402c45501703560310032040e84400c500107400c0c504080d00080c0080041e0120007001710800c2c14034050408988084802c100180e0840402030445104071007048001a51307041c8a200340c442c0b803941c001207014000203d850740c0c1d081010342d01071f10000707581c42c03908070f885042080000e072069801401003943d920b01e000203003515810105045285141411548006544104132052801c08000e2086000181444a81030600300c2d41c4c0c0c090300034a01403425081c904046502e910606c051003c1c0180c40798005881ca0b0000c02036440c0c048805030403260f0f030301c1e82d4090094031604030710a4582142202c1c0045a2280b801021580c1550a40654091124010b0762407060b9070741d502100e5018442e061041030920034404016622600d00310b91040e070b00e40750616 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 382620206 1250 382618956 382618967
    0x606050d05010b04080d030221010303030912020123060f060a05070312020301030305040303030b2d010e03060708060d110303030408040e0a0c0801050d06060504020f090102060a141302130c030c 85
    0x3049500680e60500040001740c1d00010401d1400c1d11b18280160344415032407054006104a00f4045100641580000704241d8181e111611190149101d46101c1c001075104034261105031607000c1e04540303080b09055103019148002500b20800424199800c6c000f00003007005a00643e00081c08114045510001d241e046000c00455003801c078421440c540c15a40d015000340520700005e020580d45e61126149034651201c134440351545401010b8604407188824041c0b01e80340c2c00903e0014000b107907042c800c0d0900140a901500c04c03900d030174045640795014480c800300200c009807600a20150444020f0700c0c00c3c002940583d002e2800d25690300d040051801d40c1000151950740356038501400501d010741d000d19001c1c1513882c1103c6080280d00c0504045010386129000140d20910028003012114030040040c00030340d01c20303025102503694000c003200031907400f041c811218040a00000d645440c1c288030040d04c1c50320080541c8004d824000ca00000c036019441110b021a83e60051260b80700d0700720 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 382621456 1250 382620206 382620209
    0x90a050f0c010210020a0302090915100503041703090a0b0903070c060804030f08060a2d1d060420030f0103050c0402071a220c0906090506090415020d0606050d0501 72
    0x54020716007031070301200003550f501c51103080c5841a60b01244114800788603804603802d844000780f0000b4075080100780e030218112a400b80c0e41c89110784600e0441d140307020b0b2050300d109540001d0003028944035443d0980c81d40e0300041041d01640141c0080900098221025a004d001030000454840202d4a804007004155030890014441a24200000298800d010071200307619858860040e03241d1601059410700d040d00020300e0b0590294a4411414400050003030b4041c0f01028084c9103030f41c50f4124900c0c0300c004008640c140002e030002408505081d00091094608561104201105049480a540c101360b65400c464400d000041003400810000d007045904e088504515140c05c541d501100d090010040e40352000740c00c80080c2413004c10001c500014910000101105203840c0340000001d005401001c066610348480443c0c003510510485105440191981ca45502c0703a031102e1101c0200c03e00703400c5c00d00e9000c00a40400100a0180c034000380829115203413507074400c90110b0140c40c0c05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 382622706 1250 382621456 382621483
    0x408030f07020f01210e0c0a061707050c030403140a0c08010504020a060203130e090f06040804060207080a08070f061e020702041a09040201080a140f0a1b0e01120f05090a05 76
    0x443c0c00c0e10030040d2000160102e0103814172000624090301c1c4003058140f00c8130602c1d4585c0701c9940600050800c3d00000300b040708e0b003000480039001d640d80300c00540d5136020b030400c074401651040c001071001800192411f01d41000d20811036a0212465445281307840302904080e00380e0b5101c100f484114103003170160320040c00540c0065420b01e40c40e90034403801d410303c91084045021041c0d001c1006a40f040c08008800780c010303c159680780c81c25040c240c0d0315502920503440141700d114000500c10f9404a0180101c6504c1803c0e1442c1522070346660b41c1645903014141d0f40940c1e12904588610003000720b4000548008502603141c10750750040200f124155901119000c901510004079a034a101c1c245a2003942401e03d82e00c0741c2c40340d00000d001050001400300d0444a40300600074103c0e20307031103081e119240016062221610001c030b00103101c40d50200c41008150000c030790b03139119800b6602681a60940c49000564060510008416240c00f6111a403040d00180344160a0000601c4440701c400744 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 382623956 1250 382622706 382622717
    0x1091506200d0e0910230604050d030306031a01060804150e0f1f050603030a030c120207230307030914040209030105161e0f120906090b0a050907140d06020408030f07020f01 76
    0x40c00030300221046d400074066991444c141410341840d0f90b1182074901800c0060025086c041d0b0f28600030700140900d001c140c920701c540c1e24105011041c0304007401c4c1030b02e12540e1131b03c2c8180c945035201944600111680300141d511031025940300c000c01c00441c045811500000c2400c20070361081715080310070200140000ca0709000410605071800012030303140c1ca0861400050443d0890011a410032800b011105940d00004503101070080c020800d031440b000050205001500b24411259244949100180810a212000c0004031040500b4074900c00c805400540b401c00382c440040c1c21039070120348074014042c0f8840d143d842c480c3d02214000008200c1c624951400d030b905100500404980c050303140800501c440d4001d0020a40d41125800503480407042c440c24910345000b0814590031207010030180e20301030002c1c0900500003402001c0b5005101280d2001201000f8450ba080b00d0840a651203a002c00c40011001c3c810030041c0f0030036580045064441c0d9103881042500120462910304214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 382625206 1250 382623956 382623959
    0x50a0e0307050106171912141902070e09250b0a12150602121c0203040f02100f0e0d080c07081e030a09050d240e010501091506200d0e0910 61
    0x507a1b070301755040950054a1310340b101d400d11030b00b1140c150b00000503007940310010440b1400f4000002d1194400007a940958420544801464807851011a6841c80b81e5001044040b1008920002101d003010b00324102007500d6100c800c4040f0a521030180714001030602c10102d41c003900244525840074114400124000345044002903690607010070144003184001000c10111300750380070107520030f891090250346074581402c1507481d1070301114082c0d010f40c17012016095058419030b000718051a030f079240c80020070440300130f000c0d4102070140d00f19040c0d041045100701c100010408800100422001400d0a22100c044500d80c54031104141005a00502140303140c1c40c6c01220355825548180ca0010500d8060300700301c018440c0d2000c020450300500c40724061682240d4204e07001100e5188002d0102d0b076684e010090890300c591034101000640d0782010310002d8402e0b0a0a03100191019074048500813070202141000040c841607000b1030344209020704641400121540c1c04040c1452906425 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 382626456 1250 382625206 382625233
    0xb100b0703110a050703080307122a0c05100501051804050c0603090c0405012d08031b0a06060b120f070e0105090a0b070f17070510050a0e030705010617 67
    0x28010818010103008000480b406003010800000f4110b81c0c01000711218903940307003022491948103071801d1000841303105908007011075500401074441c05c00c0d800d180c0c0070b140102851112911880300102006100300504002c28002c005044a070b0890a01c000341d030b54504030800050300c000c200002940f40074a010400400d034082240300e4141000e46140d56a40c0d10110014100850b05800c180d20034600303c00844e0380003100358104014810211026111a80d0146089010320b01c1d01c0303002ca55038410480850fa0794101050094016500c1048803000046503544000352801500803100240001c00c403140b500005410150b0400440340900413542410280108540b18a5501c241030050001e00a03425854103003611008003014144c154445005151424060362459016110b082c622040303100c4d03859010080314405a4440000c101d5400c170315103a00050800104140c83c0241d540e42e80e02d10342c040510040001900c22030001030b03a00c0c141001d00c0d0341c2c2001c1442188056006a4014015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 382627706 1250 382626456 382626479
    0x12120906090d0906030b060405100914030109020a03060207170309151e0711071d0612030c100b0301060504050103080306120111070807050102040807260d1d0301090219030b10 77
    0x84e19418500441c50720840760103e0319611441d0300c002e41112200c6443ca40541c0e2002d42c030001d4030350200d14074201c13080c0c0004140c00e0703520047d0041c0d4407507511241000081daa581c000d0162900c1a06003840708100006441961b0300100d0707850344a500543d450031054002c40c0003650744545c4504c1d000310f40320700d45040059005402420784041c04528100354101f80390401000b0b00801080066902d408501040041c030007409580e0726024032600c442081024001106407520b07445654000d1106c40701ca554081e01410001c0540c1d609035694542c0811503803a140a954080d602400800303550703050400a00210508440d0813420a07403510840d12070170845070044549541d0054050b580f165507900340a4028810341d03202107118455010002601000101c1d00d40d9014000c1c2c21241d42204c2e423103100d0307886124500301311000950300e200c801c0c009c01d040c0d4600300080038080e00015016225901142110001c070440074001035841500b00b080000c14480305601c038540d600400c40f01403030f020310340300c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 382628956 1250 382627706 382627709
    0xe100b090108090c06030702070513050702120a090504050a0504032709021308060709050a0812030105040c05070f080310050d02030a0b0711240105030606010909020c12120906090d09 80
    0x1003001030300110b070f1209000c000040c112200102055038904140700060b548412a101701800340750304a450341408003080c803560f4450011600500300c10305280340507003801e0703020ba078441c0140301c8001c1002c0790b01e03102c9100325403189100100c0011581042e08000c0d0184101c00452108450107200c140302100c030b4901003c08441c4d1845016032600040288110740403000e400c410743c603100740c008000c100b03944540d21108850702903402d041d20780c0d11104016192050541d26118a0b1300820042000707050907440101ca6103030503e0202e0038648d00f5512000151210034040d201d41402009101c010180c1c20422401458116249884ca12a6a001c2238a0780e0a5000151500003941c00282000703002ccc10152071240000001e030f031489180c2080d21040711032400c005401200e141000800c66080010399503020b184161144410186051580d4011394006021a9401e024600c0680400317983c0303030040c4c90700d2060010342d00c5481c41c2c24040c280c50284010b00310049548203112452250f40c10085280 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 382630206 1250 382628956 382628959
    0x30a0c030201080711060405010504030e06070c03020105030a0f020d0e0f0a030206040809030703150c020606150714030904020f0714010b0a0306050a090f030c02010e01020606010f08060a050a0f0e100b09 89
    0x300944d01c5107400e5800d4118000564443d00501c02040f040103c103500c95441544070781c0300e0648514185045c1300741ca006400b0010010760014a040c0b0166000c1e00245602050034a00407407070b00140b10031501a41c10000103130184c81d0311009181c5d00340300c013031041d1032381c1d014020001d11014580340c900075903a480142002e0024840000ca10549440500c201d002031600705105600000b00c0300b42503401000240c1500005005107000f242c841d181491480129034542d4a1850a00140307843c1c0585c59244805c0c0c2c4c202d00c0c4020401c40c64542c951380040c2041d440703c000d409440360b41ca030401c0c000090200c00242d5060340b600c20440301582d644400c40b010b880c1c000400265550300d92044100a1241280140c00c00c801a007808040540c0807642c44d251038400c1e80c500198003420401aa0f840e40e003568050702041c401d42540d100144034001c4603511810081c100803190350707a00c01182000c503681d000703440c04485a460910000b13003e040302d80d0700701009030104181c807407a02030318140381e006850354103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 382631456 1250 382630206 382630217
    0x60d030530100605190c060e060709090614010905040f0b0411040305071a04060f0c061a0f10140a0c080307091706040507090e0a0c09020c010e060402060d05040302030c0a1a06030a0c030201 83
    0x5080c007e03181c0c00b5080c4002914211005414803d4014100807040e101d0000034505003030010445104111103912082410784980031980d06140c108006880d006010000c1c0581c3e400c50b0b694030b5079850207424901c201e0700700200da4076402c50510f142003c204e9045044d164081c0c1800d48403440c00c0780100c408a8a662802846d03032003e03000200d07004844040050b049600301010040041d004081c1104001411a5003910581900c0280524084c40e03100900118004028210080041c040181480300c4549003015054140b65a42100c1d60010340341d083c0050040281845200c20b884c40c40c50044410b000186441c3c81d03d6034549503622464002c402400307440b00c0f82d00110040404c202c00c1000e9000c00c41013800c0e525151044001e41024940910540c2000401c829144004c95118000c2d40c0182c2450300c0d00c031310050050054400600100c08500c001c011041c4800c8050000644c141d11410f0010701d100b280c400f056510120103001c00303200f504040e0b00c4000254400f908401101e40c2030904 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 382632706 1250 382631456 382631477
    0xf0f06070c020a08010507051801030b240f03090609060912070818040c110d052113050604080405030705090c0a030e070f0303050403051005060d03053010060519 71
    0xc01e03560766030f80e0310501c0650300b45070521080941020207021480b40e00b0055a911102c40c01c0114161003140750001c0c2c202e125424104e040e1000c503040044034083c801c1c0c480703151603000352071140300364000c0f204851150480d60501a00000612400740c0101d1543c0c0145085c40c40c11000d03903070a200d44070000705540e0f0300040755040200e107907120095a010084c020003401051480180424510071011042ca000309505900100d0190b000d0301c0c060240c015850904004d2810768281d54080030349444a84c1e00101d070036900240003040741a10070341c0f081d0201c0e07031500e11708001c1c580b074044a500028442c1c5048003c01c12801601da0a44800112510b03002c921202d01c070148030700703206040d080341c0301c420407012010082c160020700910481c0c0c412800c44102c200407208036000c48005403405507111a48100801c0802d10580281600802200e8804a81c440c1c6110040030204400020007009901000b0016148070348000700c0c00502d882d041a074035025404800e030b03034000004080c070418031031003000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 382633956 1250 382632706 382632709
    0xf1909021306080307030f081303030906020909270105010b030609060a0f06020a1502030106050a050c0c0a030c0302010e030606030606040908120103030305180d021b040f050a0b030f0f06070c02 85
    0x11100e103501c1d5403460810015031901c0005440c1d0b400410154042103070001312881c0340748103083d511302c104100300e1100b42c070180c01e5034214058980e03e64261482a000e0001494036603c0840003401010b00d20702c0114540c0d22141c0d00b072603c0d00d5000450210307901d00300c01040020781d03c03411264800403c4400f0102c959400001a41000c215004510a000030031030129030140c0002e4071444032400cc5030220140240740401c3c909a100034010389001031400d1050260490190300a0301c0104001020780340b449002c6800300e401c4400b2503105076015045201c081040d56000400420520b1094024081c07603c1c01c200803030b503140c0d00a040340f805035540f20b082105001c01d00040d50f03a07c02c2c014405a0203545d40c3d0400402400c0d05803a0840c0e1480c512008101541000a040c088034100d82c000d000c4158518400e2107810448540c0f01c6c1e0440e80351514680c11050324030039244140f8441d02d000030920341c20700130b05140002000c2c01003941e501110751302c400c6500008140e5801390040c900504000017520 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 382635206 1250 382633956 382633969
    0x10204030803181f0c12060b1b0f060703090b091515040902040905030a0207050105070b0a1a2106010b0909040f080f0310030201080a090320010e0304060509090f190902 74
    0x614071004404c2c41a600d807801c80981c106902d012080c1d9912440070f820002200c04440d4180708045016000b0040c00c1480030914540b04e00c01c0019009507107080c01d240d0180381c10140122000301c0000c3d5500e5544040203096120716401401002c001d0011394500c00d203031000c0048c064541d94510710070540b210032503510740d00710003000c0b50b015109010108242c500329a0301e420440382d100142c0144040810254820420340d00d05507001400c0d12841d480b000b0700f04004048801c2c03d48200e000710340a0003c5070b00c4d4001050024500b404200036003151541410f0300f0302e101078200c4680c9003010856002c40340d54030645503410136004510b040544100e0301c0d102900307110300c0001601041002c03040210034181d6064400c1140d000382c13142e103815a1030300f2524040300d503911001401b043e40c4209030341c144031080041183c081480000058011146059a8510b03006503010000240340000e007241c180c00c01007040c941142903084290154140280e403805807a10200c00c1d40030050f900c10010003556602c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 382636456 1250 382635206 382635223
    0x8160e010c031101181103060601020109031205091e0f0c010302040f051507060519050c0702012f0609010b0301060f0303020705060d020f0a030603140c010801060c03090e090a050f01020403080318 86
    0x4807a5035031720741c4061424100d41410307041303518464000c000004001d035006018030300445900d03a560141040c08141072100402e0003030078007502c9110343e1903280440c040c038a0718110400c45501c02030649a1203014024504202c40d24410304050060100f00b20914200c840d05054800c121464207a19400d5802c5d020380c1c0c0100040a800c0078100300034400c0580414003013425010346d14105003c0c6540f4509c10940511072000000d0005e00e400c4500d210480052203103450f110030314924001801c0070114840e00d40581511041000d0350340d0f03041d609040c0707424880d800062028a14030b0305401d1540c0c0f00a92103e0051040f00c0c000e550000b404610812258112011849052003582d00c40001404c020700429080c00200d84060004480c1340141d64006040c08135104141d4072825a40c0c00c1504c1212920114407086082c04542580803d4259403804007901c10141040241510704407400c041d8540b00d0040314624280e44100000d001050003801120340c00844032a03026048103030403607414a0030111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 382637706 1250 382636456 382636481
    0x1b06030911101b30080702030f040302100219030306080106080f0a0305160c0603060914040c03060b03010906090f0c0b030f0105040209010c020d0c180212010e04060b090708160e010c031101 83
    0xc0104140003040030b900a02513280c03a030782e0312860f96840c013009036543c0c8950001903490000610081006181c140121010b45009105459011808003c4402c0c0010901d4080b40860f03155103042c018112b091180c3d60051040f00018240c0310519400d1644079868844081d082100020351a08020900341e80d00205983c040400c40e1615915240203000b8030ba18003510414a00340709140f002120220000c3c1c2c0119084045071101920750b9480000070880428030035015525103104a0109049108000440380541c0640040904910300003003c482c01c3d070001c4021442c01e00511054500c200c02c0b49056a03015600180d58041c5400182c0d00841108030080d80301403403104c110308103c00302e400103080b0b4607980280c450641c200080541a80684000f13482c0398999000108541a915030749660024054400058511140c0000c140442c40031917248021980b81e030140000c5a1429891407024105480d0007501170504d00b00003818801000005410081c0420ba580380c1251f00f980f059409000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 382638956 1250 382637706 382637753
    0x60a03060e0414010b06030412031a0a08031908040302060403180b0c010f0b030c030a060f020c2409030918071701140f0a050307030b041b06030911101b 67
    0x10b0070b2500250301c0308103004006455080c4070303540d80305041c40c0e000c0e6030046a10143c40c600c81102100100c00402c901c250500c20b0852600e03410342107403503980c1d42030003074004032025560b40c1c0d4190450907581c0380f40d00c01d0726042141c08020071010903030110300244c10907850f250642c4508101d1582007003801454015070312403100020301441c0c0800540c8002f1030210240814440303c1403080c20151507a0060344108d4060300040400c600003401640504800100303004014201014a2200d074030300031110808524021b014945e40740708131100624940d1280758200191b02d822070640100d07040455009182c441d0600d80008900200e002d56480595210100f070b10032210b41c0d43d01009901c2c07204460741d182c007030041e0711006000340c102409070405965001d402441400d2550b40c43c0c030b10b0444014400da0b11342444003110200c0204421005001340001e550200e00e405031400c00c40b616420700402544911035202070200f4150300200710a0300d00307840111040c0c4849031401c01a0481235402032000002c40c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 382640206 1250 382638956 382638961
    0x1e0509061e0d020a030c0e150f0409020f0306010210180803042a21110609220203010e090312070815030609060a0509070806160921120f0e060a03060e 66
    0x90b40e43e8090805074406a03010b02c04610448400e40314014940c5810380c11141c9521050380e0401c40c080201140740308807c02c01c1c0380075503480051741280c1107541140905e0000000340000e41d80c3c1002105c14040c0314950400a0000712042c101510030359400003009800b0120004042c44031a03606010101040c0300f8004114221240101c40443c250140c00600f5602d0344261040ba091b48403201500c40c1d100081800d24a5414200400798000c8081c00b0780c04044007031403034080c1322400b070003080d10400000c1c0980c807541445101d0201030801005046543c1c805e0044010600340520314980201650a1600c05a2900d01c15407030f419984503107840d014826081030001c14000014268840c10060ba0200141d480300c4c4009a100c50307ca01c20000709501050101d01c032401d0b120046021800d00c0e080c00d000c15541c1c1d00040880d00c0d13001010038041c00f525040f140510401041c0048001d0301c42c5440000c0006105c4068005885203207110300480c40440c822403d90b0217030f8022005000b055031030003800e2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 382641456 1250 382640206 382640227
    0x40b0d050103050d0f170c091e0906010e0f042c03030411060403030f050306010513060201091403040501120e1207050610060f050301090504151104061e0509061e 71
    0x200402c1c0320450301071040d1000d541c0c009100c1e90394680035004035903d1246440c0c40010300095040302600e1031300300010070024042d2a568004941c5c03400da405022852091040d0400c11003400001011b15040c081d6541000e9910380d21003540ca402200c0031140025969040400c0c0e0b01c10805188843e0803000181c0d50745480080008080c2d407046110b108019000e01160081c0049401940301c02004a03803040d101c4044c1030302a40180d03600c030300d043c94003508090b6403603075904108400368042d0025035034610040060003c2c8c20030940c91403110b400203614040c40c3c80f000a101d1145100b50741003441e61a030480951b0f40060103085480c11505492070341340c18950501c203448800549600454016403400000c00354011103100c85c0082a588a190031070b8030340511040a040020802c640340ca001c8403e082c0b4a140500c41c410503403071880e07031a50b141d9003001c02c0681440c960801d4000b084c1c001010b9450b0141d407040486400c0a0181c411b26100c01c4604181c003d40d80340d6985c008881d90012400c20a103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 382642706 1250 382641456 382641461
    0x3021003020c070b09030c06180a030c05030c3102070b04050102130f140d0305070b070f1202040b0412020303040911090406050d0b071d12010f0e070b1204020402040b0d 74
    0x1800c140200f501c004a94074141c000503445910032164041c0c004450852a0389401c40182140d890314038042c040c00c003c0800094105c0000e5001150108805441441a802d08220280207401d0513181591481a6105d4490003241480314070801d0035500400c000c0340b0982901540c0210368840382c81d400d281810702e8054042c0d04a030f10401c074040c1d44540300003440070b01c2c1d541d080d003200c56110f01107005c005000284604c2c1c0a4060007074091100411545c2c002070720344c01542d1710030400342d40c6261401000707440c014100220484490100c1d4010720040c803805c0d41391012103044a03640901622200d040d440400d0030740c001d41e8840d030210303481c001040e620040301310300604503400c08480801825486100b00001d4102940020300410705200000301900d005035581204690040e9a2044802d1800001901202d104804600030f03516662102c0c1880c8440c0221002c0f074441101610a140c141500b004481c021041079003603100219000c602551074541c1260041c0141c20385182c0c0d0384201e119110007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 382643956 1250 382642706 382642717
    0x30f06020a140403081e0702060309070302010210020a1d04150603020403150504030804060b0f060a050706050f060102150403091214070b0f09060706060518090606180406150302100302 81
    0x71a038410100b420a204807070449040c0c0e64400707049400c0601c41400300b80c5141c01d0300310403d010b05040002c0005070340da0001440c450461000141121400c5100090800310411140718a03d801448203030b04440d0403400c241848405041014114082d00d0005805001002055140070b43d290b040454010750680060041d0380c0212804038142c00120231070b40448104543c0940020b007100d02103400280d50f40c000d07034299003006002c6600208208000360890340b143d50708401040e0005a08010804c0e2409015841224119000b0356850038200107510b62030441d07030084887c0680000641098060f0404102800c07030b070300a0030041d001e20314101c2141010310040800304d120f254030004090b122841100e400e2000c10301402e0400e00d840c1c0038401d042d0031209040714041c0e241c5001058075110b0119442079a0205903000e1500d0510071011820b105019210724007403107020801c1040d180e09040250380042d0700c00340003e41c0b607213a03e42d80540d100e59500000c0d13200c00c00d04883c11641d81d1603005401c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 382645206 1250 382643956 382643977
    0x30406080903220608071419020705100c0b01052710080a14010f05060112020c0c04090803010f0b0405090402090601020a05060403050c0111031e0c13030b1801090309090b0604030f0602 81
    0x1449403206201179400c0981c4c7c601100002804000c0440103001d910f101d044130a68a004540e80d040c1c6808c0010b0002c0c40b030044000008264054030414091f1070741e800f500600044d62b42c00402c0000a5041982e6003852002c00d000c0124100420300c0d070b8160350078120003400f04a060b200e10585500d400400c0c03003c004a250110b40c01c00e00c904000e80380f148a0745018081c1616a0b0325041c10080001c400fa400080c4207114500690002d880c903602c1c2c60240c0622036100c0c0c55403c0e600e604010b480a0290525089890207800a00080c0007540314001025009501250641c1c542d581d4040100c0c501400700400808078099002030108040d0004040c090164412009000b81004950440100d0200301c1e14041619403801d50344010044507400390350403951064a0700e00d000a022020208464558000c5038a45a801c00704102e4103024401c1d08109581d1400074019001e5644005058551900444245607901c4c1c40d400b41b1540c514089400071a8040b901d1740302d60115052020081d040f940e4081e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 382646456 1250 382645206 382645217
    0x906031a060909062710021b03030108030a03050a2a020606031f0213081f050601030b011d03031e0301170a050307031818050603010b0103020c0304060809032206 71
    0x152141c9821030006120300d42140044c001651038030b07055000a500b044400300d40ca00391034038100b2280030600020044014800c005642c4507003803080340c21801e80c0d240c0e8170903da4000340014800fa410202c07c48090603414940455503840d1403205000509e9000f000315015805510078050741c400c100341c541c61840700f03902511581d03500c4200b81f584440c090104d00d201c1110a030128185901c06a010b03040c1d9034001e10103103402640702c2d1103651811001169600c0c80c40394140038024030440a001d4954406420318040c049040044006010a04401d401e240750090020240030161400c00955582c203040e03a004c0403030790005140d00240b07a4400e000e06490640302415204809400142000c43c65501400451400c0c1207070b102224000c2c2e0010340d840041d8000100003608a81110103400074400c540000140c0d401c1c51010942100c210086c803d05260040c40500180c0c44003005403411620075041482c5540d440d0a009030852240c1d641b510105900040030040d90b00e100c407101c0381525419181c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 382647706 1250 382646456 382646461
    0x40903032f040504091b0e040b0c0a0f052b0b040e010e0a080c0a0c030804150c11010c0206120a0e07120c060e0d05060108061006030204030210180906031a 68
    0x3801504000c03114507000584081004101a003841d51003035030745a0143c2055075101800f1000c0150076400c030740c498050074200b1024082803000b030342c0900da0001140742520703151020f14800070344040c1603081d0440c2840303004140000d900111504400745004001800c031508901c4500400080500c110700a0155160140307015082e44144035580e1804407103001010080500d5968514a074042020700e0010b0140200340f034001000c1e280c0060155105580d0710380c64909021904100d5809540b140741001801140080031801000980c2c05c00e00003860540026000c80c004a80f8a1040d8181800c880c60790500b08605021158003490f00d040140d400e4546043e52010710302410107044c0d03400781200c401c0c84d004001480c0520f00b400304e00c51010302902404003442d26020304002090784625110f403c0801084401031a8180f04005040c00c0c0c1011800c090a580100e864421a008450180496020905c1d0b41000c10780c030b900001c3c001c1d40402c0c4400c075160f14001c1c1000981c503459560070f000b00b002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 382648956 1250 382647706 382647761
    0xf060e01050f1008060f011406070506090a120806010f0302031b180a0b120f060a0905040b0103020a06050a141308030c10060e0f040303050a020c03040905060f03031207030c090504090303 82
    0x304240106c0c40000031403080c2c1d00784018200c420013800c00c00740d84214104030802c0025000e00109100e1080c11002e805d00709100d0808403c11105031b9141020401c049040200276a0404070455071855a45801610707642c95025010355081e002c8401c1000c18030102d4075502c41003210544a9500c007040c0c90310700c00680c4c0c54001e0b80b414002c170311025150f042408000744103900358403459941700800911080002c0c0c0d8855200d003c561042e1010f40391141d01c3e00050082d4202413a500005021901e4a01d01d45034080304010140d10180f1900260800300244903802a40640c401c0300250020600f40c03540d50402d4100706076503400044100001038145840020703100001070240c0d10074195609010f04c15a1290b0302240104002000e1705079040d400e00c4200d401c5001080030b44050050000001740c40d042100030000031000c03070f109551007035004002200c0b0010800701c0613504102c25050110300c10001c0001600e00a14a030030194116103011148024036a03d5000448100c03100e600e00490b10f841e801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 382650206 1250 382648956 382648963
    0x1b13020301060519090b160203060708011404020702040b06040807090c02010b011b031206080706030e06090a120e03150a0f2d0e030a11060709060c0f060e01050f1008 73
    0x86501c0208034180a200c03c01c0d1342c840300303120451105191628565840d4249404160081e40f00300c801e9900300341110046017030030440395410500c142001c4181e0340c5400c640b41c03808400c4144070b0b805941c003c10482c08548607500030820f08000200030703903150303601c40d0b24283e42c55400e4441e0148039802e0041c4061020b0062080300c501d40740682d5003072105907610380c89400d0103031802401c40c1000651361400003140c01a00c200b07000740c644030003e04211840c0c00070040070b0307480310544500c0e41d403c2079090004604000441e50009640a8044500306032040001e0f9203550a0887c002d070140240a00700c0300c040540320003944180c00c0108104003810420b04240d0032a4000f84c881814000e910060480c4c282822341a002544505200401d524035072582c0c144c1560000501c85012840240c001c8001c01d000380300242e4401e04a241800a2603e490340040208881c8a0090045803401032440c050152540100648155001c0288a18244002c5894800b182114601c08040100401190121011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 382651456 1250 382650206 382650209
    0x905071401080c03070e0a080c0301062102041104210210050a021e01091e1217070f050c0f0a030206011e05090a0e07030303090c1403030d05090f1b13020301 69
    0x40c1d541501c1d580c1d41c450307014104c2c1e00151941040c0b05445030341101590b94600744001803c242d03406020013181040506084d210a60400c00400420f51619040c501e4443c03040000950100d0703010448400d1070704080728510668010512070200502c0c803440c02512802c40d49001d49c800d8a196038100c0c1c0302c1108403014060302000c0e10058128a04100b41140b00001c01c508203042140002114000c84d640da03a555010b0a000340550001818040c0900103040d86140318500385040c40741680901490507084003000034841ca00b40012040003440300d40c0318a05035000e80301c07040c046800c010208490781c0c0d5250610582140140b0491001203502c20000000c0803028440c8925840400e003401c5c2040000030b0001c00c243d400980e2040242c15150040041c280150700980f000620340c4060304000c0c565508981108803007076103c80300d038440783d2000001c0720441540500c00003015118810560b0a0403442e03c032280c401d1107500d00b850152046000081c4039070404580244038600900040d500b0f80c00309 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 382652706 1250 382651456 382651459
    0x5070f0518091c031e09080d0c12051e01150504030f051c090e060f0a0b180402030a060e090d09170f03030a06031109160c1707050109050714 62
    0x5035441041c4035020200164100403140d0a03078000b6520340398014040006030210400090b202c007603040c04c4422415048484000e0400140000803503910307070079010710038041c00c00b86040e0b9499402c4801841a9041d07410880d01e5141440241080d520420300142d400048081c0b501504000142880100121903042c1a458071750904207440d680b10190074658481003a83c280c0241010f034200300d01061041e031501041c603101c40c1e000d039081c10a0300c02c0c852001007909014607080c4c0c0c9682c902c0e6580031800e40489480c0040c0944d218102044511414880501d070781d0420b00120511551003000d40041d01030380e103d10404038041da43c04400a41d60441100040003103143d001041c0400c190383d081e44c084912040c4112030044013900c031424a564000c0f9850800790b82d550340180304010200e0031071907060008403803805030b42c18942c020074124110a401403007407180001814041051200144007500f1001914075150071903800c0845c040c00791032400b101d0070300510700f0204203911924001c0b01c85800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 382653956 1250 382652706 382652719
    0x140a05150d03020a0506070201020a020d0c0818040b0d062301030b01150513230108191d01021603032007020108070e1c03030606020309030a1704030b07090305070f05 73
    0x300c84140841d401c44808150b046000b400d0041011440030080f05004403e0760703000513641c5040e01c10090a02074010f1005007013004010118010586e86c00903035008044003181d1500001810000a004021043e03460f90042e0344111980c0c00e01500f03501c031041c100805011202900103035601e480510a0902000303003004482d00052041e040e5812140e104880f0f03500300a440e0410790071030021801d2596108101c500c088214504400d03032140c0e07020b85008000c3c02e01000c1410500351036550001ca00e01c82854041c0e0f940192024120302a100f1140c3c400d5410007155601850b05c000140070340d40c0f1000b07030042400c0000380c80385c2450410203002200c80851342141010715581c011501d0f02805440070007000030703c2c800d01c01c407591003218441c4107049408141525100c145805030030349265512403010340d0014820003206132004145802c0c4260712075000e810896103004400c515000300c0e0009441e030b15103c02044081070300b000e0000190b90040046580d41c1d039443e180314060041c580903023500201c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 382655206 1250 382653956 382653991
    0x1e1603020d0f06021201080a022403130219080c1017150d02130c0e030309030a0f0c09110a030e070b09040b0d050111070c0906080307030809010605060d140a05 70
    0x1d00d581c00d120440c0303110303e1001d0300e80315810154080030a404e800c8040b00d03400015104007107261a0b040c500702c0503a481c240346040000303074514000c0740c04006e100e0011402c44900780011075940140d0400a02c0e890604801c041d03071102a903507699421407500398020800400303c00141d500078450b1005e4000031280e0100b455503440d08500805003203d0b4280d4006400e80f032044010f0384c40000750b204980003039500050703041554a004014000091166000e0b400801000f49a03407404a108034400d6001241112030b1011807800307130310b400140d500a040b4180b03080e444400d4220844020440803259640034170040d10307003040c2151118034500c40d007030401d54200905a50350a240d006000440340c02080300f00701d02d09940b600c5094805281d02040f4040e400600b10301002078208004018001c682403c1114504100505a0303903c92000040e05000b0000001503103410250041005014042d00b0517461308a9443d0b818040d1254200381c0505403c00f4002601359010f40c030482d03101e084c07810218405070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 382656456 1250 382655206 382655213
    0x5010e2e03061803031503050606041a030d030b09010e1005010807110a0804051305090a03030e03041706010513020a020604061d0304030804141f050307111e1603020d 73
    0x14400c404000454a400800000116100d80f080c1e546441c0724010514803060381d854020100e95005002c1c122403140884180003194001880c1e42d03110909840004a00d079102c0b1203030001101c0034080c1c5916104c0c0c1245001c4088d4103800040c100c1c3c00984030030b0503030398890f040440080342c21120310711b00d43d074100b508000940c4134020494102d5070a04140040c2102c4048980c1130844280041d125403c000400304118100080e00c1d00942c0440d40f8100000e00f4100c05150300c4e12040c01e070250401d130710784c1000314280c013050007241c00400000c900c6415000c09041d41e90785590003440791900c2000400e506031803500780c900850710030084643c0541515512036913001c00500c10315091500d80c201c800848150000108020400b0310b014100d2070f62260720300a0a00004c22400a2442c01030002c03552402c03603601081c140c00035041040c04e14586a594082084070901c2001d1035840040c8a03c0500b58045110310105899110b400da0a443c500c07a049846000c510300917220082d00300d00c006075a440403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 382657706 1250 382656456 382656511
    0xc05100c030e1c11030c04020c071503110418050a0b28090204060206060316031a06040b04062d05060a051b061801060503120d0c03060315060905010e 66
    0x310008002810180081d1941103103205401000c0758003c50138016a074491400b0000f5002c8103004440661a200e10702407481d445109912400f207185c1c85182c85404007a009810640d6281145d0f66441d8445541d07091921030004800d030701464007803400000c1f442d404014000c181d58184007070440b5007030741040b00030103c22081c140801c50300c1c52040d48000c81c8480f4280000c0c0010070081d401442070f400c02104050a080c001500007003050301480d410030000340120198a0707981158001c0c0c400c55603419000c078001c2c00c0b800056550191034582c001c2001c03c0c0300d0202c0102a40e05922041e0344850341380340c0b00c403200058056194444004d00c68a20802d01c9003005045051180220b004291004e04e40c1a01c0c01d48140c440f40d12a03034161904182880091091038020941100280207d840c3c41c00e80b05c1c0ca80c404c0080720820789803550a01e090302c0e13000f5004000150f03401403400c0c041c41c0780e0011500c000c1500340900800c40b4200b800015070020f516118600510007100c2e01070300b01000c241c907500d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 382658956 1250 382657706 382657727
    0x4030c05120f0f0c120303070f0c0807050105040606060e0414010b0c070f081e0d0c140c09101a03060315100b0a02030307270902030a09080c07030c05100c03 69
    0x75902c0788225811075010244103041404660700010801104000c0030010300c1e003089010425191300034003c00203440d41c0140b0b0346107010b20038201200c49092900704480f0912441e070300541150300744000d000c05c004440c3e01030011150f1075a9414a400e040008000542d00e0b003c0c0503d00c0c0001c2c42c00103101c0040d40740c00038015a24880101c0c0d170706a42c0c51490000300b264550000031503410102c1180c251a1451003000703d04c05c0c07818050700341d403e04014060300980e100300001e09620551076542d03500400410490010010003011100546802007032468080a54040c98085040c01040030006040304015a4060100100a44080003000c00f40b03034002e440007441c086201d41013481c00242690741000414140c001036020310750320320f8012406041d14032031000c50049042d4400b200440c40014a0006040e98070100015940e40c0324640c0c190090426030b40d015040307980000c0c5003140903000081ca03408603841000c1c04840039071344d1410002aa203420701002d002c07072445000c000000744600003914 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 382660206 1250 382658956 382658989
    0x90d080c090a030606080d0806010f09060509010504030b16020d18140a030b040b09011508030901211d0106050402131a16050a0303060e130308150411030f01090204030c05 75
    0x461403543c13912440240c2d1003c5d4010551a00030380c134100700c4142c1c80710a865100400382400480c0c41c1e24900000c1a4154a20840007086000f007260302e00303688910100c4000750f0f0451301d90381450502c0e40c024411300000c03c455002502c80e90300c0c5416543c0c0160a03115020f000d55442505940c5007030458885407844c4100c16a004240b46004000164014410303070080b802500550501e00d46504e48508403000c83e2031407002c103490000c0802c2154400030855045031030030320b0120085008002d0058072400320442910401c0c0c20003032001c0c1007012003203880300281c00a100138011240d4401c1404100d00c5011031404e000c10141c10103106401040c030260701103450340d6002c03500d480900010b9200d020310119085425400180c40d5000349641401080041d020000504d00c950800b00d42002d42c4040c003003401000d02c0425030003e00d0b286245201c01881c0007028209102c000002d008a003000e078012624402c4c81703078045001181c64181c0d4070039641a42e0f400a00300401c941000c1c1002100d00d840b07005003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 382661456 1250 382660206 382660219
    0x312281d01110f0a0807110a03020a051009030b090a05241303090902030c040e090c0603061003090c0b071502040803040b0711130507030b090f0127020c060708090d080c09 75
    0x1d428503c0410507002143d00401403603842d682c403454007480c481c00703007400f00b0b110b036242c210b05001596800030240e08582d402c5800b4000310f40b40320415038070b4007000da001a200b2031102c002c20440c18800300e510449644904282c130034030302001d005a0148810959607180484462002407818103a1101c0801014000c1c1840d503442582d900c0f07418266442120484200383e0003013020410303501c3e1310090390b400c4400304000e868001001c60102d0301c0d40c0801800e183c070500700b9100b521130642c000d070b2025100503000301440c1d0401303850321820200350b88481011202140b210084241c401e84901c03e890940c1e540c40042c1d49468984108014503800c100c1e010380b02504c00802940c0c590b980d1034109900c8455020001c9081d28200e200501243d84405005009014400401082c442001129410745080040400c5484100c007120309449040c102e2000d0307814070010348800c0380100020018800d14041c0e503003402c15520000d1441e22008603446420204d54ad8202080400005501616681102a101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 382662706 1250 382661456 382661473
    0xd0f02190b0c07060c0c120503040201020a020405150319020319050c010305180a050c0a0807050108061318081317060f090f07060809010b09010317090312281d0111 72
    0x824003241c45c1d80754000049841205850208800c00b91700d03500b01c0b5110304106003103152a800207034803590a180000e200c0d0740d44900103060b4440c00340030411006405011208100d040d40c1c1c038002d100c01d802c88141e2083c820925800c070b81800e21103803002d00551141c06004081d03007600056003d040c0c0900042a02c204014440c0c01d40d040800800010710f000d0401800c11000600a2000101c155041000719400c100300030310442e40c00101d02608144d05459191030805149031440041041c400e40c00443c2194034041414041d02d40c0c0a4902d01c3c480d000654034840d40e400341121800809c510242403500000000360012050000305076011a40e4826107014884404503a820084c60350441004a40d020060022803002442444c1220206541c0c8211a505545984180f94200380002400e1840003030070a981d0703202130052091031000c09003a551510f00114050241110b0f0491100080031402c2c404030070584a964040380304d0206240010754001c1d607500441d10052681d603c1e04c0140f003031054 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 382663956 1250 382662706 382662713
    0x19050a15090e0718090513031805030610030605092b030e060901150503010b0102030415140f040501023f070f0c1a0408030d0c17090d0f02190b0c07 65
    0x50041c4991515134583d04c02d076140303007003c29003500d1a0b049940768500d0481000417503031907030800446064043c03e04020325000c030010021100140e4120a40502890061010702d04004444030141e03841074400780f006540e100582942c848492141182c0c04800c113402c0e07039004486120351000145c240c900450411480d00701c0514089090f2806015603540c1c0c126552400c0081c0c6801010b060110002d0200201b507500003507032030080e4043c441d02c0f031400d48907200d40c007400f0751006a070702c2500000b060b4880e02c21104000c2c9a400c07a10501d07000d03000e22081240f40360140e006e600038031010a400091150b480003a403180328000c40c00f80d106283c03020401080429000140664058440c0820202517401d10850620070031035007082000c3c0d40780034003007405040303808401d0300d8039214500e10001c0c550110140440e0502d00c03003411078095806e09003c2c00711400e000b10708914203038031546074140d036448010812a6141000c80d0003100d003140d1101c0b0710b000641c0c0603034001c0c2c020003034050040c05c00c0311944 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 382665206 1250 382663956 382663979
    0x815070c1e0f140f010603050703060213090501081c0f080c09030c1309020f0a06021506040609020c0c03010c050903120901021515210c1504080102130519050a1509 72
    0x2c4207a8010b1000c407071041141c6001c00460380302d884004000d019042c81c5079507039a95415140002002c058002ca500c00c20000d04540c460f00400c00ca5505220b103503915056503455400d419465000400c40011024801d07001d81613400300000e03603640360b0456a4400c00752100c181c2003800283d500d070040d079440801a0351149400c2c1c20101d92000002001d8450744104080e00190705401401a01d01c00c0d000c000d8182c020030030710b5a4102c0c4000c1c0d10425039915000a00402841d040081c6036480820aa5042c071000074070308640a0040c0e00800c41103040d86410f65080c080c81d80d03049d5155003c0d4028804e440080340181c40703040e49c10300446054002e8500b440611100072116464107842d9146003403403510b0081802140700c105801107400d25101819825266000c90000900915404c840c0c02c0d131002245007118018101d0b07a0085407540717042030416114926910406208500b00421410f5180c2d18403e880c040301c0c0c0040824045c185003840d008103044100010500348125510b0000b01a15240e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 382666456 1250 382665206 382665233
    0x30c03070318120f0e0d2d03030e01050a09120c050111070b100509010b0a050c0c210c191214010c180503010b01050306010c0807020a03060902131401053102040815070c1e 75
    0x2c1c0c8001c41c200d4503064040d2f013144c030b006242184841c10122880e0201c0d41402c0c0c802d40c8400f480ca0310400041490614070701500d000d0748558420032002410300e040c8000c604200d4080c91901400749100f0780d43d4020130150681c01c0c05110400c010404c94060190f010307a00a0100720401003da40e8075540d000002000001e4681380b403d21100203901e6503541540900140502d244100c03802800840492041205203115025203030318442e0381850541070180c23115880c900f94030b41c00002d00581e00100f01c0241f407030080726043c513001c10140070040340b50718042c080c0e10154141a994a0300315039a8900448860413440d0301954001c8041041002503114080604040e501584001c12806210701c14403910303090302d1282040c11441c00d5100e0031401e140c4090780f41107450450304940907802c42900702c03400501c0f0090304030780e40302503042c82194811941c01510449140d9000d40344002c0b0034040300d0512410494335007001680940302040041e041c01490360460000791a0300c586103403580d44491161500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 382667706 1250 382666456 382666463
    0x1e1b0807050f25060e16030816050c040504030504050111030702030307110604081002070209071b11030c04022205010903051f0b040c03090c09060b030c03070318120f0e0d2d 76
    0x1106602e0600800c100f040e580100841b4070074045031407440c0c8606125000e007881d42c0340c900302501e845009206007040400000342008100b044542440d280c007806640c8144a0240401c203250403070a9548008010303541c04039000f4001e14600141035640c80410804d003448280d101005101c00300c0c03103280c100180c1e0b180310003103200140d44007071500402c04408001455903040000702c00841640d00e403000004d0301400c2c2d014081c4120031038540c0021707007801e01031400d0382e41146c4045040b01070450320310000d080c600072400010030745903121401151021600d000151003a8400007016108424066100c185100c83c03980006240ca4030070f001909a4a546030060002925405000e090043c1140c1030b1008000b01242000401c4c03a1858840d4a4040207200d1054541d0100c005907002d80079811900142d41c00e02000320344804140b070300c00e10030410a21081c00045207581d60586050241c8140d0140c060000d121550400701680c640c00062500f07207021071706049e900500407080c01045000c0409a11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 382668956 1250 382667706 382667711
    0x60a080a0b090115081b03010f140a0b010e09160c060905010213090e070603090f05030304050a0b0a0506010c02060a0c050708100e0a0c05131e1b0807050f2506 70
    0x24110480b0342581c000b05503200354601444000c001c00361002940b0b01e880c060788140f48000b902c0300310009005010410721480054101000080002d000c80e85207071103110030400070840350054100441d02d0601403c02107030071100000c040b800d140b0b07120f1000c4c040b0708030f549000036640b0070b25501d003800e036548003004541981d004500001247c030b404001102400100c203081140c81607440d60310f030313075541d03a8403584003030659685200e414440510700b00101940c004041301e03664240b81c50005d5661000c0b400c20b0311400b226a010409070304003401110f005201c169545000140c0c0c0da020003450340e10a041c2c00b014444041411000150300303008200042c090100508500055490403509807444104200d000750000d065a03000103615003000300c150b0310181c03100d50b08922a960003078000d000304104880350030307020203210000741c03da40c000780420f12010b4500700012401140c26501104165a003401140c000d100c88a400900503000d03244041c80c8000c142e540e05122002d890070204401001d0b641640c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 382670206 1250 382668956 382668961
    0xf021507031e0206070f0201021303050718020f070213090203011a1305010b1b16080c040e150103020609040906110702090108030a0c0602090d02040c111c1205060a080a0b 75
    0x1070b08071030580d50481010785144140b00c5102030081d12100018941e4083c810444416032a0a200b541525148940c00426090a54036414019544e0569110301d000039403080b00d00144444e2540207845240010407101030801c161a42001522450f0387d04805481c2c0d620412680942e50900520400c1808658403100310850442449030b03441d070304604021120b092500410030f00d0568402c603080e1041e024005001407402e2900301e410030960700c0740b0801c600c0c03030034a02146144000c41d4201c1010011038040054102d01c183c040e03100d0042000003122525414010005414030000a003041c2c04010800a408000340c2c0e100030448000e45d0b001c80c540e5034045944400c500f001c100f100d0161007042d000318106501c030300004180038200e4400500c1c441c2c001c0741607442c07921440181ca8426a00410900080e40400001040d4094000510120713114014074100c1c800002c81d6868406100c6550703820481121865920252070082e008980103070700f0440020314141c0074030006044900c6040c4104050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 382671456 1250 382670206 382670213
    0x418060b01020a03050414150304030206071b020f010804170403050a060e010b1c02010215010b09010909020a0e061b0d080405062805040614070903021503060f09040f021507 76
    0x5440c40e8604605551001c180000030a40213001d43d02122002241d0340c0c64074402c0030105008003030407401000c07c030318040140010103802141c4144100815691800702100a0618070008410780034040d4201a6201940d0f049522600c07006912a004100c4000761010103503200465a20503802502c450300700019820030401c039030107a9144815448020f01041c2191b0f40000c0101303645000c5200c1c0103040c03441580031079000b804855a01c00c40072001c482c2942e503560300c14900c0c3d8051541c01b80020380410010030050b149100303580ca03102c650354070030004c04061818000c036603000340311511414508142c02d11010008100d00c2201c42c1c40e40e86c420754242414640113241071009010581b095006c489004000030841c95101000c000d02000420141c9950502e117009000a000c071182c880301c60300410640761741082d103817012248241d032028034410204411041034081510859842990b00801d5a101d160844800e5042802800005416140d582c00203280303042c12000015141c1d408035806091 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 382672706 1250 382671456 382671461
    0x60e010207090203220f060c0305011404050c040b09041d0304060809031606020901050d11030106120501080c120f010204061e030509330907080105180c0d11041806 72
    0x14081c80d5410f50640c2811000706007107404007a807442180a10702c4258060280d001c6500e040320750402000c01c6981400c581c01005801d007401441c2c0b500701000c0010200317080512500344990031003030a4034103050070100c444c040740d40324009607a0720640740d12201444a24405c1c10480304800280119600c43c07901d05e001c0e100d95402800f101583c0c2040c001b1110024141a07008001c1d5400400160b45010101c01a2003900a0304510003038603103480e80c90300100c0c0e290401181a0780705900c0d50a4601d06003400482510024050791689402c0503101d040c1c02e040944040710241030070802d64042d020381400c25400c80c0c000d030f802480051030100c003030b00384070b010424031070f2601d8880d00d401e200301d01c1c01c104456564890034404c003201586038104001112003d00c0c10a55400071140d4281c0c3c1802c01004250303641070303d03005401107035280c58085180c0c048210520500c0c81c04000203000d0914500b820003c00c00031082041e5507200540104185907521403007081184d40600c54110702444540c1000002c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 382673956 1250 382672706 382672709
    0xa26030d06210b01030b040f1b050108371b0206061c050d0c060209030318030c03010510060807030b0a1517010501140f07020301021b0f061915030c060e010207 70
    0x18225a14401070700443d2074003004605403500035615821948983c60320b00a080110b00020b032003403501c24908c000f000609080e00c01110303000d0783e032151181c80d4001c880b460900d8018412141d40484004003040c0714942001810b460b822210006445070580b600102120702c401f40c94005820540410070b80740b4200c0c01d60b88a40c14280e901400c0088155900e940e184d401d032810905001310b03503441000300100b580454a100382c024003036949922140d8404811400801c1c1050310070300881c00d003000d03217060520966110324241040103422501e460409d0311070803005041c002c1019114a42545191501c1c900107008001c070301c1c1014244440c10790002d00c445141030200849141e40e00040205a07400046091981d0781d1030040b50761003a01e002c20600078810610000d40650021440440b603000d412149100107402038103030780102e004440d803251030b204200c900b8008076010348110442c4c01b0b251b502441d1500b529903041c0030030548079160220400d80652019002404030001c060055030305200410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 382675206 1250 382673956 382673999
    0x607050a080609180f1b060a05091e09040305030603011406091602100908040e100302060d0f0e0f0102180a03080d0c0c060e010203010e090c0a26030d06 67
    0x3420030125010061508070080c000c0752044040c0e80c04500c420f110740300701a43d00900380d000c50b6001020b90300d28944500d0b02454814252001c1c84180e245400c0100c2118a0081c559456503c1c000328501001042c684148005a20384031800020303025442e4150340c10f00607802a2181c40d16850010b08143c06e640c40410b000a82030003070000e00000380c8401c010b540e0050344ca1041110603100d82c0a0880c50002640104002141410219010721080e02c1c01007040d40c01c00741c50100039070383c1c4a89142580f2220b205c000d410002c10000020841b1a07907109920540c0c00c10404541e1400851a00b485e04040803c0300c1590396001644800c904d518083c841103588080d20341400080c5140c950300414011a060390910644520443e1196441100482d881540c4410100484110120440d000350000d002d86a000c80701e010200f407000340009400e001c0e9040c01041072082c241040030b40c2190585c00d1030005000071451440c00c054541c01d201624008104410000d1118541400500307214403800140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 382676456 1250 382675206 382675217
    0xf081602041a100f1814040b120307061503050a03020d1d03060105091510050405130b132a02060618040f1202030f04080606030c120a030806130c110607 67
    0x2440252550201e81c1c0b10300b505403c0c032100032001d84400b501c00e10800c40345d800120301d6105d0041240068002011407100e81036504002e081d84540a0107500c0140403000c1100358403c4c400e601c00101690000d165040d0410201000c85a990780e500d441c080c11010124056001031410507000303940b11090550601d0050070301070080060a01098640f80180561801548038400240030513100a0b810031020038003401403c00384d016100002c01e650014080c50344503046120001c2504803050090b403400c076000928044074084d504040b00020551201205007150a40f60034158614104600ca00c03220f4894000d040749240600402040b80d4841494034000c2070090107001c046002d1042448982e81c0c44000242d9841e9030070401c3c0e10350700503500c1c031614030100001c0201e041c03003002c540340d4080c6034250220f40c0c4280703280307080002c9003c4141208080741e000100110209106900141d0040c0e00600100c200381010b04d80c0700103407a030649011000c52080400380c0100b400420445130311540c9454074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 382677706 1250 382676456 382676501
    0xb01080619060b0a14040e0c070b0109060b0906070c0503030301060e040f1b050c07080616080a0c0e040b011b0804030528022e020d0e030708070e040f08160204 70
    0x1803c00d10b00450207100f00304540e4400e05c07840c075101d00742100d003c1c1c403a11055034228a018400244150300c4000c0840301115038200024403101d0a000304c50544040f10300c3c440c140310f8002c00744600d9422020050f15110b24440000070640c82c24001140030300110350b1024002200e503001d11041d100d030b200070380c40301c00c0c40d01800d0840300380c20110082c03801840d0b01e0b100350380b00100007441e4a000202d81000046018000c18806c014401da85008142003070703034a41100d9581e501c000c81c011100741140403800f00307400b19840003041c5403c0d405122840014102002103051001c0c0c01202030101e43c07003c817a01140000e0503c01d2240c20004200b000d544013030480d40341a485045841d440c424000004d019140315401325401d41c00301d52008503005042e210003000846013100007035490ac007002400c00840c20941c0343d200a400d000c50444240c4501c18002d299035881c0c4141d4000c5200001e0046c5c074080820895100094080d00040005100c000e0340ea1587c8552401042f040b2441107400d6a00030201c500c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 382678956 1250 382677706 382677719
    0x1008010b0a0803250b0c0901030e0604030903260301090911190902090d06020c0715090803031803071703100f1503053d3602070b0108061906 62
    0x44544c0d483c089401d59000303590494245146100021005003a800a14100090508160047c0a007804266418030480545000716501c5820591340603000490312030080c004550044114051070103840518000e00d402134450101c103800c20b801400d05142c5402403042070080807010072050100c119842e6554807144a04000c1c3d500c1d0754850041c1d19a00443e072881c5a9461142d444071f0641c10010035551090000540341c3c0b500d446000e244010302e150081c05050f9441101c2031000d8451910042d40781d5150a0104a03030403032541c201c0b0a6500c400c01c90030380042d4140c06414860002c000d28240c490512440903003c003105c6400040b1480540c0104018612200b00c2c48910400d407802c0020b600d0301c0d11200c201c1c5088521003000a0700b40c0000c4403140c10422a050105281d03414207451941c151501c41c100b1041500e5040e2000009618190020104103d0310140800000c03100052600e00540d896580540c0309a102d00e489400c10802c0251200d842098060034510140c4204025410402c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 382680206 1250 382678956 382678963
    0x80304060206151c110301050f1b0304050a0507060c0b071b080c070e0903090319020a031b1e0510212d06060f03050403020a031101141008010b0a08 65
    0x1c1103e02d440c600500064040e40300d0070540201c42d9541c080e000c40b032840340d050100403d8100d658050103036180c1000100c100507451504c0c0c0c05002c4010a0b0102907501d049d0302c0015800c0a041039031180101012040081c0d41008a480201010344070b41c900c1c03444504002d4030035900100640d040c030581a8189150400c0c01d1069891560301007207160b21100e1100d0228a004250f0700180c0c0703151541024000c01c0b020000c00b07091541d900301d040b00d1410303008a22100c07030241481402074108407503043c24000190021500c500c2804021034048801d541c0b00c4503c0720f1314190080740340100448030010302c20782c02c100c010010309154604050000d030210680300c4403494564070311090b030950ba0fa8a142c4d920184c0000c031103061311b58002a000d090440f0441c10004014074030807500850380410340010715500a0040b280700e16059005401c1840d09610195100710f4808520307141c6568460101950394130a03034078240201c104d1156031450b1814201c416003192151220140f00b2821110100004500003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 382681456 1250 382680206 382680211
    0x2010e0606060703271401032f0c0a230a020a090c181d0601080108030d0b04090212010c201e01060305061501080c0406050a03050c041d06030601080304060206 70
    0x54541c00c0c0c0e9000f65040c119510321038500b031400c0d1818043d41c041016600f5500d003005a401d004035900b0040b030440019400c89414541080b50500300705010b184001503003c41c03215508030030104520301440c1c01e8855003044594a4111400301d90218401660680b12051a4018142c0303001441c01000640004100440c10300c0740e20a02d0752944400882c062260f02c0108581d200700d902042c1c515281c0d5180b8a00303015401038103400c2d180c52400201c0380d61003040901d040340c2c8042c000c2c500c3c06d00414820f6001c0e00300701c01d005802c40d0f187c840007001a00c1d0b0380801d8480d40448000043c86002e42107006090454408440c000d00c01d000d0324031218200c0c040b5a4440b03100540e9880d00585000c00089405801c0961015207680a0901041524428144440241301e030903a030711081c59a482c40009141e014500035600019018070184035400d020360f1010f43c100501110050600356144007460103d00d203d03145040b224661818003d0301e06080240c24090314410f405103040c5418144001d6030340100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 382682706 1250 382681456 382681459
    0x3041118041506050604120b070f1b051504060212090111090f030c1807030b010201090c050d06060302060a020109150e0d3606110105061507050111030f0f010602010e0606 75
    0x140c1040c20122410f40c0410010580a80310756111a944d80d404c020b81c1c074000301c3c1695030b4910b420014209078810782a00b0306240c829160070002d514020003160043c1b0888604403614850800007160301580c4c4401244240d105150159071400404105c0f01c9140e0080c208500036810b08030f114202041660aa600c0d215042d03801400f910b441c0310000385010003444c0340f50f070007055054032071038002641d950540c890748007a00e0a200040c540001203088541c01c40025206420819017803282c2d1508500c8403245a01600c0003240da151a6000070b05503603c200e80380070240c2c1d903a9083d0703010407001242301070144482d104100042592185516113806540d5001c0d81003140c019810003034441070744894103200d84a20707400300c48043d09100d039210b001c009000d810045034800120800942d0140281031040710080c000380720540f6040c0c103844413070300a10808c61b60307552901c14000c010072045000d90f105108d85007501200e0308040d0f41003068a40c0c1030308504d0869041051030304665000081064008a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 382683956 1250 382682706 382682723
    0x1e080c09101502070e0c0703090b03040203060103031103130603020c150c03070e061c050f06240906070203060c030601080f040305180604050915010f0207050109090228050304111804 80
    0x1031188049041c00d40d0303600403d42106503582840305550404c0042c03c002c501c6a107600c81612b48a440c40820f0303020403100294158852801400040d101e40390042d1000d04080c00ca03402c006e41307054681200d5586821040000340d01044140c0c004804010081012400d0840500c0c6800c102d040740110740700c000c01d13000c140014070802c142e20f500d0301c1302110b02646841a04028002060138602d000d402d00780c5049091115070000b0031028501000c404103020784543d1241d040c4804e048400c3c0b900e030001001c0c10752292051200c45e02588040c40745900c280080707203205603240b400e500003408168016124151075001c0b24208800039403c4022508080c6d00c280405400f401e428002496501c03540d007009400441c003100740050710380728041e14200050240c841300c1c840728a001080b03030703210315602c0b64600003140b65104000d056055802001c412681d044084041141903400e582484440860300000400000400c1306008070f00307400080521044541d56040b0390500070510441c00007420181c503100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 382685206 1250 382683956 382683989
    0xd050702030714010902130c05031609090c0801091b0210090206090d050c1305271e030c15070503011e030b18011404050a120201061e080c0910 63
    0x60080060b103860b40c2e48200c1c0d40d484050b958203098060540c600c0100e00881c840183e48414510a0080f241304500640c1c03258110f55400704250030901c440600d40041c40f20659010440d40341070702580e2001000b0741c4412110354500360400013107481100c204007070b0011071400604059800f00341c410851104680100d1f08074403500000d01c0d01d1040c0c1801c5c0381c3c0461440402c1e01000004100808614022940d45c00b8214880d194501645c400701c0706c60040c50440d0f01880504c41626030080d0542d00319000f100e100c041000f041d000c03019012b2094258603440420300c0200e0690400803149055014200d0329a5400c110354003070024041801240103095131401ea020503043e5141c41c40d002184c000c640f0401c0c9081c003d48041c600c8100a581813801d50808107140d04002c04100711034099a4054001c0406107615207a51b40244d406c071100004554960400242c82d1070b280010900b0b101100d040da85405281034549480d1580f03d00030070b80940c5002d001c1081c00000406803c0446103141d9034200c040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 382686456 1250 382685206 382685221
    0x6040506033d06180b0406110f030301032604030b01150519091d0103050a030f09030501050f0717090a020621011202030d02030c0c061b1f05010504020f0d05 69
    0x2481e425486481051500014001c1da040c00014004440258031141600b1003800d4041340c80c0101d0380103800e4140403c010420003144160741898411240300217540034000d400c0303801c40c2598000e9000780d65580c042008522a9030b401c00700d090601041c480021314252031a03482048800051240708561425805000c0000c0d01030b00480708a00030004860491940701032014140c02041d004840c103c41d81c1c0c034040c0c21480386200c0d000341a2a01300b0001c0030031110954046a00d11040c00251040250711980000041c0c403d0140e24084ca544081c075002c02e190094004122001c2c020001482509280903c610103e021600c03040716038050f0740c0541ea030a69903083c22145010249e1044503402d400340000303014210400c101d011241300301d050350708504050b24101e0f628042c068032a98940c100f031104a10f0384c605040281840c40780c2d041d1429a06080e50103032030810912100047c0c0310310307404190a071084507511030207016100807a821824082c2e04126100c0c00c4c082c1140b5040507a55640204425 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 382687706 1250 382686456 382686511
    0x3020709091103010912030501050307050d0f170a02030903010c0509010e090402011e030f06090902060d021c1a033c0f0105040323040b030a1e020a0e0109050604050603 74
    0x1000b0020b0024400103002d440c00480348102d80505e00b001030f207024008105403902052010868200819030889001325071101c4103101402c0b43c04490110f1640460343c0c68100d52400303802003c1481c1c01031500d8030f420b1030905003994404400350040000800115229131b070800c0e18940007080590345050540e42e1440142c40d500042003c07a9400c0f44501003108000c0d03032581122058589194081c0001641c4000e2801a59030a0130000d500820920180042c000c0ca980a48045100c40540064201012201d04200d0750050004c107402d2a1076408012141802c00804400c01420b16140750911000102203150005002c4200c1c01c4481c3d02607102030076581000811700e403d0805008100c5800d141c5005880d03049621008040007008904115031035903030703800350b60460300d40990180c40e41e616110440007c1c1012000062040100c5207414104680e37440030b01007020041e11401500400c5000242030b030103044d4805c52203441b04010500403500e40c5000d0380c0e082113055090152000f0b0040300d0a02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 382688956 1250 382687706 382687733
    0x313050303090714060c03030c0f040506041202010e030609100216060e0601230108041203090515180303041505180a060c030b0103290a030f060510050d0302070909 72
    0xa4030010040c4038080700089805411188001c0380030f08051036a0b0300740300550189241d0303a82d1640060000a078254411001454000c82d40c4101e685844d848000140d86504540c100280a100d507115005c1156005400e00d6004c01d000c500504c09031804180c00b964030300f54100c0720b807d03290300032642e08072011900181968541d84014140441034840441a03501ca500348034914985810811591211401c029942c44100c410786da51081c40d55176031240e40d5032842081149003090741d9020000701041003445440c1000020b48100c60441c00d04c0c800c81152074034410720304c010319003080003804000380f10b81c80c20100c8210b0f0410007286950760010b2110b805448907640754160700520300724808000c47c55102c0460010710740c50410101101c0f000450403190080200248d0036040d0014414141030b200060310302c104001c041441c034a889603225240540d0503003040314615214001c0c03240e081c0102060130f0181a056884c040074604c10f81b0700039a100860301c1034102d140c4e0b480e91000b00b8000142551721 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 382690206 1250 382688956 382688963
    0x1050c07060e18041115070302070510200106051905130504080c060c03041b0312121503050f0d030c140703030f1e11030601050708031f030c0602100b13020313 70
    0x811078541170904482c0042075030034940c420002c0c80d00c62428000310205851000b9050f41c020028503090800b840b800c6a01e503540502030014580560101840032540c0e05640c440010000c18164034000510800b00b1141c40e400e208103d41fa641840151209149500c4c028480440440c243e151401d0111981c490302c00e40f401940100f10800084c0a281d17001507010f00c1c80750043c00b140081d0b6000c40783c10850507001c010105400d0003440116144180c02d440c8241003481800948035403201046030036509294000c0380e003504011107001d010300040c000c09034420b0103030400f41b0031420341140c02840c040900091490143e408150a802e041c0309030700006a45104540c03c000407006500010003c603024101c54030154145180140b402c44000c040d070380141c406071a11428408266100314080e00014111580d0f42a0b0310412200300111090003c011402103441480540c200107000b418140421051543c0c035040c02c000003065107806051101c044207d140040c2c407a101e424594111107034600700038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 382691456 1250 382690206 382690249
    0x1e0606051c0e2a030109020609010e040b0306100302041109010203070201050a27050405100303080c07060b0a06270f0e130609050708150f150307090c05041401050c07060e 75
    0xd00f940c03107081000126201010034000c04002c40004050036034180100c000e4001e5428480d004172540200e0514181c0f400c001c0011403400b49180211b882d04004441d580024244400104254146031081003030b00c0c0c10680c4000d25000034040043e5692213400c50090401600140210910344511242c0c00b10100f20f00456500f04103a18800c3d01c021600c0c001c10303100341c1c9400007042c4081601840d1004503507164450401035a5070101218082c0c00c210410780e4a1921810b241c9595501d866180001c2c1c517a0f03844180f1820540321103041a407043c80402c54408140007401d00940164a41d4081243c900740000400d0340d0301c2908169803001c00c3c0d440104683d00b0401c602041000c0441c0310016218444200c4514602c2951054406802070301e2401541c0a1480410760080c140259200300c8e0601900301c48040781d60f1200c07101250303000d2a00c00f00041000c40e090104028944101038041d50034640b26040c041d044003415201d8100f0302c0703a0820301104011494164031146a408100e4082d0f0030038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 382692706 1250 382691456 382691473
    0x30a0f0c0b0a0c1a060114130306110d230a0c1101051005041b0806040207030e03030a051306170a0509010f0c120534050d050702011e0606051c0e 64
    0x90310446050f0b1044440c0e10610420300c19018104000700c2c81254141d6030f0b68002c2c4040d15010309158407404022009900400700440071644a000d00d05141e40030b2508255142001d510341d038100c1d154080ca40d000d03a40e0200403090422000050203070461040e210004d1a5030031040c083d039400101c036051081075424901006481206003080f01c003100d03403d4030203012140321080e016000040c203d20391408036030b001000c902503091590142240d42e200341820204a031000703002030315603080800710314001400043c503501240d941400d200c00804003402c1203120394204a07001084440001d0603103444a6a40b000505011000d42107540c90080c0c0081c100541128580010322025492a070841c3c1c2500b001c020400120034030401d061200f00d40c210080d0180c002038a008070301c08442d420f0108003c0144400084102c2e41d21500307008501c0790b000091440711764041c5500b0105410f1001001c00d10b4850100103581c0c01c10102d648030101c40ba070f1034451041c4981070100034000808141414400c81d00c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 382693956 1250 382692706 382692727
    0xa180509010b2a100f0b090f04060b0d020f12010603080301120b012907030309020a0b1801080702030919120506090f07030222140705030a0c020c030a0f0c0b 69
    0xc299010094810f00c44500a000d41c0c40d0550000804401003544040f44902c8048503d42c890070781c4036040c04020403400c18100000341581021b0b034050400383c0a030014001080824420700803050390942c0c507407030090011f0b00090f0318107541c40f079034500070132010b002c0d022501c00a5018002039a0b124072000d85035610381c52604008500c0390400c54029141000102d8480b01b00c07100d82d501c079000d03504803c2203940740e40003079401c40d00031036011810325403580d1900005a81d0b110081d0080e00406050541b00c1c0003041080a07010982c288060500c840c07001030100c4a079020048590101c1d0030340d030248140341c44640c801c0b2403600342d6000c000d4800350b0812545c1001400300f5542e014a481404403017014200c80c8006807034000e5440000c1d13001c2044507005c0988840f80351406003145050784005080c141c140089185460f00300c8100001501c00070410403410003038403503004541c84510040001c0001107000c01d59982c81c44401a2040b00d0407180c10042012043e04800a840bc2d1028035407105081c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 382695206 1250 382693956 382693979
    0x4021201050103230f06010306020705030408030c0a0b150a14031f0507020d0807050d050a02040b1201031e0f060203090307120f0801090203190b03010f0e0606040f09080a18050901 79
    0x30824414122604c1c8105403012000a0341e06244080300080d0405134a0b699170803000f54441841212035010a000010701450144054610000e035440680800092464403a0038800000c00c041c0741020a908546402d450b100719850a4401100300e4080e9135030b50b0400645030240394a540c2c022903c00111003a86412a5041180036480d2a000c82d85000030003002503600840840c0c2400004405200c02c3c0c1445801e90000c58000040200061405440f1044501164481003941307500f000c1d81d42c010404c100e07000340420212880440c80c0181120756966802d010b03ca045005000f103a00030000c941d04000900c01c81700382076800010070303a85120200000d42030584074807a510110744500d00005001c2083d0003101e1040c2d100d5001001040e8090001c207006282d80c040d010340565807106803400074003076442180b03000611030000345083d1400e0700401058440c1e00003d85202070400c08150006802542640c3d010320a50420610384007042000c120313040da6980c4101d500c0f1041d0340c000682611203d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 382696456 1250 382695206 382695233
    0x15131e09021003060509131b03050618030307020705090405031b0d08010e130b1e0a14060609150a0c0b0a020d0e01060501090510020f2d0c060a0804021201050103 71
    0x2624000041c80c03003202c0c1503040710480c1c0f20315900200c1e1880050142c1d0580ca0480618070310406003826440f000d121400b010103443d804c1160a644050180100607480300c0340e505807100b840c0000c510394509204025111074440c4201401191481c01207803c100040c4140d8020b02c401d83c0c043c01c0c11300c81202d0000d5480300000400404107070b07080001305070b80c610340c0c0005100342e0052091101803000d0390340390790404200500e4840745003115400c2140980c0c03152010350103044020004242c01800740c2480070500d00103410284114010481e41400b07403189001e58200c048403000c500d4441e02d08040a5880000d941070092441c0082c03c1007101e0030b000c59000e040c1c0c10301003000404c0300408080106080f1a280d00607140030a2446008100310300e040383d01d00b543c000182c4155146980d0b070810480c03422459004110408020452554540b040c14001280104074800100341e0f400044000c02d020f88100c5900d841004a40e00018003076446402c148151000300030000c011942e541e082110f03a51020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 382697706 1250 382696456 382696459
    0xc0309030d051903050106050f030402030309090c03060117100627080703121d061b060103200102070b03011809082d0c070905070201180b010501020d03020315131e0902 74
    0xf8451081030a901c82e02c10705040e1002034485600d090b85180035440c154000402c00c070f901d84010448081e46880e40545940285140302050342c49003003450001d00300f1308820076044010079011003080920a260760701a000c03980c040c200744140c6100203112040210310030441360421a15540b00085044c0c0004d420011280984100c06150b8401d940c105c40c0030321040d03d111400e4442008000c0c49140c444002c0407100203600b40c00941c101c3d01000d4a0810009a2095400141c1c003080442100d4042007001c106103824400303043c41a042c01c041040303a0106010b140001c01004280010070015a4031524046822a01e20360300c0d80e80f00000e2800000c09110b0f004200d040825012030b00c1003c0101b681c40b00f40410b8040c0045506108500d002844014920003c541d21010300c688035000b0281942c4c007180c09089c560b000c940c1030030300184c83c20700e2140700c60302010301c1041080810f00b890740c221045100b080342c0e101052a41d4070380d4240a40b000308107051029483e03010021fa2121140c1c400c1c19060310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 382698956 1250 382697706 382697737
    0xf0f0c0e100e0612191a0108060103020904090602071101210b1c050607141306030f02040f03030f080f070903151b02010605010e0303030f0402090a150e150a05060a03020c0309030d05 80
    0x159801240c041e1b810304040354540e0300d894600b0050750360061010542c0100e06160060a00c0741140c0064191504a101030f00c000d98005840014404014041c1d06402028207201802261201d80400307180400c40071007820940d50344071244a41c4d01c0480c40c01d42d1036481150115011028201543c654a0944290300440c0c548040b042e258400c000c08e6800b11941c2101c42000180741c044103601403c2c000a0072250181d00300400b29903524560782030800b5501036922008030103507a8170054100c2c03401030552800420303a1010060070070750200050003541d030310401c0d01082e40f016252400103480e07004418070b190740d1040860740255505500100071070340d00b641c82c1e92540002805154891005a4a5074422194100090050300300003501a420852505000510145114031002c4071800c6030002a0000b20f44000d00c41d4000b00d039221001c005000b200c3c0c00030b40610305000108144074072a0110281600410303c4105a1010700039100602800740c00e480f500001080b00134410f50112405204044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 382700206 1250 382698956 382698991
    0x130e0f0a180b28090b090d210c170115141c02030c040f0311180609040213060515030f090313180207080a030f0f0c0e100e0612 56
    0x1404400010a0708003036821042e4840c3c200e60501c914071100340740000000c02e105040c4103485849403102c8180581c0c0e0010b014200050300a0504842003448002c02410440c2c0d030001c2007040169500e004d06c0414005059500c620007030ba100e10506500280311820b6030000100303e040c0013607050351001c2d83d5a882d0316082c4910001e8000f03000d0401c18540091001c282c0541c000107542c0155001003200600d203003842e0b6901d071040e603002c58030f800480c0c45000c448540d16480c20901c03101c4a6104005118074614504240840d03022000200007074071900b000780c0d010100052540c80710000d014040e091140c000c401c0040814103a009a442113042e0b00c011000800324000401030301d010b030340108070000501745001c42079440b42108021001d40c684c0d007045480006441d41c00108000c2d40f040e28017040f510039403c6610100e0340014410f000660a00c40d1000a003039200c04050805d0a0451319807000154981d0102c40300564006450b0700100300040301b05466410303602d03481c40b0b2101d4841110010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 382701456 1250 382700206 382700231
    0x60d09110d170a1b0506012909100c0c0f0816030f1b0816080c01090e0c031f0620070501020a150e01050705071110080a02030711030d061a040f0506130e0f0a 69
    0x12698031240820b0b14049c0b2501c2c18502d0643e80c41501e030401440c00c00301c1c1041540b51140001003652080c040302183c0401045200b0b824005111901c01d00b14611501e01d1454403801c80c3c003c098203008000c4c00546900c0340180c1c00b4407400e040580380700d400301c50281e41c0d448000780910383d541c00b51804911034600400e10540c410100301c4242c608020b2008140c3d161005148180d4202400d5442c80d4032341c0080f810004083c107180e070720050420f507a138580200f0314415000c0400c0341e01081c003e51a00712450521043c0d03000034012041a503c000c09400307d135206654007005003c076407601c44443d42880e042c403103142c3d4002c01a000d068000c080c015180c580500c00c00140034810411040801da24000090810380650301030340d03002c21582882a00e6a4590301103d04651085482c40d405560701d146c00d00210f040c150200c840c00c5241e1031424a45810300c900814101860b00c01d20340710300350024851760a82c1e1440440070050507801800d50250800c0c20341061900070807a0145180351500c035000d03440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 382702706 1250 382701456 382701509
    0x3090b391009080406110a050a110f01080103230c060307031d060123010e090103030909060602030306131d0a0b010918020f0909010605060d09110d170a1b050601 71
    0x40d0b80c0e111103a02d141501e00b0005413903144911001c944203029100c071400c0860030520268040c00d12543d10211580c03a101c040104c10091209000c2c104407004005200080e488444200c1204103402c210a410340c0544c1c51074681100300c10307032681201c00413050125480c0c064000294039450440310039244602e201801c0e984400900c201001203503110303400d807141e4090a0b060b4040400601d0050707201c14807038011444101080e0b10480004041d0102008101c40e00e02c1080c001d020b551015500d50f0818a0000b0010f0980c0088050500e94485002c0150107001011080d1001360301c094592201c02e81c2480304180f03000344507212641d420110100c04100d2440a031001c0240e004203011a00a550014030503154001000d01d07085650b42c00001c5090740d113050161880c10042400803c10700414030b003010755500c4603400140030b0020308013408002a102d60b80725100c00f01c1e10754480e4681c02d0015080b1141d58440542003428a42c900030081404130214000f8140c2d000706005291108270301025552 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 382703956 1250 382702706 382702721
    0x705030106090236011b05010203040b0115030e060c09030f061603061401020615220e010b0d020616030912030c06110307050f0702040f0222080a03090b3910 69
    0x184c0400d12070542c2d642e0360050064002517030042c000b510b03c80009070b880d10700f20b90080d10709850808162004110050105a602c19040a946001e0005034440c4c40055965400034080021458000c1806012501d040280c01e07006500038003181d00302d08061811410301c542c20000b0350300090624030301140c083c08004c4041000003040e07009205a5030340260061204c680564074540c0460b0940071010141030346206a60304060042c1300040400b003404105003118501030005000c1d40031084590003599840c1d0030303105003040b164684d10303183d5268542260080c0e815040107101803260715500080c140e0041590362090f124079010400b00d901c104640d03a40340001c030b03080c00015904000f4420381c00c110401038405544090400314244540784110b1084c3d07004444000e0030441e500000010407011061078030300902030789000d005a5490360710020300e220001d001e030400c05e0030006110601503800010100c0544050712013611204140c0300e45088540250074110410312074244540300f5003010348104070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 382705206 1250 382703956 382704037
    0xd03080411010f0e012709060518010509070c050102090a060507051615030207050c0a03112110020304020f0d06020a020d0504050607030e0310140106080a05040b040b060307050301060902 82
    0x2482a0303000344c011030780185480c03070407802c1e5008000840103460b001c05200c005402980008900c1a050070184107071074103007a0b0f815206c0e403086001000700b5140e08133000c1c0c2095842c035012660a1040c2086806403003107010f0789420400b00480013880310f52040103080214807460945810a1131304002c1485881c681c0034a0740f5480000d0013100c2c105010717900900d0300c1c2c1d1090087d0303061103880500160701e00051f503005440000c5c5103920901c01740380c407543d41c0300440c011100010002c10495600c0d0307030350605030b03688459566002020034190743d03540c04032041e80d0358002e0243d444a01c00749003d901a41000780070358054840c0e004143d09141c0900d00342e07002d440019006a05028a9490459041c0c601d2005d2a4050003a0388a103801000d00c1d0054032050b28101411813078652505c0070041001000424680100d458941403000044500030003980180e00a0314410740ca844180000e81440072507071020780e266282ca440020303c814290054540f1410070521455000d003004200280d488120400381c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 382706456 1250 382705206 382705217
    0x20d1502092805011b140307030f02030406020607030f0b0301020c0a020f0102011a0d080f0c0309030c01080112110a08160f0e07140c0304120602030f0604150303120b0d03080411010f 80
    0x10300044d4845c0780040b10094425a80115500003511a507282c0794900c807417807243d074100192321820b25401085c800c3c0c07120b15920066187c145080d9000b500c41d080034004200301a203c00c01e10740b2229090b00003070100306004000310742d29041c1c464a50b0785c2d03807240c41c0106d0103803055000c551042d40c0184220020540c40800028601c0f50340b4080224040b64404111001d120600500e403110400c040900300154559004582e26000e01d0101446c1410045004d41003000e400014403524043d2812448050b5200c030300100f10307040101c0042e1507405550005001c510030114a518044003415084084903030082c0041c40094840c0f031014919039040b6031700c0300420700903d00d240740d01e00c8110091001910031025242460740f03881c01c01c0808881904107070303100d540120a01000d813440888854020384100c404202101e442412040340550f5840301a040c001103200a1595480a4006c080000001001c000100c0c006140c0506000410b50f81a590028a0302443d45294050340100c01c1402c11074445 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 382707706 1250 382706456 382706459
    0x16020a030305090f06040803010f150c03051b030d02090405010b030f130c24080a060f0b0f04050d050604151104050913050706050309161202010804020d15020928 71
    0x81d0060000688080540d04ca0719031074400a0b10148045030095200300126940d81d454890804800c02054210001c650b184001503a403e50704080161001541401c003582ca60b1158440d941100c0c0302c03424801e90707500000860380c0b0202c034a607008140d080c4040300c01700400e0f602c80d10035110324001100d201040b000c011020605082c61261100811382c451450300d400c19854180d5042c14030382c220420100703c04041540c080321504400c809600c521600810402c081c80c106540030100704505c10581c07040d000040c1d2901c06090f07030301294042e060185c50041e112015180403940c9040840e000d403413035581c0c45800c040c1941540142008030505140e414107081c01c19040012800025140007008044c912850700041d1050203000d0080110751100ea40780d103403240e039031410000c0180c0308801c0030181403024890106403401d01c2104e150280b900900d599224800702c0d0a8481c5d40802070000f080024800c0140d022030b400805403440300f0b59280b0300d080c1880640c0e0b0210701178860064507500c4d96900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 382708956 1250 382707706 382707713
    0x30f0e0f0d0305180706022d0a0b070e04020319060803040b180109090e070e060604032102031312060c0305060d0b150a080105010509060102070e0a0b03100212070816020a 75
    0x81035801040000700030440c1150586202c4c0b42c1002c0368030003405038102041c0d484088091101d80408c072881d1010308496410f003000010f40340d40c0d40440051250b0300c1135011850051181e80203071610030024000315503d06020140a184440c6952000343c25404c008000c00e240d0b50100c16a01201c40000040b400e260ba14030903e11406a1508998100b10000c400021000ca0070700030241755500300c101911545003071030b01a9200a10003020b050044e0803c00003040001d2940b00d440c0158031021014a005020968040b421032084140c01c0c1004d8030000c80104103036081c0c3e9000007100744198402c10109400c041d007681600c3d0200c0300740d61b000d070345108003e0101e00b28103181544010410446800110200c0018508910f40d400c1040aa9501d40050000781098140c4a401c03107800d000820a540ca400070322004070000400901405445414a060980f81003014180300c6840340010740d1244000d0340003009200048540c080002c0015022401885183d180259080241d5010740504c040a85 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 382710206 1250 382708956 382708961
    0xd030c02032b140f070f02030a03021809010807170604120e01020111030901090203061b19140703030e01151a09061201270c0e010806040e010c030f0e0f0d03 69
    0x800d01031002c9041001001440030b54440c60305600300c0c072091406141085071001344071070701c010000410301c41c01200541d19150000b080e1f0b00507030010300d00903a131042c0c0b41413102d507020340004015400c071100c0c2001241b2010003081d11401d0714005e8042e044050700b10703800503070782d00e04c207440280071081882c1c548000c1310b100f415126291203042c0004160030b48052400d64541c4d00c00c440f110700300d941d01c84c142030851405103c030b981c0105185514200c405842010002544914a001c0b1801c001c0810a840400d00900c440a14a05100c692076202c0c003035418098080e14140e5441c4506528010880400a100e00d078030a090710510818401203822084103201e85038030040c0c03da94050310620238070295607145e800d402d0291441c1c50300c0c0b0300d1301000b1980070032011107000e2683c80ea690400b0200c4111540c04004040002000d123001141526810f012800601000200383c0c070079400d142c0b0a20116130550400b0441101c185810000c1046074070110b80c0f41c181a1700b9184094005048984030b10303210340c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 382711456 1250 382710206 382710247
    0x1005010c120203160309062303131509050109020a1d011e030204150f0f0e0705072301050601090b18040c051c0504020112090b1b04080109030e030d030c0203 69
    0x240100d9140401c290040410700c250013104800140c05000217100342a131004000c00c1c406541c2c035810a04881c2050010b245001c018a44001e00d10844190814802c50307020017044507e20100401401c03005007000c50103042015410b070f0050021201c0043c8200e11000e080201d0410b00c1e00200c61a4200040c0e003141c480c40714024002000d0265000c000b694540c4a41c8041001103803c08005601d4480041802c400c40c2e0b005800700c3c24588070411106c20007580c56176024107a858600c1d501c00301450040e200304421048000d801500300d140307880c071140c15840180512000d0301e540107401d030341d0151018203100d9070111100c90215100445000c0c14180c026201e01d400c103007041400c1134000c014a0203e55442c90345241603640312410b0000359604030b584260b100d151840240148030041d12a90300c10b41c405000444003120002221100e441c0920584c0d0243c204003000b40200038150500401d15000ca6141c58401d0045595051146020303100e402d02c4880650040c600313041d0103450040103420314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 382712706 1250 382711456 382711493
    0x150306040903020106150804200d03081009020c010212061917030c03030907180c050313020a05040606050d05060409050c010c03021c0c0519031d0f060a0f081005010c 73
    0x8178000031452220381e002d01c2801e046507903200740051819082425040300e207441c24441002450000c04002d450706007258402a0301070502100c070b9240e2440c41003506441c0d511150b000e03440820104420708064008110401110320f03040c240d511204100012424118080541154800030400c400305962401c3d440414490042d6800e0001c2c0301d0040e811a4011a8003040d2074000c0304007444802202029242a0795103158104070300ca024400c084c16900c4003500088060701d5400c0d1000071075450780c074030401501010307009101140e0b49182c00740190300a18280c000c41810840081d000b42014803800074401e0b000001030044420303032401074840c6c440c2e0a5095085015900b005603580441c04944044410b4660f600043c0c82401c0c2840c45c1081c014640019044150f100e01001003076100407072205100303101c504010134800c0c07800060001c0d6800010641c0040000c6003808075142c01c8118171210b6415921a44150703a5407000c0e114100d950341c0651804107100100c41d0001c2501101780700070b20b81c02c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 382713956 1250 382712706 382712711
    0xe0415030209131202030c060f09010207240b010c0f1103160f0617040308011505070b0a091412070314040306150602011a0105041701060f180b1503060409030201 71
    0xc8075000700e04040c40883c0c00ca802e8000303060f846001c000d0182200c100c50300d1244050350170401c012081549400b0050100b21110002101146521500f075040341c8010760302101d2a5442c401400c5000500e01064807480d090618080f14200c4079405803010b485400e500c406200520105591228880c15103d40540c1c0c1511581c07201403008000355040030003030150304400e0401507290510042a508220402420810440d030600c0002900603d489040d10829035521040788051341045400703008419003e025030380c0c000207000f04441c0580c4001403403400340e9901f5458000c2c40d10020781d10502041d0004411004000d1880441d11401b41e4080c421f043c4000da0345021f81d1381d1136482c1907480901000d03a240100000400002e1307024850007035150a03021442c100f5000c48000030340b040c002c80c0320350810181351624610995500b91300c058040c00c26041161600d54a07000c01a904581150044960610f401c561000ea803904414184000070600c0080d851690b0b0175080c0070240941302c40c201c09564 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 382715206 1250 382713956 382713959
    0x5120c0909040602072003031801050f04030c180b03030a08070504090c0e040b01090f0e0907030c170d080114130609060603020c070e060901033903031e0e0415 70
    0x15541d0224a001c0c5002d80c03409a21083d8904003160760249041d0410724a070228004072129403004010744010702c60380b41e0b07800d402801000041e1020710540d00121500c10001601204011561719031070143c3d220070a41e9110b010712510101c04589400310110380c1a030044c424280828411826240d00c010186001800d0542c0d551105082d03801c0d82e146900440c0d4074894513007003070406100701c081e5031009281c1046110300e01310920140400501030000141d24040005410800c1003107444010365010000c0041150340b8543c9500d50340400020030003900800311a08061441200e00505036210100203420403240103080041c9440d0040c2c6480c3d100f9203500300002e9506640c80340500070400c6860150b5125071a404003400c04005400400d0212000d4003813110a480303540c04035040d01e502455407a84010f0581d40c5036a4466038018130281c000c4041d02e01000c4072854040c1c0c0040b03e1094030740c141301d6124105a40640141ca5403c030000441c0ba820303441c9036203400e81184185034400120000e803036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 382716456 1250 382715206 382715209
    0x102031911031903181203090614011e0609081902120709020d0b06070b01030b0402120601060e131e0c1211090901080303070203070f11091003030806010507020105120c09 75
    0x180c000d004001c0218110181d56810a81c06010314150042030b940b0190f141e860503524203182031b090307010182c20159210340c2d620404c01075074442c05040e400c541c0c20b44255a0b440280d540d003000c00507401c0b201c0c2110400000b07078440c002c00e0a8000c1e10030b0080a0f00e06884180b920440c011510142a43e019444041c401480103092190344041c142610001d030b5556506490003080e20000c908130b0303000301010031420000c03801115095055a6102c5d1000d41c00b500e0f58000a09140c1140e0241241030090b0000020590b410641c3c3c14001d5000b44e0710841803400e6403084030112580c0a411244c004040341515588000d140d10100e20310586040580141100b002c801c01150303250941842c0307040001a000d092480c1104805004200c0c00004610b94a00028029102d014520005003200d151088420410500c580e40c1500d020010703189118502d0041d4007402c1600b4035100640115074030a02080480d407080b811256803131740603101c081c81c00c8481041d503510800300601c1910b0304401803004070ba55 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 382717706 1250 382716456 382716463
    0x40807120305070f210203070c02060414100c0f020121020f09120f0a140304090e0109122a1103060c0a090b13270c11010e0c0102031911 60
    0x110400d90340c0020341440e00880103000c103008400b1450501c280c1c440c10f80c003240151403040c02110103003c030244e103035161000261050383d0305000081d4040c038082130100f1180c160b12030b925034030002180d400c02e106d1425a4141c070000c000007006800c10a1440c10341c40554003c13018010403111200309068881b03904009102203811401b105000044001030840301807074400d81509400c04100c010b0300c80c5854800500780d07540444500148000e000c101f0440e0840400c1c8141c3e801006590012f01030b11400400a41c001c05004d40104c0303080e40040318207000c56100760230030101c09074003100303c03050141800502c901c14405c075a01107803903001c901c82c8980a07460510072705004001c050301440c0c07100f401c240040d04002460b0002d42c0701070b9040c0b02201c40e103890301d006a000c46986510a81e04801c1801072402000c2d00d000d080030b096824007146c01103450384000ba007011001306a000300f00c40c0c00c443d000962199182030000340180d1043c4801c801c0c801020301135645c41d845ea030902a2261041d001280c0c203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 382718956 1250 382717706 382717733
    0x1b030c0f05061003020108100b040608090106030f1a0a0605011413030c12030215190e0118081e03060d060b1f090914061809010b06070b0403031d07050405040807 71
    0x401206103001013046503003240a040e0000304000e0701060079414916111601d0103940300e40c400308404140070420840b400c1d400b01c2c000e503812205442028089040c51a4000c64009003055115008400154a40e00c1071140b10283c2e0740503075031528404211410b410203a0421520111403903001c1c400000021f030588805001014640022070b500c214904000c0d040c8240c1003502c4070045582c2040000030040100c042054466403900056914500400140180b0b03402c0e131031005445e030554a0806106144016044100d144420991042100110300215000a640042c6c1141a80e03a18500142003600300c0d0083d071002601601400710f0031042887c407070400d1600031000c24030041081c00b4400759402078030b100317003254082c580960070310310045201070310a000f0414034050004081541048290032491007008000e20342500c55110f8103040313884920030740341200400e24050016113042c2d4a545921a0031400c1005070800307911745000c2c8805000c0c018011189540200704103400114003000201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 382720206 1250 382718956 382718971
    0x60a0908010501081b010207061e26150402070506010b07061107030503090606150712020c130608060121080904021902030901090e061e150403050d08071b030c0f0506 73
    0x140265801410184083d1984905c40c11500494030511120b03800055035501c5034910850501030000c040d4040f615600c4c203000c01d44040030329102d1109082c2c03410700201e0013a4402c043e407142c401d41902c2000100c0c4681c03d401015034110000410030354600034087c01000b4002d44000c1000e10320b007030a11560380e02c640e4084010030004400c0c000500c04c200305641d0f200384107540c4800b08030b01800c0481524010007e004088000c103200c49001607109100e00ca0105101a107400c40b0301c084004020040e1401d800303100300c07500c01c54000259442c1c650080016421880b07241790255586030f200c0e441140e120f00480e0740c10980800070925901d841c2c448000ea041440d9000e035440d0b400302c2d800105490000e03031100c90515104028408039583d81901190451102c50758903405401c08400310b00e04008184902100403030110b400000e000300071446480300c00d26541c2d0800c0c00c0d03070f602805884444803c1d8202c0100482d00c0410030000c0c0c01a80440307000c03802000ca150b00340074030743d0702c0c039107090011904071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 382721456 1250 382720206 382720213
    0x1508030a080a090309030f030905040501080c1915120209030d09050f010804080f0d0603020904050610080316060e100e070f171c0c210e040911060a090801050108 71
    0x11114640e01000164200503245024009111a600d004203001700900000e090525403450303407001c1500401c103090042a01900074403003503a44035800e640715100c1410460089003800c40110000600c0310001054841c02ca0444401000090003103030404540440880880da003080342c41681d079010414441c0c105030643e6403030b03a640d00b408280030301c5142c1780d011503052060b032505010000300c1120640e490307882c2400846894040008414014000c00d5202039003212500c070601c0103000c07000c00e41900c100c0b80c1c0c14025840940d0f4140081d80d0b44202c0303005500940c8020824400954140c01142c1c20030000000c8a4500701c0808181e4212010042c0040e49a44a180100614074030300c0e042400a080900b030010304030a203202101d44520020309a0030300c80030420441c8101e50b0241c7c2c45150366940151421440c3c2c4404803001d50400000021000850700c0c40703500308103e00e000d019102c5025408940030000c3c0b4022814050a5000150304809100c4206000300d250b08091007040e000b4079408004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 382722706 1250 382721456 382721467
    0xc120201050c01290315060415170a02090601080c0307030f270b07021b0913080c0105010509061002030d0509120a030f110702060703081905151f140d150803 69
    0x104080f40744044c00180660001c480507145042c030b880503594801c030b06640100c0d09100c01e2101d8048081d854005514072001da502072620340d480003501d42003242c42580e428404d80c031400700548003460708840080506104000094906102e42c02510b40c51203224070109c0c03243e000b103268602d0601d100d0f000700618a6001503840c00e010303820081c0741e00203055002a00c00c44003c000303080c0301e222401081c1406100c0d030001061002422601d4490310f96046010b0507101d01456820324080d040a12585224500c1d400110711280351528200b5030000981d0010344c42c7c91103003a242d102400c1c0040105096014292284200d0a401001014540881c0e034000880b520b00600c10400c0700c9098590b030164510500081c40161144812944807030b815040415035951402c070318440603100d1a414000c03080c1054180803078003072808101284124101c8918801f07400f2000c1d4000340c1583e0025400c001281910000ca070351081600030242e00204040110b42078101045e4640901305a45c003103072a69200140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 382723956 1250 382722706 382722761
    0xe040905060603100b030a111201150905060901120b18060a14091207080c0709060b0304061404021e0a0509011d010803130b0a03020c120c190c120201050c01 69
    0x4440342c00d009404c104a05482803021076650380c0480d0f13005010300c00921901c40c003559041c0200310300e480c0b090f0090100d0805242e681914000a1081040307160034280419024542400d64906a45251800703105a1007503407502034401c2d402030300306019070f000f010866102c0001448524402d04810f5808104c040d148580340000307000051649059411140c030308035004103104122079013141c1000c2030648411f50036590504140c1150302c0001028545500060800e5902d8090762049005d08410010420440d0b5a6008000d040f14000e500041040b0101c04414826140c6034590700c1c003500300a00c1d039441da004030720642803e8028640121400064580210110410070301506403007028604061741e408803400c0d04141da006403103038040301042c21803c0714031070742c1525148070011049070002c40603a8103102055003c1081501c0038029005071500c03401d04e06407156002540184000305041c0307021510444104034607000ca0400000b04015103052500f4062107400e0807030380c0c4901c0c950f0303c00a81d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 382725206 1250 382723956 382723963
    0x40c02010e0f0703020f060c120315011e09090f02040e041b05010203040e07231201030203010c050909060f010309050312010f0504110d0906020f0f120c030f010311010e040905060603 80
    0x402065042e48652018070051b1611001c0c0c1c118040241c076150346070038070200464100303140c039280404002404030802c02480d040405c42e6010f020b00380c980c0445902e11018034807954005144050103d076165404000c0904958041c0000381c011030001418a52503c600c1800e002741600c082c0c40d54070b0310b46a43c40400d210b00469100510090004500d418a0709410b088001e42c010044c4050054180d5040c11980000001000305455900c2040d40c8060301000b10b0320b41074086c00103900035841c0c0300c591840d042c060710856070240c4001706141030954501041205501417034803401d04050702c8540c4540040e40400c090a08504ce101443e900b03036050880d225081d15099020304e200e141010b000300c1041c40302c0740446a40f0060710b9404500c00341281011406849146000c10070a200010002c100301740c580080c0c44d9100303a91046850704d031605080d220f01400256810024140b20200400c006005c4511000740c420040c14021034143c1c0300c200003000c41d012803000340c4854000740c081110074602071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 382726456 1250 382725206 382725223
    0xc06021c0203041103061b0d1515090b0c0a020405060d06140f0c1306030504111504080f15010e07110d11060702062a040e010b0903070e070804030e060702040c02010e 73
    0x217a004017081d00e0012900e002c85110b03400450801240014140445d8000d608071240360285d5030300f807242e81070780d920042c04561400300f00840010304410001c580601e0b080125808445000004c0c09106030540030400148805804e0650019003000d1038800a13141d4029403c12609802d0024014503101c1ca500c05006001030041c00c00031410012450381490750392103a0f007600c1c16443c0018a690b560324221701c0d00102c010749603a020003040b03451781a0b21b19280040003130740d903e14140c1d0407000c0503025881d56203c2810101e0810111040184140b410050210390301071424540ba46c220240d07003250038240458940000006840302100d080702c1101005919040000c2d8401402145012060415100d00e14090706004240c3d504095506403140810340f005000804550350351943e42d54102221944403001c01c038081d0098440c00141040c0c02c40d4814400c004989a110140d6220b0364115409840c00700d0042e070226041c0702c6c000158a030f510620a6511058000042d2041008801c5203000801c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 382727706 1250 382726456 382726459
    0x12070c120302070b150303090d0c09140103020a0b0906040b040602010f06140d1203020909090106050117070e0d02010908030706060911040f09020307020f1b101d010c06021c02030411 80
    0x10894600090013110583c1d62016680440741c000710b0141d00082d00b14440c1c588003d502c118100c94600501c60350b0104c1404842c58031500300174000c0d0700601e001344238a0910000c1d42c410800b9400304480750580000b840300a030010003c0340340c5a101e00005005405c0794203c4030050795104e000d11407d185030311a40002d03050b01c4c2021101c1003500400102d88144d29040100708500c120741c00c50105010350107a60407918001e141ca03000e407a0140c241402440e8034401c042c001442011188640140c030b14480d80624110364401c444101590103104280103452812070411000180c0010f820700e050000e0b04005200d403101154062401c0144d07815646c602d85d40c60482d403820001001408034040d0041d04a4144e01005a22a03687ca8016800c1606848095070140102041014801c1d10034110300b445550840d01c0e0104008401011a25080d240c0b00c02c2041086910107240c2c03542c080d02c43c6034506846810301618113001a40070320f14409081150000981d000300c11b000c00c10143c1030140ca4600310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 382728956 1250 382727706 382727711
    0x3b09060412030b0f0409060204053d08040b060a03020402190f0302160213200d151505030907031b0f21081305040218040e0105190c020312070c1203 65
    0x540000502d48804c0030b6006031085075540707161000c00000c0e4054500805000305010b56881d1982104008038000c00d42c80083c00031410041e401d07940e03010700c1003403078007141e42c1d04d051596480350740e4501500d41c06408240c1c4003d01c2c07000080184d03160300007400c0360010180101c00c11121410013618080d1103005e1002414014020300500c1d010044400d1081501254601190460303030400c8401860b140a610649840c0900c0302403120994100030f212000c84d00000704010440100c0010101005010344a0b0000920300d2403045140b143c00911740009020040c1d40301c440c1d40340d950000c80d40d0480d58403200103800001c2042000000f0404a00500403019400c4840292000d03031039152105040041440b0400308145403c5501844550003508001e0000c40d0b80b40c290062040c82c081c002680d50384120b007401039800b601c2e04180103213405101e14a010f965600b402d803900c240039201c41e94500d02184424040d0180c1c8400c030301c0200d401518281c880d0703090f5294505000c070240740003141010030b060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 382730206 1250 382728956 382728971
    0x9060b030c100f0f050c0a0525031a043906050c0c060a050c06010605030114030c01021e0c0d390302210607110d0201063b0906041203 59
    0x190405141c440c0f040c12031420a01c1c0c0035041c0b20649150040081c03010440c4078105800c4204040080e2900e01c0c1d0070645900082056061940211684136000080244401010f815500c0b0b0803a00310300e0f00a44600c0011b00f0088a0403510200091503c80903001c0d0200c544880010a2800c0c40c020081c0c0a10700c0e19030b1402c00b0101005680d11880f94074940910307000034100c18510320032415078510729203500545499594909008000750400c1c0241e6502d66540c09585406107000030324284400c40680141001108022801440821520040311280220007030044070f5075400400d907518906c11580b03141403c8080000c50b03140030982883c4650144090319040c4030035481688501101d60454103c00e44542403880d4040d0141030700d1071502c481c8261010300160315080000c2c0c0102d0320381e69084555442070030300220f0070b0740d0b52442102c05448060082c1c980c7c1e01c0c401e54401c000c20500c51801070188445045041c0b08100450320003070241c002d00d0600c800c0006401c40e000560042c0c1c0340900c601f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 382731456 1250 382730206 382730239
    0x70e040c05030103020d02061317010c030b01020c0d140109050102030f1e011509030c1202040b060901050a0c06140403170f0c0a03020d060e01260a030c080d0e0109060b030c 76
    0x14401130001034800c2c907003030054100f1035888104407500d540c1103016000c05a903a48090b1818a42038440f000550750074000f94203009031103071103014402d2405030300400055040c40c1c1440410403000600b82c44210803032200c000600340900603802c0151140740016030700d140040b98500c014202508903036142c0c825407a607802e2541400500ca0648100401c2d005014001c154140c4598089031300040808041000c0000c02e800c0d0300c5598400d060007504c0601040c14103404000c458811900712a010401c24002d00f4081441070114160140c8100b500045040410b041c0070200d0008032130880000300f01514600000c1059103070700303070010003000c00b90200d81080d51100e22180950b00d4031104259001c07484550300101c07508120001d0030742c1c3c011a422541c44004141c02415400c0a03200341070703040d15a102c500440001c1c8816000d41556a00402c4180c2d5524288158003000c3d400722003035220541461219428440d0050043c8280c000080e03244018061600f0506070340000e034031400c00c0c42541820b8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 382732706 1250 382731456 382731467
    0x2160e0115050d0c030605030d141902070305060a0b0a170304050906180106020322081002090a080d1e0503092d03030c04030c0f0b0708090604090504050105070e040c 73
    0x103444007980c11039100c400c540021079890243e100961903440c185001c40c48010303055032050082d5041941628111507001400b03481c034101d654040d000369242001815804060901c0c0002034400034410344011660f203807184c903d0190181c9146000d180d880c50502000c0c030301042c0d500014000c200191101b94500c41840e44c40f80500d1003403078042e012a500181d85580e0b252141442ea0003039010f085065612580003e6885e0410822002000740f4100b0121140429505203000c41d25030100400b900d2411103005400f0303400040c0300f01c0d041014114040b809000c180034009455a581c0c2c0d42000581d001c00c03511414019003441c0005210007041405074103e0045100e54940b000e110b00403442c000c21030342075151074030390600310001c0c0d010200500280c80440001002240d00401d140e00300300c0c0d1a210701c5800030f01503110780410030704100b05403400900c03658090000300d50020003c50030030b65652014010348108840441d100e0350b41d0410030408903044411600f20700416107003041000c440f910084d10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 382733812 1106 382732706 382732709
    0xa1404050c150403020904170714010e19020108072f011d190b1905041115130b0f0706090c170a02010f05220f0602160e01 54
    0x1c03810800d8140c40581707400030041c1565846540d030303054110090a69045049900307000750400f0859003800f80b030000d4074035000801c0950f2a00d00302410700000341b0b02c03101d1010000b5070001c0941d038820769151740034489003003100c8030301c0080c04c204020303802009801444031005003620841c4e1f10b041d001600c1c1c0c11200812401c2c03d06000701800d45a19100e079040a0b0320030a501d110011502e1400c006802c0780817075404169001202198101350f8a04039001e40c0c000000c550144085e0601c20ac00b071071405554018241446080d292a0303c1683c2c1501c2000561400852039104912481d4211141254408800c02000289241c04842114240310300e090001c49501011004900401c1c081c0b9a603a050303407110701c4d15064000c11b84642e080031300030480e5040c00740c01c00301785074452503079210280c146000c50405c542e15002d0300034a4000c2d180c29038142c61055074030802946100365001030 = true := by decide +kernel

theorem cover : BRFrame.Cov 382553956 382733812 := by
  have h0 := BRFrame.cov_init 382553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 382553956 ≤ n) (h2 : n < 382733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
