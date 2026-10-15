-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5042
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:33:08.768224+00:00
-- url     : https://prove2.me/submissions/ed707d47-3e15-4b39-a1ba-f412c99f10b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 906654676 ≤ n < 906834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 906655926 1250 906654676 906654691
    0x80c0f18040b091003170405030f011d0304030b0c09030102250203122107090b070f021003060302030303130312020304110f01080c090607020307080102210108150f1e 73
    0x322081000d82048199500d2400c8540521804020003124074280d10709602203d0308980b2001d1289203d140e814a82d1040da0449501407060001100302200c055000b4a544202800c0c0385491220400507640c40b0301c180d02c400303000b100d6204049003c0031104c4008240444d0020001442c3c500c20508880711100c4110700d107814003d2400c80301c17040d0309091007407501c807124110b1668641803001800811800f410900c0302081e0808000003018140509030070740c050407444d1182c5880b01c10a20b01000c00c02003245089015a00e41006480914041d02404060340d90050281d41035994482c040c0400c0c5410302402e408200301c0504644150903c0d10040d03018034010251403400340720000c02c1c050300c1c8400c018410704000e4508100100d00520105232601c10a088842c190790303a40900000e81f500f08190841300165100041d100520f00e01d820380d01807180a50b101d41c801582e0f94601250b01e4071882c40c9180d000504500c001501c000023103451650040141d103204a20f6001120312195400c4100c8035031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 906657176 1250 906655926 906655957
    0xe010603061806200a0c051608100608120403080d0b090114040b032b1107140307090603033f02220f0e07050d020a05090f060a0f080c0f 60
    0x90b828801c0900461800034002d8240c015880b00311410100079210f0000d0460400083c180d03902c04000c0d0030701c20541c0049480405004540e103c243c4284c40c0c03031401151042d001d103003801c0019046808600e081003610300c018010704251071034031190b200741e000301058080c50303503a0580d800c0b042c2d03560034149001c3c1400c5002809000101c0d401c0c4821a10306a2143c2d119910420700c11180811004181c0720382404192480a014480d0701c1c00e480c01403100d80c0210a5016040010a40c00d05a5564004031a011000c5070f540aa60304a88000c550040c000500040d5916000203480d0000c8203140445031822811400c0012007640c0706200ca04142c2416416a500010310000d070f0740300342000039199500314016050749403804c106c00d03603100d520b485420031030704001000402d66405070082c0c1d10b14952020056644002c2041e00401a6008859141c40742084c0740c030740300c81c0c2e00304603064805107075075a201d40200f0741c000b02055800c5000113044d094807130307800c0041e42820080f800141c2684400c29221 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 906658426 1250 906657176 906657221
    0x40602130b0d02090a08010218060c011d010203100e07170c0403080d060501120b0a2d1512020f1206031f0906230414010603021c03020f0c01120e01060306 68
    0x170490300d040c0a52010f0b82c16801409124039400c0092002d52555000321883e0f40c1d00d01c2106680c50150503102071740800840000c418402240301034004500c80d03a000100d9509040d122180080400c106442101c000b4110114010407607506114164011802c4000c041c140b9a4995444441d948002035040015490341070400155800021102e03402016504c244031004245010400e074600a100e400300101034103e4504101c408800fa842c800030140001013501911075a03298a00705a24a0500c00640b02169803806071205100761115011243d0540e441c11156000001109001504155050013462110342204882c543c0400080e40188008164032856041400445079076001e08403a03000102103502c603c21314800f81c558000e81c020a030600c0a920304003124014166900003e4002c4200f5854840d00c548403c9907080e0b0501c65400c40e0025a4040c0415896001d40c00105c2c1c08545292a880d900750890b0700100213440c501e000024196030799485880a6070b801004c02100042c00750032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 906659676 1250 906658426 906658429
    0x120504020f060a23041203050f1326030f040e07020c040e0d030b120604021915090e0a0c021b1302040f080d11070324050a0f0c031103040602130b0d0209 67
    0x100b4132011100c141c612410107181c144443e0f800c01000700b0003000c03c2800600b890501440c1307001d80d4200c20520309076500b050f1316004018618030024591032080b106e10514501081400400c88080804070003010341007502d801030740b50300c0d0340e03001c2d00b07040660150b9410032690303441310311820058100f580e000b028402d88560300a011604115000c07805031101143c50649980300184080d001035043d55a0f1066040c00c183c4100c240303109400104244081d500d003469066480105041074400d400810030581c0c0310f0003001401c5880140000c1d000d0b820aa42d60302081c2d501c0706082c0900c600103131404003030751102d402c180202c2e0300c99000548000190001400302e40d00800c510200c0e100a4248180a0300d044000716a0310400b5110050904054110006002c42034884501030150f660703405103c0c90a01100c0500500709080d108800141f8090a104000e4840d0165180758206001c01d50700c0c5840d26192140603600801144d04402102180090b90780844001025805040e40006840e01e81020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 906660926 1250 906659676 906659717
    0x91012020d050a02090a05151c140f0a05070303030c1704030809030909250f080c03041a040c05040e1b0f060c0717060f250e0d0b0915010303120504020f060a 69
    0x71100c0c016822a895007494107003140c0c3c1c0030340c00c2d0b4010ba060a4052b0052030402d00d0024035a001c2642806004100c1c0104000060311b001aa44030b510b0a0000d030100c00d500300c48028103880d01c002c03030000c2c2d8004200031902801c59240c21150305401e4900c0c0c400c07a88040b890080082d52070801803103520568100ca0b10124103205480d154078500380c1c0640e009154014811000a000b00d00305020010118007081950003401c0b0a58403102c082c40349034941820001e180d540c1c0c0e84500c41c000c60414000b524200d20100b080145143d55040421503035000c0d1060080c028800d40143e41c0010b01040f10142c00e020410404008013110b10865200d51481d142441c00e1a201420b0440100300030401c1c004403203c441d03903129140c2a10182d074442d03444400003c85480c56440e00f43e0340c0105110140d1014003a560070b90510a00100048a11203c006a040b03074000001f4880607000940302898010400c5513900041c0d00076000801c07072841c0000e44e00019a859001d040f040004c502c4d10804079014101c0b08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 906662176 1250 906660926 906660961
    0xe06070804030b1e15010c02041b12150b070c03170a02010c0504030c140406031202280b0c0310050405180c0114030a0905100603060b091012020d050a02090a05 70
    0x60749080340e80304c840060360010015010420701050081040a00e9110300c10b51802c154008109001c02e00450a40501100404403400700003074820a82000c00c0003140200f0959855842148400a1074010b1442140c0c0060fa0220b80c004440d81c1c00001082c14001a10b42c030b000c44000b0741d030307a9000f140c10180c00c685205850b40d05010701440200b0104840c000208202c40b40c101100a84007445030025006060b03640006140300040d0007001c030310650004011504040a0003e00106140921400c1c28000e60800061504412500040009009901071a080066042020704190b03d46000900343c8400f2500a150507040c45905110700c0340030418484502003c0c2000f400b8a5a041078a909510000b80500d088549a0340d81d64100802000810034901180c101004055101e2800030060b01c05024294806c0c0c1e007990104552420201c01142211241c1074510b403180040d90a10080c189282d01c16901d0340584035074007000d0b840700301d07090303126038245030b00007800f441c01407141380d04803980 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 906663426 1250 906662176 906662191
    0x912010c0f1701030809040b041401050102071a03010b070c0b0c0c0a05060a090e0603070f0e1806010e070309061e0b040f0606080c09030a0f1a01150e0d030e06070804030b 75
    0x451080e50203070010764400c18190b80c1c0283c1c1c0181d1b1441d01c032000c036029026200e0256009031030b081052025207489040c050588078242d00307a03854240c1d5040d280700091186950041084800c00c0108540d070b1401c03004005c158895444c0c00c6145540d4030240386103803c281040d007c80e810034121000d56143c01350030078010b030004a6001d414201b01140090181c6014040d03d600b004140d0b0106103946d60402288004050b290018191640c90340407680c2011000c1d15242034084145840321070b803d2011070b455058030180d075070700c002a682c1d11004801819807190250f800715901c04040c030311005149611140050f4100c1c0208501c0180c005000c2186d2040c01080070740d80c0381c41c00c140305103030380800b0035600a844c141c0400c2e00d071500480041c4c2400b0760060010003440b028482d5900300185080c0b60386504885c07009460040c1e0f80d03201414040124819503100095010842d5429450704000e0403500c1303400b03458480f0104000d000401c48a601c5490140d4150f900442c0030001c102c5c400c0c00303090b40800c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 906664676 1250 906663426 906663437
    0xc06080109090f060f020c01020a030e0610060c0f260306190f141504060c0b0a05100b0a0e0a14150906040e0403030e06040b04030206060f030717030912010c0f 70
    0x5441e11883c02104a0490013842d2503140c3c4500e072a0600141c040c0e903c0102900000c65845016990140c01002d0155500034203004040001c0c40001c41000300c0c104841c11515100d070f0350301e460703a10303000841a668000c07580c58015181c85000c41503c0002c402d034254100c0c0156680e400d10000700801151094811039151031080e070203001e0714140005980481d03440c2c8030090103403610302e80080c0803800d000340301400062010500207401c603030094110f100030f4042c924001240e117401004009a41c1c044130900089003e8120030030504081310001d0031507140d02c0c684518200788038000150701d4403296000d01c071221400d001102c8186021000045425680d913030543ca044503a10201d05076001d24814103000310740c0c150000341850f0181e04510602080309043d900076203002c0c40e0503e04008140c038203400512559000401c141001100fa078000103004000b800703043c1c035012191302c13400d0045001d50f609001c00e010030501074840300c5036441880050b4002042101e07420000404c01c1c14411010010400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 906665926 1250 906664676 906664691
    0x60a050c091009180b091005090f04020d051b030d02060f01050111070803070b1e04020906040f1508030417030a0921140d0306120506270a0c06080109 66
    0x1003255007141e810305002e403100529901080800c0e165404107034803103403500d215400180300201c2954000100e1070001c5501a02c5610f40108140800c82d0b40d00902d03802040381d00104601c0355455459903406032009007941892a010b0761014100400c1c1482031106001081003030308113190601010340d03441c0c0540300411305440d000310400c0702c401040c443e26050103206003151001540034000c8501800c8244100d942d00c844c04e2a0a203007010049401400080f00c07200c0d0b5285444000122034017440d00105206a06d40b6450104002000f043c2014080d4955414071400750300080c0c0d09110081c420310000d56103603403034052000440011000b008641381c0080003615407079074014021109a0701d0707264017140c000a851051103800991070b40c02402c00782d8002000c40e540c590019070629600d03640c0e038051202c29510604c0c540d00c0404810010100e400010009a403002c14198007040010b10b603403002c0041b10005030351402c0c2070f1414810788070540030010601c0205d0700a0105801407885075000c00c1100c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 906667176 1250 906665926 906665941
    0x1b021b01140304140d0e010e0f0d024501080601031203021c180311030310330503010e1015050919060309060518030901050a170703060503060a05 64
    0x501d040c00c40d452a912020011405000d00b9044101c01d10a480703003140c9103c00100c030003030040455075540038001000c601c5803824a05000d81d600d00105030281091044401c15030803c0340e520845084880001043d181103444414400c1c1d00300b82c0c074285040506003a181e407240414007642d0503000280c29610080c01040012554403594100c10031518005848803440705103080c000d030310064010591410251141914043c00808058140c843d4131200c051000780c0034000e48901040b41d0002a000c00340c0400c1042d105030050000070000b0208144090035815000c039203480d0080c10400d800500d01000501c40c5248001216401c0540c0000340c0522a1401d100154084141c0c00201c0400c9004a070003081521185901e40701c85450382c00e036080c0641c40340002402070210308019540070f4101000309940d00500880c04d400d0b0141180170f10306c2c20140d40015145035102c0c8403450104800090702607001c0042400340fa00414090b07801040b102d240c8030800d41b6100f000b0300000b00151400040c004a03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 906668426 1250 906667176 906667187
    0x6060504031e1212060905040b01051f0f050c010603061104181e0b0102011b120b060708090d0804030804080a110f210304171e1209041d011b021b01 65
    0x1c40d182032403c04d2a402c0e80001002c0900100d50000202c6070070882408204003e0f010b600d41a50700560b00b8265402c661000f070b4141002c51381c103080204601c00c407048030f000d1044009007044840d02e0008210342d6600da480c3c0044074070290741508502c0001c01c1c1072040a2380031400800b408000181446981521140421600c1040c00d010290581d1004804a264000e41020018080700c4c0c0648030f41d80000c1030301624129100e88002e2240d86007a07142c0b141b40ca0440c3c103454480340c100540751b08001d200300600013440300c0c103401559900300c1404000001000d000c0240050b104581c0508403112080c0b8000700e00c805007088403172140c0c11007880c059040c2ca8101342040d04903141031801c61b94080d003200d82801e501c515040451080300b50074a01003401c000040e41e1881d035400720130195080d8500340e0342c241c80d102124002c4a01720b504001c5209a07140541044054407204485500c2d0305581143c9c072421560401c0c0b41c5d00d45a400c1107040b09040e60103100700e503801c415641200f0b0340d188900000806 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 906669676 1250 906668426 906668453
    0x1e0318190506071209150b09011a03060d0c05060310030b010e0c120a020f0a11070b03010320040f1a010f08010807050904060e0607020f0c1503070807020109020406060504031e 77
    0x1c112444841c904c0c0e074401d9030040400143c018161080c8140c1c0400c201c00580b0b6004c014074040c09108000090000f0102e50440c0500c0c48503080307504680b503080400c04440c000300020f81e060100c1341c0011900e40c0c1e45100850080c05071412a0120f546103103404041c00740160700c510903c0f40b5940401110048030740c01c03120010b140c1c109014a41e50740040030402801016401c400035031011805a940540041d0340e04c031000d80c008202c1d0040c40c1d076550754160302c1c40240001041c1c42103c00070102c8030100c0312011816118002c00c0400c9183d21261140d003181d40076407803400b049802d00d618018039604042d180341e01c40024540000300b9814088041c4d5241c80920545014420860004080c4074480c0c2c4202c1004d003e02c02540c40c981047c820081d515018060610a80d00a0151440491808401c0005040004d105e918155650000c0656201c0710050a044c10b5548880320000160356074803511010301000c0d00c0d081d80380c80c254200207000d044c0710701002090650b25244c80b4013140e078500cada422 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 906670926 1250 906669676 906669691
    0xf020f04032406290c2d16031101020705100c020607150c08090a02090105040c020c0a0603020301080c0312070b0c040806040f02010f0206040c0302061e0318190506 72
    0x44800100028101c0300c07612400a80300007620300107000c540c54103030032107408002d248a01c04006401c66042c00f55168030554050210660020006c1c0d401d9000c038003510200c0303544030f580804006485003a002e0400c000c2520082c0030b03c0d100300b410310170480d200ca101c0c2c94109082c40284070803801d15000c500c0c25082c221422041c090b807145403e08554818049644065102640000e0544024101400f40900301081404921148000b6007008000079a450207150004c041d040c20381d180c1000c1c00300416030b03007107050110700600c01c011490352500301c1c5480081c000307560010782d0f940c0340c001d14508140c4000d4009100f030708000d420a41892449051f2040c1c2d640203c0e00c1d411035152400703602c004d4480c1d80d0000c110f41c0200800c22084c800b1024400b0002d41c001e8840708041c3c12005803c82e12000201d07002020003410000a101500741103001e400544881c184012105404d01410f18440d0000c0310462400d5007088000c000f41da80911110084002c8009081c05000c504d0795141d4039a6401011035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 906672176 1250 906670926 906670943
    0x50c0603100b1809330402070f05060609090c03120f04080709021305150d0509011d010902030c042903070302060a0e0f0a05010c030e060403240f020f0403 68
    0x46220014a41e150010000108031680d549040ca980400c40741051031214420000395000a0101c0c2840404034041c2e190300450b450100e01d90703030048150340b18030390425800c90740c00d01c10800003803a51030103c900e2074010310003401d540c03800008118a03140c005084001c65000b5a510005036240058204405440c205000c0e031102c80500c0507040b58000c0d60f2181d182032007003c20020b0410300a07401000041c06c1c10713407a1a9010740310b50500c0107100001902c80b000800410800800150b56803056801c445d804001142c10f051500a1100d2034882124006030b6075504e9042204601e0b080089000e15081601c1c103201460240c03a600c0c0900c140d801d0009588489640f03181e0b503c3d60140700000246600520381c58a03800310280082100720401103090045440e0321a5010510300320180c84101d81e416520045210348599003280c419400032501c03500702d50240004400075010722a0030780300700c4005801c2044162400445001c0d56030070402c03131594901c100594441c100001080f10309803600003e40d13 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 906673426 1250 906672176 906672181
    0x60702011b080703080f07051801120f060b09090a0b03060402010c11030d050414010c260c060c120a14041415070206060109060305091b06162904050c0603 68
    0x210103441c0c0c0008002048180009005030426070000c084a01a6810f149001043e9481404c2944d061140c106200842041c40400780c001c0e40c803403103040300901407504001c61913045250000d41a5582600800080314011504030001d05103c04c55a0303000c001c84030144410314480380400d84482d80500083c0c100300114800605104000000d2060724202900311610352418003002001c58101d802040c14580e81c61149400315849012812207180c3c0044103000c1c1003051071558840c860900342da01d80348140a1040000d001001d00210744103c3c0300807907d40e0340700720100b4640140000205848081850004441c1c0240c4408460584c13090344070104860403c0c89905541c5042d05641e6100c81e800419801c00096960115015010310001e8841070811a240e0805605442c403c5a0b0f0607003950100350042c8200c020100d0800c00c000c0302400c1c2920b000400c440489200c11401011340300c1c0e403400284605680d034181100281c0e1010030625154038100f65070707003940390362900c0411403060030084003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 906674676 1250 906673426 906673457
    0x1b0702030a0f0c0e060607021302031b13081207051b0616050f3a0c02130203010501120b0906090709050a140406060f0504170c040914060a0b06070201 66
    0x1824965402120307044594074a850f107103680ca0024000c0355070030180107000c60300d00c2c10080150b844080d4002c1c10204440302801054000b50402003d1f00e03441200c0c00c05030a0848007034001023012070480b90300c0701c0115003001c00c03091400d1320242c84110805820842040800c1c0e0114000260640c2056840c6000c04074100081d0a0b000d101503030000040402702540800c14005007030500d107a603000a881d540405141301c85007004400f880c480041a1980e0b0300d00c40b80b400b001e03c51681d07007410300780001c071604190041240342c1480c0ca50041c41c503a00000512296070460600c40308000581800e01c4400c0620300032848070a80a4a1603000300c1c9e180300403500841c0185015406007401500307298106a6070360f90400b2202d41c0b603036030500543c80c0c0503021440c070b032003003d01c0d1000c0c42040d1103880c50103143c9115491040a80828a011402603046100581d9140c3c000c1201c1c0a001c1c400580d00104010401414150050128200545810340c0c0c401140c40704000c0d07030300d00e81e02400e24611040b0380ca00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 906675926 1250 906674676 906674683
    0x11a0706200c01050412030b0109091d0708030a0e03030f071b08030d0c030b0a05010f0c06060b0d0509010f09050c0f0a0b03090609101802090916090b040c05031b070203 74
    0x207120714180d180032034041d4407140154040b9105501911802d001140722440075800c403030b0000b070410700051149005008003001604480103104060038180c088004451200c1c0c05e0018503000b0000c80c4e0030000e03402e41090f5001c00c0701d000c50503003180a549400070940083c003ca10070f5050082c6002501d0030a080505007440d100e070b008090380c5082d01d50710079000e48140300920000d298000440e1414042840f5030804803501710a031036045e1510012210000c000780e8095410442c00c1700c185860304c0d80800c42d0138141d000f511514007802c20100342c0d410407085090a660740b2030284060360f4502400351011410004010b00328200680f9000d182d40c0762074002c05c4030005070350040b10440303000106100c4d01640c000340d0107101e02e400c00c0940b0140112414000c040c5d5200e03000910141c60314400e035401610f441d8000d207400a42c0c5004451004461800304606080d6903840b95052039074458001c3d10780d0825025100c0c6c2c90a052800b945540351070805214411031000345a0740c107400100701c820440d10b040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 906677176 1250 906675926 906675971
    0x503012603090a0621090c0603051902130303080c0a20010e06100302090105090c030705132106060f05060d090807021809070b040303440f011a0706 65
    0x2074800d000d6644c0383c0c0000380000c4401e0151221102410441101e040c49601c1801c040300d902111082007145008402c0b4090103000d0090301c55a803400754190950f2845200910310401a030701e004040519505000c0e101c1d0310b0080c82401000001c00140c4001540800742e1003042c43ca1082081a4643c00e0030031900508581880e2100c80c03207008280004c0d041d201c5c82050469108456a540980c0c03a007040c8650b07010300b9540204031450034004110941e02840c00b034a000c03001201603501d480d40e504445a02e021100c5c01074900741d20296441c1d010710030a806160080c1044400c5483d40510b000007040b07040c460700b454400d102c0d17030300d5021504000c136100450b0181c5800400c02c030b1035166010614800c4680a48600035207102d09040015030080d0310302910112a09900c0c5d030221020411784882c07140d104c68040085503030508482043e03078400d0034200b20244040c6103641da0b0900c1c010510698241040e00f211044580d08200a02400c0c6d00c2001c994160740d000401061a21107800600c032544001d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 906678426 1250 906677176 906677179
    0x70e190518120408101806020f1c0b010201050a0c0e01050d02130e1006020d0509010309140f010b040e0a0b0c0a050d0501141314010b09010504030f0302031207050301260309 76
    0x16a980607205007052005481030316a000d0a80d41c220180503048811110700e4000d100080310036106d0f0740049019a40030300540062078100c9840c02d032510180721050200524807450043d55010681a59642441410340c00304c051541002124820341e40542441d2040d2810303030401c0000a01c07100800f50a8050720b2140070250001e554032030300c0790014043d018048a00400407412200c0c00120940b000450403213070322154855514100204004401500d1005415502124401551b41c0200030030040107001004110001130710821440c10013060f1424008042c00d59403004801c0070118039070312075031500415011507003a60f81c002544280e0b00c07802078000401403203150000000b407a03030541d2091581044120344122000350f01d4080c1c03004540b90203820401c0301c40724a0040c01881c0704500141410141418114241a0707a507803030b03c40c41c0040e079004030016000442c40c0c0d20003045822507250005070070f041c064107541c113007684504412050406d0107169505400705101c4210240200c9820500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 906679676 1250 906678426 906678433
    0xb1e0304050a1703010b190e0d03030b1302040503030f070f0b0403051c020a020a14010e0102041e06020d0804060b0a08030a0801140109031e1a040b040302070e190518 73
    0x50604050b51030300301d4001c00342c4107420402e52000c003602c03541084034182d5092941072401e000c2c6501c400702e40c003c0500180d0061040c0313148031283c0350343c030311542e003503c80e101c0e0341c003c50444944001d0003450140e00485a680c0c0e030040c0424881a030b000300540b0503513020301240d02d071070b90180e003000e40c46d8040c0301c60060720f40c8a1880c240170038103600000420040300140c5404030703a107024006c0c08003280308013240305005030004400400012040c2c400c8007012908440081510706c0b103401406e0072a0f11990203020120040d401d8072010311424480c0b40c00502c60340c0050007043d024504c002c0c1072801d00800041031165104122000c654400b0141c80c060550f150451b078a030100600c002c4c01c485c0081c0103a0034000c0c200d1022042c07542c4030340382c00c0f410b83e0340c0000801030900c00c880c0c0e19451038a170308800300c2d0341070b0703510740380c00503030804000018855400b40300d1800c80340c2000c0c200a030800c0c0301030308500000e910900c1044940445000c0803003441c42071400008050b91003860003400384402410102d110300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 906680926 1250 906679676 906679681
    0xb04060b1002010f14011d0c0c190213051b0304060f020f09090a060b1b012a0915050403080d06150e0312040623160c0905070c0803010b1e03 62
    0xba0305501c180d0b03030b406141c00d04005841c0c89141d07840d4282c009100d90000451528187c1320013084a0b818640c2100509200c076080405040c00300341085524290040641e684645820039071818100c164118070700154100101d080022200403035001c0042c03000c04220000000c10200501039001c02003084d824101103442e11040482c01c0c0c05980074207082d601c9141c0000c0442c42d980014880d5400b196108070303a0364500001c00c1404012007502d00b01c10710407075684044480c910a003080c4603200c02072000756840159481404060f10880003a0001002c41c081600c054554a401000305d40540e41c00c1a017240d200d030708001d604006448203030000c081c00c80c0e0f200c5100201981150b900801c840e421002d42e007001075074404031901d5004610800e40042c00a00c012580764445c0c0100e00e29440b00380b800da600e000b12000a507501804135607003c5034200c1e944001000340a49a100b03e07600b04000e4900b100340c1d042c0b1178541403020301047c0a49107241c0d000042c031640450700c2c00300f58a41d42170502141c85e240d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 906682176 1250 906680926 906680959
    0x60b0306150d0f020720031903120c0c1b0503030403140c030a150b060702030d0e190e100b0a0c02060c2401031218060c020d02030319020f0a020109030b04060b 70
    0x350005e010440d0304801c1030201e007820802500c080c070507401001c0c00501c184400c813071031421000c1c100c0009905005c1d480c035203460152841e0003688281d4002d520341c15409161460000d18403103074503040b0000744014a07028005030303034040201c0f030841e40c0056250a040c50b2190b2200e0401804180740c951600c00e0b50321078400c000d103120301c058481c620341c88100f081071704610070b00c07025114843c4025816000721010505a03401210039000315800903115821a100103c0705c80d09082640d0840441742d0390010411101240005406000d05a20700600c3d0820641c0b04000c0c060790107200d0700910441001c1884001d42d9000c00035a03031011800e00d00e50440e5400102c50000c140402e01040d110200b042d4596100c00b402050410802e4001d080101d1030249414021202550341703e10803030344400300840c80009039400f0005010842100011b890582000c45406441c02d40451040005c07034110341d05100241c1e0300000e0300c0044076041055140155280c0c80d203000180811103240794021421214000305 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 906683426 1250 906682176 906682181
    0x10c03091503200909011e080f06040204051024031b05071a07120e010f1103061207150305090c060403081206011b060b010e0402040602160504060b0306150d0f 70
    0x94070b0f0806440030011003d141d5511441044541034120b0a00d078010031034502c42c61aa6403005d40500d001d6102c09856401c403030704040c1c98058518441c0c0c081c800b800f06510349031080717940181c407111201c0c621034a0070303807248400c0200c142d44200781d0f9244801496842d0180e040000c8110002e2401c840c00c2008150103032043d0051202510104115041044446900f618213402041c160311170840147d41e05202201609a5454509540d501c50010b941a829540100d269a0050f40c0c03085442e490f110b409d200c0e0842007410701e20700c294004a0200020b1054a0040340000360328940460703035039030304c505092801c0a01c2401603009007000400109000c180400303411180c40c1707002880c000c2d4842d0f00044450f02c0d0040c6031100b21400c1048007900203603c5a10015031040c06044c00404c032071030398000030202c0c2c1042d0310810158208072412822540b81c4004880174000485080242500708400380c6079a00008080901540011031864409600c0c5001c0c0c0c2d1001c0c0c0d02d401d040c04084104c9900402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 906684676 1250 906683426 906683441
    0xf01090e0f070f061101050c1c09170409050f07142104080c1e120904230105130207050c04110c1b0111011407200a06022a0705010c03091503 62
    0x20b480c0640d4174075046042c01151302030089203000c0380c10000d201604400f03044c00200c45640c2c00c1d50f6003500d0b00010b89000300102d14078804002d80c03505c65190000d5001584c1d0001c0c210340010680f1010891680d4102407540c20101001020726100c040640a142d2460310a42c1c0441c0c04c203200c00c0401040102c035000070500484035205540c0000280c8150401104582c0902c0141d0b400604e8294041698140a840c0e001030040c004114445045454580f02040c145400c1d01c040d41d0170b0050010382014a12501c100d48040d4007145498a2a2103103501c4804030041544030b9500c3d003604444120714641a91a1318110101381c44c001e62058041000d0b1128a0120602003a10840d03452210303801031086080280765104803116607550344504840c0e92160300d074403000340c6048101005031000c00300040b000303040c40f451006031384a0078050300c0e034003c405064000701c01107003a0524807480d500c04079560040342c0e800c0c20890040c0b600c1d032905503140321346500100b0ba500602c420f88034002c1d038590054039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 906685926 1250 906684676 906684689
    0xf0f0f09050f06011224051503010b01020a0b22120512010e06060d050709120f1e0818030c060d0b090601030501080c0904290a050603060f01090e0f070f 67
    0x4211002001d066600e650003442160211079001d40c01c5030100f1b072070082d6104c00704400350176040c9040a1104140c1200c02c15110b220700400d0600b290512401d0900c50700140c0c541c02d0004014082680d618080c100000401d23240d00322113200001644405066120070005032f0012150b003014106100c01000d5802284900ca2004141c2c0000030f0740a0703c004d115801030001a0000b4a000a403420b000084c00c006030510782040b810160000e0703114155464401c2c21442604081402c0200d42451003503410800d5041c15440005240840054105030407582c400401c8242e0106020304c0c41c00103403c19040c103418542280e000500360259180300ea02001444104035403124032512290011412504240103441ca254080c0c42c07008070f0307460301818481d4000d1007824084021080450705641036556000400c41058110040c0110103015004507648420282d00130f10840c035054000340d51001040c400c01c0142c0c1d41c1d600380720154039000d0100c1080c2e03040e408100d40f9200e9450012030000b804910851 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 906687176 1250 906685926 906685933
    0x8210c030916060f0503091516170601021c0306032003190b0a0b0d0606030c05010212070c0924081b03010504020f01140c150105040605030604030906030f0f0f0905 72
    0x1107450007142e4010303000e641c001d5403110071034a00301005494913030000d04110458400d0a040c428042c0d08401c02c40d120b801c04101c519142d6079182c44c0a001c0f0040f52500707000120300141000201e0340d000030400701202800328000d145041424047e00106260740000d408003081b000c0001a9900d60003c07115901d01c150211500d10794654a01d0074101d900f900c00070b01030700c0d150022039810402c030f8004d080c0082006010920004181d521082100c040c1d034002c075148041e4020801441d078051000c060600d504000031482c00f07142da600c440302e21015001d45500565201600489514140091803100c120f0030014000e10392a040c3e101c1d43e405402407460380b201441c22008000d0300b41030007040c0c000c46e4090600d22105c3c1403c00195100c00c2580c5950078220818070480801c001c0402c0842140f42040703d101e640e030350600f01844203072021500310b00e0180c6c0c0300c2030500c00000d5200b036030078088400900e00000d890103c81c07080800b5100c0c900141d0034141c11b080d030120b40c0d6009030780000c82c22441441207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 906688426 1250 906687176 906687193
    0x40e090304151704122106030209010f0b040e07210902101110020a2c01020c040203162f070f120804060503091005070c0c09150308210c0309 62
    0x2100c2d00e030412082d5100207070f0580301007800210240d042030b03079104c110704011604500c4100500c180020103052003403119161203007001036003440326005004d0200ca1080050003810310b1040c3d025072103203104a4620407011000210700902c0344400502c00c0c10014415031542a002410002030880c10700141c3c03040140c503400800b864014904040a816500c000d841840c0c14004008001c1d001000140184040740d0914503a56068071041082d20640c08140706015040d1400246862900844140210300c1041448030000c0400c8627240400b2036403810281c0003002e100c1c04035805000782450880000d8410107c0c2c841e5074041248425a01107420301e4401d540d0310a4461210018100c01a0540344204800d001d0701d88540000d50340725841d04201c4440350811000c00c4c045070401c603501800603520b15680410081c41c06014802070001c80810b01c500030740310312004501052444003c01210000502c02022030100018400c2c130403101d080d2038a1443c0c41e05400fa05c56108555050040c0030303240f01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 906689676 1250 906688426 906688469
    0x1091101050a020c0f0409061d010b0d03120902010c0501020310061d1c140303040303090b15010906110a0b0907171f020f091f030b030a050c090c040e090304 69
    0x650b1220080307540200b54105400d414000b0f5401c040d4029500a61503000c00c40c0414818040c8500541031503004150030711524a40a084035000a01648184c03805440b10012961025501c0d082008580b000500420ba510040e580d1007004e41004103194008410003002c20060100d91040741c0543d00e4150384600ca190b00302c103102a4040c030303440e48134030000c030f500042c0780c40c0d01c0c21803003020f01c180400a034002540030001d00d540c1088038110000fa4031396a440d0104503401401e0b6401034405046540708145078000607200084034010f4404000f480000c3c00c9a8039020070080314541d400c142d0007001c0d402c015441c00d4485810b801088031200d084103040d070164900140c188003400c1c4040c02090f0f00480010600041c4d400003180603070241041c020121981d5400ca0b41010701c5c20030201c105205141c060028082d540c62080f0700b80b0030b8100146100c0072171008986180401404c1700e4600099846084500181c0166080902c010285504010403100c00100074800d8500e414070002c0105000070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 906690926 1250 906689676 906689687
    0x70b0c0a170c041403120f04090f0b030a020f130501090b090c040305032a010f0506040b121c1b08130b090f0d1104020708031602060105030616020703020d0501091101 73
    0x4a07a9000b15504000c20001340d80c802c8444d1148003030040c1a1010703c1c40a850901854003d081341604000700080c0420815149200d007956411a446080c402d2a102400003074031502c00c1200030340a1b05020304180380310340d80e0881c2849c40d45040c0c0c234108601e50316541040014503440d20141e00408196012400c10700f0383d0801d480480e50b00c600211324145210049440504070b201c0002d00e01c001085024400c1d25081c041c410002c07245800000340e51900360b00308802d23180302071030590260b00f02c1380c01c0000c034035404a4080b5a41c0f047d003140250807100200210748075000703220540d1010502d071f08000d0802001e0001081f20140c131200c0d204010742c5400103080f02c0d10407458655070200c124000701402d403c00910400300c040c001e55045c0c5044c0d2209000c60140e0340484e008860080001003080b540361415261075003449100c1c40141b000f581000082903844201410403400d40b481c103600719040510810010024507400780004d450306100c0d02d06a4040d01c0b505108030b850b030702c004000040552245 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 906692176 1250 906690926 906690931
    0x70506070f110a180b04110408210d0608060403030e0102090f22021603031503050312040c050a030305030601030c02010e070b0705070b07050c03070f14040c05070b0c0a17 75
    0x196074100d881a0969074103141d8500c034041c00c2d400462901000078041101840040540184c1c00082807070b00b0a00c0c02c00085640c484400b9018940c01d0105014100740025440310025404810502107200b041503001e0324050402d055a05900b80303a004101848086000e40c00340d0301c6901c1c18400c102a9015090030303401101c4440390844480e0102d4200b030702d071072032a0b950b08010890f14110103014824056041e41e001c003c014605041c00390080c2c1c105645032045820960400200c415a9401c2d50307071f019200c1c803e02803400058107905001c01c1c144030a400740040101801000302401a40e245000742c00b0741c004403001c90200b403400790340148841c0103000e0203c2050107103010704816414540500070340e0b041960103031824030600e0004601c501d2118002d00342c0034061030040180b62103401c201440e00446402a10707140c034030544104039541c3c02040c0084100313030854000c20600d40c80c983c100c8840c05003d6001d00074074190003d000c126114880108042c094a40c0d030312450ba2018142240c0c0010103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 906693426 1250 906692176 906692183
    0x3012c0a0c0e01091a18101e031e051807150906022109060c011b030e010c0206070807170c09040e0f0c06180d03180b0f120403090f06080907120302030d0b0418060e07050607 76
    0xb40ac070071681d41843e641c011a88002803035040215100d100310f44c20b00d00885ca402403949803000c446c070240e0315500554040b0040181e4801030007160340c00c031030034501d10111502c4001500c50104491078035a480c5400c0e1190006c3c1080200600c1c1640c281d11040c0c4981351241c00302203444d025000c0001001800f506010700c07401e03001422240c580130003c071800580180718104100031881c01448180042000d18010085009225103d90703039241004222001c5030900307031040c1e0003400640c18031440441d00402d5140c080703542c1512030100e44c0c002c44030b0864a00085a01c620341401c40403c140d0881c10703040350000740500c8406170b1034807512002c01c3c500c100c0781807018121050029030f4024401c5d40320258070610074036100c86020b1b9555441800412140c00c40d2000c14141c0040024110040180c071000304200e0b8034824200e03451f03890294a81c4a0041d0f1482e030140c403102036011503110383d00035142c0c03401b41034511100d524040c1840e400a0800c1050740c4160302511800089900d450400c2e81c011580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 906694676 1250 906693426 906693461
    0x129030307081305011d01082802040e0603250b0306010c0602041e3011040504030206180a0b06101e020c0a080102030c03012c0a0c0e01091a18101e03 66
    0x27603030b800d50321116410f903031030300342001304c1c3c4010145003520341c000b030401001c0002c04440c942c106a4201814001007006003000d010501042c9070300640500501e0b0108c50041040d86e591ba140c9200403070311040110009040d25000240c002400f080c6900c901c3c6c0d8469009110303a51840d1074038007441e460b00442d00c540308180d18020f00c1070300c10440c49800d2100603200fa01c488203c10b0404010a0a0300d1040340e05074051b0300310034100510a01001d101004408014000d00f80603251951101420300001e40441e000e0010ba4225480190003080071208101d0a0320058044000841c0020760300e00b100c4005a01403260030034000b82d804014000e40c1d02503c0010f02d02e5046030b080c140001c4500000354244c4e098186403080d02e601c25250454850302405800b10302140b40703004980060700b0403051b010280c1c10417007826000c00160321014580310001c1041c0c406543d44841501c07001d000701c01e100c0c500c143d100841038a121240754200246000c0e100b00c003c01c001400c2000d58064045178450b041803440002c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 906695926 1250 906694676 906694681
    0x21809030901050a090305010c0e2e050a050c010509060106031113170a0611030a0b0f0906060a02120c0105070e0d03050906130e09060603010e0129030307081305011d0108 75
    0x40c0284050004c514861500b400c51950301d4075054251b81301c055001c4003040b0949007022140c248240281c07000c0060074024280740740500b14090890000414040c100100400c1030b40800d88a0000c49420030f80c0c10000303110608189110507180d00086c03050300046031501810b200c2c1c403070b404000e55400c0e0221251900401c0e190910840c101521464100030b030707001d0071618000241181c0f1403040d0350a00c041d42170303483e840d000c40d44c0c0e001c8901100c0c81c0c0c3d11400102400d00360a40d680801c2950101d0142e075900d032102601401a0f1801c40e800d155181c09104c086060b20f242070b0b0540c00944140039035030b241113102c0c0c0c009082c0480c40c0c1140c0d40c0a0001202000102c0107803c081d0002d20b00034110103000004507580d03404800003c9000d89825800741c1281c0103200e03d9280074003d140724908054020018038044221160541c403450070b402c440c0c0621000ca9040c5680e050081d03940c4d8a412071f1146983e10300102440056143c3d500659000c28849001d030b6242200024903680840303c10b0310364040c1038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 906697176 1250 906695926 906695929
    0x6011d01091a0c0723060403051915020c1b01090e0c0f0f030a090302010c0212181302160605100e07110c130c030f0e03070b0901090b0f040218090309 66
    0x403110254540004400c200c1440007807000c112000092210721017102c40c0e40851100344c1400ca00c3d00b00f030684140004c1c0024000700340301052140ba0700d036511041100900741440c1500e218541c1c2c0711841401c1d440030907210003a401c0410103c0709001f40700b00995503d034031070b030042d02c808a4600625501ca5550300001390f583c0032600007801d0545000171100d0504102c031180411683c0119a0556550784401c800d40401d0740902904045060600140456014214071032903640202030540d03041040076180031810307440340301d40d0094501d4028400e541d1030880307100034040d41c0d046103400c403545441d0030001100c652070baa0580f01540c1e06003030b0090141c0c40380030007103405081e031004030b83d81c5020303002d022621980c0d9414110a03032045604085034030156100d01508840c019824940c0c5681000840d0110150100444400a500410514040d1510040705005016850f001000e013501d01c41480402001c0c1c1c000039100711300c21242d1030401c1c2d07450fa011990f45070b000d4400071110307403082c04404100e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 906698426 1250 906697176 906697199
    0xb0103140c070f08091c061506020c010f1101020d090510090503031302190807150c02030a030c030224250f1d040f050a0e0a170a0c08070b06011d0109 66
    0xc85009001c405d0920012400061402c4020036200d0b0308130b500035000c8001c00485008200e0301c1076131034142d40c0c44c0924141002e915200084000d50401240f24039041040b4020f20417040020302e420000c40d203d00d1541803c2c1e00601405600f51410300c501e4070006406601402881d070182c2d80103014500319211410901c003e8031401c0c6040381d03c0540c840c2040c03000d2546e507030104000c04012004110b46440c103c400a000c09860102d08100f1808030400c3c40941c80009000039008d90503e441d146140190400b2402c0c0710303052119170010304100350200031100211203000c0c003c103450a407070355522101051040c41051a41051000f1441c040410003000d40550300038121051601080e01d100a20780c80014120b6407338411469145a5400500070b02d10120300c500001560703d00010303e03070303030501d61101880c43d0044440a142c1400000d40c071030203580b20b10a004002988568481c1c0c0300c0d4203a140100c0280c0c0d0480c0c400d40080d900942509c2240c1c4a0841032204d0101a191012407a0501040401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 906699676 1250 906698426 906698453
    0x31106160b0606120703090606120c0506031b0a0908070f121220030c06010b070203070324060e04020f0405061503060f0d0507180c080a020c1507030b0103140c07 71
    0x5000c42c084c412210b0420054003014400e1811341c2e80040c0c0541e043c07600f81c0881d200382e0804044c00c0d011000810010b8404100502680c508607401912580d9841000307403015445907811803100004517036404955001040d40c0244d81e80201507032101c6880d0900c080860500c0c0c0728054038864600040300c0410700185d509108038144e85420000048100d00007003021b4044880700302c1381d5000240c03c1c0461682484254007601c0080f0400c1d03c1c1503680d400083d503550361800050013004040c480030310003040b030346010080400c100380d00307110b070941e1038a41c4808400100e4050b03014403651020405185424801d07244144002002c14012240c2c0d0076032883c403030700001c1c800354002c920100024042d0b0740fa00f106c3e039000f078400c01c020301001f41001a41d64413051030040d400465810000302c01e4105402030360701c50340400c0032480180c481e00e007800d42c00d16021414400042c2e02d00303010140321a080e8150418a415a02a01d00b8401a9010042c0302080c41c81140c011b5411842400b80c6800142400c40614 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 906700926 1250 906699676 906699679
    0x1090215070b15092a2709060303091002150412180b0d0f021e0a1b080304033204141207140d05030f181215100803030a06031106160b06 60
    0x485030702402d6250b01182d4000e1403c502c5402c00341b240d6007000c03180303060300c4940c0c514103443c3d000c100c2c2011004681c0d41d0003904200c3d8403440100c611b08038424401c1142e5403000d08101ca0101c95030419050041c0c801601080300d0002600d034059401c030000329000c00004440031029950f280011101d4800300500e1948146d4003034a400f004185211602210848405040042015555864144080e040c46c10902c5e489100c8600350640102003940b21054a910175054200f0303c113244903040300c0b22200c01c41c0c85001502501c03c208070701c1e094808036001e4004d842c0b0b45598808100151001c00c00d1600e0340248000b01644400030601a91141e50120341051030050500c0315100c800c0c0c0e46403802d41c2c0107903455903103003800402c00050400c104c0c0c0b01e8550703003030307081e0742c1c840092070703035590301612101c0c1d0b5240d000004c2c111201140c180ca000c0325100005040d12010350791a411b0120080c000b410051000b910304400c032804030ba440349041130890719034020800340a046a00b040d6a030906c040001050f09 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 906702176 1250 906700926 906700981
    0x1509181b17070e06010804031b08070f050a2a0306020904090c0b090a050d05060a0905191109010501030c1e091208030714190503060301090215070b1509 67
    0x5448900c6200d400c4420380c014041e0682030700386200041003003c0103000b40c2c104400d003c1480086500803009000d80b0307070b101da5480307640707031072424482c241d44681c040003001402c6210707051088c00808101150f2162240740c0400d001d000c81c0c0a40c1070640ca03100070a0b60b4210480303d041000070407942c010b0016102c050f0000c00c80000c0c9849440e09410f0f0307580100d060380e400041182d0f00d8900414604050300d400c07078840795640700c1610748568504009005012081d603541a10341844010090004603500c5031004100c0e00b003992074202610000b1141c85801004020000724041d80071380540c000342400c55545c001032101c2010b0030502640c8000d20b207401d100910340302045c60b16001824480c07003030041c0d15082e070b03038100300800511045814807a803010700424418411444900c13a201541030340686031058580e12081c0020340100034069000b50300c21401d030100502c0344e4061003c1c1103240d0285d91246640c2c0c2e5204038548141c5c11846100360f201d99910005020b50800301c64810700c459014840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 906703426 1250 906702176 906702179
    0x3030d0513170c0d020105010b0f09010905130603150b061204030c05010920010f021c0504050301060602010509060f0103030f08070507060c030b0f0a35030a031509181b 74
    0x10386141145115003800312410000740d01c207140c0d9081004c1d90415066100030040d541c58245102c00701e000d24800d09a28407070001301588503a00c01c000a0025200081444810070b807158400700042456210444030150300c9040c0f40404403592040500508014000e14601052000c40b0038000b13034010812028484008841c0e07021030400d2007103407141c80c80396448100d84241d40c075100b68046220301c04141008002c840c00180e075030340403034100c10306104d00000880c05812000c06032030601030707a0081600740d0f107080c000107080741d81500040d02801d442020703a245920340008612041c0000d010260216290882245010b44903104203640008036145c02d50402c0d51554034003013607450300c00040c000130351215001ca03170700c0c40e1081c080f00ca044030458026610310f18200c1c66503500c10131840342c9424001c0d4180b04645004520b0740e1481c01c0c41c189000da030740c3e402004c980078004000d881c244080a0107076140c003244654140c402e0b1060f40c00c0f000d201150014050b501c441105da07100c102d10040b0900700d0b40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 906704676 1250 906703426 906703433
    0x405060f2505060a060b09150319020d0504031b050d12021603090501080105010201022a01110c010504060b0d11131d0609240a0b01030b10121a03030d0513 68
    0x40c04000d1521070000341c280d41c04c03e001c078102517030555049022403403400c00c510040740d03481921803a82100c18002003500c9607a0007004058260040841490340c600000f48040d80620706c0c1d10640c071a40c480d44403040c012050003001103410b014050b0042065001d145881000c030f01490502c43c0308001074902628003803069a000290226024003100890804001032003071f50303000340200d405040e00307200841c208840300300f40c0d440e250000303190000100094492523030074071420340040c00809130755101c055860915501c807600a004c00c450a8901c0c5140107003954803071034503c00580c0d0142d0001c00c032204014044041040594044800003082079440e90341580503d0441d01c1e220b034196400c4040c2c5040c0c501704c068076041030300800c1c002d441030803080006440384a0420359182c112520610004030341c2e00100040e002421400c4180d640941e01420786851035900c00c01011099610754414441518081c034095400703003192705619891381043c800d2003810303411a840720703502c8032400e0f180d800840050349 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 906705926 1250 906704676 906704737
    0x6030f0906020d0906110f0403021c0204060807090b060a0e130617031c090201140c0a061b1236021302090315040b0105040903030209041e0f020405060f 67
    0xc41c0010301392501204d50504c40d80d44141d8404030f12026200d03143c82c181c0d054058552145010003481102c40c49511a11003a001110100e4503034042c208211217510b500b4610741c5c500c82880354079406800e11342000301a0034030781c1c103580e40c2201c1781c1c80d16000d406503a0100306849618101e0f50600700d645150028003004a0a461004140c1c40c030095582c4003d0010f255030408111010301190703a04120a80c00144d921480c1103203440c0020b0031882e00c0d03120885085040400b200310240109040000001034942e41c02d1719451039516a407108407054215a10b83d8007a1000e00c84545c540810440300c04100c8074040d42640c07503541049080300b40c4401c0d03036400503800c0d0b03280e500c0415200750b02080080d45030400704001e070404445030300440c003d450681c2d2160340090050160900503a241e026450416004c3e4042d2410044c000f8010712408040070484210b15610070a98804039050246503600712089100f1101610000340130350746003091160640d006948800401400c001880255005880044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 906707176 1250 906705926 906705937
    0x8030a1b05150912030112020918061014010206070206150f0a0e0708010b0304120c0204020405030604240227030c060706060801060e16200a0614010e070906030f090602 74
    0x241c182d105604091800e1490500d13461103100903100b0030401441001c40c503008100400b43c1c1110070a2990b80d9143c4a40c02c20210800c45095a124203401d00013003000082603002030f20041401142004c001c8401203030b441c001520301c100903070852004280084000000b800140c0d402070701c000c11075841c0101003801e1041a07840f881d206052241408800d952081403180108100c652490860500d91502105020b00210030300a0002c402d0a4004646613074060317a005000080503039405281c18144003400b4040c482610201c6441b480b54400d2010040c8280d864400e017507080c040001c032442080041049440484550603c580700b030141441d56568020086240700f0310300410002d10381900e8900b55202908044070081840d010071640d401c114031117045095042c80c10070b42d6200c80b5010010b016003e40491003103030044a8100d0203100300342e00178580d04c0c00c500c907008000c0d03a65030741e10500181c02075803903100003074225400300310304ea01c02e40058002703089001e000280028107a699200300e0303202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 906708426 1250 906707176 906707203
    0x616050309030d0509091305150402130e0a03110304060e28081b03030a0e010302130503010203161706150703090e13030e010c0201091509080d1e020708030a1b05 71
    0x1071800c40c141880c5440c5038009040c010512501861940c402e529031041c4512701260304100c1c0300080c203541d500c01c2545028086140204444000e495040c0c0d15201c000e40182c0c04164040071810300700200000b25000c548065441030300720101c0008120622008144481204030000307440303c1004011070341200148203039001084916030b0fa1071aa05038084036012140310b03400030f000400049820842003030200400b440c0040e5201e40203807000b08190f0150b0402a01980302004200082c00c11005103154003a094884d40c940014140c51520405401c8503581d401820742c0e5a03001c0d0701c080180c0a00030807032107810910b160940390094410091008c541959a00b20844580d005040e00102c011020f5007083c6065111511203800282c5414524414403542c032075400e1700381d10881e00c641c0f07192000e810160261003103d488020f0082c8140d648000c6104d561413001c03010201e40c0d00015110382111441d2000c0c500f01f07521860107403098124103854800810b0103042400c0010b0042c03210401d000740 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 906709676 1250 906708426 906708437
    0xc080609061e01170109060903121503081905070b07050910080601080c0c03120109090b0903161211061e130201090e0405011404060603021e0616050309030d 69
    0x103029840030320785180030708554a101800e01140d40c50200000d0000d0560301c0b41a4002e0200d84c0d0a002a80186280600608505c1c81c200801d41015030020081c01000351343e0009000307440c00d4110400341c1c200c07035100040a65104004e44100c03040b000d04428003004090030139a0030100365445a01c6004130803612900010800290f4800c00d10b00604181c0303400308070386031007022403605c40c00280c0f0482020300207454840003c242400420410422222072040d00c0481c030140d03594074103404003d0304981a0407540d0b2031030040000c200100000c180e81080440c2d88025848129946801e091104200000e000304660740c11003054010040100500661566140c1500c0c1523070401c0080c2051006080540707030718100744c80d0001507a44464000141c61f014450303041e10761100c1c0f60090040c0026010403840c5900c0d070007017000340511688488220390098900303514400300c4400d0070f00103034481124a548a0703018058034402108e80041c440b2180d00c00c00071645043c003401e00180ca04030034200c1c28030000c0c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 906710926 1250 906709676 906709681
    0x101b1101140f0a080a0b0d0f06020f0a120b0108040210080c09041e0605010801180509071e0f09090209150a0e0c090f06161b0f0b030405011805060705070303090c0806 73
    0x541c01101180d1000802c0420410386c0d821000040d011080c001d4044d010703110109005060040e150704031510f81144aa10303e649201128000c1c2413100b000d031a0b41a005d1809988084550050501a00c25a8000c2000750f04600d001c01c2560000380140140d213040c86c01740208001500c1e10311950300d60030603210401020a004100da001070780d040e03800107410001c0313240c010801c030500b1412600300c0c00407071500400c0d50761b201f605252901d891540303c40d84a5291607001c1c10346401e80200e00043ea2086000c020b0041d450703400400a4071310200300250030003800000100c46a03660203e18906040041505582940d500d00c1d45490300b9040d42e120804c002c001030800b0480c644043c458100484c00d031503107810041c020030b9000540e10000303405415100d960326081000f0b6040071915002d011071800341115503403503101e02102e98004880884156180104600300d80702d125103500109a0b001000340f80ca03a898000858194010803411828161035903c05000190702c0715a200c09481c1800c001c20003407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 906712176 1250 906710926 906710947
    0xc1707110f100503070c030c02090c222709061a030c09132603130606080c03070b0d0207060204030807020a1a0a0819050f06101b1101140f 61
    0xd00c00d55003551045550992480b040c582000580740d0140d114200303200c41483c58101a500c00200180096101041c0802c000d40b411103480a880055a070140e500c0d01c10007004e451022501c1e1038020f940b00783c91345402c0e54000c076880b1420814810300308000411180c1c1195074800650b0750440e030940d2000c070117110300c0b801810100000005c03004211900c2410f07041c64205040c0d203151043c800360604444000d6a030a4020001038403400d105c144568959a1421003442c01c445008100100c41160400170001903610001038584442c4000402414450b450308901c4645907100d15468001035030203003c02000302d10f0b148060b00007140280950707643c582c085d1041101031a00307904030b07210300c91034158510405006013042c0d50301078a150400e41d8580d00e070b2884c0e507009480c3d08151248441e0600c0200300400940740c0c0d60b240640380c10f0740d412101c4a4400340c00d50300e04000030b1502a01c0c100e5103002101180500c060540d825506040054416542500b1920b01d94000c0c00b16250b101000100c11218 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 906713426 1250 906712176 906712189
    0x2010e0c03030a090e09010905030409051905040b0708041509080c010c0212030112080910020a17030c07031206050d080a090902040b090f120f07030b100e070c170711 73
    0xd5030440c09185030900d080d030b0180080c01103000c1c200300e00e220324002070031500007540039500f1b0b103811008590300c0c0e95032602014041c2c0b40407201080041c0c107a14407911a8101401458003072075000030f900d44580d5601c141280ca4203401001511803c0404488000c3c0a00b203102d0304546a00806038199942070341c541e99030a60701c14503441d0085610091b040700030805580c0c280c07070554512455408800708181803070812800740b000c580382e01171070046401c00728580014415200301d102d07088a40c0360340005101d03520b1078003084442440c685001c1120300c2c00070b44070790310828280c0148034001445540300d130081240780c500381c04100c0d544540001d0138000a0381210484008051792542503150505291072000d01d4010002128040e11607011000c02507075800c8285e0320000034540840d45060070801405a0343d0300944030644806a11001103118030004541d8042610204180c2ca030041e00c810b0400c4415020115050301c80c0e0b013415031241995070100d4000c05c0f58500459120320062000e0081064 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 906714676 1250 906713426 906713443
    0x6050a0f051e33040609031505010b03150a0308070c030317150d02011b061d0303060603070e1801090605090703140103150b0d080d0c0c1e0312050702010e 68
    0x2440350441000c003103e03901c072040b152005051550008151161420380e000b0f02e5081c820328049000d0204000c80e40542c050038441c1102e000d64080491544624050b008030745081c0294111150100300190720600002116280508090150b50150340d17a47c5414070305801c000701c00c4030054076040d02081455485404641000098081e55605082407104030007000141c001c00c1d4010034500c9590025680100007070701c1c140304840400e11240b080b07840d2010060000039008042000c2407004002c1c028000010b5a101c0d000140005295440b511402d540343d9002c01c0500b40d001200465022104042e0151079000b0107440782d0100d06a414141003120110000b8030900815240490b0380703419800889071581140d0f0010748941c008801e00340c215018007850380300aa00080c0300078a810800115500a111031402040100a100800d000403684c0c0310190002a004050103190041080d80c1001400180c03446802d04c4000f901c02c4808940958000311280400b40c0d5480020400ca50b000384400d80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 906715926 1250 906714676 906714709
    0x31e1a01180c03020c010903020a1b14040e010605031509010c05121f0b1b0c01080108120306010c2a06091d0c0c1903030b041a0405090106050a0f05 65
    0x108560402804041d8410421040c14103a41c44408000b0b682d03000303504840c0d14203420002405003064606000e5a24152051b089604900307003a0b000c46404e4008503240166014614601e0b06402c01074208405080c1024001d011075680316000603881d03404119902a440394032200403441e2406640f400d0840743c00c240d00c43c040c01010001e1100e044e501066081e07000400e50089045004a8250200003440f15008101c1024002036500c956134402100003000080d0b4600310303282c030070704040116001c00703003841071280c5a030006904003a00c00850000e15030080041c5014401c2d58130581b162450708a68204c502002c020400ca4007101c0c000440b0304c03001078500350422000c201d1038400d000451140820f114941c0000c80f201049182d5449011100301c08502004c8503072083c648170500c0309522500d00c0407800709142400d05210381c10705001d50300400b071745200704000210b13400046c0000340900400b60203841d5038034840400d2a40d6039a200501070640300710748030701c40c50900c4103004118102c0310180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 906717176 1250 906715926 906715973
    0xf15180102040b070204090c0e100317040609030b150901181410091802120303071107180b010c21030b0d02030c0d020a0b0a0201020703030b01112104031e 68
    0xf403041c100e11104072080183d043c0d90028000840342480d00300d10185801030307812816142c082c8150500d214801c0020b403402034200d50355018001d070300000b061085100b407a001c281d00d207400f007000c2a9010303800360b404840c51405407242c006d04000201c070201c2c03d07004065007005180340102c0c8016103100e40d4904480c070360485030450904c04d210421070200703440754011a80d01c6101d1b111109649441800701264042d241200541d0440b40c000e071a03400c11142840041e05151300140103031000241e810880e0780c01d180e41010f8401c9990440098124444c125050100d51400354000601822885000340860204207545080340c45000303055075a0b040103148200e5802102d803000d031340c0115829100d00341c11191990642d07000e2021604902040d0712141072140c01041d11000a6019002880d10a101e6030b03040086941c90401911200d04502c04829070354000e0384640b0858240064407019402c501440d10704160303a80d5120b0200042058400324004480d00031034081000115503212105045201c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 906718426 1250 906717176 906717179
    0x9160b0406121e0506011101110306010e030303010e010b090a05032b0c05060a0b0f10020a1205030108030d0e03220e09010204050603070c020103090f0f030f050306060703110f1518010204 82
    0x1152010018848400f0806584201007040341c0e008031a880c003e50302d005c0c000d02164501e0500c11001d070b002205c940c2c1c040303624008142028500401128161510401318a40e241d0801294020b00d030402009030380c2219004c000400d480e07070100001442080c0720034050701c0507003003407041001107000d1084000034800e149e8440320018134003240b1264402c18401000800d194400d0005410b01d580d0103040350818400032400c80b040e41d0105240034110701035580080a14004501147c0d684024070950142c0c1d0010300c00303140e02181a4101d085c5074003200f0202d905000d05044030541c0f46070344c40c1c9480304010201200b005a000c0002460b070780543c43c0320003142001c2c80c280120b8007510004000300208051300b984501160301030f9004941c1981c005001410300b82091801200c111002c160a8001c90140c628a0114901c624100da118010242440303003840d0050360305550b0030100d10481411802107517000c101c1d204040042c0d000c02d640140707640d04242440140c3c00ca1801d0003007041d40059004000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 906719676 1250 906718426 906718451
    0xf09060c080c0a062406020604080912070312020723030a021309060c09090f0623031014060a09050c0f070f0f050609010e1c0809160b040612 62
    0x90300c14603006421603980341c03201c0311894249028124020482450050070421111440528000c0c41500060051240d51035003c2603070364210854006180840c00c014883d07150816900403808061060103e0710f006481750b951107000b02140803d4001a404550200003018a5410b0307144172800c00743d0852010344045000c1390b02c0c0c2c07903000c0010f0700600140c1c55040102c01c00c5d50001c8200c0c4d402c80130800c81ca41c6500f60003000120b59200c4d05580508200d00301881200170710415040380c103520400010710b1046000e054000e80001401549030107080c24040e107000c518003d90a4201030103032a00b0003440c0c50710421401503420b4001030403452a0104011400f40614202c40180940a42060329094145041c045a0210038001040c00044045044c20001d0004480b8085c00848000340104601240400d54941d0340f080740400d42c102504540d020603005001854010210a0556500200300200000c90610716400742503c140c0001d010002c00b5031003052185550514078091100f49100c11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 906720926 1250 906719676 906719687
    0x10f0e0d0303051b040603090201121802012f01090b0906010e060d15020a0806010801050d0b15010e1c0b011706240406030804050301050c1c0209030c09040b070f0906 73
    0x12002002e040d580c034042811880041a5012500a6001c2c0d40d66a0750700c030a001009000231801c2240131648074580540c100e08507010300c0711442018800c2c600030b540c01b5001152400c901e03404000202d0454402c405010509140300382c030003035200c00041900e000d5450700034450760f0f006150007042c1d0420801488003084e10250580c101400300c40b4881c081145061000f021080c6580503d062403001a01317031102500002420700c6044c1c240c03034480042c0e0341c07441403002c9240300f00001030032101c4c0680064403504080040051485040c58041041044076006c00c444c8821100c1c1c004c800054002040304004560740c00501401c0c02d01c0d0941891046250203680e00c140143c120300701001020940f5420b40e0304a01811900d0b180144140300b50b13590303030130711452550103030250381d02a5081900003502e001c000c07030803115120500c481c0b44107651200c1d0f41250080d0010f201c09039060042c40b0b2141c0d0a0350b034901d280750155006441c0305000d41052034000e84040a900780704800d009041400f04255030b000f2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 906722176 1250 906720926 906720949
    0x6040c0b030405100e120417010c02030f0a140c30041a091915180e1314100506040f0902060d0e011404050705030f01050606250210030b010f0e 63
    0x111000c25810000306003141401c8003655245020000071031f0006900907800ba10540c070000d0400200008000e00d42c08980301c0c07051140980d0340c401d04100e62030200c2e00c110103603210701401c090014180b5060710404d600340044400c41010004007074040151040d2403050318a10041c5c0c00018528107884d1100c001c0c807080b810f91030b688540d9000b08101c1e18070b4486841c00f05042c41c0c2d000005203000e07100c40b061510543e0300c0c10f03000c00040c1403031100c03140700d1041034001040c2d5214060014050341e07941e0340b50700601c1d600042100e0b003410440a07030b160064100a6132105001c074813030100302c9242031b5060100300e605010300d41030000d090404810168591100f181c00030b03101d0b4400443c042c1d04481500380500041c0880c8851a40c1c0c2c4001c101c144440800c08000742c40741282a140c000d1880d1980030300b48c40007070f41c01c103a014804006496890042282541c005c054901600902d02040d8000444998042460001080c1c50f41d11200d91503a0040100003d150b060921000c5404640d02007a0b810808 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 906723426 1250 906722176 906722203
    0x12070905130203060d150e0d030e3a0804021e0127030b040c09060b1201090b0a15031d0f0a1b052806090303020a0f020613030506040c0b030405 63
    0x4115151074001d60401740e15040800d6600c0e1520b40d400728030042c040010003420701c0c05403102003540d0500ca4054004100e030302000a000c401716240000010021400c90014aa4115407075003c80c55103c032021030300e58056850302c801f2454140180300915144180d811a9070b100800c0045031603800c4080c041e07502001048030f580c0401c013600075003091441504090a2908040200010407035180c848030240d8446140c240f101940c0e940303441001d4010780f4283c8800400880060007603070078503031002e508144010031094486a580400500c4403004546040020f501d540d40c24400d40c1c0f103004051022401034006000c0c0e883c001010315254050550f000b13004109481c0361240080150b01c02d20007034000107010003e03c199100c10105e070500c0c6401c0090300c00440345000110340707000d02503001c2102e070950003510302010240d8a0030f41c05031035040b0403a406074081c4504240040312171441005035110b42d00070038541c145400c080d032212101d40e101c8842908200208000a540444c4024520342c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 906724676 1250 906723426 906723431
    0x71110050705092e2a08070c06080a1a03030a081902031f0509070f050a1116090f1107080d020d0f0c030c140f0c03070f05031207090513 60
    0xa600701c00700c03140d103e00c20720b0584c040c1c980b81400200d901c0c400002522010340741003031030f01044244001da9414050341d00282684074082c3e0100100300c00c1003000782c1e0b242c0c1b041440602d8030080d0354600f46060040e401a43c0003440d11800c004500701c1c944560044050022200c03400100124002503403031058040c1d54013006000300108140f81401107036881c8184010200355100d1174040100f65200e009098541c1e54070030072400000c0c1e981003210840c1d00550b5240c0d58100038040d0a00305031070030b5204403034080070401c062101c840010b0040c4022014460103000c1c020070546000c200f007040d103803000b100e10340407844d0210b81c044d50180e83c800c8800a55004901d140c558082a05460003070041c04d808101c1e950420355100140f01e055400340b030100c00e59440800030300120f00303000c40345514202007001340c1d5002048200c04034944803010300148443c150849140840a07980d0845c1404854011103469002081c1140c504038140c40640e0b010016103040000c00313140400040400e1401c2d41c62808956 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 906725926 1250 906724676 906724681
    0x6090718090b06070b090c0a140a230a0b031f05130b0a030c03110916080c160c12050f16050d080409091a0106050711090601020307150c030507111005 66
    0x7250301003a1004c1d2504105000414076003180c1580e110090b070580b441c881d4a81c0b042c0803400201c40303503810110800182841384080d003404a0103540c40e80001441050f1401000c485400766a030100c4070029140c0400b6960f1070b420205590180350b01c40c80808080322844003010302c40c1303440780200c112581c0d1240b0750110b2901605030118104812980001e0102c2da6011808028004040e1000d4401e2800307580394407507950342902006144204481c00b0000071818808241103500440c080c011203d60f015000031601c13095621a140f020044d80042c80c2400c07407245c21010700a090040030060394003200500440c200005d030007811583d45001e11840b07000c0c0300c2451410700541c0c40c10349000d80051541000502424100400c18202c0c066a05810007401d200100e02c00b4425001d58214aa1211b005083c0100300f0042200d4a400242070a04520003408a640031401d0081700c0fa00c1ca0840e40340005448505810080940300300600c10010700c41500400d1500420002d0314500001c00c02e640064240c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 906727176 1250 906725926 906725929
    0xd0f1805010f2f070c17030913020301060e0909120403030804020f010c0503030a0f11281803170c030307080103050d081e060d050111040819020f10020f03030f06090718090b 76
    0x1000306c1d007200c880c0c50100304042c420610300000030140300718119040f01003014030140b0442644401d00510000030b080016100c0141014002190001e081c1d2041e6610910010010526034006900c2600011005030603c802d608007800d0130103003458203185c0351440a080b503e1b036558170f02c800b800721218650f690342c04051048031580710480071007400e681c8550315038a18084041c10215030440c41c50510341c15000f56156405104150300031814048000da0b410302e182c440c000c1c1c400c615041100b04000c100000f5450040c00d0004501c0342c0900d1f01c80140079419424443e242c1125951428248000d4200b448411039480c3c00e64030058181955100960340c6590103c0d14049102500415940c00c00403214820744e580c10141c03094990240c22602c0c0c042410b282c0d503045024500c80a0740000014000304940e042c0600c0711000345032a8012078404105820015166500c12110006d04201c600f0500038145411418690071801c20710f0800401030f020070100201c0d45030707441440300d2140d031a0444100b6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 906728426 1250 906727176 906727193
    0x14090307021e0411070201180e0c0a0212030a1b020a08031314060a1b0e1003051b030f010314030304050d0305090a050a0812090d050d0f1805010f2f07 66
    0x207046002d0f0091059061281454821303400c090422800709a01c3c041e0140f0700f501c40c60070ba600311441e8203080b6032540c6800c0e05060709035101013140401c600030520103058854417000194024540d1000004240300a01c0c05098558026a5600f045410100c070308000301c2c510b502540c2e0400403404080350440d41500c1c0558040c1d484e011004d4150103000104011030380160b0100410607604100304014124003401200c03118003051501d54440045004015045d00c02c2c0c1c007042c0c0c040700609074a00e08020100d0034400b2a00119484140b50700c02c103005008020150440c0c80304091507034010350543c1000d03950700740c443c803101651204040d40c44000031810320003044516065a0010160350716403001e4108a1000d5002c03201c00350355842108085684c5800000b059640c1c000d06907a02810444051034220142c021400500a91900d07069581c2c401c1c0c0c07030210b440e0782031442600001005840c51160209407024841601c4d1400034003850388030310142d14880e0180820401c0c1125688094901e80b0509 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 906729676 1250 906728426 906728479
    0xc07031e0f1109060d0302030d1d0604110f0105030105060313060b0d0b040b09070b0f090a052701050108090703060e0312101a040312030c031b0f031409030702 70
    0x1810301c041200c424000380d040700744008082550340b8145a5201814040a044003500040040c0c0c001c000462400c2ca5540c40108440000d8140d0045043d08141d03140c40d0a00944040d5200740456501010600e803608042442c5502804c042d419580f6003c002040e901000302040b403090780e414000c8041056990203001c0101d001403a6140e06841400c01c914054802c4400311612a91500030802c030b550f002644004036100e039510b152038851182050603151700080c04058010311082000310b410743c0c41c08408510f500d84000c40300b0341b00442042903081d485041c0c0c8083c2c1408004400c0c0080b003000403450500341d03a08850003080c6078400c1c004179441d5118417480b07440c80e0b01848082c03282034485007803414100c550280070f00860a100603001c4c60288a1840000c11418031803045000040c000e80007500b02034082d0400003158031124480241c85070a00c03400d000012424049014040c1e0035200700f49140c4074840851f96580340040c9456502c0c0b00b14000079106441185800c031094404098818 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 906730926 1250 906729676 906729683
    0x1806060e06220f1809081b1c0809010510030c05011103160b04050d050a0f030513061103010611070e06061e0706020d05061212090a030b010f0504060b0c07031e 70
    0x85580d464415500850b50184c00700d032103c41c1ca40008409038500440d40740170781203408903281460201000081c102601c0201c44c2c6809a03094101c60040103882d02415180680c50380799071031030304103c0c090842d84002c0c0800f100f030b503900c0002d10108080040b0700c4c0680f40b003802d10800700824085002e05c6d6003d4889102010302e141a20362040041d03001c000c900491040c2e00300c0d080c3e03095800742520390307001302607003840002c1c8520201840a4441d4100c2c40e08800903840c120511100c076150803040d0790380e03440301018441000004000719030b40896090302c284402d40c080c007806401c011040e0010310b005030035244103030300114121080791010001c100054000c00c2410750b0b500c07002d282c503a020f50803403481c4c58843c61501c00010464181800a4000c404400002e8143e10001600366030350764118a40054000c1ea06800200000d080f0024040c083c00300c490440903480d103004104810f0322820b8008000d150818401d01e03d035000002500010340790711803031600441c5004052803940304a0b904018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 906732176 1250 906730926 906730987
    0x30f06090207060603021c1a13352107050408030a11010f0515040c020316060501030b01120302030a050a182d180b040f0c0503011806060e06 62
    0x10b0b0100011940001c013100d00c2520440e00440d0b40140c000322031000150080c0c2244200107921240009182545500504e050720f5030f44070184680310641040640d0210038130300000300d0301001c02c10701101210030008400000c070500e00041242c0200043c291400070094014408020403119402001587d010b01a00ca040380d45840c0e07142401450b02d030400c00740c500154a8841da4004004150194500c246503a500003a80d00400d40180310060003200b4000045010034090750048498110a890800f07000d0840400c2079410b60400302c40842c0c0681c0014007100c60001e42c43c00181c0c000c03046e40c89880881c10550f8651401000681f50022001e1224011481400d00443c0340d138000c04407115654404a101d14051880c400040c0606001c0d005089038003881710314454072411140c0021003c00005000441c0040510b24560203580956628802040d00800144400c0c4a16540908108030030501405044d16010018100c002c4924296001c0c1c84005007021000c0c00045094102c0d00940100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 906733426 1250 906732176 906732187
    0x203090910150f1107121e0209130b0901050403022a03010617010b0109030b06041107050601241b03080921031603060807090b03070f0605070311010c0c03030f060902 73
    0x510f02100d2161500110300351392804c00010800048880c213803017006603c201c1c82c1000c0c1d21248031900c28580860049540b40b07039040c005032039040c0047c1c0101c06100644020803030303900c1d003c070301190010315954181e0b16041c1044003280e40024540401d00603044040403020150200c541c1c40c06003080000e403d90300b400d070300040404410405c0786100c02108020000140101c00450b01031340c00b80700140c0394909150104020789016880384c45191855030701503240805640e601800c09400b64005030300c840100f0131030848040a4000320b94400910b180c40f50403005c203107000c8075402c241a50060200051b0300700207121020104488420201c884a1895020900070722082999208507010a0080ea01a00104400340640a040181c50081003d056900d05013480c4d02c00800d8144031255151241c0c41c0001881100060a1400340030143d4a55540d496142006414505044c00ba126640c1c9415021000c140e441000f00c403419505190114a030071210618102401e080d0b0801d100d0284001503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 906734676 1250 906733426 906733469
    0x10210020a0e09060d021f0504030f06020c0c0a1d150d050c0f040207170d140103030305040c051509040b131d061803030a020705070f090e061005010203090910 70
    0x1a01034030608580002c2c0564446081c010040c9032908004c0d00083d040c7c04144c40e02c4210140c40c0321007070f01441c280781803a0341ca885110140305040c4050315010380c00110381c408a4411700100c00c00040c19201085080e11307040400c02d00d0601e40034808990103501d000728005443c2943c040305808001072603040c250111b0309003640c45180c0d00503402d2160000002965103414640207992003140c01642c2e8108042507150b0b00201035000811802c0f0031a030740c2055030040c80c10082c5050195000b5030300040c0e50300c0c052805009520756500110711804a4031030460300d00a81104807040140252408100391988001050f05210030340340100c4a58180030b49030000e00c0c035003288d6004401201d41115259155405502030051010b50111b420fa001000000c0d1032002c076070006e1940c5880b540803504036540d00c0310300100e501210b410085200c0d490b40c455440340e410401c601341d04001c0c011b001c44846454000041c0d07581c811600b500d80a142c0001c005a04c403c0c1c80e0944c40f005040e84194000546101070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 906735926 1250 906734676 906734687
    0x60309010e06010501031e0b12011b27090c0309050d0f0201050606031b13030c0e0117010b061c06030b25030501050604050409050f120d111c050402010210020a 70
    0x71019101c2c4552000000c0543c0300e4003d156400303208041441b4201d14841681c0080c00080201607004844221110080709092180100241d442c2107040c00f1034607031007001008002100c6c503404010401c4148042400000c038805e00490380c0805000514041003c410380c05030403076004c003410303d00807506c44060564014030712000c11880745c4e000300200d6440104015542c00182d031700740600e03c1c1e0071020712a15004440100042c1e06960b442400113580c039030f40d550429005401580359000d542c3c1c010480c11442040daa404102c010009001001e83c0d01c1c0440c419009a803111a40d080e001d017045000c820082c1d200d40d01460308075813000345504d0004280d441c041842c14403910702c10034004002500318400e200d03141c180c410080c00309244c20f241000b00030281c1903140c0e0a594070301800b0300c0e503000c2040411004195544041c541625264903080c04c90460720388890082c04a0400c1012a0300860b8001042290344101100091192110300040b807600d4100000341060a00c00144107400b03d8128 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 906737176 1250 906735926 906735941
    0x61b18090f0b040e1f1802091f08071805250e03030708090a0f0e0f0a1805070303090f0b040923010e041b03120e0114210901021e0d0b06030901 63
    0x120469840e0700c0b80c41c0c201702c2160403104442d0b82007141c554014005203404425250402d20008050940302e0851002c0030400e07581380c0c05a416a0311040d0104401d4500659566003051020000c0003a80b0700052489030030004880d95a01860465000034140c0340980030604603000b000c0c0407a529401c1324030340354120303902001c4901c7c41014980700009081d90600d078404103072903251078405c1a07a10346155440204e42c001c0e21503180725499070000c90600d84440305c2043d905001d0401000550710b5410007400890954104502c044410031050001000710b41c02c513400c440c000d80c8001030710b03148012208102c5610441207140031141c100000307202581c00745054001d500030070403d81d40c245007050100d201442480000d210243d5055403001403030003001d03880b01d650410f06100302c5202c0c0603c6901c010307501040140c1382c0548158602071f2110781004030719030300c004007a0086180000344000c103800703c28070301c024a1440c0c00004600c2020101600041c150080150249880f41882222903008c0c0c1140e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 906738426 1250 906737176 906737203
    0xf010309170a080a061e03030c110d111504060e220e061905130605151302210603120c15160216051e040216061b18090f0b040e 56
    0x9101700442c0c10400b031800603040d811444d80740b04406155540030b41d68140388000a8900c0064005104813584400754981d50440c42145440e0041d44264200074520361036501554807070a05010500c81560056552003510b541103d500d00c42900d2124094400c42200d104186c500d41001841c00341c0480c0080d80c1ca018590f0041041d000130f4607502c00320103c0e4011121010128015211100411010f601140e0080c1400c200d00e940c071500383c00131400d900291805802c0655000441c0d61201e200c88145048602c201c643c1c2c01154284000040e0f80e482c0068400c0c0420032002904c0c007092030b010407489226415480701c502c1c4070b203030000000696000c0340c49658094020421108000c40a404c00d07803060b20303001040140c440480b402585d07127100401120fa0307001642049035113060407001c0290300b4524441c00380401c20030485c1c8010308144040d00341c203e041c45a01445969007007100c4000c2000d80320300040018031200c1640d841ca015006404401c0d4001e490714000e07002851000c01c450103150308 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 906739676 1250 906738426 906738431
    0x110706090b040b16020709020903010f0509100e070e06120708010c020319031b050a02070306050a1a0a0b030c03071416060b0d050703020607050a08121509060f010309170a080a 77
    0x807130340403407130308000d40c4569100180c000003000d004000313042c2d01522001da00540005200a41d05440c1d00c2183c0041e15030b0721701644410210207105140340a1021165100406881d68524103400100040c0c1301919882c801c5a04041c0c0289a01081104078000d003034400084c010703601100c202a481394000c60310440942100c10f600c1854034024080c2c00100700c102007844036600b01c0d200045542d1f400c51789100d41140a0741c180007010901c0760180f11300810f14558000b425583c0c60f1400c002a94001510700d0103458541c1c0100001d000360015a580440c1c80702104d41e8039611380b14101c400003401c03248403a24000115030998880717032844c0c4544040b4480c603c1000504040340c1040940a04100020403a92050505100608100e0050304211340716008032040f0300d03402e80d905002c54101c440c0790140d48040d401002a0307007944070004d0110b1102500c44062508000f40441d00384007500c900c10f8185500ca4814108000100c51080310001403002c1558541180100041c980c01041d200c00b0031450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 906740926 1250 906739676 906739681
    0x803072c01020d0f111f0605040506100503090c0a03050102030a0f0b0a03030c1b0605120f040f021e040f09050f0f1e0a0501023c090103110706090b040b 67
    0xd8150503030300495058000301050a000d500864050001009060130020302601c00c03c8840d004000401d0f411241d050114030303000b91544084211101a44414411800c140511080d51103600d40b4026514540c82d1190f40e81d0b44074441d07030746000d5a80800030381002e410070b800000c1c040194040c40c09000e252905210148031588007000303440d92031515950004007282c042000078054544040810b10407034088411540e480c41400f900350155203c040842c20000d80e00c00e0040350032600e29405152100d00f824641081d0321080814808650300034003541e0700107545501400e00d5403100c1d02c070341c070010014050100715004580c0030340b0b0003400c00c490724030980c03440c0c00b150400031800ca0740c0c00401000414141003040170409000303482021070800e500a00c0340a802154081c00203000d11440c41c44801c240d4032901246441c41010707481c420410ba10b4203038640042d200844212080800e003480c01050b1400d1003143c5501610031241300402e81403510840600300302060000710701c00c030301030721444a040c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 906742176 1250 906740926 906740987
    0x406051803040b07020a050405160f170105010c020f03010c0e041103160c0f050a060207032709050c04050405010e0703200a1b0b09010e1009020f0f0607080307 70
    0x2800d400038003110940040c00140040c0820034040c05085000a0000d40802e07640c60203d01201d0f42a00e00c2c00e0720000e41c0305100701842e0020341e160b1240c070140c5443d109490841c0303058081c400041c01750504000f0804200340c01d560b1884490100010010001c010040c101d003005010000f1601714240540d00303020a10b0580081d0900340c0348a1010080103010b4000c0d5020111000c40c100c9000700ca5040d1007050000126100b0049400401e20500d401a610720706420040c00380085000e15910440c480c1e0314843c0281700c40005002280c581c0c3d407000c11b41d610b030010050350354020768000e0745d001031400b000000e0b448260625140071b020141c03010000380d00500141c0d030400080c0592581c0c039101c10021030a2241c4aa0502c45201d001480e2440340c0b06001e56488200343d07416252500c031a912040c103442c0d400d00c1030009030810301c1c02e01030400c071084c4a540820300d0b50404401d4079108841c541502e8600740c40d5181280c1b4135507400308147c1d5891502030030240c002807010180100d0100481c1440f07510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 906743426 1250 906742176 906742201
    0x7032304060b03031206040905030c06012c150d0620040e0c031e0405070e13050705061e030603010e030c07060f03022106150a0903030813030f11030909040803040605 73
    0xb051503414003642d51b4692041c0005054400300880e218442040b41506c480030902c1003d02030703c610f1001c500030b0002d07a8009030080030006842c001c03c000c05014804105003429500700c0c1914143c4005031805801c0c205038006025410314010321a42d21007604022a0100d4010820b403511a0507412190700d50100070700141c0001c54030904204102c050755a03540b554001010340c0a0301c01d40c12280201d0b100d4030005003440f02550380608030383d0440010010440c044c00b81801400e0b05461517405d00030f450b00007d289041e0180c410250110001c04100d80f52030079003024100010b680200ca51390f403e0391103c55a9892030344a02070001c0c40d880c0ca050100727440f80c021070320318081210000c00d4821030203076400c01c0036034041d101c41d62095811403e0400742c0c855070003a1024408545550340200d10b14100a08044001001d01c10088403004007140081d40024400405240601d010101b40300350f14809407a52203421002a4407080c0c150410041051240043d0710942c82000c09000c1d58407000fa06c80340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 906744676 1250 906743426 906743437
    0x130215090907120603050a0809122802210a12030501050310020a05070609050f011d07140a090f1a0301180206030705040506042d0e0c0307032304060b0303 68
    0x1400001c0701c000ca85a240f00710503c410000800d440003c84c9607503680c82c0c1c0d06d0040000001c0361441804103c80e511480c01c500c05114a42c8501c01800401c5c24100301c694207a160400d2024211080104840964542564205a03e8460181c05424002e00300d01140c0d0380056000032581c0303041e50140491014824003d1a040b41c40281c020079010390300c81100310280d0040c02c044020440140034050105034203006a01145000b2009030003e81c41c40f191040c01c0d074540403100580c01082102000180c400010194101e03100040613010040b403035000a0010750340303503000603940c40c1030000c42c000e00d90195000c01451001c8a00c00703445102c1603000d260a88002020681b040d404102c2e4060140c1400c01c01941e0212440c41d00d286000e465500040c51600b01e40c0000610403150b00394805240341d004200000304501245008001e441d24a02c40a203401c000c28040c2c02d80c4000c408142424081e401085c0c15a402c031180900d0261400d0742d40189910841c0c0aa50f610b041000c4035146081c08030031540b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 906745926 1250 906744676 906744679
    0x30f0f0105070c030c06091a070c0c0b090f0904140a0c06090f050102060a050c1603020102211003060b03010f0912080a0509070b070c080712060b09070909090f060513021509 76
    0x42d03041d005d901c41000401004200b03031250100c03c0404259007820306287c611800980d1940e0101000a060803e01900e05800c04200c00310b007004800001d80c2c411400c0600c4010856040210355510710340600e420500100e1380b9010312851088004010900520400340d074096a5406c850554808000e003150707a0500c44d582c00340e003001c80401c40440303c1e50003c0347c1c0440900321052a140c1d039402100c241c1109240c040d00141d5001c920110841382110050001c3c240c2034070161014100101548249660340c88000d005560f6201c0c020360540b02900002d0710108103007420002e20300203080c1100c6000b8410300c2ca000081d84000050f2a08005d4440c143c0562000c000501c01c040c1000142c0d2100e9000480075034205046000015604c441000303d0005400710407a4645411024a019000d03200300358111845441c09204010403164445030a4044802000380829002d009040c000041000c20f00050b058600313220030044030344c00720351212040382d1090b40c1048451040c01d080790320324043c407134003213 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 906747176 1250 906745926 906745937
    0x50c100605090610020c09090a03021506100c0302010603080310052119030e040e0d0f0c050607120b030a0b0106120203040b130515090c0f121e0c030f0f0105070c03 72
    0x31a5404c0c03082005000411034011200d9015100f000036482c584100c0300c242041e48820314500c209581403100311000100c03101c502c100e03806d00c0c00004005032154540c04042044a54401c0d003458030035040b4000658100441c1540d906082d0710078030940c00329000b8140107012101284010807a4403030fa03500726481200251108c0070f00300c5c64a690201490304158104030020071542c50664440c802e121110480b80014203446070141000303061040c15104000070311a05040d048080350001c203c0941c4812507140c0f400340e01e6081c03081e01008010010403503405200c5d2100c002d040005803148541600e0281d02c80c5904003c0c040000740580c80112030052040c90441c000c2255402947d03150701c2c801c1d1055085d11114400c1541d0703460380040480b0741154907801090741c48000c1c2803022511001d0002a100b031a03c11501d86007507696800d0884050310210180c01c3d011404460502c40e0440c8074100805807034241ca1040f1100ba81c1d0014000c2940c0e10354a85008111110f0040050550042c1e0540f905e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 906748426 1250 906747176 906747181
    0x318230904020906040f0f1410060906050304030e060d020a0f0207090e031903021b0a02130204081506030705042c0703030f081005090403170f060d0f0c0305030703050c10060509 78
    0x1888003800740750081030031060706d40342c5051000220307009000b6551100c1011401c9880c027800b01b013409141642c0610240108040107000181d03100080303c1d03001d50141001c11100e006900428528802e0880203541240301003225440c032940819401d2080d50a6401c592055803100801d8040760880b0712480c00c554000c00c100309501002c007190141d00c8409040060408904070009040e00021411090700d40c0c02c80d4041c4021854a96210903010f04800300840c1041d0030701d90203682e12880d14600184c14440c03100014210384e070411629000d0701300038000f8001c495170b102007103410a10103810b120315a03100724a03000c07500c140050030304c003260b8240d501c0f070244006011007076594a00184c00c02d243c5d850120404604d0f61101e00456004500c01c0e0f48080070080140181c00d0528009045400d44030510420b00501e43c0d161000243d482d5001041c490b035105007407908980c00085940018824003000c280c81092680210290148101c050251100c600c94a0303011403c80700b0501580c0c0c3d014040401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 906749676 1250 906748426 906748429
    0x5120109181e080301080601150c03090608042f0f041b0c0c0807030803091b030c0f060d05070c02120706051209241503010501030b130318230904020906 67
    0x203088460899507200c1c00b0180c4103600c443c281980f090704144c800da8440e01c010401c00d590144080c6001c4403501e00440307002900d6030b00803c001d1a51040c0001c02c4030b0003011806000c141c0c0d203d4500304081810b0000740300400780c603042003100b003054024416101080384500d80c0c189401130f88100740604040403a0310b40b42d010141d840d0380002c4c0342500c2001c818580803942140c1000070700c0c041c42c0216205900c80c60000c54542c0381440c0e40c102d0740070791907100034542000d0301d00146009a83d5401c03030360810f50b10989804140039010740212016480d08210500040c241c0010042d0300f580d00946501a0f03988150b8010340e6950300030300c070765800188200101004001e02e1903429800030480821740e020a03607207002940c80303113000301d125143c4001c0d40414401040c0c3d004114181860003038000380002d40c076580b119100084014008000c000300c01e0084400c051140140119141c1051101a540c517210054008032100c1da40d80d86401508604188005280c480384213481144e009248601c103030703140030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 906750926 1250 906749676 906749693
    0x5070f0801030c33020601090609230a0207021e0a0602150a0f09080d0c0908010e1902030c031e0114060303030402010f09050315091002031311011e0512010918 70
    0xc0700582c0200d06008000c00b80380031199104c01403540c0202155410001e01000321241c070703031082480a103440219581c0d078003030340c0c0702c0d49240e4010480781c010741d40c505150401074400d168000b9400141c4a90841011105000f80c0a03501800c1d80c074410070603180c081c26030f99105164240901521061700080c8801210f41154000040601c40890541034a54079412036400004120019584920f0044501c51303001a144000300b4020000f4042541e80450032501d8030301e410200c0990900403207208041d0344040112b0a9403220290807600b0310b42c030400102c44004c11507800300708207500744205980c504540700880ca02804006010350710319101e603801901c200b085039400ca42880b0003040001401d903070901000c070842c48030880217401480c203030314100d050030140d604070b200c0c0c18814024000b546000300001ca041e02d5128040303480c90940740f00142d074081240d501d0700074642c00c1450074030790b00d941c0807000d001180d0b45070b5540c2d001070762074035107002c140c1e00c030640001c1d6034103525100000451802ea = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 906752176 1250 906750926 906750959
    0x190c030804171c020306190b1206060f030408070b0606090a0e07021c02010c110708030a11010e06010603091109190c0504050d140d08070c020f0f0d0605070f0801030c 73
    0x1c002e21458070b4884901821031410031800e01034240e90200403c08141031100c40241c44441039502c441c10365017080c0b1145180d001e0344041000f0180340350001281900ca043c103c030511000d240c00b0715224078040c9040d8244d544001811141c20340ca81001c01c0441c1441410b9031440f0348005c4c25146451f040aa824882c0038008100d08114030541c090020391503000c1040201d1500168000303e0000f401c083c01408001c0404113010b5290b11034072080124480c04010b4541001e61464182480c400e1284100c0c05008000010700c558002c0f20000905d4607090350042c0803035481508080c2e00310044030100b0154110440b01030b0540261464181d800b504030b680015031812040c2041030a12340c544002c6402c03000c5200f01216031400f07080070021001020071044452410030714110000385484000180003000320303000240030310b04203200880907030f442d4003544484410192400c41c0a28403418810301a00d419542c000104100200180300d0300d109800b60350581ea00016003000051400c80d82e00380c1c15402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 906753426 1250 906752176 906752213
    0x62d040f061110050a39050903150f010f050306070807111510090e1c0e01030f1401090501050117180f060406020309010609021812071802190c030804 66
    0xc00115806008461044c00e01130000644001a4098094082c400808012654250500c6003280c207800c1840003040c89152a041031034034680303a0b1051004645040d002854003c1c044428000700007805040c07202c00b6040b01c070000c040601c043c0d43e94082c1030b15894144d81240028070260001049140035140316014200c0001c00c8440c5200d00407650707518610180c0b01540410f009250401c426030103400340800112030704001d4810000c0101d2407041440f00c081e10003003402200c118141c1d2580c002d600c042c0d440701d0702079030600c100ca203011414a8002c0c000d01841691a01d002e00103c0c165101c1c0c103603034803501c0070300e625940d0a44440c292040c5410600441c0400791184088540a0070000d20909000314410080961282005100b0500b559840d0300100301c4e492050040c0d60b0f030091040540c1c00c00400646000311008600c0c2101d904010050708241104581035243c144400c0749540108501da4101000c0c60340322101722403c8440130070a20028000030b46c01d50204000c924500d032422040404c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 906754676 1250 906753426 906753433
    0x8010603020a0c0b1f1706100f0e060402070b0112060c02011b0804080403020a080a050105011a0304081c0608070608150105030105150705010c0804061506081b0702062d040f0611 78
    0x1102419081008415000746c109414a40011b0380455020020b06802c003110070490203580f0308020b041c40036080c41d84101d0550310b20182c04100c1c29190f550440d001c41c0d412100d401c03007960312150401c041d80060780048a201d0710f40071340003004500c18868a481440500c51000744401c000750200c40d6014060b005542000c0100400001a61200180c40013450a04003428030003880d82490b900b140c0c0140d10000608103000491070700c2c403c0c039108880d4001c3e8494151030312240d080a01040c4007041151410b0107625061000c1011180000c3c0c09049a5441d41d907590385507100310003a02e0441c00d46021364081001400140300754039101d280d40f202ea00312409214101032837510340c0d5081d168514005004907410005100622840d801a00a204034504c10000c4107840e05800030300341e04000344689a0201d0042199182c020407504845216030003e05041d107419844101001000d80c09214680b00c12100d044855241e00f88000ea5040b03032044a40200c0051400d58180c03940074034004114580d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 906755926 1250 906754676 906754711
    0x130c0611070f060c02120607020c01210509061602030906070201030b030a0813140d02091f08060a050106092702031005040203041b0515030a111e0a08010603020a0c0b 73
    0x11005820b00002c0100c0c1d681d14100052600501030400394110415119030440c5040048050700040c42c1000c009080c64140801c10341d000001c1030380c00c0c041c40703120030031424030060200314000015807034010f008541e0402020a0440c400340e80d030f44642c1c01d940760081c00034444038025600a6000340205c0c800903090304c141d4811a41c42822f01d03800f841030380d050f10111080c280181098641c400c81d5205095400740c9018141d50001800c480c0020030700d00c81e41d0705c1207000c6d2102080d0f1102040040455070200c640604000d450b40c0c1c0680000d014580c0024807034440003c02807a00c0211044030000c50078001000c00842070824007a61000700300e00c40e5503d0441e0001102d48a6200441c81180110304166809269403440080358825600c66441034620680881503910940226500040c0300a00040c0b24890341000500328000c80303200b5820100c4401d62281a04100d2008080617074060b50340401c542c1e252441a4124020b50004030002002d040c0100b0004e8060001c07150056040380b100f0b0b8050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 906757176 1250 906755926 906755939
    0x10203040b030c04180b030a060f020c011806050603070513051f0602010b12160504021305150301060807022a01120606050d0506120a030503040303090227130c061107 73
    0x190710556003500403d40000c1c0801c0707403140039680d0394211501c0d06414444080d5041c0001d50b40e081d0b00c6009850269a055400041c401e150304a420420111009000300700c2002d1403045d1883c503404041e12120306000014942e4030b40411440e05491000b0805407100b81480d94580c014000104030381d001c0c90708900c00f40c0c1440f91200160001300380c00d82c00414052001d009009240f5008040071103d540304151221031b01290840e0601a180c0540700140c13240c4124006e500035034055484950071030034406180c6c070b01000d030700000c5042e035180392108505a207405504036a01c030740b01a044c44020540c0703004501c8801c0c0c25000b86405040501d040c204245501c2a407c080f103002d503010102007140040c11a104956074064158000c104507000d01113018030303080d81612400e0b00b02008082010020000d0101402070b1300c280d80d1540c0140040a1030300d12a1024000040d104180c82041c01c403a50004038802141002200010f5000001c0b23404c43d45000b00030b88460050a10038041805203201c04981e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 906758426 1250 906757176 906757199
    0xa02040e010b0901111501121712061c033507090f080a020303120709170303011a0c0d030e0307050604060c1b110d06090203060702011e062301020304 66
    0x6002c0d00c042096943d55008009025440c252407041501d8205900d460b4003405500c0c070090450f202441005801c0c840f5143c8115500300003080715661840102d05820076103100c640d00c6100d100d06482c03046654030111108aa03c0c0710456000380051002440701c8851a00c007210f00e0100340d01d0354400000001c901403052106441103a0030000a04002c10030403094104002000040803140c0190048100d03030b402298070303032180c00400321a010b842c60100311352074802c6504000608200c640c18049076106260700c2d451354020b200b000002c00080141c21100800903003200c2010480e0401441403c2d8600e505030060945080100c406000a1083c071011820a1100d070384560b00c550400520105280c40c0034003aa15081113881d40c0031041c41c0150300240c0c520a1584550381c00f101d805000160500e4404058108908001d426000380c400f40010913805400c480810b048180c2d66000711f821146002080313803283d200b9900200701d0505035540780201c0406038004000184141c2c0d24058440c16040031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 906759676 1250 906758426 906758429
    0x50c04020906210f1321020717010c03114602010b270106030f110c06090607050c030906090409080307023f18150909010524030a02040e01 61
    0x201003d000c41045121042102e240f1341c4030015007038000a03150f183d100c403088041c16a010003e2800d5000a01d0f000f03500801070100100800600003411140c6804294081e10a48800b80003007801c0000d00720000840708203a5004401c120b8002c42482d5055030030b14194441100501c0306102072a040c000f001200c0d250107020f00c0102d400109210b0107410520680c400c3c5520403200e1072100342e00e211140d0341041481070450f10285000710342560000d10f004020b02000d10313006100100041c1038201d540d0041030a504c100341c003505880b615540c9450540300c0d4400c4005407000c075001084868174170301d00840030703061940c006840091855459a282c070b04561055031000c016900c00b2842c0c02401d80100715420a214000a4076004241c00c200328060801c080c00b1074081c07101010845600101c0810111000650000c250010807408500f02c0e03100c40e88401040303402076034008004510f6081020b066031492400380c40324800b804075054800440d03080603050018854007080009601100d5039034250 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 906760926 1250 906759676 906759727
    0x19170c0d0605060f0417060708161b0c09051b0a03020a0203121e1f030b070c0203070e010501030b01021b010c020d080a1d040e0c090603010609050907080c030a050c04020906 76
    0x69541d820a50400034502000342900c1b001c1d8400c00400c2555940b04050340d8000c50000302c0071026203000201920110f14501c07804603a004950300700350502020075009012150048020001900c0d0012000c1c1111195200414000020071102c4402071080c0e00501805540388141d904103000b61a0034218810281c3d0380842d1142c002003a1080340c50b1130f08100d90401c0d414141d6180d424000003940e482c0c0d404030f1102030700d911030010001d6032450042094100c880e9000741524100381e10b4154401d440c020a000303083c002840c1c40340b4540554000500b100c01007003401c8091a40c0300d04140111010b00e00e13044200d80200411045000080c4400c000d000c0f0700d401a1105101003420f0b4003140007141e119516203100790b00f03060341c2440381030003c45c0d404400744080c0c2e44103007903644450120b4013510703541d4010070005140c8010840707118400f0400d4401c1e0740d550000d5841074a0000105a0b5440c0e80324405000354111703520212403480c055009101d501ca000d0704003800c04209078080308050001c4030820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 906762176 1250 906760926 906760957
    0x70b0307052208072918030f1018020102122a010504031b0f110f060403060b0f06070312020307020c0d0b0402121915020c070b19170c0d060506 63
    0x14000e50394140242c10180c00140500c4034884000054440b54002d22811748a2041d000500ca010004e94080219030415000d400c4909180c0a45610790750ba52101e88400d89081c54040440805502c480311703c0c0020350140e000740303419a10036210700c20740c0d8001007030340c000180d070140414545c811404c00360707251940c040000156460982405015102e024804000c00c10380c03c002040055a08442c0c1c074040d54202c079440e04110b02d041c0100e18840010740d1810b90009001c9400020480c4036001980c24030003d4645401d44843d80040c4651405880e034020081941c641c8c5100518107154003855001d80030348111071158070304102003120140c0804040d00d22407240d000b04003c2d820110301d030640080854008250f960201c40d00403020720107020b8001d1102400c580a242400000d806603046902d11500b40c48010f079440000b980290700074184601584081e01c68142c45901586240d840604074040184003550f6944c01000c6aa00c81c2d146000200e55800e0702045a071076903c05002143c108070380d803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 906763426 1250 906762176 906762179
    0xb091314071805030606010f03050403031e0f0e030f0406181503050f130308060402090607051204082a12010207140106090609090210051b330405070b03070522 70
    0x70b2041541500950b00991100c010310105991042c103083c041180e81c80e0028640d04ca51400f1805040b104030b501c80d810308040d01640c0600544d40c007102c07084510741000c0014110400d00e0710784034041e03100509000c40040c0420072000b03008485458055014003048516240c84004e421003030122130b120440002c5e66202000303146240400c21a40110300304865603c822481e40c0d00a0420000a00e130700d001e103030041001046602c41006680205038000b050321005401901d5000c840e800502c9003440c030f1301c20070410701c80c1c2c0a0300f04e2000d89041500d4144c90146803149060001140010030000502d43d4200401c001060303e41810ba4140a91400081091072404040c0d0044d0b6080d074020b14085480c008804c40181d403220280c0d48100d9540c284540c848065442a0034a510640c000b01901c2c0079070b10716510207a00780b00080983e071200d0074038075a55801c01018254101c0c000c86005140e980110b0f014015000ca4501035940440e0a10744640340408000100d1545084a44c2040c6500c0c40c0510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 906764676 1250 906763426 906763457
    0x20d0209090f0603061f0308120405060c04030b04020409210e010f03110316170a1401170a2a0303020f1b030a120315030f14070b09131407 61
    0x78180d4010312400300040341400c006000030f8403460301410004880d65072074204139400480041040085800100940d100c0364100c014007040f1600f120212400c1c021355000902e680c0c07101d0305682c107580e0092020a0280d0342c56091000800c200c420998425010001355508009946d002151403100b50361074503100a00034002500350a4a01c01075421f06041041e0a060404040207690f0300045036141007143d162496001d44918921200307241d000c03040c80c0708014101100d50070010104890f0401d020440c0c0c0d8840180c155100c0c00c03101c117555500300704000d0f808660865980c6601e031011440344a549000c4100700501a50664402c030003580201104640d010814403140303d00c51008180c0b020342c2052000002d03110320301090300411601c40d0404001225120fa03011f0f0071110341d180101c428003610fa04141200c007011620031122211000300c0a00e5841001c0b034002c1c229051441e689050400400402c0714030010007a940f41801d50f2085008500c400d131401850040c001c1e038603a4620701100a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 906765926 1250 906764676 906764689
    0x803090102101a042304030810120f060b2206050301291c1e2609061b01020406030b010207080c03120304062004050a0e0f04170706020d0209 62
    0x10010100b06140500c400002c2c1d548084050390140300b1100003416140c59245001c080c80e4030703441001800f0118040004058000a0460052007c0f8004001c01c59650240080c244d2141000400404044000c400001c0c001d40000da01850000d01c03c2c00d02403102020f174179062008101e641e42c2640c61710020481402e0a204005241402841c082102103001c650040720403243d90352135000384170b5581e4903011482c20180814165900820b054160f1091998141c0c0300c0b21325040a0340c0144030542403181120805400c64000a142c5800d81e00f800b040400b0011660071182807600b64043c0100f440219480c06c3c40200040c2085807000903070320b140d40000928061143d00101c00d00d51101d500d40c2c1039580c001820701440e401703c2e00d1403035480c0e440d80b1b001006807100e40d1840c600c1c1101c016101c0e030081240d90141040d034005803010002c682d600c0380c2c0e8060401050f0b6441d0a019020b038040340200320410700054044095442e52498080c5a030b03114007ca0b4070541140b65034a40c0407a07020124070b01032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 906767176 1250 906765926 906765943
    0x30302150907090507230405040f1104060f0210090302010b01080f0714090315010e041110080c03060a1205060a0f060e0c090d02030d051c06050117220c03050c0301020c1002090a09060803090102 85
    0x856040001001c0711060002034490b501035037062003014030351500706500c00c00501c800c60303003000c005118521141c50007070301826040003110b010071111000104c1000c00000694459002a6111a04655190080f00090784007082464041c0900100d0280c0c0c1c04030040e11030700030000d403082191146003034104010054016211248605040c111084085070705c030740c84580040c1d5035a01c1079a281c484100050351070140d0b500c1102030a04140029050080c0440c0051190a00840a200004041d26003800f11aa02e0050210009000c07000c58030704010300c0040d1008603806851100c900d600c81e000a844c207485014810700140c0005200f555002c881d12842140c2042004240501c030f09000018104a80d00b5085089820341040041c0b80301c020700000300252400c40c51103041741000d60405000d0b407003075400156942c5c40351501c0200d040c00c05108561810180d203020f000d052200b01c000b00f01952041a0030b50303004041850100e02c0c0303403e0380708180040c40202d0046a0f9015804006800d0905c607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 906768426 1250 906767176 906767201
    0x60405070c02030d033204060b0a1a0f040e010f09110403030c030c0203010f0f020c0c030a051c0207080601150e040527031c0603030215090709050723040504 69
    0x12074000c0303401600e00080c0c3d03071200340350b0781804120030402403162a0001381c4a001a1000e012004004c444040c0310039641d40164000d050500c00c8004040a0000c0400c00b0721030b034601b1450b642c8480c05031051000280025140940e0564039055940162408a00082e00b01440da00349901080010b02001d119038012103001c01041c0d0304007403030340c1c40c0584694800b0801409101000c0850000c5560039030107a41c20421880c000c20903503c50400940094012100c2d1307c1103403248566921301d0b0320f40051079001c0e03d58400e00038449007017603803401ca425040c0d5030740800c1944103d1001055200c014045079029003402c0c0c00f0720302c24040c002001804004a041014002c2d413510042c40300c141e200e600162240b44607540c1104003040e1030b4503ca455403145d648a50b01d1a4505404180000b96540110080702d010713900b180c1541146001051012205031141c414640c0320444c100611002900031650096072807c080c500e20030031010309441c0039140300044020460000c2d0500c402d182030701c603003030031410f6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 906769676 1250 906768426 906768437
    0x902041b020613080d02090301021c0204051309080f070203030403051b040f021801050c030913020301050306160e09100e040303090501110901020a02240d05010306182a08030f0306040507 82
    0x20aa120401140b0030b00680b90f12176500080c1d0407419403025012121145c1c1d0141020454178200081040250441c3c0a610310580d030001e05d246260401d40181e109403900614170302e1422004100c0c0429a034426102260140414000000811020300000c8a04440c80c41d00c1403885038001c01f0801241c8004040345c41c900c4c418440e11402f030103805a103104000303003820080d540d412003140a92840c0580e0942c2548510b001c550100102455005075040314001e6046601c00d40b6404460303040c010140350700800044003441801d105241c520022a04442c880410705841c94950000700310f5030f60100c400341c0221707850318070720402c003c824410304580d1080e0750b071024202048540000d4030760aa2240c003a00c54000e040b0341c0503030344061200303024403040d500d858030b035441011095040182c1024442038031441e1a10034480d01400001039020f0819600102c590644003485480c41302c14000e00c020350b2041e1180c2400850b1208003000241481465400b4854485c500b402c201300036101e008003880c08020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 906770926 1250 906769676 906769711
    0x5040b0105120633040305070b0319090c0b0a030b0f030c101101020c010203070c050c040c050d181506030203071205070b0c0f010906020d0b011707050d0902041b0206 73
    0x542d07450300c980e003001c801c8444005510408059021042103036282100048001c041040500303500c00050041724882c03010342c0c0840390794005a052501046a401901c0070150f4880000c115050344815041481510400034541d103a14842810f03411208445001c130303590382c4e02c0c52201d151400007480307106800c0b40123010112000780460306800c001d07001203060126072200380b08550001c1d0169003026074580003c54a903d4105401028020080c80555003801016409807050815005005040c007858917503501c0e101c0803a41010040c41c8884010703021103940141304001401107559403502102c1c10801240c4981180101800c0040c0e540c8400e210007505c05160000410206240045400312402e1702d03140d0300c50611040c10000380242e030b883e065282c81c0c2c40c0030030401658041d01d00004102d03420800c400b00301e401076583d0400000a1800d078100d00c0005400144603000400341e1703c1c50414003140007a215408641034500070304c0703c8007800d00c000310150300c12641008030b281d10040d80e55001c03100a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 906772176 1250 906770926 906770947
    0x11010c1202070c0510080402090109020f180609090f061305011520030d1a030d020a11030a060e0d020c01080f06040c0905030d121d060c03040320060105040b0105 71
    0x10103010542400c000d03008203060041c0454285000000e02c0080c044805042c0c4081004007001403c440807841012068004605800c4034400e55000c451040b408501e4501190310710b100a01055109603400300c02049a4035080e02e0354603101d8050104050032000c0c508228040140740b000c1203005000c0145048010400d203150648440108051805c10a030000361645030b400000703040f0500f001e01440700055404455001da400205d800031409908200004031f141010380b281d03e910000300040e4082d004607c0850401034036607090b40350082c215600442181d4a15082d00c01000c10b0f14030b590400e400200300e80e60140a4881e03034100900c0d10200714500000840c0d41c40c88042c0015004541e26000c001046000b042c0d5800940342c02421940c0b040d40e607034001403480992854503c00c8a08000324400070b9a0611f10481d0044c0054001e4440e5682d461524040c90b000100300360208103904040c0f444510703125200c0c05003040341e50080d00346c9604140500040e1803840035420704002080101900b403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 906773426 1250 906772176 906772187
    0xe01030b04080d1e0e0109051e01140411190509040b0903040f0b1b39132306011713060207260304080403080a02010e0607021f05010f1a070602030a0c11010c 69
    0x10040b219580c0502e503561001c503c1c1c0103010001e01c1c00c00112f0140140b00a0003440942079862440032109140c82a002c02c8182425214070b2049a8029604901040c00551608401c40d072103040c01342240e0030f19583d8020010340041c1e0358000c520b44080001e6500c408039100d0700b0a102010340000408500200e46102c503403411422049020940d8200200007007120941d50700e4100420060846075180c01d00034030500109405084280c261000b681030181103107407924601c0c40740790b05031a0f950050042113520281e920004054100042c48102008000f6035244040d20505004058000214005150301e011480000200456146080c07040100182004003213a01740c952104860340c0b114084081a0f014106001d200c07045030040804201105500281043c02d203011340b800ba040d640501c60400d02106d40a014515642c2c6000400b0701560b040580d100d00c0068903815464a8900710340c035680100c0e0419a0f01c003440301c1e01d50394000441540b0403841c0c4200f4000034000c00c60003a40c1d2001800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 906774676 1250 906773426 906773443
    0x60902121303020f0a030824030d030902030a15050103032d030e160329091c051207081503150118092909070e01030b04080d1e0e010905 60
    0x1249140c0a0041c01010710034000340191100e42c1c4c007200c805828516001d4110728088541e0f03001803c01200200b91240010007040d1400b1000c2d0140416a160200441c050104140140c0e0036116082500000a0481c18642401c80c042000000c055042d80b50040485c0300701c1c0c0c102451103802008828010542000d0040030212a00f000191280350049440c01d0500d61301120481c2401c0c480d0020502c541255880f5425005080d4000307001d1103480c1c4286403540a40e01101c0c0c640c07154100085001c52000510b0344600340c0d08200b803c1c0040061449241c030030444900700081c80d420140f08595400810f5a4003011044000d8907900d040c14200c404624814800c0507d404122040a134200e13440ea0310565070240c008219454000000a0005802c08029004081d0358210800140017800200e02e8106a0364000c480c02102c1c0d2a5031100a245100030700180c4240000700a00c0c000403445e449888003035405010411181e01c801500a07003207881c0b1081c44142a410403110a0014402181604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 906775926 1250 906774676 906774691
    0x40b0c0c120340090e0a110618121005060906060a140c070801050f060a081902130c021e0706021009261e0702060a0c0201020a05060c04060306090212 66
    0x36541184511000200300f480e24882d11030010b01d9440030a80408481c01109a604a020038041d00060842c03c681c1e82401e4a4013030107820950552401c203181035002031804200811195106d455140005420150100004009540141001c4040c42858000c15a00160803541d4400b103180c800041507240c42107140c8a4100007242990100314044002036404020810081364016600e0b41d0441d4000c4c00f05840e0314a106400b4000a506894540e02c0c400941d62031350003910400880e000340910141002c0000c99011b0803141c240e81410f003141c441c1925004580d40100b11418219000b82e111942280302c01440c0d81050400f0711169800240424074222101400200c04105007840220b0010210480c050800c7c03c81e00c0901c00d4102001a110341c0d07500040100081403000c8800240e4454003a00940164040c8490524107000d2503a65801600600617174a045441c0c2d81c60358180041220004424000407805000b4903515110710009003010f420700b18500030003940c441e01268001003045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 906777176 1250 906775926 906775957
    0x617160e09040c170f0f010203040807080c0a06052401030e0715140301082a010c0b040615030303051e040b150109081006051c030e1212040b0c0c1203 66
    0x1d080000d1003400c20000c220b402a201804130f90784084e20380b542100f00e000456489010041401c1101c1031003224003544e8842c0d0303680d04e4120030b0b41d074110451300454681d800c01c0c0100b031040b10110386107000d01c9101e10001d100100707640000d800c040e4640110300d0719280c101071401080078141680000d0701c1040d40c058005050b89905040000c41b00e40c45055244d4520440100001404410026003814152503014043d04020f060122118403010b03800d60107030000b007125446401181d807221940350028020310010844540041a07a03481004560084000076520b604015002400410068a09100345c10902c0c072030415880b001024078010700004682c055021240b0500da014080a4005040100607151540c20884500006013068454035000b82d0345200c4400550620403590084182c0c1a2a5242c0b520360380c0d010301070860290080c10245110b500d4161005c1c071140e0010348020009501403d07910090100c166007040c0301c10344464021b10f03c00c401c1c40454003002c01136590008410070b11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 906778426 1250 906777176 906777181
    0x60518060c0f0111120c0c0601031209030f050d02060c070507031104020c06010303110c0409080d110409090c05120f0a170d0e0a0525140a0801060617160e09 69
    0x200d0300b01144800080440e611300744848074440c00040140420582030b10000b0b00c41d994400c01c1005174424040301c951603030460070050000801099100340c0d440824603149070026240c2e42c03416170300e403102d040640b100d0340891495042507504110042e8458606902d0780c0c181340c80c82e5178441d541d6200d0f0000805002c140082d0412a440e2a41904c5005440c0700845900303583d02d042c0035145a034940300da1081d074043d903245901035007068003c0e01074580d40214001e03d001136901c4100c00622400040380503c410400000034030152030302400b0030386809143d2040781c0924260401c0f140c4c68051030050081d81010004040320f8101285042c145500421400200c16148903507050901c640903d400c011072502c2c221004d084000220402401d224004480340c02c44081184060720011203002c810410400300306110a41025901441e1500301070b004041141e04c4030b40c010b003912000e130070000c00146413101c0f0890400221a40a412949050340c00b03041400407000140039440270015603006079403d102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 906779676 1250 906778426 906778447
    0x105071104090204061710020906090f010e0424080a0503040b160614070f0e0f0609012001090c0e040b01060c0f0506180d0908060f07021f140106051806 67
    0x2c25007503980204100a80303500c440e0100204440300802d20300500c00c0d5101165890300d18803c444289034020f10311380c01e2142070030400001110301c52401d81080f0080c4605a0140c80b64002d10346810100e807400340320203100408146d0400c8869100d030314154000c08912010620201c112801e6232900040325568451400f4180c400384001e0718020242440c0c210041072505692548a00403551544c40122074068848126008080c04a6159100c01c0303e521964140c640f0310000c02e4031702018141940b4240d1034004a04068001245a0007140d4446002c0402c00c1205120703240505806481e05035141440e031640000c1ea001400b441c02423102c081c650500340500c1021a00f01c1960010840d501858001c00401002e00b02500c11070380f6200d4019488009806030810b002038031161001066140d8071440060746401000c0d1001c401d50052031490a8032030350f03e1010203e4100c6e50000418144040c14204840c07000507445101000303402d005030b01c410000c014103100c00c0d42044a8071619603207000c6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 906780926 1250 906779676 906779681
    0x52704083708010e040b0601030506032a090c070507210b09070609050a0b220e01060f021006150c020a1d04060c030c05270a03140d05090105071104 65
    0x802180c001805041c484490920300c0c02501d0003481a503030450310340d0344d640c41e400300035105490003040c2240150010f159035100c0e621003980000001d048900d0030510f00d03848050340380c03000c0c80e21022105c042c55034030081c10000030454000c40640c4040b460b100090703c3e0300da10b03600903010700381304419042195128094030106500711550040d80307100641c105801c1841d501c000910921000c03030010100001c4916040b41c52104072100780c8082d078070300203000c004a00d9010308803001c03c101d1441c81c0b0010071017506960640d8007070211a00c8030011404c002c3c001a20f0278814590400410341414000c2c031442943c0c0007690401d01d003e080c00c5803502900d10001d41c41c0503a64004110015070b038001602c100e01004109405180290810828000b100c0011400c0d520681e80300340215108114032400d48882786580b041d04045240018400550280001c03000d821703990044d01c1c0144400c01113550316109008180308401c46007440d91401d407002c0000307007040c02485400307460440da1a0284c5025101d94 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 906782176 1250 906780926 906780967
    0x1204030f080f0c03090901090605060f070212030705071703190807270302120c030303010b030c070c03080306120d022a090106110723060a120906020405270408 70
    0x600a0984030042d00c010303103a0705e402c030204030382c0f1400c044000000c03890359034819041542c401600b02031601c56901c08140d0f240d071000c03d0072a000306c4803074450200100148081c007620f510410251410b43d01c0d04044002146511845030740980081101c401d011105121100080308141042c0d1044d58820b4401c0d14525111800384a03004240c06d89000200031420324402520700c210340b6050b589003412401941e54000142c040e825500410044c001c810030700024503030086008104a00c0c021056858102c96201030b4011640490080b080c010185840724550583d40e0074100103020b4130307444850007507844031040c1056403078040990040804400e840b0854480c3e9a0262844c4125690340c94000c008046202481c640c0e030144410104920304403c1c81c0c4480003210403603503058482c210081004541c052000b407002d00181030219040d81c105030140030039850180100585840c607040034032184420150040d03041556000500c040040c04040e080e030003641001200c0d84071504c148203010380c400031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 906783426 1250 906782176 906782197
    0x13150f050a0e070803040e060f0310060305010213090510090213030f050a03030c0801061e0c292a1b0f030319090201022e02040e0115021204030f08 65
    0x40c00d080100203141c0350840c0c1e00c9009407604585205680c2d455182c1c40e40540c0c01110010070103040481c03010b00d00a480e010001c0401810b0702c0350300c42d0500608007102c3c10b0b0b80c800c5401c4d17500400d640000300a803442d02002031260410a200c40e10b841080d5203130302d020700c1c000c54800641c003044182503c440940001c029540c0418a41e11030701541c10210340c0e0b440d02e00d03c1140001d04014142c1101886100303101d0413940303c1e842e2144030340c42140750840c03a80050005d00d81006808010140402c0c0d0103044500001c0341000a50b803c162441440c04c0790040041000514404800d0300c1c01d003441c031440d03209440c05039061949403140807002c0c141c05102c00b120004055485144d40c298245440400198061110f41c038000c46101c101c0007001c015245201806409038210842c045516110b0800c0e0200600c1c2000754082000e20607860711007203030000c0e08951405520040103002e00300040d400c2c41d10040c49070000f801c0001c401c0003055058803460100030300440c2c02d10901c00403c04420203841c801e810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 906784676 1250 906783426 906783431
    0xc0f03230301030611041511120406031a0103180b13122703080d090c090222120b0c0f0d020f0306100e0a09150914160813150f 56
    0x403040884000340d0428007080d151207181400321003120003003d08460071240380c012002140203080ba07042d50070580304101d030307850390207020300c040d602c8510300c0300034000b920564070000ba0030300707a06100c0e08581702e01040d1103051600d892942c01c1a18280d250202e44241c2c0090051100c0ea240e00d20581c0d2902c00e0840140841c10319808100d550f600005451821074038030300c0c91200840e6503010029a10503070322003d0181c003810040303040c040041c0e8101c920b5041c0201c1c0001030301035940801408982c070159108010704002182c4415640200344520000c043e10101c0090103400e68486d5509444080d106d00314601c4000344500a082c2c0d2030080e140c1a00318204215100e40d82c04802d2451940304640142c03081d14a240c0102c2014020603200900b4a00644601112810451910000c1200c4048404682d642100024030031513180200b10149155070342c5038a0718181465424000341c5849014014822041c0800165080d10000310305096045009170785042200c491f440f0045c02020401c141450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 906785926 1250 906784676 906784727
    0xb060409020417030f0720210d030b030c010f1404090f0605120607050c0c120f07060503041e020a0b0706150503030a0215041b0305010b0a050d030c0f03 67
    0x806580500212050401d829210314031030500b20340c0320302c0b46480c404240c0c2c4003481111b0110300c21050040c130500002d000f80c0341b519010700006900d048805814403181c140d444040858041c04c2c0107044120415040500900c11315000003912100e02c600c810f41007000500c00000500d100790b4000c00400c1803109210360b81da8954010401605003aa09804d074503082079000202814001040501524a680500103e440c0c4020864040c0c3c410040349503035124220240c0065940c03143c0314095503c3c6d032401007408003400314415041000741c1d400402400030500400002c61a44142d415100040240585032420306100180122840c0c1c0c000381000710340800e01404100e074030340c030000c00203c926042d170015654500405540744105408080103070001d0070460b90500d5401541030300240304e5001103100c411076202c511241c0800b5441a5010b030746030b170300c100d800e4180035103060064a03080e40c0000801c89a034501074142d10320b484000b0900507503000d0380804e052054100050102e52a4080c0012a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 906787176 1250 906785926 906785939
    0x1021c030506040b060901050a0e1f020c0a12050d1116031101170601270503030c0d030e16060f0201060b0a0504050411091c03050d0f140916090c030b0604 68
    0x10003080b107010340150318184410049160034019203c000c80d0503558286400b80840e4111041d600800b07070315411118081d031229504c85410b1440c1c41f0032800754018855003000d4000c00c100d1480303661141c800254150b601c3e0000c1130000c6503a510342c1b900e80c2850f40001d1b403d406000d1510040810380311882c2da80a4000c420400c3c40d07104885080700076039030b00302500c285400716000c1401c1510b1050102d00984188040c40400c0d20000300c000c0f803036001d180f10712940c0360040303801c2d644208603032403d5400811200811680600c04c0e050903002c1b650051240c807200d08061406621240640c2c010f01840802d812401d038400d40100000d0729002082e1916511512005803007078016000310b520a0741004070f080c18184818007a00e4a500c0c0007402145080c02d41c0c1c500340c0032000f01403c02c5d010000d0801c60070511041c43d01a00f0300c101c02d60000022a0109918480035000d4003070242e4220340c0090700400c80c984074841000094a03611500090384c800c4406003a4000c2c108242c6c80b075008680840c0001e0607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 906788426 1250 906787176 906787181
    0x210050a05131203031a0a0513091208060a15170402190303020601180207080a080c04030b0108060a1d1005130c031203180503030126010f05041b1a03040201021c03 72
    0x1031312989061101003d00b6030700900d01c0741c104000c40e030030070303801078041026203050001074442100860000907054290b40368101459241280c04012603500d60500c801d034100110303810020712400d075550840303241d030803401040f405140080130105001c800114040d5603c40c0c000032480806030891460103982c030b02c0c010b03444643c01d1041e5240c03c056820204400300080c001c0701c2c282ca41c80348006107070508030382003991000c1b005444a0000042480f0204c005419021414060304050300200058a4642039450a07a000845900780041900c0c0112040400004602d10317400b40142000c68140e803601440000c40c4000034002e041076106c08000018000c1c1c01d90700d5001c140555034180728052004201003090340b000900103045a004100401040c4691041c1542c00b10114145000041c032000f01d4034207403003010017051303400d6964109000030009604d00c080e84001c0603841400350580381c207100040707003048052030349814540000043e08681c42480110220044140d10b42405a40104c00400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 906789676 1250 906788426 906788459
    0x18040b06091b19030c090302060306040903020106080304091a040614100302090d11030601140d06050903090409141b0303040902090f030a030f0e0301540204050604090210050a0513 79
    0x1117880e100c845500c00e8800c5042000303680d00902824a551100c0381403000810754070100390115580c171080414401c2042c4010002800c6010011135814150004184490400002075104601c1e08100b000030742c105002120000c001100c07400414032500800358080d05c074030600320b5409070319094501300b044200b4a0141c00680290115940c6030b880310301c40303c4a140e031410700c254015150100940040c2c05600043c0c3c1c000d002000b40da0415007803802040980e0091442102c0c441c14130070180500c59002c00a1f80d0050140c403100580500854020a4491183c2d019101d5025000201c511103501c4003050020546c00180c11220040c000c3e0400038001035441c02c1b0304c00083d520a81000d442e1070305006940c3c14042081c1d4516814000003088040169100d0721107040d1220581215120545608500c9106003507036103001b60a0301e180304101c21200020200b9219074036001c8840c0143c0c5a10fa0110503c003020300706155a0440c2c04000e0740d0307030701a43c1075a4103441c00c002c1001c10405042c80d00f020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 906790926 1250 906789676 906789727
    0x3040e040201210c03090507091a090a150b07050606040c05040b07020d140f070b09010f0c0f020a0b180126100b0313110f010f050d0e0708060618040b06091b 69
    0x99900c0d40755035486060360b080c441d124007200032428000f0080e1810114198111204080000354801f22076014190824203501c1030030008003f003500d0303080c0982409076a13440507003114104041000008080e160b4000c0d4092020341100c0499000215140c0b0004900c00a410410803440e200f00445115070746c1210400d9002f440c0606a03001800b0381d00b013130990303024182c1619a0300254004903021154000440c60588462040244110150721204080000b50541c04101079072940b08050101012840d910b48504204e03450152440c0030507d66052000c10040441343d216945070840d600c07107031031001c1c1c10030700e034111002051001b049100d01101a1070b91161001c0401500440308200c80c13407240da03080601180b4081d07440d0306420322840c0140509200a100020050305408c041440c10240340c01040c0d442d840141404020f1504088212081049030b07c108690b25080c1e41d034000061010301224058012a4040355526030300703104021a04640e84602034540b022902d001403000391100229 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 906792176 1250 906790926 906790933
    0xf040f0f050f0307210c15020a0c08070303140c0a051608010501090615140d02040e01170109030906030e0a021005031b03060f0909100c05190203040e040201210c030905 74
    0x100441c0c100031444c102100d1409032070201c84800d50b00e015000718410f55048440501d0104080f80c551424840c803424400c0944c024401030b182840c01c820810a207411052840c3c0c440c1204000003644004c0880d50140c901c030180c0d8441d6030021500d403a084d4800ea00a181e4007640d0700041413006c50950b40c10071142c440c0002c0c84166aa90652401c4a0403030149040b100c685034600402c25000c0c080c5414202e422098041c6071103406100c5604030380007900400440000000100450a00c2c540030ba00000c0481c00208401031280da00940f2450182c4291004e064440b60f280c083d5183c1441641c6205070068003010410405140040c159801101da28000000090002101d2032258003902d01c1000c000d01f00e801000d65034810001c0000c2c0091030b80d400f9200e541c1c0030030080036082c06680003168040d106c03e40c0352911240340200e40340d90000903804540c0700f03000400001d00d1000300250030903020308049540101104c00405080000142803903014107000036108801d5242d07108440003800780096 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 906793426 1250 906792176 906792199
    0xa02090f07080106030623010e04050c1e0306101b05030d0e10090201020d1206120c083702040917180301050903030703020f2104021201090f06020f040f0f05 69
    0x317400300c4245002d020202d4440300c00b080c416080c9501e0704009003805060405040d0803030b00004040e91021a00d00324000e801050100201a9250080c060031940180e45819443c088001c5910480c0c80109203042095100340b0600f0740c0c92641d1008074468004040e03075501e0750340d022001d01400b210541d4843c944a41c0c074400040034418414401080e505034003500300d403400303060111000d600c40000300f21810307921a00041e01c00090083d2031200e81c0f00f06100c0c0303449071030603030150b0804229542108031311608100580d1100b102000e81c0764920413101c0742000381038041c000304000f403000041c0107005986488040524207142e2000e014a0107646e9208075210780d500050600f641c0e0203581c5000541d1003800441c181b58081c0e0003520459420090542c18040c0d106d2040c40403500403045034141d5090345080c032081d0b003000d0300e4900b0944d40c0603000303101d200760070f40e200c84007180e422038003800080c0c0c0421000c55061040080754020845890f1200c0041e40b10303100b449591039540304007403140000821 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 906794676 1250 906793426 906793439
    0xc0501051e03190f0e0c1e13180f0c0501090b0f0a18030c1a0c031801200f06150a18020909040b04060c020106080c01110a02090f070801 60
    0x89605810307280003195500501e14141c05555080541820000341a001503000180118841c5056400c80d04c60045941c08503e844c00d400d143c1110112400381d10000203030003000840c00071515003080165103d220b1040b04d84018001132120780c2040159180c650001801d118030400300000b214020701c05440015074030001520009107a10402801910601403907048010b440c003e081038040c1401c01940d40718100c00000071002042d017080b191201298414090f01d42144100c03a100380000030140d103001c10aa20a0390789020701d01009c20710a9000d80501096446614904009401213460180c0c403801861607540fa0761214a40581600c19074000074030f898140020b00c204118040c000119081c14607600188104a820b1144101c0b42c0822032650389444100956115070b01503402c1c5030150819150240075510004c2016046a040c454140170002c0089940c103440704c802d0070183c02c441e041c0380c011420701403203000207944010140100300070304171140745580c810141c554402c40940e882d60b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 906795926 1250 906794676 906794687
    0x90f090114010e03010e151801140a0c090b09040506120318010206060915130923011a150d110c01020304050d14030103020607140604030203091c0b04020904020604090207080301030c0501 82
    0xa55181c650b031214500080c4120030601c0503070003845401105041c1001a46509c0c259040450340201520000301000101402d034481e140306115103180c148601ea03d404011800d5000f4030b161140300d07a648501080e5180e030703a41000000d46a4038002d8035200e1800c0c100b40b18030003a44c0f40b034880c0540166000504149001e84030a031050300d81062501d4404080018401c4000c0919880c2c11041d07a10000680411303400b401101c010100c0c0c2d0010a00d1003185c03140725080d40d041419402005030007001c4a202980c540f6861402c0700d002140440c1c07280b00e90720783c04020b003c0b007028100165400161b031381004901900107500c00c502601c1111520018103a00700e40607c404080721030100c800340014001442c0043c0180f05080c01000100d4190441d900011304082091b10304a01603030001032550f001d410089240c01001c050b2640d03180e030071131071900c1d141d050200c0240f00921032042200010300310760340c0e00c0986002d4075162800710744902c4c4a103000e004550080c002034074211405040003440d507214a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 906797176 1250 906795926 906795941
    0x70602010e010b010503011d1306020310031415070503060d0605090a020a170601140105090415060801081b0d14060a020903070f050607060c031e06170d02030708090f090114010e0301 80
    0x3111644c00d08e21117440031000e1000003400e202c0585800704c6008d004228140081c5014006402c51081d00c1880c1d854480e040003c1c03294003208a4000c40b81d030b0340640d000c1441e0198004007505000750740fa580c03140055512600d246000b4540c0f0305e40410b002c090030001a400300040d209403001186107403521000340940700c030394102c418150710400040c407542510610541e0301c15018103201d41000d0010000401b540c01d131031a0518601d03090075080003002da0000940b8018900140600785d10040000840d0306280201800c0d8062508440c1e00740400c10340c8019210040140e00545509083c2881444040d52241d007001d4428801c144020401005030300201c0101d40004146030b1400c0c00941d958000b0b020803484201c02d140e5900b070300d481c0d26480191800c0440c03035908400503945041c03183c00c0944101c4802c100c107150b8050b0800d0200d0503000011110440d8022482680b02ca0341c0400040c480505544119084002c10000140c005078841402c1d040303040c2600c0344000065448180b40c06c03560314 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 906798426 1250 906797176 906797189
    0x110f03010207050a0809040b1f020115050a030311070801051f1505040501030f15090b0a0e0f040b0c09030d030615020c1c0201030605150a0f020c060d020912070602010e010b01050301 80
    0x131124900003814800100082c000190000c150f666029000410b104200090908010350f0f9240010380b81da070a11030380104404c409040d003103003410180810310010042c0002010711006052103c0c190408020120051280b04024003561a251860307902901c1460003803a61300114910214907a01c100388208000c0b9000e03920982890314080044026294600182c0d1140b565510741e0281c0240750008140a01201d80000c00e002d05640103005600140703900540d00c0c0083d02084c400c134042300c000c2d15900160031125884260b12074a4605402d4031a400c50790340e16200d00c0c2114000e81d50180c02c034400f11007c80e0320b000c9010310901801d0740c8480281421551040500d040f002d002c601040740000b00ca401031400203106610f0720080741850f00000120007056902060350000c05030300402c00fa0189416102030310a10160038041101d6000c0c0c00e642d40b4541d034000c107501d501601c3d0050610550a900b404071a40b1030341d0f40b40007074005c00075400d048a85501700710021070154010000c890480300b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 906799676 1250 906798426 906798433
    0xd0507171f0b0607050d1d0d0c0618092a020d021218130222081f0e031b01050c0403170a0224012c0f071803110f0301020705 55
    0x40c0c45840707400410b28901c60b07a502000070300c01c40c808540700300800c8070303442416200c6e246022642e01d590844400d54504040c8a484110210340000710b00341c0e20300d0200c642c10304111015a005052155030408260010f41000f880c0100d40d00b0030068103240ca80034500c0740e1070100049008a58103d071580840720b908000750348401d203410a0090950001c10504849210514080c0c84100006561041c4039441100407030b00400c00da0601e1004000e1002d40d0701c40b040941130654948101c2c0340d03c2d540d4600c204045015000851125401325401c144442d114034401c2d60765411003110142601504d56444076034035842e05d400600c10884c03000444050301d411401c9060018500500d44055034020b00c03c541c21405400b20f1140b10118084141580d0f8180038070520003503040c0007400c0da84aa8000124803802ca50381e0800d2115180007460302e4002e98400801031085c0c2e00c0301001d07100e0048003210a0000c29548000100344a290b880c442d074950f0f01101c8510219480c9400c00d400e034080c524001d4450340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 906800926 1250 906799676 906799723
    0x90709060206190e010c03020c0d0810170a060606050d1b020c090408161a0601020313030f06090b0a090501140702150910020a0807021501080d14090d050717 69
    0x188940d2284200100d410f00100304190100040d50035108900c0307034400484d402050a8040100c02c0c07110500280283c6400c00003841d182211200160f000e10034100600012100b00700340d07203c00d105020b14190131047c1404a83d0303568100801c00d9100301c24514103030b071900e84961911540754401005100e9103900030884402e041d0200300c042c000c050401c484000041110042600c04103581d09919030280034001060168003401500600c801003280d41150810059110f00081200300700040d00e410060722081c80b106807910313000420300c054018200d29019010040000c00c10b800c00b03400c09119400034800180e0b5100e0074080030005a82c6032026030041042104414080240d460f070000000f021a17410014414000c000c0760f0000e448840040d0405040014042d01041200d400812810390211298540716902e5200c8112040c0320f07040042c2500309403c290600000da1b401c02030005d10301040da200e18030b000340e66080f0030b108801c00c1600161a0302814100881c0121002c19542c0c0b0945008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 906802176 1250 906800926 906800941
    0x510090209030a052d120304030507050124090c030b06070219210b07020c0a050f0102010b0a0b0301092a1b0b0a050f2d070e03030711090709060206 65
    0x29001082896014803c002011001c00c404114200c05071540c50382c030a11003c034502c0581c078981c09480401103d0307485803510341030100b500d0301143d42c400d40516000752600302500d4203e02400542c3c181400341c0c5400301148140240c100c54003001c640380c082301008031540201c801d41c252105102c8080c2c0c0400c050001201500b000000c0c40e03000e54403c1c1d014417603507840d18405200707054a07410a02c012412001040c0811251145d1150800c40c0d600043c1092084000051114039890080314041d004600c201c1769a64000d4020080c20507000b012051241c8d12031400380c800d40c1092207111340450611618010340031851800041c000f8441101080140c58030500b600c404014089400420700810614801306069005640c05100f40d51408903407810464010000000c0180c6800a03013200000b003403d50490031101d41d0b040203d032034800d00d81552081802e944500c1402d17003076038160200080900411a01200099883c5402c40d25455030352101e0340d0031202d0024502039940503900410224610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 906803426 1250 906802176 906802181
    0xf0601050409021f0f08010e0c070609030207080f0f0c01080c0d0b13110c011a0d030e03030c01180c06080f040807150f1a0405040309060c08070f0b1504051009 70
    0x306002038030132070071007404000507010114100c480301c2c0042c00a202c0784260030340c0000380500408a103643c82c120340c14250100d507400c5c0304200009101d16035800c05041018020303c01d444c010301408090b00d4440702c1501003581c41e400d00c074203035420901440c101c8107111741c02081050302650310101c0090400c00c50454a0008100408120b548194018030b50f0300c3d02c40060040f0602c801d14000582d8440101d0042c007030a458142c0005030401c0900942020b45131a151803d407034643d018949254100ca148001c42c1c01d5201301e4006e03a40d113509024540d43c0d130301c4402003504440b500c40d0008071b4085950303400860b00704100366074a01c4c8040307420021070045860b110190403017070700803d40720300107060a0581c001220703e451031101003107031a00202c08a034194945a0303d810001620140540d1074250f41c000c010100a000340c1d000d2041c1401c854080c411b118095900d01c982c0030040c0501e40c44142048006608101c8920304004402c0e81003000e28140340c0621401041070450100c0100e0030035070300901 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 906804676 1250 906803426 906803441
    0x72001111c0f020a0518030607020c040f06030203071707060908031204082109150412080c070c03210203190e0415090504060507260c2710020f06010504 67
    0x41c03154807065100c0c2500990b10050600d0b240c50b4444a80c0ca880f41c501d01c5080e92881040503200b90010410041100d40108100c02c0911044800052b0b40c9100340d844002090240c101942510a0040100318200c00f0342484440c003890008440e0380654840d000c407a400c485016407203141d001408951244900303444e80b6501301e840b0f4180541801590031b50420084030080c084c3c069000d041081c80041601400000c2c40e60301219407540304da03d090b840d0b03140090014420701d010014001d000461040181050f02c4903aa44101c2d064505562410f20782100e40c0c2c1009104604118030002c0a4007d00000840d60741481108650780c80d525898425540420b07404502c03030300240c03115040790310300022584482c05440e1a800005050a06040060485e4001494403080c4044058034503130040034030b44890411f001c86070151840c0d030394980c500955030080d2183c107414096400c4404444c0411100071103000c44040d01d51040381010110201da4031400c40d44580d1550b004030700144480c0c10243c0040c030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 906805926 1250 906804676 906804727
    0x100f030c09050d060605040b010531081009030f05030105130509071d01030b060f031b1306080a1401051603090501060f0806100e04020604050609040b040507200111 72
    0x200c030b0351040410014002504211003d5544a4050213540b4280c414411656400e00e0700c0350406500700b824200420001c102e0020110300601248039518880103203d0141280a060307074041c2e000c1c44039000107019074840031804962051081d0b40001d00c0313030082e06d04894000b00b4082102e24842d16850040070042e04160413800341c58000310710b420f05420301c1c07500344c114000d000c030780742d891424100c0413035601400040c03103082d1200e42c680995034006003003407200f000d450b01d064241c000040002c80e02a900441d6090795801d0080c00152000b010501c82c03d05030080c4c4565414002d00b00b0590700325201111900e4244070002c03800b042c610f01c25030020145920070030001550076100c440b501d05c0400d9035030119003103a10050401c03c410806103000d00050240e0304291180e4103199000542502403402200d00901002c03c80000f1030360380b50800502d820025204000e0382c1010540109004804803404040c1c10342400c0401114105200f4044c001030508419030600c8482007200c20090801c0e200328 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 906807176 1250 906805926 906805937
    0x306060509150d02032d070b16141513031e091202151210090908030a0207030519110c0306100b032e0303030b0d020d0303021c0603050303040b0105100f030c 69
    0x40c0098052203865503049030140d010300ca206c1c070760001d107143c45040c0c0c0000701405d409214065490011400300c2c0704981d4016441c100c09096020410320340f250000d04010160f29850610180d4040c105d40300c01c0d0036000380d95082c0241c1450141c444148460091000065480b8001700b084c405845032070440144000c28003c80a40b0712800402c20780c209500004000c400c8100340030100c4e800000d00c5000f44290f660a0000c0391203501e0380070840c0002021f1090607500042c00c1403c1501c1002100e0a9241402c00c060068000920003843d202e410050f0012a10440303901d00d926260001e0340510900005980c0b03080319040020082190701f0241c030000d0514100c40914001c411141102019565484009400300c0d15605008056603400314060b8052003d007403900000da00c0300707680001d400390036040160750303150a54810ba003498141a00400c01301d24140000c810840d0200046001d00e00800c1810b600d0790300c51040003801c1c1758041c1f01601060142c01da1803900740c02500a14001441801c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 906808426 1250 906807176 906807193
    0x70b01090513050f0d09080a0b010b030a0b03010f050a050604060e04110d120815040c08060108070504051002100b0307060c1506050d050616030203010506040b0d110f040306060509150d0203 83
    0x12145854101c2ca1341288980042c0c0036250115409040c400080010070010401644113446149040301c0600070407000c450b0001c0007819100051300442106e1101a00801080401e004208024081501c000060138140400308a1030310f030070b020300025103e580748081000c0d1516520001c1ca41d00001c4001d0700110203000c814041118a41300351002500313030b110a10701d0301c0d10b412400391080a00011500c55490124450304141c1d200d02000d510280030b08140d00c5e035403a031f9031054505014503401f440d0301070724602642e80e96940c0402c00e02030208034150305000450784c07003040580b21030b03850047d0400038800b80017401c0461022801050f09644144001030407a4541001c10035030882c02c1000e0324a68806c10500c203c01d820802020108115407a04505550609000a00610491007844210031000c01d8002c3d40317210320790101503041e04000d0090380e644186440200c1c2c58210b031000395400d078170b030150008460914042d03841c8a1202c0c202580005c20880040000b2840d0f1003400366054481e0304003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 906809676 1250 906808426 906808433
    0x90b040b060708070302151e04030c06020c010b011418100c05060705030405061303440601090602010e100f1d0c1011030a082e0e0a02070b01090513 65
    0xb01900750103a4240c03aa1040c26040107450207250048130130000000300f04126600c401402c1a000c2106090039189a50300d990404a8110382c0044010700b8942c800614450130880550144003810700a80340d20f17019800360306c408242806410808040849003210050261500520307070400804941000c916000c1681c803043d2402c0b00858000c1c000c03d00002c18001442000c100e2950b22501c51004079501c94644e0390300402103a440c0c0e8000ac0ca01c5e0b280c03ca86c20003200a143c003c0c0030044d6045550403203031140201c40240b0042550424045008014003007112807042c010690324444d02c0c0f0040c0641602e8041903001002c1c680d5003644201e5030741c803010799040f50801c000024410004001c24000350348004001800250050980610544c80d282c030010060200030790342c1031034103401c1007045540c4405e450034101007000391a600c3c000b060105100a000300500000540d0000d40707400c0c01a0f60781041c4001207116925010f01301c2d40180c0e0040103d02d10030381010740c2c80a80c6100c10b042a80c40c0d540c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 906810926 1250 906809676 906809689
    0x90a03320d060b07020d231b0a0803030f0c0a030b190e0105042a0224071d1c0c1a1209010902131a0a03031205090c0307090b040b 57
    0x285200e094040015a41d03498540c0d402424050f00010004601e010180e50003d00100c0c000900100a03030004600251845032200d0740d14900c000070f1068900301009120745c4140c0c07030011f0071964031581c003075000499600400030960384a0048010300820540706c82000300c8080e004040408201030712541600000c1d200c0404070500f4900048252500900300f104003040101c058000c58003651030109400d000000030320300310700400450950b0408106004000b01d00f005200450741303e401c001c49d010680050316070484103208840f29513a290810303e90075243c1b40070860036050603a00041041c4800d50f0216000f1204404074812441b8000c103a035074120803204030b0000c950415010901040118140344143d44d4182c0c0310141f90020000301019900040c03880e80410f0000912655070005c01c2400480c01541c882c50342d90040c100e074221596407900078000c85122410581c0c50303041030081491103500084080348024014051f02500d0304004105004280d00c924050303009403903031140712003a10b480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 906812176 1250 906810926 906811007
    0x715031107171e0c010c0f050a080606070f0327260a060515030c030705150d060302030709050618090d05131707210201120c170f011508090a03 63
    0x80d03c2926444020111401c4403101a01d160901c01c00140c89101a5408411600344255a05041010f0f80b60200420400c1c080c080f0010140c00480701200c041c9a00500c2a070305214071030f0011383ca003480840303002c1d140d0307000c9202c0e030311030031028500508821881000e1285038a903501c0803a04180c1054907600b00b62a001c1d204103420f02508803862003e81004e21400503103030426801230000c1071a24002c581020980c08107c45d01c260041810120300c000340d00200011074004080711055274a40350100024041911450310401c0340200100182c6403410b03200c1e103d244546c000d0030040881d9082a291a40000500040d0703000031003001c03540c50035070b1540c0840240c84400825480b41050b9080c200751401010140703501c40c02ca110070006070713804444242d81c0360070320502191010180d84103440c288103098025240000700c00400c0310105840c81100c0c100d4104000001c0c40c01000017081c1c48045081d600c1644940040e04040080781c0900c4000105c91400f4032400c502001c400b001c0c4040f0b1010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 906813426 1250 906812176 906812227
    0x909100f06060e061e03060135060301090209070809070f0f0f0b0f0304030c08041224110313051c03020301061e0e040507051308071503110717 63
    0x7142000d1160b6a0721522440800d80203607011898036591041c4c0840302086413030b0030520b4510020000d10140d10900401030040c440504504040ca006040d002016800c6104118448180400940546014040c4085107900601071410a03228004120381c00c1500809042c00b6100c2c00710f002403241e824500d40301c000e09804500d4000d940c14a6000c0f034010b0010352000704076070400d02c504240c410f920002c40c0d030010fa00d41082c40c0401c086182078a024040c030f9203c90320b9031440080400030300454032141000000c5c8c072002c7d0b541c14010b060040b012101a00b0712134603c08810301c006032042100512164140340100c0c00c4600c0380b415910090415242c2044400000b50080010007030f4030307045100c015850b03000d02001c08449505100007483c1c4e01355003a6261003a511840410001d070b002da8101c8441154202000c0c1203907071100b881c40d80d600d406100e11841d4000e06002d003510140300e84a0151002011040b03949421010703101c01c404030440c00c903c0c0e10034420403c07400c8000c070a03041515840129 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 906814676 1250 906813426 906813431
    0x406020c0a0c0306050702010c0234090c09090e150c0705120c100b09130c0e090a030212030f0c0f0c0a030f110a080f0d0207020406090222030807020909100f 69
    0x11032600c01e06407100a446c0505583c14039a000d220140c02040d00b00188840140312a0038100909601980901100b04410304954040c4041548002ca4103c030300300c0a159203450000301da84851000407618450b0740e56950b40c108285408612a020504a4110010100250820300c103604c440b4106840080f2841d180c82000401248100301404040010201d400d0200324405216021469400008100300c1c452040300b50103404000e45582504043c00d035180750384502c0c2c58029034166460291103c29009403003840c00380640f4250a00c222842041040231a00154460202c5c800c065080b00444101081302030200007a0001c0c104042a140d5000395030b1800c580c4075022015018101c0c00d48082e0700c68020070003c0c400b245004040751161304101d02c002c0e40e1280180202402070050b042c0081d4880d090420008044049802820703500c5a201050f003421550303031142003408175041c030000740018070603c40c050161404040c01d680c854007420a45209041825044e42115071140350901e0180d07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 906815926 1250 906814676 906814679
    0x20d15030b0112030806090601030905071403120301050d080a4a030604080a020c030f101b0905061303060f06060f05090105191106040c060e04060e0f0406020c0a0c 72
    0xa036041482c018850183c2c0b02c88800c01685005005080051005000d29210b1004c00d0481e44650301c0a4035080d004400d8800c900e031034010381210741034289001442031241404119803513150350103ea0496100519048502c210755450701c000b03800c048000d106215101840350400424605100c03131034411044019046861000d440d4110280c1910151507400300c8007101c3e01d1a01c0028440d90401d07003040040c3c4c0c9070a10307004101c1c94141000038494041c099503214852040001443d120700340c0c0341c03102c01c1c40b564091115100b501c1d24098564000103103a903c0070003080c203016004221850240150502194036034844406541a0f4070501360001d41e40c820810200f68440c50004005590713140c81c030320703208601000900e2409801000a10502d00d0700598501c0c1d0300484840e0080d0350507070240d03816458103080000010601e07120711000306071412191055031410f4422481070b512200c0c0b801045071103100a8900c0b40350014000c859003a42085050f203d4035080001e200410f00c1240300d0902c00c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 906817176 1250 906815926 906815933
    0x108010e04080c07150f030501150e060913091101020a03020a03030e0c0913020111030405210f0a1b06020d052a120a14130e0a1e0501050102210f0c01020d1503 70
    0x10700f031040c6e0401010305d070000500165240c0c0d0131040c400340c040d1624480940c0d034070300000c1e490301c00e100813640d010354540d9103030109031400c2d044811014003402c032800c440c0743d0010040e13841d0366010900400680003605c2e100c0009000790b01c41c00102880c0421180c05205050100340398840c2034034000e06808201000804541e4005030543d4070303e035810065030800340f0313141c003290304980064020754042c0394440c940c0034001001c1000081c0791030504100ea400041d1414041515980c0c0c000d0b4050303400050310017080755800096412004002d45d5200b0b0301d8507081c05900881186d20325041c8040c1c0125081c0c1d60b80d840400c01031502c4240603024000da69896441d005400710803002c25100c14240184500c00c040c1d01d0084100f401c031040294107a41d90307a507142e00380c0010040081c068424402c800c408a400d1000c5070f00060686200f07808407241aa500d480182501d48041042620000d041001940340310810018051400c3ca80c4000360810030011031103030544085680d2a40c201180741400c1050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 906818426 1250 906817176 906817187
    0x203120904051620030d0f0506091806040305070f050d08010914090a020409020303042102090c03150f060c010e210a08070302090a0806190b01030b0108010e04080c0715 74
    0x301c500e00d5401c65900a041c0001340c45054010b0b00b0b40d40301010405981401c3c10300740100c8545640c1400b04001075865000d088005180c2a90214040c10000380016644010300c9812121140100010a0300741e13100e40c0e0442e0681d1003000226040074058001d500007400801101e0300400440c0c542480300e40c1054501411540701042058007800c46106001d072810011940d12074180c2c041d200428220307264008646580314560110f0081d09400c841d885005000d405041d415a01c2103030004c140b511039200c03d0075680820754161100c1052049010703c145440d180c4404000005841c80d030074131200000040c00c645004070140701e10340040004020054100180600c0f529816800501300405000014034188004144106145d4001040900c0760707690b100d100d0003851550122961840e141008040c0b4180e940400040107040003000421580030340034404428006030342d41c91880c1c1c6400344040c0800c0c4050030aa6621404100810184805104803409814290f0049043d01c1501000504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 906819676 1250 906818426 906818431
    0x1d0105060d020607121709010b13060303170403031e0203040b070c0b070e0109050604030809010f080915250f120203040308060603180304080c0103061406030c07030c020312090405 79
    0x1288032903001040060343e030b84054840d516000482e1504420f42800103503413004200c452050022030180070000e138104150080000d0440a4990511210080c40010203a69207408020042103014180c80c0403141410002c0fa4000e00030728001c507040c0300302482c100401c5c00110f50444181d0700002004203004c100c0342516000109440e2449130303200c407a16032204c04000942032500700f2045420820250b03100c3c40000015150003040c141d51503035280360183d20f6610030306115011545100082c40054001c0021910910b01c0d6805401c185010015a4000300d90042c08004600f240030910200800058000c503c0451113032100d174204100410003501032007026900500f800d0041003040002544407100035003001b0182d41058694450850700d500955010100d100b90388804140003c66440c000ba00001048083c0c8041001c03c0c0c450f4000305901000400843e000001000801c0706049810024514180246070403482c4c4c80480d80041d05203005100d08290301c42001c221021985090b00c10a0b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 906820926 1250 906819676 906819679
    0x90603060402180a060e07030c0305071409220204080601030c1403071203020f0a06050106180506030c0f0c100606110d020a030f020304260c09010311060711041d010506 74
    0x24514240e0700040300740e0f02c25a40144251510030106080032a035800034800f50044221048091500910040c000c2c2054154100041d01b80b4000c540f41c035000320403034402040142901464915800c0074425815400844c510003200010b003d03030545031191018001801100380604a29455400e04528094554112050329414a64011800d9a001603020101d440314420b151840440703040a90603d10a00000c0d00207000e07114403e010002e032030f44094140d45854844104503209064802c08031503881c0240da03048501040820f040010a40142440b0160520a60301c1d240b10000c240341002d2400c0301c410412601e991080c003503a500581c5489604000304000c043d90080e504000750343d4025050090107010444895004051092046802511410180700c0c00c0b81061405100340700100d0841c0013903401002804005c510300080320504880e0031802030780b0040281010000ca5500070001110b810b540046400d071a42c969008402c800000d41803601d8180c032800c4103843c2943c40c01040103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 906822176 1250 906820926 906820933
    0x11109032e09030e0301020a0801030c0b0901020a1119090504020f01050306030d0e12070f030b0c0705030a1206050d060f06050301110a03020c0c0307080d0f020601060804150920090603 81
    0x9400d1503144100c1d50800c85030802089000003401d0540d00d0210310820b40d41c05500003c1e54408a03900240414100c1c0d100d48100140150f50f803807108800d01238407103800d0044e04008903110224080080110f0844801042c1c8061800080d014600240940d80004d411030b840c1d0342000107610344101c040c88400030a0800038654a0990002500d0341c198441980521403500521003c0340c40d00f050440d6106c1408040740c1030301d80c03104210b210b01452840122005481a000680d007000700e07400b0f0303c5500e070b4400c0086040071982c41d0180d450400b050b0300b03022802e90310400051582e80303520b41c0c020024007410001404008040e100402d4840070f400017400b030b0381001c0102c0070021001c000c540100b04246001a01c0d00c40d020907550610351280c0031150305101e820b001043c0c048011881c00c9686546850342d1440f9080c07000280c0e110f860921840c408547c00d40c00203070101c2c02c2d540742c0c2480c4406c5c5107030020729114541d5400c554550110501400e10000443e100e942c3e040054009400c110102d005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 906823426 1250 906822176 906822223
    0x50919080f0f0d0f030f0b04050910050c0f0306090916170c0a0609090b0f0d08210106213308030442020c0a12030903020402180301110903 61
    0xe010100e044513028101581d94202010681d0242e012000c0408018814440c1d41031030b03074445a44188030880070606924007004202058909400c8070706442c011b5406a04594030703001003000c0c0c2d000007840a40c840c01386d59409044400e0300d14000002d070581c07124403110a400d405d0300c54500160014010300840741c00c102404069081a811022200c0311540400e82c4502540800d1503034007130f020301e030b904000b00c0c00c0e0342810883c0e40b8028002004045403420807140e80394074007401102c0203210b1032021458424188800c2440800d01440040d440507000c20070000d1040319820008406036400c5003603900b03403240004104407501d140f00510040c0c0c02181018140030303498001580d003201810050a400204030b00d080c01c10080302d2640a4000d6100300080407009001c1d40303030303544452200e20074583e400c8041000362805408030303007450f0160b43d0700c00700c58159800e0100030b40c0003480034240c1862244444200342c4d001d004200c90401c5001c501da0312030103034030305251900030800745000c20003035461503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 906824676 1250 906823426 906823453
    0xf1403061305060d021c061103040c060309030c02030a0c0618030c0e040c050907050409060e190f150803040504050115051e04030f0305071103030a020d050919080f0f 73
    0x204103601c0346079800002a140c0f1510005000c0805921009400c004540500064410340000b00c031503850003403606220454046482c1c400d5484100c500511845640b10305201e664402d03070021403124403d0600e1781e400200f03500000e25184070400304840b007041c3c69500f0b100351984400075491007050070180307480e5942580d880c07440c50320980c0110b410740c13010403000400f4003000300518402042c002d07100c1089400c04d0200141a40c0c0940200001c0d54246a00010701c0540030047c58410b01c040c1d0444101c0303444282c0d860b005442a0302040c041517072500e00b08414250301c512408014241903000f1f40d41c07589032409001c20394034164006090308100004803410150410100c07100c60032101c02c065868041000e0f890340360b0041c1d802c058001d125001003402090b4000000748103441c082c048038458018900c08144d42c0c0c4c411201a08010b8100d2091244801d0280f000303480061401030000354000d04400b10010004100d03400a0001c3c0e018440c1122024000d00440003401da0500141000851440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 906825926 1250 906824676 906824689
    0x2030c040506010c240912090501051e1b010e030901110105040201141b030f0703031a1e0301090203060c031801140414030c06270303040209060402130b03070f140306 73
    0x84c020f094481400401426100101c00c80112038000a00411079143d440c2048800d240170100103001003400000c002c41c1960280094468080c49110f0142101c01d161101500c0c41d00b10b0803080401030154604c00142c200c0a00416543c603582e4001541c50382c1c0e504000500a02e8076604240705645410140701c0540d90184a41400c150110b00c03c568a00f2682c1603a0844044118404900e000c0403810023a1040c1501c010f0103010301a980a11402c0120240d00b41c613000c89055095200700030300a4010388200114400c0c1c8600e20003400010f080450740c011a003000012154105003450001c2008452800114540d80d281d403000c0c02004000032203c46480c141c1c4010300040c04444290519170b103140d004104a9041c0030104003920214146030107107910fa2048210100e951a0320b000200c89032140000a0300c1c8140e8000700704280a84503081072100a600c9026001501445010080340e5502110b0085018400325503800740999414203000384609002c0700307034002e900c40800034450309588a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 906827176 1250 906825926 906825947
    0x90807060503090f070303020a0212011b0e040f1806060f0b0406140c0115050307080c06040b0a03061e0e060d020f01030506040b030d031e0902010f11070f0e0402030c04050601 77
    0x7810025681c0c3c903107441d00c600d0611459000000c502c00d00740d02104050b404102844510b01c241d0b10125054581c10160f0700307840b9842c052003008880d00d0b241161541c420866100d030709401400001d50114034540c94011313501d0f0000c0342c810341d40040100004000180c8188401070504050403041182440c9481c0c10910a501c0b5007020840761548110102c0116021500403450004c000c02c0301101800f41d45d0b0340140700c4e103d4507100b4050f00c07a0000e40242c01080060b00400000c0a6034542420110300c00340e140c000d02c40d44804c141c1c0c0e030180454500d9038080070409504240700e50760304041ca001e0f0b1948103007100503d440c0c081c00c801280000140c95030181030300c0d14030302401c021030180d031401d01240080000c0c98426615105081403010380c0307501a03201460296180346403402034a40810b5a1040c3d80301864000d0000e004500842c40140c403c4802940704040c502c10354030402d90b42c400c0d2800e01c14954101038445101141804110301c0c081003207a03c820000d0340c0c00e00141c030709000041c00782c0c00807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 906828426 1250 906827176 906827189
    0x30316030204152a0501091a09150903130639260a030b0916090510020f01020711090601020c1f020f030c010902180112080901120615020c01090807 65
    0x100f2550341c104102000380307119040b000340c484c003c608074500780180070701402030003030300c50b0b00c00c28801c8038180c01c5020038584520300c0f45004111000058101c2045180d00a10b601d0b05800b0920440c80c801c58448550001050780703580c2c0d0300315480000c80d960b07812140d44c082c1c0a255003511015058100c2c401c50071385211904401003442c4c41c00c0380d42000405049100c45030a07640780000300c0000a07030300340d44074040744039090b15805280d58a1281003908002154a60804500701c2c0c40c0c00c00081c60200145140310009206a0300d40b40701050040e42641c000f900304488a008a628203ea00d082c1070b0352180d403188003440241500030030600416003083d00d00c8540b0041410502c480d4174a94003c22240040240400499540d200402c8815001f0000020200d114101a49c2c540300d10b104200c0006059032442a6558400501c44c0c0d00c0400301d510800c0802d0501204440d41400003050744035182c010f241d800104001600c110b070f0000c0c10180c12028481c10300c01002001e01c0030710000a411000d5400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 906829676 1250 906828426 906828437
    0x30f0c071505010b03190605090604090309172a1f0c1a15150f0a030e0a0b04030807090b0d0e0705060f0408010507050903030910050904090503031603020415 69
    0x114200781d0203030aa0120719441c014180000000c000d00c2000082d485064103d008203035103074070044003106841c034903c60160f004040c130700454001d2400b45d2088041070300c43d0420b1820595100c0d40c45040307040e00d881140454210114001020801c1c1e00a0581c4c0e0b110f440c1c2d0303c001600d520780090061680c4490242045695411601e0f045d4002c41c0d22444054001074080c1e808040c404011000603012980c82d0281f81c45d0459034a101d0400032140e514149421614070b084c00b0080c1034124017a00a90602020543c503601341c550590014006050040d00540039104540391606001d07020240c060708140801c00032106c01c21680c0b20388002d5070400c0302080c2c0c0100f41c152880745031074030700180b5411143e4403020000c2c050540c10b0780c0b84020b0080703941070342c02444a55540081606d050046061250305071f001080f640c003651406450101c000303161410060b0a01c11004080703422103002d4081102d05500000522464a0b9070156460050030940b90a5184c0f07401c14000503550381c801e4524809010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 906830926 1250 906829676 906829687
    0x180708040f020a3602120f06030304090c0e1807021e0106170d1e0806061e131d07050406051312111305060603011202012c01090803030f0c 61
    0x10344440341c3d10000c0a02c408281c1403d10103462051940d50742e00941c42c02294080c0104140c0500303070082d100018040c3d000102d055441a101c0740c000400100f034250315020400c0041004249442121410481c90b612b0344010020b40061211810505103481010018401000095580040c0718911152618030400030000c0d00200240540601d0308040c10216508545112262002401400129203591190009002c8403658400400103080b00360025903802c000032550304040b00200401000701450107040e4102b10001100740d000305503034200010050b64104401000c00c1c60382001c074078002c040d83c407403400d0803c4042d01610440c40349400340314010400141050704e07587e08800a1904100c00caa90701100d2803c50b0340c4c215142c0046206001024088110a50b68460a0b03c1504060319a5245900f44a000130002d506000e00300c1c10400100d0755240000c1d06c000c0d40914403800c08103001e0803000300302d0016118000c0b98103c9070b8107038002d001700b21071108070b10300b1550401c04084d00d4075900c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 906832176 1250 906830926 906830929
    0x180403110715260906072003070305071104061806060908062707090f0501090209010e0909031312170a020c010c0309050d140c030309030a0602090f0a03030509180708040f02 76
    0x7003d0440100300d805011010032041c00e0300402c00038807861266907a401600c5100c0d1f031a202807102c0d01c8014000f40c0c014050507000038007420081a0950007100715010908030301c00060103403005078004802c81c0e0000c11141d20204001c0c041c800280c05103003451a0b801c1c0c1000e610301d540e034000a0100c400500b080f124220342407011600801070341c402c10141e651007515400c03920090040c840303113680454900400060300034020f1003550310380c4905075039a108031141074041012540340a4410f015034041000581401c0c0360304806031009201c20030307101c04005010705140811400c42141ea440864041007000c8c00e02d1f90110754083d90240900703240101c0062420100d501a00f107421181e0819041c0c0743e414140200a91040101e03680c0c402101d0010740310b1303014142c60b400b5080c0300f503800d03500c0110a5000140d56070041e185c0040b0180410101d14102c000090162041da0310a0340411400581c8043c103080c8555600c01660000034409498140b801c7d000700084801000070341411240048403086 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 906833426 1250 906832176 906832217
    0x1b210513020916020d1103090d033605010507020913031b0308180d050406031d03040303050d0f0212070806030c0307090c080603070605030c0c010902180403110715 72
    0x1074010784600950315110791040a9400d5400109016100e82414501010320a504040c110b01ca400042c6040c000d0302002d000312a400040708a0511034500d203c041c04030404e070407410741e400c2c12030548a02d4003034510a40780d03a00e003140c00060411800700036040241c4c075007481d0b0b141c108a404a20a03010401400c04030344003445d0035904200190300000040515500480007401940201c01c032070042000843c0306030382d0f03080c200b10460200c1c105200400a0354000e42c8001001c690b80352000f41d10001c2d420103503040d9030060304124086100441c4510200101e44144914051108021440c00c071010800c1d244102c07008040f401080882c5000505070780b000e1008889030302c0b010b012103601c1c60303c412094020308940d0503242c0020344a040090654030f40010312a088070f8254075841d1a6854141e1800090382c0710703407000580c46d900c485c129001030f00d440380c0941207030b804580018024146460f005000d000000100c448652040509100003d0800c41a5040305100c1c00d0400d5070b0900b91071000403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 906834532 1106 906833426 906833461
    0x320090123040b06040b1903020309150705091914010305061003051f06030507080a021318060b040f0e13120e120f011b2105 55
    0xc68101204400e010440060408a41c9211000c007043d41030713010364403006d4584000200302122040891409440034003a02d801d610b94100620b12550300c108541c1076112110300c02002c1007595005208844c03204a000c2c2c140030201d90303294000980d501451003262011148900d490803190300c6449054403c80004243c1004920100c03400c034000e140040404500b070b04c030f152400c43d005032072a003c0001450150f40109062030401310081c0b21f400b0141c009204240140a10382c150248010340e0010780c0c40150710b0142c0c238401003080401070305e2103a0050010b1800001c000c034180030241d200c0e50594071ba8140b00100d5440b4152149128101e8140c003a202545803d17886030450b10500142100304001844081c10050360481c40b401e02450080d0b068050399641f1881c07030304800310600c0380364028590a101d0a0000203000f0a048250086280d030700c3d450751500000c8004c500c1c500c0042c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 906654676 906834532 := by
  have h0 := BRFrame.cov_init 906654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 906654676 ≤ n) (h2 : n < 906834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
