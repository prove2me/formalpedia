-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1910
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:07:25.706856+00:00
-- url     : https://prove2.me/submissions/9686bab3-de7f-4556-8e1b-feb5c29e0f7b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 343345323 ≤ n < 343525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 343346573 1250 343345323 343345363
    0x191b2706080405030c0d0c0212010506030a060b0d020303030f0609010803281407030903030201050105011b020d1a01030803040c091811032103010f060201020c0d050f1e1b 75
    0x1040a100342482a00180200220390509048200e0f10782061340000e00100030915a000442c02c50509c0e81001070311603800360081003075290510101e03465503102c6400401d01d035601c21100559585000d096074400d038000c1c0460fa00e9140c0241010444603094a40901c101c080000000e41944000116944600c03059501c41c094070303041e5058030020101100007402d00030341c0418540c06d0b4202c100070381031641c00707a030b10104120710f1410042d00711403040e08810704002e8281d410403041020f0725a4080314540c19a01540706034294200040031a00c0e001e03400c000c125615000000f8404100701550085010f4040c240c4619075441c480c00c125080b0f511001e90003d60003101201068046100b41401c43d00902034070010b004070780001800d410440824030703d5520100042c0125102003140b1006405280002c51a101c044003950b03030b598158180100401800041c100364412a84042d61181a400484220800b41c02100381d40160030000c802017040321003010042c2103000008111000c00481283d0308 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 343347823 1250 343346573 343346579
    0x101d01061805060a03060216031112041a0c0a0f030806220c03060b0316112113081c020c010801030c090905010207120e01091e0509191b27 61
    0x3030050300c0010f18540d80309441030b0380040421850f000034400a2591449030201ca103041c41c0180c10300905034080c5100d40c0c0210005011415a0710440c1c06880f10650980c10011500110000500c02c01c10312100038045d10710044c00300020701c264001014402d4556500d15a0f650b4140000d04000d07840301c803124080d1061021022110360302c58094400e80303190100e00140c461000100c99402039504803000419001c0907054aa8003140140c0000020341c081d1030304c01c14905081c8516200f94151101024001405011010040c40040005d001d08000e481a420405844980c42101c00c800240036000e8040485203035813055814506903940102c45014042c248074801d4014440000700321020345d400c21950011518242462040311100c0e43e50320044200a0001484418960f1000d00c2c410f15104008040301501c03501c180650380b06540d00c0801c3c0d0b460610445450f08070402440c1e010386003e01950030840150340c0c00d400e00e103403074507100b0081c500b16068806101d084083c8a104901f110030034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 343349073 1250 343347823 343347869
    0x6010614271311090411030c03060906032803030c030902152208010b21030904200d0b03010606090302011407170c0c100c0308060904030908101d0106 66
    0x49030351039014042500c10060805140d04039000d800075002c030310101044c1d0032410b15042c007641000c10740d454100b45c19410940700a500c0d50202809452203106d903000016002e45003009540621246111081880400390240f4620450445c1040c0d000a04203107400e05014041c1c014050300075805084440c40032426481c80b1010340000001031803280076210621865162903502d440038000d1b00300001003800c00c240c100214004034120700c0c000644200380d41c080352070010041e01e02c0781d041500c021540a07060f02000a00250078411071181c8034011448079203640b1107511002c0c203024203600801842c0d4607824269001c03803503444004e0016026183e0164a4410b41001e401d5103440ba502d0205071410042c0c50703130034079008460000c4c16035010310b02d5004a4584900751009010950411483e8a0b1460300d00801d440402421a801a5202c001050405100308140c13801401e000041e91005170217007005e04044c25422081e91001e084040d0303854400030061141d04122081c040b0100e0706c100014001e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 343350323 1250 343349073 343349137
    0x8071211060f15030d020f06091609150b270102060c0703140702030724030504020a050d150e07080c19061d180f090c2b0c060206010614 60
    0x20f01030707007020804803c0220b88081214503100e0713002c1c3c2c020b400c05180c4910720520740340004188145540c41a03a0003884030035500001c00c04d071010300201041c180c40c1d83e01028020811640211400407001601c09101e0002144a20b040798541c0c01200011642400499440d181a2442c90710304404100d4000000d014020031001c100c0185446414290141c000074200f00442d4864680003041c18030702c02004c40e0010b0034031825a95030601700614100340c1c022072074014081c0141800b400c0301603034900c03d000d0710600e02c2515000c1c005007404a46507000f001a01d4221034884ca80e654410324022544a18244d44445503003840004c8003490245005411103440e250f02c29100700c0e0328245181c039103864031aa821890100c801184501361030500c2c280520b2010b40052a13105203801030250419180c1d0340b200d00c9121001142d00100006400240c5405078050b1040c0050401100c0c0400048098002c503031141203e110351100071640303040382141240e40c860011001d6400c150304000c003a498080c425 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 343351573 1250 343350323 343350331
    0xe030d020d0e01050d11030115140304051009020418050706021011030627100f1502150c041d04031e081902040914010807050d030207090f09050a08071211060f 70
    0x2000c10103001da068507591301d031f0080e0040b18114000c0d004001e04a9084580703400300d1380011032001c1c550325040c1c0b9480e40307400700d44901c5c6456039160700d602c80035561690014803190802c008050240009890303d56520714540c07143d000907008105004d005040c15126140e07440c1008000145940e031400104098040001c4200045510001d0865900320081c0503441c07183c1b9010a4003500030b8240060450b04400990022884510600305407010f6036010840c0380a504000d0260103464980240c98404e50103103401013980c0f04101d81101d4103546102140304e0180740207455141c0c541403400c000204041001d090308010458480110760003500c010000745013009016001814280c90307a4070441540c101c030070080c548540f4030300103016140060003e00300802084a88600c490140d41e00070f500d800703191107580c105950711107400322051180e03000841950b5100c41031f41e1002e421441c00c207102e604084d030306840c809400366100001c01d014500e01500c1d510103500620517a5180b0500001d0341c40018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 343352823 1250 343351573 343351597
    0x12080409050c0c030c030405090c03010303050d0c020309151812030304141006080a050708070810050a0207060c0507030905180609130b0106210209012a120e030d020d0e0105 76
    0x902d020119084c4050b0150040083c05190785a1800d010001c030302c90301500003140d14030304100400010340c1100480d800700c60440004103003021610740982c214040c18800030340080d00008607010300fa00c4080106034002043c00520301d200c40782c405021464000c0c1e0707640b81c8180d07c10804074021400a2040c0509801b4141c1128505100c180103031003038400581c4540020342c0030040e5082009814012080901a854020f007003951070000690b940305c0311440f000140f50b9403131000c5508580c1c0d54045410643e000502130004c3d012001e0020300c1e0b68400701081d80003645148002c10545043c05607070680600e406010115070b19010300308618820003404120380d030154015100009220640c04900800c807a850315815001041c2c1c83e44441d61003007030000a50303032040058140aa8109001b03030581c0b000500d409585007504001c9080300200d540340a0019040d603403072078050700d41c004c4146800074030550540303805645804090341c0c1c2c2c0003424150700104203060189415944204058480d10300e001e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 343354073 1250 343352823 343352827
    0x5011703042306190305070c0507050409110405041a01080708030414011107090e2b110304080601091a010e0a060809120708190801060f08280605040612080409050c 72
    0x400081e0880d400f5500401c50b080c02419108043c170303058130450b0b501c5580b604140b000740b175165990700e0f01d4242174007a4602c075541e40c07882c03141440410120040c844c80040d008001074101410988203202900f032087c8110700075207002088080000c1040400c030b80e071200096041c5070400000840c900c4940f0b601340d04000300401c0720487c005042109400400d1407040001d081d0000b2801d5030305082e8410b00e07010300d0701101e4004031342c040340c03110303400000440e030f0300c1c001d08512800d44000342188280e41c400c139014401e04c4008140c1440c96030182408a42e0005040b0143e4400f86c0103490300501d0302b0702aa4801ca000e402003080c140190700290740a0700180a403404d0a60728800304442c1d030404141502e0900c03011079a00008584140381d04a0207001d03051082c503561621500425813802c02d01420300300503040c40850110304080701c400103441010b004a82041d982c42d40000300030315851092501c2681080c00000700c200800c13070205031007500400414940790414412201074040030f400a0404441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 343355323 1250 343354073 343354139
    0x13080f1c09030e0109090b03060c0903010b10030b010f030e03160201120207050601180b09010b07080d0603050d1206081905030f13030c242609010f0501170304 70
    0x744240ca203120300c40d480c0c0104500500d00014100400307600010a118a0700c112655a41ea0000e800d960060425881956540d070782000310f13001d0104070321001c2d0441404008210310903003581003c3c1c0c184000b07a0b82c01a0b142810407044003680d81910914459410400200e002200390200e01c860036401030600d200071508070071114080341e004c000705640c0c40e0003440c0180240781200c40303109000051640c0a001c29040480040da07c0708040c0314103c91820b00003028001c121007942500c1030400024005c00510759241441601ca20320004088002507940da00540d0540082c49408240d560400080805500101820034074052020040d04c0c148000d00080469400756030040c81c0504075018a9004145549841108200a07400c0700f60b5604400300381070314441034103d2260304500107140c0b502c202c0d2100714070456410b403504002d030103190300c13001044500d1005400c0300f061021a00810001e2781c0e031700c8210501c800e420040000841d00b04000400180d00b05401501002c212940c0c40040300107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 343356573 1250 343355323 343355377
    0x3060a031e050706021b03150f040609020a0609051f023309071703041413090f051624030510080109031e0e0906090a1103040803010e13080f 62
    0x52550101340181c0c010301c2c080c0442c0d80c4070012203282100540080140301d010f405111400704005000c0c03a07100d001200080c0a000d0241c122034003164015100101c55925424014072006040c05654002c500524800c05502c40c2cac8a085264480c40b80c2c00f0340310317214402d080c0b403407110328040c2c640c1c401e0f820203405003591940780f914881c01004910002e0040902c1d084080810140054602810b034005000c10400660368946101c4609800c80c1d81078a00c00e85070314081c00070040c0e1f035006072514104c50500003c1000004209100390400700075807800c2991130503085d41c0301614004c03201c01e03e8180c4081d007039142e009810203a00070440a0300116074503202d400c840d08582c00e011041d0b0000d004009541483c804c0100d41d0841c400d114034140c0c40440c80900411070400010b0080d600a1b508034001603486011580141030115926031280c5d541d09183c00c0c400a01d800a02503010038a5454010803001034081c0c180300728070703a80642d400d420600a400c417040550000c1e80c4241850106100c01e2035055 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 343357823 1250 343356573 343356583
    0x5070204050a090c0e07081303090b070501090308060a0311040b0d051209090a0c1b110315010e090a030f03020315060d020c120906040302040902040b06070f060e0303060a031e05 78
    0x60250030b00011003480504051070000320039030140f0b45015111041c4850303281d00054007548414129010b0380c9081c128603003110079a10310b520229a0030408203190701003140c117402400300d0368020303600c41c02d0300d4641000300520240b80d40301c01014003c4801000006003040d4004074042c003001003402e0b90008454035124141400101ca003140110000b03540e4000f450803103a02900056504410494268054405881d9100c00c2010b0404080d400070b20804010172144a076640c80d101500b903410240401c40006034180081c02a0f20700b20103c140000c80951002a80c0302c111a05039941a2203010010026002940090034240140e030080d4a6266903403143c0c00103011181280000581e10511a20014140b21100e04054035655040040c0c0e0815950507003980d05a07a01204c0006008030311344001002000c02c19106070b0012808200c00d0140900710740644103503030141c0300501c4400c1240010075100c0c4030441e8103503484080c8403010f001003000160302c0c0c1800c07412414071215000e1144c403800d00d40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 343359073 1250 343357823 343357831
    0x2a0c08030c1513020907050d060320030f01020304080319060f03032610090c180b0901021212010909050a02190515040b2b0e0a2901030809010507020405 67
    0x29803000c40d02c1c030242a11040742c55800850304060251001a030f5000510003000601054100240403c9a020703446d13269020b007004640c0b010020a000e40c02c044150441190100c040744280a4a0314441c2030070018000c0740c0c403803540f0032802d91650f9a0300300c201e0802d501000d02603549941d2100041804001c803103c4001031402521b51090303800e2002000429807d4941c88030b51013030642c005020308420760034840001d03104038000100703401d6034401044403208004841354492a1070b00c2000203c40606400900100c6030a80c2035482e41010406082c070342c0d104030700600425410490041158a44640c13110b1503191051040d154201101d400040b902d418408800c0b07010558240200010718103c0450101f0350544a84141084d14021f414185401489182c088003ea036048204038840d251424650b40348071403004000c41c5842d40c001550315001c21408450000310380004503501d1110f101d01e801d0b40008400d0394001607081d0340e16408903801103200030381442814001c4000507581c5004083c82 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 343360323 1250 343359073 343359097
    0x182003130b06030a0203060a020d022203030311040e06010e0a082b020706020307020603070903050703050d030f0506100c020402040513050f130305120712020a02030306102a0c0803 79
    0x85101c1c2442011054090181c070b1090380718031900700044c2c41c007052845c0c0c045400740c40142c48900d0030001070060b01c01c0388070080214002909002802d011000440c3c184c900a540402034084100300c3c401030703442940240c0003528203010009683c0d41c81500c9011820358050000810305036508851890103245000030004480410103c0c3c401c0581006c0364904400d03148004e2041d2443d1001c0039440744100500a03008260000c002408203000740750900082d507000c011a8406503903414a83c2c0c448082c030040d08006400c0c505801c082c50340324003505010b100001c001ca98040032072002a51090b1103104100d80058017440b0000340c507030b80c40203000e41d1117450350000300d0545440c419550364540014824021850012071800c08240e021080e5441201d806001c110300761540036064130100d100300380d04201180001402d83e059907010000d1400303031100f0748a1400980c0070000a030344126111543c1d0300c502c1804440450840640002140c1c0f45001b5052401c0c0f164651043e0b900755403045004600d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 343361573 1250 343360323 343360351
    0x1b01051e030402010e040213060e0d02121e060105060904050403020c0303030a060f05041a0d14030706060e1005010206071b020d0b041e0206031801021c05060307050a182003 76
    0xb0079940c01c1200103001003c101d504628081c105800c4090499032805807c040003034000003a050342c1c4a541c00d81d8200d43e00208034007030701900c59020603600d00d900c3d40ba0300300d242c0110b00e105680c1e0381d0004010b410398900602060404100f402403000400005000360114031a41c020041651001d10085002d000c5003c00032034010706102ca0141c01d4982d0780c2c80680100c1c9000440500350080d140b02550382c0c40700300c0f103055403a1800d0601c014425042941441030f404002450303410020b4a9112104413449200c1135580355840aa040c0c1100e11244100c42c0940c04c040002510740380b10714603807028040d141d01d0f050486000b6801103800309141d168110b40040c03007c0306000a024a05110140a5040e0204941c10aa040e80450311a0002a101d500c04107940003100102907800c2d016070354400c080e01505c3c1c4c0e42d010343d81151000380c9002c0e2801750003401007000210b01410000800e0040e5204550b0b03140000700028181d10081091800b15500940d00c500022042860140254050000010800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 343362823 1250 343361573 343361581
    0x3021603180e06031b01021f0b0915180a0e120c120a17070c02180a06170615060c0f01060501030b0103020a122a110118051b01051e03 59
    0x503580e5070440d04919180903400c002c0189075680025844240000d090781d4106584c10500103030301d042c0100c061005200444600352100f00308940c4003150140049404400c1522195500400640324854040d0000e00c0400150500000d501d0019041450104006810520107000d01d041c082080d614001c860070015400c003410800300680d02107206400402490040071240c042d00410040040c80034005c41035001407c82c502400020300d01d2034000d040c40c9002151070b10742c50020407040b01d44804043c603060307004c50404613000070402c401520200602450300c59003013225444a4540070f05900c41401c000a18417803070240040c1440480312800030800c81d08101c0050141ca104034145410148140000c2c103400d58002c240b0740f01c5107000080000d00e10174802c2070000c00c00d220307880000c01106540d1580011a4440900900f18801000810200f110b1000d5010401d08564025002c0d5206030002d008501411808480c1c150050400034648404100c1c2d140b1400c0345202481d40005000c8100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 343364073 1250 343362823 343362857
    0xd0903080f07140406180f03050c0405010608060d0b0606210403030b0f100e0f061611061201030206031e01030b04050d030507050f1c0504111309080708030703021603 73
    0x200b90040498140a1410548221080d0a50245100d9102000b690540820600042d0ba1024001c1c040a0046801c640c0e1079081c0a0703550340405200780d028500c2c1c40b00001c0c120748a046814000d107001040c02008150588818a840b0405007055500c14020081c500340c1c500c0502d45400c9103041608510594901070502408072104500032500030061860076000c60359481d1031421502d0708070b0a1001d1145040d0000c00c4410000000c1c554011400142c0c060500e81d80c801021030040c814080407045e80904400e0084d0340c01054044d5450b0f14403c80184014a80743c806564001c0c030f402c034002c000b20210342666010540031380c816110319140d402808103012040c040c04042014508050102d82800c0300010050304c02e6002ca6141c4d0000400caa124808a0802003101100b100744288851305003400c14008001500b03c00d24071800e401000c5030050140c3d40202c1e100320344c002c96800e0612103c2c0e1105161503100415a80400d035080010002c95142e0110000d0024020b6450285881211070b031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 343365323 1250 343364073 343364101
    0x708061009120204180c091e02090604170307080415080109020a121a06070507061b0c0504020a091203020106090f02040e0112020105070b0708090d030506090604110d090308 76
    0x10350420803444400c240080140400c08004031941501d0019290080340000a508212498010130003608210000750091054100e402d5002c00441d11024070b59492038014100e1183c0c0c1d126941201c401c0c0010407100c91a2a92484842144010369140404a0340c4425a981c002d410400382c260ba8004103481096104c044d072409040e450030110725000420348060400f480d9501600110342e298030f00d20b4044e0300948208001c515000d06510f444d4003c0380380c0240c544495004100008542c1804851208001a52548166007004002e40c07064201070610002c0d40c0000d4400f02848201000010142d00d4800346015141c0240e0001a5060802d2852001e80310042c0032140e82c50700501060200f10081d0150f18115085134070201c0c4d504010f40700690740b50080d00300103001140c3c041c0c100411240c00c00c4a003803113041d11400340c840d02c0085800540c1299416101903030000880d00000f80c45040c280d01901c002001804000d04040a11030505e098a01075581140003c100c030341481580e01e00303981 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 343366573 1250 343365323 343365349
    0xb0a1106070903030e1011010c05180d020a0e090c0a180b0402040b0901050711030321070f050f030a091218080721080c0613031d0a05060c15070806 65
    0xc0d000034842d24540f4004c051111032110303544103a46e100505804580074034180302001d150240203102490003008041c0403500150100d1003040640315100c905443d00c0b0f4003c4040782d50090009030a1403d21107017040d4203400804070141441110941009030b6074209204004020741d107083e401802103440c401c010b07964040c41c8280540d00510050041c1c00840055a400f08001c1c80c1954a80c241070408541900704145080e4250200044400000f904005400304440c1d807440c0e02c040d0354582c10001c4445903800c49880c0002a024001903c100301c44030010358110b0003c0d580401c4aa0039926aa91084600f10540d008500002c0504580a00401444004104031009012080e2a00c02c4009801c00d5046000801c0503152440e103080020000680c0c0a07081c00d03030110b03101480c05400456200c22107070030680c040780245102220690000c1902c45004201030405c01a031481c207020b20072180c11190001c12a4000ca40f5144850500d50a09512441250b40d812449041281c244642425254 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 343367823 1250 343366573 343366577
    0xa02070e0103150b1e0118030602040e0f0c07080d0e0f060c0307030b1e040b0d061815150e06270109060509070e0105031905070807020c040603050a1502040b0a110607 73
    0x550030b1711803402000148405183d0a0905445c080700000d20b00002e1a425003008140520201300071500600c9800079a124640d1803500c5500c40d111110480b410b4003a4070070080c076060040041c4810003580746c001580300c224030411100140d47e03503234035a030801d9000c46140308a210084200218150306000c3d40100442c207039041449880d00d5054404d1514140c880d56008035114420360b40b00e034803071681400086410180400c0b201901844004281e80c44103015140c002c01007400303020000e21072091614415198440a01007850907d030003880c220700074189984030520080600503147e5042e42d040c14035911034200c0300c80d907051408407400c07554aa041313140244011320821031883d801100420306201c09080054885d81e411030400f000e000448820b11850f81004280210399800c484044d0044000e6001d8034140036002040c041160464400600030f5440902d1401c0401d815141e1481d00164035600540307015102c0610313004c00d6000200d1400017540d80a001c03010304205200d030a030084828 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 343369073 1250 343367823 343367839
    0xf070b0405031e0c0a03051f02030f06010807110a05060f010602030a09090e0c150d0b03011a09040606030203010e0a1412030711100f06030b091903050a02070e0103150b 74
    0x710700401d55404485040303d04100c0d09120002801c0c500700102a070070440145000095a100e03c0c0440c0c0343d5000c01c1a105003000ca0fa40070043c0700d00d40e402038a120700d1032082100d4480e55800c00454045c0400b03080d0b402400401d04d4a12008030050000303200b00c0d0f020302c0042002d800c000c041080503020590040e41190414409480a01c1d4001070100c00c540e2100d4001c0b40c040901c5040d9410100080040da03482604a410444204407440140050410100003084030301c0000c02458203a80c0c105c0c1e400c4982c600d20350a60079152411002490304280034110010f889501ca0380400d00311004d450300d850055226503480001c0150250441c174070007101c88040d1000c0220351200c12514000540b449090001000b40c0e085100d000300311503030040c400b401c0300b80a900d4600f200d0f4001040342e0300064501a0043c400194103800000301c3c13203000d110300b1716031601c4408203480881b440d4000080b04404c5004002001070b00003102d003a124003941c003c0f0f1007013090001c00004c0701c0860344c000215034000c2e086 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 343370323 1250 343369073 343369079
    0x201080c030402060412150c03060611010b0f1003020c010c020c030d1e0509011809020d0c0302040f030b040c03151407020a03090e0a0b03010e0f160b16080412050f070b04 75
    0xa0203007520112641b6007052000e0b0191860b002032401501814011120300d04107492a002d41c0c03607005041100e0301354039500c1007500004d417405c2c20ba484882c6a160440c0d41508907207503a0610b04a81c001b01816440c0040c1440420302600c2e0075105200c152034010782c000d030041c00041c42d0a229a80e420000c604110380310070103560405041e00d100700e03804828000c002c1500207069000722010749040c00381042d00b00310140c42d03000400c020342183c642003410b5458000040100d9000f4400c45080d103000c42d0741d031140c143c51a035661856070801081121141c2c240e010000000340744041601500b0b410001c013083e1240c3e05042807020fa0303401004502194821000300d8003190300710391034030142e0708052015606680e41411090251003144d0389180c00d91b2800c046800595000b10f154942c521803003051b2014654904030300000c01c22103001d2100c0c040c0c42003081951301ea005506072a00070784280b10080c101603984e140025000307142c034415103550300042e84010814500340101e43c05010170092190405003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 343371573 1250 343370323 343370329
    0x7080c01020d09230105070b090109210e0f0105120c0304021e061206040b0d0b100b0a09060323070e131806020c010b030d110c030102040317071a01120201080c030402 73
    0x3048a01c07030384460800c0400010139902c600222004036821038900320460402c0b0301910b008020410060700d4001d40f25408c1d4110408242c0c2c000440149582c0d440180605c0c40d0810441703058141d06141440030810120b180c901015900911809501c2c19007512490a401030001c91042402800c50404803c507081301e50b580d601058621510001424026966981020070300030f142da01c10301c5502884440200d801c10800602c5544914008003840a009075201003268040c06548201e60200d80044000d01c603851007988000c22400e102248000710300384620782420302d00c030140d51080010b42e17182d03054405030030080c0140440d02000041000461942d03501800c442030640802130101e9000114070220358404d402c18180c032140141540c1c020072203401c003d4003140400000e48000d000d0954501558501032080d942100d400140c104808410803035002030a5001c0b00c0c045500c0e2201c03a0710500541450b000c56800307040c25003000142980c90b0b000262200070010b0800011010030002c00005031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 343372823 1250 343371573 343371599
    0x10608070f030609031101060b090117040203060106050705070f060e03010c020a0203101503170a1805090402151e0a030b030601030807020904050709090506161e0810050307080c01020d09 82
    0x250009000100051303d031904a42c40d0101004803403143d0b0810740003280c000403100003400505400d0301c03101c96128000350300411403482120003940c56000140101b0049015800420b502840741d4103a550050700c0f802240c000c0509070300710200055000c103144040382400d210304045101a80002e20b51041c10f40d0000365a0b0071404018800c4c15101c2d5244500c204408034202e01443e44103114203007800d02c8584114554000700c00803000104c841c10150190203900e030b030740d10964801420320b416942d40c54080c0300143c001005144044042045030b203a404002d40040f5050001c8a120b540d51203800da400241620300807141503110760403103401000003899241c11210341e180d0503203510700aa40c540c2001c60070114594000c9845500b810103c030100100880c036540700d84608034419008540486040b901082000b807005030308044540385c0b054141c05820305952151328070b800b041d00540c0760340110341403031001c1d4042c1070b05501080a0401c0c035031b014045100124242d182045c86c66140c904003000603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 343374073 1250 343372823 343372829
    0xc18020705210405030604060203061503070c0305070f021c03110102090307090e032106091506031302040e0f0334080c01090209040b061203030606120910060611010608070f 76
    0x400070702d0589550708104142c0b0010b080007802e4540d0303072601c0d0808002a6004841452191883c80800c1b42070103010000c0d60700400b400d40d04d440a20745259001c0d00c82d03a00c04042943c001c854840c0710b00041c2c0e502c0e0842c1d040658115900700398510a850b014204c3d0225140210301d590040c0020070310341d20300056900c12551010400701d409880000c8641c00c4d84944880c03480480084032100300141402e00c1c2e028000e0a003a5140340c8640e1703c48415000034528550200e903c8801040440c810030f042c4481c101d400ea0000f80002842c003521030116207000d151480d0a140d98101103103541011981d01c8541f5441156044202c0c4402d8494000100152000000a121050100d0806445a425070003a1740095015042a596003440d00f0094941c0d174089400754400c051480d02225041808829030703000f808040d081d1070138802c0e20302046d840c8c484001c011441c0f81c130502400e0450501d01d0b004140080407103071110150710300c400c2082400d44049800c9440345500c0550300b0041e4440303c00d003800031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 343375323 1250 343374073 343374103
    0x1205130302161203050306040608070b0712090e0a0e0c030d0e0109290706060f030f060b01210c03020f120f10031203051f09050915250c0507030c18020705 68
    0x62591f4510004004201c42d0b080501c040c0b18000d000318080f15014001c0410034003032502550080c441580440d480000c0317001e49940e03205410003041e179124481d008007091161030025030701803114035004249050b825000b03010005015000d0318843d942c2040b5008044d040c0404841600000c050181400d41c00150602d8200000000c00700140003441c0d100d140901680440362114076a6401c00d105c2c44441107009503010340c58020f144416601804412400040c1c00707907001b00048020361941e000388442030303241e02455000c002c1000e403985140000c0c894003003134003c0c8141e00d045c45600b24584420080c404140c80c03030380c4c03070003480442d480c0c004031000c2403403910f808a1940d40300c4c400e10f09070341e500b00c4001d103ca00a01e01c010464049540225110704515011200500e0502e540c040110b10309850161449a100740c01030841065140c0403560300000b82002202c924165984601d0200346500503201d40030807032018044950720012003240d43d40c4281c001d40c01d01c462034940310b850309248040300c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 343376573 1250 343375323 343375327
    0x501030b0c1b061608010605161b0801061e1502060c0d060e07230a23040e010f21150c02071715070306030f0f03120513030216120305 59
    0x10b164aa0403000484001c0400f030314100d0521003d040044c506180010020800d00e00001c07400d1442403040c0c5201c150400c0c142070b01d02400c1c0d150008030b05031400a12120100c0c504000c112a2002d005030001000420440e018907210360400700c070b03062041d0704490f074100001000c813004280e000840399003008a9040d070310360740c104000317090700245210f41c090120101d040303080121041c2c01903007081d821500e61031a41101c14900e6082a0644247c070038000115080c001680d403024508034244062004083c802803800ba16014032680c00d140c241d22107501c0c403e2868061205100e18100704481c208094441c02448207180d4403c250800e0106210b01580d0380c0b40a07001900340b080000d40c0c01813000c040004400c240c42500d65494580e2496190218481c400104c2c8a6601c40c1c030510080302e4202c03100c001c400c038003a900d00d00d411001070425006c1080310840e0404080840c0300f0b986c010070b804143c2c11041e00d80c0c0c1c5030103401c04010101c0c00388215039503d404c00072040070542c18080e81c2da051419039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 343377823 1250 343376573 343376587
    0x6081606081009060b07121b0b100e0405030403060b01030b0a050f0a05090901090c140603012603040b04260309040209040f06030f0b0109020310140609090709180501030b0c 76
    0xe4458190f001e14020340c140400041c0d640c0d9039070000c0440c41c1c0200b07494075003854805d000f41c8410348030301e480e030700c103120f601d0100400b207482e071081160400c5549204503001c41d40c078840300302481c0d826182a1201d810002d01041001840d103d4001483c00070300f42440000d050740c0010300001040e101d024000c0111510034441c86d610650b44001034140203000c0e0036281425480c050003004041012214114080e2001c01c080c82405007042c041d800003449503155138240b164071141c000c2000c8a8542c04c000c0011655414501400500082d03c2c6a1032119241d5151640801c0841e0200c039901c0004a0780c0602c245203c50084110350a41e80141d90150b61000b07603402080c02041c1291740040458909080030003040f6050744071002e00d5009015001d0140d0b201c0c42c070070080748000d5548103007040a2803030400c00200c142c0340c5840d812034010501420031003c00c01180c1440400c0b0f58100002d000798a00307000c4484284144904a4000ea4007001b10398110b5881700402140600520922000441c1c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 343379073 1250 343377823 343377841
    0x50319091208013f05120301030326071202091c06051005190911040305011d1207020303120606040f060309060b09150f04230a0608160608 61
    0x80340000d03074841c00740c061010a04100400c0100c082c060703690754540039403c1020f0901092a6100000c140c04070013445030100356143c3c2c03000300f41c0c502c044507540a1000c800002800700b501170340c021400707910347d5541c0250071007000c1342c1d42c100c006103484580c648000380507480754031001781c903d0990312040044e944d10b1420000760310f421000d13107800078140d41290745404004494000314002d28142c1c0c0c0744641c85480740108440c01503200c1d806000318485200c10886110700d6080941640c00f410402d13071400f5125161a03080d41c48074990980c091249140030340c2c101600f084460107a80512701001c0c00d21500c0d5000039100d1082c070100306940119400400c0482da00c100448005101c05021074000750b54a100150203007100710810f503040da203081e6443c1510708000088034401d100039100407511581101c2003011200c1c0000000e90403a9440201c0007040b84249072001d00156108502811071034180203a8066810640004800d41c01503000d84403841907822a00007907903801d0a06903900e964606030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 343380323 1250 343379073 343379081
    0x61d0901020d020a02010e1b01080f100302130b0a0509100b09041b020601030c09200a0c0606140f03120a0f020c090c07061d0309010c030504030b01150908060106050319 74
    0x20001c101d07840002c4c00041c1940540c030008106080c141554100c000e008542c20503681042c0c02a4003042c5103100080c80c1010703031410b90760710005180050a01c0c81c3ca036004280400c0b101d20903000c210340d648426081c540380c0489030740e0007400704130b800711102e15003c808074101f481d4a2180038a044000318026446544a400c01c040c0e10a106211011100704a003000307596400a22040d26402c81c104004144446a40a8142103800081d1801d0039240000c5119403c4e070b100d84000000c006906ea80ca100080d030a0080c0402040c48420346614801d5000400400c004080700840c0f09030f200301000e02c0c0c12848603042d1401600300e400c05100c030070303401c3c04140e0410b0f2920107841da00c11000410813042441e01c1c8050f0010381c0c040c0c40204690310500d82d081c03202202001000500703034002d005400032980316820030031000b03210b45171407820290b0320342d54011860004e8000801303408800e08407070b1031554868018002000c07910003e000c02d514160001d800e501c005000f141105000502c3c4110860440e04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 343381573 1250 343380323 343380337
    0x601061d030a1b180207080406050d021b0d030b041a010c050f0a200f0102060a02031902031501020105100f061209080d150801090507090509010e060a0b030c04061d090102 75
    0x584080380300c03400f10701c0f95030341c00d20300882d01c007441081001349201c6510320075a01040c6c1c1c07000b080d616160804206441a80041000040c80d98003040f040d180340000c0b600320b028020607400284184401610003030141e443c3d11100c180102e02e440c0c1106400b50040c0ba1402090301c0031709011000b400c840c1001400c3c940c0d414240381080c440c134500001044090740c001a510003504041c800341706200c500b00203403080000c0300c0c140140e014002041181c58954010364000001240b60b211441380c3c0850881030760811190036040928001c110a11940c080c010564803803040421948543c0c200880d00b80c0c94961405210200500680d9030301090360540e0144580e0f90308518400e07100c110001051001c1d20300d00402c02402c070f0601c040060458414000c4080040d4003034042d245480c03e01204500074100284441c84079921244460a204d1702408100e000740100500443e552040f50300303045c64092928441c501440c9000000c12401d01c580180503507900748400074490607120010401c4c00380c01070304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 343382823 1250 343381573 343381583
    0x50f0708041706040b0f06031c051e040e010f03150207170412030210020a020706080912030108060f011a0d0b031510030c0e06011e030f0507030603140601061d030a 72
    0x1680c2c1c9540c1900010740078452841510b80b143c950f610110440a50403090329001d03050781c4403170041006101218500040c644151803c00d0810003841240e110180c100c0d2101e81c840c03140010140725400940362514058100c943c1c4010034145036948151843c40401c15402242c2da0200c0c0b403508110003e210400c5800041112544a94465a400420300f4102b1350440c007502c5421807a4103448664000c1e2000284a0740240840a183c12400d5072240f00c001c00b191102c0c0144130520300c4000c1501c000d10701901030003000f80b016240071044401501d00680020802d80c2c044601c1e100c0944045045400950f00342d0408075010100d070b00800d10345000c0340c107030162101900c0704001c0f02840b54641039045030b0041000c0f200441da21000640032903800d49034540080c83c62030182a5148600020785440c000078070740040c83c0010030107100f00319030050b508440007940300d1100700144503400280041d078104280280c80203515265000e86070001e002c00d40360900802c0200b03031265a500f40b02c41e00c8516080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 343384073 1250 343382823 343382849
    0x7020607031b080301050f04050906070c08071b1e03051209010e0301060e1608100527090d0906080f071101020c03070f03180e060d060b030a0c05090a0c050f070804 72
    0x5241c5090a43c10134007419002e0080305600b01d40520b018001e00b030150220700081e064a4433500400c943e24401c1f200b0079180400704010400014801c14200c0c500c81042642c852a4682000700b4500c43d40d25125510314648030920007031003c680045200242000348440c8030b030f543d442c50801610301400d008034031a419460201c00243c20701c41860410710810040c0740054405840c1c1401740c4074410b0a0715003144420340345170240900d06126680d09045040700304400c02d4100c0c0e2900c240540001211404c02c1c9410a520007184144c0002c44038024001a0400501c01e01d40715081d100200f1008000d1002c104080315096200c280a5040b50f03070002c1c10605a076941c1030581446494017080300000c40015494500c08010115405d4184d404c1d5511041d070440700707880d6802005041000c910003580c6040d920400c1074155178042080d00d2030b181c822108102d40c1c0d403402041041c0c140e0002c000d1501141802028020264840121003000b0141e00a0307680b11780543c01c10b110726000c1c1d90801030b890600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 343385323 1250 343384073 343384127
    0x31801120f0504020306010b1215010215010f030203061b03060108040c0902130f0902030c030703090812070c0213060803070206160c0308070506090319030c0215010b0a0e03010e030702060703 84
    0x1c2d40120348607600036412240c030340e6610701b4102607601c03801501c480c02c0310400f0080303000420040706101000c00705104480d05181c0300f01010180e80740c00e0340564000d44484d04100f0450a003445080e5000081040002125800418810703d0780720040c1054108108240000c2c1003004114941c0081c1074084401c64031802e00b40b85000310f254803405000c0d0710207180100000c2d41410340c005c03039102d00e240462007810b5807102e48059001e803d0021088540f01414404a1410a000140c103441400320781d451060b0401c4c980180181080a88408143c5a084c010248109038000084555155040c0c8070303190746182801c81d950b1180703ca0040182404a680c82c00424461f000c4083e10640b0300900695682e0386808000b266280b04161800c2401c1d2441080000210300a41c030404c0d4442480c01503500f02000a22170505000c000d8001512621002c9102c0d10350710303800b1940904804041c1c000300651311000c2d0392981d4900420200078480c00c2e00007092010140b1810507600f141c04443c019040441c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 343386573 1250 343385323 343385351
    0x81b0a050708010f0510060e010f0c02030102030c042102090114030703061103270a031d030f0f0c19290a030f0f1a0609040608190303060501020304060203180112 71
    0x107480d10b03120001d24104170201d4003000c4c980d030700d243c01c80d20301d5100c1034034580700000191100c840600b4203e0a2207114120300c00580c5007800110300c5504007410444c1c0c2c850806a0302a003906000c1d04460003050b01c5501c102c0140c0b40c04203102d0548445074400a0004001d00c0081d203031450070b4100402c0c4a051050013566803018402543c01085589014005124203441c1403010000c440441c0d50749030310129690002c00d00890075059243c8404206807416072558004c03034070f441d84c0002c003a4071660143d000c0080f20f920034400724052640441d0031508180400364500b004008900840000820f41843c0301040e5103540c61900e40c094804100d55202c0c00c00c4407014000300010320004411606005c802c0440c004148240306034402c028110b1410320102405210703803030b0821800340340c00039540c000200f50041704021485490311701e0300032400d00307032141e00d4000e013554551b44c001810341d8021702082c06000d4011041c0c1303030074018541210b00c503444510012a822500d45490103003840c90a002601e40320 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 343387823 1250 343386573 343386581
    0x2521020403060509060906040321110c060a05220602030a2d050c0c06161119021302120a0902040603120305100f05030c04050c1209030310060507081b0a05070801 71
    0x4a801045c2c0e4102c0d074031907440c0f98540b1411200100016004040c840c0240c1f402e01003a003248900c8400010a07020400c2c00364516030280346903ca1390340c4400204600940d0034007030310b41c4c03003c800c0d50076010004095200e2000321521690041111380c0100000b22211400e23800500520801d210b043ca902d1400f81b1080c030352011002114651504100c0000c420689000440340b903c1180001880c4541d510505251440e020303041c1c940800c121030001551480e000c011b04041c204d46150210303404200b40c410007180352440382c80740a070320b801030060340f560180020256900004010b0041040d4400340b0000d0010002d682000700354905004044030381960540c0034030304c140c1400800c00080e6403200c1e010b205558584c030070b460b41940580034200d164209500320300d800c505240b452508103036091440c05c00d510340c211080116a400441049552020241444002c28007030608a01e4943d4170303200c00304680300b90300c0451041d850065000b10415000c0200a0050b6000700948401c1034803500014064 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 343389073 1250 343387823 343387831
    0xc0f060306040e0a031713021c0c09020c030408070e0402030a0b09150f040303050a0902130f0e100e21031501020a0203010c02010204080f0f101104090c02030403020925210204030605 80
    0xf07030803400000344000d108400c94244d1f142d002845007d5074002084a640d81800c1e039001169a481a11000514000b141c00589140704450001c0c6803140d050640a900d00151070b8020341c0c002e030581040c0070160300c021405d8228a504601c0d44250365030b403036280c546094012a1854a141840820020141901c1040764081d0f4441d030307014019502c030088400b007a2241000041d500c850002e0142448680d03030b50201c00106105880881d0318141128030b075003000d005401c042140d64560b03042c2c1d491804c2c10701c0040c200c0c0c1194580f6940760b19903a441007001d4000140640705001c81b40e505981268001c0242d500d40d07650080003405180700b8904002c1c003030f41162103040c01c50322030700d0096410500007145d179140120003000200141880070002c040a0a0030007034000c600030703003000007140a07079940c005c410f01d9a00b5900119a075515610521504400060240c050032402c2d0080300200100e07a0003620700c00895203022111000c7c180003004024201c244a1400544001000420050b00350401445 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 343390323 1250 343389073 343389107
    0x3010612050402010210051e0c1e040b040317090603071706010302070f0b13051c0f1d090604020f2109010209010906031515030e010e0c0f060306040e0a03 68
    0x401406500c03000300303840080d64000d0258000400c80c150b18000e55200b66400000150845000c01c0301c0c0b0601340e1003180c243c3e142c6038402000038040008005003800075804040010380b030ad140c603292010150190285000042c0b4015480c406c13103600303c00d59805d44005c04002070000b65a803c2240001e802034043d000401c60506031000010b04960191083d81d88864201c11700301180c10041e80d42c0c103802007004018480691959015a02095003000782084010318000385c9034034413143e010083c007501c0d081213355003004900704c003001030624800ea1113201104140c8603a41603031034240000c2c000e0300911241d441c1c143c00114100a00615034101000310703034074490b002d0800d511080c50b0107003030744100b86078180419002e1504001c114466800501c0c9045509041c0001c191039121400d92405400c82d0741c030000c4c1c0c6800322181090001c2c441c2a6842c0c04d00fd004000b07200d50308000c9102c00d8607424540e84030351008000260261a80d0f000b6503402c0045c0303001e0743c8004485140242803004076018203d9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 343391573 1250 343390323 343390337
    0x11b0b060625021f020a17070b13050714010f120b041503110a052d030d080702060f07021b0a0f0e0708010605090f090a0b03070f0501020d020105040c0b0c070b03040305030106 77
    0x10b05109400b0720442080201d178003412002c0c0c03458032001107210920b010040300000421000001c00c041e0b440c041d02420003260700c0a02c181303184c100b19150010310340020015140f8642070071407681c2c200140c3c0d0484107080c20300d048242600058072008041e020001500182408202140c45c20f130700c1100000c2c0c1c0d100d0b501c000d120164000c00e01a900b05540a06904520510307140381c03d241200c2c09494500340240c80901401d8110b030003207030420f00340c81b5540700400d02c101c00380a4682d4040c0015584400d6032030312041e00d840e00c81030003503603400c040b8032900300c0380424800c1c128183c4804c4400d40180c911076000b50342055980740c290445a0084690000141d8042c001081191094003212004500108100044182c41d000c1007021000034240e000300c00e0355211f504485440511002004155050b040c800641c500400682448000300b9400110b916010412001441072107804003a20703040340d41941c80d148580a440c0c42c201440c1c02c10820070a0100801c0200740d4811b0003035040c0c0d12179036034440e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 343392823 1250 343391573 343391599
    0x903070f0f0b12070e1f05040306050f070c020402030a0b030708100b010c152c010b1c03080f040c03150606021c02030313080d0903050d0b011b0b06062502 68
    0x182031405090140c440c0c3c2d00c14200400d0841e40b00b181194514840104254400d0310007900c80d2030220034400100d40401c00c042410000d1210030300c01e140d03100740c503040c0605951402420003005001c6021001384a41e81c04000b182c107000340359000b13088410018040310b103607a48400b0004e40d01c2154690300040c8505125000400d940b0800401d60f0841d48200d862a0100c501d036601030107800d004d940141c401150741805100001c081261020495001d130000030000b00031000d00100841c41c05171800d0800d42440340345d0019610026a0768007002590890807140c44626001100202c40c0c0c0c400781140c1500e5010030384050030343cbe02c0a030444071607800321910140034500d40b030400b04070100d1500c0940c01c107000081002181080018000e80300d030f010b061074104030a0b6010304427080c3e40310540000d0300c0030a41141034541071184608805003420541100030b0102b8004000005d0204020020701c0340c140450696202c08003540c001404080e100350819000041c2da010000302e042050b40704420804100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 343394073 1250 343392823 343392839
    0x5060a0f090302100c0e060a1d010219080f090d05030d1a060301030305180a18060b040312140705010f0902010f0c0c1412010c02030714060c0a080a020903070f0f 71
    0x640c030503900d42c014004c1d072480855980e00401c0060082030a02c01c1e101101c00c41d0b9542c0320020f00300303a00203407245080100501240c0d03046900401074a4103540c00554401d95a0082c0d40c0c801e04010385c0a07081a0f130341c4a000000003001d00034294060740010080f2094410060b0102c050100e41c180d50000300034107603d290020004035021030025401c410100014800b0900c00c02c028080b9100c01c91880381b1502c001804640d0400c7c00703030700c100100b0130f01c0c00b103485040595005880c0280384c3c4c85145400c250968956000207141000c0103014002805814040c2c0ca03018810781d14810740000007040001032503a00180540340a8804130300080d282482c0c019058020350382c0c20141504003601d83c803176a091612500503c03801402e00e035032002c0b1100d01d05100307c4090040406454417680030b5600e84600d0300e0080b44e0307158040c41c29001504580c08201c0e500001c0c0c02a2891a03d06280088032600c444401e440248a080c2ca0319070140a8080045030002c180c40003001202c2d12641886001c40e41c0f40c0c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 343395323 1250 343394073 343394081
    0x20f130e01170601151215080601170f030901030e1f0204050901050415060e03070b0403050705040606140904050712020a031d2a1504120201030c0504031e0c050402040305060a0f 78
    0x7500b00300e00b1410600c0c1e1507041c46242d034000130f071039118030000c0c0305503403110246a83c0d80b07d40d01c098581e40c041c10040c010500348005403510240460020200141c84460a50702c900840d00c0850401d0307a54504800607040400c8211285000c02c2ca01c54083e8180114410281d401801003030702655a400001945040c240728402e4040c81510001d61082e0a020040312003e651046140d0b151048410210b00c00501c031004100a610840c000c06104c1e15000601041d2942035010800740000f0301c910710803400d40e400032112440d0301110009101e0740d0303401050391007411900514045910114808409a401d61b0094a810041c0c038451082e031480e400d800ca566403810b140078104001075006004420b03d11800450300004005d1200e03080505480b1040c210350019401100b110080210101c10355801d44943d40e04c40300145401440c00741980c8540c0e000d402081c002100c180d02004024041c8558590400060032000704155983d946d03904250343e071004180c41d003080841c030b450b9442d076203c1c800f84a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 343396573 1250 343395323 343395329
    0x1701031209150503040b1803120406052a090409061d0114060d0308091216030f0815120a080c070306050a050106090506030c040f0e25090504020f130e01170601 70
    0x5121031a559032550b8005510202034403c7c65050740560100ca6036110034009032225a07801d200698003440c00d030600c01c0699002401c014a842c04580b82e0030184202c42c140042d00445e10101107a030f13080d40c0c1002c1002003810000107043d0614242c59101d4140a9240006408116200034086140c440c0c40400c00d00d0700607204e0a0380451148010000203004d207520640c00120841a5180c81412a9641c0010740c460790500c0c0c100600c0c0d010110806410001d00e44444c209807500310f1062400011707106e403540111100c0c0c0d1058011005114003180104001110550311584407a15041d0341200f807070b902c40042c00100c800a0800b00040d00c1030701c862181c030f4120b81d15591590740e00c503d005e01f840525030001d4001c00b03050804100c081000510311040c203008044241c0c041c41d461904144001d400c0044000c1e00e10b001d00c2d62001d001040d07030301200d4507007551303021070300142d4401d00790740e4801940c030802c0d0200d0b0464064020004038000032002c694103c0d403501d0808400c0c00000701c0c000d510303038500340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 343397823 1250 343396573 343396577
    0xe06030106050d200d1a1305090d1115130609141b030c19090e0619021315020f061014010207060c170d1b02010605010311040510170103120915 63
    0x4014522900c01740e420030030b400c48040c11000d2842181c100171035601452910075061194451090101d811010040c0d2813998a05240c00c250012040c600a82c44a152201429000e031420000c501044030160700c4410056000204210301380c00c2e4545901c2902904200000034003032a0b050086048512080202180006000e040341a200c4000c10111b044185c0c201e5400b02c22030b0b0004200884d00d0301c504140d604500005140a00e03050440203000b0f000ba00003013440e9801404040300b18248a480d61081d1504001c2040000b0010300d0200c0c80c0c00840c154809007480345506012451f174540c0910021340d04c8078415203440352803550045e42d8442d40fa1190b000003840343c103800408215412511081440951402c80c40c0c89050300400081d1000541c401e04965800d40b00c0312546030302442000b008043c28201844003400c4417001071818082c03481400c0c0a540015400c81d003880c815003200039401342e109030780c1c2c5140d6101d00304010141203120002010551180e0b001c00c0e030090307560642d0208034180d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 343399073 1250 343397823 343397827
    0x50105130e07020705030f0f060c070506040f17161b080715030f0609021201141c020a05030a0b040512120103080a0c05010203011806090504210e06030106050d20 71
    0x1c1025441001c00003403004045016281c030200b04e40d6130903ca40e444d0003c04000410304041c0007100c281c206017018040c3c1c0c0300f09608001d07810000c1c0d800301c1d200d03034031a8100c41e0319400e5070202d05102c00030303401e4204a0551050f00085441d506102c01118010b170038041c0c03019034011041030618400b0700000d0b008411169000b98420090b0807412220741e0b8a9107080e240216028604020f20000d590300c40e00204051a000305290701c0000580780d0385401441d41c500354079084e140c000c002c120b00a050a101c05801404041c41e001551150301c015002044c028080711034042142c1801c40788400c0c01d8404440c0d50145240000164a8800030780e0045c03180d8080d0105944d1844e5070304401d95001401160138824400b0a10011403403c0c80914001c01c601c0140c0005941c40c180c0c0041200c0721a000080003a182c44103010208100210700c0100040350381009070310103900c16007512134950381c100083c2d11650000011412aa1110280c03030342c0110840c2c148240301e40c040d0003400c1ea01aa8a00796405401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 343400323 1250 343399073 343399079
    0x5090c1f0e030a331a0102011505010503070c1a010806090f01050f2d1f0b132c0103051b030d120f020f0708040e0c040f030620070c03050705010513 65
    0xa29294030100445021520f40314805020710000f034591100885e200e070340074003000c403040c0e507028041d0003d1074840030b000301440f03405c0000180441c00302910750b034104807030220524208490320058a602c461010610b001c10342c2d40e8418943d603a0001c80b0300440034021140f4090814005000315801502540b400045035592884181c01048081261001c044880c0d5405e22006040e454080e010b60300b01000d0f801c850044826210400005500c0420b40360402c0100324144c08811640070192460348045002e5044000c060514200742c41070a1181400c0080c000010000d00040c0380748128650408406c404444404154442c030510386100c000c106c5000c0350800c10620342d84041010480200014181501c00410100d40e0300b04540403100b0200028085c8580c0700380d0061180e010f1101414141323440e0400c1c00c0c9140c2100c2e20b1000400c41500e03110b2402e0000ca40421056098061020840e01c401d02d0703060510a2a1345403100343c07514080c0000100c2d065215004845495043c0c01a00b02c606107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 343401573 1250 343400323 343400363
    0x606090803180f06070506040b1014090a020912100609050c090d03020106080106060527010f0c150218100e01051602030c0a060f181805090c1f0e030a 66
    0x1154010954880e0865001542584d10302000d010458010002000b452900e854518a002405000c841c1502c443c80c00030000e030440010a41000316081e903d480755030302c0c0d099009000c0d020703030b214880d4080d11280751207004003c005191400312001010620100ea503404014085a5090f51312108089040100ea00641886031464850b2482440001a01c40e030b1903c406003100c85139004100014000030f8400d00c480403c0d60554185401d03104455035610f60400082d2042c1c07800c01ca04024840e00a12400c240106c42e50000102140b41c0c0055660380350740c4483c203111041c004e0f20107200d420002001c0b00607038800c1803039141c0700750180c45040c90070350f80d541d8a0300f1003440d20400f00d9052094914001c80e94485004000041c074543d180e403008050342d150043c00703102d03440c21400c00d2004a50410007640101d2443d6007410f6035203142c00101c070784510440c0c1d410300e00c1d0b818176a60402004102d080f103082e00385100038400c0344a0750340c01711205070324020140c4410002001a062000c80e200f000364080b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 343402823 1250 343401573 343401607
    0x6030405160b0f09060a20030c10051312020f1c1d03100b0d171902010c08010308031911040503101a10050c1213050d05100f0603020618040606090803 66
    0x440e5402d0001a034151126054410310907c040140035030000b0482c01c002800800203201c00d02c0190405016510340407446114401c01103001030b0103100010824040d0700d009100900c2d110728414199120a1100b1131200f6042409800b001c1c001030100f00982940f9546000b2401c0701e44004020704815400e004503200a403020000c065405000303124a0400203150000000d4154500c041b144d45811366000c0301c00400d04034902200542e41010b00303013044e150780001344506490b80b000d4055140e4849a410740d0a030200000c01c1e060b200d1804e48001d4828100801500407241d00f14200d075007061544c2c02c0e600607120851407044100c400c00b00c500c1d0662030010303541030311701c551b40c0382c00d5090070504001c0500c0c01c1c0d914407202c0e03501500050b43d000a4414500054042c0c1010394001045214941c4c503d5501c13040840d0310018159515030700c0e051541e00f500800011a00100080e864109031f01d50452880c0e01c4483d4284514030b0500005078180c01407a80ba02281e103841c0c040e41c1041080b240b1ba801107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 343404073 1250 343402823 343402837
    0x1090b280c12050f27070605070303090209181e0304090e011103072a020306240607150e070f0303030e0102040905010801090201030b0303031306091106030405160b0f0906 75
    0x221490410b90240302100b4852a489020b9400019210f41050503000e280c0f0140001c8603c0070110b80380080e07050f00300000b5460b041346c4103450070f50b56800090804900410620348001c1d40320b289242440102403240d10b04680300c030318802c00c1d10f140c0410081050700b220300a044aa203990000d010800c10030702642d2040d1302240c0c509001254204000f445800c056108490420110705c52901d069000c1504040140c0c03400400f42c00b0090320000c1d0780010f60f03120001803003201015416031003501940541101d005090201030002601d41d0440e03c0e00558607114049520360749490100d8980c0c0a0310005850740440d00d0b024000c070045170540d202200600080341c1d92007129902008001003130000c9200f480e008000c400000906a8171520004065940032503526209910070300502104201003c80e40c00c260341e1010001500f440a45080c2c3c040785205607603181c2c4144003101b0132081c0038000c2100010604100f10201800340c0301d40c03e1802c5401203010ba070304441c400384003041060901100500c49 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 343405323 1250 343404073 343404077
    0x6060937060e011503060b030601090308030a0609020f07050f060f0c030c040807060507020f01020703020105091e0301020307050a09080706020d1b050f01021903050103021f05070c0801090b280c 85
    0x4652a081407900c4640300707038810f03503a082081c18100604c0d0b51512403c0d01400c10016654078600348500024000c1c02e0340d00003d440340f200003001c41c041204590000009040c0d030403055407254424010750000c0d800c4140d056695000b00d2060049404000c240d040c400c00c4001f0314030a9540310401026a250802004c1000c68803041001046001040204000908503903071201d07a00c071a20302c14030560640c0088031750305541c032940c01480180e8004066556071041916001100800007842c2401c4046d04000306801d0f501c00000c2c400100d511600506040b031103500c414410603a588401390f50740316684a0040143c020703851070507409101e008988000c28454040507030920483d1120360130110002d45240c0320b0380d400281000d4a18265103094401d00c142d080801540d071554000c2001d0044080d085044918000105200c0c50b014106950310710785c0121081d038205031074140c424020540c008003074804000c4d00c40082c14a42c041c02c0c1c1c0b0004000341d170b076040b078402c0070403034210002c4c0c0f42c05040401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 343406573 1250 343405323 343405331
    0xa090b0607050a0516081b0609030304050d06020706060501440915060604051c08040b0c03070c0b0910140409090602040f06020c0603040314040f0806060937 69
    0x310300300300104a10f0358001c1c4050710100802c203400040c400325a5108151603084500082c1d00301c0040801550604030689049030348181a070700081c21481281c110039404906803039202e003445a5076024159551086100304000781d1240015507100c0314080c0c1c0b041804c0c0c14034214124410341c035412500311109010001a032062030f60680842c44004803a280c4259001912010005206105558000d013050329440c3c40c00d400c000c0850164500122000005a16146503000f0071040104943c000e0650144854482e10020f1401c0c1e00c0b03030310820064942c402d40c03140c00b2550369050f00440301c1000e4020500315040d101c0c29001d484d282403602c12300030348420a1000085107202402411042d6200c0c4000590322802d101606242021070f81241e800c5501940d40125a5103e20080301d8003e0340604140102f06141170315401d0030300c901d8001900142d85504005522000091003e0140c2000c03200342042381d40d00c4100226041d84110580f402c4511201200108400404c51784003031052030740d01107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 343407823 1250 343406573 343406587
    0x1c0e03120a0203071208010b092407120806010215061903060c09080106150c140102040b040303030902040c080f0a02090f03060f07020706230a12051f05030304050a090b06 75
    0x305400c54111400035030000140c601c00c204800c12107011710302031420720380714075410080e02007110301030081e085000c0c046c54407500b207003907070010500d440203250710301c40d190b4410392460300c3c1d0200c4503101c0c0240d001c9003403140410300560021806030714039003102c3c0c00b200f0203544039001c000382180a6441e0030384400e43c0c0b29003c0b0119034103001d2215180c0040d200e03680d0007842e0a4906084601950003070400400c0140d0910545438450910a2001c5c1c200502c05002c80e2001340040c024880c691100c0d10a40000400104264041c6c0007109064000c46e010460307095907074000c0d40c0a2508440350741410030030400041c04035005502074000944003031b00e0b15590030080400301c0d260007401d4a500d5020301c9442d080080041d070410192028046900d081c0354540a1042043c40307414150400e219600e1000c01d038032140f2807051450401e44620f6140034005420245030401c0010100c80313500000c1240608040b8040c10008200c80840380b0180580000b1490080301e80d00402c2a110f0055100340100a05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 343409073 1250 343407823 343407853
    0x1c09110a080114061c020a0605190507050a030e1807020d140702011e02120304110405130b0a09030c0b070e0112061d2502030a020d030e0a0b040231060501021c0e03 72
    0x147c000744c00540c80b40ba07901c030782c0c100300d00681e004816441c904016040140200203000450301d070692a616050107818120007100094100341c4078140407101165983c1041106ca60000c0c80c4800390141d40c17220099880002e0440c24607200c2c10001a02051a4580e040361306c500d842d00300021000c552055030100140d0074036401950740161800d03145138a01580142c0d07986410b201d5903030440c185d18400c241c43c0409036a91040b44e04024031038004540d4450311030303040c14010301d00402404e034050340c0b11109181616001d0304003034000d042d2500040c6410f00c40c00000107148511000c0d03a9071154200056056100d010308a501c0041c165005802c042280c96035a6003078110048034140d2603005035848629000c2c0080c94120144410020141004141d1340c01d000c1c040307402d407140b0b5082071622406654500214841816500f038148450703104240a0f072200c9074200307081c140844102c0b400d1140c03da4a0004aa0301d5600c02c2d90541604180301c1001c50f5540143d201045006c2c01400b6030361407400391400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 343410323 1250 343409073 343409089
    0x120d1506023a03090b0906040201080a0513020607062009060715060504090804080111031012021206010923010e01051e060711090a1109061c09110a080114061c02 71
    0x280b00c01103601c4800400c100040c05030040d51104041e80102180e01e06600000d0003000040e00b0b003c3c54540c2d480100b00301c4c8c10005084101075801824540c2d407902c0920307000c0002c00303607647c0510905c000300005511f0143c80000700d038142b4000802050410300d8a40ba0345042c4506886074041c500e40d2803400107030a40703e40c05601c0d041d074000c41081c0e4840b4035241c0b8503400c0d0390340c13050021500c440c00c008010194400050306400c3c3d84400b00d40c002071218902c00b10b803c0d8019404109a00e105100c00003d0400c5907402c14460349070b0452844440345100c100c041c24600c401c3c011034810440b6400140280c2c02e0000c1200c0300750f0708500c3c0c91250115000c0c00300c0e8036544100d90580754003820882231542404c043c0e20564015140405c05c021103c01d12202c810726014904419200d60000556640d0b686e00030b0007400381c1c410700710200f040004000d207400315101e4010034503207000e02d042e000c2c00a10030f501071041c0c0b4041106496a0100f0b0394030b10080000203d116401c15401100ba01e05500c0983c64801c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 343411573 1250 343410323 343410433
    0x91003020609041a0a090c17090d0f0e150a02151009050c071407263d1a090112080d091202070602010605040b010e040b030c03120d150602 61
    0xa00003032480600c1001860301c820400e108d20040642e0044c01400c030b0b00091104d2070781c0102e280074510701103504000c0313035410201d0082942c0700f4004103d40750480705110080500511503000c035000c0030010031103200072500803100105629442d6074104009500c0380c00880d4041841c0c1007040c40d15000b643c070140311026600d4903016541c0145401d01c08108840c0d0010114060300c00c00c140301d1010f1b0b0401c030796a04c0f08001a0303a400c0030f14040829001070000107071500340c40700032076500b40b85004040602c0107016144042804606004207100c20f410542440c80c160f034410503034110758180680398100c890f131052540c90340c40c80d03840840c07202048030451411404040c0380d014082407450044001e0940f0040e8000c2441940307040c82c0c6110782d07a004070f01a4019041900c0103c0c0b8148800002420080481d140c1034140c0541c0c070030761004042d55401032100c50000c0c03004010109446403c00c1e840c14140c010740016038400c004040c0480808904004080c0c04524406c0c0c04581c400401c12000000c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 343412823 1250 343411573 343411589
    0xa020f0a110d091203111603050a0605100b0a03020708090909011d060108030406120f06260c090a1a1207050111010c050313030e0a14091003020609041a0a 68
    0x5a41107000c08402d01c0b011116050300c0c03a02598460400b500b44082c41884040103007803140c05080045030110501284100c0c807584600720032043c2d43e0b800d100b91606440e0608481c00d614040015150001e00382d07568080c0d980c80000b0904000076000140c0080d40800001c3e64018000e00110080303a03900b0710701d00e02c1a0f4a83c03002042c801048e58400300410b8242e00c0390f020980000c0d0043c0b005400c000113513012a110741c50301c402e82e1150010b0403001404210701842c9600d0520741c1c08555140140000b04440c90701c1060700c61501c07a40c00e640b030b880b51031140c980380e4404401d2010900c3c20307565402416013040e000301e650102d00300303901c0040c100700302040c6418065080600c08001640c1c20401214119103207400034401d4a40c409001019440010320b25500381d100d841d4054145445a0b00c0c8050895028100c41c0c811340c1ca40300003202a00440340c1c62031041c00007030001036503450a00d05400480f40d000e03200078241481d6404100c058003540c40c89026942005120070ba0503583c044032500140414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 343414073 1250 343412823 343412837
    0x503040b041401120e0318010e060301091413330f05060414150907050417070f080a05060117030c010f09050114040f02010804061b0e01081608010e0a020f0a 69
    0xb0002400000040d074100041500d8114040b620000c00300840d1004040440c40c000e2401c80e0302c005848042c08040101c0d049034002c0004542c9540c0f540c0220006042e010b5502d80c00c0d980d0480e070318203d0300622002000100802c0b0380c942500b00c00241003000707840a1040180c452201c0e05070310101c170b1802d80c10004554443c0e09100b07141c00d051260300080c1c030070501c000074185030210540c10880a400d100500540c1c40c040041c119a200e502035070060309200b9042c41c030b282244000c01d0b54692140c02101518840002e0008031000009000803020740c1c132200bc1c2850382e1030b1040c84401180e010030881400e020400182e922100280326014003c044070200103000c5441b8140303942121180c01280045056450038400464030075104009850f509180c000b95590740c51614070007500d03010510f50702017071724514643c440036003081040d0644507080c1e0300c02666a45510b41218641081080350002c40c074104018400d80109c48002d50b032154100d1000f42ca03105001441c070050741e01501c403000010f07400b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 343415323 1250 343414073 343414109
    0x20705030a0906091205030f090301090c1e0605180409030e03030f070b010b25020a031a07020d0e0609281d07050915090102010b030d030906052a070503040b04 70
    0x44501621900540a10317071131682e654141d40c0c4c4101c8004040f2a8001b0a00e141140d0b000d4000110b4540e11140c510003d690b20108042d6001d0244907002045502031400305900b849881960441c1c40c41040304090f90317040c03c0c1400000d0070521015010020384041c11403d540b4100000d000d0101d0400c00b1554030f40c19402c0c00000e407a070607002000300350700030040401c0c20014046010100040c101c034141210125100194240d640359000400c101e500403d04000440e4918819100d64040d0b02039403806001000d00315048801c1c1c0300c140340c0c0141d007030210380e8082c101110322040d400890003007140340c4080103d040c60601c1c03040e8041d48880f810303184042c0c0c40d0492861200d030030400700e00b0705074281a0740c000000c10001101d0348000c00602c4c0400c01c090b103a8400d400c500340300b190240944a04d00304881380100035143d12101510950b09240100d03141200b01840c4220100a4202c0d4807090084c40087c611142c0c003410060b13032180f00c07d21001c00c070342060400030300041c400420719040c0024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 343416573 1250 343415323 343415327
    0x6071d010c1110020c010305060303040e07050a03020408190311010e1b0102100509160e150105070809040e061017060105010c0c0b030106020a0c06050a0e1306030609060b03010e060415020d020705030a0906 90
    0x40018900e2b4080d40091004101030301109010f0342d0042c02c0d1741459510b44441e800120000e010b90750104420340300d012062461080e0110f5401400350103a541c01108030704103a10282a148108880c0038181d0007100c1811466400310714409003200144191994003072000c003003406441c41500e5402c0303a03410011902c03000201c4420010020060490050b00314585003801c0109180f0074a0b00350306000b00010498200103841040342c00c44803008008114090440403d140c4d90f07641106c0030a0300803010240881c106d03800b040e507a204294501d001b0101a030902d8011291079000000440d04407444280c049008004d005c05180602000c0d8001c020011030f50a2070742042049901600c14420300300203051085500481d6018003100070369040c546a08a020942c0044c040d40d4006089a0b161800050820815810440304000100c00a000629102d9952601d4002c1078800034040e41b08044006000321164024012041d0540700050038003c1030f894007411540840441000502082801e1004503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 343417823 1250 343416573 343416581
    0x501062405030c0307111603031206080c040b030106080708060619060206060f0f1302070203010608070b07030e030a1e141603020105160609120206071d010c1110020c0103 75
    0x9019140c6869060088001500ca444007419468a07142d0020000c1c030220f00400c880080c0211303d2040350f1800c0380f00319004000c880305020840001e640c00c1208002d09149009110076910880701905048058000700002000c1301408103806540300c0c1c1000032414018810300c2c009104460141003503240200c00c2000388841110709060303180c02c8030014803245600090240d4040426200700d01d0000008001a0242c51282d1180d64000c0a660310030355428040d40140075050301c264001e008580c0c07039404054131000709020350b039600d84090001c0c4010901c01c100100bc0100098140d86082c40c00c0d4441c004580341604820028112100310001009200b01c02d80400c0742c440006800e00600610b06520742d26560300c070182c104078005c2034490444041800c0e552171680d100408010301103441c60480380b003c9681c0107502c0075004440c0014034040c00f800441c0f102d19010032143c84a07841c0d1000640d190b03541c01ca0152a20078208090400c241c40312000d90361559010f4004010800c103c0000505072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 343419073 1250 343417823 343417859
    0x1002130306090b250f050a02010603080a0504140a030f0201120e01050f0f06121c0504090c1701090c0905100302070f200307030206120c0c0318010909182a03050106 72
    0x10750410000c4c40041680207840016000c4c092030321507030f10300a000007240076003500e0b0009848048002001e001e00d64202c4002d0040781d0080609029600c200c0080040181491101400d00e5202c0060200158401d42e1103844130102c032030f0005400030103415602d0844034200c5000d1000d810490a014041d44156130300d0380e1003601142c001280848941c1200e0301d906940c011441440c441820000c5600d00400680c0d000c2e152000d070420012080044c02040040c0440741044036080034070020030080e070f0b94012032a841f44640c8030450420300e0314043c02075100240d0113013410942c0c00c0c00180d0006101c100b01085503401410041a00603610426008640f51810001d200350300c042020030044e12800107440303100e00c180500e0f0341c81e0b50700c1d030703c1d400c60910851b961090a80400200e1241e41010140d04900380d09017a661082d205131180e81175021038121040303560411001c40200780004095070401080346000c0f00c012407030030440c440c035a0610300d0580c03c02c0722165150202802030402074080d03280d40b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 343420323 1250 343419073 343419121
    0x30304020a050603091e030304020415080c010e060f030f0f06010306030b0f0a1107050604170a1d01090b12010e0705090a140f060307031508070501021002130306090b 73
    0x51424140d001410a1145110b100d001c2c110210000c1c029078801c0c4040b08480307540c4904401c05081010540d6266403040b6801c91185140460407001c021103010701c2c2d41501e2003a4014000301039481c0040d01c680100110b9254880001c004603e000725003940a107002d260420071044a6042441c041d145c82c40008020783c1c1058541001000032075004100c00b6082070035105031702c082e901c91180384000341c50410b0000ca000c08002034107200300040019424400e0b40152450708c2500d01301d00101c1e03040d01c60410788a00054462094540d1100080e004030070003901410454552030783d40103c0c851940000030003460588000004210110317204412070752016107460403510300b410740400112100214010041c000c0001c072a070f02c000e5120464440490350009140755160b00c2d203840c006018011215450098003413400700012050b00c00a092400e880058010340424082405408000e400c00310705c6009500003543c000000c502944506030000380242107003450341c6050f10107071710f21002410a02c42 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 343421573 1250 343420323 343420327
    0x15022802030903031c0212011502010507170a2a0c02040b030102040302010912050f03190e010903030212161b0608150a1a0d0e0c0123041e030b0a090b060303 69
    0x1c20760341c04400c840c0507044010302d9904c103140303408a40b00280520f4603005880d030070769000442e140301d80710300c0300e610280507074028803daa4a0007800c50b410405800112142e903b203101107005250b5503001110b6502d1054603a0b0203a00401d19080c14500c090402040403c08a542e030006500346030007403e04100c000e600039440c180c915030000f4403012492240c840c40d010a9009141008418449030280078101070449846a080500410b101c804582d00600498025036a80f11194001c455000c12250182c003d403010b02074801c8071420a50001210012101c2c22102100c0042d03080404003407001650310001442c5400c082c0c0c0500300742c1000e40445040c6a54020906195444004107800e403400480740000c06544100300783c0c0076000f0a11304510103400e0100710004c0c0f090009410710104002d0340c43c1140c1c1c41c54850079080b00c41a02882c100d00e030204004c1440004e0b20741e4252100701e407601b80e0812409a03203071200d8500e0039007660340303442072500c4916110034444c2c501905a082070049010318 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 343422823 1250 343421573 343421587
    0x30f120513061e050c030105040605030a051218060f0409060b070f080f04050904060c03060504141303200d02010b1507150b040f1e0e06010b03041502280203 69
    0x50740048050070081c20541c492050820307140070104140642c0c07040703003001d000500307003484504040e40090150b0341c060f62501d0000074040c54001011041c55411401510044e44c03a000201c1407039119a2480b0105081c050110800d03403203100050000d030030448003580c1c485081c0300300c100580d00c0345d0b03100c80c1d0030f1802800b00501140d6400d41c11154158000c940c943d07111900040001035000c2c941c08160310891400c00c01061002c540c001000318040c65804006844d00c5004220468482c6030700d240600c103040c0001100c9030f0403950901112070003030400c3c80300c1101040101488141c010880030172500517050710000e80e40c0900a1104410301142d00301ea603070160b0300160800d0b0281440c09400030888020850f0103c9480e4081c503800c45011704240021720013918900e004d080c0389011034480c00c1040300303400701101e060701c1811100d8003402c025101907482c0512083c0035030006001550440b450800301140081070388010303d41a048168146200c151000010070030350041940345c019034008004013 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 343424073 1250 343422823 343422841
    0xf080c040c09032307170307060c02030313020f0a0915090b01140a0f0c060e012c0309060a02011b11060609040b130507080f010203010512070e01050f01020c03010504030f1205 77
    0x8008400350644132001d842651192003480d0100a912000a00010702100c005a00021004110050140344140122410700310f040b07031ba0781f000301c8a02c451a00100d10300c10043c034085152401c140001400031610a45a001c403004494500d601208104000c000400c00389002c1d02030780b0342075002400e00c00d80f140c04a0076601400e02c0b03a41102e504120303824100b44001c070301941d10300080380d030020020000048404202c0740201041c4052072400c868500e0b21070008422017002070240151000918100340c403c0c1c05004a0760040c1c0100d10a6540707809001c01e4000c0ca11070207200c02c00850b514100c02c1c442030b924080c00c100e00540302e240075651000400001c03c003402d070070780d41110b030030b5030440d0b05444981402c40c10003001d9040605980909115941c0001c01500a1410b81c7c80498885400800203121240e544002d4821500020001d0300100864074000301a40038016060069071141081e11000a00715801101c00320f0101e0040d480c610721030755010041c041d0704099071500b0412424000c1c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 343425323 1250 343424073 343424093
    0x20301111b28021903120905090c0403140a0b04050106060e042912011d060c041409181603170a09030b090a17070302100212070c020a0f080c040c0903 66
    0x240c20300c02c5025814032001c648400c0070650310350030000001d80c24580c80e0715000594072044840c1d0000602c0c005000308851406100701400380030480f40c182d00e070030703d183d440f0311f0000800140034446000e00420f550204000e034a80f20310540c410800018014201075000c0c1c22800700742002c9009903d48401c40d481010803200032120600a850318281e500c0e801c0000480130403014100081650030b201c020318141c100780040402c0900b0082c1918840c0c2d6502c04545040d015034070464076540c0201803d110030b4145601d81c190400b51840d550b80d01609082d50321844c0c480070254103660b01c41488410001d101c4d403418041c011130702100d2110700d40900c603170340100390310039901001d41103121900108000050030010241c040d81d001071180d91009000a1146841c1c001d8a020f80c05805002ca644040c0e0f9403500c00c5400000c61981c0b000c2030340e200c10000b21241c002c512001c80c2c0051803041c02250301010b074030000e8001d14140c00100840b103070200a1000f82c42c2045100400c0c070000500902c002588500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 343426573 1250 343425323 343425373
    0x81f0f05070509090405011e0e0d111f060b070b06130608030f03090a05060f0403090503010204060f030f0e12070201140a0206060105070f02041407021c2307020301111b 74
    0xc04500310b4170b5074200030b801012030000c000c00c1700c09420820814070180d500201015600034040e41c1000c01140390a40c0c0c24240c1191040094100590340900d428032440c0400024010a10000741e1a0312500381588a5010900649030041a0010444541f80440c000400ba110015050000c60300d00f8170340c103699000d4000c00644003003001c40061000c500030408880e616070000103e803040d0525000d20507042c50305071800d0b80003c24800b03002c01c80c2e0805000315003c540f2a9a07445984a081c2c0c0422401804011011200d003501d5402902ca0082c00b00300481061070042c000399034070041031002400030620501c2d0340100140034065445500e0f008102030354058400e00b08260b4a031600d250044001183e200020350081c6003280c8800e4a50083d07280e607219055a800712241e07003400031903141007901861200030000700d070549a82902d445240c0081d14071440449014104072881d80000d095901212000f00480d17008201080c0905000000c020382a4114000d007000942c0c0d040203400200e6482 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 343427823 1250 343426573 343426579
    0xa050a11190c0c121202010509210c010c0e010e0102071401030b0d1a070f020307050601050f03070305070b09010906090b09040b130c0305090d090803030105040c0504081f0f05070509 80
    0x440080d8070a4041c078220941140d121181800c20b9880c1c20380ca011501224100359216000d00d1200d116041c014820240036494100c002c3c841d50400d154808418040c524112000c00018480c9031030240c401d01400c0680e0080381c807001045c40541000410425600c6e01035811503101d2401042048011516469042420310700803442c1c0c194030740440c0d035100c60301d94010440307901d00048130503400078000f401740550480d42da284c00c074202130f8608aa490292400241c2290419401000245400c403a40c6142c0b80c006404d8444480c0d03a40c540508100440d0b01c11650500001201d550310340e032003102c1c400500f025042840c1810f0602d14210800d000e5103180c9802566205500c240e241e94181f0f1303a40d4643c546507802c0c44088210715000300500410340e0b428195200790b48496141c9401200031000360b800b850001c500356031905007001b000d0710405550354180034007004045102e4509021040c18905d042c10700d40183c0043e001e4807011a0400c010680e8654076100502c001c1c15409002c03268907402c02c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 343429073 1250 343427823 343427857
    0x91e160c0605131e05060a11033409030210110714010302070b010311150a0f0804060605090f010608100506041203270f1d0402060d180b0a050a11 64
    0xa603c1c1c03c543d0014104060032030075003804403014054072580c0844100d44220251040f54644182c44e105a0720004d00c80d9031451010b0002400b4600307400c0368820a00c544c81b03100300311069046600403205c05445501030004414140500070750628040c41c0190444074648280180320001c1d040743c032041103001c0d01d000000071210030800c1e80e1103501500ca400f50045010440d559480c074244444107014040e041c02804d030000058441c08240e400c0e03c50819281e240c8550001401e542282e5400c0d00a204a420b160380c1c000106054580480891191070f10380d0b00d90481d0f504011000c2c01044006010004424814000b80b01d0381d10380b2000c0e00e040b11036448031a124041c0c14602500c200e01c6640100507200c02c42d40c0310324448900d80044104503614000f00908035600c4d103c542c4a410b44c0020092480e29101004c80c0040c10a0001814008154400040d0400d00040480300b8560300500c103581c10001c440502120b15032512a2a070003010550041041160084182c20940a01000000c3e10b40003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 343430323 1250 343429073 343429081
    0xf141c0b0601140f0409020306240f130e15010216081b041e020318010908161b030308160809120c01021c06140102300405091e160c0605 60
    0x1a06484e43d42c0422581981c8a035100c0251400a41017112a14440c22100000c1204007804c040c06030032141504141d18034000341c0c8034481c21940e0241c80750b003040c990600000241c0d000c0b1151601d000c1d200e40b04003e0341d0b01e40b0000009103401e4048d0302e144007030300003014200000707100040c0b1102c20100c1c0f07101030100c20f00c1d8080010028407000f03194070040301c006d010001460482d03a00851064011f02c02d0b007101c41400d000e504c0d0890305414001080603000304009034803904041400c1d030901d48500480c18007018003049043e0700c0440341d4400c41c0425130f4a81804560040924820385025643c5031003011490800105540e030300c00e007500e0810320000002c81d095558001e40440b88a101c05500c0043c0c500400b00729000100b0b618810f9000c03501c1c400102900a41c808a01110364a02c504058159400c913103d41d81e20b1610305041c0e04010031030800001909444046405201e50851095082000345010640d0303d4110004c1505014007401c200d801d00980e0028030211a0f00d420910000e40c13540d07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 343431573 1250 343430323 343430357
    0x30e060c0105090606130c0801051903020307030803102106090201020309040c02030c15060d290406020306030106050616080c190507030c06020601050a0306150f141c0b0601 76
    0x31031405005219401c20041040d420b8002038840c0c09184190749844803e03400f00000c034103e602c1c01207000300107414480100510b241901d120042140a0030820003103607074960006e494020f045e44112841140802080a104140b91400005108600c52910344111624402e1140c0b010000020400d40d43c0303104040a5902c01c000b81d03038007040c0142040160b0078280c130019540b9008000004014403c8040989080350a20509401000302a00200f010700d02a910b400b48211500240c1c903080b10010309203105441003a021600440c002e0380300594900f858401e0500b511480d811407030040404000304100d0001042c18019280c1d044a02580c4904140e80c0b02801c08108a0318070441d542602002c0041c0a00841d81c3c3c022203100b01000b40032130b580c80005a13140c43c82445030f036501a086900400c045031041c0c121260501d001e040c80c0e0b0003e5110000c1c802d25104035002a0030100441c20056020304241a80d01c0402800e621300e81d60585140d076070b1a074040e000800042c10050036510b0207078000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 343432823 1250 343431573 343431577
    0xe01050301032406090e0c10020706140f0d02031519121a04031e020f0a060507030b0a080d030f0504021e1507060207060b0603042109090f05160503090703030e06 71
    0x4461243c052260642c1c0d4041c10740540403603104004940a00390301c0708410719011501c90110f9445801414a0301e01d401e2042d941441c281c4090840b0030740c104000041d6008400040503140002c440c0140c50b0305268103081110046400e6807401000290344041d0310251788a540d404035500c002540d000700e6040d1512808144400c1000c0c0d00b2091904240006c0580100406424103501465900c1050141c04101d965140e4441c500c20682c1002c0f07100d0004c140310350480b941c020014140442d100c0038043c04950524000d43c00203059410000700d42800a500d406103c02c02f122101052003d4280b580010b070f12a1400d0707080441100d601551541580c0301d6403104004c100c08686003e8440e4043c1c24501d01135404004110b0350a841d00f41c15003540c1c42c0900660303000b240c02c007401a4901c001040c80490864615250754180245a8000034401c03c450045a0110812103004112414002c1c6809d4848955443c0c0e402803200500811880d2140010541c0450746c03d4a081c4800300b1011011450034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 343434073 1250 343432823 343432883
    0x706020301091a060301060c20210601080114010510180605030a0501060801140d021207120c2918120303090609010b010f11030405030102030f0114010e0105030103 72
    0x4600200c000500021181e1018100c112810b6503071243c0382c41c0a007000284d10090141401003404400d4940116640c505200740c07444620748000c604410460000c0d1120200079141c110851410391000340804052002d1801000100024400c020851107629090401402200d02611000c8070369a4840e2103594000c180c0908240a000701903224132000788a0303402141c03c2d41c22642400000a88544141210750495010284446103151044108160111b60b40d600b43c0e4040800300a4604140003480a070700140b130441c0a29944808500c0c000780d0380981640140010001800c10a14038604402c030040400300c0d41d500c01e582e50705c080052500034120410011b801908a207081c928004d400030084d800703104a0070840301155200e009150036a156140b40c01c1c001042c012a040c40c184c041e800c0b0004c0302d2003050070b032414941c80d00c01203404c84c0c20807140000f29810601c01000b6003440107042a41025003864812919114100040c4c418801844001c22400980705605610401c0103004419 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 343435323 1250 343434073 343434083
    0x7180609020c0607021209010e010c170309100e010b0906060304140a08070b0604090c0504020f0d05042a0605042d06020601090f0b030a02010e0d05011407110a0c091107 74
    0xc0341c549801c1956148022144d500c054414450822040c004002c191091030780c0596400d8003452089004481da040041c20031950903200e4040840402d0120010b18426440d0100074842d02040c00510819a0006c40e0703001c5169242400c5007203545c45600109502c588107450050b42c0740c48502d0022030b00e11002c0d111688500480c4900020800400014076949000341c02e202d03541e85462080008131114104000c056a00f402da00300300a050540180190040742c51246061001042580c01a036500711001c48500c0d042e00c2c1c0c585042c801e4165100c00c8607000300e0700802510f05181c4013904502c5540544003040b82e10300240400e030324020304001016840d84ac06e240c10300d580d404000c2c1d9900e5007070140da1b11250424500210416040c4102c02080400070001c0402460300e800540b000842c0d09001600000c0c3e0103089804110240034401044800c621075403140d1070702e03d50003044c880701d4040061040e000700300c10f0302c08580b01c0b0070294140c8030310b08000108c0c8914450742a020348644500201 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 343436573 1250 343435323 343435327
    0x31009022806120203190c020114010b03090706020318040f0e030c0703030e030a0503180319080a030501050111030a0f200c040e0a20040902040501030f05011407020718060902 77
    0x14090248581c800c0c120703101500c4115058048000100507404200c404521a0084001072041c00115401c980381c0818907000004060101c81008051100c090b000741034040800814010380840c1004844010403091020310300345804000d0440d503141c4105a610720a640b030b502c18442e90052a0f004a4501010104507561342e0010100c0c15110b030641c0c40b0550106414240841c5682000300c0c0003003005a01001a51a00040d5003140155080c180c01c2550980304003020680e4004045070340540c018040e05c401900c6021152004041e82c03016080a1704210399207079607625100f000002d0710304900141c10100e00c1c80c600b8440c211040c40c500c400080001d1300207500c00c0707070790b042c0800d01c0008080306540910460a0140c40b03156601046100141408031001e8103608400c1c04106246201500420101e03542d45c0d542c00190a0310300a80007564030321458020141042000d00c60804224141d5803100340910380440080d403943e160344603001407940200251000310241c2d40c4070b00080d10042c6000c40d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 343437823 1250 343436573 343436629
    0x1090b061201120201080f09070306110409060f1e030221010b030303150307120c06050a0c0c030b07031530020d0f02030d03050c03130f0606062c03100902 68
    0x84210f10100f14160301003126000440e002c1c00c5903440d07683c4254141e900601c416869650b0b840000c02403040c2c80404039905020100c1c01111074005c5200401c100c20407425124201440107070030200025030240f19030080c00003080107071075440b11020309900301c1c0c604005d200d80c80300ba440c0c00f603c44c410945505000c000204403d810319040c0c0c0d820322006c20f40859a00945580040402140380700300901207030104c50303007080b01c58810001440401c215281c000c0341c041a0741e882506600301a00215030210341030b02003110880e414420481d000da4045000c003901d6140040400941040c1c1a480c3c2c449900590a0740103900003d02c8281c1582e0b010780504078020150509820b41400100104d2180c003407104030704426403003806842e00401c9544129851629002c8005000015259040300d1a203020349410011a040e803013100000c00c169200e41c0300224510540b0f00c0218002d01c501e48112402c89d00031182a140050701c41842c0d2425403000071741000b64000181c00c0e0b0307510301d9205e10500810240ca = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 343439073 1250 343437823 343437839
    0x6030c04020a1b1b0501020712060203180a0303020706051f0608130b01080303070206090d1b020a080d02071502010905070b03070c0f06020702011b030c03080c19050301031103030705030301090b061201 88
    0x120308503600c13280b4951409071210012130710740025225401114444144030f8000c92056030056400c0030880c1211342d81c0303541d030210844c10522880303c1030703010070360100b00e82c014450300d03008640c0c0c880110b07000945001602c903101c440d464030900030007003008911070015040e51a4040220010354218001d6455580e41300381d45a40c0f5031040b100e210050069401242c0e0751100000d144c02c0d400c0041e02e0b441181207151001070309400740e001050764001d44d10f00c40000e044400344903d481d490b0240e8090b2146604040c040f019414546a1080441e894032845402282c008030740d00003503408920091341d07217884d841000c80d448491144040e1901752070594a00400c070080d402010550303c00c2e00e0320b0301d00c651104c801c0a41c0249404014000c20300310800040003a22075a051688011010003150901c0b0b91000e10b04050986054040017152000006106000d00c510003c464018201e0085151004594525881c0d00040c4640780185860380010007080e42c03507070242d0381d0103c802c070300040441d80d5038035036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 343440323 1250 343439073 343439093
    0x509030a20191401050606030a0207050a060e0a0b070f0c030e0301021908010603050604090c0e0403030e010e011a0a0b1c060b0a030b0415050a15020102310e06030c04020a1b 76
    0x440f10400c040e003c8000036031040c010740340300e19402044681103503107004124002c0d5000c00320881d41c50007058042400900c1e0741c0724200948007180002d05042c1101d00e003149a0b80d0b4040c2c0711005102e462602c26020300e6201e01700020081d071500d0003c0a140c042d4001c240640220300360080001c40c40b0781030203101680818443c0c100c44c52550148038984440042c081102c0134508050028038401c82c00b030003100003208513036400c00d02c24030b0001819402140110700b1103030052407003101651100c2001e4103170301d01d05404450000040304e02402d21440e0591a003060f101e04d8420b14411780c42c0400405d512141380c2c0c80240101818000c80e0b6591409100003030007052000c5007188201e00d448242c040762440c040450041e81c101800c01a20142848600c03501076801d00c102008540d020000f10b50382da11140380880400c80d01014414592584c501c200d03080c18420340196403081048010428160340003d2958101c060a0b47e0060760794085450454548014546800e50b0100c0910141d0403c00341d006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 343441573 1250 343440323 343440373
    0xb0901030515070f02070e07020a0b010905060a06110c0904080705010504060f110702220204050406080601050909030c0a0b10080105090a0302012018040b0a03060b0f01030509030a20 80
    0x4002c6071542c0c41000583d8218043c040000050f80500c1050245950416050b0f4000c62180119030003074449649503440750801342c1004440eaa110414010386060145080000d440582440000081d01d400c2c6a03998070054008241b0a8240c2408035090008010450392690b4020000740f0283c0341904000c1d01130189154810345291401418094040f500b030150390030240d00511000780215503201d992404c01d021080080300781c0e03080100107802c0d074581c0f00c0c1d41c005108000c050301541d071408080041d550401002d071680c542042020300c4071300d400404d0b904c5160340d10240e08e0036540c4541c209a05200d0f41342c4c00650266181206000240c2c90008181035094800d50007401441e0b54212184d1034021204602c0480f1942400f8145140a90280040c3c00c500090000109000f030000000c110350843da0007a640300c0e0b0748903003902841c148591940d01c180d0007801c040c016424111001ca9480c0304d0509103000300038080d4001241006038406070069205034608840c540d00c03008841c2e05451030000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 343442823 1250 343441573 343441603
    0x917010c0914061803010e070303260c0d090302030d09060e0616020c010804050c0307030803010e060402040308040b07020f0a06021015060c030f1107090f0506031506060d0b09010305 80
    0x200184002542c141054a054050001c1c0c0c10070302822041000b11003100d80c400d03890f54940a840003421402c0000b24001e6010744d440c01c1e075013188185540128000081642003840440042000320f00441e802c641e41c140c000e0f030001914400500707040303045004078128441c041381001c0700c55061240c1034100c1002540c0d00016a50207441e005050082c502201252001680090807030142d82d6000c0c012045c0e00500440980c1c540082c0440042d0810406030000c5034a20f801200610544901d580a140d1105058408518003411034507442014001c51080d210002d900140039030440d110290300140015015043d442c00c9501c5100103505e41c4080d44048540354038203264811240703103480030441110142d0312408803418180c1c4084819020b421080300600c010760092000000c0c081200600410440d6000100c508805003c041942d4016022900c00c0d400040010f40c070514401d42d1a400100071036103184d13103540c07170404030001c0c2c481d40e0a5103902400794000002840404642c503042c8031125 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 343444073 1250 343442823 343442837
    0x5040f0b030f060405060703091a010605030702101802060a0c0c090203010519050f010e0d080a020d030f02090f120a17030a0b010816030c0e0d0302070f080106051309030917010c 78
    0x1070b220550b9004212000b90455104d0008074040900a41c0140401c0e0300905034800709408a031503410002c042a03104400003000001003001c49a418001180c030704188800910140e4a1140801d64200e0111400f9105540000344801014022020744051aa21550701d0010681e1080b04500035002480380328051034070054118005071101c1603035010b0700c0700140094603c1d40420011540e8402050007140c101071041000004203160102070612681964000d0103840306007040142036602143d040c8549138011302c5628a00d6545985203070318080c003600c42c1040b0351413850303105203001091040031b41211105002810700c074021100651142812031400d0104032910030044030004011603d0004004220b0441d481e0b1601c2600320403511600e500d8a0541603040b8000200301c502001c00031005640418010000005040489402001840b00810144d4030340000b142d81c0f002540e4040510551300e04091080502480c101000380c074182100384813540401400e02d00030302c05440b0000c085491 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 343445323 1250 343444073 343444093
    0x22080604031d120607030c0e03030d050408070b040b10060309110909031c1409190b0c0706061d15060d110c060f0a060f120b09070b0f07060e06011409040c05040f0b03 73
    0xb648040400230015000b5441c01007248003850090001400032124850100251404680340f00c080d280150b003d03d4100850b0b041003403104004a644c0e0740071205143c1030070018030108003002801c0070301403c181c3d4000e0695aa1469103400c5d44a101401c0c00c00e00781c46486100101c565500114070085400f081404035103034200a86c0d91400c01000840026204081c1d10001030341c1c0248154101808045440c03c000066807024281c075030a0b04541581030110b5400d0000079801107000b03400840a082c010342c0d0040a9001c201c1c00d100781100300300754644034030706d80029060120489101c1e0a41d001a01c0c010304004510251800c8191042c080f814105400800c0040740c0c0043ca400b101e0b0f081c070040814418039034403100e2100c00100310003102c2c000e000340084e5094840c801442008080015140d84130740314034000c411942c603d02c081001e03a2092006000d060440041c9012145044910103c0f503500ea14206c10403500540203144c015041003601010503025802484d4522030490035580c0e9029 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 343446573 1250 343445323 343445327
    0x9060402120112060612150c03050f07181e0501020d0f0c0f0503090409030f1b0b0601140c010908040905090109030804060b0604031722080604031d120607030c 70
    0x1d6207850442000750000104003642c10200074100e060300c1000041600c9503200c8a4980c0140701c45001c0d180c04605034295081c0149600c28034024207407504040205003005000c400410300700030051000d001c0c0354440c2c041d06040308081e01c0700405c4105625820950801405440800b6510410340548105402d000000f8014017035144403042036a500c03c1004195210f50300c0d0148074045c00d9526000402c4986042c0d150b5000e8800c0060003526214200382d0000f00003000104000b00100605004c00b00c40740004400c12075480c1c01c142e09180041d02c1d41c2805100280d9803252200c040880d40c40c0202c054100840f0f440074004483c8440c50403c2144e87e80d03402c25080c0c46c01d4072001400502840005000201c05900c14000078502401c020700b041d8903903035202603411107803000007800c40e8041140500d1803441c500c1703400d090710250311001030380e0301d0041002e83e0740c2e901400003028000c402d110800807640b02e131600c104031000103014400071910030000540790002540c40100090510f6900d0998034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 343447823 1250 343446573 343446577
    0x30103061d0a0503090603040309120c050f040908042606070207030201080f0106051b01020c030f040e06030a030c03031802151b030306030705010e1804120813020901030b1801050106050909060402 86
    0xb036003002c0136510b003558544c2080382d294401401101406854180851803103501c441d030762003007441481507180503070600c020849011200301c1ca0034172440c102510315000074110030030350702250b90803a42c41c206041c001010841c074650780e00203c0007600c42c01d800c014004d5070010f13030034003224000e03258010103440d1003080b0403218100b4050040031400410410880041340c00c158134071403110000050804c02c03070304d040500b547d200861028401501080a01121a29031409900f00f4412001000980d0480e03502a064100c9501c003d0241550f49240340e003061284400d001c1642d034001d002d07103c02d82001038165070641007880000344648050300241910103001085a000b508024000d10b0a14500303030045900c941042c2e80641c000121020b104203420015800034040d91042c88008400d40c4440e50040041c140200b03175036901d00c0010f880d900540c4030344030100d056070303001040100c440c0c1e100d8000c0c11000b1100700d5200d00640ca42000029555804005800d4400e41201d8180c01501c0d1001000268 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 343449073 1250 343447823 343447843
    0x40b06040515060a1130070f020904050114070512070201060612110f040b21010b0f0a021e0708120301030b01060302090d050f0705131a09060d08030103061d 69
    0x49152030515a02e03d0300718090b141d0b0440500d0300070207502c9541c000904203441c10030108441c14142409000503100f98103584055444e880c0b0260038548280c07100c030450461000b01070b00404086003c5412b00000b034019060310005084241d0050814400040c020360101c001c000c8018420306c0403c49944c410f004502c1219202c1d62020403500700c04515000130302c00350060180301e031020002e80c20904840b002400061410048803901c9110300901d248400407010022412450380e440144401c44031001921440301304503003541d840380d801ca081030f0701d4615015a02c2e440c9030740c00050070075408000142030060321906000d90b05850346281c00110140000c0c04006c0c507000c07001005008151081d0b005e4585e025000700700c1100b0001c940c071246d0802c00b020790b001401e90000e0f0014443e508050300084102c0100380d90810244900c04440f050b40c080c500c1210703202d144110045209035544c0e4415918440d0040f03419944da581da858884000d00b440315040d074201c43c1d09000e155442c0d40204400f041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 343450323 1250 343449073 343449091
    0x100c091d0f01140f060c2b0f180605130513090c09090203120d0b0603010e010906050f0127090e0705091e070e03030f0d0c020601050609012109020d030503040b060405 73
    0x807034280d1404204c4503412190b0040d0a511401504c1d1f0403001840c0d042c9402003012440401210b81060801010108440d600d41e003444124019030385080905801802103d1061800d140c50308545440c0401c0301030182d0015038030203501ca00580c0e456070250301505013a8400c00c03402d1a80c0355200a02002d0310001c0c00c000c0e60540108080c24084030944006140b01442c044002881501101c0000e40301d4001b81c001e80780c005e40e40781c0180070b041414414140901811074513103891350316880001b003c40821701e59842650980c90245003001002c21000c8010740351a450038000e1212007000305944804512a45109110303050104100250601407203040303001d020851304456680c840291024801401166090701c010081d0007400d002c05400350941101100c000310f8480c0001c04000d28000c0e060b004144941d504109402403aa04202048103020244c07541481c10032001000c00000c0c045075001940140c0406c10120401da03008000314400d92040c00e0000c0140c0f10402032008444c0e0407588084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 343451573 1250 343450323 343450339
    0x60f0509060310050306040b0a1a1c030e04050c0a020c0604061b0302030403050610080114012d03020301090524010b09040914070611150405100c091d0f0114 69
    0x10318204080255400045402c000b40b100f0b80da000802c0c6401c03400c40b4151036018030b1000b480115505405080140260103c2003150b80c5513200004070a141c00311500e181c04c07000000030b2010503014030140d00040c41e0040007000395191910241c220756001000f4200140202c1c005882c0c9440e004003540c09843e2540d030744c22041030b01d25041c0c0c3d4014070804070940030341c80213210000000d803080082500c03031000d041459442078a0310861070700391510100d14020b1640c4c62001848840325540d2800c46000b01e00c4021118140c908610410262680d00007a40650030480d854007440f00010340221071741e11148460107010169800d94041207028000c040c8213040400200041c0d10b0143c0207002e1940c0220045003d180c0c60001d82498004180c2c8903901003606800001e950713803c2071050075028027800b400d800f40f503d0a641d486854000c42c08070310240e6a41c914003040c1852213480500b001d040c2c02c0c041c01020b040703444a84c503024007044031250344540c6858000710300d000c0b181d43d02d03e14500c40a00f801e9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 343452823 1250 343451573 343451587
    0x1203030f07050705211801020607022d060a0c0e1005070b1b130503240117070b040b0c06061c020103050a0b0a0605070506062704031e0503060406060f05 67
    0x212183c2c4180c1c0181c40c0c6102e040c54001c03040d40780d15041d1085580b107042c03076540c402281031840000003501c54041e0543d08800100070209401149010100c000340a0707035020003240c0401d8602c4404615241c03c2c140c8108001c000c2c00e800154050b10b1140200d44a01051100080411684075051009400008c0051003032800252849040582101c1c07a42203100725420300505841c030582029410256004400360100224101440072080d011510501c1e82c22150380c80d0847d120740c01c01072242c041c94140c4285104110481844138901030100110529501e55a80c14207840329006101c03401d840d40a82c0005c00c0141c9000101c460070f404070b46040a103414440d400540042c02d00902c601d42c0f854807a220a40c1555410090b00d000d440e698890a40382c691504040c1e00d48040200054041c3c11144000b8050b24074040e00044080020b00e21482141c0c0d840c9400c0303800d000c0307685106403000b03040c3d051040d060780c105025502c50f0000f80d03810040075980d0300048400c25807610203100481d201300054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 343454073 1250 343452823 343452827
    0x1503070602030d2703270b0412060b04050408070506010e071707180f06080a05100302060c010b040603061e060f0b2a061e150405060f090106020c1203030f07 69
    0x1e55030700802c00b844c92034901d40502c10b0600034503220108400140503051071841111202041c1c000074040b0500080c609410464001c20a120307a0188041c00d0340304181c0030f130800c4120340040b00540c1c4d0141090019090507c0c09010076040440119590f01950001103024443d051020303100d01e40c9561801d1403103035410f042449504018052400b000120300b5039a442c2c0c0225440d2000406d6200a8842c0145c0741c0b02c402880c26001a121940c024140f00501180d82c2c070082920003a6601140c400c0da403185256030303842c01032008403600c81d046400d0400c00024000194440d402a28464485030301440b9500d14140850303600e4080c00c0ca443c0301000c014050200a038002c0e001841d0301900b058000194411103c000a543c4052041d40e54045820007101281105034101079a40d130500e80350f1503040140025081c4803180c00601d00442c0c0c1c070710010303c0540d038400005210b008003a0554450307503110740c0005d403160707400e450f150700a90003081600102c10001085074800d5400d003101c940103840703003001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 343455323 1250 343454073 343454081
    0x120405190f29010303020d02010c0c050307020906030a0c0905061005031e1003061416090b16030923040c02030c0a02120f0f0102090a060305090a0609051c081503070602030d 76
    0x40051050340b803400240100610a41c1a004c1e5009070010a9413140c40c0c5402400e40740d180b042c0c981000441d80f0003400054002003914403995048814450b29607440020074900030080e50302810403201e00400052911b144c2d403040d406481c0540c1e2004407640c03511420b961030300c015200c21400d10310149007404100118081c40390850544203503841890b07500e8580c40c0a0364104020300c082080d585040c42042456026280d100c101076003081440c2c075107885954242e0380505200f14942e241d0303a914903400c240c4030302c440c1c402500c0c45001c0d00201e100d40c6e40303d4603042d91401501034010381c500b8800e4010b6038000420345404640c0400207168402240e824441001464802c01c145880b5080007001050f10510a28608001401c0016210030038001042444d110710350224007414504010300140da00c0c00b080c0010460f400c03500100750010249080b500e41130300d004082c3e900801a4000080076640704201c2d9000c0c5944100700721109408070105a110041c038481c003809640204041220252a504 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 343456573 1250 343455323 343455353
    0xa24120b0601110d0302090406080d210207081611010815060c030d05010621091101031e0c030c0806031603240c0c2109090f060506120405190f 63
    0xd00a1070200f000c69507946440ca41020501c04241c001c07800c0221410540304110042a840c401403800c1d03207071030300d02408503032100d17a10400e0300180707007000074000070550110351902e07600100701355540f100003500011800c0340800481d04101019400401c0d0f6201e0000f003800f0b51010b5500d01c19000c0e808003000481d0780201d1712004180070900001c4201644e9100300c600801d150b03203a04580ea201030040702620310b038040c541c0344d400d4548440580410595400d011034174000b8240050850315808000282c8400004051001803d0034450b41c011a80f5820150041080d9150a1456141c6504040e21081a1061020032000c0004100b011843c00300109079521000c91881100c41c0b2500c08aa0540e0a0034000d00c2c0404c5010a00b1404c100248019090540e41c0d06401c8280321154000240300546912801410688405a105100009038030080003068001d0200340d844150302810407191000b194140ca090089400c96010720910800e0386805c1648500d01280400899681c1030143c10141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 343457823 1250 343456573 343456577
    0x90103060b210c07052d06280b03060604050705040320010e030c1503180708061006050a140d090807060914070501052a03030a24120b0601 61
    0x64000400702264801080450703030350700c04081c80121080841c200c030200a000500b40503020403a000204038003080018541100030b0f8030007107400506c1c0032000c1444040418980342e00602041c01121644e08001c444108103004c0712405010003503960700c08070346c522112a50150010b000092841c0f5142d80301700c0c0c1c4181141050350a05840e07840e0314103082d02038080c000c111000320f850b500e03081da084003240f041c10504500a16550801c20302080a910242842e41074008021000c25070900c1c1d02d000910720715003750100d40307280d6034913109140c1c1c418069410b0810025031490200c4c04c903200300d04440c07548001e600c131014009224480e10240d0307801120741c10840369940a8420004030b040000308034660003060b02042a900314180303605800c24900210349940d1007102c0c10011039811000b0354148454a0381c2e0704012442c40441c6182c00806c1104c40d1400b80400010840246200d9018068078561400b0144074084041c00e541c542e0403850140290800c02d6a110400051000e500a607202c9018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 343459073 1250 343457823 343457831
    0x20f0601090203102615060d030f030b0402070b01050901170d08100b0f0304060e0706171305010e0f010c0e011b0501060b16051002040e1f0b030a0518011a06090103 72
    0x60040d5200401307174901546100803150b0746100318044200080c0281c00350204100925040207400a1054058880000c05020020041c915024003a52040b0100b43c13000d0001d40d52031300e03e8940b2110010090107118850f6040f04002b01d2072407014188069550b111030014000540250740030740314518003c0001c07400707003104100481c000352144c01501010803180000c540ba400d2600e88035090303c1f4a1480a400c41d80016001c02107558000d01813040c580780382d5182e88141d19400006c5c0c82d1212070f020003621a60070034401d003280c10f800282110201d80d028000304040c0701c030754030b0855214007007900380e50002d0030840070482c00e50f14044500d003005104200010300d50780d8881c1200d00c1508480e00c0c7d4420310030045100e806002c07044c440304249c141d02040440c9070500304407200002c0c00c005481d041946080050320440108486c00700005081008031190b224501407403040c0103031904640b40c0c1c03848800400603668010050140141484045002c0c440003032641c405e0140b650002d030744550400d40c40e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 343460323 1250 343459073 343459079
    0x11120c0a030b07030c2c0f060348090301091b05241602060c070b0702100e0310020c01020d180203010c02030f0405041107050f0109050d020f060109020310 68
    0x29110803000258424141c0c00744516141d4006000c80c0d000200c04070522120740c0718054003118104486460fa412180300d80c90309407580002c90010b40c000031409800200000500071041c11180050b0502c20401c4500c59941d0850040303c4034401804a10318800f802c41e410307445e52020294040c1072060000750001032081900e884030012007141188100d000c0042000a01050074a20840d92002400d000c940740d070300c030310840381005500c03485a0a40c0d0141c9040f907018110351301c1070b007254020305400d021105100d03107424072917a15600078401240f04004000c83c00d12035600401d801800c2e13950041c00b520201d0304e0340990034081d5020120300700b43d0795420407190403507405074130400502c2607a87c80c1c400181070040c4103050868048022050940d03000384030b04c80c0e0407803508080b139040d25400e030303004901c1c14400d9243e46058001e80741e00422500902c01c00e01440c00781540400700340e5010300d048039202c40300e039281661113844c03403a004400c6c0d4100c00d0060188121640046030000a41e800001c503b6039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 343461573 1250 343460323 343460329
    0x2010e040f140426030610030605220f09030f080702030903190506010b0f03070e13060b1e0406141308070f0e01060e0a2306130306060b030411120c 65
    0x30010030300c0e40310036004030603c0180b0503507404040044034082c2e04450004184142c92101e40401881c1512403100540c0107600c462103500400000d040180030050320382400d0315070b107151306e542a140c036100e540341c6201c8405212003405072541198050b19213404400c0122421100d0540044c040c10641c807080000f64542c3e03c08014103e28844d50601d41c4842d180189049424410180d124059046041c0074079801501c0381c03000c0701d0304a951070600321b41c420003000210b10105003401228400c14030301000026500c0c1d60200a15014070004000000340501220600c01402107004220009006500001c4403500f43c03801004203004524001803144e0340c0307100c031078642603d40d04500f0800a802004000303c28491603082d000d8402e03400c0c84452406000082b6465030624840c03120082000b512040002c2e104003488001090044d007919034502c00c1c050500b05202d110320003100d20a10309034000481c028041d0980c0d000e580d0002014810001e11002c108c0207015003182513146000d107420001e181e40e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 343462823 1250 343461573 343461581
    0x5071b0312030b03060612060c0c0a0b1003210e0f04060906080c0102070602010515060a170406150605030f15010909050403030b0a05060705100c02070f0305060115050f030402010e040f 81
    0x115182d03008962012001c0030315007841070207422903004214000042110305400b203441d582c0440b003680c82540f254038800e00a813404012040c00f0f0105150001804110004d0210b00313401e8a0041a83c0128145002d5032041413a421503040400102c40400a601502d0035181700380040c0b030700070000f04086880300c1d14001103407156804402680d1219480a0340c0703580602c500002424140020401c51070092018510a1180514544140030026a0900396800380349081d0b006002c05d006ca241900d00b07464244014071000b11802c00c8041700810001d40340348100e007280c6c41000322520b15802d40d1100d0302c0f58441d21101030407103411710646c43c5c0045280c088a00c50944241d0095901240d42c0c095241808440010364104e14000c810410070b060100d003000512a00d200802c440c0007546268510f022801c00d2181e800060003004100800010b003c8000f840c941603409e002c1c0d40c1980800140d00540321071281e046c203018a070700e091000030050b40c003c01d88010302c2c80703004d8004075111f888848010121 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 343464073 1250 343462823 343462853
    0x20a11010f020d060509070e0922030f031b0e10020a02091302040b0603063706080a050907030c030f0213090b07030b0102120d093e010f05071b03 64
    0x1c036a01180e01d103804005030180000030700003030703074103132202c2c01d280500814000030086540d00952405011680d40c0349408200c412260030500084002c0c1014507000b4241c40c0310140f000002807e120111040c0d410600841100c0145510b4000c040c94085080c8104049032555640a5008a1400801607120484540c5c4070303130407500c100c201c519100c0c07040008803000c03654854010103061003008619150603610ac2c81030840150503c42400e100138a0041a0307402402e42d070f824280300c150005603d0340080e03000703005180c102d000b03115507958000c1066507650240700c003030050788105a0800114a00181ca200400c0c0094005c9640d15607c8020303405440d10040d0488803030b103110040088031b69041c41703070008410302480502035080303040350901c0d8280201d11091407215070302e1440808110781e804100800b0802505002030708200c0d1059080300d0510200070528134212815240301c00c1d0710030414a401340c440d6449040c244030964403000c000360700001190341900c60907100407010030041c15007140a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 343465323 1250 343464073 343464101
    0x126010806090f01090b070509040621060522080a05040902040b0a0206060f130e010b03060c04030201090e04051c020115090f1104050319241407180603020a1101 71
    0x11500b0050505450f00349206280905079141c0405400010103102415411415502d407881e100d003c014002001010786502180b0550342708001e00c102204903080701180c1c140900402c00c81ea6452150300d03c145a02900d80f001401c80c200c4c82040000d2100c0080c11050383e26250090505450790400000c99000e03800841c0c1d4a600446e12101040d81088100c0d400a030070f80d2a40307411076000c00407030b2a00320b6202c1e004e40300544460040c110001c096200c91000c22008023100c038103041c107154a41503036000e8013090303001880420300444d008140220303842c02207522030000e0000c1129030b01924082d43c2410078a00840d5290403030a94429000001d82c005442129000200810644185022214100500c000101041c04200700e150b4000c540044ae04c280f20103401d041248a00e04803032a4015485511050032003c1d00610700c0701101e500a078180e9080c2c042800c21503d8486007030761380d4a240852204000309076107047c001c1e42d11a070003400b04080c032401d0601c03802c503031011480c1c25200e1218a0a007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 343466573 1250 343465323 343465333
    0x80403020a06050a0206011701020f121e070e21033402060f250b09061311010f020c12030d0c030b0315070e04020a021e06090c01260108 60
    0x551070400004401803610341442c500d07010030300d00041d440d080c0c144a0111000d031240c0320600da0034001c3d0111107002401d64105903545180302c40080d10030b1015540c803421030843e000301d0f50316204403e640c2409076203c0c0d117540c0c50390041042000800c0c618100309030000701880301003461040302040903000590380940200740c000140708152000022100a4a990811200021000d611088112141c00c0443d08005030f844907420301d05140440c0b9803c0002c9442c41402c01c0e075081c0200300980703500030b2070b07400c0c02d0782d503562100e10300042e050203a41c030040d1109107c0404e5409560040b001e080c10108140191000340310303001c0018000c24450a910b04090704000740c010b03c0d40f00984a001c030903111038202084105070310800b007552000d103050210002205000482c42c6140600d0150624010080c001d640d1103904201c0203482c3c5088036440241d54003e806906003542010840758420384004000742503060030720004540903d10020403400c4040324118800520b114030748030601800180c80240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 343467823 1250 343466573 343466579
    0x406150206040b0a1a010c0c0b040f0314010c050d0213090c0c0b0f0708040b0919060f14250e060a0e0111030a081302030f060405060a11030603030d0e1501030804 71
    0x115540c0050080005a29000e005d1800c03401c001c1000008000a190401d100030040c540354602c049182c008540400e00803500040e03406100d170b6170006680c860003d10b0821145400d440c1d00343c5d40080800c8011840a0004420710a0198083c1014121000b410228260750f90310000807180100b064000040a81d8060002e111440c100281c0020040c0c01c1c40d1403901c0c00309002094100c1c0074200824100101d0081050b50b0380c100500e088485001c03501c0c0d10058400d140050041030070342c2d22400d942e404c2c0880000b40301d00c080c90503071240b00d007008161222210380d04a00b121448000a00f000d0123450000d0648a4503104041c05805001c1d441d100004180800050444601501d5030340b5154010002442a140d201101c20741003405d005070206041285c0c40024204070214034994094444d403001c100612900040640c0200b2060b0010441c081d5860541c00880c0700454510f41c250740100800c000fa04001d81c002405480540260f80d1106013803150203088400a9100380c440210204041c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 343469073 1250 343467823 343467833
    0x110d0c050c01140402150c0a0b1303110105270115030818030d050412210324240e060304050a060f02030f1b0c0d030e010b09071409040615020604 64
    0x100c440c8600d507443c560143d14160340010314800b074405004080b40c1d030104000d00e401c0c03010459004810380c8220064040c1c82e02c4802c0d125084541710041c1c00051322114100c0d1003600c10b111b070780d00941013450304940340c81c03c1d440081c2e031455200c19200304079941c41610300f03041c0340c00b0000c1c00082e610820016a84004603040c1c040022102016984203070414036006100c544c101003110200c0300349194030b04080300b1074200102c0c80600540502c1e000c0551714005900d0584c035a00c8110b040e0701070362610075004100d440b8080000316a0044003481c2e00043e144800505255241c2400c540080c6488101d955401e400300360f803608150750844460380440d019030700300030f4035005100780c0307208640b030031400c40c6000d0484030310540e405040105284005200c600f4521384c0c07001101c543e0300c5010110764203c050004010000d10402107450041c0d4608640c0c405c9a18042c04240c1c0210300b2582c0e00300c04880b012035501fa00d688091445580540c0c0d5600001d19460704206c4080c5c8803070241c015240a03e454140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 343470323 1250 343469073 343469081
    0x50d0606170609010f120c230103151203110f0111070506151003020a18080f1903020303010b210c0406030e0105070203030c070510060e0601140405010503010504110d0c050c01 77
    0x2490380b02e0443c40c0010b120008405000c44200e42e10002001281001810855510000b5401284400c00d15100310310351340440302003100c0c5818080e601009400182c241e000c030f8190781c1d8014401806550503145011a08c03c0001880e90301444098851f40c4180031451401c441c40c0403400f4805590102e0904244002840803a5024030340075a00e28950070407400054045071540c5100080c5540803032002c461600c81c0b19105060091a403990b1f071501d40310694550343d00d0780c4100742507062150302c4030011001d044002c4003628540c160029401c50342030241a0380c10b80c0001000c05941c180e91000d0340789441040e60349a0042c07111211181d6943d040100081c15541c1400ea111f605038100350a000810780d00004880d403140d15404000d031202901d1401e6410110700e84401c030452400c116002c2210300c44d2200950003040700362110342408009641e940c10030300071032068130f01040f01400104030301d0400d07821510f840392290300d82038074001c10300d030701c2204490f0b051903100006400840e1a14040200344a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 343471573 1250 343470323 343470331
    0x32f0a0f150305062b0c08010e0c04090803040f080c0102030c0a0801080307200a050303030a020a0f09120b07030e01050708151815060712020c0102071d040210050d060617 75
    0x2d01449207181400c0031480720b4029030003180c501c40b1a007800035401c80515040701c1c50349a00c10345c4900302645e640c1d000c5020b082c2d04d14010f4010300072000e80014a16182c07203520065540720000f18219600c8c5d403642e11845100c120203440050702041200e410030300a10043d48107503840ca42c001d03222000d0300001450300005030800b00c41584100048404510070902c2005454071000c500401c0080c4040460300345a207552055816110110901442d0305064000e440402c4035581c40304043c140040e0210344000c801d100c4c2c0c03040c0c100301060b800d001c04e9000140301d6000e900d40c00c0103e214915164000d08407881140c03224001210340d400e20040c0510811100031448007100c40c0d0b00c003005042400030000c40f010f4440c007446081e500303810080380c68100650344803e8100684003904401000e0103501c541d501303032841c3d005001d00240031480b600740d6221410100c40d110740c00485980d580d400d011422000c1002e580510809001d040901c4216018080140000b951841c10044c0c401e50040007418010b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 343472823 1250 343471573 343471577
    0x152d120212010b03150d0b041b3203010e070911030105060301120303181208090601060e0d05010603021206011d0c040302040c17190e0f03091314180d0207032f0a0f15 73
    0x5a04000c41a441108841c0380f4400c00318030550082b20441d80c0650390001c0038880d070903500341030f5407600e888030102d17000045441041c0c0c244545403413054002900c1c4024002c041d0702074014030043c4045007141c1c0c20b40707489a120b41800a030301251205103141e4180e484404491650403410607110740ba078040d600e6500458942d008024550600202428110208024a0194991075841c03c00d00409400280c02590013a20744000d401c61005e00c90303103401d4240244803421640d4003034484c411600703000c9036200d600c42e45091801c00c1e0855003004080c11808404000300282130800211001240c00c0030f0b4042c10504143e180c68540888200090300d4503084001c2103504400042241c0d03c102200302c481c1c0480480d0f4500d00e01c500b04030354100808421159103910703260002008a030256003200c0c0040c1010707c0044a100040841c1c04a03951103807400003c2006511401580ba40114580030200c01c000c84040481c0070008403003c41c0d28075100f540850000d0020038402c20407106a201c10140c000d04038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 343474073 1250 343472823 343472873
    0x50a020a061a0f04270f0b0405070e130b010501032c010501170a0506040201080c040f060c022e081504090503030a180c152d120212010b03150d0b04 65
    0x208400320144a030b11881d0050b0402d05d0708800c1084820341c4101521540000003001c40e04142c140150760f03000600414110440b10f00110700e07542d220568861a9951011445500740e003071a00440140c20740f044d43d4a4919800c0207002c044440c1c1c4c41c0340c0f4080002e8507000042641c584411710b421201c3d41c4402075802c3c0c0100d00f4aa0101740c01040f02544030740c080c24145141d031070380b141603040740c801c2d03a0180025402140000c100d06034820610440d040c004c40709560064110003204c592000c1501c1380c0c0c001e0480099101d01480d0080140b130b6405402c030160030341d07500c015801103010385400c0c4808407010741000040060341c0c8160f01c2402e11402d40d144140402041c0d6980e14208001e10740140001c8204060354406950310841c50002c00ea4600151114031070721000c5c143e42c4444a040070080032902c2c915840c14005080c0c0709036020544191581100c40c2d183c1407403240207070b00107004c451580f0b03044101e204240d1103c900020125100303030500d105901c0c060524414602d010f001034030011541d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 343475323 1250 343474073 343474091
    0x216120221040e1e01080714060307020d0c080f07030201060302041406030607050309190b060a09050910020c030c1213060c03080c09010c020a170106080c010906050a020a061a0f04 79
    0x1c5030140c5090712481c004588058484c0030404d1380c1d03103c10800440c011256074002284604d0041800e0b01150825410a101c00c048401001203a0008480310b0005900401011000310f208008400015019503545440c042c039903004001107610910080d0b0140c0c1d12aa010030071400c20740b081c0c09125610b002d003042c00f410000006a200e210252a00040000100200e44211400c0c401c4580c900c00c4199644084d2003580b6180058020403140c00707100c2c1400f50b4001442c98598007440340700d01c0d010b0014014011025100b03400a40115210030520b200c14803d5201c185400c004200345280480300182d220b078603403842e00448041541184081100c05108080040c1d00032840b19085250000f07850f07220b00421004031a81424100065482000b2590010304e01c542e10302c00c2070690038a01e009000c0c60741c030385a4480c0d85940d400069030024101c4c0400b0080b00c0c0c41903014020010036481900c101c01810740f070701c40945a84010000c680084240824a24a00740040030402007064400f4030100f82 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 343476573 1250 343475323 343475383
    0xb12070b0301030b150a06080a0c0e090c07030507080309030309070801060806071209020312090102101a010c030210020f0904061e03120e130515061303110402161202 73
    0x603c40200310080030000701c0c40d07a0031091954003810350064055401e0341ea80340700c01024503000b1f0b41ca01991380d2804030b50810b814820740c0c00551440000c1c05011554885002001d02a40700101c20313070400c0750034094000020301e6000110f00507941c5030010b40e00ea04046850034144061030307210100030303031514900b040120404140554002c45030f08218140d115103501d8a13016055060b0001d60501604261154a003e03650107040036041c04e900b00c42c072440c0005605001c1b07590402c501c0c0180c1e07002c8180d0224039031149041c503506a200e441544c5040c4054213060341607801860000d0441032000c501c040d0031781854801e6000400001d144403884c180345040c03030489081a8000a0842c0c509180c440580c00c0c09251599021600a08402d004e003440b4401c802c0100000e550340c6428040000600c40c4501e001026902900c3e0310a404148151556403104007480c09030001c0d54125400f80007040049a103406c11401480c01050348020321203a051000741800d06000901d90525284030003220544 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 343477823 1250 343476573 343476577
    0xb070b0601052506060314030703020c0409020d0b0405210313060902040222030203010e070b0a03050a1805010c0e03060709091505091305070501031a0405040f0b0a0b12070b 76
    0x60030a0800b99640c03003126010124020800340d0011402d00100581410080113900007012a40505c40220100c00000c05c1036803613115200015006a00215245076a8034069004000c00e0344014107920320942c081c0d4419403503c000b181c040d02c0c02c0d004030710b89203026117a4180c5e00196031250f00c520b46c40d61818883e262182c000440d406055595900030381d5045448640c100c0d00765114120b0314044003044200944428291800124040c0d42004401e0b15004000140701d42580c1104000c14186000c40c2400c0300246030080c140c2c0d19041d155800e41d040c0329141c208040040340560300100301220a03850141007140c81c600346134000c1c1d10150800141c19401882d0f401a10341c2800c000c107a80070542a4902c4a03000354011f154491811018841e588111490b21007070240b04105585005903248015811a80c1d07203c00d038a909000c0000044040c0707410307400729500c144501c1d80d05181800945600840d860121120f071012039440d490158a441e0122000c4000c46c01c0340000d0681c58245508000c0d24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 343479073 1250 343477823 343477831
    0x20309010807211a1e0307030b093a11030a050c010e0304150f020a0209060405040609150b040614100f110d08060901121208072001150b070b 62
    0x320201c08880402000c449a2440402204003800a1050300c141c1001e2006050011445a211007180417a00c46161001c841e40d000014090801245503407180a00c4d03040c000c3c0100c000d40101c0c40a50444c4800c551428420b1001c1404140c58003c80c400303c0d620004002405414440c1510aa03001410008100c0c0d200e13101501d4480d4076009003444a50250100c80e0408807140004600410051a5040c0641c01042113644105a40d006441d040e40c88822254003e500200140e000405504080d04a41d4001d4410b43c2c0c00501c401164a450380c0090030346804000c169110401c0c0c4a043c64140610b0024200d01c4441c0c20503140a00005400c1000b505820f40c10302590050405a0902849010300b6020642d0160307900000b203c60020300310304045410758030070380907a400406c101c05d8680d2108445036103e014500841c80640040e00c60300001402d107401c10048050b09984040c96035110407807110b0150001c68062905004d010700d107003e41c0c0003035140c182c0070301c54000030400c0e0034041c03900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 343480323 1250 343479073 343479077
    0x60a14040b06040c02010608120d0c0813080a0941090415061203030c09090203151e0402040311030f010b060a0f02030403240c0f0c020f0f1c12020309010807 69
    0x34803814010203901400490340109214001c0c09d10030400314040710000d00b00522154820007201c03e40c81000d90b080c1c1e0f000c0d2401b01801c25100649400a94041700410b004119400d00b6522640c0c1c8007030300004a1500b242c42e2400d200404051900480c0c045030888801c0b41089140c0100740595004c00c0c00001c0c000c0c0040c0c4120f0b81c0007003100751410158011005403a030540383d8240b035106414054044c1066140c110002441d442c0005101c003060700c01d480c040c0007001903000c1031415030010003016900170040310806000b1200310785802d58507440140b0085106401d003240e1301031900b04040c2090310001441d45c003a410040782d006640d844c01d00f1a400b007506418000c186e040c104e60201e14601554000800369a843c9040c2c10380c0200600f40d652031801191820b00c00c80302e82950440d2010707001d40b800700204050a00050040c50000502c0603111401f50400100281c007400098030039180301120709070f1040f4004210300380403200000c0e46146c0100d000451501c08501c0008010200051103002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 343481573 1250 343480323 343480331
    0x9011b0204020d090503031807060503070f0201060906120b0606040b040b130801140a051510050d18030302070c06090b070b09011d010b1026061201050108060a14040b0604 75
    0x421581c0300c1d8143d40b48030320060000c02c5004003526041396654000d0303880d00c0034114042d00300910580c000039010700303036403245d9240c0f410340d25a00003e84040c40c1511001040d075480e03d84c045407450840c818074000701041e00140300500a207040c0002400d0015040f540030300300030031003441240402c004071000c481d40c141a06580300600079600516101c1034000c45465402e01c0d00c0502c0c0e10710444501d60050311815403c11075078503801c42040994101c3c15070a900b01404203107100446004202420000f0558080454640000b038060300002a000f0408c0303011070b5000c61032400f03100e0142c0469001d400c00b41037100440303060000e403564134094a04000d2603083c11000141c076080084d00150100a0502c140300600355a4858190280c0a201d61003801800c03000e103a010310521a07010f00c3c82c0c4038086005078298004013400c041d11440c000786002e800000d5100700c3e40b00e0440900c40e590007020320130098511420300140a5040d1050a000c0301d01b59800d00080c48041910203904a40009080300c0c001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 343482823 1250 343481573 343481627
    0x10507020112020313300806042003010f0527070c2003010f0b01120902010207240912120804030e042d0c0c0f32010b03030901 56
    0x71401081c074031880740d1890000c0203002c1241c546207500703001a84070712540e1124404c00c6c03a260302180f4000070b06c0d081c80072610b2251500540a140c049400c03417406000480e20045c580c003000d0034070582e0000f508410400000410101011880751005400c089a1700c440319032a080320381c040c843c3d401c402007043d19140d0002c01c003201d01030124800c1e0503038090940b2031132180b0802a1030750316104188440c080d5003401180c0380c42c50080c1c40b80030a500c80507150b0b902c0c0741000080c040000c6c2611f06040f4150320502c200410402011003e03e015400c51090b05071451030011402440500c665000f02103100a00c0c00400c00035076070f03070007102500701c1d20f00c1c1001e415500d60500700c0d00c0b515600c2105401a143c5256201b5080b81a01d0000055a0002e000300401e00280c403408102c840d400341c1040041d40c0342c904100040d00303502086c507029018064100c01284103000e0f018000c0d000b00c4010700940c0c400781600312040d00030b00801ca44010120050b60a140394a40060042006071100e080b84001c511098 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 343484073 1250 343482823 343482827
    0x603150c0504090606170105010e130203040f171306020304030c0b0306010c1e060501051519050705010203010e0414011103070315030b100f121a0705070b0906060a0f050f0105070201 80
    0x42c070000c12560070b081c4003040d82d03120003405a04110044a01e200540800494117501844003400c00e80d80c00307403000c0b0041c2c2201e0040e41c003d41015004484801c0c4401c620700125039440015841c12500404982d92819004a00c5900385810740c001003d40d0824032080010419030365600c0d08461206810b203549a685800480d40840d000700c00501c40c80da000d02010700b840842904090952203090100041d0341c848080201c000342640b10990920030030040165004c10f036111007081e8010740e081a900f81403003581c0361801c0e60001d070044020b94007414100418031203100292038500d102d500003040164518074580ca128880105204185031f100c4690034014850624003a0041d0f40100325020241424610403540342442c1c407030f640d0031881700240401d040751900b10152642d0350185c507090041d650010041090030004120170280481030002501103080500103d00c50440b400203400549812800c01c20003400c990010001504203003014045c0e51036500c072a103501c10007401c01d42e46901241c401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 343485323 1250 343484073 343484077
    0x30b0102100f1d01051501020a021509010c0b1509011203121a0a0905010f0501020d020304050f0d02130b03010c0509010e0d0f0c09020702010e06070b040605090102041508090706030603150c05 84
    0x1280303103000004088000d0f0808190300a41c01001141c810041055541c00126610305002c10b020b03500c10108011030301d1a14100e0000c20158506050854400e001c0c3e0f03e4102c0202800c691005d283c50190120112905d00303440d1180c05450898401c3c00102c1c01c545000300000310a0b80346c0c180080c0d44401401e1908104102800129402003050b104c0c80d44030680301020389000e10500c40c8045294102190a6002040007900328140f58000c6081078504410043d000a4030210b080e000158043d13510003584404800d4020304513400030114610324107001f0300d0308460110000401b041014400d09040b6030f8020200301d40d01c1c508660f00d424101007400c3c56884480c420400034001c2c0d4a019002401e17851a401400032603000f600d030500c405115109000e80c81c465010020640500c0c0340000300000c245d9800546c005d0405000141869211200d03403418100c0214a000030034140d104020070f03a001000000c000c0d10761031605101c051300c1e680c1d40840111600c1c005010030b6407142d0082026a2107442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 343486573 1250 343485323 343485341
    0x4091a0601140c070f0608060607110a031a070f08060f0108060609061b06010e010b25061104030b090c0d230d0e0909010e030a0e0f0301020301060905030d030b0102100f 74
    0x407501e5550f03640301c0031860b591181413003902e81c031001d000c0d8000303003260003080014810b54000c0c0840340742c40b131541e880760929241c501105a0207160100c020000c5000402c1c00c9800c5c4481178104239040c100111302070101c400e415540c00801c10384408214560311907090751310b5041d0080c202440c10b41c81da00d000886600403442000d41180717011400034406c0f440f2501e9112010b0300d440982d100d03030b600c82d07480b440442424007501843c54001c00580c001c0c0c9201383c050a2001040304401c40c040c1341150348540c02d80303e80c80c108544400010038140180081407403900d81101f44100200855203a90303002c614518203860020349200801c840f41707120748600d1402441071040020030388802c030403e040041c02c13a000a0801e035005600e5800000c44c15403051041c0e5004003407800003507050154440d800c03120341040e0b1580680020700821040030350349003400598040e005645880105906060a0604e04251180d00ba4101400c0401400190f6004195080340d204d03807450100720b00300300554503005045008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 343487823 1250 343486573 343486607
    0x309060f0d150303110a0507050904020310092604050a0608070c0804030c06110f1c0c080309010903170705030103060203060f0306090c0a0510172502030403060b04091a0601 76
    0x5581c240b82c2103000c40c450003501e1007600d0b00709521202c05101540c1c2e00c06900020100e9000303250a000c5807800524056016100a089440000d44141c07030200381c038a10b48046a50820a01c1141e2245076103e00140c840100b21040c81d04261500340014036441591241209000d11040031582003480b40150320f803544c0d008010640c3d660380c0c91070001000485032092800090f11b034480140360003804181c00480030000c3d0000c0c09078800070a803103c0c3c44205d0b603440700309101401d0071180c002095140030b0b501c142458000010f000e034441c100500300100c102042407081c5e0850040051540d000403d0364190382d04003600680300d66652020440800c40c80805540c1407080400b045003141c400071302c0c01180031013624000640c3d0f0b5901d00b8003e02c884102000d101184040040e00d00c2c4008074084d0b00d07481100444194002d14002d000c141e040343c4080c1804c1d005800001e001d105100050250219070001035070100002d08064840925014161002c41190111030000ca03182c0ea2140440740c4c0415409 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 343489073 1250 343487823 343487831
    0x11403010b091c030c110418140f07031a011d0f06040207023712150213030b04140d0c020103090c030b0a020c01150506091903120518040c020309060f0d 67
    0xf07801c001c0c2044410200441d40d03030617200e1140140317062601540c0b41e0081d2805284580503860703a00c3c10204a200c06190fa17051040031002c2c18150170402c8113400a501802c45410003a101c81c0c0411441c0c101600802503540b08108500207a03504220034960000034200d0311092601c4150000c2c0180c418044003960180c009250544440401340c00300070803012035541c0d0b0401c00400030003050140a288103440004002160010101c0e241180d00448904a24401031a10b20000b515000301c5055400a5501110344c404010030080a84c03010b04041252000520061a02400080289440540080c1010b4480703081c002042503d0f44000e0145601003000c803890318056070700320000e410400e00181290b00700001c20102031a0080050103684000c1e0942e443d10300100c00740450498403c1d00d10710b03100c05200000000c10300045243c0c802e18203a680b076956800d5185440380c2e490031a0304015102e40c1c50041590b50054000046810ba0901600d8064442e07400c1d141e09051800398079141d44585082c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 343490323 1250 343489073 343489129
    0x7020f0d08070c0b250506062214061003020304020d080a11010501080d0311070203061f1503140a150603150906030c09061a0304080313050307060605010905011403010b09 75
    0x40c3c00902490300390002d07483c92103d04404c0040802e080317824040c0c02c03500a10041252070a01308588010603400f003040001101c0d41c2c5150350701301c41d81000c1c0011a07619540c284412880d041c0d0142c51400d000d0b2805505509281c2c001030305400005c00c0c02084d8910006198903200c1c010b50b103803042008034000800c8a0740c5c0d95044a9110303010306051a001916100050307000035124000d84034503a07000760003443c1560311007030881000303003038902058030b02034000c00d00150b600914145e1500001c0641d8021a03135442001e40c040c121440500203010590405a000940300c1103461840c007180c0c9140760100f039a510000760307074040d840c983d0021f00604d800c100c80030040c01884405001124410001040810b960b180340c0002546441d200c059640c200700042070108a0070b0f00a150822880583c1e1880c035420b658440b445c65004d0201102c040e030b1600001c12a039030700429a0700080c882030030711030483d9000c04103541071440140500d0b952540003156040e09500d0b601c035000102c501800e070701900d8581c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 343491573 1250 343490323 343490339
    0x20904030305090610030302071e081605010e04060e070f030612080705070609080d110102041221020111120414030f13050a03200414010b07050c030307020f0d08070c 73
    0x38007183c2507032491180e100030075000340f08030004008481d019405041501d00305103c0c0300840c5520140444110152040414500814086596040031041d544040145050005098404440545881545010301c20030065491004265001506251031081e10000090960003008280c000604500c0d004203028100003683c0c00401c0c016000c1c0c000c0703590b41e9984007422a00840c40c0d001d10442c64202c1584c14550038000c0c1800310b00841c041c0c1c000360034180c46810a0b540d10300f01032819500000b10700b0f0b03400f00703200d82d074515040d00300781304e200034081c034002e2603001002403040c000341300e00441020001405118a070360400c40401c0c004016265a07030440c000301d0f42c458101c1201007500141c4c0300790000326844c0c0318100504590380140442035042302c0100e80905c0c010008080e90b042a15420000007581c800c98071706001e4521101803503240e0200d401c1151403da42548a01e00030761003002100007603980d03202c00590704802101e100c2c0100c41e081c03400c05024000d00900a0891a40c5a40420b0712a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 343492823 1250 343491573 343491581
    0xc020a030c060c0b160212070503070516170f0c0f040b0310050610170103080708160309061706130506130e07030303051e0406020f1611010f11060705030604090209040303 75
    0x2c2c002d1340800d040d51501052085d42020000589015030b1051a500c01c01c2c003840310280c030704c69004906a80c200869a11581d0401003020a1001001000c03082800403100312048901240645030080085c98101c0300034603a00d0304d14030945440b0308a001d140322090359894000c618118400b9040d0780c0111101d2010b000070b080f068420a1182c01d00030204515944611050b0b21284040e5613207054603481c68903650382590105205445240d020031400400707081c1048045c110074841e035a0307a0206031818800910442140c404c20780054028000d00c81076980d4010154500320450100141c15100c0c1000234000c0448100c055084e2810041592a11000812002e044138041d032011f002a55a0103d082185031078070303140c06c0e500300e4080c010070082425640600030240d00c2c010150320b8101014402403501218141c201d81005170212610120759100701e0320800020142400701e0100c580e0382040c0c1d11048010105801c100d030100000d007844d1303155005007110035000b80c4a0403842c1040d0070014064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 343494073 1250 343492823 343492847
    0x20409180204114f051207081c090f1d0a05060102060a0c090b04080f0f06090319030204090207061a010e030c010c0206040e1f240c020a030c06 63
    0x3980b41c030344401c1005034608121031440aa0441190440c000214640c1030f07181000d000190854013000d0040d040966001c1e0369000107001090004400d207000100168030001200c3c2c418540c00940e010072203030740005030001d00786941c03500580450308075030802ca0360642164401146003800d4240080c400d01c0101800e034820900d18440d95407030351412203940c10f407403080c0c4000b80181e03c03600001c2c0303014586038001201101d4510f00b94480d41e80c3c2d203080b4469504683c05c40600d0343c101415580c02100700300300f4032003a4420500580503030f1600c10601a00d0340540c1c40321100c41c0031400c0d42d140800e80700707078110b0340548040030b0b0841d16a0b0240c03c060000300303565281142139120300701c6962754540c000e42e41101c19000041c0102406110b18004640400c1e50020890f0002801c1c000401e08002120105c0d00c1a2983c202e0035903103241003540c04d0504840d59001205806080c040c4520400b0f01e14903440c40310940303050202c034160310341c030200e009010a90300217042d09203004804100305500906607059 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 343495323 1250 343494073 343494079
    0x12160614071205010b040902090a0504110c010b0d0503090108190204150e01020105010515250602090306010e040c090e0f010c020304050a0614070f05160324020a08190204091802 78
    0x60b1400150034101195001e000b4644540001e000c00c1005030115001040b103604041e00c513141c1705560b680418241c2e4928030b4040070f08a80403a540321031039070902c5982043e620031107040c40144501d40310302e42c99200d0b090700c1a04008040c00010035094803503001110550030302908554540e40c60580f0460450b0011980740020304002c3c0100c2158814058103060310303401004071518a0078209580300c50b500c10145621003491a142a07034182c405903100008242c02254003590f200115010107041c468160444500074038140b0034800403c10b08490041540d03680b50000a4040030003500030700e800c00c803001c8451158202001d9402c3c060380440503200b10b0710240c4e545142c15442c2c41041d5181100c0a114158481041c084203005c2418604c40110250140c800c0c0c80c0c4000580000c80c04c03100c940d0300140ca903c114161004d241c3ca042c46205400d20030020350440c02c0c00c1680c04028542c0d80003600242601d000c18050444c4907401da1f04031001080001c00401c0441c014121600e02050010700982c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 343496573 1250 343495323 343495337
    0xa140a0308090d0f0f0e0d06140702030a020606040903090e240303040815060613080d0207051017220c090509070b070b072604060b10021216061407 65
    0x2070070003d01d5802070b01c004c3d01c46800071007411008a905012a07151102007100b6059a6080b54072003003180c22030107000b4038021443c884246c8084108031006020001154810060040281c0d4041852500f12200711004240c038010340c00d040781c80180940081c00445100010b00450003a030f40300d80040000d100d0324607901e101c48a4105070b1640980d111b01b0b006500084000e40a131441400c402d644000010100d03400c05042c0852079400b4404d50300150035039400280905a850780400400c0002c01c1c0c11280c2c00504500d001c4018035003c0000e1030303407131751024210105a41e100301210460b81304801e5003040110141178104982041070034400c0c41c940900d0301c2c0101e10000c01c0800e9500a0b100c0654000c2d00d0300c0110303a1a4244950020300020800184803415010541418113a41c01e4000a207070254160909092200c1181d50000f00c1c14840c0031680307610f8105d19000704800341d41691540d00c1e19111103000062500e44a20311000a0841c1e1402060704c01d4045500d85403800381c034140da00c01d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 343497823 1250 343496573 343496581
    0x901050406080c0d1406040c080c031f09060e030c0a02090903040302010c14010b0a09022203050607030906021b06070908010504080d09060f0903051e09060304030309050a140a0308 79
    0x710341a034080c240203600040f1880c3c9550800700f00050b2083c0c45006035a140c0681d0b00035081c180041564100c44183d0b07540000c200c030003002c00000300000c030101d015081e40e10489a09181b03281c2c1540340a07001c01c0d110b00342c110920030aa4012070350702103035000b540d0780d851508a800781c40b010340000481c42001131402007505104008140c606481d4182c4898010700d1107501d402c1d41c00b132407110700742c0300317030b41d21b40030503080503290001100000e0802010140e1035103585100500e105003102c0414400b01c1c3c0d090810000309100050030354000c40c00d4140001e440142c0d0510700b01074841c005414030a1107c3e40d0710341000c1c4100040c580d11440496079201545a1210703481800d0311010345001c0d18410044c041000c24480305c0c0e00103034409214000000e08000c504118400742c1c2c0103807005802058010402c0000302e210075481c41d40d4031034184030301890009070307400040d013030b010280c0054100340d5903c40c8030080150400c00641c520780c0000c000728001445034009980e075a01640d0817030014400d90045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 343499073 1250 343497823 343497829
    0x160b0a14090309040e07080708010c03240b1309050f04020f01110606042a0801080601060e01090308180d0507140607020f09060103110a050c19020102060403050c0c040f050402090105 80
    0x424001c152020141d46031107801c004201c060328114802e80f506008031a000115030794200042030060410344008030711443c42010140c1202c0c401c0c02039002e03400780c0700d0030341d911040c52141e0081507401001c000d680f14594540d00078140c80c9503801103a0214a05810300215a100448152049100f00d40c074130354904a0b5401150101c2d920240d00380194002e10125402c0e190030340010354211103c000b201543c08162103501170400100307a9020105100e0001842a8502403220b607014101608007081c00850f10380c0001d00b0100d55100c003030440c1c40040380034151304001101c4090030350740081043c0700071105410200c2d1503001c280300782c84142c0e0703114106000d1030822074141d4032002c0c2c000b040f02002da00b68800388000140d0060102c0d04242d0341e1030320b21030000a4140a05074010b040d90760340e900d0b04010b52500c0c0c6009690f0040403250301c82110882e0040c0c0c0d000074103030342c03259041c0740c49516070145050303483c607180c24110b100d580141400444411003150f03034459403146000722800e81943c5d0f031b22024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 343500323 1250 343499073 343499111
    0x20a030f201e070f030f03060503030c030703030e030f0a0f080604090b0f0603010f05071107080303010b041512020313060510030302072d0e010e090c1e06160b0a 71
    0x1c030410080520040242045424003a000e154820680d18030b084081d98981080750b1150000b00c010481c4400c078052041d40c03510603e009030a00307034011803800000c4000f807039980c0103401004041540301e650070780d04a10240203a406140b07a00303107002c0c0c0783c00c100000a40007910031803005c400111a0340004d580c910380350240404043d08800a0380503601d032803503103030180c0400604564041d0340300c400107611264280300d01e6200d00750a903200c5000c6054284a1420004d0301c0e800120940e0013403005000700c0b55030300d08070b40c00ca0720407046070328908200d040300359201420159080d80c028401300030084885c5080030800344180c13148000b00302d1130b030380c694004481503110300021300140d20480c0184200c055849075100c1811031000c0070f03000702e40c071541250441c00c6540c00040346c0b0500000108007400c0f0036050550072001402c0682442803580e00030400c054160101c0400c540c1d4211031010043d04c0c0c07042142c00b1506000c00480d070700c0206042035070400b001554184400c500d13049801078203040c9840b03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 343501573 1250 343500323 343500371
    0x605030912072d14030c070905060a050d03090b030c0d0f02070b01150921060e0604030e0f01092310051318140106020a0c06140a080a0b04020a030f 65
    0x121410340f1900000e0012401c10445890324800c44140c075203404203070101c122043c02c00800c0c0095036120000030041e420a102c0b64021051742d4141011300156031344002060040c7c5005070303102002151242000c03100b00711250b0007894851800030501440a07516030040c00802c14011051226030702c511100f0040348a8000d010f4401014000140302e90206d0004600d41c940303807803a10610031915004031080c160703a50b440c1d0280b112000203001081113441d001d800001c2003c003010780800e140c6a180581600b0350818841d02c2404008403000d9940c0c09142c1e41c1000d041e030780c2500c5940c010307808400405150342a20444c440d2040b80080442c051042003110b412805810b00d50001da80b82c15004082041e03020300400440792101c019286e18843d64403118005c11095004001c031510608003885206000d400643c200074404964010f101d01c11401c690f02140c2901e444915070b0b0710858030400401c0311000550703209000140304415607505400009610080c40340c1040003c0107695003004c2e9643c030394 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 343502823 1250 343501573 343501583
    0x3200f150f071d060f070501060512030403030e0303124803040f1202070927082107090f080106240c0c0b0324090a0903140301060503091207 62
    0x408483c82694020711100051011480480101c1c0c0040c005030849042c181d41c521011604505002c002d00034600204000d52395003c0072400c0850568a80c0700f603000107000c3c0709183d00c00c034405407010003c030b0303403481c02540d0a030a60307007050700d070072000a10f81040191402003259900000305800c4103820031a030140703400e1081e03d0301c2c41300d0301304041c0e0308000c100b90703400c600504201d408100d9102200c4940c610305d41c0a8401c0b64105540f6804480400303602c0007090b5150007104101c040d240c91054200f0b07030420440e90f11808415400c02c9070440d12142034103040840700c01d0080013030300509000241c81000c035100606070b440e028001c0c01c80d8083d100310b41c0c4e038401d180d4030191528051110b060b110205490400c820714800d4844008481c42e5902403180c003a400420041001c070058074174403250400b034212418030b02d542800145000b8020300714480181d0b581c7c1d4202c0402d4042c16005500740111920b29440e5a074624000e0042c3e0011104090f650150140100c4001100821a0700c425840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 343504073 1250 343502823 343502851
    0x130b040e190e1b0d02040c11062401030209061303062003160c17121005010c170c0309090f09011407050f07150504060903030c21020703200f15 63
    0x904681c5181680315034083c0d4006010318604009600d45004034040e0603441d403207225000000000e03040c5007020040214040d10325000003c0b03101814036140042e080402d00e009600c41c4071302070004440b4840c092241e0703050a40d00740000104201034000c0081c4468100110302c4005207d14001410310040f114100a2104c0040d03c0250a028820349244c0c0c0e8010f1001281c524111602030300780b603100d2482121203803914820040304a504469142c00fa040038a072084c41c4500c40d5413039941412088401c1908008042901801c0f02c01c03c206481d81080000c1c0000500d00b4008401c5ca88000309490150f025420f00725210030000a5408a03030080d07000340d80710b07460200503a00d00000c54000c01c0c0100e0f08401034036207040c0342d914a03010755401240900c0c000218090700340f40103000c85142c3c580c014140540b464449100072000080307144c600015800150740c54995203004c070342c05100407204660303030f00b5040303a400c80085001850980ca80c1d00441100c000c1580021400302200045905c01145224 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 343505323 1250 343504073 343504093
    0x402180321030606070609050601090506090106090e0f0a0e0123010e0c03010e10090c020303090f010510060c0c0906030c090f05160f2a03031a0312130b040e190e 71
    0x2141c40200740c0c17140501c5001801813a00d42d2905e042c01c8080c2d000304015600c6400b805000e25005103807900500003800d040c0f8103946805406500e101c0300401441584608500007505003d450700080d0780c0a88050081003c55011310040030301c80120411081c103440c0703034400494a4a255009240078184501ea041c1c10b40e0701c0c0100740e0080382030003022514412803185000600300707100d003d882e461903002c0e009141c613840c000a14a1401c0300c11918054642c1c14001403004100b01031160605903001071400da88c00480350306201c200d0b00f0055101071040d502d007000c004280501402d580041d9a51002c05200440c0b221102c2025240141c0300103000d00032603450058050702800b00154a40c13003a08002c45120b0a514024400d407000041c8200d107504401850300405a0600ca40c49408140708004e280000c1c099002c243e44282118015602400006503641680458a100002805010305603a07495807543d103a000e9600e8255041c40c0e1000001c1d1010319080308034090211039a11580040240c404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 343506573 1250 343505323 343505329
    0x140102061308070b0f060102060a06060905060d0204180219020609060601050702191401021501030804090905071203030603140d0c0623090f0c0306040312020f040504021803210306 79
    0x501c0c61048422034001c10035200040c82d040c41107441110408a01d0f8100d280440001e824407400078a200e840342d2401405220403508100c00c0c0c025200d0035a00303643c50b101882d000100a101e40c1d04500c0281821407030100300c070501d64008010145007208800d890420481c0d05030fa90756003d40b10800c40390003090020340207500c22000f4041c0300c1d0000706035040d08070301411404268041074102c00003102036011030905558040015161620440000e50710380d625507129a80d00340640d024420130580c0303401c0300800340300d420848a0b0261003035010280b10340d034403803401800034641803100b01ca08032228046040c2c0c0034404198400b091704103844940032000aa600c40004004c14941d03030800b0300c02e05511403600c09601e03842d64440e9054400520800019070a00ca18004a20400b80e20aa2014041000007035200d40b4024014034006409601d9082580151405016542241d90402d1000c21030601610004501842c84e440903000d0754201c0b00110201c25000009500f5060140420008210141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 343507823 1250 343506573 343506601
    0x7020c04020a140c01091e0b040f06020c0f07090c030e0a02040c02011e091401060b0a0302030603120c060403091403150c0702060415030b0621070e04050c0d0614010206 74
    0x2003a40c070f4080240000b64400354650b800c000e030314004030380d9121481401c02242d511162502500c00303400c1d840301c0c3c1e801d07920b0820701900180024010f07000c680260301049030540540d00a0b21809054a100000d4015002d03940c5c6010301c1078202d014145610291028028401d88100302072000107401c808031690280409001540341c0a02103668030710944480424013241d101310b448904001081078491401c000e40c1c00e80039000340a841c1d0340350407020032180329810202c0741800c803035080268581d0341e44000642001303000c4401071002c0d44000350030090342c180811114400c0d032083e10303041c071241d4450020314106141000129003582c40b882d01814088004405980d008042285152900d0881d6003c1034164000d50300440c00d004071080d21035102509800341d0303440a44280c40843c240b4001d07007010281d8420401041d0000615480452940c611500c107000c00e2341000f8200740001d0402200864080d840039021040f84c61401c98003140325101da100d00d842600c6c05170300800442d00c2e445406010700b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 343509073 1250 343507823 343507837
    0x30b09010e180f010902042301030209190c030b120d020304050d050118060b030708190609020414070801060e0102060c0406030c0c0c0602030901080612060a02030901020706061e080607020c0402 85
    0x40d0b080303034042400b4000030001e240e484400d420002c02c101400d44180401c1e56100c884184101c1014419140080e500e4505181120303012580c2042a844e4404070380303031580d1205001c50100782031403940c2400030307016044160664000c4d00e2000d01001c88107107140c3c84a5940e002d903001a042000100014502045d05484044c000c3c0c00010710040c004050303034903012200f88200c8500da158190580245030901c02400180303824000b42108170f1408400740000460990002c0c015581e0380041000d54507035500502c0f2420710441011020704040c45e018011602c00d210301d100140713400d52214029440442c406000b2013140031810304290030444250064060788401c00b00f04007030880c207240812101d00c5444c00600280c0c029603034a0201d0341c00140749d80340050280380156101e002c0c000c030580002800c1c40d4451361581005841c0d442e2a044613029106008000d865103003010310105015100045807c0c1440b20702c01450300c00c9035603001c000e441e404202c0c1d6000268008101040480c00e15800030898 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 343510323 1250 343509073 343509091
    0x112030903060515180a05010b030115030c05090603070c0501050919061a191d01030f1101020c0a080303010e070806010c24050c030601020f0705030d050d0237030b09010e 75
    0x1801400d1070115286150041d170f2040c1840c0104240080c180803403040a0140c50205102c615643c1000469401c038900c00811204141e6075864144286104105a40080c03600038113043c1e0300d0400e40781c001d080300c4103804191500e503e40390100e068051b0008000c850682940c04c0c10860090b1526090000d01004a45042a10310b401c005030b042ea803194102e4501c0c4100d4101d00e003059050585140001c40c030010716010320480c0310014008181c038500f580012035409490341d0790055142c00103d0a001482980d0760f040004c042000c58141307400310140d416034000e003842804507518040210b611901c10364405001c107580c41100300100300300b1925150503424286130003055036422031603501165822510080281700100900c1104d690502074140e664030380d000100851800d00c00001e80342c0d0800d102480c2400b0002901d50b0185d40b46d60144c2e403010076412a40b48100204581c403c0aa02904c030a034824110ba04136051a10303402032064620b41e60380074142d485d03a40c1c28804c8140c1091005041c5040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 343511573 1250 343510323 343510351
    0x60e0d030b0a151b0f050622020d060c030b060a02070e060a061b050109080304061a0108040b010902130f030501060305070b0c0601151707020106061209120e060408030301030c060801120309030605 86
    0x1021680c0402411560391040e0000d00c100c1c41e007406901d01423101035809000b040400a00320026035106c1058403046a00400009404012001c0c2900100081801c0680010001c2440303086503030003050110403141c042c0b248102d00e0b51b0340310422200e14071a001700c0c0c0228003240c1d19a0510140b6000507140d40b4407030702c00003c00c0c07015070300e482001341c0007210100c1d801c5450f11080b5504c0c02403143c610a4207282802d1640543c1840d07070310341784450414015400350b107074003060b9204200024102c0c1401000e04921040e805074507410030502801ca0740c00290b40900c0b1b11b2000003080402c200071150700030f000101504d40303a400c080340b0307200750b01131b600c020010880c250000034008088070000074042ca02680001500c0ca00c0c01c0700c0509400800e012460745540741101c102d010901c07440c18030745005c9041c41c0414030010807030000b44043c025a08920420710012001100300800c9641d044182d6080c2c0e1280d08c0907030790300c060078000f0000702040140060412101040022140d03000580c001000d0a0312030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 343512823 1250 343511573 343511627
    0x3090907050a1106040b10050904020d0206030604091707053901050f0c010606030f180f1e0803060a050604080a06050a1b02061602070501140c0703060e0d030b0a15 72
    0x91a1130800e507030030b49280400c0f005102e1801074100c101c4005060641c0c3c81c030390b545030a4000442c0b1001c240c101a005803000400180203503515413020303c00d9607009610844404000c0c041308810780107941f0031122071140d80308607030328214400400e40b40c46240d850031204190b10301203070010040c5040d41c4241800030034804031107007100310009044481c03800800059500d01d413901c010b081d5109013401444d07492500210100c00341041c605009900c0d00b202200c81810f0f0300d0310380044c104400d03403000ca81e12089071405100300440304c2c1c01103004510481e00140d03010344075000c110b524411031044c00b0180d40b0620382d40d800551150032a0754007000c0040000f961400c0c144280368075030030101c1c3c04401600700f14200040d60307602c0700b0011492a01c5100070400641030400103860140c14100b40f5202910200f82d20340080d40030483c1c9000303035511080074000c6450300600942e44030034444000b0042800e0851a011300e00f005040801140c41c00f030341d141200f50400c042660500140c2840200680c0c15094071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 343514073 1250 343512823 343512857
    0x90f080d061206090312060627151101050c0313030e0312040611060f130213020706090303090302100c090603020a020309030715080a230a0207140d020f03090907050a 73
    0x80c80090150f000403a0119840c50024140500092545149440d1002c10b0010320790111075030091440d5070000700d02d0085500f03a5900c1482c0c1310781c440b0001e05104180283d207075a2140403882c0c19556031000b442140c445a031050644d010854402001c0f8080c2c915000c0460710039041c0582d07022018042c3e440141e0103460328411580280c00200202d4100000f080f04075804005655211840c41001029414100000c89820f20289806841981100c8107482c0c0c0b01400e50440c0c20080c1d2140b02000502e0803840d000c2e018107501501034015024220030001c0740001c6010764004032044d69104851517003424400c0d0004d4119642d09030451105100c1c1c041240c41c00c21202000d00b012906a003654060345c5002003c1050050040e014903040160040c002802c07a00314407500d8003007070700040140e502c2e102140300038040c81c080907010300c0360021203958484010490403000100c039400c4d541c40b83d006507a01c0360307644a05400d00750030080890014034182c0c4114050203101080d4500000c1003c900a51 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 343515323 1250 343514073 343514099
    0x40506190e090f1609080a06020a0207090207120e030a0209070f1701090f06170601060f03111605060604020c1509070b040b09010e0f03031b011b110f01090f080d06 72
    0x402507002c11440709000500e2071402c89510010394605c0c00044071410705040b5034a44290351fa0040842d500070a010300914000c0c0200005411050300464440005040040b154040444600d010076400d0142c0c3c0924140030030720808982c1c018240702055100c40900316845e0407c03014483c00c0003100015503e00041c501d0155008181d40c0c807000c02d12000104001044584982c0a402803003440e0048180d500e002061b400d0448606050079182a5072118061f40074011003108146140f038009089a09034403030180007900f460040044528569444040c88120b10a54050712004c0e030052165141006203410b4032540100482d0a440d80103503034102880c50b82c0c000d0b402c01814080b001c1a0050039590040000f1014402242c4810900764140b010944a1140c3c10010741d10402c691407040a1400c01d4100503030f84281c41007800292014110020a03855003d00000700b503020f00104c5000441e8140035030200140c02001c00b095402c000d6541c4200d962140305022449500d40c0c0300042c1003400c2e0a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 343516573 1250 343515323 343515331
    0x1260309060a0507050d050702030a03030c0302190302070b0730140906041205040b0d0902030f0303090c0a0807050306130510140711210a050c0105010b130b040506190e09 75
    0x22444e4403100f15103091401c00c0c4000301c4800810005100100161350b0004030040180e405040004000910704002c4010b40304407070300e004c00307182d0880009078803990642c010300e2654050a180c420b00d889072a400c860301c54230840380d0b07826504104c044a0510081c521000ac0312040c0c05000240200119407002e10a401103d800c102500080e0400003070240340f9525095036200c9207011490182003505c000424042c81c0390486240d0398500305941103450401140020f0700c039000c112901e0749800c5000c245c5c0d0703001c007880310390080141c8800007842c500b000034860142c54005001c0e0440b540c801c0c4505412a503074000a071034500c0345400542c1510107600c110388207103980d1303c1c0d42c520a191540000c0c0c1403195452001081d0341c0448500e8044500704444a60002006441d0700e56414040400f1140da024040c84170605510780000007803d5a0444000c02169440040e400c1d5299941d042e0b44140b40910311605800c80c03002c02582a50310340b1820081c150320314504201d507045001c0008110310307490440e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 343517823 1250 343516573 343516577
    0x6090d0b01180207030207151211030604060918030f090b030412030c020a051506031e070609081c030504151a120d0504090908120903120a0501260309060a 68
    0x3800620420841c40790036010340a55000c1545410340d1540c0c001d5880300c0c80d1090395003500080707003c003903400d219088405081c0c00500050220314081c035480d43c8141c2c0b09940c002d106070300d000400602105a4000c0d2200c0c94129541035001a84a45044d00e00d090711460f10070400150140214038042d500300907502841c003407000b0021301110381070084c04680c0e04680d040d0955000c2240880041c80001341c6881c0943c0d50201a03006440d107101013449c1c40321150390303403286010781e5288140c101c40002e200c400322005c9680303518420343d48104494031010041e034804601c100460140d06403502030f030405a0058071800c900000d00e48560a40c07000c41d4021000250428080c480d40701c07440c54440cae80d0384850388981029080a1500c2d103000ba0907846030f41700d072108151301c0384080c0003486954000c0d62003103206101901041e18111010320b80b00e50180c2d000d0141581c4e82000f2460380b50052103024141c981202c400000d10849294071982c030031054112001502c02004900860f44508001d01b15104250b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 343519073 1250 343517823 343517843
    0x60402210a0c0503040203061b091e0a151b0302120c01020706050c09030705011103190f0305090c060403110f031f0b030a02090c160c0f090c02012906090d 68
    0x50100c80706a912403062031080000510500c005658040341184c0c01c229212480044140c000052040c0e9000f29219198070642c46040204444441080e848403400d00301c0f1044002504c0b506400c84170718038175101400041c00c508442e003842d40c8007683e0410050103401184c014080c081000c1c030851788403180c20161650042114401c000d800e01449800c0303020783c2171203130408840901185c2c0e0391040e0322034541005048a4102c180380418421550340000d140e035545028940418041c051521012056002a02d01800110340c2c0101080c4400030103c010081c0c1e181a143d0f441c0c4552145c41800d000e68840006d00c044140c40c1d8080010345090020406110306000300751090300100c850b0029440d001c3e800a4145100507510316035010341c00900005119241c40c28800942c01c0307081403200c000d0100c203e031040481d10314800c9090b04111403070b0f00c0f000c2c058a0b002400490030384102d040c8485050041e80e040f007103c41c810104086030081e01a2000d400c00c4600e40000d1564482c45030140c8568280e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 343520323 1250 343519073 343519081
    0x30304030f0e0a23030a0308070309060b09010605071b050904020906060c010608071403060c030a020309070308030702011b0c030c0b07050903101d070614160f060e06130b0f06040221 80
    0x315000c0e0002904802521b900704480d1005802074100400728410181d85803103200400c944c2c0c1d0b011030700e440e80181107030103950784035032000d0000d502420041c4d410400310750031055034000c852182010b8031400b610204042c2c80e25401d00405032000303070155a22a500b0b02c018900c0300024032400300140341072001046500d10700b403030064655030a503030140e00a070000020044007800074804c49400466042c40141c0d03d42c0e4031041c0c141030040a4100511400002003030081060381500144040c00056100310758030301908009440c0300308840070050200d0110b94011020602004000e948042941407451603d001c1d013000030300349a8084010f801c01a41c5008000026011058182414010b20004c0030070324100000030b401c00d030349440026000c0c880040d00058107000c0544c06424980e020000c02a100d2407840c0a80c06071200b41b1070b140c1c05108002c00145049801107180c40380540020381105917848104121000c480e000b0440d1b80c01580800c20354072520610f402040c223101c2d000c800d80c80c00c2d040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 343521573 1250 343520323 343520369
    0xb0d0501060302010f050f030c030414060106030501090f02090f09040303180f0c080106060909090c1a03152202180604030503120109090c0b07020a05060c010209040f02030702030304030f0e0a 84
    0xe00c8070281c1c001c0003000c4c0a181107c08540084a0b0040d12800c3c41ea83c60f0f03038480c43c100700030300b0807001d08076064000c80c0000514150142c101c24141c03011144240992590030300c400c0101e0280041c040da0010444c03003400441c0c20250080e42d0401c3c02454045042c10036100313030740860b000c80c001c200d425201403644e13082132200070300381c24004d002c00400074082c451400d4801410945e080c00351300851a84d90801070104618407548800801c0340c011260301840000140505682040311440c4035030514100741420740c50049000310b65240308460080410700c00c4250780303000750807209840d01d510b4072840401e19503545140c09403004511850085545001c10b0b0700d11040e402c011707480354012600305080c82000401e1000404165144250203036194030180c000201700301c034540d03c070580011001130b10000300801074004051010044e07505110004c1804113900c00c0340310403a100382c0140c00030310100d00040d11806c0988071408040c90440d6060744c0701400107281c03200a610012504038151011b0f42814 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 343522823 1250 343521573 343521587
    0x3090902031302010215060f061b010c08160804020616060609050103050f071d060603190e2104210f080d02030703061203090303080711010207050a0506130c0501030c030b0d050106030201 82
    0x40a1b07450702180504100c00070444544d03400c02d41c2071040d0008106910960901c002d01c013071400d5418024081c85110300c9000c1c11444056452542d0110840407045207580543c840d01d00a9a02900d0245402c096001280c4003003a01c403421243c00c1d840d85400144d81609004a50203580034101030701c0352980181d007a0b45041c5241d48003800505644030900131000041421542c8004151080c1c0e95a54805140c4444421302501040c0000d1500303848080c02d0f800090070030038000c0e00003606034602c03405080078a01402188900485072018044040002c400c09401d41c8102e4410340441c160f0a031250741e802402d030880d020b64440351781e001c420003120982c180900002031142142c0100e0070045507c00403e00400f9000103400d2003801804106403e02c901c0860200b030821400840d12442c45241c0f140c1c507000e110105903101d01c210000315207101c541500350840c81d9840312000c0202450600150082c01c071150303d50060590320910f201c11034031818041c1500510420002446c0c500350310015200ea = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 343524073 1250 343522823 343522843
    0xa05030c03030601090e0c0d09080702120d08090f030708090607020d03120612120f020f101a0415060305060409150906050741040305070f0602120a0c030909020313020102 75
    0x4086d4005108000c0c0e08481103d08044003040c01082c03200660500c844c05228002009401c0f0701140c4800045040100d12204042c80316581d283c4c040c3c580d6908142e494400220013240c580003088450000b07101a8003c04514001401042c1840050780000d0f40101041c401503000c61182d019180d0f54860074450304001e006c1ca42a42138540d10300d500c0d02ca049809000b0000240058034521b2003a080c001c00403518640b990404490340b1004154080b0064040b00441800460410407030401a10b800c0c02040321340107240b0340500c0c010740b070200c0803005880007412480c0c1160b80c5240c0040418400101d8210703003424441d004c41d42a4291904004959000704070900b0400181079845c7c0c40c000505071004858036540c100e510348040340440481c001e40d21a0740d003900d0301d070000c0c1c0081046404182d98044500d04100844610b55501e0b080c1d0311603000c403d40781402d100420000ea00980070b610f10f0242d01e40a4504005038549685400f012640281e61040103590384e0b14400c0308641e4100302d11000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 343525179 1106 343524073 343524089
    0x31014030a06020f18040608030a12020903060a0c080901140109020a1214100605040308040605030c090a0303020f01110403120c08070c140f09040b0609090a05030c0303060109 77
    0x2543c4414174650107401d845881c4031207032601d0302c00d9004842c01c2d20051031512091100440341d0645502082d00f400f9030920249105480421501d0b2042643c1400029110421100508004030041203484280c1c10501d0720f400003d940a0f106044400410300075031102480707107090381d00203200e0703865003000c62408004049210824078080c0c09030740030060341d247c0e00e070b1101070031601e80c803a501010b40141c10804c010001103204e00000c5905c0b940309051941080340d118000b80302c1a94980c402e60050b07010492000d49400203100b07544800c031240c26824a000d00c0e590310b040202094074820f400f0b00550301d07046014800c0c80380c00c0b2401c465002c0c1c1000d0045460b0b206a60501c0c1c0114410b81c000e404850000d041410107040e4103004942060840005070f03107100800207400d4004200da122030044c0c841700c500140d0204081d180150340300020b50703100d20f006030004220191a5014001e = true := by decide +kernel

theorem cover : BRFrame.Cov 343345323 343525179 := by
  have h0 := BRFrame.cov_init 343345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 343345323 ≤ n) (h2 : n < 343525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
