-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4945
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:14:20.611028+00:00
-- url     : https://prove2.me/submissions/975ac6b1-e518-4446-9494-c64ead42a939

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 889208633 ≤ n < 889388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 889209883 1250 889208633 889208641
    0x203090a090207022b051501050d02060304020d0512040305010f15051003200315032a0a080d020309030d0f0e040209041506030e0c06040311150d020301090b01090509 73
    0xd900d00d03100c201c0d11410001a40c4207868004a422220130240c03480c0300c41d1512164501c9105483d4441c079045004070107481c2d030294601c4540556000c00e2140039400a0282120001751a00c0340c011500548010100051468160f0716281080a85ca803010130f804800708007042440000c2c0900d10103843d031440c0400c00c01e45000301a51851186000799400303041169491000a8029031028083d901020a0900301250244843f807850b841114031100c000584c40100e4010b08002944a290007400580c8034010000c45044084000c0107544141d80b02c024042c000800c1882884040042c544642c0a185d64030254018146040b1203032801100300300109001c1c0c003010781c0c40f4a11a40151080320050ba94003014800100039000d0401c0040789041032910019001d601980003c4040844a06680040808a0070000700f80698030010b00b9180f03084000000c18902080b0540c010101c5203806401c0070780020018080383c0003608682c05c1c00c1e5841c52659401d6070050360000041c41c2c00c60320364195241c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 889211133 1250 889209883 889209889
    0x70e0a050907030c11060c130b070b061507210306080f1b06071b0503010b060c0c0d0614070905012d111c170a020f040303050c0102040f1410020309 65
    0x20100c0e800c050b0b131503103081401846100b02d0603458031280101c40319801c1c4081640d030650301c81c1040503591181942c0010315070403103105641200c1e400240080c59641e540701402480031701140743c0140d0203001c000000029215614290580c010080079901c85084188050110b030215080365001d0703031241420000c100c03400070341d0010f24a0120784140c034596214000c034400c1d0207100c000400000c82c00b407542c140020342e110b8210403600b0440c003c0c0040760024083c868a031140003600589508207810b90601818901608203200344034440010f640312011001406070304041e02d06800140d0070440400c00c56a100000312004580b00036440320300700c1c118800c01d0150048030b05c08010f101c0030401071b103407402c41400841c40e0b0b1050b01064585e01d504079140104001e0b4803070110030b0002c0c40f61000c01d10014483c801d40c0c2c0d80c04c0e51001080d180c02c2c03c51310151000d40003c05848001c0d0340800001c90f00301c0002c0c01c00c4006002c126240b08840c1e44d40c07000c02c11528050000042190f0090200300030981e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 889212383 1250 889211133 889211149
    0xa060803030a020901170a0905150112110604050406080a120305070e010c1b06090f0b07021005160614060108090109020321120112200906012105070503070e0a05 71
    0x105070b8200c0166254080c000580300c550340d0015040c14064410204000a41e45401c002c00c450700c40e0050b00e9281c042c1c0f20340c03000340b10f0082c021070303001c48a03d0040700001400c0e100d0130392002e0380041c00f0504103640c840c00501511456080710440d900f09600382010441c80d0242410405e0560605101e20b18001c90024400c07880d4800c090b0400070f02c0101e030400e010f140c4200c4000014004d0740e0103031003515080b000d419540d99118181079000586000500c05151806544005074001e10444604404241c1159a500f0100c4491482022030443c0400182c0c1d40c4140c0d814101102c0003000145010800549007010050603802d060b4103103084040165000b0414074100014010707465a15454010a181f44d8040c0e400350320341c03a280000c0081500003880c2c1004801d03a105846d4103107003e205e00700d83d45900309140c2107150082e010b01d000c20342c10340c090669184200c0511274240406c1d03100035540b078240d52041d262400800d0002041c01026a48115000503412040e45c8502c5401d00c0c0c0310101e40c40d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 889213633 1250 889212383 889212391
    0x60d08030606070b0c0c0708120409020f130e060127062003030117121801080c09030313050f06070f060b0d022205070806030a021207120602120a06080303 68
    0x9000000c0041ea042e0b440c1c4058588554028001075034500e0b00d61170403480c6030f00c1001d20010512a0030800103481500003607080c6440c03010091141032038a85100ca901075048ae0005030100c10b000d1121441c1c00410501000082130f08000303041c00c500303282d0000340620600040704518160003010b003031035818801b13502c44210340281ca440c038201c2c0f1245180003d00302040f011462a800300000010b0302408000420241d0380c08001640c02440e40311040c0c000c03c5c070070b0800741130080c2c4814038a80120741c000e2207032682c00070444000910f003180b100300190459000c0c3c031281d44c901c400c45405000d1820009042e5000101c1035458500d8a0015103418903494001840207101a44440c0002d1064460b00710504203203902400d80d454051624100704188803e0405000c10340d40f42000141c80c083c0b26003140390041002a020b041d1201a41e002d1155200280c900300f6814862620300040000c071461210803040e006a0005840710025004403810f04400340c01d142401c0e0801000303010000c0040122508 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 889214883 1250 889213633 889213643
    0x6110307021f180809040b03030304020108130503130801050a0b0415030602092701030302100209010801060806010c050f010204050a05060304050309010507061107061a040c050316031509091a060d 86
    0x312001c0c82c0010009042036082c0e1045000c2c0400b000d03400c000144010f001800700480d024040c1000382018103a50380801c50300a40090841d6000c10711003c11a480d8003080c034014003c0d20315040541c504190780b403800ba40034190503990350003080350350307a494420b95440040c215002d2041f070003a6410744c2925489170101070711407640000c007451944d54a4121142000300b6503078004803940480500d10000409100680250062a02c6100003180610803911403031030507155190300b030b401d10808503004400104010705002c1100c0380040030680c204144c080c905444400581e4482c1028140038401200e40c0c42036009030740a0045c0000510003105880c2454000c2c6400c5881e12601d00304103019100e40d102588022a0010384403050082d00d420803004a0584050000458010400c2c8000c89100d400c00c3d0300050014000700341d040810f42402600d030849482c0208460304c4103007e0140401c6a84e114912030f5907200c406101700400c622142550720301d440d060409a01d00b41000c281185040100101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 889216133 1250 889214883 889214923
    0x30f030213090e06041203110406050f0c010608011a0312191206030606030b0c090108010501030b01020c150a18060c3c0c0504020f0f03042307030611030702 69
    0x10324007140c020a00060041200600401c0b2400800a403030f8581681c040c2c1c0e40f000c2628590349554060b0042e008002c946840480c030301380c5000011201c2e600085641030b4140c1c130800c80e009030303132100f4003494001d012100300003d140010101c81d80f11071908445030760f0113a00070070419410780c00000300b034440c901c0700b082c0503c58031440c1090840c1c643c3c1110078001c111900d8500084140001a8809402d41c4d106108050090310f4a000c02e01c510700a21107000d000401003401807102e54441d401c0f100c0c00c1d26042c01140c003001c07000d000140c021241060f000441c2d5070b020828040d0315a0202030278a2888055414000482c00c110000b40481300f0458003403d07004000c8500840c070052403010b150110110320308002c000f20b0369408000b28082e600400c0d0f8405541d4200481c1d44d261510848508040d06503107d0314100c100f01c02944160030092090760002d44140000c05031f0052140c0114030520020060400a17085180c50402c031041c80801204000041c42008591500010050506603544204030b03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 889217383 1250 889216133 889216147
    0x5030d0816020309090712181110030b06040308190903051e03040e011e08030a0906033c0e06070c060f0b060c161d040f05030408150609070c030f0302 66
    0x29180d48950080796800103e90301c01c2041095210200031f003946d6101358140803030080a02041050402248042d00b180500d188900d0149000da8892002e821641400b00358201044000740e00c40d00700c2d0340f003500c40c0003000400d44044007070005a00540141030500c0c005050842d03d03038541c0c0d9140c40882410340009003c850344041d004006641c0200342c100304940e03a0b0340e102c60303464a040c400c0b09000e5003500d108071004107036a0130120644488150302d9588400e00352400b03030114064807100c1c26400c2d88a44030740304208803004603111704007400c0300a40000030498450420f0b4040720142042c0300b060f900000c061002c5aa4418596125560003180116070071101c1701030b0340000e16260840f980e2215001420b450003141c0814040741d218181c00d02411072070350701c9100c40c031582d0a914648640c1807055002500180b0900b0522099501890489040584896119192500b240800084845848100900c41c680380c1e481e654425498941500048107a550103002c0c920074404003000e01d038002c03443ea = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 889218633 1250 889217383 889217387
    0x2070c0e190f0c020f0f060a0f0b0402040b0319020a0519020f0610061101060806060d08040b22050d030c060506120a080705060c04080706120207140f0705030d0816 72
    0x1440701400d4050030803001c124500a1001440f4111498000d8019000703240c0036460013041c6a200c0f052200060b00040ea110b600000040c0b14207800a02501d03500c008051040d103540c1b01130000f4203217202c461941c1e414803880707513411280314100d007480d858010070407120780c0e031b61000540b114141c41010b203100c0c00a0805050381844113a100c0008180724280801018802c0707080000700303e8002d03440e90020021b10305803c500f038511500850101d60700c1a1701007112820075003001032200c1d001c1c0701d40d00c1c20181c84040c126010f80c42200303407980041405004e00b00c121508000700006040c2215041d44c0d031440340e034003e00b0110136007602810143d5102d0010356251501d1213031807000c00c419001d40c0d414048600e8055121742050034113558501c0b40000240d00c074419801190191041070300202241d6240c018102c581070038180c40081229003d000c0030380000c00b8806425501070340d00024240300128522502d1510086a0005100f81e00c6240ea0320074190304444199000031404040001c442d50854003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 889219883 1250 889218633 889218661
    0x12120403030f0905100206060415120215040e1003060c030219080c0d09030206150307180c030b060a110d03020a05090405180a05070603060e252a021302070c0e 70
    0xc51303034010010402041c80194007003200d0740306d400120341c100220020081b0341d8030590041d0041c04041b0107020134101c05468484c10844a0740015100c1c6450700e81c8500e484160500e0a595a10f64800102001e104102440c0214115001c3c2880d0860a03c200380c203003c0804c441c40c01c01034003400003013004500e008048004403507280d080e6080600104a06107802961041d0458810741d901651581c9050280b50101d03428085407002e0200f540c5210004114100400354103074030800340f640d40ca5540800f5201c00000d8070030182241c840c10319804900100354200501081e070f9400300b40c4100b181c000703500c2c0c100302507c1d0340d1101518001515036803460590320401103400f2201c130522414207460b0400c000001c5201c01d44403980d60078001e10b030355120b44280503641079a04200790444d400c4200825800c80400c15811515880c00340104003c032100240c0c003203d5035601e80c12240c1c81c89a01801d600700240c007000c102940304011403400b265911200620441405001c10522120000c03035011001001c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 889221133 1250 889219883 889219889
    0xd08190203041103190b09070e040305160f0309080d0f20030c010f02070c150c060f1b0201060f05030c210313150806030105060d0605280b12120403030f09 68
    0x4c1225082885800c01a01c0c0d0b051685040b10803030075410004245100108075041110344103001402c05882e10343d801da0701034100c00c0a500f200b0160740204c0d40851610b81c8411140c034082d4a40366003580c1468040c50520304116580d1043c0f101a0042548e125032210202c0f81c0381a0400c0c04506900e0303220001411031007075103050101903080c00d5181102102580c02031103440d12801c0300c400e9090b550b00e407000b0340080582600d000315074415450000b140d610307049400b080b6a82400007a8000544002503070a805c0c0004040c0140c1d90340074240300e40c055200c0c81c000500b1044004140354240c24001500c130301145041894141c07002510a44119020416107600c03824045410030055200c1c50900c01481140568000254000000c0b4016041c10701c942c6000d030f20042e05d0705050150319118007020307210207403100c0f0350310801501070340081041c0011032400088680022898030b98110411442d98240d80c0411034079000b000ca08030040f064041114102e03645802e060003000c034524016510400c0c154 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 889222383 1250 889221133 889221139
    0x411010201090c09051008070608040b060f060d0b01032904090302031603020f0c090723161a0708070f03200c0607031104180908071208090d081902030411 68
    0x10041007401035604194441c0c071b4006110a09039607100c540ca666941c1510410020600700c01c0401d000c100d0300e0b900c481e440000940500c000d4002403000c50580d62050114458595031404658030540c1c0c54080e401350305c03080c1c40300c25200d04075000c40d04124102c003600c110f10465070741040a0825009100ba100024680441c0110180840c14040c4d2140d0320342a0900143c0a010000300492411440c0036000300503aa480c4010a00070202503c8208000d000d101c04c208030500142061801c2110030781240d07840781003048101e405c0c48119184040340a422030081c0b00192040188259203c64009144203482c903000c10000425520301c500d42e860300c01c0e4044020000a204400c0b084001842030040000e0340d410810316080f0701c00c104c0b80d40124000d01100b0315194204811403603888e0050070307917217020740e61141c540012507451951500c0724803070402c041048901041001041401250401c03110303400e0403003079880d0405400d1b108c00c1c0c004047c0c018403a4040042024003600c1028040105005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 889223633 1250 889222383 889222403
    0xf050f0301240e070807081611070f09051303020c190f0b1c0c12020903100e070e0a0905030d1e060b04082a150d0204060503061201090b041101020109 66
    0x41c10b2400703942480c500a03200c0941c411008510042e01c40c140c02849202d5070ba560410325100d00000203459518024000304010003044407810f40d200c2405131100400801d01c011940c2e52414004038251100200b084440d4050462007001080c1c02040200e200b08044a980e81c00c0b041c1d2109450405005800060550410120100d100800072001b014440070219100140c003200020003016940c039680e000d030004000791690040020300c0c0c1c018140160005043d10a2040034034520421901c92218203e202d6210a404004d83c0422080407500051719502c1800b00039090340300d490b503a108255841130b906c1d41d595544003103000c90030034403103c004a010b018021141d031303448002110342003130007020305500074071030030f6080100c8240320781500350580f038068401c0c0f030202e1040001c2150a070800d040002c00820034030011003a14070081c0017604407919826187d00b4998140701080c1044031900300141c2c98a803001020840820072503512a0344501000e5210b41e0700302c0100d015164002004221001e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 889224883 1250 889223633 889223681
    0x9091a04030f1d181b0715140f0c030a02091801090509030702180a061a030f01050a080a1515090b0906060712050309120a050706050903040f050f0301 66
    0x10001d01c1a0082c40c003036031810311224090441030b015580d2164035990104181e5008810714031600c14481e400800d1410720b0046421003110048103501003e01214048503d081250b81d40c1002c0c841c100381c0100006603240a450203028020700958064803840c0700c0c00c0044001040f030304a0760101c43c0103002c0548000764204c1c0b000d624169142c428065800150305160024254580010a464141d0380080c000c0354900080c41c1c20040c6824081c02d1403030101d49490740840d43c12000d07200e1003090b64803000c80640e00d14124104000300c5806801c543e100d40c0300c1303000801640c03400080c900f07080c0f90070a80c103035810f28040300c0341e00040440403c40c01e1030070804580000c03014074039272142602207410f8990906c3ca0b0380e07141c1003204620450030300800f02441400260003d501c150b000d0f5a101400170201c50700d40780103210705080da804c40500f0310300051001600c881040264003c907500102d2040040d810305092601e0031100340000d00031540035021480002450f035400350051200091f4484076840c8441c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 889226133 1250 889224883 889224887
    0x50a170a06020703030509150603031611032a0108251206090c0215040b0f0711030304240b010806040b0a1205010b010f0c1101050d2c1902090109091a0403 68
    0x10080307c40b09928080d2100901c02a401801614170441008000e1480d085c01c07003104d040c05500385007065501c1d00c24550300500340d4500700810091025039a0100a500e1a00034030b2000034180c0c04242d0307042042e0b00040c440100340c01c1c2c00c0a280412204a8500c039070069402c01c85202c1c0d640b1881448403800d00b040015048803d900000207640d0560036510b60f02c0b0481400c0800740c0060724000e0a9490820018525120260949400c10401d1a10308403800d54440d40c1481c5400580b0306a03006654030740041000745000301100c1120f01030040c2403041c1a95200060f0640400800301030140303894003e40c40e425940e8000000241100111a4800780498108540282074080745540841e0600d45002c4003039006a842c10381c2d481d4426040b50036521242d004507550f1700a40c0080303d501c0d80750705480c011202200203d42007401e20320402031560214200d0f81e8030b4034000c3e110302c052047d182d407842000b580b908020103064804110001c20000801d1a0510f80d8100c04039042918400d00c405000c209a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 889227383 1250 889226133 889226141
    0x70807050d3311040308030f0c1b011a011e050a0e03011503021503041212090f050f07060c0c050603062403060a1502060403080406061e051801050a170a0602070303 72
    0x1200d0400100101000c00744030f002144a50f003c05091194117000040d101d0b040404426403258503110b001d410107121142c030540201c41c40b030302000c60f65107801859000342040001d581c0ca403a402d181c03e40c20340681c084110202480d0400003000c0000001e0a211140d009140c0b2102c461000380007000080300007032a0048080c82d6003c1203120700b04403040303006e00703084034020380303000e01d400c6803000e400c01110300c0301901e0582084070740c87d2005840e001010045000c00118001d1907000300c000d407241c4141c0b40500e40c1490700c19001030303051050640411010449910084050303030700554406980e81c6035400014000d00c98004000384218003500400d5841700032101541c0500d10949031480c520380c5803d603105421070b0040540005078032520004021034407400110350094005d01001403259100e44442031005101d10303110f680c00f4855002048541442503955050f4110401075070b00725418280016080b84071031060703055128404001c51500a81401b03622940ba500110031561481545009400b0f4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 889228633 1250 889227383 889227473
    0xb03030a18060302030c040e0403020712060c0e060f04030b041502040b2206050703230a090302121518030d020d0509010b0406030809040f0f0501060c02030f070807050d 74
    0x5407014040014194080e0081d0382c0540301caa00c0b45400c06090100300300d0320f40c40040003a821445084400200d00b082012140c3c5014050200810b2824600d0f0015095030600c9100c180102810400e62800c5e00e006416281a02e51104400e1456100c13410900044000441c440741e06c10301c0001c0014040003010000c001d02028000000324031403050007008120301c103c1c8500c00102d2410070101c000030313100f2071000b48603010707800058501e68401080d903801ca4204496403804280a52400d009600e04251900600d00d0000300910900c1c40d0301a08003c4010080c03c1c19541d002e0302801002414000e00582e40c2154005808640352443d0040074400f0303040968607800507500c4c00c500a40181054020b010070f03a50062030313852a02c01013105100040c41c180240100241c0c0e181110050300d005402040d00030b18841d548d05800f281c0038010941024110714014a07207a01507102081031100200c0c2c11002c55000700d83e405c0304043d503410302c0042800f403100714200c3e030103c001c81d801000e480000020b4403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 889229883 1250 889228633 889228667
    0x106030203120a0504060e190e0a060b03040f0f0201120f0902090112030212090d020a0e0403090b1213111216150e040e3a0305010e04060b03010b03030a 67
    0x110b2500741d461002600c511072541d000100304000500825005074481c44040401400e401100700c40301c120005c0031113560b04003103041120361b4280101800303180202c0c80500b4210000514604113907480000f151500a0000c000070070b41c0b4990300a682c09085060b0189105401c00d00a0004200c0010024114035008230b11070b80200f400410304048000044141b02c0d4142c004000c0c2c1082d04520b110580c0109402c00e5110312000301c1b44005032101d5100d24005c1042550110030b500b40f9140c090a40701c0280c0000950303100510046210a04d210744444d00a1148045050404100e08003411403030f040d01e4a158000c40c04000900411070005030303005d40c808004001c140c42a88500c40400c0c0100c101002600141e0300d62404402894103074881d080303490794002110921040700000e02c13210080b18842004203c1c50702850804102050002b0b1410074162904206560600441c2d0381c03040c00240020f400301ea034944240216840035404600446070003000ca079110000d599005003400600d940e6240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 889231133 1250 889229883 889229893
    0x60e0d15060f0e100e13020409021c060f27061e0e0a151a060903160b030a0e0606100c020a03061d010609060803071202071a180d02010813050309030105090106030203 73
    0x44c40c2c074402c0e05e4482c0507018200e1060544681602004044c011035841642e01c05d400d03c0c04035a0303a6900c403902000841c440d990202315040820100c2c3c04030340c4000e1034003050035800e00401410800400c0c0403040d896000000007200b030442080e010000c505034829a0782145054000c1c143c0e03003400a41c442c401c6106020517140449404101010ba51340d50ba030328401e08103000c110701c0582c64001c016101c424030240c01c0360111140002005c40c09001540000c4d154040003040c06a1a4901c2c00f80303040200d507180041c10345041180100e4a05080d07440400c08112840040e8401c41d81c5603050840103503041001405680319403610180801612940d4802661800310b00090034415805048215510300026500380f001c0741c1c45613501004500c691004600964401140ca01c01903030f4100d0104c11190600c039107031b0701a80206880ca04006072600d219102e008541d00050782d101503015030010f04009000804042e5160444c6103000308031500e507142d420300c0100404954154800c0080724002c50440e6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 889232383 1250 889231133 889231139
    0x2a100c150e03340b0c09060706020a08040309080109031704230106051801030803040b061f0c1202060603120d0b0d0f02090f0c1911100e010501060e0d15060f0e10 71
    0x40101804094004c1500c41500c000a6813410348501a11500a001d8070807850144181d55407401c903401580e001c004510b005007032005240c0d020422401500c0e568008020080054502400a4400c821400c01ca0059400014104003c180e030012120341c2a0307800c04d0903000300c03001d0709000c1c1016004031401055044c018481024110722064101c94100d41c24070b04e5600c90751225521210001c10440d004802c203041b0300d40000050f50042c02d1552a03540d03001801c60f080c6054102810100b52003802c40d4852010700050707030380200342a5074240c0d2110b00385581310b032040d2008010b004103103540d690205180c080d6009011031002d86404c00c0d4030031140031145945440100c001420705840c540f0081c1e03014400141d0a01140c0320944c03945071541003600c9006010100e452800700d19010b007044403034842142140408090080901403c41ea081c81010741c1d45110100d25101410000640301d41c000b8081c0301c401c03100d6a4001400f501481c201302e0301d2243c8840fa6070680100584003542104034000c400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 889233633 1250 889232383 889232467
    0xa0e0f0c0f06070f020a09020403050c040e0d080601020715200307030f080415060b210108030708030c0d09050703290123032a100c150e03 61
    0x8108030050060820034850058410700c40070350080042214440940710241025076100d40006000f04040e560250b9282c2c00c5240c03490600c04400c24840c0528240744c2c001e0607000d0b01103440e4910300790038600603040c2e80d45d5400407840d02200360f21004411a081a14483c02a401302c001801071411046a184080714418803585d280700301800a0002803502050301c520340d02c1881c1450700580a5003840001021408418046400c80da004a10b60f48000607035011402182c2000b060002c00e10200390419854928201e07200d11500200505002c80040000c6501401000340c03948040c08800c20049600d031840d040d9a12086800f054484040e07502c882d50780311275840b02c800030545d2801d11251603646041000e80200d015250744058005800c0d0f4840c4680e00c0030000e2410400d074081d510f4850743c2008000c5652441c00320b840e207000343d0807034025032007007600070314070241b01e65002c040c80c3c0d4946940c91a4900030070520209400501000036001c0302c80c0e4010f4040b44103c2200d03100303070b46400480c02d82 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 889234883 1250 889233633 889233643
    0xa0f0c11070e011410090b0a0c0219030203060a0915090503040f0e0709030201050901050702150910020303011a090a0e010603050406110307090614040f09020703020706170129030a0e0f 81
    0x910360344006115080c0485041080780342030200c117241000110035031100d00c0c850081d040f0907030701000201251800015844c0014695203a0005030404041031070a50700803a4403a800140500185500c8020074130401440b03034212001000d181008210403000c503c1c003243c4981c4a4400c1c2e9100020f089004104002d40f50300c0e85001e0310306a03c69501c0079265500540d03064024110703407814000c0c01d0102c000941c80d15850800440601c403802551480880208030f202c01c0001d42c01011544144010300500d05140d8181c00c04540d00d5415580700c4003407500040d904055500507200d84201c8800000f0307001c0e010b402850282d0310405081c0200031121a8484e1940411240c03480000c5000200300302145c0100c1074030500070a40070300a40350588910280c103002c3d0846d4403259509a00090381401c1c1a418403066011300064504542c0d580350008030074035042e006006802c00301c42801ca0780319144100701d202c14981c02102000d15160f10703040404400401141140c10094056000c00c01454280410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 889236133 1250 889234883 889234889
    0x105031308182706130f050a060501031b020714220212070305130311030408030714010b0d020d060b01051b10060506040b0d050a0e1e0d180302090a0f0c11070e01 71
    0x214083d10fa0740e0000700440c200448408000441c0e503111403901c0f204040c0121482105521800b14916207043c00060446082c001075101410345130300c920446941c0494090111503000100c0c111111200300011600b03460003000d00342d80d10101140016001c6a9005040b1032041c0610443c460f55070360b402070741611800c03900340342c0f8521003010300390001e40a00341900d00420410200c90a09403204101c900e554002030042d540100c002280d81c2402000340151038010a003a41c11841c41c40c01680465044804104010305854544c0390752003c2d41d106400344e0346c2502c012182c082e4a150700110070780d110302400d60043c0c0102c1c00e00300c002c01d580c10070100b180c0031514420041843c000b44880308000a020240ca102141a00d503618031071006010000e0500301400388a03d66030404a03080a54a4024a0710400040c050480403100600c0707458032401c004c171b0741c058807140d040741e4406a8141c01054003000c41c40740d00b850308209140700d50703000b600380c60b141110000b16142c41303440d03000811404070244 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 889237383 1250 889236133 889236199
    0xe030405100302130f0b1c0c0503180a0b0103060218090601080a0213030c3218040303090f060c0f080402060d11044b05010503130818 59
    0xe00c0c409065100750f00600b0100c1418405403a92030301e41c801030b4603142181d4484804150702040d608805800d40d145442c609039441400c02041185102c00b4103240801007050000003051404040700d120140214041c0f10b510040c65401583c413450600002c0d003050141055803a0b02d40031a017a2418501c10141c0120304c140c5641c001e03a03a400710854080e50040c4150321040c0c005a40020020310700c0208540601403c080034004982d01a1405400201040a00c450b1031307229010303902540c175028010b029031101031400308100d546d5030400340d002d0902550300a00900901301c0920902141c3c0d80070810020181d40c3d440c9a000400c082200d604c4019100a517000c5e100300076a00d00d482d415408482d1064420707540b80c2c14503590782003824411088000744404000c0c800c1d60f414140c41c1400c024501420542c403400c0c802900c5042180039603040c1d01030350741804000000b0401191001c524001150b40c00071005545184441e0382680f030008445907180207040070b07242868100c509041f0130300710300148 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 889238633 1250 889237383 889237399
    0x9070e0a0f08071706060307090b030c042313031e050910090306230c0a020c0315010819030503181204080c0f0409050d0305070e121c03061503090512040e0a0e030405 73
    0x40527400040080b20390301a414422541c4540103a110b50046810a03c00c3d08000c030340c0c1c03515010228145a5005000e20500c02001c0b07a418002a042000c0101c3d11901c0c1c1c20780644a05a408144c07580d104040d2510f5000d0154085c40c0350840e485240b80d030a07284541d00921101480c802895600c042c229092140498020002800304031040c000d04004407103403044840c4110304c0c0740420704205409071500040e010b0803005210701103041006405540200082c25114507241d00c000303109000c054650306000d1002c0d01145644c0c1c8042002190b20b82602a03010341d10b40e40c4212082d071340d507001c0c80840d00815a9a29800c1a8602445a4800b580c2c000000c0c00c50040e07020001c030028000144200300b8441070002c4603015880300401141034140c82c200070801d82c1c50103105451b1300050342e0422020182006c0d41402501c0400740f91a81e211407908001c9911070f05440c00303500304110080c030101003820114000550108030007010380182440c0c0c0b010040c6050143c2029164400c9001d15a000600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 889239883 1250 889238633 889238639
    0xa0f15030c0305090d26010e01030c0f05100f0c320a0f02010f03060905270a1e030203090402030405030a120b0f0d0f020d060c0e01080609070e0a0f08071706060307 72
    0x5207000c6e4212240b05040d0310040e1380f015a4044554001b030300440c5185110800510803c00002c0b00e850141c0240000c1b09180c52800c40024182c1d9110450702d82008407007261690300c240111031460001c0e901c840c0131600008441c0301c5290b0341d605005080e9208c04400545200f004000c6403480d58103030801d404c094055550380040d10001500094942056031309c1b80300040d80501c0744a524000c00d4400c00d21a10001d00328078614001410003001e404980040141100095030108504c40780c80c0d58506052640095040c1a4258022442e6482d00316000004120030020040000e280002441d1078200c08400010200c0303088558203000a9048100c1c54004103491505a003003d4040b4801c05110301c82c0300031a0301284411260040448089840c0c00180481c1e40c1c20544003115403c0070f00e0040c0c0c0c2481c2400000e03e540030094401014040c250176402004d4403000386400140000010891029a030390414554544040c0304400e00c1005024452042c03140c04030b5294080c0000400500c09103007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 889241133 1250 889239883 889239887
    0xc0103051b0c150106030b0f030d120f09060e0a021207030c181b031b03020f04210c031103070909050606092701090204200f090a0f15030c0305090d 65
    0x3014042c0314010344a5000d1401121500e82516406001241c2c2d011440000b841c00780141d030070041805034031035040130a010340c0055100d5004400e5003040c1c4804a02d449070200c1c1c0b50001c120041d4050b283d00d0504410380255840003c05802c114070aa58620403040c00484164644599010080c800310419908112201d003034106420505030b05200000d405d200c0800e2820404029501c08011070f4880303162044070a116a9442d02c000d106041c04e5250519824009006104030700996071040080c0c4211945d10041d40c00c05840b00d948a106098500d4132810074400e01d03020700b01c545100c3c0c0720f50b00c408182c2441c28025100269030050040145407209e00810201600c02004803000c0b00406204200c0c4007595520460f000c201c5000001ea00c031100d0040c04251105060f101403848840001000b010134108110740d50040c45000c29030720b0f0b503031920009240809aa01031242280c182d100070a03040c00d1460381c0c0c0c03410095900e01708402181c150b0300b5800d4440c112000c070b2003038012a400a43c114 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 889242383 1250 889241133 889241137
    0x5010207081e01140a0504030e011e0810030209010308070507050f062d0316020c0d03210207020a030b0a0e060f0c0a050d060b0c071706061c060e0f0c0103051b 70
    0x30300804000f0424229031342c0889100070003207030000a61a00c44043c0010b1613040503c3d021400000c4c6407801c2000d030740c0da110050544080301c0b501c0070040100001040003000309142d074040c690040888142c0d503034030300300700c03005400c071580944503400746000024492601c0301c01240075400240066017800e040049050310444070301060010740c00345514452501c48140c0c015441220403a020098814400e0700003803402015031030781805a1840c08060010030380000040d0344080582e44032451441200b01c01c217020340150003000b03400c94000c3d41d021007000504409280300e01c001180400c0924180300030250744100c1176500000c081084808241d0710f25909008090a0740c060400c6840d081d0341321580c50445070564010100f2840c00b1605c0c4040100602002d00100004001952204000e9441a84a401c0580624403450703d400c920301c1c020f0607141030403c2060704038604115549a4882d05521818078401c6010740340240e04420002d98000d10625000310812222a0030a014001060f0150303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 889243633 1250 889242383 889242433
    0xf030b0705090301050703051b04030206041e120b0103110108060f011407021f0f14040b161202060f01210204111b0d030f020c0c130f020a05040503070501020708 71
    0x44401c210010702c0343c50900501d402038510782c1d0002040e141548401c14611140701c3c0708807003403008200400151ba41c4000f9941941c1802035034440c0c015400c401204175085643c40300c0c1c801070349140ba507030500c60f4480d030a90403a0300501d610200e10580c0c8004480c0c0d004100e485540c840c1d01105614910f52055452525422101d03078550b00e022302c1900054040002da2040c000a800c0c0c0304010354466500c41180405020b103410444100342c402401c202850259006490185d03001180c4040e4046548200d0f0a03203682203c041940c035140000001d46585040780d0801c5040181400010220341c4405000004140086c1011001d800382c2d003080301412500741d190900050511050f051246040c05105012080c3d00081405603150207014003911a5400c0c140c071420f02c14802c60101803004150b00402060407104010039100c0e140310b0000030300025030045012840420321004441d0408000c00903520210102c844090f510001245e48407418000c1d03032440e8004106600d01c02110305104402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 889244883 1250 889243633 889243637
    0x402040b0a0c0c0f03110f0d02030303040605061302040602030a1806170a020721020c01020105040b0c030901061e141f110c0d1a0901140c0c1608010e0706090f030b07 73
    0x3c0aa0b1040903d10b1a56550402d48944401400c008120700d402d0340e0310000604141c406c400c0400c01c940010342c41e40401003000e401c0f80c0c2c0b01c80001d50b0703650f80c0504001d1000240441103440d1910f0b800000c0d81d030b4200f0781800340810358911360b1017800004040d10070300700d6038650b40d406296801203a808045000203005003000c25000d20200300050022004d102da01c0d41c3d006c01018040c0a5104000d103080105080c10f41964500070a200c042404082c100c0d501004844515550b91900086940107041d0359100c1d12a2800d05c0d007524035102c1140701c2c2041110300310044407840490000421403480258281d10043c01d41681c1c03c0d0a8081c0140001803003006808103550b039078030341e40d004109912081042115070310350410140043e564150303080c9400c00c4082c4020000c40502030002821043c0160890300d034002c0c0800c14010b17a110410010030301d100b414000004045e591821680a05001c0710601e403103000d0540080b03041031042c52444101c6803445e22650a840c555150146c20610203030094003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 889246133 1250 889244883 889244903
    0x14162325170a0b100b03150f03070303110c1203040e0717040b180d020a0308090102130e060901060512060402160f0311190305070204020309010603050f15060402040b0a0c 75
    0x1008071480712140328010408014240b0300d01c2c1440d0180e124180201440c00040c2e400301c0c00d0011000b043c00340c5e0741c064215801815502494400211042d899035001036144c8180030000c02010f030300c00a449590a4120129092404030904100000c0c0b040026804543c1c401d2004010360b00080902759080324240c18602c0c1040b03152001d416420408030740a9404901034401c2c0b122044070180010b042c00c0304e032005020b0150501000079121481c0090290802078040301160440000794100c803190503007004c807214665a0398812a071584411184184550b02d000c00018855000c1c504841e00070140a01d505070940d91002040020b401115200c1d0180e414800c1c840001409281c2c0741846601984034160096860f8403242d240c65414401c9020390380100c500c41e8006a001016610b1b80c6078101e0300544c89544541060340140001ea00242c814070860194141850020590f413149024095010607240d50b14400d100607449144991131010303c080142040d02032251fa841100c03c0c5c407801c0700385 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 889247383 1250 889246133 889246139
    0xb0d0f0c030b0f090606060c0a12090803070c0305120301081e15251d210712030e0901240e04020c011e05060a120314162325 55
    0xc81100000c82d8001491280340041c800d40344c10400146a000104a94003444d2a49079800c80f5104c2c91020703001086c3c107031804003c06241d8010700242c0d0241804e102102d0300c800da80d044c60510340020740f00644072409034a5817501711116000449040e100c1c40002801c81c3d809009540c81d03403038404c112640d494000c14252007a1003a4003e1060f01400440707101945008881d0700b040700300d02e008482d5000f03106210041080440d0001011901c144044410b5003000f800c80241e444080385d6204880514007412201042c98054245a649014000e80e07407140700d620795001348000c4100c28040c03e86006001c06212054030401d0314680c1c0c0342021441e00d5400c0c200d80c40041400d03a000207000b0350720b694440d4111407107030004501d4030b074440700c1030002403219042c22000b041c075201d00b40c05507013494004a43e8800030300d03000700e540124101607080440e64401c0701344017403070b000d016001c0201c2d03221000584420011006010903030307107062880d01a01480b0200400c0201d820188100300c0c0c1443c1600c4000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 889248633 1250 889247383 889247393
    0xe1e0d031b030306030b061207170a050601060306031a010810050408190e1207152601060801140301090b070e040b15040e0c030114011d040509150a0b0d0f0c03 70
    0x45102522075140030411509600d0302c1b00114500404a60080910401d990b9400200144030002c1f103c044500549881c000b043c80c50038041d03525000b504a10982d4000107a031581070780460200c82c000c0c08100c6026001e240003a4030142b00703200d01c1402ea4068517142550301d17010740c481908540b141c0d111504c0c10f14071451f0810740d280f8206c1c038440030941c1400400854103020078201c82c0d550584000e004111b0601c0c2c00001e100c18030101080070401101c008040c0310131228141102600828039140296a5580008284010034007920315680707041c407000304060405003d036400c030a9000305401d80d990742c2d03000212003120403001d01507481074441c54001f4050720707440950035243c085909007640d100e0403c940d28004080140007070011031000c000400008035a40c03200e4041880034a495035241d140701180303242d0a107007024156400780c40d00041c85510303900090040800a41c070080b5182a94584500000b224441d40b007194100c003015003404000350041c4501042c9610410b1040309450301c0b80c031a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 889249883 1250 889248633 889248677
    0x1e1818050f010509010b0a030807080c060c0a030c0e060a11033001381207030b010e0301061d10150c110906100e0d12030605010e1e0d03 60
    0x96803603030055645081220700c00e00641d41e0000505000303205907400300f00411400195072001810701c01c0089617580170401040111450b0000303160490b9518182403071580d025a200f0b044500110745480d48000d001da01400820001c803400502c1282400105807041d540600d51104001180c00100310342d00e03400c42e0340103110341c05030180e42040514450000d01c00f041640b06802585035400404414128440340c254501c2d032000070f0700341403c2c032104001c48040d150300030040785ca00b150501004000410341c2c95884401900300c240c2c2c4403141100c0c4d1006040c00c071240f03800341c0c5044082d0001c8402070580311208080e005646070f212242c0581d40c440e210300114204824000008021030304a03000e1002c101c01280107004216940841401c3c035000081540c11024120070900c0a82c0e8141d06035a80c442d801480c02c1504120361075130310300c104403006006020310700451b80411a4160902c0180c248103500100e014420301b480d0f60204035078001c2288040c82d1440803020031044042e511007003034550740 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 889251133 1250 889249883 889249931
    0x10b07052a190803031609030b1503060a050f1b04030503040311030d03060b03130f050a0b0702010f180615030c141c030f0f09091e061e18 61
    0x10404081c580c0e2081008400003601c407811034040c802c502c0511809001000300c83e00303c10000c958940303000205030260b501d9009980f0160100998804000344a2b4910044c003581100450507100700d0b59554140344119a000d0301d400821203203240015912000107841c080000d9100ea010505055482d6141c0f46198820780049484443c03500c804140390500f0070420503c650349090510159040c029074800d18000100300c11030014a07181c4007002c1c01944c07251010b0898000c015511f444055051a0305603200542d1620015841c0110200c5400f400c2c2c8501a41e9031101648007501c24183d44134100601080d901c4152044601d680000009902d45941401000614141054101400c3c200b08640e4400101d0010070369440314000002035208024101c9203d40d820000d0b0074480c0000d045031000d08540014001900e4603118500c00d20205000101c00b00c0700c0c200a214031341d100e40402d100890050348505808174085000d0101000321001c1c0c01803ca0499000140080314094241120701205 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 889252383 1250 889251133 889251193
    0xa0e190201110a0b060103110c1b10091802310501080c040e1807051008100f0303170603030d020a03140a0612060b1503010617010518010b0705 63
    0x82408400c5503000602d842c14045507001030800c0302c80e40e0300c4c0c0309144100200600e04144d41c03000720944196200d400c4d20507080c0401c088844515040c400c540d00c15082d05603442c401e0320f0b4900c0840803e4403881c040e02c10340701c4003000c40a550b20b01c0d0301e100c0d000e5041859a1005100505441c81003c58201e28044011603103941c2d07000c4491803d4005020400040c044020035001000144060b00110031581d03000440e410605c0f4405c2510b000190410b00540c10050f44444040e070b11082d0503500050960180011089040383e6560b10a00c40f018402039200050100e42c65028902c0708852200890b6440755000c4c1c01d03646000411161482207a110004a80c0840c7d0344101181c0c4e01101d0300f540b6a441003070b9103001c020f00c0b07060403003031103521b100700800030404d03a03c070405041c2c940c44d0611078003444004010301c660ac95855000150200b0f00c0083c0c419850351000700002454501846500c01c040b2f198100c54101c2d03400d2909680d05540701000607511449003a045070000e908074091130b48400640 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 889253633 1250 889252383 889252423
    0x1404080f070603141012050c043612050c0f101b02010b0105190c0b040f021002030313030c02030a050d0504170a15091e060504290c030a0e 61
    0x165020f01100d0b0490140c0700300c21410780400a62586100d100026141070000c1001e56845601d007441c504804032100d40c1d0018185201c5a040444442d0b00148101c284401c098100000c084004140706a1550142c000410704401d03900c0305006800401c0c000381c002c815070703210034a0881c5491411110340e9030a00e40590b900c000307624070402d4507440700010341d0520091041203c0e55000038450702079004600045805400c0b0501411300400d01ca440d180c3e4030507441501c0c2c2c1f509042c03244515203500d8050b8000c2c10994801007415202100b00c1e0700c10b81e030113a68003c000200d80c604803a00080040b0403601441803255203004142c080066a0034a8100c4d55607d5513941002d018481c101c0744144030000d1a400445803400045d1100750b4090928450300b800125424281442005a40001824111415810f402c07100344010b0740c0101d44220301032144885c054605004032595001c01415510345d40d001c0c0340c040385850500301c000b5a0003001007000410034000e522481030618001c0c0140c01c50261507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 889254883 1250 889253633 889253639
    0xe1902120102070302100c0c050c04020c01020c0708070801051f0e070e0d1101030605030705150310030f031d010e061207020c0415140904080a050703170a020307080a1a011404080f07 80
    0x814021f0382d000100e60320b8035094400c020742c2c980d070380c5070f1200503810b224a80224481c0801c000940c1601c3d020038400e400c40345540c2c3d40d40c2e102621011580902081542014001905005807007807029040707503525000c3c0425881c1980b4440305000c0948450100404115401400d03a03070740951602d042e001d54a0324a41d11207042c000b41c1250440e0340282d0194110f01e40400443d5a1400c8842c203070b0700d8000340d0940d41d5032645d60048000303640d904002d06a00742c170602c40f81030551000c0c0021300e812001c400d1b92050120000190340c909210410242d00490421042c1680d240840c0c130750340c2101c0640111040002110300003015905c881c0509034810300c0c240420071212021741d2034103445004c140d500d82e1003804c1a441e400618800d0b194150b0621100141e280209032040e42c09007000042e084000c207050520145101c00381d4404c1d00d07030000080034400840e0448480d40708042003641e5003102c0025041c0a2001500c40a44206160700300903810700c000540c50f030b0240420b40381a0103150241c021182 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 889256133 1250 889254883 889254913
    0x50705060d02030a0b0f10080a0902090103030207030303060b070f111909022d040302011107030510050a0b0103060608070c1e080a021c0e09062116090e1902120102070302 75
    0x80641c5403a2059a603880380c207070247c9841448503d020902c1c40c01003542c1d41c0300a020300c050b103181c0300001d41208404000005241e400308007001901c1c841c1d03800b0f01600340d41d0600108e00740920540500700188601800c4001482d0b240214102c0101800480a5403150038054070411515400520103503000110440c152540551a410000d003225001182c0d80034070402c114680145d0000034103001640c0c1c003a1402c2c8004001d080003c6520034200e03404ca695030b190090181030705aa10045407401c00170010425030003030041c1002e41e80d156585d541140c1e42c9a41c1240c001c040044140d80600540c803040ca02c0c081d40c2e020411840e40a07803245030796007224290003460445501d0a6448207144d03070039032001d11a845680000e450f0130444180015454200004041420b103e500d0120b01e50002e9003010aa00c0c082044924100006c1001080a0395000050b0aa0380541050109900155808094030f041040d003400d41d14005010080942e03400544a0b089901c01c8905501585c0580881c0d10028 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 889257383 1250 889256133 889256141
    0x6030721020a140f0912101107060b270c040302120102070b0c07050a081803030a090f0609060210050a02070807050a1e020f010804031b03170903090319050705060d02030a 75
    0x240480c00d400d280c24132100340c621150061440300c61245507640740e004134a0004100d0070380e59482c0114100890720b800032000440798002c2c80d08680c0d2a0405124003081c0c64007180512064101c0d901444845111000340038184600401c80382c10703d10280f20100258903844c40b51242c11984200040c0d803110303181130904100340000d040781d88580c0c007000020300068010401070030340d07030b401140f141e2180e2482e031010f041143e644110a4042c403010032501c2030140d001e59031030110b4030071180910034107031199070484204200c2d000d00000341c0d0000c4042509200a40d02059102050745030060071f00b04141d403035980990045806a60079440100220b0501045c4c0c4090f01d018901d81d0000c408092990b4045030424026400050510540e2030000e0305240c01a2611410b4032544001c80c0c2c0b0f0450685070251050120034200000441101e00044e04070034000115140031400034014030b1000e46d03144100c01c1112b00b0000c101c85a01883d000003070f0790307140e413070180800841c0210056164a02120340e0382c221 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 889258633 1250 889257383 889257407
    0x1009080708030720010903080a02030d021c050c03240a0f1806120c0b0a1202030903070b090304080703020d06060803030106031d0109080d11040f060c02180601020c06030721020a 78
    0x180604040b1a1321070b81c01c0b20a080071a41e00080300754032103801002c141d0650041d42900d590440c0009400381c03040c07181d9010141076000300001042680c0f216510b007105408100e0f01c03050038083c80c004014505592062900c19510000c2003929811f46942e142010315446070b0040440b4540d00c046400024180d00460700a081441111581120940c95848080d0818410f4500e24400002d0584c00341c0d20880c40c101207215982819035580c2010519555203900080050790903440043c00b20314242030110856007207643e140000c00e6200d055800f08484909500d00884071180e440c44001070801051015500074042502e002894841d903860010700e008058810007030591420300d2050002c0e00700001e903900c075031078920000360184aa0420b0302c80c1744a1a04000c100f140101ca0018403a50322020414055209841040d5200c40345942000203034800d55210f40035030403403c105000b41c20300902965000c441450001441903025030440d02105d00d8040407215a9000544484000d0b089130312100e031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 889259883 1250 889258633 889258673
    0x902010f180308030601120c020601050a0506211305060103050109031b03140309010902060403050a0c0e041502070f0614011e050a09152303070b0405010e10090807080307 75
    0x1103010703038070001038862180c0001454602c001c13000c114944d205036400c2481c980e4006e01040010a07141020f903507603200344603c034440c1e4a45200400c9130f0500c1030581c1c18200c0315640d50310b1000105030301d001d200b401c000c120b241803c0c1d034980d2160204004100c02d0b4000c40c013030000000c1c01c8200f818010010004c440000c00550050001d46000a40c0032a0b008818000c00c14070688944584122034094003041501030b40c480e50100e00803003803060100300c0500c1180300d54411440349a903400c200c1c00038401185c0c06022281c46403640300018490f50014072841c0e1203024400c808551030fa4410080310000009a01051001001809041c0c00700400e6020030030701e80e0241d421140b0b0071002412511540c003d5154003610b800f400c009030744640c103001c80903045c41e8841c2d51450108142c1c1d21510a50002c41d1071180c41034050001740d81c50407200300c1e01540c1c030607500c240c078040e04d1809000c1171000000c10241007010310700c00003592030030520003040500803440195680c0e000710308200c0180389010400040f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 889261133 1250 889259883 889259897
    0x902063c1201050f010f030905070f08061503120406050d0b09010603090b07020705030c0d05150f0a1812030207050c0909010e1005010b03130c0509010f050913083a0902010f 76
    0x165030f80c1201b04030840c07070039a1a02013108041450880c2c10001140d100c500340ba100f900c00403400703100109003d032150b0780d2003e880700307030b003400c68105980c0c2c00520a81c04a112410007042c082d46100d034006204208683c0001325440340b40c41c011400900c1d00341e01410001c0d581d507150340d040181035040c050300082584000d15410f400c0500081d190003a40003994882c0c00da42440004018091002480390b400b03190300070b81c26280881610010042c1125841c408030320b40940c0703208401d242384480080640001000a030f44240420a0b03009500c002025106881590358442d250f55900c1c4686104010240010a8003542581803038a085c4d000034907140b4060030100117200f484411010b81e41d02c201140030240f849076107400e001100000715040660007100a0001003003500c1845170380d400700c420585e401c4250f0f545001030103030704400c0004002c2541d541044106d44041c8102814044041e00c0521a40d4412403e10043c0c02c00c02e50220012030652111060415580c02c00100d0386d40c2646800c100c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 889262383 1250 889261133 889261159
    0x503160305060612150412110f1c020a02040c02010b0a090204050904030e0105040f03110109060f08041b09091505072613021306030c08010902063c120105 68
    0x10ba200c480c0109404d001307881c540d40910507910308005800a20010301c4d420a918106410f02c080402e8a4440d1240841d000c600807094030394000034003006044000d000f51140c0481503192151588446543d0030861050320741140140c0e07035500c0b6428240720036400000c0c006141a092244401865122240c0b0500c10301c410000364892664003a407096151030114005047e00005031218004c0350019046917000a50200c1000308070400e503207408900740c076080f1165540e407604842000842c4001c0703000a07203500c0880d00107603001d2600e41c039480038196009034054980040c0e0703044a03514402501c0864a181044110314010312820340c001566203802140f45112250010500c01441550040c41100307100141d007000e44103941e503c005500907d80e11040045040c07020140c010b0717000c151003030824088000b80302081480b41d240455400b90509003000c000c002e2600400a40082c0b040c000402924030400403e038040520240026002401d9100d107405030b00680c0c2403e05801c291f008580400e011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 889263633 1250 889262383 889262393
    0x406090207020f27040f0615121113180c080a0c1206021603021006050306060a0e101203050a020c0402160605061f050d0e030403081e04120c05031603 66
    0x11481141c140c07440803a020540d0000e0065100c5041c513207120792443d5051108211030320901c9081c141c0503000500802e0484401000c03d0040781c821403070542400e04d58000001c00d811010010700f080103003400e0400d00081d804c00283e0f40b00e9000640462800042d0b40100001354040074007801c883c40050005d807203d956030084417400d9000344060003480300c03c5d47c1c1c1002500c4e01202c0001e00100800c00c5c0701420f919010b941c51621a00d40c503456030900d90f011400742000684503100b50401003542801e030346800d580040512015008540300f41944501090161440c01451442d074440e87d42c04d80d4650038901c0081c100740407200600d00c1744d0300404c440d08036101c8030b22a100d01560000070000c5c541d1603660001d115650001e1561520924180c001200180c005010b442ca020340003030244420b603020b80540342c5030b10a0340001000c0745c006010300911408040c40302910404041e1055182c15104c0074801184210401c0440700480101d4061155007030910184449810310004080042d0071aa10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 889264883 1250 889263633 889263649
    0x3140307080f0a0b151209010506091803090901030c06090b0c0601030822060306140117071b1401020315010804053705100507053c18040609020702 65
    0x1220418005008241d20540c0c1364000d14214400424031440b02040080941c4943c200105c030401007052240014650801806500d100c1c400042c01d4601c00da680c40694810f9034010a02d00b561880140524005500c5040705d040c00703103010780901181d4602e0110010805c1a16811065a8a03010302c50784122010000c0c4d40d50651f50f0210180782c5032801010300c031040d603031591442d401e4042e2400c0300150150b0164071203c158ad48074000740d0500c2180100558003500c000010410b800036040029074807902c5400c1b07041500742a0920f580c0c5601442d02c1e68441c40182c0b51301f03201d09035800030604c01140d401281e0005503a00c2801c10801519003500e1311503c0d14920181a00031020407140c0d0303034502c0da41c2000103c0c2c581410f06c88003418416030515035518210041c3e8004100e2805010402e4a03001d041919030705804001c011240380c01c401c0c03054143d00203e038a85518030311503100c24000303425004040c026840c43e003c0403001402d101410803040d5003460784a60b000d248100580380240c0c50780d040f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 889266133 1250 889264883 889264891
    0xc18030114060f01110d1b0b130c05040905060114040e1516080606070b0a060801020a17010603060308040b0a03090b0c191e110a05010903080f15060d1e15030314030708 74
    0x1401e0b03905030300c10989107095410b1140c002303001d0070075107041101801105810b420780500030302e1030702200d03074540050004943c0c1c4020007402541c070000041000384a04d260503201000040d10114021901151207841e2448187c0c903908100c1001c000c220b45c4844801e021300c501d01d40ea10f40780d41a8242400803505d103214012029103d411004006035058825410060040003224021035071000074202c0103014001840000c0100010f000000178503d10034058101500c0e0012003a41c030301031800382c00300c0c1c0541c4413041c850203050701d0351400d0004c1000c0400c07552250124100903595001c0102240311041034900502c42400b520b103142000c003100d240c4401c8401348172401d00382c1c4240c4900380c8035803030710400a04c001c1456081010080c1010b90108690380030344400724400402d500d40030381c084592440c101420740c011100703110344403030900281c0100003418607000714090703070b03603840100b200a4588841c05c1038883c519401040040562164482892401181c1101d0844c200721300c0c010620310000c0c5c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 889267383 1250 889266133 889266137
    0xb01050f09010c0b340e01110c030d050405040b031b0d0203010b0d060c1e02151e0c03070e0301110301030b060312130612140c18030114060f01110d 65
    0x8110044164002d41e445660319400c9078800f0707503038500b151201784883c02044089048034103403890410f2441d071034102c603035800c003007504c07041d0250380407000441d02da90021608030000c1c80341c14015040d075203040c858900045629540c040d652400e04080c08162000c1c403d000380a42d00207800d48510100d1003150080c82c02049416154121250000074050002982c001e035000381d805038110208101c80d440b0301004051030700c7c0c2c1013500f80f8014402282096446040e80580c003c4040c2041e807002d22a01a58003565040c202020039a58500904118404951801e030841e0300100340001c0380d030400c0e01d030024000c0483c002c1c800c0014100000040f800107100080030202a4408504190b8040c007a0150404400c0841500c601c11082c041d821035149129950101e5100d150585601d401d5004941660101c03288229280c0c44088944030154040c0303e48280282c03180680e505c1903a801e000d1003944d01c1d041c505a194030304050741040001d194106240f41030140e003c644202281c008140008800264 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 889268633 1250 889267383 889267387
    0xc020a0c0e190b0d0c08012f040b1e191b08070204020c0703150507091d160302040b0a0507052424090f100614250f20040b01050f 57
    0x180002c1191491300050007840002050030100b03065005620013441856128a221142045108259208919120300f1070142e641000140a4240b0041c02010b91064090701740d40c03101c0050108852a030080c0c1d1524920051103002c3d82905548580a212106a0079501d07000c40304881d40e41440b80c0c03281d010000e00031500800c002d00c544005200480003507800582080c030b00020245d01300000c14003207481d10041810b910000c50610302202c1415a801400200d1043d280c80b03125051098600ca2840c1e101010380802000c120f8880b42da000d0f100859042c0c9415844460901c0d02506158000340b0f4040b01d6010090a103102005004d00c107500002d030808840400f40c045584e1260918405950030380240c8800306008528400010140c8500741d1501009070941e00d5102c00c030341816000b800d80304960014131050281c1345004924100a05141080c0a0301c1c500958594000340c14080f01615001c1c040384002d0040030702e003c2c0d0314143d0070044404200c140c5603800003030080d010f03c142203100f030100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 889269883 1250 889268633 889268651
    0x10806100306091a071106090a20040b0a08010618020c0d11070e130b0a0e03190516060b09011e03080304080904050c031902040503070e04020a090c020a0c0e19 70
    0x1050200721002070301180784d041d946000800980700d0101e6900f801c0c1103114500000d045103002041c4402c0465005401801100480c80b0b0200064881d0365038503805a900d22000039155107000a20009000c03440c000301d0003514018070b00001c0c0004003503140e40b0783e00410942000040102c0c281c7c101000505004400c6000c4035205031406081e90404202c2d68181001c0c4a4030000c00310340350010358880c85021450750f40f1400d0000a5038030404541c402d5030310034010070103842021410b0b50b801008629041c4d0a04804400030310b0390b0000210103841440da606002030385410302c1c3c110540504040d02003410b99904418200c0f107041c002e803001401e00030300480482e080104080448107145402041030046003031000612a959105990301d00c51000042c02031812511540243c1b0300b140e100601a01102e8900064031900c42d000a004a900c041140c0d004540c8038010302c21002d0784441f0340e0040210f00f515107040b08090f5000c1e040148161100c00400107031210314810104401c1d0500c90104083c2e503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 889271133 1250 889269883 889269893
    0x30a0c050f0a0c201e01030b06070c05031504050307030311190801050f150d02070203190b0106020d05030f06040c1407061a06120406090804030f0305030f01080610030609 75
    0x24031100151401c0c002071000c4805601040800c080d5000783c0c00424182c540032800c1c0c0d545034070b28200b20f40103500462990220602e80881d03490808042c1404210324a140b4001059070784050340c00c4900181111040c05641401c0180d004004035141d803d4180b070400d91070703007943c07030260703410003820035440d0540c0640011440d010740300210010034080148074628540508501000d0140c1d90260044c4070400050b0b15011a4072600f00b800d150741c40b8074140c148140c54000e50310100b0166003603c80c0000704145940b840c0e144428240c0109130b484d481e9410684000d0030020180cad0601c04000c82401804080c8100401c41a000710080700c0014132112a04c50035140158180000e500344240030444009102c84e5801c020591500180b0844141a00f282002564010a018266036103081c1d00050002011350b0301032190380e0301a91140741026035940c1c0e03452030280c0f503940460000740c000c8148206084c1c85258240580100070152880f860003110111031007180d4800608016258600b40301402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 889272383 1250 889271133 889271137
    0x90504021c0501060e04080307021005060f04020904110309030c101b0c15060f050a12050c091306060f09050a050115050a050c010c0309031e020d2d02160e0c030a0c05 73
    0x4051800030807241b80a0801c940d0310b400480ba020094050b120355040d0740505c07882514440c0000401001400d1025800e01c4000d40192610f250400d80d100b00110175913881101461003616500020741da00c4e4043c24840d410501504000d403042c500300101c14400389100040c0c3d040340901c610340800c0c0b442d007a05100407030f0340e03840d02018403291504e0380110b1120300190905043d50b006070340303681b0b080d0380d074507404503070032001001c05441508002040026442c002c40810782215640e00043d40c0ca11081c1c86e1001100d141c2d900a400f1410145010800d541240c0111680241c95003010401b641c500424142a101ca14103010100079000500c50f0040d4040c109a4054180410003000b07615003210001d4010320b050041903000c02c4405040b84822400359804005004190380981a0940d1481c02612110112129050120f010041e1907405201c0400b040d01000c07640c0e401030001c01684ca0109004801e2900100103007070146042003071900c40d880450b1341214440038005880382c00c003c0215824 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 889273633 1250 889272383 889272389
    0x3130801090c0e25030e0f0a0c092c1f0b030606151b1e03040303170c040305010e010504020913050a0b041b031511031317090301020403031206090504021c050106 71
    0x807182c00070344d0b102c1013a490f6200009860004040f076900c3c10018160983d20130320a81c000740b40700d040c81c0080c4080c107178a420400c00b1140c11031100381d204454804100d2200324400d80110380390b2041000003100b0180781c11542c83d10001007003c101c0a00b80e1004691107220040c415402203d0380b043c40b00454800310b040b5400d54502500154103400012840307a01c50b0046040c0c09415a036140d00c15180043c040111811658985c40307500c0c03103c4200508800200c801440d6420029040c400080403031400e000c0d442c0410201d000000c1d65151610400070304d054050580380d03002540e42d20a900040000462802381a04050400c442d503440d841c1c401c50702440040c900d0000a5003402c00000c000c8031000051610130f031400c052040031101d0b40c000c05035000807101c1d40781c061003561089011403602c0704942c100400580b4440d01c1e10782e58a01103421f9a0047c0d10072000240e9011090f070f4955854455007001d030251400911990920b030300002d951100c086001ea03041c1c114016a502088801d620131401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 889274883 1250 889273633 889273681
    0xf0806100c05102a0e0a0608040f0f0311010509010b150304020402040302060417011802090609040c0b041401110f070303050c0712080901030e0a03021f110c03130801090c0e 76
    0x804c00c481030460400c00c608100a803851101c0ca01003140c034011400030144070000780a90080c50701c3c1c040120346001c1c000c0c1050300e507800c2c1c07000c40a01165140040c01d40d402c0c040e0301c7e884800c241c0130840b01d0848100410396036660345484200c0c105513640601d0840d1000100d6461074898035503000280007440b0743d43c00254001c00c009000120342c013981120b8204599001c2c02000300d814900703410702c850035a000300203500400880c00600c4c0b515004404070380081c09180414042619030f68011030b0b60348241c0110b00c0342e50140640c0e0f45170b50391040c40b440d80204c804000d4488200961042d564030182408014180b1102040030403070754400b00414002803050f511621580210740c00c244071258010382c4864006070030080e1010060f06c4c00108010780c140e142e8020b0010340c43c20020659100800078911485540f036226100b0210507103c06000351641300d1001c1c0d56a224111100005009190700c42c03903030303a4103002080012941d54004c0c0404c4030421401000b540d07440d00c0303440c00d1035445842c8802e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 889276133 1250 889274883 889274891
    0x15030b0118060e210c01050a20010510060c0c1a0d050109090215090102070e07090905041101030c0801080c1509040920120a0f0302070b03160f0806100c0510 69
    0xa100c40d4841451941c0f20801c2d01e0040f0013401e10000304c00c21020703240c0510120b0303000102d425001c4d44508001c0210891500c0c0054000f1b81d40c0c0c40150000030007420070a480d1391210103000c800c040c00608240105500e041040000003140c1c0c40e6612101107202e031a00d44c58004013140840c0c414607088840912411004108640c1c40e80f505800814a00e039003640a50b814403114003442da418000c507032010030140c00900900e8a06841c803524220f0051040c010849030b8940002e120605004a0b40924425848141c40482c1900010200e6804440305010840341c0300040181c0c00c40400c07644510101901c14180721018010341560074880c81901d035422510b02030f069010310034440c001c8924034032003518a080445000c0c0412545000305280826580c019089510008004042100083d84640141d4403802c1c0e40d20403250f02504101c1c2c840600c1c140039039501e1000380c0d12904800500c003d6007444001030900d08081958000c981d0140000e205d030381e000c4001409401c114014070300c10202000c1c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 889277383 1250 889276133 889276139
    0x1501051210060e150909062b02030c04150312200c03120903070e15060c030c1c0504060305270a0309050405061804030e030303040c080c0a15030b0118 66
    0x40c081d2810701c185000103684551481891404426620390703d00384181250034449a04200840a2809403004e0b6000040c0284040f548080d24500402c60349054402c00510b01a40141810400d0803030076544074500c1c0c41d80351409088a074140409503500030304284100300e031402c0240c903051952031180500200f030008602184a00296025184900b58141d95009001015200716030080d80359141d40368108400502034651803041444e400030080d0030502040d1044c2000c5005076005007400c06250b040001c004034203e030200000f0082d00c240e080220201101807000504c0c078080e6000758020185c132100403d81240419213592141c46122030440d000c200707100d094070760790800d1000403008114203070000500c41c90140300d02d510841014250000c1350096a14050b40000011310850a20400d210525200e840030006144620701c229071000030344d0305003c209031601d81e64940180c0b207814002c41c1030092501079a503000907075440d81000314020041c5030041e90301200c0d00b00c2c0be99588807000400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 889278633 1250 889277383 889277401
    0x1a10051c021219060f1401030b060f090109080312010303030902010c0501050c0a0f020102190c03181206050a0504050a0204020c0f031201060314131518060606140a0815010512 77
    0x428000d054480f04000b8070140304001e802030300d8161160540d104041c0d5403c02c0b21192200c1c0d0b2202c06001454001b65042ea0a00010a583c214003400c203859078001c190b0186550300565000c000d040d04000139404c0c845003200548420304140802000c141d1542d25000841e40102824690150300600a20844c40c19419640c1d0075004401542c0018062802d480c1d420342c01842110720703150602500c0c49840d112507006445001d40f00d18110704000414030b802d071580e00c402142101522140706d440c000103400e424058150b800c068140351150340303031005000008200160b03882c10107a042d100980c0700c001441155040104c8010020a5400300254082000d82c0e41d444c0d46043c1c0b450394a040018080c1d180c03450010840842c1c0c0e07240503110080300c400104030300d40031321001c441c844000407904080c03261a141d0040782d6110101d41c2940c0301e01084c80181e402c925030f07242024170305010390304200079404018100e00019000140030445818070380d20b280d01c20003c41c0c2c40e03034202e8088001c00e8244000c0e5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 889279883 1250 889278633 889278667
    0x60a08150103090c171f0e10110702220207150c0e06070f260717130506071a070f11060c0703030c02071a0406031a10051c02 55
    0x241068000400c004a80c9602910070707442e01c1c981056030808035906000c0720040c14264640355a080303110f113006075400008480c4200c42d44146608001c60746401248900780ba0045a030303841144c160510454401840d00c07401030b900301e42e17011540c00d000d20b48803147c412250b02c05c241c80c400009000150740b00902c0301c0011130184800440208210214410b84d007221258092443e40e54071402c10004d510220b1180090100c2250080008081d0351418000411640c4085402d955114201084101c02e0001c041c1110000394224240540380445420802d81008068000c142c41148003041d10b41c00c3c011802c0042203203041352400741e80c5c0740c1803048010f4003141410070546d00140401e00c84100e50103011660500841b0400d05490a056265600764003402401e841e4400b1032099850001da0500071a0000b0403610844240701d0b03075682002d00042c1662503e00350400541e8008401c1501c5071078600e810600d0800b1403410544651042002c501469580000624101d00115241c00c1d603d400c0c1413 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 889281133 1250 889279883 889279891
    0x109150201240e040807050c0907080702101406121606030b0a0f0608040210020c090c0d0b040506060d15030b090c2805010806031005181e0307081305060a08 69
    0xc0712420a051500082460220b54002c0d142c9106510020800050100b40075195541c80f80e419102001072050104030222030031540180024065400c0c0001c1c550107010f00061403100a00900040103040c1d8401ea42c0600909464083d1442030010303008208240000d2400841318170a45440315a03e4500a000c1c1a100d03251510803810030340002080d1105030340e10b504545442d180c080381c6650316000c00c181c1c107580d00344020a5010381d90bc0d0989640c0e82c1c01900f4400e51582300740648507818a01079000f1510800d000c0784c003e0f8600700c24003295688020070b80d0859070403580d000c201d41001c00700b450b07400c241e07990009081c440900c003840b030944004100040c41101c1600c41260fa4981705a00c4c00501e020b80300c60407022900090140455449103a4a030741c001c070060222048002012801d0046920484030300101e01c5c0c9103001355a040f4821f201c0440100540e140d15084205900070311500c07032054820041604030300082d044030508610b2a81d00090000034845921405180070180080f00100e03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 889282383 1250 889281133 889281161
    0x20c102106090c080412182112090602031210050907030b09060f0f040c110a26030702030315041512030f03020310030809060c03070c180204060f0e0109150201 70
    0x41c3d003240400e07108480e454460b80c2c00c1840042c1c0000d00328403d4400e00360b2408070314a039000341000807a1030041c100b07000402e80300000c107460802440b428404240e910145c1c0c0c2d42d04000020100b0002d20b6400815038540b0b00d400202420780d9103620032040070000b015403103a50442d81d84030400420716055403181d44110300548400321184d40e00c2d000c0106001000c401e41d9840f0300c0480d00c2e0300d40c5041c01c1c3d20410038402e5500784030a84000400f60319240c00c5407404200c80c400c1c5404d0341d0340b1141d0044070b04244100c0c44a0107041c1182840580a5141d0000900452030340c21800070b059902c0c3d40d00d400110b20701540c4910700603074a4655445100f0000b29010581c080b44000344203080c0e180c0300388200c03031203404008010b090660950340e0b443c4a0382d120303811440d8400c8003400b002c000c08100f44001c02c0f049100d440300100d020320b4400c10080e81c2004c6189001400d1050004003c1075030490301c4c00321785100318507000782c0324008000140d881014540102c4407043c1b4244540c2d855580551100c00302c00401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 889283633 1250 889282383 889282391
    0x210b090a0c060224061e0409020307090f11030f1603060f03060516090521011d031c0c02191410021c020711011407080a09060807020c01020c10210609 66
    0x142003c1d6160620682e51170b60054005901d45061b4100401d0900148500034400b080c03164a5030002458407100f0381124070b40d179965030b00b110849001352181446014000c00071f1030940c81c1194410703e103403000422180308080b90300380445100d84a0380c041c1002d401039081040010307481e400e2400050104481a94264101d20120b10129000d031007200103c40f001000e8410b8041c0340303075508502c0c4000007482d842564960324044490f1941310042a500800715008549515203802001720f1214124108a1010b1808403400845a804504041110100c2001c006014000d16000061a0007401e06c00030a01030000380380503900c41c42c1c0003400c916030340c05da0241c001e00c40e800400080b23110340c1c0401424401c290000b14019401245007135400621204083c4c204112511061801d03441242c509001643c1502e0600015030010404c0b03411505501c020b200d641c8032100040c1d91030950035541c520a0750021115001d0324440c43c5000380720080201904071449080e81e590024090328025454000c2c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 889284883 1250 889283633 889283683
    0x19030803040312051302041e180611030403120c11060411091605031f0b04060c020108070305090a14100e06011809050d080c0d020301080610210b090a0c0602 69
    0x41c0105801800701110b802c9003605e1079420807004010000150307000310070f035800d0518840b110388104000b00d0000b494090244503640340100850303040c0981c034000c00d03505106100100360f0040c90300781c400c0c640304000500420307205010360f1104a1054242c0b014482e500c2008100142c5858281d403080302075444181d10b40764600100c0c00203201401e5000001e1003407002626000f140e5442c01038459000d00041255602d0f0300c0ca400f500d0340700b0340050012503940020100ac6582c002801c544c044000d260030003c50801854503600d49420000203001d9500c40c01046800b00420f2043c03429814280408201d074070756200030700361900c100340f180c005001040038103100071400a005400c0c0d40c40d4400060131a00c9110901916820f00107000310901c1d00c418000325011041c20b20055000c0e02030b41c40180001c2c5002c0e410307010102100d03081401d0469a06003501c19420303900e500303440d103541d02c20b01440c03003a600e0341d4102e4508107000d00040c205032007030200007400c541c012942501941442c9051002801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 889286133 1250 889284883 889284917
    0x21903030b060313111c11370e060a050f13051f0b12130804090c03381c0605011d07050c070b0309160905090c010201050c0711190308030403 62
    0x110f001c11191b0032640e17070744401c001440d131184101f00440080402003d060503000390a5950400e00784001141980d14403050401e401c080d56000400d201c106c094000c0c541440420540304d0203204980c0075038449a6000402d6403003508080c640c01d0220020001c078038190652642e90146a0058107110502510102d031a2040c1c1c07084404241030407032a084c49032180b034040039040009000c181c40c1074900b0312010030012224040e194280c0b90756a03022031a400b89030a4408100c41e503c5a0150410745040d417030540741000d265000c03001d441201c00801280c0d04403a41500c0c0156094020002444e10b0004101c0c0d0b40c2d802c0c40031560203c642d07060500d035610750030161258071851030b20b0311541e0300007070702009980d504000643c0c0c0980c0c65004d41d4080480c0c0b0403030712001d580c29000b85c1c45950f103840801191050030440140014000d1001b400340d41000b03840340300188a42034002e850068201194486912600400c0c00104032444920209540e6400c0610341034109450444c00941d1034080021011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 889287383 1250 889286133 889286149
    0xf0506030a1e1d2413080d0230150409080c070801111602060702131a090c1e030406091a0f0a0902030c100e030109050303010906080d021903030b06031311 68
    0x41c10204c18024180c08454080b0198030042904010168246001c0001240301001d00340650b680140561904a074182c240c81440d001010b00d003171200300803203040884c0352446645420250009551204001507404a8060480400702524a410004210030a030b0b01c0040e80310200d940300c9000700040400301c100304820b0310a6000b251640409a8145800351400d04003d00141384000c006030b46542500809109607940ca2030f0703070320045a02e001826424200039948552000000300e149140c4032040940004030301150523081140c40c004400102040f0080d4042d680140c0c00a811a00304808640031911840d000c5410010301e1031503030003180e44c10b0709a029101c021766005000e440c40c80e040c0c406000e5400b041460f0319041106181c14007619440c00e00c1401e40c43e078013440c00f4641e41d40c108442502550a1544003c046074810621006401c0d80840d50b981c040640b50440e03650381042d13086c1103000c1c106410fa00e9602c10800010b00c14410038800300c2ea003031948203412340140d02c540d1100300005c80c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 889288633 1250 889287383 889287403
    0x8010c140a08070e0406030f0204060803090d0f1a18010b190603020901030f0e03040e130215161203020a110a03080105010c0f050d030b09100f0506030a1e1d 69
    0x30401e01010000c81e009281442d03000c040c618000701130680f0700c00000d069035810360040e1040c92000f00c0c90303025800e0038054903018066080c015890204520017040c0c2440c01140050703c1000526206c00c10040b021100e004c0d00100c40040c008142408200804111105003010300590702e0008403203441d041c580c421070024200080c14052503071502400b94040d50140d0042d80c109651030401e005c0d0440d0a00c02d01c42c202446500954031a800d0030b4a100f014800a01020043d407107801c1c01343d006a0360000c516814521541c12651604058503501440400160004201a940201030350310340740e242e406450401c1440c4d50780030780080d20300304041d2100c511500160016060100600c480d5000c3e0105141c103520070300606110482648a00e81000040c0c0800f400107503d23164018403514000a103c2d80120707041c8101441c072803914005141c1d43c1864800c0c103029200200010729015000c1c0d100079001083e8401410094031044028401081d4440310300e401d080034a1401d1000c040e00107640002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 889289883 1250 889288633 889288667
    0x9030406021606200f011b0909140703110f07050604290a0b0d050f0d091505090411270a09140114040e030403060e0c060c2a100908010c 60
    0x14107140d000f40b04c1d0380781c001000040c10b544104000492100700c24032403e00c1244c0c5803d018826025106402081004980e12181d0b00509000002d0740c800303a040011a0012401c3c100000c1c0c110450602c0c8810340030303507219000070381d001181b000c040c0a00416420f03c69885403a02d1001e490005d0800040c42c040141140c11282c00e4100107540c1c08101e901100c20700030010050003010100daa41d692804003000d003050440d42055603c03030042908540e0700c00251411905e4a6204d038400200107085000701b545d5548261746420309070711882c5400c41215008812090340482c6096004c160b15004481d17049040e0180c0450000000d502c102441a001501032101c0d40d81c0303070f503481c00d01c8198490081c100cad030a5002e0345d140d03444855180200000d02c0250310134240400e04000c2003680c0381c141040c0c0d10301d082c021070080090340f00360500410340c0c0714003006c45680403201010140c0b16890345020454080d40104441503141c032a1508080c4540071030700134030000d000d109981801214a42682c08400c1c5e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 889291133 1250 889289883 889289897
    0xc0e0c211e090309120102090a08011806021c0203070f080a052e080607080429182a1e010c02090702010b031c02060a0b01091a09060309030406021606 66
    0x2102681c00e070754941164140702200d00700140840014111405000840b205030742c0042c101900d420001c0b10030004180c2c0794020083c0c0410b4400032081c0b02e031240401440241c0c0010081c02c00002416425004403101c2c40854032460b0425018207404110905000852000e0001030842902030003010f00c00c40d046410748180c2c03449941107401910844600b01c2160244281c00b00d8100400c1004c03920510050f03440100c24107103818a40c3d11403181c812800720440b0325083d0722240784409002c55810580f40352107400e00000c0d84c40d80381c0c10400070700d050083c0d104d802d00f00c080e0010950704400c40c205004555500b490020f0b8041c9010390445040600d000c00d10000000c005890241280303548100c0030300002c65500000400a030800580c8800301c8542111400410314042d41002076543c400300b00b800130080c0c4941e100018040181503c00d000b001000d007111099070303804010030340ea8103000c054082c540342d0400000042c0c60742c00c2030086e8801031044c541142c1990343d98441110403221070ba11650 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 889292383 1250 889291133 889291171
    0xe0a150f0c0203030a0e090702010e03040b030403051219060e06100305040201180f030b0906070816030e01060b090f09070e01030216080703020f0115080304120c0e0c21 74
    0x240d58011441840418041c075281e44401584061009107084006960717040703101d00440c0c0c00c0043e4581c01808200031a850007401d80944000042203e00791b8090b60a9280c49580307500d8100da09101c0c55145100103d0b8800038400035034900e00c080360302c038880b28105022168484070f009101d5041203651a5002c41c0c44400c20101901a601c000d41040c01031400011000c3e011400741c01c11051030b841a0508401c00804100380402c1c6105e80e42c115035808003903c203900300084000d18400000e04110b07059a2091600d080140c000c1c1c3c400005c40c8a240006c1c40056074a26011245d41c01c481112401402c000351466014580050134a10070110358607410310722030008c80110000d410200d4840c07600c00030209540b0115001c14003030304016101c1d0b402088001080f0a40c14217580c2041d440e00d1141c02c0120040c00b107040c1c00700a45054405142aa0718484c00c1401d00005500b440d0340701c3e29500d503103441406940c000c140000c16045801a80440c3c080c0411616804586e900b190001001c1d168050701c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 889293633 1250 889292383 889292387
    0x70602180303030906060102010f020901211d071e05130e0a020414060f04150306110d020a180807121b1703040311030a05060106080a0e03040f0302010e0a15 69
    0x150005048000d111810595100046840d5902c1524529490307400201044910342c2d09000f041d000700e801c1041541082d6230740001030024a821484450a941a2131101c40001100d80c01038040b1113101e0f12980c441904040256150718540c040e50105468501c1c104d240200c0c5541c1d0042200c20207800b900314401040d4400740201008080d01aa0303009521940015a465014016038101d940e001030090b800c0c5030081000c100c5c4007619071405a403c10002c404035902c80d032001c200320307608202c0104810000c00030000940c451080840b100c10320101d1410f030b109034030007240d00c84c1e1100000048a8541c0f01c0c2001e81d91440d880c401d41545186c503020060002d00d50048039400a501c0591407401316450309000b00c0780c03030200c83c4a029280e20120381041132000790b0340080403810f0164080c04d03650300d443e10b0300e90700c5560500aaa081c0401070002c2145d013280d5074080c01000c1000c00507251650344405042910b03140d1480103a0005013a004030500030320780041084115050589030310030841c0040341c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 889294883 1250 889293633 889293637
    0x80c06131203111b2403010519030605071701081203010311060c0106030b0618041101032003100914091b06090607050102040501031b020c010c020a120302010b12030906070602 77
    0x403400c224254001c640c01c0c0404200b00242c1c1d02c074008403411000031304030034000c0a00d0340c02800c500c201402e4411130301ca8500704d0120390544900303644d80030280c202d81c100d044410f6541c0d800200000d10309410003e40f80c0d070203548a02c2d11208500706450700e90303858461542e80d0003c06030092004804000401c00140b480c821911a80c0010300528140300112030301d1421152140d1054491801900400002c0d207040c42c000c18000c02000441c0d42141882d41350400b914410b51059414165540f800c03d0085105c0c81d40002c5509104407030981e01e103840c0c01c0701d5640d51010301c681c105030750500d8030001d10301c5181c022035403207005014010302511651150241c00402c0581c07000d0741010342081404d0b0951190310060030b041d402500056074452034100010211020b44001c146a03140e2001441c0e01503070301040c3c0b0507a005017460031201100e024000544d001c1c880398010710383d007410301c21503c04064045d04403200380c0c4400c881c3c0c42d01000340901051b44a00c41d0741e0f0520b500442c20010440040d05541c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 889296133 1250 889294883 889294919
    0x915070306150903060b01020f0a0b06060f0a0c0b01091109150d111201060e0a14041b030515240c0c0301060f031e080708030a0b0301060f080c0613 65
    0x103400315203240d0719210310754842086240040018001801403080c41114024494070100070b100400050012203030700380d100e05980000820662080011410540d03480098503200c22a4540440d41e400c4060405003500b43c2c0c025044481884075400080d01d014580710310340b100d01c0300101c05454446401e0401882240070b00d41124100f000b400b055001465a100e40b820125426103201c4d40c9800d0740180500302101640010200020702c001800e85844035080301e012128007191201c10b44040c200014054003152034040c0c10620803100002c0215030503001a03006404003885070910002e240c0c2800030b0055510500c000615451490190a10280c1c004015142c0e80c43e05a03400c0032a034600090079601c0a5012004074030046c0d00510030301420b408000300d8032601e110300c00341440c1d20342d440003080e015a420103000d0f48004400185c43c00081d4200324003403c4002d00070040103458090080b0001858003800c4564411011500c8160800f0800c40303402594017030350801d00c0c914051a00e001804030803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 889297383 1250 889296133 889296137
    0x1202010e0a03060e0a05010f060b0f0a0c0f03050702040e0a081b070b070f0b01082d01021605010606030f020702061e0d050f01090e010903080103020907050906031006020d08091507 79
    0x41c1c8000040f0340701d485203002c04040314020f096a80b50328102036094801081074410f4080c40e2500411140c02c1d20030441d078501101c21050780d100ca009035810740318840d15100141a030202445d0100416502500811020340700310390400c5040c1205c0452952651403250050021204000c07041940605000d4410701c59412400c0f034503500d031598100046604105804c45008480710014020040d08504150160094a00a1140d11a6003455010005c01c00c44001e9809400c0041040100003e4044501c1c1a1200740d603001d2038500c1c2c0c4ac100b0300a014510407040040d1411091402001e1180200c988180d0007c20381030420b1aa28084140c954040d404201604002c1200c58002e49807405104c0c41035086413401120b41d85042024400d64040c6105c61045901d00210140040e4001c0e1460341580c0c1c0651707154001d0750300e505068a20b4802d010001c0c2d030080d008010454420307401100c080c241e440300d50985124881945064800040941c0d41e01d000750001403080b02240e94903d03504d0b030f1085044c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 889298633 1250 889297383 889297399
    0x40c050616080c0a0303050105010215010e0709051f021b0d080f19110105070e0d060b01050c370803041202010f0c08040512031501030902040e03040806010611071202010e 75
    0xd55602c82103520501c0341d81901d030000d103951000d0541511665004100a001402d4000302104030451505014000c2c9200d02d0210740200c0e690f28410b54864002c7c1c203000d8008901c50901038080c80342c031208400244014440e008039440d640c0408104d8615681c805015010f00381c0c1c896035880c1c19500b202080c206a9030381408240320481c0110300c2110320403040e4803188220105520080c0c2910001000304040c010014541d180c0d0361518214920403d4100d00002205501c07100120ba2a100c0d1140100262040014101030030303281c03a8480345880903039000c07003021160540b151111041141c00103420404288000307000704540c2c001010300c2c17000f68800001d50101d818441b004407078000320f11400045800d420442080000c2004002c80140c41140030b0031458003200c000000304001007180d0400d9102d41043c03046452325040300b001441d00a05990b25151240540d541c0d0b0042440b80d84001640c0c0c41c61288000b5000c00c0b04001d5130344d840e03075104480105070011354100144820305a040015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 889299883 1250 889298633 889298677
    0x80c1e09040f050f06151905030618010509070609031b0e041a25110304090912090b160b041e060506010315080721082b05040c0506 58
    0x6600599115078800c545140034442c0c01e040c1280341591896040d01c155101c40c06101940080b007008641c0100b040703800e004401003885502c000c2450341d922082e094410501030101c03003085400003500395940c00b0000c0003140d0340c40312501e54071841441b40c000420b02c051010300102e42c01080340300800c400c850200c0e80b415510341c0035480300c500441e000d880c3c445490090100b49000c550a0039000034203018040d01d0186e000c10003071700310200c001111042c443c030710315511030500d001c0c01543c0041002d02401c020b8190ba6003050102c1060005030000002d92501010031130f040320909489440050301c03892400d180c074a9507089a000700240c41030740c2c13a004002c0d40100704031b40400e4000e0030b24400e02c80856503003403040001d801e90310141030149544e1203110003031212000004030b820449440004101443c071014500e0480e00b0040c5070043c1c600d0348002500e40c043d40c03d40b4440700504000300e40f216a028080b030047c1c003c842c1c040c2d40c0148406440360341000580307002c00240110130400d40c02041210b80c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 889301133 1250 889299883 889299889
    0xd23070305091615080c131719111507032705030a0302010e07061706040c03090c0608010302150319050c0f0409142a0c16260106080c1e 60
    0xc82e880060100c1c02d003200a00c4a03984802c440750000c100d16011811f140b444203504072441d00d24050619554008400d00405282c104104e200522514501500c400350500f80510900e04c92202d903402014803504c08000003101c40c086485054155481882d40c0c2c10100c1100301c180358101503c03100d841c80100218066501348440030806200c0c0c1c000113401007071a007581d42401c1c0c0c0396004c40140040780e04a0008013020014160340f18400329800a9941101882a801060406409080303200c00800102e14aa0081c104605803070003190b1441d0034140201006134507200864122241d81034005c440c00c00d42c0680c0e00842d0700a1034900020b4140320814141c0c44142c1c01c0b40d4000040c290716400f00d082d0490702c450303030582c0102800c3c00e0480b03404004880202c0d180c0040701e52411081000900428140c01401400200e0101d0150b90310200d50360383c8080c4808151007500352043d80c0e6049600e0b20703c0300c14401d80c011501c003540640300c684c103071008024400c001c241080107032090020612845030f03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 889302383 1250 889301133 889301173
    0x60415060206090c041b080402060d18110603163027081606060e15030f1501140d0506161d0f0409050c12030d2307030509 54
    0x46000d41c018422858280303190361600b50b4003500350740a00d150034144144140c02d000c2091b4030f0a50b41c00c1c1086030362624404140a441039074150740b013040c60b01034183c842d1104840c4c00f83d103041c003440002000305120740812003036110030780c2c2400d2040d081021404005000f0b00e0340000240348040f094103041034203044014401c07500c0e00358141080c1d03609024070b80c403142c1c0501101c400141401c5c604d46000c1c0395441c5922881241d20500892403018407413005c0017a00d030070401c06403910380c034044e851f070a11270b401954040c0d0005560f0720030b01501210030f0f21504005100c1c2c500181100c5100f4290b4030f000310501c441c5a1a111a030340040402d104580850340c00c00a8902030b144440c44030b078880b000800020301b00d1140124440032024801400546550b405181040100048078000f804141d01d10301503150503c50a5100d0b00050180b500d102c4240c404000b404d00140c20500c14014900c01280f1049403a1100700001441520a0301013840c80307100e540155800b03807056045454200703900c480c8224030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 889303633 1250 889302383 889302389
    0xa080102030c1b0a0605250806060a082526040f08090303090a0f14010206090607031104050306090c0a050621070e1810090209130b0127030b2d060415 66
    0x140b90071017000700303102c401f46e15a49150130f0b5501c1c1801a41c10040009141c512480c03900800300306055010030702c071441000c00801c4940c6c1411854104411803170010b0141b006400300079a120b0101407190782d01604a045d010300c6194041041c04000110380c1d0348032081c0e04081e088682501c028490703504c454850380714040c0030b000e40d00c0003940c40e81d1400b0028230b41c0c1c201d110905d40c1150420800e004011000203003054021003c2d06002c100d09a0408540001e40a9640501d900d40724900520100c0b030f4010881c0c4203100001c0e42e00703420694a440a05c1010b103e00e408809800b020704a90307400490714000c41640103110741c0b402001d203450140000d141044080d100440c0380080c0307400d11104151115104008010800d0154201241c0c480004c1041c000c220407080b07007548808021045a209000484051160b154040c141115030141040c11000a000441b190b001a4000c1901340c0d01044095088052010420700d40d6440d410940c40080e81c084c203800e800c107440718002c920141c281c850550107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 889304883 1250 889303633 889303651
    0x70e04241a1003060902120f1807090e120a030e060106090803070201081f0608160c030e090a090c090b1816140702030d0c110a030203060c0c1f0204050a080102030c1b0a0605 76
    0x1417424801d08c08501d10300090160780041031581c07d4078100041c0421040102c42c000c40300020403107043ca000e03d080554200d81c0e0f072004900040c031b0031010b80d0168082c08140052500721032950307880c1c80044e0b43c20f007498050700c0c03907e034002d100d004010340c85401001d50140d072010200d08205605181500c0035211600180049000c0d8007c000c040301c050007001040c00503500c0d041102c00c00b03546000d17000d0f0006042681c02034030180300060b12260310340c00c035050159100c58050203031691120300f10020030500044d18801c0058960740a502c01d0403440c418000c00b940303111410307107191f15802511217100b40107040110a009000c1d5102503030b0705111000e450034098032202000061403a1084541e070f82c0d560130310b100e0210703a5000d00c0941ca0000e88607074030035000c05515603940d071442003041c5403150341219150070302c03240300c51038908201c1074018000b00c580547c0c0d14040312341c0700d920160a0380130880d0310594600c41401003040144d0090803030203601142d401a2030812007217032035802c2524000c49003165 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 889306133 1250 889304883 889304917
    0x10e0a0b0901020f010f0c0f0e210f0a0311070b070c121704080601030b06060a0804060b0609040509030c15071b02040f050a05100501050403080d0e070e04241a1003060902 75
    0xc04103400c02495078070303140d540c80c20030400e02080700002c2801d0341c804403644540c42940107036103010f1010020800070380745103811075206103101d1400501c00ec0035000c0300324080c0194140059040341c1c0c081540e8a20358000c0c16034004d44e0600c1e95111041d5602041641c20b80149100f10105906100040000c2c0071440b014049030741c10340c2429802c1000250040703018a404205117075486034000c80c9550025800301012580c00c40e01e500141641c001c03051300390360251601041c071030070100000080c0480264a0192020700c0e0b41c3c45514200c802089600320007140210744051607000508402850300d51004100003003c82c00d640c6102d041364030850700301d000560b03501e0074004501e1011400d08020203092034407a151034150303503030070416005080c00b0180150310741c41808082c032002d2041d0000703401d044260135940d2500742843c603846c001c0d03840b449401112203941c030400303451a40204800a003280c91109802000710041c001c0d2403400c04040703001c00d0f40e206000700e400955400104101c0d03c1528050b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 889307383 1250 889306133 889306151
    0x20a030c150903120f090510080a141e040309151d040b210c0306130b07090e010b03040507080303010f090506040c0c12050403151a010e0a0b0901020f010f 68
    0x92400e2000d078803910203110b10040100000b0701802819000c1d40c00902c1c12000040740c00c5800c0c0d842030013a0b00001d80c081c2602d45050501540000c0383c502c580ca40c10010b010240010001c0240d0401c20f80e9128403404030b0040000101085d00301d000d411520924221940075131380c58051a030304202c0401000002c107100030040300398641317060340c1d40a600f04a0701004052000ca0005038044a107440801050220306005094064184104c084842016003541c05a140c115012021000c0140084840c03043c081d000c5160140308030f0554040e121041c00b6a4440d0b42007060560413074000a000320b515115110f004950303d0300501c081c41c020607000040c0c0d10030310704200f001c04c140c420081949000e1840c000320610b00540c00949081e0090700040300c034400d2404400100ca032881580c0000e4240725010309000d203005601d6005ca00f84004484440c2004901c4100460b1480702414841e50710002c00d000a0010340070b408000c051080c0140100c0c0c20b04008405014207481d01c004048000f55903d8601c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 889308633 1250 889307383 889307399
    0x905061308073905180106120e0a050d180909020f0108041b0312031413080a180b0306040f0e0a150605090a150602241e091b03030a1d010c020a030c 65
    0x1840a4401e40f4a044155070401f20010550500303031201c0414241c031f8881050900401b805a00c00523a007000584240b00720105010f8003050003100d00707910400c456030001840700c1040c4501c60465031b00604882c09446600011102868094800c0d15901c1c0001d08602d020328210201000130351040b22004605c10024501030304895444071070a0b0500521070030001444054050050b1032940290095158441010125651244070505030448500c483e400300316640c0312800b440c80355404450034846032541105440a4403003402003258540d000c00003400c0001c964907500c0c94691681600028401c0c0d4550010b1030441d03080d545100d2107a03660440c1c1901c0c102d1104200080c0c000c0c2e0000702901a0924011020307112030310070318041818000301081003078120951820400c031031100c0700051402c04201840d1509030005060584c01501218a07015003404000d90300c0303081007034a8291244940c8240c48c0045510a01210304010103a0b8035900141e4800e140c0f0005580a403440b046d10724104814 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 889309883 1250 889308633 889308649
    0x210b011e08010504150f17010219080105041118040908090d110405010906050a030303090303020f18010801051905040209030c09041a07051c0e0109020a08010905061308073905 77
    0x41568410f14070340500c40c03550380702944e0b422200d000110b407e810b00e42ea213a0f80c0c0240a001d034a00000e035000400005941c1c0d01283d014142c0744122410860016000d09802080c40703600181c4084420100c0a4070702c0d890154040d0300c106004804c07540c07a02e110280000d0243c180b10008407124192400301d18160300b817510440f4007402c1074030360801801e41800000340c0c009019100082c101030711450400c0405100ba01078813140d04c80301602d25101c0a002007540c84045603845018000350140b0300000300d6242020f5890400c0307043c42480c1e80c121f41070109100181d4020108180c05215803080c910b0541c4680303440d14410b900410a40c102c0158400c1140184140070700038508002d000d2103544480015401040217840044400003000408414100d0152090708800380d0700484e1804006002e031010341110080a114005840e11641c0c2c2450301a468901c100000e050700703000380800c000041d0003982608020031540038a81000750381c1c88581303554100061109804c0c8140c04420081030401c405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 889311133 1250 889309883 889309901
    0x140c070e010e0601080c0307050409151d0115030f09120810090603030203090d020d05060f07020106050103060b0d0203190626010b0306150609030a0c0501080601210b011e08010504 79
    0xb01d0401c00e0b00f002c2d80001c162050107402c000c0907201c000003245ca4513004074100d034000c0c03c00030b0041c41030b03a414513045802002240b203841d81d50307400564441c040011307459405051310348460302002d421448020450041000aa86410b030581c0d4400450101e8800886000100c07107a03507803041e4a181c50f50000154078207a0703200c01c103254207290040c00005d401206440704c40c9019941c1d0340170603140d4000100a007000041c094254080d10040c455091082c4500318404c07071032030f002072114664030001101286e07003d2190380440301d014003441040f155280c00075a0002000300707003001c0d0341140c9200002203c500f64840780303a01c0c07002046c3c00651065400103d0040a10400801007400050080383c2c079501e00411030030010428a60110b4507545500540e564180d002c0e0407142d800fa050320341340441984a0041a000c15a1800000c540350310403030701ca6803c00c51715401012240c000c841018003502e40119144c0c184583e0b620211180c410303500500800c5442c0351340e5a811949000c05200480709419 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 889312383 1250 889311133 889311149
    0x50a020403020f011107061218030c1407080606131b020309030d090302010516030302040b0d020c12070305120702010f0221180a02090a1107050717011b0f140c070e01 73
    0x20001e170b5403800450b480c400c6507050b0800e200c14511140021000b003e00007110102050b0b6207005605041e8400910025140304000c180203800a51101c1a60390301980b00d80070b100e40c85000003503101e00b044c0c200603954001e00d1102113003d41e0040150840c032000880b040005034800f0901e00d56038502008074180508581c00c02c144a5400d41d000280030380306a104075403006c0780c00a20101014441c1e030407500142065191691600d203d03c205502941c0240c0a04115104d140c111003251610710044401c1141e154407000d15101c44150503200c1c01c04004c00b00f02c103656031f0b502d000b40040c2c014002480032200000064904032100700b0411203114020b4a000320703010b080047c000704d4180001d610401903404032060052a91a003c004014149400c2407688401c3c002c100a0204440003407040240c0300002c41d0320b01000c0305a1902400ca40b800c2c3c030103041720300340910310741c800a0040303044082908840c0b40100d16000d2401d5201081e43c08106100c0c0c10350f001c12820002070020459503405842c0c81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 889313633 1250 889312383 889312397
    0x62a0921060a0c050702040b0f041104030204060b0901050703110f162d140d021809120f031302031e0309010f050c06060603190e03071202010903020a24050a020403020f01 75
    0xc1c0d40000c115000c0e140001f4050307a03661158810580c1c2d05440d115180e00002d0003404414120020025660014841240240d0a0174004201054000c09440310b1403410b03551281040391585080316000400c0c408030a480c05040d460780150754040c08400789100c0a07a1200b04150725003000c501c58113030101c6c611050800403180f04c8507011542203c21046507840c00d028900310f080d03540059107080840c00d000b5403040f901007240b0318190890165a00c42d131504002c0c0d0f624115039005050051184000702044142c0c00c00c0022080440100c01480305030000d4220740540b600300c0b0400d80305040c0014070449070703440403914114030340c0e02c5441d46046221910304207050640d103230480c8c5d41c0d8201c040d01c1c0b07501ca01d0000c00001c01040d1104007034104030b018410103214500c01c0c0b1454640b654854002a140825000d403041c000f0741c014060320a56591543c0101070180701a00c480300d0320811516050b44555640e901c2d0198040c59001d807600543d5030302d000507030712441e620400070017078440c1305c0c5203042c4074107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 889314883 1250 889313633 889313651
    0x10905071709100f11070c030501110a0806060703050403140c0a0b090904060b0f15030a0b01030509101e0f0e06090a0503030a0203070210020703030c0809062a0921060a 74
    0x21603d01e980482a46000c210194030250000c042c021401034a44660000700da1031042c01040401d807001caa0140c0000c001d5410070413450a924862817130300401142d91500850000d04255004004c86406440c1850426889a8920f41d06009083d002980c0717a20141c44207540d4581405090010420030807401e01d48500380b404a08030a0b40288041c108680d03c2c0042c1d1226203603040341c3e128544000302000a017841c07900c580081074205542015442d8603241040110f54082c2c861a801840460003e010360204031110340041d01d20392040d8802c3c4844070101d15040403041c0505010703180161030116046800d01307071041c40d11000078816100341e8072508003c1d01058020046a8004e44040c4000d650307646c030910107900d0815108080314040e44000399000915a15038010038844105d503642e4016a03e4801ea040e44d01c0c00700782c070104900d012410482030340e00a292404444084a490024140303403001002a02d049221280b0001c00040341010f440b20160a214460b8002d960700c104010401d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 889316133 1250 889314883 889314901
    0x1620030304080a0206090a03171c0606201e07030b09060403090e090708070306020c0c01110705061803030301060234030b040609050f01020d11031519030501050109050717 75
    0x43d1203c4068000d400000742c0d00c040d0b0300c404000d00302445c3c100a08080005104a82c000716a0010582003940c80d018000744007a0b400380e0007000d0444603281e98800075246002590480503081011004891103070091048081b071202240106600c001d4000d000c041e440c501380034060f69002002d075405500300c1001c0000080d0081551400e80d66108295106643c405110070720b00304081d044001d1901c103141d0004200030b2140c004054a900740c13019038400c00556001516514001100e82d001601304c15001c1c0200c1c00c004c03018110384104007510984e03121095001c40d0840d4000c1c0c010b2001030300492031030181600c516913590101503503c035460046000103028840e00083c01c0c08010724940c1d11402090500c0752a030403010800390002d007510741c0a4000c86006000303602c00ea242ea030b122401c08a0a080e203c0031442601d100741c41404101151510000821060342c64010481210307030742500b03002c80811000d10600e8041c103600c4000240504085202138025044c00040285603401c0d01e0410011039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 889317383 1250 889316133 889316143
    0x1103010b030a0e0a320309030d0e01021f0509010c080103080a0302210a050906090d09120f050a082d0a0c11040c02060612070b03070f0203162003030408 67
    0x4015400c002005040084060f0404d003a025018113030030480c0741030841079641907034401c003903000151120005400a102d140d84a01071606c00a91503001081031a20050242048008071070301481a241c4402001510303031415075940c0c41341c0101550710410090000000d2107454620071803400d03c00c82c01c0d8916518820f0600c11482c05408140d0045040840100c80d407130f001c040d0040c2114000303130318900310403240b0007082c086840c1034440c400c4002060a0a02c0840c070100c2901c3c85540c1c0090050420000d03280318134401100316031041a44008001203402400a00f41c000d00c5108483d550308814000c041d04003454042c0c2c604031f900852001d2036014542011a140255a070a10244410b103e041010048031400303482d47d085414450040f81a40d40412003d1140c0c00c101c0f01811420705101020b590b4178510300458008900070000f041007035000d0200704550350b209204685c0b40403c03020341000142c14501c02181e246075400c0220400031513203918850f507103d055009500b0f00349800f5401b0b5444e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 889318633 1250 889317383 889317391
    0x2d15021b0103090519082701090608060604262401050616020405060a0e10051e010c0314070816140109080d0e01060b070812090a050606063106031103010b03 69
    0x42200308078400c0260101c16070f45c68201700c10887c4c0718034103181064400007402002d85400500020b201269250003001014090507001c1d01040c24682040b510110301c02c454240031944950118521640c6101004180c92084d0801d08c0c1c003a600d60070718020094600c0c1a0007140c4151400d0000c0304002c00c200d08401000c980484000c6038a449440114402d1115a008600c902e880d036020801184408401d10044640c103958401c0c41840c4807950141e40d400c102c200d01c1c000707465034400310702181c03041d100032840031401b03030b101171400480340c0d1108165070000d1507402801d903c0c0c06c45002401207900070b041d180120840280512042030365040440d00c22949182011a507400188100120035802940a0700c0c040b01c0d180d96801d02400c100e800e40d00721910001c91545003c0001e0003800c408144161038950200041050782c54a0041091b55040320840760444420030265403a03150824400e101116002d045014245007080e078000d0a03120b2a41c4000c2c40c0c0c4104000400c807011100c000c90342d00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 889319883 1250 889318633 889318663
    0x20102280605060d021f180f0b07080f030f1b071a0c16060504110312030105060a030b03160801050c25020102071208030a0c08012d15021b01030905 65
    0x890f9107210000d500a0a9218084d40016414030b04031116440d080b124101c2c41d52130b849522040803109682c4080500c180124280901c116004004200c4d400c0c014041d420700c200c0d100c5082105801101809400440f00e89402610840c20300540828904000c11156069070f80d4070315181040c0ca9170b8007414071444030100d11914050000320200405010348117801500d0003400365402050a07c04c015080550f000d43d052050810120102c0c44e00050380c1030700e1000b01c00c40d00c1c11a0f184c40108400c0c0c0e0446400401415214810b840e41550305121a1740205280441d80c8031340d07418110b4144c00c403131000b85480d400080c2000314030103107078280085c20440c24045018001c010102d00c0100e08242c40d075070010481c9140c40b4146410000824003031441082e00c10000c005032182d907942180e080070203100d0a00340e0070303400c2c0c546040f4440f1400903544001c202103100c120903503640511102800900c3c581c00044e080000c402c040e9403111505007100c0402440d003880121010344402d5114a00b14505005e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 889321133 1250 889319883 889319891
    0x50c15070b31021c030509040c05091c020406050604080a050606091506030a0f05190b01050301031509060b1f08060d0c060f0e09041a0604110d0b01020f12070201022806 74
    0x441d40c41800940039000070344403050641c00c2d21701c3c010305103130486034085100714146403107003015038402c0f410340c0d404800003020118440613144500c40c01c00700001090b600a502c03074074003144644800f4010801404803000500360345456042003801c1070b00203048035200701000020300903000d03076009204000f4030041792655643d4540d4484480204410240000c0c4542413504015203c0d144844c4012102022181402003d00f02c200440790380c8400d000044c000c0c00941117011902c0f0107684040b290301c0c42000005107030f07408400001c0084100e00c0080350b4005030000304032a02c950004034103070840c4041e1040c04042c0c1503545c0c0c0540c0d80b001400f440c41004104d0178106c030300f54410780300038604180150815200d81003c0c2000c000580c50170750420341c94017158001c5481801d00748988407070070348810551414007200701d000c10060911805050f0452182c11809550003006101b02d0340380d580913410759a503170101480068100948619960042c4030014000404a82c04400c004030159000300e00003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 889322383 1250 889321133 889321231
    0x60506040b0a1b06051e0709120f1b090b04050f0a02030c070c030302060103331e05010b03010906150f2d091701060b0d09050c15070b 59
    0x20b411064030900c0360010050844200d01340841980242d0048005035840c42c20007140c180da030700707000700180c540748001155081c0812074402031000005003240308107203a0944640e241c4840c42c0c812256000c60020b009030003820032600200740b0445254202c155028007861502520200b80302d44000d00d03036011180c0020008182e00743c2c400c101c1c0e8107158040051112144c407410005d40d52002400101c0e0a18030300704c280c420240c11015043c07000484d03035801c00c049081007440700026061015400d44000c000d9406e0700891204d50040318081c0c241d2071000b9403650f15225001c000c0e40c159a001000342800d4485080c90140d12205403000ca040508140c1e4000c86c4840d404540000500f803269090b00100750f800681c0c03948030b03000001b10f980c5101c0108000c01c40c20f2183d82201c0b10b07407140010f480f408007d4110310004d42c0e0000c0f40c4160140047d94403820041002c118680c494655108210314002191410440c01c48070540d0804c20350012410940d00040d4103441a41da4080710700d42400c4c8448c640303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 889323633 1250 889322383 889322387
    0x207050f2407061b020703060f0624050408010612060f050403021506030313060305150a0f0e09070905010f030318061403091c020325051c0203190806040f060506040b0a 74
    0x182102141103015000c0300b5080304d81c025141c00c5580411030f030b19070400b1035001c22000c1c80d000b0802501c1d01c1c0c01c01c0c64891186a944840ca20175001e030180240300d4203110010341080700b031181800418910311700b0b0040700c5807460044e003180d9030200c406448914001c00e00011076400160222031060b2125074035030680303074000002d140d40200c0c00164201e40c40c13000085600750f810340080d8080e811900b4201ca074190090104108201c80340540958444c0b140c2c0200500c1100d5200306403c1080c1509441c0e50680742c94a000684409030040d0051942c8a50708104041d48590003500c20b241c0c02d01d40002c101d050402c010440161540210001721010001c244140418444402c551f1940ea0b0b044618107040c9601948035041681011810303a40b40c0d10902080f4003103612103101d139500c40084c1160b420042004414480008070076000c51000340500320740600343e24204003440742d050300c400c02185865030410041e5031119500c01d21080c01d08000304081d85410040e40c083e03918030761a5540301c100700713201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 889324883 1250 889323633 889323641
    0x6050405091812093102070804081204030b010e092d0d1d0409020904061812050d2a08060f06030c031510021009080f0a0207050f240706 60
    0x3089158012008102c3c01e0604000c0101503107042581e10b14611644400c6111260308851450843d11001c1104910500c10560060049600c901c080600b81038460314032a24003081042a854202d0300014144203125810340f4441c01000c503010140c500e0300d445600e8035140c0410058880104101c00b40f803000e0000410019484281d00000700c65181800c640018114152107008400d00c1903081d242da0480d0425026244000d84c01a0032010607454542c1c07010b0090107216000341c2e40c030220f00783c0d900c0020700c14000c2c00c03410001d0755940c40e110200b1181c86012142140441c1c0c005800645010b01c581c000000084c13022205401c050005a45080108101e107208640c0781d42e21480000c10480040720020145000f41c60036040c410b040100c44003032204101c01140d18901590040da4140003138021a00405103003440b8404450411084c28170825131908201d0044004d0307084000c1c14025800d041400074a08442100d0b105c1803031100b41041c4042c4101070440201c04c00d40010500b00740700881d04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 889326133 1250 889324883 889324921
    0xe040e010c030501050a0b0703080f1b0307030c020c100c1518050708010f05040c0b25050606100509010c1502091801031101090b090d020409050f0a0c0b040605040509 73
    0x703001c0c01041420050040009000b039910076005400d003c40e007480c04406540c1c600d40e264a44d000d03640c642c41500031981d0401442a404403200644203000d443c11440a540640641d4401046040d0034040190a28402e620240e000354008a803814981d0303070090a0003001604070781e98440c0a0041240e000140141016106040352040145020841c00084940494902c1b8008102050b90200c03460103550007501c5c080c082410f50310062081480300b000802000080d140040c649803e0070a0304840e040c1001400d80d0240c00190402c5010f007015006240c4115803458500d19118a8130006400c0c6502460080c0c41c020140c2c81c103160914840e8100d4001c528014500303d9204202c881c0e418459500340070448102011014500c40c65001c2c00041041d070707020090050400040340244555036031500c0060340d01035110320005010500610184991000c01406410721441034186031500e10302d0f560242c00c1c100e000f00810000c80b46d10000f41d50035038108403540181900c071842c0080004d11018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 889327383 1250 889326133 889326161
    0x304170c0f0f0c12062e05130e0d020a080a261018021305010e0d0611130618140a0801060f150314220f0809090c190e04 53
    0x34000a0010018016004403011a5884134054040e42c40c5a20303480142d0711291182c90b43c0c032104e0b03070404101c0582d802030003038603030364021059480c400900f094002d9041c070800f46a560404110005040c00b00341d07103880d4107000500d03032900d00b540d52504e076110f10300c40341003089160520070310208540795840140c0565052031030200c0c14600007464030601c5900c114508103d501c80940d9a44450b4000d4542541c1c88c190340780103040c60b00c1d005480f895030488038035601000020b880c44c009405403084c20191407800e00590748800c403403124490598500d410130001e001e11200d07420540d02001c81a031095031900b49100d03d103040728030046046400560003c014035400c00c0b901082c01113681464500b2148803100c07410301e142c904031003a0304441a42000d20748107034003000081c00c4003d00e03054034039000222006001c410a07940c0c5a003480040d022104642da0355002441800300c2c0341c016501c98200841c031081c1403505404040304441d405c094401c5006000564480d180f0f560b4880c0d00a40901d0024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 889328633 1250 889327383 889327393
    0x42919270b0c070617071d030a11010305090118061d0f1501050603090d110c060c01091a06030d030f0f0906051015140903010e07060c0b0105060304170c0f 68
    0x1c03000590030b0341055500802c07a21401c0c0c1d001504501c0303200909407540003416800041d440341d400c11a00c2c2c000b006040c500c025032180140441d502d040010310a56401074460403503480c0003400042c00e48501810541043c0c0c1480c4040025005400b00031104a40c00741b0700103818500c1a0804445580c4d54131451000d00500d810755000d00310100b504040500a1400d055052b03032502d00b000214082542c0502080e4807404500315424000d290003034904854904803201c03007c1d604001146a80a000c0e0000541d4440a80400b0000f040c504001104510100c9011900e0b01c040030980c1c45510171103120130140c0f01c01406080d0012503101a026030300c030002c2441015032904000300138020a03583da800c54000ba44d000120082c200e10710070b5036443c40b9a2040069110302c000c0c0d111035080300904540c59542c40e82d00c8515190b0400c040070051048c0d440341c0c0d40c1302140b402c0802004a0507480140202c9041007000300259541c04503d030344844500019440340d10707480c1110b15241130056826220712074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 889329883 1250 889328633 889328639
    0xa0b0307120501120f080a02070b0c030d0e0607050f0a0e0d0605040b07020a0c052809060510091a03070c230f07031707030c050304291927 61
    0x1c40741c101d0740940c201507024003159903116000420101c1c0e611001d0000300d44020a07000040c440c034001d20400015204659460b901c3d18001c410075404440a031195610000e240c002c003007031038011184001046405401c0d5460195000f40451050b1009956010400500103000c0b49c0150515214140043d0178500e00d600185402c500a06041d40d0075a421162400000d40280c400200071000035402008425120710300418407140c0b4190000c03002d0f10b00d00404501200141d41c58000c40140130340750f030210742d15140000340030014511190000402c0f408440074002c400c401040c0c0c0b50640500c10109a8030f036221030007202c600401e440000d041610b180d1900f040850640002159404100c2c20b883c2001491021103a0b500349521005040c030403055072000900d44250301030b000550084c10192030300b113401d990313032070441e80181c200000c94458001ea443c8851041c408078203403400b078018950300d400c004507560039020500c040410100b10800d103030010291140481e241c203420810450141180e1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 889331133 1250 889329883 889329887
    0x7032109060f050903030403210e01050a050114030303070504061b06020a020703020f1806090601050c0d0f08060604061209050102040f0608060418020a0b090616080a02061609090b0a0b0307 83
    0x41598440302c9840e00f4140480d40c54040031003200e0103039905440799081c505a010170440c201d43d50390000c0f001c656032501803a40e0020280500d0381726120b80080090b503581030003004c0c02c8640a00d204980254814800c00c451aa0000116000c1c0e91590603e42980d140d0686444540130702a1030060401c3e00200d4280c039a80c0d00002c100c800d803031080f079405202c0000c0f40280715455041c80c2c50b00d505c0e0b60904021400b5030400141640d00185c1c10b24100c2d16001c844004075150034100410000003505407020f80300181e80c024000c64001404484052405140a100400789418070042e0b050b0196201040020400254100d40040058861190456a54141c0170702414001c6030014025070401d485030034800c844141a5030700c180d0050601e182d65040c9514154190000d410f50790704000c01300030b814105505a0000d03401c0e14440c4082503030700c0d42c604200a01f400800303000d81152003d8803d600c4c402e150060701010a4401020000550304081d0000071700c40c50043e401040780340000810700804c0b0ba = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 889332383 1250 889331133 889331141
    0xa031b0807050d1e0e1905091305010b0108040f020f0f0405090c0306011202090705072a03050f010e120c1507080402100c0f020609030309040f05060f150703210906 72
    0x41600d4842100307244104188000210913540400c000804240c000245407811910020741c0310301e44118492000e8807580410060704094661241010032400c0361010002c09008403100c200003031074005050f040c540c0d1016000d0000540003407040e07040710080301203511070301a0811001402081400103040c40c29051361100c0c43e103542c05000b030280c01d0001c10480c2149000c01865940506840c01640ea0117404950a42210a04950305a0414950602c5130701509a8185042c0060344800c4420f1a601d00145841c0c401c0c20f90308201c2c2d051129000c2c0c1b4089c089060200c120781c0f500c1960342d90b00c07011606407c00c1c07080104074090600040511064984c003149641c4142c2c405d1368242076100c2041c6060305c4000c001d100c0206070000e4143c1c00b00060801074040d1050300c6000d0704582c01c0040d164005801da4800b02c41599141e540e410030801985000002031041c1107095801f03407644000382c0d02031002c0d0b100e10540034050003964880c0800080001d0400340244086010810155040f480c0c210050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 889333633 1250 889332383 889332403
    0x1b0801050a061407030806150f092d09060f0409050106152a030e0d05251a09010905101809272d0b0a0501080a031b080705 54
    0xc500c00701010600e140901094242d00f0300c10141e1506051003650126041d99008003800e4110121940114040104001070311802150100e0b4a884480c3e08050007c41c0e6020b03144201c42050104007050030042107841690400d90640e10700307203a81e55600c085030380c1d07215401510b07801c146044c07036a005101c01940020140c486245440c40b0a9880740e20031103608141c4d0f14000381c41000c60121350312010010044544041c464180700304180d1007070001400080e00c400c015103294101580780d840301241031001d04461700c1d50040413000c10382800000b1b40382e02c10b0041160840040003e400e40668000c0030402d0060500410700440d022480b00c0007807a045440c110302d0568030140310041034110182c011031000d45055030700b485071b01e020080200500c0c801100266000d040a0310a480400c6804031303139030542e50100c04030410303581040c41e01d0800d051009200d046d5139450030006000302c002c04200d240c221901480c10380c0c1120b10604024000320701d0b8040081c885440010320608102c0041000764403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 889334883 1250 889333633 889333639
    0x60e0904030c4d03010b0307090b010909020720010918091502040f080c0a0509041104090507090e0f030a020c0607110405070804061a28050603072a020109090b041b080105 75
    0x1190700c0200a2500b1b82e5040315010b541a085642c040c001d44190b40d01041640005140c040c89281e910200c80089030b0008005540041584401d4040e184c2d030603d070000c00300c40a00c0c040304490700d400003010301c1000c41c07031401c0b032070a854101d224284a80078043c0c90300404004011552580d440c800c204030415a4820300c1458003034208400154035207a21030317404681c0c010702405e12541c0c450355500e21010f2516001540701d5525960b500c0132030401c01000c400b6206100c40001c1200e10310300720900e0030380c00c2103104030746e6030040010383e00b0303154080741c0c80080840c1502d0554580f0690310300042810440c44019400c83d140508104000780d00c02c4d0384502a9000e4841001302030110420392075107800c1140480c0d0465000783c2d2212903007401c0d0784aa007400c600640462050b58484002450903801500c0d0500004d11900003811760407208100b52010400b00d161800e808042c0381d00103081c2c8482d911030760b8802990b03801d10100c3e0351070304e030401d150300d200c6544000c3c0c481c8042c150103044d0b001c2c20f001d6180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 889336133 1250 889334883 889335023
    0x706020a0201090b09091b0d05090c0a0806042a03170318030720010302070b0906010801050c03090a1e15060326120a0b0909010501060e0904030c 64
    0xa000884c942107445401020305a00703c980c0c0c450300c00300d900203181c1e0800204941c04100a01c800ca580d446814002c155080207800d000c030310201040340c0c403401d541040d0702c182c010100b8080060406001510043e4141e00414003070204501c0d80c3ea2000c0c0705500152040d441151643c104d5031003000114460b600040006445500081055642e0700640d440104002c4c1800f60840d282c1680340480115600149000761410b80d03d683e91302d044c0790707083e504140c103544002c0c014008540d0a000d041e9204185a604600f185003038040e00d503035102d41c03100c058070311100ba8516903190881c600440da01c41d500a17840400000da4100000000d01c0c09220a4820f42c5018803150348c01403500ca41d114411004050391401c0440000c0c1c0a00320640150155030100d80c1c07030ae4000140d44072400700c0b43c40b4140c2000000340030740c54540c02501056140501502c117680d031104100000c1e80010114103240c1d0043ca0300f1015801d092584000074080b01810001d00351484808500f118464440700015084100c40d19 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 889337383 1250 889336133 889336139
    0x4050d060e100204030302060a051807090b031903080112030c0b090a05012901120b0a0e101401050403080304150f0911060a091527170c090a0c0306080706020a020109 73
    0x1000300c4c0280d010040060300000081750600103a600045e411a22480325140840d415614040c0741c0708140c1e01c003940e190707112020b00c602c0703280911a086d800e0102d54503040a0300c02690340180b10300c0c4140600c140c64416403814805051059a444806991290103180a403d04944440d074031001e241c400c80d100d60910101c0b00e001262055103c0c7d91030140701283d281c512100e001503c600b4100c0b450034425641d6030003001e8496403559030b480028205001c9503d59418a5100030952a400350004d044102550080b03141d44e980c004110b9003141d0b0000ea074203460361030f980342480c0d070f00841d070b050380c1142810801d000d0754050031a80304c002c200748503010803007200c1c2542040c03050034040c1c64682c201050940780100191000c180340500c2c0c2061602e01518011950440c00107281020102c440d41480500c1c41440031002e01c80e240405007184d0401040640d130035100081c1000001402c0c0202c5541341d030580a18540260172060107801c444054540454540d0710080d5604c10280c01a030008091071800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 889338633 1250 889337383 889337413
    0xb041205120d05090c1818010207120c0308100b0f0306010e28061b03030e03120a020301140628021204080105040308010b030405030708071a0406091101020c0a03061104050d060e 78
    0x503000c0c0804a145a20a650f40441f80044c800350400c02040b9950204200c40c0000d440e500f040c00080519180d404079402641002400c410000f44a5014012629400c3c800b10b0001425100342c900080c1b1401e035280d0f200001220402c142d9000c5c142c00048000311641c04074808240341c0060000822901003140d0f4880d4112030403c00601c0c1c1c0450244c4410411001c64442d4110040000c1c50000b00c03440c040706442418960386c01216003240065001c40180007009149200103070104e07003102d29a0030a65075820b070303080c113005a00d0404a41c250919148149170300a001c2150424410503200c1c0e2110380d0f13184118068802103c08400240d6000008268070320b110080e2800345030040010341c20308105a442c40e40365401268251082001044200c401100050a240c4161301c100c101050b004018600401a10142421981550845043c00700c080d126501004101e90b0040e2022801c00e000301c589000d00e100c0c54103e2900200014080d505206250f0096a42014401c044a9102c0b8100e105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 889339883 1250 889338633 889338649
    0x28080f0d050105030d030903080c03091606080a0c1d0d0204110d0b0f122a0a08100b2209060f110408070f032a0506130302030c06040b041205120d05090c 67
    0x7c01408100c035000800e4500d0603120140d07501011032030403503d10200c1030040300b04402c06030b4040c800080e8000d0400c5440e420500070a100136031542400010003a950110706070f20402e01d03e82030300400c450342081083d541e85402c903460440070030218a5503003071408141c001809002100a01440003801d01a00d2814404222959008050040c008850701c02c40b070710184011020000d114216041004200c641e13401e90b980008110b0480100712005150f00d07603805442d0301d14a0180305040d65204c0803e800c000103070002e071040040350300140301c1d411440d0860080106540d07041d500361501890303103107207001300e402002590510002c88810980c2c60881c181c0300429404010488900287e040c0c00c95003c4203854152310700f000c05c241801d00d4541c0e008c1051038100c02d070a40918a00c9820400541c2014007d900986606a40c0ca0b071400782002e640000e90f1166100fa40303030440100c003c21043c0b140900c4803000c494054045540d541c442c4c44a000c0250005460740e0406000e021090030040c502194 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 889341133 1250 889339883 889339901
    0xf050d05100e1e2806020d0507080403020f011b030e030c06040c0503150915130b04032c0f0f061204080a0305010b0c062e080615010228080f0d050105030d03 69
    0x210b100c64841d03c0d403213411560621a01102c80540901c4a01c180000f42d0045901c500040c5ea900000781c81d19040003850040640708111040c2d14265140a051404108000c505a428100402e040d44126070151551151235801580c2c1e024075070a01c0200000c041c400022184210102c8a0300e090306000c0004600c42035845103402da101000c80c0d007940100c0c2c0a22075001d00c51b030030050b000050648440c0105201107500302d00050040d843c2400d00d882d100e251901026200d8102c1524007a040007180c030462480400714030444085096005030303603491085440642880d20048c0c128280351030311115036086070754454007280c246000840c4c0340081206642c41200c0a04c000c00d41c1c0e0302ca0301c8000700030294491005111212020025011741d2074900c800380148400001402c06150454507401400703503c414160454110640d860070116031380e80312100300741c1c441c450b064080b07401c0d10700b841191045078041400c0e01c00100e1050241c50f102d50104d81220000e80585d4544480d080c1d04400b00c03030a950b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 889342383 1250 889341133 889341163
    0x1e07090e18120c0a06050a022a061608010e090c03030403060204152609071a030a06050303040302010c030e0619030e1b0a0b03060f0613030c0f0f050d05100e1e 70
    0x2491113003c00c285d40c0207240c120882007401860250b250010024a107080703c0f800704040c00e00350421a400e002004003c0c1e100300328001c092029030300744800606501d010301c00c0540000c01040461a040001c0c000003600810040440766140c0c0d43e40b03811000303508188103424040b800c80ea81010200d0291050314448210513100c8083c3c08185c0580e009810800340c10900d162043c61004181119049202c400340480c0c02c0710140c40e8a40790362130138180c442941146000f07800900040006036000030801130220342c50700303244101240302e80c080765440c01041c14000106005c00351000c82160507500540c03030100503034161100c0b1000d195000c0d00d1030a401c2445608030584500c200143d0300f05070301854100c500200703003150a869030000140c02ea00303c5000c003103804440c10001c0042254200012000b000380b6003607400442d183c00d0302d5401074615440f600d07000d0b0711100040020070205209120428a03c10010404007000d0300c116991205c2070310505941c0c00c5c13480c6448410000000340121404159 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 889343633 1250 889342383 889342393
    0x2041b1e05030f061306050604171002070203032d19020f120a03020c01150b0322050c010f020c0306010b040603060b09061603140a030209010806091e07090e18120c 72
    0xd414000c941d0300e41740f0340162882e1b80e02004100c0e5a101c100400041c4805d4409651200b80d51211b00c0c10300000766256480148108250700050314044241e8600e04042c80071034034502c0099007540b002d40d0f0f034a281c007001e260b0006200d016000d04410003000d03450a03a4202d4841c554140920741d61003184083d80c05d80030308140246401544207030020310b0f582d11aa00081203440019581c4c0304041d00310341011042032004020007000c0c0500310300c025645c03034403e50745006526550725480c0c1c48400e15042181040214041050454003c00a0075182d51015046550795a901d0f8440c505580050041c0e400007418100000b9030f018214056a40003c030081c40c4070715040d04c0c52459003000c0d108540480500c044a01000b55141031031000d0050021680c0b009682d89000c40c0c001821204000e00881c170800315070050100030f800086294000d0840c05c078103283c180d03d44940580d00040d9682c080f01c9441c1c44034080002400c41241d025098003000c20440e01c40707501495031001c20303010b00240ca030040da02c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 889344883 1250 889343633 889343641
    0xf0f170406110d0510031205070804030b0604110a09030b06010c051f15030c0509100806040201030f1b020708120f16020a05151c0c0e010c02041b1e05030f 68
    0xc0c81d4402c0404201014605140151800340c00e0700381d8400312001d46183c01c40d200f0800900000c046503c120700500c3c40d009190144036030360300b10940558000500705100002c00115141c032181e000100040100c00201c1d1540080d500040122110b0b00080307030200321010119035107500642e4909030080d071040c0a040b13180f4182460a8034401440f0380080e206444180300443c100150500b000914020007200c030540f801c16050182e140f00c090420084030b241c0700720402403204007159403a0841d0342441d010482002c060300c500043c00000c07150007194458415800700301500098000129415902502d8914250202003110740c050b50042140c2d000b81080034080090101a0030140c441c4002c00030781e51183c4404c04641c081c8440c000340c1400040015000091340c0c4440301e101154141c1c1c6c0030a201d01c900c8030b4001041100094a9107041c00403100d810021555036400101111031840716101070340c007045400401c1d1700c030b0f6469000804141041c542007110301c660100c074411603124204903c2900c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 889346133 1250 889344883 889344893
    0x40b090105152203031806140a0807140c0c130b09042301060b0301090e010b030c040903030f020a050322170c0a05060c03010612090b01050d1e030f0f1704 68
    0x1c4001c051502e1541004400f2007002143c1c150b280c080c50283ea1054074440a185400001c5c105076040041400100412510b02e03200c44011900005403600d00b4800340d4a6421065413a51812101c1e2204124041823401014600268507a07658004031000000140b5030500380c1c0c205c41b414501f95800100d0000050042401c1b030000103c05010b040ba46100c041204000b9800c541c070039041040710710400801041400094041c15520100351002004850b840a000a59400c01410098001d40e01c070b40c030300320030b06001c0e42c8982c0e50304151400540d9510300785000145164411103000b112141008511040c0e004010021a045903020f6028400c4d24074480031410503420448818899208541c07941c400030b101840042d02450700000030644039410f2510240200e015000c04124251030100c403407010030843e203502030441da0145c40a0030480800c0c00c01c0140c1e46803910010040c2c0d85602c03841400c0650100541240d4443d542e100c0c1d00b81e1003408022a003640744507541008561080012601142c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 889347383 1250 889346133 889346137
    0x518102601030809120f19020108060f03060f0601051b0a050d1110110d020a020a020a1a030a020306010c1b050f120a141606090f060906050d0c0c06020f09040b09010515 74
    0xc0c82e50f00444811079406c08083e850144062120000640382810780c4045580104005d6003100041759041150150340d00880d9a40304010074084002401350049203050340582d0856012208044007841c25440c440d0200b6079450107071804480038400e040d84160154030656070609140416005842d449808002070b402500044140b9403441e103081002408410b042d100900183c40d85030090f00703020415004016054440707501c0100400145151050021030040484e80c0c000c441040040c1c482e00c1d09001268010348030300b8004c25800707650040b00e8500c02803109040072102d04a03548501d802404060001400412102d09a25845050407500040901a04a440305810411104000254510010040c1c02d552044012400c582000d000300d9801000d244040c00c0315042c038603419450900d004101e413182500401c1c0c1241d6806250421a100d014001040e9400c500103640300e0402c13001461495000800c0c591040c2d281004a0300242441621581200c90042c224443d409005400c20300715 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 889348633 1250 889347383 889347409
    0x15020403240f0f0c020708010519051f030507170325060b100909110702030606060a030204030614011e0e0604150b070b04050709050103120518102601030809 69
    0x41520b8019074071140030148601000d00c200032201181a5030b140708040c1c141082074000b0340040e4101400c1200c01c03041241e0075076008452140010b50741e038602c0c0d204035403151040c009010101d40100c00100384500043c83d0310648039540304001c3c28030352003094650f43e88681c5c602442081c0941da80550200c044040040b1064003840012441e000c10348001604800c108141101040356000f081c440228140310302d0b41c5940c05030028610b4081184c0002c0d50301c0c0790041c803440c03250100285094540780304e501610f00841d4001c1e41400b5000c102000c04002440900079068070651484011016210048404049940a49003665141c03155010312014000c440e542d0701d0440b40c0c0a10010741ba007c0751004000c004d00851841d1814245031a05e6400c084081d80700c24802804e00c001840404c0d80084030b401c0350f1440f03051150342c03103035600390341c90f2105a10382000c1d610030180780b8070703000507338124041010504c01300303d0070715030080344e4800d07640044020b020240c10400706026000c07050500c0340c41c080c0c030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 889349883 1250 889348633 889348703
    0x61003020102060a110c0f03030901060b03390a0903020f01020607090b130e04050606180405060c03040303230103060606090b041a0910030b10080f070807030b060c010915020403 78
    0x360651b0003102078604030510101c03460b0340d0300000410440034030071321540b03001c0c11460300e4851860030300080611010340c04a0713a524180d1003420131482011183c42c0c0c0b07488000c2980d151141c4800c1c0020014000d00281c0c80184d02030751942000038201e41c40490114440c21141d2a45200b441c00c20390aa01d0350740000f06400d081a803013001c0070403a558040c00780c511035840b8100030082da117842d20500100811005d4040304100590040c0000034502103a0303150702802940005449130390b5424200e02608091101c400f92201c1415024807040071903c055058902641040c00659900c2504607a80c01251181544569041c4004e006c3e80c1400c102050b00c3c3c40741c0c0402107003005401030000e1115084070300d000c1c000c65a540041000d5003170100c0b01c814020420308091603103141c9501c0c40401c1100040006040100c400001510107019038000032990030003500c1c1da44c648401da65441e000f0205000251448040b6800f04034000c0c065000300c5007502d0313008900c01450044d20a0030a40b14545071a6031304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 889351133 1250 889349883 889349887
    0x81302031603050325200406090c02030a032913200c070501050708030f1e1302011b020105073917010b09010b07020a0504021209061003020102060a11 66
    0xc1c0180000c50490069400b820103141d0714141a101c400c0320b440824a903401701095024082c002c00c400814a02c107400072943d200001c1c80b400c0000800503d2584c00c0702562034541880800b090303600101404100145448c01c011100e507500e80e54001211450004002d0002980080d2040c03c1c002c0c110648200144000300d5054481c074608464154091a0030811100200b050400030a041048600511080c2051440c10050f40c0720509a0310004200403020504580032403150f658401300c000c003d0b845450704c0003240c10001800300038088040780c00e0b400164000404810080030708010356946074161105482d109459541406011285401074000a00c8148041035614283c5201c0c100c0803806d40700e0700d10300b420f007911840b00304a50002401c1503890131040fa441034a41101c128103441c2c183c00c4090310341206100180c01034049410003a080b90012418901d5455041400c502581c1107a0980c0c11035501c00541484200e1184030207801603101102280d0300d030641c0c0d40030100c002e0b426a0340e14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 889352383 1250 889351133 889351153
    0xc050102070203011b08160504060c0f020d050d0e04140703090302070f0b09120105060904080c0c06040f030b010501050c12130308161509050307171b01141608130203 73
    0x24212026040d01c08010009000c1c000a05c0e81e010b00e07400d07400104410042290109031100030498041c03800341c98140b010600d010780c1488044d200c80c4100035030041c40d6041e800490300d800c1d900d50900e8446000801d025501002d800e18043c05000c000d40030300e88006a0503951a00308402500485005030b00358001d105c400f040b103108c1006084050041c0e1108940e84080b6103060180120100d0203401559261006001095a554105541042d00044c01d6034498503002910303810a540c5007882c0e43d00c003074000b4000a0322650715844008890080031890b00980e600c0c001941c0e14481c0700651500ca4000c24000030318408150040c4c4503d10350114001007185d00d0b075032015001d0f40104001480b41d64043c400108016503131403040b03031a5202d003c09112101190b07907515568022070383c004082c0750a04195112080006080d203601d034000c540c0074440c1039500c8066034002c00f4041c0303c6000c400d02800010300c036004086001c0302c0b1941e581d40c1d420525610002800040e024104d400c81e81402849032072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 889353633 1250 889352383 889352389
    0x150f030d1d061209210313020d03031b02010e160e010605031023040f0608150a0e0d0c0302010b040504170307020703120f020f060c0714010f15060e011d010c0501020702 74
    0x1980c41213007580002c2640708001c070310000d40743d4006540d17140481810020020306810741541e0110040e030546d00d50550510600d001da015100c659040c1140c0520b0402c01410305c0e034150407184007240302605a410b548606020b040c0446428010822819042d0004102e10f81c071420055912a01c2c00604220550b15140c000e0040c04564030b06a0b203899038000680c240e0302d411700c64044103181c1900301700181c500d0b05a0a5480d807402c0110018400e40c02000504a00680e4026060188078a41914148980703c00080d003214540c0c1c2083d4010361810014042c9400c0c103108041c0203c1c1c002050740d480e08030480071044154001066801140107120000001642c107095002c01001c0c1900c91700c10400b40840002d01e002e88109075a00260312000c01c0c03003c81000482103c0489400141d0000444507000d00180900848100b104c4140d14140e2a801040202081003050310010341e200c2e2541c416910044075001d4011600150000c0210b10204030303076028080425402d40f187c0009070400d2115000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 889354883 1250 889353633 889353667
    0x51002011404081c0e06150d020d0b1b09090103080a120920030a02060d09140a0b1506030601090b030a2013210b041103010203150f030d1d06 62
    0x842d5101004664064200600100503540b503041c2d034410400003010050190b036880001c0c1c0340c09087c04544080312000c5d101c0c10b51106032150040e140c201041c0d114900302000304811188080b0303099920800100c2c0700c0c145802c4810203413005102d550140d08580741d00c01c05501c1044610f0521900300d10f071600024030b078052090740f10b0041c0030007600190311242100d00340341d102c05400c1c481e401c203542d08001aa906400d80343c040a5100c070024180c102803601c0c001242c4d4100e0001c0c202c0c0318500704c84e01000720311510356203c0c840c00e43d106480422442c091010902082d210740e800b0660340d441c03d000e5600800e02440c0c1c040720715500410140e00c4481e84043d4062060124407240c038000581c415402e40140c403c0c8000d11400034203c2c100a03c1241c0500c0100c190000205001e00b503401107418084504807407002610000d000719502d0900002488014041584a42c064132403030304a60030710314011403a00742c4510b660b00c0308154012048a1540b600c1c1c0c14452207680208140486801003c071420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 889356133 1250 889354883 889354891
    0x8071110050610051218031e0a020106120224040b180906010531090e010f0b060c1005060d1406010812070f0201050309011e14010e0f010510020114 65
    0x1c1c10308000d01400300c00041542d200c0700303000c0c041120002100e11000da003944100d468403507000c0001e5420603075055103d1040e8841135500040f420521400c4440c006100f01581a0000c00c00c40b55150820401d6241e0180e02960003045403d1030b90428119902c0791244074130344240d6511b0207031035502c0c020070742d000841c411000c001400502d104c94100000da0540010702401c1141c100342d800030440188407000390f403044415110501c80e1040c3c1d00c0c07490340c0343e01612400005200c010503483c1c080780200500e02400205034144803e071100c509040d81126120070304071024007039140d1010383c504080e000203400c1e55080781407901d1000c0411100d956120418010380040e000d01e5241505039846c268081424414520b001c20101001903110307034400c4103403542820003c3d200e80e0340c1c1d00080e004010020a8108001c04090b07900f900740100d5021008508050105000b50b03601d5400c002c1d00c2c004110340414a20254000520092400d119120b0b12620144000f06440034000320580324640162 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 889357383 1250 889356133 889356163
    0xc0901030e060c0d1d0c0105070f06180b1303080a0903090e0703020307020f011a010e04150801060503070e2217040303020c01030605030c030c101103040308070311031306080711 78
    0x86240307104404c1c1ea02a00c0c800c4031320583c4031300d00301080007052078031120382801541c14000000f4071201044004000b1403a4250010f108011400c1c0e8003032090044203403658121042251343e00000c08055100d400d0342c12403501039031001b4003941c0f4101d0540040281160035810301c10380500004101c0c1941d03888603c00d104541d03000d80c50f81407580e0082d140c0b03050040038804e02d0b410201c4031010b000504901c8075560100340303001c44540d00d415010a000301900c1c400c6140038142240b0209145405400c20002c58074181e0449418640d01e12500310759620030380e03403030400824100c0710b09208000054203042c081c0c020540c150107540f8902e0102c04a5005500171800342c0c0154001860fa0341e010301c5001c00910054010780111801c400000f41c4480500342c51a105900351085410340501c20244a0510b00650b8100c03a6150b85030b06060b0680d4001010450000342c0c41890324025800100c01c0d1801c940a8001c5900c086042c19070a50340040010300c3e440c1008411a5244682d6108100c2500544200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 889358633 1250 889357383 889357387
    0x50a0902010216120204021c0504050a0203061609090507361401020a33090b06150706050c091807110d20010b0301020c030307080604140c0901030e060c 67
    0x151001908100b2040c0c3e51a42030403441c041003104c8900d200b9100c4256a04403401a81c0e140b032003098420f1900079080d0700705d14030718000400c4100000040d44016480c000c5080795455614001c0301c940c4803440d003a00b0400030f548080108052291038104641242c60b85c1884e5106000440b1652114403103400d4086250301d455420360700790441c1c0e008580c06844140710240c2100083d0001030350b21b00414034000d1544c243c42110f18100d0502d00d20341e110902401c60109481e07107602c11100007804245d0016500f8407a000007050303d52806d08000341450061048686c103005803902c60900030440140260401300301004540c1c0540c3c0c842c0170040d00314440e62a03c40450a0610000380646c001c01450081d0344d0104111480c82c3d9086640804074110410030700d01d00040c40c0041c40d014212401816802d07600103e510344c0c0748000800910b22890b00f5039541001a0381d040304200035207081141d030010103026000862401c007881e030000e0600001c10f0401141031a03080b02058501001115140c1003a000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 889359883 1250 889358633 889358651
    0xa0c08210a0509010b010e090403170106030f2421021507140c06091c020a090b010206100303080a0c050c2a06120f1009060f030309080d0e09060a0801050a 68
    0x814440d041c0c03c01000b00082044031080300010780707003459043c0c000c0c3c45000858009030800d0f10403c804100e0b500d00c6100a201941c1d1500d0182c0503003172104000480d203050a4002d101c1e80301304407060f030500c40c224030b980094519150005681b90b00780070707168018400d4000d05401503201c2d240a18854104101141e545030001e0419000c0401a4001c90005404c00440d40800c1c0d030701c0e9030948209243c1182c180034074440300d940580b521441414000c1d040f40c00d0030740018801c0080d5200c040500000c1e001d071481a039562822001031881400000d01090050000c980740f03001c81c1c2d101400a21841c1411032810403000001894a00102030703802da030b0940c1100c0c2e1072090b50700000340309200d1419904607007404207803050718103006001000380960075216000140c0741c802c80039506008000120081144648138103074111346041070b002c00e4010030f81c00080001c002000050b1a204030a40d030399011307040c02000c01000500740f4040c083c984c0c072504101002c121040c081c8a02da00800c01e0a10010f00300c80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 889361133 1250 889359883 889359901
    0x7050d14060c1b150c0a02211305031609151706040c12020f300d0e09011508060f03010f0218090c250b0403020d140306060a0c0821 58
    0x1d41143c3c00c05035030880101001d01122107490107400c2840071780326070385800302580120321340f40b00709000e56170318440303110401005280c41000702130b040792014203054102e8603501815541c0d0940c4550601141c0a90000c000c0c22584dd405149001100c04078540b00e07965900c98400711000612a021303d030740000301888100700210304408014a10400e00700940a201d400140300016210003050007070046920202040361005a10042c45094003038480043e64a00141d40d41c5903014050640841d4140e070f44581246001040541242d4060f0010b081850003140d0031a500c1d80c01034601c43e04030050b0b025204d446d40c1c080c052240c9901c3c00d01e0700184c0303d5100101c450300c0d030454150b42c24044c0200e81c09120140328030300201c6040d03141911000c180f9401031809104030700b41c02500502100c20342c400340300c01c041d808510540c100b81523a680c01e915000303a5407134481c3d512040d00d40740d510a0081008036036590286003000001da0044020a0030f0110300e261020903440360b03c0c1c590201003241c2e020041c40358 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 889362383 1250 889361133 889361167
    0x1c1119050a062c030c0610050d0605060d0c033f0c1407090b040501090e0a03080c0f1308011506021b041104060203031803030606030a020f1b240907050d14060c 70
    0x1f00304d05101c0e01040703142c0800f02d403c0d01ca0300d0802814031a01c4100040c00c684409440d24425940865a000190341d281084c003101981c2190980c100031006941c4d00e03911078038008c960032031408d10750032100301a45440140d9100c208035404440088011b444000810000d2140c0c0e8000c0c8440c1c1c6000c81c8140381e2008002c104c4005030049195940742940100c034802c80064000001649400d040b105030b1590f510420550240000000d000d950000ea05a00840003280300300454108030700070b02211100440b07407200c031420707030007898010382c020503400443c0c0300d403c90f00452503500a0800a07094030700030342d04185940305130800e00141c0d00010900c4050100780184074175481c0300038041d50860408030005407461201a02403051303a500031480e240d540746150200d840c141c5080030301d00303212500302d01c034142c803141c0c004159440ca11860451440c03040b080c0410368070441e16003016141407400c003410081020038402c0250342d50078861080d0306151324104070080c0609456840b040c1c136403140144940b102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 889363633 1250 889362383 889362391
    0x2220b060304050304031103100609020d140615031801060e010510050301080d050702010e060a0909061406120907030212030316030612060b031c1119050a062c030c06 73
    0x504030400411012810210a55041d00d40c41f104420a003652080000d01e0036000c80100c0d04c88a180410000d400c01c00c0c1e40c02414648001c0c0390511500c1c11000300d0308140002215000c2c0c10585400b0056200459a8001d5510104050710781d00311450070825282103a2068000304091069000180700c01d14105001006506151410514541c103140c6210345031495402c0d440c1c244040460f07548116070213407821002c241c0000c0c0040383c50f003854910080c0311000500c1100c9001c0e14042010450000360718001d018802e0140800b46020b030a28044190160300030200c450074011101e0100041c1d880c100030b040d0b04180000119140d05003001405c0110640b024024181858030700d0400c24294504803040c0d403180c2240001890b02c41c01c1000c2401e01c129292815521030340500610304043d08428a07080f8007801108441248080d804c46203000e083c1164041e0140e80305003484800a44180c01c88681c52510b2103c08100c05214551401d00d5462060301c1070464001054600c00d50104000751940 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 889364883 1250 889363633 889363639
    0x909060b03060310090c090504150c050a1805060a0c06020f0c0304030b0603030412150f02030a02040609050406060c02190513020d05060103060b090d170301060908060912030f07020a02220b 83
    0x4981c800f0350b40c0e101e1b02c101078862090301546410000b82482010800308588c4035140d4010b102c002e003098001880727540314007942004100704680030365511107258488403d407000540b80c5444d1000307001c400d54202c44100c0048441390303000c11549803211060006491100b007901c00550305c079800c0d880c0003106450001c180c0c50003584244800c00c03004801e01540d42082d508510b0904280003900c03107801c05003990440410085000006104005030294028030868806640c1c1342019a202e604000c10768181c1c0c0305d0b200001b01e5903c04400035250090480700250244100d00f40b601e981d03800418503083c900c03105050044e5021a00e4104c1d0300c614020103611000919080186a060590b103071080c0c02003542190180c0c414002040400141c920700a0120001c000016181c1d039440300f00038008000c03406003035414011100403030020030303000072500140282a2081401c65844901e1a045200010304007421442810b00c45000341e191801512030a100d20341e401b00202301320f0142344003961600155140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 889366133 1250 889364883 889364891
    0xf0c0f010e0d0c0b01140f09011509120c1a1605010603020906030a240b0301050c2d07201315080c0102030f0a03090506010e090105010b040320010909060b03060310 72
    0x3000013078540d054694001c00d4100400ba10000b1130f448143c05044283c002410f038001240c105441d4010b00c030203000c20381c2d5100c021502e454403080c1402180200901ca1440c2c65410300c074081070780c1c002101000c2d0311b15880b410541084494030141c1d05040c1d0554259558020a00660402256061f4441803e03030003004121060b83c1c0d688403c110072240c001301207401048100c0d0b0303c8042c4d04044079410000700244600c1c107000707000341410f0303201908140700450001140c0200c00d01074100001c110300080710143c104144c68490742503041009102c1c00101c0700b128004440780c1c1d10764103500722100e0306050025070040c481d640c007508541d040d0003801556002d0503410700076a900204031884000f440b90625240c15200000354080c0819800c014418000d9500215180001481c2c452107185510b0007407025990f1101010079903c0f86010282440c2c20b682d0758492460460004402012418501a11019170744c003298012100c05400840002000100380b152a103420407070501c0c6421003000400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 889367383 1250 889366133 889366157
    0x2040f05121b12030a020f060609040512070f060c0c050c011107062717070f0e0103030c031e05090306010b130e0a0e0a030e090f040b0c0f0c0f010e0d 66
    0x190382e070488040b204550b016901d0008810307072a010419a00107940000b203d8444000480c06911490901ca0090081c429240020704c640381460125020756001006401e07039080c040000c0d01554090403054616610800c9800c00180c2036218044034040b285da207054428403146001810001d0710380b4054100422440d0f40f6902400c08115076003190345a0074080c811030122402c05030503246400e1080026244000000b41a80e04040c1c545030000048082c0c0300e4075074864509001c161101c1c002c46d65a01d82c241c00503c00a4002d20340c0c10700700340c064200145000d22070b40c007607826402d402110100186012504400900301004080e0141508403103060501c094141e2070400220144100e81c003848407000403d0002d019513201c1c50681203a1019100070000d1824040d101c100d42c040c078075014001d07136400030b100460151100c5000b15031161490055445548001d0318580012030716000e41c207410090003401100c1040000300460b84200080340240301440341a003082c50340c0c40703000c0c10f03c50403101c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 889368633 1250 889367383 889367419
    0xc03030301060f120e2508062a040323100608030d0c0206190c11030301090605100206090c1002120c010912081306180f060501080706021615020c090a02040f05 70
    0x1b503806480b503088501e6a0500b40e45000d180e0505900ca41c05500601e000d00100c0860100059034555500540c10004844101c24032624480c910000d003921095540c8010400402140b065907107047c502209c0800001a04030300c212805544002071945c07000800d80044141c40c040e50203400d055002405040c6482d030452015854084070704254150381b0285c00d0640c500810f070301102d0504100440b92203603110100d00300185600d005e0b2510640014880c21582d42c0700140a0307100d90b114a01401c62450120140011840010601d00c298090300b407001c400203081101401000c4c0c0c4520010900003050700b003e1000f00461031a0500304803525041011151490011a200030303848840001c4e00707080904094803000c80000c000707004011f62800c0000f801900d0b041503040c0c90000080e50310580c0d9400c420b07a90703410b08880002c41800b00f0042004145a941c0e00080d4169490050350300d80c103031900005240c0c2070105c88003005107902040a200288002240c0d002500007030f945a11404074070010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 889369883 1250 889368633 889368643
    0x41407030c0306230105070b07020a0204142806050d0503030613090b01031203060f030305070b0f15060304024902010801090e0f0f030901120b150307020c03030301060f120e 76
    0x41003001409070184e0b04281e48036000311860b084c0c000f500e100d120704100b00000c0d01d484030781c0c1003030f44600e09007098020401544144140140900c0e4000b14920666100702801500082d00b203869440c0e580320002107544440c8000c1c00d60a00c12005155a89071540c10000d1ba50b0813080d081c0f4086140c16503240018111424482c103494210101d5000701c10403e404070080d2555400001c0301038001e000010405411201400742c0e42d20405c0c5c02c42a90361550080540150222a03454424180c0e95240c406400d04a004603000350018000b90011a264000801c4c054031401d81034aa420000e10341d1850700e511072042a032901012030400c00050f4090300002c10a9406014404c002e40d5100a42074040c03c1c00c20003441058485005e903446001c4240650388c036500314448441c08030b1400369804031004401e108035920000b00501c1c0742d00100c80c041d0b0390102508020024019403040121000265504001a500034005580c413444041142c600003050100080381d500003260070414071000c104008a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 889371133 1250 889369883 889369919
    0x50603010303140d0c0c0b150603012907030905030d020105070f0e1f09060e040e0a0b061801231012202d1804020711041407030c0306 59
    0x760400042850310b640f0b000d18030130031840030b10041c5440c00c411180c0350004407450201d8007600d0001e2a540d01c0c00501028100c1c500c0c0c0040e8425070400c018000820315600b42240c1524410200031407050380c02800f46194440201900411f0f03c0700420001450100001c0b08011503520090205007400c5d8005040081480241d500307003e422000035240d03845802c8020300d000042940302c0e424400010340901241000d0044c480007035101000309440b800d0500a0b8444501480d0085c000300000c6e0b200c07040023000281003c0c0d031169100062400c055200c00c54503001e0003905201c080402e40100781a0349644440d0034040c0100c556928104c0c000d5046084100011000a00071844640c182c00250003003402e01c40c01c5000301ca020400c044007803503500380740700b01c01a105d07500040003600000c110388500038603c6204178020900500e89644c1800d801401c1264464034030161403580d8240040d064a22091880c1c03a805030b0340c000c00214960501512100c0406400d08001c0030341859019000310311029 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 889372383 1250 889371133 889371137
    0x308040b1924050312031b0909150a0509041a0403030b1c020f030c0303220f0b0304111906050702132301050102012a090503010e0705090c0301050603010303 69
    0x40000307000d90072070120290010903a2801001105105400048803400720b940a00c0000400000032486050011380c4035036000203611001e09503a03031644107030031030010007007800348692082c40340c0b85c60b603201c00341610b000300b107569900c00d0102054401d0000d099190380c07241c0e03c01c0c0d903100140804590003103541001010200e403520451303900c0d4142507001c2c1c452800415000f000b48844003038000a00c100071101e091081703510382d1404404004160351081c0c54a407803541604100000d11400c0410302101c18106010800203400966903059002c0c40b003010361141403002c4000040108001c2600c60f101c1d00c4139011078404411883d5a80c001001e14006c1c000c82e01071110010340f11080d5030703c9506c031600e030b4110b0040c1803200041d44030310b0b45411912001003607420240f1100116441d801805517034030408190641020004282048000c1043c00401d4002405081c040100e10360f01c0070f006048007075403030308000c0c0f80452906090100740c0000415070f038107010040c001440559143d90440341142c4d098 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 889373633 1250 889372383 889372403
    0x3200f191505070501200f0a090f060507030215041211010b1e0306070201020c030a081905091e01150e0403180e0103020f040903020a080c0f01020c1608030403030804 73
    0x180094492003030032600005210441d0310540d00c07140d80e0007401040050f1088009020100b00d41c0c03800c5070007001074140301741014410302440301c00040b09805415840d0303403880d00420040d59031042450408540d0031000000381e00041940c00c1c150100301071b4280d007500540000444c034140d04d8100c44406031b0b1341003404019030a0ba0784014054250000000307001c00030000103003803812003241d0038040c01c0005218000e00601000400241c018800d5440c1202c00c5c030003075031520403134000840c3c500074020000c0d00c0303002c4203900340c046c5801c161042c0e92017071608800602d5449010581c103542000b400c0d40d0104a41c1c140140080d200c41d0100b04031080380d110341040340d0142c4440c40d082e12800114209541000c138602d400240b0980c0c00c9a80034100ca00980e11011203150341c0c4284010350301b1102c809400b5900c5051041c0014201000400e42501d0110a49240d120b82d000c242c0d01f66808054040c085512003214a540c02880b4000c40d070007003801100861900f850340e41c000d0400f510043c00a032107100f00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 889374883 1250 889373633 889373659
    0xd02060f072a020f03030f03041112030a09140a0f0b03090f0a0b0a05180318031f1407030c0f0804061e020a09050307050102100e0a0c06050403200f 65
    0x42c03410200001c001d680303024032480c084124229140321031005902c0b85442d00e030030b4400360902008444551120900e4145181d58948030204c444860803c16500300203122481000280e041c03014180c0c000081c0d4032a08590301d0300c05032040085508244500c54030064500b044404440907002e022140c1d0301d000242c4940d91036558504061080c1e002000602449481c00104031184180520031203040030101b007143c0356400a1003a03140e4407140d0a44c1503100300280c4140070005174001c0e1a030301005080301d00c4038031100b18098008911105040402e03464000046460700c0c003402a43d8020b0342460304011020034050010b141080d003201e43d01c18411000f02140c144011034104042c0f21180d07140100080148004400095203c012400005500380030042028070300420480708468059001301200c01036910410020150074941e450b0724801e03c01d200001500034500d81004002c00d84443c1d848500c0e500304079200c4403248c0240c40c0000507072414000315a540900000c500c04017070b504003c034409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 889376133 1250 889374883 889374887
    0x3090c041d0303181516080603101109010e15070f031b080309010e0a050601180209030109080306090a020427020c01050108060a0c0503010810150902120a0e0d02060f07 74
    0xe02140c0720300c5180000010000781a00d0300001c2104d012091044a00390b26a445c000680038000ba10710a140c02c003074500b980301c1d003885030440b560000b000400740d49061000d1059181110310078212088110b20210f101c00b519a042001c070a100310003540c2102e0200d0240c91510018413964000400c41c0c00c2c0c13020400c040c548582054010700000c0411071851264500b4610000d03082251002d04941c02c013164100202c2d400b0825000e525403000c014a0243d0800b070001d002c240b091489021110760a2040107465902400740e0707003a1030b014014460b5a414103005000e0840002010118880d00401c010000240b01038042c40114041408850b41c1000c00f11000c00070b48150b0340c184500c0d60030500003042215010944a010303401d0320f103040020b070003107144c2a207943c0801d21034241290801c2121510f00c250704c1d041038225520660301544050f44900e07200301260080c00e002c03036481e104041003100e02ca01e83d21400401d4200b003402014000348004009580f6400280b030180400f5411010450441c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 889377383 1250 889376133 889376171
    0x6081902060304031b0602030609090a0c03080f071b03020f060414101b05011e060e0114030106150f12021c1e0c0203070255030317010b03090c04 64
    0x841071805c5c402103030440d06081020303401c25995103104180c0c1d040807880f1980e00103007082c10326600c02d81c0036866600d9612008016003180b21003160004c410040d0031700184441007860b10a840010050700b455045005000c4540c412884450142d4410041408400c50042100d03003000c00440307191075840b6411104075004d40c0780c6440500d07203c190820f002d04101d0190007c4038a030711301400c0c525281c4503504242090b0b501c0751141c9161800d50400500801c0f41a05404054440c00340001c10740320382d2030300700107021106050340b01d0008480d514144542c6030304c194610100b03580d0802c1582818014084a81d809000791034400d0515030313583d401110f45800800d25962002a00303020450302d14400c00103501ca602289040f40715000090b03111220318240c100396900440c6000091310781510003c101012a144a61800801d82d804605000d01c8071820344007002a511039035400c044020710207904140400181c00541d000b0703c0610400c404c4110010b9001503292040301c01140e41e81400c85000030344 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 889378633 1250 889377383 889377407
    0x1707050109140102010902041e0b04020f0d090203070e0709080d0e180403030605130f050901140c030709211e02030322090204030b0f0108010509070501050c010b041d010608190206030403 82
    0x1150078155020009d0301000c1443c0c05103801c22009100c46042c050400081344100080540c00c098244400103044031a0703840441c070300c0c0c8050104c1b031f01c85031102c0c01318511003012110140000d0443c0806d202840c000d01400c003445200341802640a003a10000400b102c4010260003500c16900000600341840f0b03070490f40003088040c002c1286041120030030b0f0050504850a514a1801d000108100e59414170401c03400030200c00c040b03815503c0385d41e82c06d074150740080c00d04420408045004a138a0650590070003004c0c2c83d110303848940c41174a14004141984e14a8a07607909891089450056240482200e074030411144421600300c160498071011030511740c000c8a95248003080220070482d040e40400d000d40c0e000700f01041c117a0707a0f4030882820307a4000c50b41c0325901d130401c980c10042940514080c04180c240c400c008a0341c2c0803058040f60850300740c0d00d5020b8400c11380c44000f401001c000c0c46010090440300024205000d0f01c9029000f10b000c103104024001e450010000d07040c07510400c2c105580c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 889379883 1250 889378633 889378639
    0x60303170c04210204320108120a120c0201150b190810030c08061503030f301915051f230408010c0503130201080709170105011707050109140102010902 67
    0x4030100307140c000c0420303580c0207440d503d030881c072400704190380d1b03904050300c50403140c1e21401010b5040510560880a0300150040802d001e243d182001c180c5400e40140c80d5800c005900005001552022009e4074600591150b84020000c009c681d00d800180e40c00300030403180e6070a00003541d8a03105123981e002d601c0e552016050000c0c5039004102010b010071042d0241c0d002610850030311540904140c2c4074802c621a600c4208000c1180105503940e68031034064058403148003004802204c00a03d01c0d0031001c4801030f4461b4280380340100c6204551042d2190b40000c0100c5003200b0381090081076a8101401a000c10800144c108070251442071104100420b1510500f850300e01004c00203000741d422074081c1d0481c5500704121903203001e11a006891050340081549800740300c044c0c00540340102c0152410b42000b01444010552940c0d02d150511598100c9000040c19031404070080d038603c6400340c01080541010301e0400103607a000361742030255a1441070811035111401c0050b030050020f0000250 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 889381133 1250 889379883 889379891
    0x50c0d0905032a06070804061401080a02091027110c1e011b0c11030105011203030515060306090915070507020f04110d020d0e10060303170c04210204 66
    0x800c000c800b00c05024441d000e5280980c10411480c07081010200000c11060640c1c40080080d06480c403480c40c40c0d80060081100045908001d2640c241e4240260001d441691280c00c8407811400c01d079006642c0850440b070743ca45000d04010758040c2c50069032005903100400407410b00560b1101d684040b0b41c83c044198036903a80c0b00c002c280b203500c40790020238960101c41c3c1c032540a06212418001d030f9214400341022031040091b40941900c0c005801e41d01504c1c01280c1c1c05c8001c8d85520240b252030302074146041c0b10700950b9202d18000f001c1e110001d14400201140c01046042a02c444040d2034101100301d5540c0850f680700400c1360325041d034090b000790a03d07013184203222146030864018884603000744c1d03d5901001400c410300098032401201d0022131181080f04014402140d406445c10300e010100101c0e030809501e00d62441c0c1a1280c102c009501c0d9070341c10070410107400a6032080d410660248403002d510f0312081c5622107010307911a101c403d00b802c00303102100610442500c81e100d0350080c0200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 889382383 1250 889381133 889381151
    0x110915160b011e1809060221010f0801060302030606040c050706110406030f0b0a1a090301020f1b06070c030c06061508040605060402070c15031104030f0b0c03150103050c0d 76
    0x122808000b07104141c40740c9040250310b29942c0c1c1000044055030401c13201d0602003e40d40582c03200520702410143c03a03031542407001810764203045590032001a24440854034950401e0505114180c144c0d0086420380c1c9060300400c01a100441e500e44d11400c03c960020710204680c600351824810f245009001ca8a003c40001d0081d1f0301344082d00948115503020000c2c442c1ea502c03a00b044031900c1464903840751075918100300e4008070a80b00703102105040f2200d402d15001c00c01090980e0400003034040701c5c107000b140c4818440d01010156203240c40790002000303a410100000340011f807410502800704404c0e45614420300603140c00102c020621000070520032191050014424101950116503040c00c110106040d40790500982d000d4039000580710746420f04e01111a4a91030110194030203058030740d1040c0c1c2d140c00742c2e078000e080118000c001c83c8500060744d1900358070070807004101c010070b10400c0c001d00540700c0350749005206d511000c1c03c000507162035109154509000d80150a201d05082c81002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 889383633 1250 889382383 889382393
    0x40204110717181e091801020a050301050f0d020d0305090a180c0f0f05161a0c1801021204050402070f0b150f0604080d050a14070803040201020c0411091516 69
    0x20600304a074000a18201030100081105609594080580c1052180c00c011110700c0c00034103003900840801540c100700d201c6c0085603400d98100748201008968040010411414584486110804101e0700908c2a00130b079400580c1c0030003c024007900704140400d040318291202400c0001a003080d0b00d4045548940003465409040d0721024140080d803c3c01d10744510300c0c01005100c2c14000e00391605420f184170001683d0040c0b4008405031140c010251451030a022480142e17401007500c0a000c075a104000d201c16079101c14a01e0f130850444d072101d441200400d507a881606c0035160101c5000d0382d10312031420001c6001001107009045400c0200501c080b4894034400003020120948240e40c9202041c2d00308407203801540300c2c4030441c2e003015018914162048006007404009428000200200004402020b40050400b10360070706000041c4019036030100901c1c540641c088030280542c8086410043c04c50040342d04a90291101810740000329400c5c3c801c1e11001c00111540c01c0308541c4e18100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 889384883 1250 889383633 889383637
    0x21228090f1109012d091d070e09070b0c10240b160f020d051510090c0903080c0703020904080a0e1203070201140405100801170114040204110717 64
    0x11540408070300c00541d03060900d43c3ca0f00e8100c8081228800408559503600c050300c0350100310a40c1100c2c0d1612010031005010312411030851141c202d41c01f680c0d44554640c918000e526003041a4006640041226100000682c0c41c00e60340c000b94034a45500c0d1020340703180b4024020340642c003080e00740006110380741c1800410405101c16001c0207485d00c0c1e561410100c0c5032080000c034803089032203c60380201160b0a00c0340c042d4118405842d503c4814441d81300c05082071a03103e4036811601101047c01004050421404054031402e442002140880070f00035000e0302e0984002070445c4804500c200f0b0501d4180004001035802801d15200c47c50240741640c107030352003d040ca84c0401c0100b4908184c6040c030221740c041c401c10040003513141000d0b41d001980c500183e10000d892100c400c20002c01d43d42c507015055580340f07407a030321050b00ca0350400724078a2240701403a80c01c2150380c2c5440001d21840402c003001d290420740507075000031450490080c0782050301c030b5004044c0c0510682d4110490b82c500e0600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 889386133 1250 889384883 889384913
    0x8040512282f0f22051b070b040201081006020a0311070b040b0d0e07060914040b06120702060603061e060f0a08100501061404090b041e0c020c0402122809 68
    0x7644485900000b42001034410443c80e004c034001c07036050f107807000400540c0d0000d07800c207001d1038910004a00f914145280b95100c0001119a101907005010455800c03140d05a000414440c01006441c10a04001d6880c44c0100c4040c08019450345c0d009038042c010703c0002e01501e9100882c6030345644490b150307001c5522200d00341091034034118440205c02c101003143c4007078440942e911070302589806202807203004284446c592184d9103c20311541952080001c0c6052111650460000e151411010382000801031599000b9000074080040c00340904601c003502c51403c1401351042c2d1100b0003c81c0c5100f0700315150540202c894480441c4196001402025041e8000c41c2440b50f685c94000c215216101101c000715016405d000511404501340c0060310ba00d00b019000181d40700c00440e00d254110305e440301c5802055984e09401402c7c0f541440140e801601c15039040d4070300058020010440880107018900e605040028901120f06240000355138802114003405111228180520000210350b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 889387383 1250 889386133 889386139
    0x2090a24030c150507140123040b090601032103060308030702010905060c0f0d0f1503080a12050c0301170f010f0203330613090908040512282f 63
    0x8400140c0326150030018000070101c0d0391145c1c107080e45644d5803500c131034605554132503c0d500d4407034078640400100610030b881c09601541507182d0400382403c103c072260103040456140c101e5001030003c9800c0926100000c0e035440900000d1940b1901d0490041425802c0140342c00d030000140702030f0070341c1500078114482c00341d81558580d0f2940300681c00341c3d100e0b80000c3c0002050510802260b1802a81305c801074030414000454032404003003c0100040301a0011181c452000c60500ba10b03e60010b0211840b0901440811480c2080000c02e003640c00140700c1c8442e8942c41c0b803c0e0010041d001c0c805203075002c41100003404074002100c80e40d8040c0d003040f2000035007856005031701803001260a041490313035001c7c0d842056442c201d04080c0f0015612a8001505c04c40c49900001140310491080024481c001c0c6002e503220381c180420404c84180200360407043d07512501a40c065009050b00b0411a03d1003112801c41c000e0107450680c1c10b880e007003002500d030030412030701d003001c20055140f00c541040022 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 889388489 1106 889387383 889387403
    0x240e0607030917160b0a020909070206070e0a031a07051309050a1119032a020105070807021c0e0a030c0821070f02090a2403 55
    0x540349580000d40e034004442c00c2c41490318200c44503c500c019038601e80110080f411040300b84822010301305040090100300c815006030b04448000801620309c00480c902003502a40303405027203c0c500c3c007041c0709103101d0605103000e60401c02a40c1c0e01013800310140320f020500e41d50075000217003c0e034140402040116032888486054000a00c5028400704080c9031060300041507803907010400c190000280224142d003481a00c0c488040302681c500018910103188a500740e00c00c45525000402e15409100c2b01060b40c1900000c2c803403011602e40c0a0252250b0764201e0391100b03000810303204c0c01500d80302c006440b84202c156041c440802040e49040d2502d81d11000100c501c294002011a802080c40304246814400002e41e5100c03616041c074104109034130f50440700c2c103008034002d1240400d58002055404280d0001501c90503100f0258013090340303000911440c1180c1e020035241071040e = true := by decide +kernel

theorem cover : BRFrame.Cov 889208633 889388489 := by
  have h0 := BRFrame.cov_init 889208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 889208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 889208633 ≤ n) (h2 : n < 889388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
