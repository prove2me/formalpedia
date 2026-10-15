-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4822
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:51:10.567174+00:00
-- url     : https://prove2.me/submissions/787711ee-4429-42ee-b1b5-72ec0437b49c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 867086330 ≤ n < 867266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 867087580 1250 867086330 867086347
    0x110a120315090204080c040c0507231b510703030e01050a050c1e07050f06101a03070503180d0908070905090705010507150207060605010e010f14 64
    0xa0181e07007020300380c0d040c6248070001d40c2a446034010001c03030b03131010161111303208031100304011034040d2910140400c0c41041010001201002c0d084040ea0b00608039821024415801c18900f013421411000c03c1d0100300c1300840b9a2400c142008411031091100b01802c0c001d280801d8201e1a24010641c89000610403400601c50100c044084803418030880c1c1e80c07200c1da0703420020041c000c40d0007581240e500c1e00d00070a06480c010b0160902c0b591049000501d00b015810030007014000780a9a84010041800714000248040c030442d214204e07410014422400e05c0311895017580d04650242e10782d0b40c4e000c80c4c0e12249006800950354055000d017031141c1c4999130007d4684081c100c554100450380201325001ca180e6801c13403803000a0300d0290046034002501d440071042282c8098034145a00d5001d00c9040015601c110010304007a40300b9a41c030400c0c8400f10790100c05036085102e084a034503440b000d060280303581c4000381c0c9070321010034a07115102085001c0054100381c0400318101e90003900003003c22 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 867088830 1250 867087580 867087587
    0x302150c010905390108060105070f0204151d1e0411030f161a0d09020112050901020a260f1807031a0c0403050309010e130213050907110a12 62
    0x1103060703002400d858802140d881401c1404d0041d5103444c294a6500c400c016054074071280150508006031280e84541c5c55407801502c458011100440b0f0550042900400684640c01010f0300318403800145070016003011140c030001240000c103000d03094034040c100510605210050003c41610344c005407003d8a803410481b400c3d80030f420303c0580510400e4a02d00c3c5152000071481403100080407104c0d201a22007180c080200c500361041d4804903000d10000d075100c480d0b6131142c446203105051101210050f400aa070542d00d003140c0616030b6035400300c2c48240301c5070003012604840e003510360110303a011501d0102c2c1010030f5001d030a8401000742100090000100541c81214084060040310303115552481d00003860b13072002e400c400e025034070000807a00503a2100161010360b5801005503040c881084c004407801c508008000ba88003035164800541e0b403c292008103440e864687c0003103950fa0522044c4008100060020b4040200c4d510702da8076086008150314016a510910703d1000100159084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 867090080 1250 867088830 867088841
    0x20f04020409020a0216080a0201120e1f02040f0f0b07120203040801090602030105040b0a060807030209011b142e0906090b01061e051207030b010210050903070c09060302150c01 78
    0x222105403000500c02840d9400146c489104c44124101d943c80f142c5400400b9202c1c140d130701d0300901048803010742140301101a0030940401c0086d1040300c01400c0301c0c000442c22426a41c42c03180005a0018007807129000b0160100003404c0740326800e0300c45d146410400c3c0018824000e0150a11264808643c600743c428012500100f0030000207100c902c3c11070902c01d00950080c810746100b05e14190040f481e03801d188031417000b21040c544940010f980d40300390940c0607601800030720f0704000c110101e440704c61081c61007240c06240179254500c0c014161449a41c41d1035404a075400d40c0c02c0701000c0d4840c50403c20001e203800520b00c0741000c903c60f060b40c58442c01400e1200c5004180b9850a000401c4003035100c031000c050a101c041250110703482e03500c010354442c81003d00040030420007400003551603002c0e4001180304d0a041c4100d03689040c4541c1080c003280e006641035055600700041c1d0400344001c070000785000c0c1010703403820016240b442d400940c6100b034602c0041c00900e400b00d54415221004c0d8401c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 867091330 1250 867090080 867090089
    0x602010c0e0d06090204050a0b120705010f0f0e061303050f0a02061c020d050a14010e062b061d010b03010e1009021c03022107021e040204082a010f0c020f040204 71
    0x71f00250404c4005180640301c04015140503040d88003071401d1021000400380121401a100c2c080382180b441811a5856181a500000e01c03250b03c200010706d407601001001503940084034106c4031801c510305142003402c50010705401d64450b100c901c000d43d03104070072164500419003100383d94100c1012540041c0c014800048569464081005032a411503000554451111802c0304644c3c2e803144826211071100360707809a00000d9204a42c3d100320f907466180b400010290301840d5118080755a510103540d0a01542460340060540c035054540c1c0900402130311308811802030003841940c43d44169a4000003141c0c0700c003d0385841900082d525140f518420400407466114003051050401968034500400c120500c00300a0709001c1d05003040c581070310005a40280682c01c000c05001706041c0c8004280350840e403155080000003040304041203115000c86c3e680b032658090845400000f02c0c4c0359060782c80d40e41806481c1c44071100107948640d140c0c56940c0e0403144210f482c09a20080f40c001c5c004e5410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 867092580 1250 867091330 867091339
    0x1410110f030301081b011b02060f07050a0507081c021c0513150f032c0f0d080f07091a1e0c0c040e0c061606140c0d05010602010c0e0d060902 62
    0xb0513680c0001c10403442c048240b0b582d80e1101a100f50044520b202e8a001c0803162206150344100185000e40040650b048507071221400d116054a0321402c2c500500411a40c690018004102d080020700142c034041a42c44640500d0003200d1001175211409031300c09807800c1c0d80740d610f040d81c0c813400340c001d85440002c00036079011030a84a83c0d41d4640320a1308459203010500580c000b11400b40300780a400424615031102400d035002100758902e21540c408030920f55030164124460341190204500b00707e00e90b0581c0c8014079400e03c44121050045e01410007020000e4024040c0140c0c0c00c117002400c00084140d9045d6540d0002071079030154502c0c0d40300e07007c03c00000007900e080c100200181204000c0b404903410070880c030f8258a00356451a050648039040300c81400304001002c20000c5507190580100b00200d0205508605520189001c035002c0c0f110400101d110050005140b1503103004d0002e40c0020841c82c0c12032800641b00500c8580c04500c94120b440040007081300c9034000341500c070340c042e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 867093830 1250 867092580 867092587
    0x1b030216170a12021e030402150d0204030c0e090604230303010b0c0105061906050708040b0c070312030501080c0f01020a050f0c040c0309111203040f0b0904061410110f03 75
    0x15803028142d0101036144001034140903065030186041c0b00310303551045845021202141003c00344220340e000140181d034407114852118080131841002010b2810702e002c80103945904524284842e0900d17038221540388942003007007060381c03500065076075002a04030140800c50b40510110304490f400b014003800d12404040000100840c04201819040c0a15002400710f5a20302c0144000a0441040d001d50b0001004080101c20300460080540c80d0054046900d465114429981c082c2c0c4140459003a9502c00d500400500840d00501c0000d0300340c902d030074071480d4540350030b20341c0d620141229280b1400c04025088004c0c1c1c000c1010001c0241c0c040c003510908881e00315941d403110825034890b4015400c14081400c800d2086c840c1130707a510761000301300c4c42460003002809440f002c01885041d10707200412007c2560788049501c0341c02041c0b680c05165071040c1040c00e00060741c2941d0b00800504201407861019950740c072441040c40d022514010b40f002206400c818604000440100702c0b500000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 867095080 1250 867093830 867093863
    0x6040932010510020a03020a0303051008030c100c0c080906092101051006141b07050904050a020118121401060f03051c090b04182903060a1b030216 65
    0x34406a04a403000c8503203424164001a041c0d80b29407004d60b0060060300581001c200280c0254800742d00002c00e400e211803a50307218100d40c3e1455000d190020440e51004016070302d100c0160048001d00b07503c52910030000c0c0015502d07101c09002d0700c1c08545c89103c01103095542512109940c082c40300d40130301d015000400e0140032500030b00d030a031581180c0d1064003c01040301d1707001d00c4081080d41f0f249a032440c030304800804202a8000f00581080c0c00b0b0142030f8000409507100c0c0d0713000e07000d0f5000710040c1010920303502c0090011391940654855030000004200705030040c0000c40350110340c008003002200c414100e0014014500394000d0206a01200300100034031100194607149000607600b06400320f2030740d07081901d16a51510860490200c2048248503110300c003c6240c1002e44c01c2c100120310003281200000181524550f070b81e203940410010403e0710f140802c103080d04035804d80c03402c00034141008400341040a80c10703a45c505050300091900304c40600e440030814420340104d0240d25641c0384 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 867096330 1250 867095080 867095171
    0x8030103060905071e171204060f09120f03030515190503060c1e0705030408070905071206030503091c0c080d08160206010e041505010f05040e0c060409 67
    0xc0c1c002c1a0b545205410010414010b80c901190803800440c8900758003518150164000191017450301d491401151140c0d1500104103000d4801380c00300392141540c501000304000c003c100c00c0c0d480f8045440c030764030410340418482070001104503010b01e40440e060741c965030103111421844d410300e40c0280d0070f603c0000c601c817400d03c0f451007900c2c400c505850301c60b2210100c80300c060103401e000004008080e090302d003084001000400c4003510400030b90381416521024241401c00c035a000008544d2241c04000e079490380070100c99609103140303804204407030440d19410b0b681c1c002d00d542e0764001c1130030310400320321039403007a482e80c0b405503000c0c40d01c2e480142c944800c9912900c0c4c12110001180040011900f41c54070703009000400c40c100d5004001c90380c6000865601410050410380715a8a01804690a21101d015031406801c0580c050342105151005000886464043c00c1e2040e40000b1741c05221541d0740411242101e5958a01180c100a0742502c1051a0203140c2c0600007a18001020f600f901756 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 867097580 1250 867096330 867096341
    0xe0a0e0c101d0f030705010e130501030b010f060f0f0810080102030c09090903070506160e0d050a0b090c0a05041d0a0b0906072a050f0f0307050c011107170102070803010306 76
    0x2191012042d0900d01030040c05800d10000365940c0d4150028003017406154071a4400c141d40c060002c0c103003203607101140ca031074088603005e800a41321034203a030006120000e01440e80e172000342594035004006c007907a00c4000700807018050301e1030b04201001d0003186080c0c5a1841070000741500341d000719901d080c2484007210b42d50113044214002c0b51030301c0c000351070341401106440c0350710740100107401c2540d01d8030302c9041c04442c1700a940e03040c0242800205100e031105066610300d50720550061036600200d0810a0794503800801e205120383c00303029285d45075142c5000d511300301c0e00c0503900800e040c050801c3c01000041c641c3d98081c0c81d40705100c00c000074000e02103c00ca008518240584050343c507090f0003101ea4051300c2030b0008081e009189032504080380550b40121043c02501600e4068940701c030a5404e01c3c5118151540700d900c045044410300c01c040c0714064500c0c409003000ba031740c0d108481089886902c184110908c1003100d003216145038801390121484542d01500240d525038403494848010030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 867098830 1250 867097580 867097607
    0x504020a050a0e0a0c0c03020319030f022d0313020f040f0e030d060b03070801061b0b07050706051f120312090c0914010e0105150f03250206010e0a0e0c10 68
    0xc0c2801c940e06080b0303014071b08640403103406a0103907152542d4040c034010451020591007007010303500d0404074411201480035020030b0b00c030304018000894200d10842c002d444408081a441c100070410302003904c4041d24a400350136810fa40300340c1308403036080c0000c0007047c501420550140c01c08000e0002400c0110041c050a0000ca40030400c10303445014003203060000311044000b0416020051000e10701a4000c0425040e0381941c01000040c6907450820b02e07841603501902249000c9040000c0180750300910340e001003007000c02844540c600c6041c0b0740079952403180c2ca5101d121001c00c40103040c85101908415030b640102405510300600d4056074035065403281c0f0903042d241c2101c0882c400802d00340740341242c41e007141c1820f169090000b0060074030b400701c80201d0682c40801010070305d9030514028512550384d6410300500501e10800204521110842c0c0d08115002480140302040d800c0e149650001d03641072001840b040c0c0038440915120301d048945502c0042c1c00c0310802e000782c0c40701c403595485 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 867100080 1250 867098830 867098851
    0x20c090f01170607090e0408090a0605030604061403070323120720030a0624030606080d050304031b0311030310150306060e060a1b06050406050606030405060a0504020a050a0e 77
    0x4404029000f6180c01e0259100f80000d11a10b00411001203505aa2a0410301801099242484501c001041c114031984850302260f40402040b1245c42c141c0715410061024020101e42c201c0d400f4000394a440391404002d00072848a0540c0d403142c00402c0355641001d1000d021281070b800000c1408042e03801c4084110741e050110a002c004000103124800c1c1c000001a0050415a02c01d942c1c1e00c1c0a0905072200c918a0910070f600b040c4100301200c24070004500904000680a080021540c00c1c21070714001607003481010818440003c1d842600800f0000740014600444036041c03408480d0411108140d891a2002100344804580000e4000c4c08407038000350000c1700d8102e425000e5090350000e10030880401e805601c0b0404500b0000c00401344580c081c5000d01940c1030070b50700703070f0300003605284155a415681c0b400c101c104007240c0325042d0010000c454035411450325554540e80c80000800400b00039445401150854076540c2240001d03000041c90200c1940d12050703002c40340f801c1203401d140d56 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 867101330 1250 867100080 867100109
    0x30d09081b030604030c0314131703190c05010902090406050702100c020d05132c010b090916210b011812031404030204020703030209010e1519020c090f01 68
    0xe500c41101c24100c2003001070043e00c0d4903038030307034900765628202000154144984101d130600c0d214091030003886640440c0b00744804903030504042c006100794000211855a2041220f214040f2003e54281400a010315104400040c5890300038050581e60000030341061001c010f21040000c1c1d50440c61107000c95600310b03020a480d08105030199107007129007030b0141e080f490f00710703108038400c00041131f020302086c0443d00300c659903221032511080380c003ca0808006070391558004190324800070368014003210004a040c200351100040c2c5482024060301c83c0984400312003c2c4803401210b500803032035085240084400f030b40101800c0a000c8a0340c4035400640429503405090360403400000641c0d1110000983c40030440d9030075122150b06250500c5000300921000006030382d140000c22505110795400742c4c85140e00000501009460580c0354031170b500070354034020b04d07100c0d41003500c00e0545035a030500c0e12900302900581c03c01e07101000c406e401c03225090821607a0010301011a0403a0544160f9005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 867102580 1250 867101330 867101353
    0x3050d0e1206010f0506070606120b04050d050301081906090507060806040e0303040803041e290f0412030b060403060f0e06061009030605041a0411040b030a050613030905030d0908 79
    0x102d4203424002c503218518160814449801c056014105540c4600c40014803181c803801c1c2c0c10400103513201c0895030740c4015000c0008105041c0000950a2450b0400506550525240c0c9440e032921081848429080180c00b0b000d104558200020311038101d01a9001e081c1c03070701801400074000700c82d018001e07810314003000001c600000450780308541144160b0b00359102e0342e44100e0059004100744617031290b00c803005030200e00f0500034090907020040282603441d9207025103010004005012041a0301280c0400020908000100390120703140e180000e4400c0065000400030b0049401c09005071b8a09a0028a4080141d00c80f00c088a1008101c1d8010703500c01c0c0401602c055218404400682201010800030b0200d400880c2c005d440707004840524044400c9014190004a405450246c07290f1a03200c41d604241c4205040007900350090308050f034103611940e9440002414403841090340c1441c1d40185407240724190003801d401020741d00702c0302500000410340b0302d05000d01106030061011449 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 867103830 1250 867102580 867102583
    0x6132a031d0309122802030c0d03020a06050c040f120b06040c14360a290c010b03030a020f060a0203190903021c11151e070903050d0e12 60
    0x6208520220056250040300b0042c04044c03038100a400d01d0b94843c090442c070f07200c566103090000c50708280c0c51110382c1d440b80b8010035181c8001a04514041c0040d00c00076404680c0c0070451400c410f400007000b00c1c0b6501c8100a0724400c1c1b140307500080310341007103160102e240000300c4400c5041c1ca014040c100034a469900412085078140708030000420700900d0b04a4a07101241d000c0d001629803000b0701000c02002034140941a8110002c405c46210502540c00c85441c080390410094200701c1070078521003c2c03150003d00580380392800131420f00700c003107079417502c03601c094101402c50400541036a032180d00103070000e540d6414204c442c1d4003a01514002038030204180c400e4903c510fa08000c1090f801c0504822480205444a010341c2107010311048510141e17546992110400025603c520440722005402d900b00413001001c651070403c4201400f100203081001c11742c640560341840358640e04d41715400d81d02c00f10301d44e0005003a401034180480003607800c1594843d0440e0182d5000171401011040035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 867105080 1250 867103830 867103871
    0x50405010b131a0c010213081e1f0626100203060d02060703050d1b0e01180e06180916060e0a06030c030e03040305030a2606132a03 58
    0x1030502800c03060040081c40e60b0400c0d03c03060098404041071a009216007031609990004040480090381c032203082000c1c91081150301c52007060402c1e40c84058000481e200e80380c1404114440da041012689100c503c5407551180000f0500c503e00844190050700ea041e0318940d02c500c500c200381c01400aa0b140580e000c1c0222403040c90020004120b402103a0300300036868114010a80406c50b0a1041c030a90364928445e185070ba1714081c90400c510000303000c00510004400c5006810004c2d403020500c80c00c807510044800391401258424016a144008036007402c800b028440750407084c10090212000000ca100d407420410041c6010a5603180c00d820b584036080d50304000e4001491b0101045010700c658000c084e041c1c0305240128200700412200c40c80d5402541056030036401c001402c482c134035000007030600b81c40d65088030f100044c00da0030051509440d000f40050700031619000e030b003503c4849546c48560f40e03a0080d0402210b1603016040003150030700760006040820320341614039400c103503007400a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 867106330 1250 867105080 867105097
    0x5010609080303010b130905070e04060617040f020d02150d14040b1b19050c0c01110a0303090302101802090604050c0a0c06060504050c0307080105040b0d031b02030610050405010b 79
    0x11440e69103401c800d00040d50198003c1e9100500017000400c47c0c407403a012391401118140e0311500502104c100300700464546510078400d111490204c040007001c903060496000c7e41106004024a1490011902e15403007030381c0096102c00d5081200d82c074a030012028021402025108101c0110080078084440d4002c1c0e9020704000752050000e003104500e800300e18041076a04000c1c0b420001c58405d070280301a405181e900c00310360080382480101d50b00304034100e0303526000d10f0320401481824241586410341e121002e030405407074404c0c80302814000c010964011103541c900f0070962901940d404054120044120720030a016000301d50546014041d6a0107480d511030118a000307001841030b1a0881601c2040300c2940c0c4402c800075559960b886198171031400018815500d281c4040b004084103416040b0784d10941c584441520590cc4486400300802d0745820400700c2a61080d0620100c0c041c0da107070095051041108018400303450308845011500151402d1201ea40ca0301580125401215003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 867107580 1250 867106330 867106333
    0x1050306011206050703061521020f0423090c1903051528080c0312071721070207060e01081e04080d1113061d09060a05041e0501060908 60
    0xb5840049010781d03209035040b102d9400c00085540d5520b199518103011400c5880100d114040c0e11072000b51032646040d0101e800d01c1c001c614191030008102d040d401280184032140d4506d0180c0a0921140040c0640406000b088207a15103040103448e6102e42c000301c071701c90815000000c00030350130f8080d02915018480d001510284100820b00f8401c010b45030b0540451404000790072010503131051101200540011000740007058850414180703040b40c50b11450801c00802c1001c0c1010030340240350304802900d4031202581d51040c0782c4014207d040c6c101820309284460909000002d40c000a07042c044981503201c140740750400701d005540c90082180c0c56605059407402848002548221003503000e4030458000341809202c4410008407040400200340d5504002928854110070008003001031403603280030114103080b10355000241c00740d0f030300d0240150381c400041126951070a2840f40a840f000d0b0007000100d9000c0c0305911451411074000c40024a008008101507108030201019200d0410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 867108830 1250 867107580 867107609
    0x17010f0f0b13050603010f0e010509070605040b071b05060c010e06010b040806040f02063f070f0c050316081809251e081b0301080c0f130203100e0105030601 69
    0x2c541c9026200042c03405600d55030302c07a000c0da501c2d8868411030611100040001940f40351106030b075072600f07019402c50414400103001c1004a80618812280c541e40c0c88500c0c2407500041d01c1c41d00f0500d02c901e411560780034401003401d1080140c1540f0181082c054041101d010b41d0741e456800748030b8030503401144019000b440005012a10030220348101e0340c800307851145000c0e0440114400d240c041c2c0e10f034000d101d960880c0c10700b04c070f041c420300e1544000303c0b03044002a508206a01402e00c1155681c44028064500790040900c03000344240d84040403121140c2d0800000c5182c10946503204001005000400401e00410b40c01e00d6224117202d644445d03415001c048403002009001c04101d800c9030308028080f41d000441d585000c05907802140caa0320307240514200030303980034a000f800f071903461500901407004004010b0000b8900b801d11000f130f00d172940a014540082070760110b03c10480380000380000140041402c141d01154110761520903d02203036600d4400305503c40a00f8840c40800389210b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 867110080 1250 867108830 867108859
    0x10b0406140c2b0206010b182106071112040b070f0c08010603121106040b060d080f030c0301030510090b0703020d020c07030b06041a060a051317010f0f0b 68
    0x3001103442000c1120b0783c10841003001440328583d41082040041c808150075803140c4c04105842c00351900651150906190041311f91100c20b07221419803107800c9640c1000544191610006d91402e8044243da2440c07420b900b0140207203c0015840f0f030240f1800e06c000001c0641c402c291015103500c0a500da180c000192230300740c9000da001a00f690b11028a110000f4410003d110f00d0006610580c0d4444440340c040201500d0794014017410025600201c0c04c02000405d150461135000c1d4045540c3c4130140c8203030a00d00d080b8002e130383e08540352003400414000540c1c0c009010318101c2c0d1050084601c2d095040b2542000d5408030403008040c2c5840f5804903035194080d8001d000c100c00d1541c0b00505101c40f4040c030318907100c9294015640503840e901440241e06280c000d001d4100b80c1a40b1100385440100041042481408002403c0000110700c8200c0d288040011400401d4103e81074031030880016141d60081451203241c10805182c40c042c10302c81c0d0010f004d80000810028910000249403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 867111330 1250 867110080 867110117
    0xc11070815091609330b030c0702030102070c1406070b0604050421030603030311160f0807020d030f18050906010f09080a11031615050a09030804081005010b0406 71
    0x380c00502c1600512102e040a0030143d05000d0041c03040760008a40e080101050100e000080c0c10041014540d0744040850640891148011603031800700f0143d030f998031224141054042c1d598000e5140d4000510300d402c0c0882d0032564010343e500c0100d107060800c10282004420701c80c4840042c0440065000200e103807070280d02080e0300502400c101030740801d85521001c900c1c8040c00010000c20341c0e0754824400c1c9603061042c04105007079034031403901d80110701000a13018180400c004100c030f00740500840400210f081650810355000d498034a140c0303154580944048071072202d90700026483c5140c281c90522401a8808a40025010a81c0350303e8440044880da0a00400003041c0145003800080c146010007035114964080d002501640202c04201414011500c5c44124541e0392000c0c14003082e241c44a060030380382c110b828100d41d00c1500c420260b0764900c85500181010304046030010311050080703103852514184090410084ea224070120145000f80e003e817000190810480700441c0c0c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 867112580 1250 867111330 867111373
    0x506060703120c0903172d04050f060c030705030408120304020d02120f1b040e0607080f041a040b06211c02070503070b07211b031e030c110708 63
    0x300c602e044804240c5a840d1b40c000b4a51640e51080c4c00301c800501d407102000c07810310108000303801000710000f003864003071050810f000e175000d014403038602e91700d265440390368410444103011040c1058a4a03446141131254407900144112000c5020b0458255500d682c120101c3c1e1207a030b030080c0381880180c2c440e0207000c260442d4280205180c8204c0a40340c11540b0108441648000b02251078041200350b03805100c180c0ba20752011aa0992151050080c903607000a169a030002450700071610b9540e40742030902c00d418540d01600b0580f5403260500c0203020808070264401c4d6000c0c2c80074104041107040e041090603080c1400075013504055100100b001c0080e400d01002c2056104899003251a2000a406c0081a6100c000c0000e80040c40b8400c0202003506028000e4180c1e54007614a80a0319001d01804000b0311640c00407090180704d182054003421040c40000301c000f612803481c03080980d010f07004041c1c02020b000480c6d40781e1164107540000180710800d8440c404060044080c1d1900505120700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 867113830 1250 867112580 867112601
    0x60d06050606070213150b03040503030a050709090e0c0901120c0b0901090e0c0a1e0503010b0901050c0a0f0203100207081605071205060a06060c05030a11031615050606070312 77
    0xa0200300c14400760751200283d2100c0f06a4080c00240e4410603134403642c4991b550b030b2194894034000e000b0400802e101009595021000600105060f0f56003542100e00d070110381c001c05040c43c500344107060066400240c0b04590141680c0d030b54916601d503144d0074254904044002c055110b45502072150348480c2d005018801703010305000b00915100e8028481c5058100c8511024200105038820a10f500030707070203080b114001600d038480a5031600300408602c0305000340a03000c440002c111442c0d0b4403c1c4201d41600c8001d02c00c0d6995101145800a034041403500240c0c0302e4440d03086040901c1d4958070848400c6684885828500406000d8011207400d4a013401d913424041d800e00007849510030340590701001d10840180c4814078100356503008640d080d400100c100081412042d002031800400c070381410025060421800f2440038929103184a1403082445200d100f050000c208144500480c035100903c900601c0140c0e180e0041c41280d0251040c09400284100180c079249501c50740f0401014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 867115080 1250 867113830 867113839
    0x3011a101413090902150702090103080918071805090c0703200a140f0715031e0c030b0112020a21140c12090d020304090c050408070f0602060f060d060506 68
    0x80800e403202c2014074920780c001d51540380c032a0103040c11413500c2c0e03800f440c4840a0b410020b060000940100701c10780c01c14040200344840005007200c05503241c081c4050815024003c12465190000f00203001d851442c840c8114850481c001044070b01d0324154a82c03090f81480c403c107090140070341b800c4681c060519452401c058103000706c18a092010302c000c8400c54010011031640d0940400700341c0c54014003018108964120801c14811b22520409420031151a40390105450402014006000e0308042c80e044040786852416880117030160850740c0114070907200d020441c0c1d043e580310010303480783e040a1740c0016555007088964200c150716076070100601c0c000014040210b60214003201005480d51f5102c2d040c0880e40140c030b903140d00782c4180d001429501500e031800100030040c0d0ba0b4099070003103103c032a4a942403041d140f0700c00c105882c002d221440c100c4403190380e9032001c1d0030142c00074001c0d10014000c500005a01d1a40c21a80c0d50081201402c0c016204030b143d12440c0c0141030292259034003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 867116330 1250 867115080 867115087
    0x11040c12090809030a0501020a08180a021521012303061f360b130c020a051c0207150f0f0c0f060e01050a0c0c14160603050603011a1014 60
    0x591004c1001a1499101b00e00041e5a0001142c0180200034001d00d0410030071441034075003c003210081200004640d056032016601590003032030004d0340c082c0b00c141004120f8070180348407003184000c800f14125829010742049a55180749002c828404a01d074071341d0154010303008550500350040c0011030ae1000c0c8c1d043c8032601c0c0d44452200f021034951b1115481080039454030103640c040101e10005070410040001c00500000700c01180a0303c90b0003000788031107030381d0304900340e50076009004005400f5400000d542e02600f003d420581681c4d01080101d00600c104200821074030a894034800c0807070b685460b0145c10f84900c070341c1201c880000300d82c1a01088401c49000d800034400d00030300c0035041d00ca4003020030300d07511f4108207508603480140500095400c2140140340d040e0484c9103008000d8111480c581c60324a404000c80c0340601130a100d141034030070034100003580765065110038002c040c12002840300704901c440201d95240c840310b040790b01c2075001815861941c003d00e4140410b08910301200c3c01c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 867117580 1250 867116330 867116347
    0xc0212091206070207050f0d021e061b150612030409051005040207030210050a0510140307030503120702071217131701090507091a010809190f11040c120908 69
    0x1014415510000560701c400014841891f2011040a40440030b9848009001d05500020410f60704032024000082c2c1803660712041d521581c080300e05940012542c100c1d40905680b4642d51103507c000700c506100300550105020303140c040010204104081c3c021401c00703080104030030082501502101c189a02030000290f551039600240810078000c0c1c0141032820017040d101d2003a561f000303042d903100078030300780801c000c402840d000841500d0707010448a000401500110345460380300d8101034044e11010071b580480c0e214001e8401d10a403c150b003903032040c82c3c0d00c6a04103407410905e0700c0182180400c2080d0902c000401014064400e9441103400005640e44005196412600141320781a51204095402d1050402c0450018180c100c0d0400c0b80307201c114100c0700118510039016041101e5040400c2d07081c2c0c001c00c0325001c10300704a280107e0711125440e00d10709110006400700e030000c80e04101802d65181610585040300e0450311103428040c0e140309001c0c014a40d001e81196410828020402c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 867118830 1250 867117580 867117583
    0x21203070b040b1e01060906050703090f120210020d0804150923012d091718010306170721140d080916030206031003120e0111010c02120912 62
    0x40c0200e000b848601c3e101d003000f0707203100b805616108601a0400e420700c010400d15501c000361200711003c0d072604a46445045c9421150050b49a006030380694420a010a403401d00c1034114030b07940d01c21a4080550002c010090340c4902d80d29003c2c1c000b0030031000014022409020010624075000140020200b01680e0750100c0e810b502c1000a00d00c0d50503440d5801c0f81d84092060100e500e8078440f1151100f04005046405030780400e458840640c0c8490343d080800c280e00c0c07407813166110958141d40d1102140d9249004072000e0900031800217050680000c1c0307400c04414101221000303040902041e40c00c0204800312460b1085010500540420700d03480424040c003e0f42000b108500e024000b02d040d0404001c00d281c41c050007000c9135810940040320805411002c84007160742c1503542a441c0d9031a003040366241d505541c405400c000300e03003070152034490303000c90b450880400989800400e80351641750b4a003201d0700c42d81c4d00009a030280300c0f02c903001004080508464100104100c00315050310340d0b401d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 867120080 1250 867118830 867118853
    0x10504050a06050703090803061e090a0b2418030f030c031335010605180601030c05030c090108040219120b01090c090b2a0a06051e010302120307 64
    0x2a503858000c00440002c1100c140522500031410b464140900405604c44400900c00503101c6485646003199007000c0040c10ba07518101070b00000c0401c0a64904040220b000e060400c680340d104000e8807140501341100725032200c000034420701071982400c07140e080e1441d1860103030355180d9040c40343c070b01a1800381034100300074007030f202e2424080c540319401b41d042391000400c99082001705206844002c1d0030214607410120000c3c00c185c03070f900185800700500c64018107807500456040621021103024000c40b109039540600801c0e07030100101010808115200e001c1514049c3e42d004040201e00c545602c0303500e25030381060006020b0031205901142d040300b0500144d102002522168102806000d444403100b0b00500e81254140310144920600802c0ca088030302030340c0c41c490004906840074010342048141c8004942c1c01404088140b02380e101e58500744428111a12424000000c48001c400242036410b801d942000d82441c0c0d003140e08000b1000031589110b035261205000b44404900d000c00d40e07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 867121330 1250 867120080 867120083
    0x1119032d021e0901050702011b12080103050f07080c010e010324050a140922020d03030203062409010f0c080a05070201110102031308030a15080102040815040b07120e010504 76
    0x103a5811040c4401203420600401801c48108240511030711660001c013246c0016a09103000710321208150208a030588601c4400381404001281540c2c505030084141816280260100c60101300301c4107020355607204501030b04071150015500d01440e075000315800b81c0e031114141004100b4182c4181c2c000300e41900c2c14510015811820302c1004a410310746c0295002c0c00018120441200c200030204041c0340b40544184c1050b4203200f412181d60341090b580c44142036000748441426240c9040050294009640c0e480c4100101c060316421a0200040c3c50117031b071000001241040d00709401940c1c0495041d140600380312a410303c60300001e0011005024040145e02c61640381d04184c00010800c0c00303504107610320340e84108180031510000c1c031004011182d121071155525640c0c00502d101800c40e02c5008000e000c1140700c082940071044d00604190341d0500708031820120300c03d991040c10401a90040c1c07501880c03c0c003003802d140c0302c0c14004424103941d00c0701007807903010480300a08460080300c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 867122580 1250 867121330 867121421
    0x31404050a02150a140a0c1a070f0c020d082805070b060906090406110c010614090f0f0f04260702010e041b05090a050a0b0a0201111903 60
    0xa01c0380031450103490440c00200d900c1c40b03032801e0605414014040864101c20820481804a03110084520848040e140e680c4d00c0100f5030740f024900189480228000d580d100702040319a0090280c21b0311a5920013040307500100703465034845040e210340c842d07a40848010201c14619a070100b140e4140004a00701030100b42d5900703a0380315824208400a07600180031f02e0720034800003091010b15a5424084e070380107900004005140e13800050b14004501c20030307225000d99400c1c800002095410b4110302c851401054a883e2000d175a1152010390701007086a13a00c1015401c070000c28050780e103440110342e1091107072400440a56289180625a0328030110a2078040c2000a00408550340040085d2052070155002c1c04601c01c5e220491a00c20a080702a2040000c0840c1d0a0700a0f525003a6030801081e014003c0101991600e40c80c4420390b2010004901640c208000101c4100401c42151415081300c0d03040d440c01000e01c44101c0241041e00c81404011204680700d2030700c00200c6860800c09000031a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 867123830 1250 867122580 867122593
    0x910030b2b0b04210e06090909071e031412030f041106030a0203160201090c0618030213050f070e0102071a2712031c02070507030503040303020312010510090603050703140405 77
    0x28545130080c07404803120000c00185a400c0035154980c0d03001c2d03644444088440795083d83d55141030500c1c0841640c007003e80c4020000da00e400b1200050000f00c252402082414010030040c004942e5500a00e4040c400c01002007000443e004c845406540e00320b0300ca0301c00d49078a1401c0d40001f5880d40c00c26241e500c0d03144e90010034800c80b4104c800340c054500348030b80005d002d284050344604500ca4028404c2c081448000d51100b03202ca482c140700c00018640c01044d050502c00c041d07061000400084900345204291403010074800c0e801045003d42400050b80103110740f40c00c00000e440382a004507440c0d181c41d1014041d4880d41e0811700100c1c060032801000c80d01058ac01001040f90b0400b4415015600d03800400005207900b140c150f612144d0307d100300000d40d664200386001440c0298941c006041c0340804100070040543c04401020100411441c03010306980f1b0360208109080d00400c2800031070841035003081013070702030340000e80d200815080001d80c09000000c1100007400031102201c0941044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 867125080 1250 867123830 867123863
    0xc1603051215031527070305060601170a0f1b030b2d09060d0f030302070c0905010503060718260601170303131e080910030b2b0b04 58
    0x1505880c0e221191400d190b07024000c280110b038882401e00000d9107205004000034200425480c0a0b0b450a0300c0d011005002d40010000b8030b8655005001c120703010701820000c104190b00c6500f42e0302c410b80500780303035a09a864911035000200b40c9250448102d50321a110405a041070500707803618064603031004102c0c0d0390144d040008201d0131000e01c1111000c40c0c1c00d48c141e8200e05a5020445510942d4000308544418000070b0003801034071001030080218500134010140e05401400c0014498418104c01a8031242900285c035001d01486405901c044005416141300b2619000d40075050f0309901a102d4131030b911200a0303100010110361903036001e2200d0102ca9410070038980103098828004040d4140140340c030751640b00141070f0005805c0840000d01c180f2002205040700ea02003054003600032959880c00f9401508100b1790948602c1d40a4504000a0f0080c01000d5507020020b25402d100d90310900c0c00d000100000d40b181005440c00e51101000540305000c5a01843c0103028660015509 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 867126330 1250 867125080 867125107
    0xc1201050603070c030822030f0801050301140609150402130501020c090402030d050c070902030a0501050102010b030a030210020c0f0f1e0c010c080a11010c0f09050102240c160305 79
    0x603401140207200030030411082d60f42c400407549000c0d40c5071038050382076180d0b1040c5805203040301c02107284106141c02170b9020590014110252490740d6112051580e82c1c0e0b004141c200c544011400c0c2c40c04134280c000410514200780039940c80041082c1104030410064042004c90f0050a100e46030045401814006c540e01009040500e002c210303004032041c9031503404282c071542c17400d1036030060220101d11400c009500b80125400382414040840d1645440551240074100a120b0f650265190904003019070a000c100c80209903015001041389207100d5400c40c00a50004d0101041400b0f40901e24500d10014031240c03007901c011000402d22010310030034010750351045403078041c1c15034800f9041940c41d0340c1240c0a11001d40c2c001c44480d490b84444a000e480c0c080814490400079480c003450b460541e42c002802e042180c14958580726150380343c00042e031f51400c50300010342000703110030104160001e00468280e8000d00502d001c80c00d003000b507030021148281c1c1110803800f0420100b40700018201c0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 867127580 1250 867126330 867126367
    0xf082419080c19050f04051b070302010507170403140d06030c080a060b10020a121101050f0403030e0c030705190f0b120c0f09120717030318011e02071502030c 70
    0x2902e80d00f20548070b00e0100010501d030740c01c152160040b80c54500003282801a0117200d9001d03c4000300e0745648070101e1400900820049070000003054040030404000f09124050701c2c0b1071503150316203000b0300610002080310303600728558898000341ca0303090100006502074088001003e20400a061444262901ca8103031580c1c40d039a1401800300700e4401c104141d00181416840e600080b02001d00c0340a0f0504542020014296070441d600303101c1404400500d10b0b81082c4100d00035501000902050900d45440d100303070301c40c008d50652041405014a19159803010700c02c000c0200d1000c050340c4e9a000010f0000b601e980314411621010503800b1000302c484000643c0301035004a450b00c0e149203e54030400c0c2d406045004d034090490311001c14a80c2070200b0a0030094240c85445050190030115820f0b0303aa801100c252100e1100c8125501e10b01e0070501605060f031290092112401d4201001140250000002074402280000199880c1800b6100071401440d148425555840444160600d01c08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 867128830 1250 867127580 867127609
    0x30403140105011d01060305070e1c0302060c131703120106090807060f0f030e0709050a020705100b1f0311160b1e0a1805030d06060f082419080c 64
    0x550b80c3d10740c1113070510002d40607054440d40c0c03c000072240c1f00c14008075801e036110104a90002012402d044218040742c1c04145400c0c880d50031215a03540e5168420514041c042d080d00420900301401d02c41c51034805601980e02c0341520440e401c1c04041c031011340711800b00ba4088400b180e42c008040c4090181803149501074401410501000024480300a1000050400120805583d040c03c10000d420900c0250000d001d02d20050002d4240403140400a6000c0d140880715480b418600c1c050090b8140907407805840002c1400707032042c00110044a0b1040c9500b03c81081580e100980680034444001400b4821004201520000b00e240f0b0180d0141101410440d900d44103004210134941a00142e030b41d009042001c04210f00c0c81c0d100c0040ca610912850003465030101107040603049202d50720010031990035a8440e40082a803000a95001d2415a8206003a520a90151710f0b80702e10542000400000130340900c0c60702802052034400e4078259000b8410907040400c100070f05103011490386070f600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 867130080 1250 867128830 867128849
    0xb07020607020102120114010c0501090c05011d031e07081603020109090e120a02030906042c070c020618221b0e1c140102070605130803060103150803040314010501 72
    0x640d11701c150b0112010140b00720407442181488988491748610307118400c0350390003002440608154500044480c3c4035001e11400540e0310201e03206080710740b0302091074071400640a080d289643d04645180b81e4001440307140244076988001031000c904100c1611268a030032102104030342140300040002d90541d10a0354407a040c94194242e000c40828074904504000306045c0e51101d000381d0584c10740c083c40081b1540300c0303808640041c980c01c501c8d1020320541c000d04020490501c0f41403107107500c0034040c0e4107180000c043c482c03c0001801d119004001000c80c0c036910340041440f00c00054a208142032455002c64071a519901030404c05001e03001844002a4032002c11802c450b03030003404403084004807841500c550919404082c400b959055006800007900298003200748440d0340130b0362014000b02c503942e10b0b21001848031104503d581910035480050203165803204001100a0a814501c40700000c120040001d180c020420040c00254400c0c01440340e1440c42c1d000b543c0c00c50302c05a0080e900d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 867131330 1250 867130080 867130087
    0xa15080912180d020103110a050309190f06050c09040903210605010f140c033106120b0f04050a09060e06010f03140c03010c11010b0d05030d09060e03070b07020607020102 75
    0x51040e0b101036400c80c40b419648000003103990700040b005414502c860800182c0b0008203480700a0b409001503201d0008a802c03698460b0001c28006000d00041d0382c041d20a10170703402c03603400260442d005a0307080540c6001d0141040440d10005049a4202d01c0407004540350040e002c40307440d44200c42c07041c030b60317880641080b440b46018000b9011201d01541d135010840f82601c0b03002d04900c0d10040c0c8071050104000c60761902290402210603551650710f40c40e0118031200703c00440304c40b1120b0307842604e200d95203144911203601c40342000390004540e82c6512031b500402915940c2c60f5485050310071000620046051680c90804108a44028031580d07490342100300140141510040702030100e96000c818003030b6420030501103d09104001c00103c1d415400c01c2032210103a035108444407071000c0c04d60002c1100c124000c08210300505e0050340184a50000e00a0080304401ba40c006440305004d100d021580440f0703140d1483c1154410b5900f1140209000284543c50b13038100f1240d40c5c0021140021440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 867132580 1250 867131330 867131347
    0x10b0a030b0a0b0f070807060606020f0601091503020f060702090709090b01020105130b04170705010617010c0903060509120403080307020c180a0902010c0b0f01051906080a020304020a15080912 85
    0x1680301c4c284104104001c002034903410000c6010803500ba203900043c04100041d2160002500c3c0c0055120304001403207a42c00109183c2d015206498903844011860922a85190f0902c4402181c2c001c64940c808400d100700000360300c070440c03031130b00c2000c00e17554208055080c050903000321140054290b04580c0342a00b044145a0b3b01c40000c40100d42044802500e6621341c68250807181c40c0200760150244081111020044150001c6081c3d0b00080e00e10030b000350031810f0f041e0032a0008026000080d4503240c00b0804916a0b9010a820a0400381514003001c0c038140011450b034440e81c01190f9850703000081100c8554148281408031a046400358034400481600760f02030003020b030440403059a140700c4001168002c2c240302040e03d5000e100034001f8901607021a000100074821a4010300403400e4a0342c00060200c1d03150309035416612a802c0e141c840704150002034000a008a0f00301d01a508041043c1a09152103c80b01490707998400c032920b07206420310304001107080201b411400c02c1c42001c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 867133830 1250 867132580 867132599
    0x201030624141c1104030218040203061b0703031e0e030d05010b031b28020f060c0901090918020a0308030109060608221a0a200c06060621010b0a030b0a 67
    0x10b00c0d05001c880c011070030032466138001001c3d1045900003944410310b21011742c0f41e98000e0b0b180600c1a0b0086050f20070503501c0041c1142400401595201801c0b403c205420000303000742e0007600201c8000c1034401007590541da0180c00c503001e40220034096030001c1104020b418090080703034054041100744e51300b1414a592450720580c0c20784c005000720303280403c0d005e01c81030364030303030400315546001a80c0e00c801c0501c17490180d254094020302c0f101901a08001406450529044420040701030755039060082ca0300b00d03a007004142d4096564076240c1111051005a50f07144031800166004001182d904d51501301c512003142c441c0e42c00841070121940c2000480f0f0141108111040c9064007040402d001034074103e5101809000c0c07141017001280280032029402d0303840710750030140c4c52810310b207004c020141040481c06458940d80056100320006070403070505001400c001081c8400c181000d40f0591200c910160090300411980807010a101c080c40e9454041c501043c6021b5130000201c80c01c103506034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 867135080 1250 867133830 867133867
    0xf0316181413021605150a110a120e25142d031f150509060f120d08070915020703200a0905010f0e1915170c040f02070312020310091104030614010602060112020103062414 75
    0xd0761040c1030f40f0207000c9040d101c024401e07040c4002c0545040d074443098640200f003103940046114003450071144110452416180f0011b5400081240c04903903510310801c00ca200110f000103030402c005804003d90131504000f4004008005d0b203529000b0318001100070030b104080c0e4001c2d001c5103800c0780e070141819000308540703064039081620f40381310359918138041d840d1581000c5129081050100c0000b502112980414103850101e0780d031003000d03660f8512020800c1c1d0b0940c1c135003998100e103030036550180030a94401802010394a4404100d141d0345c00d109078039200010906605604014086412450240300d00411480e070000210300313110160b14001c0c80c05807404e40d82100d6a030300001007040e01804a080700010030407204180022244004a014290014030040b1a406d0030b14980c2c01c4010749200c21103040c1c03107480d8003c1000d07a10f420080c000701c2c0200c1f00c003603052554401010400408a1050420801000310f040c09035104022000f00001d0b8a141c84100029080c440706c112005040002c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 867136330 1250 867135080 867135109
    0x5180c0d170d0e100e061b12040212030a0c0204110316030c0504050a03030203090405060a03080a050f0f0316181413021605150a110a120e2514 63
    0x125071245148001e00000b80580240780c88180303e1340c111240c0f48040358000031440340a55007924410b840d000c40203103000014001d1045080303020b10507102c1d40c401007803070780398000c0c0002c0218032045003c1501c41e0440d441484010000351145202d20103504090003100d52081c00c40035114990315010f0112045400c00b1103c1c5820540c07a450403001e0688a4025540500350080840e2510740e40c1c0d1130080e682c0cbd1b114240e841d0245091900150481c5004a5040d0407290019040b914001c0001011a41c40d4440280e82c0030032403007070102883d0359122001541c030604454505031b0203458164400741110050100f0380c003403940e0030401841002e11b8642010800403084d10000301140b8201040c0d0041c2c06011301c0b20403845071100c040c0060200009240904007007144201c1216120b02c84d0480c107661074000d90610b005400c02000f04428401d04103c03002150950340000d0b030410700c40c0300506100340c80030f8480b00410314803000d0795410700c030404d00001891400c80c01c4080340c07541d1000c204c508158500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 867137580 1250 867136330 867136373
    0x60c0a0e0118090f060503070308070213020d0203040804030b0a0b03070510050702030102071a150315070c05060103060506031b090f0c1c0c030e01020a0e060903030405030105180c0d 80
    0x15a603401518003a007462107a08450310510346454040f0010100383c1101d89903a4107120b40000c45040c08030b0890140c942140b400e40c5000c0c510f8083c000031308038941c0351a0003c1c0d8204411420301341203101443c0618031681c2c295a5a92642c2882d0400c043c0242030040c11616086000380581c1d00068070808543d4190744040f51415442000e1b1064081d40074040d405500000b1241d0401c4401040d10f80440e2149401080ca034860004100d11102001106a0941c0c4800d14050382a1042003407a580254035107012155908613a860608000003a07204441e402e8540d03050040501e800e105c3c05c0f0610030b12400c0c461018103040c002400000e00505000406103035000481d2003140801c00311030a07022541184890b000900c560071005102640864000a1030708010115040c411b00886d2125a007a54540203411801800c10146600403002c8541c5440100400103d82d203003130103481c0c400d41042070001808801e22400d1800c10503800403151107070b40d80782060070008014415540b04e4040654 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 867138830 1250 867137580 867137597
    0xc090518270106030b0a0509061006050304060b12030a0201060603061403060103020d0203281101080114040b011806081902030106090b070c03020a03080c0706030216030c1a04080d0c02060c0a 84
    0x1c0d500d0043c0a141c00c0038205407080f008016180729203801c007a0088a00c2811a0b03442c1e601d401010240c003036940520703000a80200081804034100f50403104c240b25000341072941d9000e6820038580317550310001d10000035035100d134410044030350544501c40013441140841190b0643c003c000a032180707014040240300c1c00c2040c80c52825500c0410220b28030700020b91110041d801e00396618a040e1004031f100305d810f4108080c0914055210f10900c0d81201c1b500140e10100710140002c00010300504190320b410404222041c0561000c0c50b4404801401161501001d6041031242600d8188202d101a150b60340100010001640e210b10030350b0441e910030b60025142e98a130301e402c450726150b50748003030340c04001d1850110500181078002e12411a461040300c0c24585c1c0c0c1c002c1035080e4011500104025121000504046030180c140901c4142c8078100409841e00e0118041d030002000351401e44a200000c2500c0407902c5441c81750510070041c6000510700352511510485d1103206030a44481007000e242c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 867140080 1250 867138830 867138901
    0x3030a081506070c240e010305041a28020f03040b100503010609020c0d030501060807110307060c03090314030c0703050705010f110c01061a090613090c090518 70
    0x4644001014400822466582c00c0070704102e851540980911031904c03c8441c1c0702c175640c201140c800d1071281416103503490781c200301c13a0064000306402007042d244400780d04100009100c1600401e881081da451040e039000c6400b4202040074009107080110303552040000e0300303503006a10701781d985c0141c2c0950150b40075501c80f5101902e801c1c1a1788210b400d98280b42010034081455000340078000b20401c100d45d0510b800303143c208c0c2074030402c0c461540884c501102103000c0b02d20a9142c1e800c2c017464501120724110300d66584d0300455500a00d003100095440e98800c1c201031703014a10211080200702018150300740490402c129203d075200040c01c0c05000210081003001c06c0d00000d20744845401c0c00c02c000d211711102e0f1540c580c05011f14501c154070b4040c001c50781860506000040700c480703c2002e81000b40301c00070301050b6423245040c1c40c905040396000050240352800384400846040d9101c0c0012854807050281d12900c03034480c41401d0719182c08100359061440880d9860400c847d04142240d6401c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 867141330 1250 867140080 867140101
    0x80c03070e161b050102030412051207050d020f0c07210b0a0903030914060601090909080919050307032f010503041101050913051504020304080d0e0c130c140903030a08 74
    0x143d81c0100000a041402d40c00e01c030065000d540f0550041d01c03221440c000700101195071307101d0381140403040740380c61011840c020300c03d901402420111810061070200b13a400b10102c140c00c60345c03a1149a41c840e9005112400284d00109044001d81540c5000400c656840490001c00146110703031181d030301d20304035081c90b120f50001608140c201415070845c0032541d108a4613624102c8125010900c0307400c0005440d50035200300c01506411149070381c00c0500800401440005d1006034089230440c00d0b0002c25669020300c60b98008511034442009501d0803040c00c62134880c0ca5080070403908580d407580010360303600a8101c941c0f159019180c22400224040181c4982c000e0404075070708030340d4910969003203451742e41c0407a000300002e81203a08584034000400099101c115001091312006002c00c4002d002950400c030300000c003400030750b151180d20030b01050740c00018100c400400390715440340355207803604244800080707403a1589a5290400000200f03a80e4400d032510501040302810026480610 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 867142580 1250 867141330 867141347
    0x207210c0f1217070503060102370c09020a0503010e1f03140111030c0406021b0109051306050301020a20070f1a0c0a060204050a120209010e041109040b01080c03070e16 74
    0x20302104610f0340d070601c3c1500034a1074004407091400740c0300340003504103001044c0c54881e40c10140c1c001081009030913401c0403090381412003070441c0c01030144140802c2d00c0400e40050701c1845040c0d510252290301d132559011540344013421960004601d00d04010b1800e62200c1110141c942001c40d14203221507036203403207006210821001000d020080144100021001d00030b100b21100d9508442c0100d880d039804080c2074288111690220380980d808001c41d04111015030002401e00b0b80000d0744039620400700c0c0c2640c3c8044402400074040f100d074604018a007198020301030742d0002c0100b04030b0313003041d07090200814540111220050080c0e600300d1310300319240848192051400c01d44100051528040001e0b40050254500ca80510070780171507440a1582d00c400d003160018000481c1ba482c00e403a070420548007030002d6400a458010f0400d040e1100c1d0700190045120780d0400c140da6150003012410401030000641c4281c000324820030070207000307006c600c1c0c200e6614103040e0980184e00c9000d81e1001e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 867143830 1250 867142580 867142607
    0x203030f0f282c0907050d020a26040506070e2b0302060f1317040302040c08060301050a0218060306011106010303020f21120c0d0207210c0f12 63
    0x703407400c42000c08518610309511405000d5212074216452040701100f400d0040da001204500c00300d10a966186402404160002c0c2141852031901414003a42400d076484038401c42d000c22540f0504402803d500796801341d120000d0302e200a610305183e039806441d00d01c003810880421515007000800c5686001403001c0e40210b1101040c0f000d040c403140204a652002800e40140c050180040d500c1100182170b20b110b1032a051515442c0d07010740da6007042001d416081d01142170b01c18000440140c859200c0c02680c0001a03d45043c5441d00300105425124000c3c10080302030b0040c00111181c9909503a82e0146030b008a603010b07101e0380d50200484198100714080003240c4580d000001c1499008500310140000110507542986501c10b840108500300c02c04103400300074101b02c4100c0a01c15a0302442d042205250640d1801c00c00e0040d043c16a00300700b2003507034542402900c40c0d4411340d400c0d10801d9101e4550500820f070368010340340d8a030040e01d400c6024140418131030055100c80e00c030b44100c4000e00f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 867145080 1250 867143830 867143857
    0xe100801060906171f050a121a0702060f1e0112060f0204140105090316120501050108010501030b0109050403120c17090a0206090d0f05101a191403010209030a0323070203030f0f 78
    0x1c0ea20307040c0da2540b08c40302e0005c1d5100c0d80101ea400c1903440e410080305104881035001011541c4408030308902c22100202410044891010031400c0f030500045800d00800001401d06c212443d1400d00340c00312000036044e248224070400040040c0d541c1c100008143d05030909005469060740300109013014000c0f030020414405a030004242030034074500d406141e60044008006683e21903854a0032142c0a00001d0102003c070b400401ca040e90507081117a21911a2601803c40c0032200c56203400c0e943c0c003180d6200403401000307902110f807034500000b0313921607404001000c0c100300c1a000b10306a485a40c0c25103001b100c21000410500c0304407010b4944459108007107543d108998546c4200408146030080e0200081c03907102c00540c500052801e8143c122040c0c0c1000051424000d220300d81c251351241d580654080c0700690f034640d0140401c03062140262608a040080c503e0b8820035240100120415400c09110600158500105903401c42096490950741c40085800c25000c50045138070400e200b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 867146330 1250 867145080 867145099
    0x608070e03071706190c091715040b18011512020d0f0b0a05131119050904080d050f01120f150e0a030e0d03020316030e100801060906171f05 62
    0x1036200080709841082c01c43d4070200c03000d040454840030740d55050030100024444c007105008c0d9401c800b03100d142e4460a10b04036036074613007080c0421285800840d016221211340c1002c21031442008102a102013103041c008004562040c0d0710800d18060354003925001380d818020040442d1a41c032440200203402400070345200c3c0440c41c0402c4240360441c1d0440f0454149030101e2198502c17808030a07c190f40c03049152880d99840d10a02080b0a854088220424110840000d25071641125a4012401100103540e180009403003c0c0c03d030b034006000c041c4980c00319001000300741015061040300300e41c44070351004840803c0c00d00f04040c0900e0440741e16410316003048404d40ca0000522090070310b1203900c81850810fa084d00b040740601d1700c0d90001e40175800c10003144888492420560751018402d04049160f10b107040d0103d000c0c11080e182346004210310500501c85242c0004101e402841c2e18900000540020503000c8800c150140c000400801c083c90700e0040410800318200c00707410090440d484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 867147580 1250 867146330 867146369
    0xc0405180a09140610061e030f020d090311070e07051b0c0901060203091008060d151b081f05061c0603080a050a090b0f0a0521010e0403020c0306010608070e0307 71
    0x40f19041517448241a4050740f00004029018119001c9a0203045600c00006a05100c0c02c0d00604812000341c038101d40d0030018841c21042c1c610521544601a030355006000318030250040c90040395070084000e00d11240e0070808915030100440358400071603203070b504401d000140c00c50b1a105000c01ca456000c0e100300000b04000741c1c000040c040c04401124074801b25449a002a20350303000968130b49030003843c23211880c004a00f0007400000000030601c400580c0c0e4405128070700b4080c940000313450014201400b4840102ca21922800d800080701c1443c018003807070321002821501c0381400d5082000801c00d611781c900c9115a000b003009581110030b580d9a414400c3c2d00510b0b40d0b000c4041035020071001400440c01f00010416903da14400092480c5080c1e04158152a80d81150b4540ea22a140c2200c103032000c80d5140c40b1040c02008001240107080c00d161034041d0602c0c0e0410782c0c0301c0c000e078002001006040c0d4084020303504110303142002c0d2424402280401d0628800750448540ea2591044c0d000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 867148830 1250 867147580 867147583
    0xf080d05180d0905060d09030903052b0521130c03080406090b030105100e03030409060b0a0e010e10030c0507170406030b0a08060106051803061e0c0405180a0914 71
    0xd40c441d00810a0b0303003001d0000b6205446680c16806410342040b0280040c4208000640c03102e0103d501030b0818021269481c0c5e5020f281c42030283d0141120740c2042c20202d2035003114071411410a0b402e0401c9420004001c0300c00c1040e000d909500008001d810000c502a21142c03440020b00940103d0b0b80407541752207041510840d03000d84100c0c0c0c0004c540e020002003441200c020340e8141ca40c010040e840051010500719500c0040b950640c0d4140000c0000203101d211521075680200810316540c1c1d22084816006003169000001141c1401b000c0d8803c000c0981e03548034042c91405c15410700040250414208a440d405840001880152120016841c420007500640300701d0703545960521002480354140300b4092030510511207158040d00042c44028000c82c050108200340d40e0390a000ca0003d04006803908030700340c4003000105819940314004201400f03509900c5461603280310315191038031010515007044800402c0d600c13400b801c0480c8089a03280c02c441d1070143c102c000356950060342036486 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 867150080 1250 867148830 867148861
    0x61d040b0c0c0d020c0f1008010306020f09100306060905010c030c260d060e070c0f0b07020a0c06030b040506090907091109040e16150905010c020103090503030c13080106030c030f080d05 82
    0x3446803003130500b41d506c0c520700800c10020810065076022107691840d6581006034004504109049a06000391601c5844035030810118040303a9402145035881c104020702a610380d17822460411070207a00300c5011035080b84065000c030758084428408006203104003100400121a01ca03448800000c0c0c255130040983c00c103606842500c8598401601c540d602500c000c0030a440061082d009025150046008044066800710301401174aa802185655072074241c1825002000443e645218017100e034100b611800e035005205651000090400000d0b50383d032060300e403003030301e0110b40c0b2008484008000082943c405a4000e40700340420100004100d40b500c86400c080041196030742030001d9607224201c0c0036a100d2020740c0f540c140450600303004450103001000c0a034181502da900c0100020820001140302d030704240c1d050350320750400480600c00407015500488603a8113108092000c1400d038040070301181c2c0d0003400910481c283d031402d005903010710b10702003180c02d150008001586d541c89202 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 867151330 1250 867150080 867150103
    0x60a120b0306090d120905030301060305010e0601030e1002090f0a0e060325050108150a030804060212210618090a060b04021e03060d05100204030204061d040b0c0c0d02 74
    0x40c0a09400e550515980c0c0e003084444020350350006003101d82d8075010b0104600410241c0401103101c0501792a03442c030b59442a80702d040000c5e0740740300410441002038000c03a08004241303003c0c0942d5104118242e511403e000c48143c000740d0004840101e507468a25041c185500078200e041e4043d030b190541406150100c0e00c050081c02016407181d80c460341c1200988450860760f2800300040e042c4401100c403030000030300c08225000348941200c001d030b6130100742400640c86111402e5560303080140090801911120190703a002c000c0c003203e180365440c180c0c0b5100d029910004095031350b41c3c242c0024050041d41003849480f880311030a02182d1000403800400c503038001c4030f0a0242d0450201404100d00c200341144040e604d00c1810450034071600001140c00003001400d026081160303131101c50070485034031408a082d90780000c0420031424580076850007014608130b0401d42e44001c03a24010080802000181101c800500060100c5a41e00c1550103500781c01080720a401d800b0103020b50b40340e039030b901c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 867152580 1250 867151330 867151367
    0xa0203010509060c0f07020109030f0506060a05060723011d03040302011713020906040b191806060816020102040b121e22380919080901030b060a 64
    0x20122200000d80c3c40c01140d00c4000f01d858800d00303651252290300903680c200d040100508002011484c440c9a480e1120f005001030710340d50a05400300003541c2c820303034059030082c070080c480000030413428844483c10642c0b04001140c40c40035150703924010a002a900700581c0740365400896459030020117013098074400e807241003428041036020555031400311003403140c0307002d4039810b00c0060400840050f0840b0000e4408558901d040d800203014a0710a00c09046203001d0303600422800c400c0040111102d011000304000060806600422501c2d00521400d996075100c02c0d079401242c403d6045500038201c070119151101241c948500e0048010f98100111103031442e184444c1c0c0144805075030040e410080320040c00ca03522141d030700303216121a405451540c034810b00d110900102500200d69210b200450250024000008500c2d000740030345001c05ca94003410130005a51010b00301200000c1d086000651540c03120344c0100e0107004450522a007100002c100080c1158000c188400c01d503181c1c15 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 867153830 1250 867152580 867152591
    0x302030d0c03150303110c041b1b080406181206020414040b0603190f0903020c100e0108060d26090307120b1803070804030506101217031e04050a020301 67
    0x581c02c0701510300000d03040d56103408002c01000068042d08036020b03c583d0440075648410101030000f404c50703000d60410b14481101c040d0203003005a000040c2c90781c14140c0c0380c469800d0702550f01c81a41e41c3c0202d000d41c0c02130121201900005400788181b6070700070031001c1d6000300d074820701d441e08d00040d4006200701880ba001c280b141e1900e6180c0707801021030041015024a06566800308005900a94a007080c45425690188002e401c2e205d805034100050290700104141c10103441031001441d0b035103041e072041040b001c100d030106aa0101070250000c0c021900c900ba00e4456050103480c40c0b43d4001007003540d000041ca040c3c142c0c91010003030090700004500351030070b0a5a4400e04e80d92240e111320018901011000020740d4560815070f6190040e503003030126810b20f00c2d035940c0e26110740d001f50016203069000f1030401054042020810000d044141c2e464070343c0701840e98580c0000510500c0a406240c0044002000100c0c140d1680c2c80d08405e00317005220908182c2046502c4024201d4103138040d500b0413 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 867155080 1250 867153830 867153851
    0x302010219111209010903020d05010c18080d0f11060a09050d2123040c3b090c0d030c05010c0f022e050f0604050906011815030507030302030d 63
    0x550b280810303003000c03401420342e4070a00c401d0705189510071002079050000611000c4050703110000101c1500d4400c800000d0480c904032009420a12203501c1a000742d40c241e1800c0c4001540426046d01c00049400d1810000c1006001520072031040090000309100f50003c0207122611a04100071803030040055030720f07042d049075003103034007504000c1048140fa03100300300d882011000c0d0b8002802a414910156094140102d0034880c000d02030b50300b039800250b03100c002e101d000c003103c0c2e200000d00d601091518100c0e03164041c0031f003a040302200d400c2144038402e0000d0081481030001d6804120000c000804924140c038000e00004004442520a50310b0250380105141c00b5409101340c55480342c00800c2c1d10070060312072122001291940c00301d40d041389400f0000c000c80d9070181d10b00901c210784501110b0320b014024007044030b800410080c0150b0265004203c40c119141060200640e840d00124074081d6120718140c0c4510b490340300902512968400000381940803024296261240c402444a048003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 867156330 1250 867155080 867155087
    0x61d010c021506030a060606050c060703060f03061802120d140408060105061e180324070c0218010b0703090602060103020f0409110424080312061c050a0302010219 72
    0xa00c809800503074071880c45280c42d0900c10064030343c441e500601319102c0382400da4490080c1c880c10741c403000110703001080415148209201720303075210f01140380400c00c0603c0d190180c1280400c0d4400604080d590b07640480c52042411100c00b1000d402400d45605000401052941d07070484280100c0043d4440c00c101e02440c2d903000c1298100c55034800104240d900705820814103034020381400408002c19885488054000c10243c01901c141880d0061110801c209040c1000c0e0040c40344880c3c0741c0312162828444100000721a00304009242c8a04058018408580d07410750244094131030030b2341e15000046041c000740c01444054440d64409003207036550001a65038803c2800f000f90301440400700461241055400751420300d0081c000b45648010180114044800141800320018002004c140c0420840c181000081c60010000c500e0101c00c000c2055203030001502961040c1e4a650a41d003030411050340421a81341c05c8000d42c0c000450501e4041d000754440d10304c01c4080f0194541d0021090b02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 867157580 1250 867156330 867156341
    0x290405010513020319060f21230312040506060f030a0302030703081302040507020d08090309060306100201090c170610083c01091106040b070813030f061d01 69
    0x140a848080c08401d4030710b00d00b0203034000802244214200703c01003441020203000b220f0041100d4800080305900340f80081c580405d60100116041903030f40d210400154100d00c002d41401e002c0c003240710108003400c88940c2503110b424007900f46c0c02c50110512003401404640c45008000455001c810000d884086c5502c4484c4a0300140245e0010710401c408030f401100e0142d4480407007031684640c0c4140ba400a0100d580c191050001030b4403022b03c10310015042090142c1081c940f2000798140000d410004625110051000703000b0607120a07030705d0030305000b50095200c007640800c40102940d00c070304180c5896061036420a400740308280124145a10300031080083d201e005020709044002e808150000c1c4c903d07020442c0c030080040904150303141801082c20512408030001159031a0203050000a00600344141480f170401044100842c2030791a04880e0b03201e074050000380d2109200d003c1c402d082211039201820b00c40305aa821410490690b0201c0f002d0001c1114034001c9904914806088a4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 867158830 1250 867157580 867157589
    0x1006060504060e040f0c0305070e012307080721020d03020f03040f170a0e091e010302010f0201020c03030103150c0e01120b0a080d030e0f06090d0f02030d29040501 72
    0x10300030401809098818005148810806030012030070241d0070091508035415049a0000640d58030240280507a00061903100308409103130440c00c1c00c0d221000c2e8000f8100d001c40750040504000303807613400c07c14903406545c4465004030703136041180ca100301011006c441c0542c802005014401400c0b40003400380c402c1c1c81d089092072100301c1c1540c0d1143d542403c2c40903250710075540d1104150107007450609031401485040301035582c81b0700040508003400101400130b042907078208811a00c25264000108089044075024640280601460441603009102e00c01c201c04040c0400030000c01400202c1160403004858100700b0050b03d2140041103a407415000c003e9400a2240e4111081a0983c0d4021000091004000f1280d403030361080c03c0703440c00327680c450280003094440048246250040c041c141203140300d070b800b40505203056010184c41c0c01f8404401814000388000c1c110259200300f054600386d8062100420003400054151141c0d038100e0425a00746081001041c0c1c1c080c105405024100c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 867160080 1250 867158830 867158837
    0x180b0f2119050c01080c0c07090f060b0403050c190815060114180f01090801150f050d0506060409030c081b070b1e070302010b090c040f060c210905031e100606 70
    0xa5840320044445c11406088a80845401d024003004080c09000240080103441000982c45002010203000d803011940801d903528420b120030408204013190f480f40d840380031100c000e088010003e040d1109441c0d90480d80282c811101841c41ca031a159425600401c000d881d180d007021480d102d00d1803a0f00c103048110484007903620852865003000450019055030504141c01c5080d128040d040c01c4440c0c81c0c1d6051046004d255040140c40003800c0c1c2c1001420050381c0394028600b107510740751b56408001d07101902540d07603440e400d07003814420a8601b88240d801440e260350707818140c0d03410202c40d6100d2110280c90044c420b00003000f88014085401c000c041c551300d00c042d1162003d880308503802c40030069040d9501c0b00300301140b658031004003030310070380011280c81d40307690410403810488207054000009008600d501840451019618051440d800c1d4081c200940c8540d00212445801a442103825100343c6840d607000e001c000c520903005800c490111024142407040c101d0503038140d8804c0c00c010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 867161330 1250 867160080 867160093
    0xd050405060d360b3105100c030203040c0b09091306060504060305010b040f18061112190b03070e010b031923060a12080d0e0d0e0f0109180b0f211905 66
    0x42c81403071030320340745c0050062054440443c010304095003550380801c850380001c2d9000003044104503c0d21083c101600f010102c042c14002d0001c0414034845001c2d00d00c117218a0b07000040340820502e43c01100180c10041c0041c420207581e450264003801c2c0001605118504060390300303c1403541031140340102601e0484065204011392540c5c4000c2c015660001a00101000174411a240403802c2c0c2d80203400d14001172508c40c10500d200000c40b00300c41900e9200780c0001800300082107401404a0646140b004003543e00d4031020066008207907410895100c6a09000e4040281c1003800081501c60702c4811070300409948002c100069110309005080010004030b0019001c604010044c081c0d100c055080000c0c421075080e242d924045a09070f9010018200508000e0103040114942e0742800c000c1c2010011141861507902c4840c6005007500103103a50384001d400c1c1d40c0e880000c40f25040b000a0201610400440c00d0b480400341c000c80c00c040300f482031228050884512044100d181604800035120 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 867162580 1250 867161330 867161401
    0x30203030c09040b1011070f05030703140c0d0602030a0606030209090a02091c0807380601020c0a0e09060115020a03140f0d0507020d050405060d360b 66
    0x1c5a4100d846019041aa100714201c45901c6050a41610305610b807140071130007006080b440d1a0000c190050b644a1101d4881041541c07800144801035075032150840150141c012030032031400141e911010b0344800804491401d005240e402140205502c0358103020316501ea00c001e42c113a220700c0781c20640010700040040c4a081d290b0340035115022004081c0210f00340c00d0038000c50080f42c0903030251041c10307001a00c1401c2080d000e070f00540004504111403414100203020003041550058501c104d80c050b540011f4182c1e10074001d81d07080f214020b060301e881c6605d40e00c4105007102d080314800101d1081e44008590b90400110301c3c841806290b00a240080b070a6070b0868000e030074851780403140c920510411130481a824040e00c601c0c21100000a411704e030010700240b03450021000c840620104000502080d2201012105c04025551011840c05040e111034030782009040020185000060500450a280d26125950b014010580c0480c40d03195000c0c4403141134050b00000c503903011401c10031030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 867163830 1250 867162580 867162601
    0x1615020a0203030d0e03040b070501050603100902030a0201080405010e030a0203092b150f14040209011a120c040801020406020a0615271410080f01020307021f02090a1d0f0403020303 80
    0x950711701e55409903400d150744e070300401c115600003200840f070594441c4208031141c2400c100d12102d682c100c0c00c0038000a582500441e8030784e0030251000c3c2c1000000000901400f01c01d401022a9035118400c80340d55075260800252640c03c0001c0b2503104440d01c082400140c501c0c01341c1c2c0b0030408500a18060312200c03e980340250800d411200d21955074861040940440d024404c1001c4101c1d1854480c69514292040105605058200c1030007503900d0004c0c040d501711004150382022010072590801c039103840020342c1440c043c07548013200f250300008000c50020340c0400e4201b6407030300c0f400c03007480440c001d001c80c0c00341c400a0f8000c01a0005010b0841c0c200a0300c00d01060299501c6008009201165290309c0758290008440503170850f1700c02d0300200900c03102001502040b0750a84000c504506025000940f42c0001480d1711a124802c042c2826034075045504a07400707844010101090309a0f180800280840401000610507070844006885d070b404c04e00195100d01c0d03140d40594a56a610384055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 867165080 1250 867163830 867163841
    0x904140c0901050706110706020415090305120a111e070f0b190e1e03070503160302150c0d080f07181e1a190c0b0f0a020c1615020a0203030d 62
    0xc0c0c92032511b441b00e082c0c0009445000740662401400f0150f070f20b50a050b00b12144084040c1d0b070034200041340c0f40400110b000411107010702e40b201404169281503a50040f201c0c1c21030480c100005004d4141074008000d01d0040c0f4481c8482c1c50025206070550703450000442c41d48620809510101c208100c0c000b00340b00346244200f03c4241d00703010980d08200c03000b0a00f00328604907546255200808460040d140402a94004040403002005c140720101004918070a07107100003401444d10038500c141c01441142910807000340d00044030149000c04000070200e80d0107580c020201c0c641040800c0c40c480c0300301488203007113a4501801101c2850010070865080da981c94401c09034151090100c2d9480e9101c00c3d64118091001c40c0340d84604100c032040008481202c008401e012200c4411000102c2e441c603510b0f40700c01e0f1011000c00564660b0740e0440a48100c800b512464001c0d14000040300665800302c400350360b6074540140c10540007a40a0703a031a2251100039505d50300c2844544c84180c000d4000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 867166330 1250 867165080 867165083
    0xb03060102162d080a060603061a0d140f06070207030b06060703270504020c16060c020328080409090308010945121205190c02010e060c0904140c09010507 68
    0x1602181d5079904120341030441001045031744c03a032906c4023001071061740d025402c840001002045400a000400101d1803210004000c0100002c0708080c960041b0074050070000c0030304182130720001e03d0100e400035103031801c0c1c0c04112000c4c2d80f8040849ea8a0600368280d0b0307445641911041c0300c0300d1080319510132000314901d2004c22000344450100d01743d00d550000e070204505000040c0711031181440d8a813071041440c0c010704100000c14980c0301c0941d6000038114201605002c5d8401e1112810700c0b0311014031985800076008010000d400200c00e40350794481c41c00320b0700035503403105541d882c1c100a83c00d84401c07000f460b90107100c90310a20840160040c1c80c807081c02e14400c0e03607000c1ea0003100081d6202d489031038003612000c16003207000c0b0400703070090f0800126080b1140204500c1c54548e2203207040000c41d01100c040700b80e0345e404070501c0b40c0c005d44c40f03001c601000004645982c58007913b45940381d40204d140c64015030500484102c0c44444003a1070b40500640c0c0807081c01e2003c03640045502e030f00041c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 867167580 1250 867166330 867166409
    0x120d020c010608070b04030b0105040504030f0807020309040504111f08180c04060b03100605090303121e0a241a03040807120207090b100906140904060b0306010216 72
    0x2800103c030001004190000d1202c140581c0e190b81c654240591503090580c407207030090781494100000a90301c907514429200550800c12a55150400100c5c50350151a641070b0b0490302d0101444144001c1119021049070700b03c850601c641e44a002c4502c1d85000042c201003c01c54140125401e40c050800310741200056204480c03140800d0340020b01520b0050703205d00d440d44000424020f07080654610304020b048079081c181e10346041c50300801e60328443d2410303450511030080c01041d040380005040c4080c2000541d5100e501d420300d074164000400e000c00c180580038144480d990800300342c403030903041120b80c146132150b903490000e96054400c1d4001401110b02501c2085141d0002d5036610302e41800c148564000c1090b2400c02002c801107401c669081449480d554481034a00340d40301d26100c003610401c0c03801d24a10103140034104014001c810400d80c1c014109400424100280e501a502c6020243c0c201c0307442001d044900c108075211401000e0031464885031103040c0948141c40d80d0901c006800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 867168830 1250 867167580 867167591
    0x8160b0318011a040e0d022d242809020402070503070b09060a021912110708130504060803030f0408160327050a030215040e010f03060608120d020c01 66
    0x10202421a100c8500640e000c5410f03101001003030901d8807990503070608100007850f40504400001e0340d5414000000c900d01e150040c1c5604010000c5068140c2d44c55000c0100d0f9079480054400000300c000001c07480c15103410354030000703458104446030000110f6200b5101d00c0381e400e0030b09100d405010072a10680e001902008503400045040004201a500072852100700d4109a00310794242000504803c001600501c01c0b0000009071482400182c2d60504115114582c2c132801072015202c202d00b9418100d5001c22024140075100c0010107440c10041d0008401da03071550200000c4400300d0007800f0541d4024000281c44100b521809504035015640182c1040e6468400d40c00340d50001d01c0480005222250900700b100d034041d2400e40703005203182079509950802d40030958294040c40301a10601a00298400c840036040444d00941103030000074401d0742e190350640300d182e0064401160550700e072440014401348042106491400b4180d070a03450308000841d800080e4000400c68402c6541e42d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 867170080 1250 867168830 867168871
    0x50405151209060103030305070806090f0601020f1b0916020622060c0c0605100302012709241d07050903010e011b0e041503260301030606050a08160b03 67
    0x810710719100704040001031030150b0452500034217441018000c0b42c18040b00b1818030a041c0e0b01e007442c1c15400b1002425000595544400403450700c2c1d42424440b41078051143c846e01c20784115a4a0f01c101030055030820074980316614402c10500345600c1e2040180c0100c40451400d80d03800844410740354400c1d04c2840800c4030358841504a0f00b8588011000c120910300150801140d40100b9607c0040c41c1111205540b8603000a007401000b20907a0582c51065103d817078841c0c5150358290082c0080c4401048148840b50041251544031106c1840340c6000400004021550075288041035007640a40c041c1500c6401040d22160018145907500d035480390300c00001c4035400d1081a080d02054840300d041c0b0300d640d49015160b41400c2c0d00941c01141080d4400b04a00b0034000e0034030883c2c1e17000807004907030981c1900160505103910100c0d40301c6040000000207100d00c54001c1b8003900c1c0d086a01c2100e241d80c803900ca96440003205000000761202c1e400c10805110b004015590041c042c8200d040d048014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 867171330 1250 867170080 867170107
    0x12140703060e0a06050105042a020a080d090b0906100509060d021002010515041112090304151107060504080d1211040303051305010305130b13140f010f02090105040515 74
    0x22500500e02d55802940d5400601c102030240c81e00601c0140e804010b100300100c0d0210030000821301d00200080c680c03588a2174248208035454416070001c5101d40c50302038840040c40540414141624170210000114160302404030b54240500e51802042c40c0c803030715081c03d010108600500d4240e110500d00001000340c0c5031404400e0344040242c1c00010b04d4540380704464105500300c01818003403850203040c0c0c015110740e60100d542d81000004030340256034450001c20f00e1840b898005036045811403030b8014030140c101c40d09180502442080e50403d0b900c1e000201c81c81c0c0210310424060350303ca040741011983c01000c41c410700d40303804000458490109c194411650340540c1c011030000d800000c82d900c411600d82c009030050442407a05100a04000e40a0040200e1243c805403d20402001281d1501030542501c480d09174084455015846a130341b040351911000c20009036154209030041e030a00f2050700c21660340c0401610b409042034141414000c0400c1d650074441140b140412215892900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 867172580 1250 867171330 867171341
    0xd0314180a0f060c1202180d02060403020d0b090d08070c14070e09100e060106200f010c050a1704030504060f09050613170118240c0302030618011214070306 69
    0x3408041a80041104c0013040f02c2001d410346441c103881030080c0c401c0c1907501e010406030b40364201e03180b000f103603814000202c1034440d07070740001d40c0080108410720812801e81c081b0351003050084250384038925201300c00c0c0c40242c003c403414030028070000800000203401c5100e0520382d5040008640c003090f180c1042c1c1066080c240c8130080c1030350100600c02002190f500910907040740b2580a080d07a0352610074080c0c840c1c448001183c004009c007005e41d405031081000030080d045840c60090160591840e4058500d511070784041000a00400844040607200904d250086525035901c501d01445d100c0121000c803003030301140b010042c2051000a0350340c0c0d940d019124146600c0c1d5085c40c3c80d458060403080980c454a071411040c0d0401304002c050b01b440182e103070725561300300c030300c1c0359043c00ca12400c3c500b19070500f01103064986c078112000021a516901a5100e900244d41c1c1d203211401c03050501614000c24403529000041c0c01d1074580001c1c0010a16403900e00d0b402d41150103ca480350754036410f960 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 867173830 1250 867172580 867172583
    0x215070f03020f10090c060309031e05030f010b09010c0308060f0904080307032306040b060405040c180503150a090309050d081e1c0522050f0d0314180a0f 68
    0x1d021114030304100c0c0f000d2058100c00c0306404010030940240b540d45c551030000c140310b441c09040d962070079602414003079085c103807064851490119909521080140080d0804d0b240310311038580c02e5001180c0030402c10115082e01030140c42d0300051140d0782d5003c5601c80300080c00305400040404261000d51590aa120300031032150034429100e1904260003003c07111071031040070343c1080c14090f14550041150070b01742c1040b4107a40c08100f01c600031012034003d115030340c045a000703446c1142c5841542d40c030021000d9070f52400d55442c0000d81d035070710070513540e10501400c0c5078101c140240820800b0449034000c0810074483d042c112210b540d1a400140c00800075507040e44c2e0300d00006081c2000701600c8201000038002800b001e4200304040542c0110000c04040322040c460360355021450950700c1000e44080107049000c2c1c0c0100140c140b130026110a510402d24006d44202296040c1c4140a8092700780030750514040c0c240f42e5038802003c0300c0010704d00e0481407458040c03001804c0109200c0070490720080e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 867175080 1250 867173830 867173833
    0x106030203010b0a05010918061805090c041b081e0717060a0f1509090509070807090b0f060d090f080301230919061706040c120804030215070f0302 65
    0x51960061600351148030014520030700b100801440b480e038005405d40c05031402400e01c1c15074400c00358942c10080003190020640c03840500e20b11546401c054008a00c60500e003800e03203d01c030110506200c151001955102101d400380031460507494400c0e0b005591091452592085465510100f00281c5000b40c0712000022449000c01402130b52036a117080d08a04141c1c2c40c01c0f101890020130b610100b066005001c60700100885070240b892051040002a2034210b00811440c208490728958410176403040e10381d43d0084c0e080000c4d85403918441c03886016405000b903010b101408007040f540703910801040c40c40036621a2200007240c81308940f000c00390312899802d03a8a50410080e4040301c691190114074885038001100f0380c1741c85040c1e440e43c101c081d4400e105c0c8204180c0b900034002d04225080861441d51703c03e0032040d031410015402e401030b03004010300f902060329103071601d002c5024180d0182440ca000c100c10401414207452180030210207581d801c4c140241a625140700c60b030703921800da005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 867176330 1250 867175080 867175091
    0x114300a0201080c0901021f0e0d020c040c08090d03090f05030d050402040e030a020a080307300506010203040f1a070b0f0108192a030c08010f05010f03031e050c0f01 73
    0x315600010f00f503420a05401d11681071004820000307540b440c5c3c2c0180c40c032029400c004d45200b00c0100d5041a62000c00032000c0d200c2c2440080c0000f5640d50b501809940300c2d9013082d02c08040b80b0702402d085406050240042d0441d40c42e4940160007915026101b26282e00080c00004003190701400540202440039002141a042c0303401044282c459101200c14543c0040280741c54841e0009496001103901c580442c0c0c0700d81d42d040c425650039072066800d151020380c1a048501c05500507003011818004d8032010042920360b0001260340c0d010300e0040c007000070714090727060000303003086403d0749101c40d8031603501c0e460708007982e940c09282c1006440c09940c0d9a80140140000700041c0900c0301c2c2c0b5401c0304c07600c480400d40c546418803044003020384921100102068014034070007206280c4065500078450800d0541d03912130083c001c3c01c50304a1841650718000010071424000c201017012283c04d40d941040c28410f10b0350030720344011500c038110240401003080b91041c6005100c94801c1171181c400000c0d9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 867177580 1250 867176330 867176333
    0xa170708060a0c0e0f1e12030a0507021305060109060c05030f0703200102090f040f09080f04031a04031d0307031502070c0f050616150f0c020c01080114300a 69
    0x41c44ca06008038450701030243c03588010380760001a55610500802d0b0701c070f44030602030007041100c0030310003049002e40800501d00c0d40047d0404001c26426100340c5076483d00b0041c00322a541100c8068407a10b0000300909010003e16115000f9504414001e07030540340307095034030b04184a00d5400b100e8114080703a40324032280c5083c8410a079542150038108000d500d014a204001407051803144851481181c1c0c0f8a1220310700e0f04658800040d0560203070308195a01c14003070046003503410074881100c81e402e500c8129425a00400a0345010b071b0351549420101080301012a913080520134005078242c0b041c011b00201003404c44015600030600e18500603aa00030034104401c4400c40307034010340007030302c02000104016224501124120810500e10b18642055403800e1030754181100c110780d0046003408040d5100c0d007060752150003020103035001c64900b0384140006542444092044103c1c0941c07581c1d582c013990400d4101840001c0360761030805540744e003690109080070b0202d0340e201c0003079104207007490 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 867178830 1250 867177580 867177587
    0x2402041d040218010b0415020a020a030609170c0a030507051c0807092103180b0f040e070c0f1707080f0409060501050705060606090d0203030703020f01050a0b0a170708060a0c 77
    0x1100e483c0035001c06000e6050140c4212240310f07600c0b1b50284442440d80d00343d0804d109111441010fa0f0040115031280c1e42d1303080c41070142a01ea00280c1e40042c4034921039400348001d40407644100e240d84040d0031404002c1c0c4041e246230f0000d04040d100360041e0785049114070315000b2030500000742d6403030b211801e050407440200742c90582c4d040844d032401d100102c0400d908500108160060f070500d844131070005c04001c84410711f61980d01c11306c03d521000c18a99650060800640f058606c0e00c807400002c0e543c2d5880455034115042809010000c64040d12030128140f101c886810001c419402854808a0742d07a00c4400e42c8441c400740f2107444040303020f0140e584140500d070300070102480d111b410485680c88003030700c4480191510784501e50000340c8818039107955090540d0142c00409490300c81c82c1904002c0e4440d05845041d191951a1000042e407210140c880c8910408000d40b0540c113844c100303074007080003a07502500e50340b25201314680082c0d0740c081004064803642040002060b40c9240500c00b9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 867180080 1250 867178830 867178849
    0x206010504181412030c04050108100e181f0e0705030f100c090302153406020903030f030709060e0922020d08040603021206040501032402041d0402 65
    0x2501c11401c282d00d0b10b01d00c9540007110340c00705400024440c8140700c0c40c2c800300d107803a000094907051500044200b02c03280d03400c94041c004a403c20380b14903405650f005011900d01d0032602074140701c00b81c200c000c40d4109100c070b0170a4094412280440c0c0c848007500c5914560f502c95981d844a1480d00c0d009000c01000040c0840c0c0014002030340100144036141040741d0302c0b0340c80300800340007403036891510b00241d901c1020300c040150740241c0990408982e69070380701c106904c11500d00320303100124100f810343c04000422131f1005000d0481c03524402052030790f808002c0d40c4a80f1407160f25100511602c603080e01c44100542c0541d1040d00c582c1c041625110010b000c3c03103c8890300e40d1050001e00200110541c5a1960f1150728001d80c0744240b040100d0710000b010058401406401007101103001b05400d0381690040801c40009100d0003110747c0e8a40c10001969000d00001b030081c1241d0820f019440c005d1420f4104044082d6009070030b26480703120b100c15a032115904420091005400d1000798100f040e400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 867181330 1250 867180080 867180089
    0x90111030d0b12030705030901270303030c020d23210c040303120b100309030522050a081f02070201090e090c040e0316080d110c030c0d170402150d0219020601 70
    0x41c4d810144286c0b907240c0c03240565841c0d181448002c0008940143c190792544c1c50440f0001c20702044192241002401044600da07580054481e0780c08503407140b400f4680341110501640c40000761a13029614004a41d0400c490411010415400e102040006150144c1c420110100e084c0d1301c1c0c5103513040c000d1940907000a9200403030f180c141d0b0031a8039126400c43e064040b140307050110b0400e07964a0102c0300c85c441c1009c1188002d0142e105400c8140d01492003108482c0304581207044981c5960100380c0361829400300700301d001b0440018203803220294018290150050600c221070b10b617100f2424080801c11640c505d801d4019001d14100b80c80c1601c980d00452620000940c2420000002c0607140407241d0f0003d4a1070f000480c107540070b546540c10510074400f401544a0b201c0380c6000300d0710340d40d40150b00e18400314003480724181c4240e40700b081e4141504000b55400d0701c55480d6030b001c4c8040d008110740b12030000344003007142c070740e00c101940020002c0e8080184441800446010020b00f05a4107800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 867182580 1250 867181330 867181333
    0x30e0607030e09180f0d030c090e161b12021002070f15020d090b060f01030e1203070c29010f06090506091c08071a0714090111030d0b12 60
    0x2100c004640e000c101055850401e4650350ba440e2078501d06030007035800c078a41c00780ea28428a080a0940600400e000d040a102c0e62000c0c032a108102d4800d454080a50107a4242c00344c6110005d2841c004424107003038101c2030780c244010741e8407031b260724140042c010701411348844025808540d9019810802401c4031040708204509041480d0b8941c8401c0142c51806080d507612511010785c2c0701000c0e41200c1340b241c4c0d4044100041c42c070a2400c001190401c6802902c00c03502c029003103845500030301500b2085010000039041c51101c0c103c0104468001416070720410104008050000e080d044001e0024108240d210b4100215180341c90b1100f130050704081070020035050104000381d008a1461300381c8508031503542e00c44c403602c00841c2d0b07a90143d44c1100d0b5100c03200d0820b28140803d003030080c028140141081e0048600b404140c445000d42034611400050f140114410100032160207002c03820014500003041050040e00d017480c541084103401480da0380e46110000c3e07407802174800c2601d85038100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 867183830 1250 867182580 867182587
    0x110102120a180b0d0e101b0f0908011d0c010311030a2d0603030807053417031503060402180c040b0a03091e02092706040f030e06 57
    0x22500e405005100e002414020308802122030607440d000d1080107404002c00303054482c81d25040c0c40010b02100f280840d03d6010702d1896140c0b08101e800b540e103500d08502290641040c054000300c03a00260600c5810030820329900c042103040302802441501c444045820344c03000440b010342c608150054840c203050501e884182003100c03990005899001101c07139000561002d04880a88a07210702c2d1101d2644002d0710210000901c0b0594404401e9034000c2c2e9a1401e00d03590303404180ea1500c96080a034905110707c1082504010401000c000602040410b0400c064a80d076660804011000c2d0201300c4080d010041100b5400c414402e080341d100118001c000304d040c99000f084904505a800040b028600740004603880c00c020110b900038442c3d4240d003540c40180b088018000c100c01c0700d0407110b4580c014001d0544030b210808105440c0c0e0024440601e984841c202600c94542c400141510300a503103005603c5090144078051040e402221401522a13080c1390040800d44103a109901c1000d090 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 867185080 1250 867183830 867183853
    0x10509010e0f0c09010c081308010606050f04050904110607060b0907031509051e0901050402041a0108130606050a0803070b010b040810090f020402031315020a020d030f150f03110102 80
    0x1400ca503500000503400710f95992400000403601c084480c640603041c00700000d08442e035080044c2d000c8044030005c1c802044240e444030b00440f418810400044401c240521090007189003480b145504148a110300c4240c80100344003040454014210540703c0c00e50b26080e011450400c1c1c5c10440d404032991604100740c012040515540320114050321a1456440d0001603030580c04034113525003125141a52211840c00b0a0076502030802198100e0185041103007620750904080c046900040c8161507120f4a030762050300003903003491131600585642c0c0d110b40c400038213a100c4c003001d032005d040103402450b41c1b038820382480c032098001030b442817000c800100030400c681c4038045003d00c44680b0184000c1000517480c1090310a524081102a50080c0b000050145080c5034003502c1d00200d11400c0c08020381e0460308803150807405900c4884015070014101c0c07102c194801e40c003101083e801c9290010312151503542001e04404039404c4440a001e030205c003401400312000c00648101805d10083c004072042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 867186330 1250 867185080 867185101
    0x32b0e0606012a081306030b0f1005030613020c0a1a1e070504150e0f01090503060c0906040e01140a080f1002030903160303150f0b0304120210050c03010509010e 71
    0xb00c810103c0e61800c07143d09411060325242c1400041c5411200c1c0c50b032240c1920b01e0b903082006241c403030280440d1070f1007501c101328105221240c11030080207201450701d40c2d103c84d050b00e0f03c0c3d100420403603101ca44101071001b1800302c0d1000d0290013079a000100f008851078904070840b60745802d5504c0029080e80304003c19090060302940159804601c83d2049d038941081c1641c140c000d6070071446100880231140c0f0300303c641c041828001124119021605880c00c8001581d400ca0306010300740d05038220800286c1101300d035038000c2041c030078094066440c25030f607100801506e41d002c0c2c201c40da01801e80300d95110a4a00340042c1d002800a0b42c010b4030601c000d9a040694840000007420740c2c00e0380100010324601004d000b6214001e02451f0351210744016803600038024004880058200c4000490119002040c54007010581d0341d5100054519240c2e501d52503a4100c2d144524001c51007555500e40c1189128080d60b030045c0b009210094895041804006a6442c141c020b40c9011504034100110440d9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 867187580 1250 867186330 867186347
    0x203010f14030a151a040e1b180c1e0309070e1306090c091a060403080d020405130906050a020906030a0b03010b1909060b070c0e0702032b0e060601 65
    0x3030074500c500101c0041c5000c0303400c1440003403002c1d00014590012810604840d0009001091000c0740d0b48003a01862042200310b0b400c4503807c000551007a05a8103020030f90385850900071100400286010030680c503912002042100c4407000f80c5408520445444582c1140380d81011140744003d081d880c000d680709236105d2642c130034820242000c83c00702c1c03002481c4042e540c3e00d007500702c441801910301c0c608110407450414412007195074900790800c00a10038690420060f80c00042405240c60301c0e50721990450381003980c1e06412158208000221503035480480324510307000350700204034400141000011202c0c01003894405a00411510340b2680d81c9204070380d40f02403502e0f40000c0705034a44000c60b0040184003001d64011030810024080d1382060106801103559180e003d101041e1504604002401360840080204442c4941480095594107400394840054411030741800a15004508401e440c00c2c0b031020316030032440070003a0103078590141040b07440c03242000b0049030602c500000c0c0f9681 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 867188830 1250 867187580 867187589
    0x8100b212206090309051e03061501140705070e0f0702010c030605010c0818091e06030d080c25141501030209160e0904050705090106091d07020a0f061a040203010f 72
    0x69940d4000401c06015402c400301511014218000e85081011501507c40030042c030715100b44621400242c0a00420501060142040c0c0d00e0082c0713800d10070a0260780343c001c41c404035103034050540041103028501c480c05100d0100c200c075464003418900d101a085072402d020396420142070a41c140306598100703400043c4283d100340c0131030381e90b20752914888000301c1c1882000e601050100900141d03c110300300710641c1c136108043c2614bc54580004050741e460300746414070041058480024085212000600710f400910504d00131520001000d1183d035807400d00c070486840003d100c8103c0c202d1410070400c042e8010305c003110842c43d41503800040f00f075030008007401080e180301c000c0c0e1902d0b13620405d200003000d040075054210700d080c140b030304507180c1c152401020b0092843c0c00000034050f1042c003c442c00c40e0090b18407511842c203d62102404810020071120540c4100030314200080c6600691254444c0100c00010300090b403500d22944400d800001d85101d00e00520040c001008204889421107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 867190080 1250 867188830 867188843
    0xf101413080f0a1b12090e06031b030f0a0b071d010e0616020303130806160c03200a0609061b09090e01180c0e061c0308100b2122 57
    0x20440510111076520800b44e518a404202050707101c20000c1418040d001c04200740c4809013903e03220880c84841800071035010343d240c0d0003000d401d29941c0301c03d10f1440c0304020140a9030304518000a80900d08039030150100c5401030b01004000c1c001c0c2c2d000000c0b904034401307524400d0907104082d00080000215401c600e01c6448001521264140e07402c41d12440c156028064279154489113482000d20031480c03290b1142d82c0100c0000a00519110b5800c3c501e072041e917100c800b85400b190310112869010b422a80a650886110b0940c40307207000c101c20b006480c4103032404500d50310113182950680d4203c044000100901c200e030910220b400220304010f44144007800680da898007880d41f4007400c90665091110030440c1d00b000b003404402c0742240103030350480c0340380391590721210284440b40301c1c103108946004002035013560000f031060403010b8111142550408506803030b40c1c0340c2c3d03231180d20100c1d00c40100d824040b02c00c3c1c00d514008400c50350050f00e2002440a0600898040100b407001e184020410b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 867191330 1250 867190080 867190087
    0x5060f010f021f0218060c0303011404061809061a030c1522140603190c0e040c05070b1803030708070504180911041e0207050f101413080f 61
    0x700c0e8400c2109010081110f804081e80301c5400c0c14110095015502d0b00051800c64040000c003810071008640544a0707203402149580e1030140c052800c6007000c2c1c24035038050f49810300011b2800c840e62068100c600d056900044140e00d9241003001c0310f0384042c074501d40425280c0214007a40e4040707200b50b8501e01c2911000c0381c0c0f440a5520354424071403040a40b40c0050f0500c4c02d83d40468202d80b00105450510018213100414101000783c140400c582d05c0f1900ca03e08000043c956105400ca00600c1000c1d0500c02e01405068001805640318982d4940010b0000300e0f1000900c40300b445660303008a10100f2003261078801e0542e40c0d44a10001f0411b50502c021980410301a911034011180108440008220385a04003001000038041c034910668281510990003490f6140c40e01c03829100003641e91f0010b0714212114009000713900010015221401041c809030140031b8140b03c424100c40030034500181c3c00c80340701600c450840010301207094840808040350000307146101122540d0b4101d00307150740c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 867192580 1250 867191330 867191357
    0x1050d0b03030d05041202211b0c030d180905060d030c1703090d120203061f030b0a090207030801060810120c03050a23120409021612080f060405060f01 67
    0xa10310500c0c03c4119150314001c1000103000c04598010039007041d59003600c00044210000f05000060391603e000d540c1401c21040d200b002d1904905020ba000f0b1005481c81c060010001074200303090310080d00c0224800b010b8000b584c0c000c40344088058203542104105904201d008034448a0304a1401001e00c071441c14150240048040002e05252014004950300d03d0005001070316000f402c00c2c0c480224030743c1c00b20381400ca0100c1c025684200c0024016048880d8140040700064003100ca00c58241550349210070131945420300c00030b01500503a03902680c5c444040c6030041074044141e00840402500b5400c1c0300c288070b501c2034600c085a2040750441d0102e402400d02060052107540000c00e0b6104901c82c8800b00b04101240e000f11580707008030310040f00f0201e0702d440e4460400e1001d41a050303508000a000510700e40c0c1c0904450320007440d0340d2012101d5641c030028040285200440852310720010041803025810089900040545042c070150500d8400704080700c8903c00b41d00d040c480e00035401c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 867193830 1250 867192580 867192583
    0x70b0606070503162001110a03120204050406060c0203190b040803062b1a06151315090305071a0a0f11060109061d100626010e0105090a060501050d0b03 67
    0x600440368128130039540303d400e1a003988080c01c1400c071290442da601e02840754660240034118880281d060107030007a01301c50342d0101d40d90b075410021104299802d004c0800c068482c1c2c402d95020340080d1b29004125030440c010149810f160110849990354211014400104103079400341e04947e1028420780c40752640c0c1d00285101c030054004402e07510041d0b0f0070096180f84005001d900714040d1185861308c10703038045090a6039208650558008000381c0b4000315019480e8010049400b0b4403c0d02c40e441030300d5401c0180d006110000b9500040d5000070140144001405040003c08203103083c11000c0203000d510740c00343c0c0164071030002030002d950351641c0010b006070b180c81c103100040300640c0c0b121340c0c44801d2000201602e021310300394400d00043c40d10203107040005490049120800b103120321441c00350111600c2100c254030031030400d6403284920380300c0070090083c0d0290040c020310510303a40c101000d119402ca001080340c00b107181000810007072640c0103801c43c0d03441110141d020420300b8007400402d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 867195080 1250 867193830 867193837
    0x303010821070f0c291c110d05011a0a0c1101020c1201062102130b031906021c1e0b0103240905071106070c060e0d180506070b0606070503 61
    0x40d01c5601d002100310200515049850300355042c1c2c44e403d034404840b1710303001310100011000e05002c0403402c0204144420800302c00c0030001340e070000d020500091302404000d460b08490b612160858560006208598401c0314045840c00c21903071660800a500c1e0004003c08a42c0001a00e0880800c10188e5a40d109100101e034007440075016607404641c800346103000307250720701ca0189000080e940052024904139500b1030115002400d480319100703038404400081040c0c80c441c0da8580301714452050074250443c409440716004070801a200c5244207662000c90030003101011149103800d401815408200250580c445100680000c82401000050b002802d1140340d040400038500c8010b80e02d5800c0300c80500c25207881050a009588a81c0e4050340e507041d400030351a24a400c544001400288280d40c0d6910960080b113010604840d2000018285100700e804100051500d812800200610b4074030741c03005240645149181c068141c85003c2e0030315002c0e2800e031041c800041c0c4002440810001e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 867196330 1250 867195080 867195083
    0x20405070f320a2a031211070b0406060f14060a031d0f25050307090207030509090411011701080706180e07020d170408071506030c060917030301082107 67
    0x350b581c1d64050400c060003150003010560741e5494481e022078200065401c080301e00543c9520b0b40724030355104c00c550340043c00e01d59040115404003481440003040b040004503005901410000440b1801c002c4840f42c400c0e6250410180c41c00620034015040d04c51408440c0b002801e864002940c643d0140c44c0c258008906000401c03070720881c401c41e080da0102003a140740e140c00100030320107c42e024040312004440300c0d100d9190325801004081082c00e5450700182001d0380b291411a1600c0041000209201c805841c10340745145550000116560800b0034822000102e0b000c0742690340c036100156950306281d00598080005010303100b1820481e2207141c1010b018240c400403198540310400035550f04d10004c013400080c1c8400f183d031401458000b4141d00998000301190302e80900340d241c0e00903140c1e05005c40503096a84040000220320549019800b424580e82c44c4140241351041c0010f8000410490302c685804c10001006aa40c0c00150602289000e80001410080c601c01d254014051b0210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 867197580 1250 867196330 867196427
    0x4020418062907141f18051c0e04020f0403061a030c0f010207080a08090126060603060f040905071701180f080d18210801090203101a07020405070f 65
    0xc1d171800400958846100220038a0760410140c81c802030b450700c07440d01c2c401e00500107821406031041030748004030b000040d2200380d04007441b070f022880000c1030407039109081004891202207024410007105000b401a003101818002d90084070180c002030b2075402e0a01040d20540f0b40c041e02e1003003640284032030300043c0700d90002d480948004c0d0405803003903800b0044c03c90009022091a1400021803400c41c0801c100c95001c14603240d0301d050500510b640080c20280d1320001c1c54000e800103503190b00600349524401d0000c0c2070780c10300d040e000310007607003004142d40141d03410200740310270450f001041c45841e070b500900c0324041a9020f04048200e031141409402600e4240104d649840921407405041103121706004100020300f64603a05490820001250000d9055001001344a445030042c54020400d90301004846954607100906450211b10321007465a000c90118190714141c4074082d4813464038100303e0261182d6503401030688843c1014000700c000704081d400000e002d40c40c4804803100c50b050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 867198830 1250 867197580 867197593
    0x708180402092b0602030f07030c080907060f030f090f0c171b1c0c030210050f03070c0204060518011802030609071101090b0c07050f01061406070602090402041806290714 75
    0x1050148040800c503004030109c4d0801d862019001c0c0705035003041c071405580014201c000d00b0581c0132190309500292101c10191292101d07480725460b0702c56802c107240b2908000d000c2d0940c6192804103c4226400903010607a0000811840368002c0782c0c00c10700c1850021000c064118074000142d6500f40410180c00e4141e56082c1041002026604001901d000321100c400f80c01d10050110f506108003c41090318050a0001c00c07240c0340120001c5c0c002c5440140041013007a11400800c0004500d00c4246940c00d00e104010007401c1c400e681020444c9119040c254554a00076010824500002d48850704022030016003038440c010a500c41e0a80790350080740704443d42001030010305c10780c0080c00d0a803003600904180b59140081445240200c0704400741c030030303c0c1d2500748003003114540100006031580c6400f0000191243d03901d100910207020129241c10640202c10301c4036044642030781000c04201510391492051011004018410104402025655440d103190444117428003103590000d80c81a130 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 867200080 1250 867198830 867198841
    0x21312080703020f0307031b11041a041104060c031404030b10051206012402030d053c0c03060609040603080d0f090f080a11030708180402092b060203 66
    0x103001420194000d0b804c5811102c041c441107500c034450b1000c010040b40040208080100410714401000da01032160560041032101c0032906032100f09428500c043c1c0c074500e005005180c144070780e01c454400d65152904080c1803c5019004101c0f1030740240601204880c40c001104507042110007955001d00c0d00222828a03094002603092240200e034402c00b410b50303000724010400690130b0b040b03a0120090034500c240002c0c0044038a410910600c045000c10040307080310000900405000e039100540000f1644030040701c6c2c1e070440c80c0210001070300c00175422000a410150141154200303c007001c00c4c81da2034489000040092044d8000c0d6070300141403d50020038084144054007411480c04018461840842242c00480d50684d00c010702100060808d100451146005465039403190700303100c0c0c081d92000d280d980c03441c0c00c800c00444640100283c049400c0111071201c4401010039281503041c10310302c400195000015a050794130401113000a4580507100703150300d01c22030350400c03000c5513a81042c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 867201330 1250 867200080 867200093
    0xf03080403020a09050f0a0b040b030303040f02030f0604030e010806060c10090c080a03120c030b0a12120e09131b12110a0b0f09011806030e06010602030c03040504021312 75
    0x1d1000341c0c4100c40c3d14600003441600360040921030703002c07a121a0901d550b000c000310020300115602d035030015600d00c002041038400300000d6000d40c1c0034803540032001a1502c1014503201110884e4003058012900b84000290410400c501310042402c00d2006540d8400c042031a070300445090550501c14072040a14030101c0d6130002d0f4019004403200d00507103464428103950b800c10000001c0000e0210045d910800245030b01c00301e5500e000c7d203030206945021800041c0000926000714006030b036000d0000040044c0c901404030071401c2404c0844421a2050004030030f10b5000b08410402241e0011800c1005000500d001c014885030042803001031b02c4d40c5120220002141003142d04410340707508540c1702c2c50b01909003811030703101619952400d07880f5184901d540d040000302c04e040c4804001c402c64100741842065000c1c0c020b41d40d0000c6c03080400d503c982c3c5460010b078010004d54004100107011a080482241c1c1034440a46015a450041000c580c0040c0103540c055038007070310420f400a041004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 867202580 1250 867201330 867201337
    0x6350f2a0d0819051606020d020904020a0207170106050f060c070312020c0f040b030604081605032b060e0a0903020c03030f0c0d05120109091e0602030115050c06040602130f0308 78
    0xc841c0204001004102c206403031a00c10080e42640080c010f680b80390000311b02c0d800030000707200106000350900100d03030041002e9070070402400016030026034080c440350043e0014004010030150007800140c0c40e00c400f007012840e202c24028000da030000364021501c1000c00c0004000c550111031001c6c104000301e0025182c405a00c00a80704141101c0240034500d41405a159004001400f4100507250341d6590182540400443d880c8075045503e600d0100300140040c0070f20b03c203910203e6000c0400f000d82d8030410800c41c00f6140e101e515108081c0400341229400a41c459016000041d201d909418203902e801030300000382c1d5040c800001e201c0e110300450009042c03c040d29408461204548210640d00b5002d40812216000c9c41e0f00c0c0100305184076071300b00080035805000c0103020509102905003502035460015100c094001004019445079014481e20300724ac10301e0094107001c69524140e4641e08060006410b80d0340110304100410307000d4000d04d00500d1a500c07070540003aa2803804044580 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 867203830 1250 867202580 867202597
    0x40b06061603081b0705030405040c0903050a06060e06041401090b03032a0607020f0c190b13030c090e030711041506090915031a0a06350f2a0d08 64
    0x60240300c003035443c11005045c0e035100da920002850401e810301c1c0602005003180c1000e002000f00d2190000040b60f0300f4000100481c2c06444003184180c10720030030140418000d0030060040e40b030500f1000900d0400031285041d200d2000d004240350105200091841c06070050404204070505000f609921880c40c0341d0344400e4100b01900d100751750300d68041c6d031621040070605140790843c8540c02c045240414038240c20f82c40380c40380400034545510a81e25183c200c808070480d80032035001c00780140b01207a4085001040b402c0001e00100c0300f013110703180e201d001304040140b04003440058485035682e50740200c0003071300c01e11812002d0aa980e07000242440e00a20070300018614003482c80c034101c0600000d01040e030b03420042d40c1c43c0b800711510a4284058008084414141d038500c0e020502181541090386500710740250344514007040e440075403c0b0400003d0080840c0d1000c20414a00c510200301406058a40d03000e030b4000f8940000600c2000f450302d0500e41c0d120340441c8100c0108035100c0c000c1c00c0d40c0b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 867205080 1250 867203830 867203851
    0x402031216030c0303060306020d020918101202040b061909080d0905010507051f0f0e073206030f090d02060432070b040302032103040b0606160308 65
    0xd1104900020368807515011a07000c100c100350110201e80905500f1910340c1c0f10b445c0c002095640e079140c641c00c90b0041c01019200135000200e41d4514503140541054220f0a4105288142002019150b00105074810003400f003031083c100741c0645d583d95115000108010700840c2d03413000031441d0305414140244150000c11091800420a0381c000546004160596192625400d0400700152926000400211042c1c420402e82803103240510309411b069181d600004600032103c4008481517840044040354aa4081d0700104070003804501c2e41801001c41d40e10398280701d50b20382c00c81150745810756820f40d0024030002c00c2c00600c48400f50b00512800f8024107464800c20041c80c12629841e06031009064908403e641031002102c01a2000546040901071010600341e10b81543c00c1600c1d40d8428101c6220100d810802c0d814148412141a01c1d14865400e18280c010207d03452808080c1018020008610008034640c0b9142c0488521114145084000051501e4000c040c11000c9130800c00c503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 867206330 1250 867205080 867205093
    0x609120203031e01060801060c140d050903120f0d0914070303090f0602010c140a020a17040e0105031f11090916090501030e0a060e030403020a08030c12040501051e041805040203 78
    0x400c03c400c090345050f900f1300d0b0b680d0702d0164030380302c0211070f4050201c2d0240e40820004003500c1d144a41004401c007901e07196200d560310740c0d64000c00c00d814045804001000e1210070415045682c009004845070100202c0c03002448603507504004175002d000c100740c0c0a00c3e124044000c014541c001e0119400c0301c2484a403141c030703c1d40350780c8200d083c6c8d40c5201e01003001c40d201040f041606021100981040c082c2e91044440c01d0a0540720707071600e107104410300301000800160501c4000030600070140904001d07402841d00503284000d52003184001400b030780344a507035007500e54102554201280c1020500a2070740c4500d05100c0304913042e04540140602c00f20b40c1e030100000341c55000c0d02800d21081c40c4040900a03100241d04c03524050b198490300002140010440840166540080c86020b402104021900d40705040b04003480c05401b07802540d01380100b48410032017170b80d212084500e080c10310668640f5100c981540711201e40141d8001201001c0c01c002e00c0098418150b00861007203008900300c030386d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 867207580 1250 867206330 867206371
    0x91a09010f18230106090e060106022409075f0a0b0705030c060919060e10020d090b0f0907030807050f07060305010305060f010b040909060912020303 66
    0x1c540407841001a500300205a000205a030f20403c14084081008881d41440d811403415084130f01d20f40014480950ba20a04207111300c2c1044114050240d0340001c065048450b0300707070305c4510340c000c04110b005010440001d0200310240030140042c603036151403840129112019141152147c0b46102110364001c002a41c154440d043d10246c04010710000c91001010100140d484030b070400b00c3d140c21105279200042c0303040792031006140c250300800156480d10032520405040c1440a850540150b1244920810180f401043c0a100c036902000004030a032140d80c82034142030700320742c138040c1084c0b0204815484802d25003024044612600c4100c10030342d500000c2345103400c029a5030035501e0303004940920016040c1030081c9040f40c0524110340c1d031140741c2031196203000c0b0590400701c0001d4a600040080200070401140c00c03c200058400e055814003a98101070300451107940511500c0d1140f480c203110680c1d0090b000701d90400c1e028070503600f00240c042d6a03030b4800d440f00083e1070b00c0144001d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 867208830 1250 867207580 867207611
    0x11d060a05101e0b030f04260306060306031c020d02070501051306030c02120c0a0209090114040201140c01020d06060e010203070c0e0a020c060f0403081e0118091a0901 74
    0x42c42541c1e48403007440c05a0400c0d4045210320742800390030020100000011a01c0d010103000756106030000241210030380f41514040c0d050100502c07043d071048a101841300003070340c4040196a8425020780303080b030b103955920f40041d107441501080004000311201d2940ae10f55400b28250103003007216000c5441c0182e813540111940c2c484c410105110300008141848400e109400400720780a0030710444903220f0904144c1c0741180d00500b100e4056030b0020300d0820071414901c10740c03680048404002c01c6988080110760002090090000341080b40004040301c0b854410002c3d5500e50003004000c645a000d4882c07401e0042042d8012100400c281000307034095584000129a10180e0007a0f09051091400108040070b01000c1c240b0000150244600b225020301003100502c14410681c14804a007024100030306080c0b0058607220244220400422588180b42d143c01d04581200300809503006001515100821191200400303024840e4601c4606030041400b881c040e08bc044001c1108000700008072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 867210080 1250 867208830 867208841
    0x6120308010e040302070f15030c0507020d11121f05010b0418020a0e060a050307120b03031204080d1b0908030a1209170309010903120b01051911011d060a 68
    0x2000110000010b01480e09100c0300d10380c2007403090040b034031071648076552200c8021440c1c000e005000020242601c1c1254940525181c4c80391301d040162600c41680c011a0a00c04040b5026104465006204281d5150114051026900c0e4020754081c4000c054102d0300300e60388040440103040c100000800d000c2034003000c480441d0000c1c6122021403015840d040d010750441040d038800c1c80136044949103140c40700401842800a45d0703503038076034078684500050880280c6500107400030b0310f440000e0242c0d490001c11144085d00300181501c1c41d5496140c1101c15100d806001d0204908000c03a00014049159010200d82d1541e100c0722412078640460a50303e0180d00c1c00100081d403143c6031105900300302e07489400042e004071072280c2d2001185070818810303841a81d803102c09039903d0031b07030382e05050340030303203812140603c4d10b40c1031040c034070340e10002084d034007454600d030315020014421039120074042e140c4208064660740007440040700c00c3c207850406e1002d2044900c0319026240010300304200768480c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 867211330 1250 867210080 867210083
    0xb211f0207110a060c120e150c060a0908160f0204020705031e03072c041d0c19030605130b040f1101050702030a0308060604210210090f0608040c03020d060f0612 71
    0x21078411301c071991160042c0200c2d0405000600c40c1428055080391101a000c8000c1c3e17105c84a120ba0f2030301c80c4c41c10642b5051006002000301c034540070a010001c1ea0703030011101c1143e10000c43c84a05055810510010b80503a04001e502c21310000d808000c03c0b101001402004104114080e26800304c0c1c40071041c5440300700c401d8800a034030f48a8140700d44507120004000203441004e00800e40018402060032146200080c20040c0c20900441c080075030100541c1c008100c096031202951006140c0420b114825404010112512003001825000f0305c1a0800c9242c2d42101004045003018107049189803c01c0209036042500c031701c0300101c46d5000d03900715811b4981c00b074001c0000310601c3e2406c6480f554003070010707a03005030100300014905440b1458030b43c0d0b82031141c0c544200584075204102046031201d0f000c01c00e108948108000c9210214140f00403550380c1d00300030040e030740c90b4507104c160440c242e00005c0d48419030840c65800e004695000c000310300304c2a40b00300a159142ea2003468140c502400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 867212580 1250 867211330 867211337
    0xf06120c0b04061e120c02100501050a1220061201080d0c080307030902280519180b040b0604060e09010806060d0305070609020307120c090b211f0207110a06 69
    0xe4101028205200140a126260139050845d0001c8030006480341490500c00692204d0384515035190b4031710541d401054116039521041d4644003548004102d40000901540d9015660444200070410130b078a003500010600d84d80c40300400040040c4c0d01c000e001c1c11045110b4140e1000d201d900543c1d1a6040c590040d441e2800c560380e501e012030141004e94002c0b0307080442c0c00403440e0620284000d6215072010441e0340700d201400e00f42407040416112850720a01e0030082d4080180c401a5805a0b2a422950401056452a110102e03001c0e040242049400c00000079000031130a038031000c0c584601604403a52100c43c2d980700401d598805040d40c42d154401c4281d40305000003400342c0700410301e1034400d10340882c40403113540000e410900540e000d04441d11000b80c601080101c55194540501012078040100c45000804664004444034000140442494150307604020820080200303120006580441ca81e40b060a9000394100c0c1c0b0080361914031100500016182035401a401c1e2076060343d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 867213830 1250 867212580 867212597
    0x1806090b0f030a0b2110050411011107080d050d05090106052805030a060c140403240213060201020405030708030f030f19180c0e0f0c030a0f06120c0b0406 68
    0xc4115110382c805031000d00340d1969a020b008070364035000c0441500080c10284417541c01107183e04142801a0f040e600060f803480d00d13040000144021a0001030403400b031901800e011000b40149183c041d0340e400400052080c09003c100c1d0b0703944600100101078144200317101a0315244c07040c0742030b1440e03030184542c080b6220108814117410540c0050015140682803424241e4480209041c500c10802c240c41c00c5465503011100d480e0402c0b1001c0440610801e20340c50309255450f030790101440d00da00c0300110a01c07000b42a0308103546405942c040d4501820040743d032541e0340c40280c000d620500c0382900074042c0490020390180048141d500044109103c2d03850340d582e4000c1400786403001003402d070349841c80850410001805120701c44102200310102c401c0d0403050304181244c4192039020f10910110f003030801041c240054903198000b108100710644030303220840000d0140815001001c0214500000010354a08082001c40040d020300700240203951030300c5078402144554015400440c0404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 867215080 1250 867213830 867213847
    0x2100f1409010e0d1a060108040f03030218062a010c200f030d06091103090c0405103303020a0c1b0e07050c07050103060815251806090b 60
    0x300000d1007a41814034000c001c2665410008281e40a00502039a40241c3c1d61100c5041c2d02d05001d4454200c40c003400c08440c10b1500e030b92202d1b12450440002010140c01068182264698104400b20340364010b0030243c0744c91440f40000f28002039401100245c654604420103010410b03c503103115017020761344494021003024050415124200714001c0309125170710081d820644144064a520380440101040c1c9500d000450820707609a8641c00c440d0400810900c000d0381400111880b030100c00340c80202e00da036942d0102100101d05588880a0446e0300c030142e01c580400c7d243d5500d44000041d803c40040115400c04908a0240c0318441c4007007140c4082440c0422201001c50680c0c0e00d0000181041c940c95030040e02240c9415070b210300c081000441c845554250a100302000b0f401e007072030100001032078012002d540d401d026011022002e8140c021a04514880320055150500c421140d91034801c0504000d02c090481b022340c001c820050240854210720417001c9404403103c2c0e05900d403d00210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 867216330 1250 867215080 867215117
    0x5012c150909030706060803030f0901020a0801050d020f03030406050703080c07110d050f15060f040e0d0c0512210f010b0f031f150908010506061204052802100f 71
    0x1902c000c0c4144428840c0d40300081440c00346c880501441d001454030b0341001048020307941000b0300700000300d9005003c84022031b60b004e90007a04481007141d413003490075181c1c00410711110030511041d805010000f004503071160450010300c1d00070b101742c0c0c0d80c07a5107564142d080340d414050712030700422506000c400007460b49010f907005c0700703040d0003007003601c1c516044403080502e0b01c0b0000198894400380d0301d04004040c5018a012102071605441c203003d06812080d0503603d92420300200024003100038200c03001d1050801084d504840d45102103035417045103d4501d0111005c01d40c20401d5120340f0000184100281140a4121400040a541030010000ca6454160001040721440e002424000c030b012001c2030a0401c024400c0307103a00000b9400c0c66000a20040030303600511401d038107040034404262201c90440c3d003903910300301100f1841e03212480c140d410601166510741e0b060080000001080e41b0443ca0740380098400c40c0c02102c0f5820203030064031201d07112140308000c1800281c892115940 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 867217580 1250 867216330 867216349
    0x9010b09030f160302090901150603021305040f0506151204081b1507030c23090d0b191a09060f01030b0a030507080f0a0210050703020304030605012c15 67
    0x1401d40b4150307114641d8007868030008200c0b40e44000029401041941440ba19983d00310a501c00280801c258028000100589500c0389204040c0d00080c0040c404104490ba40c1c05010020800e0201c0ca603844032038005440309a540301d119050300e001e13509641c90b1603001c46500c1d660340c50711036229680e60b40350410160001c7d1110b44050161407032107041079200340000c1d1481c208240b0204520308188200a049401c0d8001150a01c0896103540320850740389108541070150450701c00303035a40c803220041140d016038420010000600ca10074403024030b00c040c03552000403019050411201c0b600d03c0c001d8030b400c3e0320324240503086062080030895074204903511030801c5606041c042221070503440804c1c1003140e540d000b0758441d08513401c02d0161420900504004940403401000f1049031900050070f0400c601e561001071200c002000c604040c02030082e5001590400301c10070007581d5816040e4a0340301d20342c01c000d0fa01c910b401a40f81283d140b016003180100d04041c0c50000c001413a9050102c2480d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 867218830 1250 867217580 867217597
    0x30303050712050112030305160912061508030307030e15071b0c0909020a1406040e25050d0b0d030912230705031c0c24060b2709010b 59
    0xb80c8020000200e030b07980a098020406641c80d1441c41500d420020216900076006810300644000a80246544141d030700054558840713040036a01d03607920b00703c4000c3c0b4222101c400d18080c1400c000500800100145205a9198501344501010554072903190340c1c1c2c84058166846210012038101440380209030720344004825944c044890b243c07550500c205860f80180c104c580c0b00c41c02c050131414480c884200078409010000d0b0502c81c1c8000281560085005407403412410b500042c0c524840070b000c412012200101440001001d05001096a40b08082d0040d409081c40110419410110340c414240c80c0c045e500c805145041c80c5100c0b503514040d000644103101601884092140035150840c8404001da00820841707203804c0038035090031b0303924072a50102c0d4032b101044d2030505e411581c4403048a501140c0d241d010200f4a03030b0709640001011344010308a01d07042010440c2c541d900001c0070030380c0544a409410000a030044200e100c4c030b141000ea00905014010042e560901001d0406039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 867220080 1250 867218830 867218837
    0x703170901150f0614070b0402150d0915050705030603060106140c0709050103060b0102060411010810150f0801080703020f0d0501062d09110a0c0804180f050903090a0303030507 78
    0x502c520071000c90b1582c203400102c2104818030341004036540007415968240054509203040c4001a118080500c1c0d005102900540b9200c2d45406240244412500c0c0c0c03030115035082003c00e0701c0b42000d54a0a120440b0600404e180401081499024005403442494020700070983d580c03c01c14121ba400803502c903406600d00c028044040303880c009000e0100a00702c4040002980c2d0b00d1414201c06880c003540c2d8003415500b02d04d080c0320225500c0240044005003c0c20f0a80050301d0f0000130a40358081c550100302440002036110f195260b01c100720800c0301c2d0307443d034070703507001da41c0750645562240020b100096200c10028003c2c055410b00303103070f000708860140d000003d0242d03503080849240d429034051286025410403180c00c1d00d00302080b0110180c80c00141c1045440c80b2200c1100c0c044c4500c0c281c91b41030100c0c9a03014020410b03a00d00b220301400130a403a040050821070000009414010701c14035060b41014009401c0903c004140c81180740300902210500f0b1454405070001c010181500003003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 867221330 1250 867220080 867220091
    0xc0309210d020a022104030203122a011406010f0504030b041406131214090d0c08030c030904061401090b03130231090206040b0a0309050607090510050703170901 71
    0x200302107480601044035158014125408902c0800b000c0864520054000404141b2051002d13850020b0824051100b402c00103a0f038101c142d92882c081d40032500d4410480319400c087d21200101074028070194040c4450342d5400b034481c1c400640b11089014000390000303100740420000300300d4900119420501443e105801040281101818400101d0710f4000303072400d6025034020000000760304120a01c031344ca04040000103481c008080c0340316081c8594491807a80520a045c04843c07100500104015011295101c09900007643c803600100035030f9104520340140041c611108030380b41c6003c03010507541e0701295820045801002d0300060711000303003500034004081c0141c44506102002000a0803041080c03400c04503150005038070000b800e501941804c03405130040e00d40d50151800d4908040701e1781d8a41c3d030803100c1100106a940350250052091500303004016820243d007409443d41502c82c40790400c10903c05880500c20720000400060320032500002e1381030103019803a00048003a001248 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 867222580 1250 867221330 867221347
    0xb011d0117180717060601110c10032313060507110d05031501050901120f022206140f0403020d0c030602130e0711120912070905040b0c030921 63
    0x4072420112880c003198050940310410500041003140020aa404010840f03080071100391600d5050160485040c005688071000030a0414008440d41003030140241d60203401c0c00c10001c01600c000310004d020115032089940c03002c0107900407540b01d04000d41986201031071580e80c600003006d000b001c400400c101002484407024040c054420540b8090760313075946074200031011a05132507034a000c684c1030020803c0456500d0742c01013220b500030b00441b8030016009010694001c064482d58a10110201c0300311010401c080c111510740c005d03558680da500800301c5443c9061940c0d841417400790041d005003480b0420061a00803411090a446900b03d0307410181d903551290705a030840c600600314410103550030b1007018140c0c4a20f650148051400f001c1e504121807204c1c4d200c1701f80720690440d50354001501e1015440300060b030380c002000c1a0443d0081c555411200c4000e0409803411203004650702c010841c80c1c4400d070141c1e03000304810390261a106224104c5080c5800140c0780603461668103118405 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 867223830 1250 867222580 867222617
    0x3020307111f0507150501061709010e07080304080d090b1603050d020d050a1401061239080f0c04051011030a0c150e07050603090f01050103030c02130b011d01 70
    0x124900c0050f00c4494448805290005140440380d58084003689030030b00400006a001d41c2e82042c1c41c0101c0c08104a648480c406139001d48481580000c05201d04e0703000040d0103100100070003c0310f02200544e00b0b103c2002c4000c6444030807a2107030041c5080d09000000613400703050046042c1c107103c0d04150b4606011440070b0b00036604041c9101c80d403650384030200f241888581c01100300004284e03485650b658104a0040c00381c44181345410241952607001d2a0000343c40c17100038013085442c02c210f405040c180004001198061039840c1d00050b0f040d00402e905004010310cc0e8042c41d80001c0c0103061034242030501c0b03001c040c0ca0200200b0001014001c0d020341764284020005000555512403000e034050070080480705111031031120740d0b80760804a104091002c242d2100ba40d00844441d9900d80300d560041d850803440c528004165441c20000004140d00040c00703500c85072017503424030640c502c01c80348002111350003201180030400108006840641740000c0c0d000407201410002240f000824599 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 867225080 1250 867223830 867223879
    0x60a111b030d1107050114040b0a0f0b0909031b01020405060d0209030a0606090213141f1e0206220201080a0506010c0c030809030f0607020a1e0b070c0201030b04090302030711 77
    0x506042d000000c1300c00c14031400317006d80690040c04100d9058182002c0d651000b02d020020101130710345030303210515850a030407030f0400300b07001100500300280b0b030501e03089480c0c5980c45003010b03091400507003d0006290f070307042c0203940480d40e0042c05c840c10840c0d03801d03101010b0762000407107551502030244410b0004441c0e1040750050f040e40040103869019201c90359214a5064020b003d0006840c400040e00342d60302c2c1070091400fa0780d00c1c8012411040c00c40c050740c2d2155802110703000b04080104001d03c4e140d00050503489459140b800754036000b9032440322902c2a03404180a40010300f035100295001c0807e40245401c80170601d000005581d003138a480706004050b4100303d42403040010040c0751b41c0707010464941e40d840700802401050800c46c43c041c0d82c0340c404000c000d000540c035034000300d079020050b6550850a0b8101501c0c60140c6000b500081c8851202070089021a144c00146529410706119070b0b000194141c0095181008941712042120b00302030781650300c8480010b82407200381ca05200c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 867226330 1250 867225080 867225101
    0x304060c0f05090d11030f1b100e13110f12040b070302030c18130e0c0306010b04081e10060303120605030102090105040314250503060a111b030d 64
    0x1014000d4040c0100749006070a8900200682485010059600c0303600f120295984401c0c1700003404026004a82022100d03600f403070083c02046482c1c00c0001c02c02d030340c0c0e1080d120115002050b60010a0055a00000703104100307070484232200380341c49000465802071940440a000349820324150001c15010350740b201c81c0c0143c50808107401d000030003213603410301d0340c115100f81015421440c11142200c913030300690307800c6098810490f60891141d10340c0307074944008610781042888121100d41c07015036200d0350043d40c07034001e210780780c00001d90a40340d46c162000e0b12011005049000300c0c00e01600c050004001e04000103004801030710a2415041c801c0740015846500c94000990700040100e040303502591026019900400021906070303448421601601d502241c010b0206074002e504a290540740550300d070180032944c10200c101d004006c8440126802141251001d41e5400c0c0410180ca070b1601c2c0705070b00c3c0142031100c00c44c000d2070110703c6c030000403d040c1240d0030701d03640718002001d642c5284c41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 867227580 1250 867226330 867226343
    0x307080322050708010e1501140904030e0402030a0b01020f1b01030c0504050904030f08090106030b0402090703180c090f06050a0303140c19060e16090f020c06190e06090a0f03090504020304 83
    0x8001b500b4903c24004050b8064103000f80100961500f0020001e0000d4504001e10545c0e602001404150082c618801051f80150046440785401c00c00000103219500365036002d84500c00c61400250000100d4411102c0064040c50034058100015405440400d0092043c040140804106030b181c4088441c480c9007c0d0341c50f00d020710b146000c05005180003400013480d43e418071000b13001041104141c80d820543c1030755020950b035240f0008a00810008014000001e40b40f2081c20600440c10208020f0301c40e001c508004e0b000038150408101e41141c483c01e50402a07410041012030300400310b010101325500f00b075030329012744444010b0070048956480d82c1200901100b0409100d0107204104803405030b030380101401024011481c0034103482e0320880000503140c03007100c051415190151032003103168100315022070034090162100d0550300d800201c0d08a01e0b141c0403001034076000a46502641c2c844001e0403014406031510401020b003a0300503020f01c040c050b000a070903221031000750b20a500a20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 867228830 1250 867227580 867227591
    0x3180f0605090609210d09060f29151201153506031908071e0b0f0406090b090a02030d09050a330818030708032205070801 54
    0x103040011650050030304080b942c05007007006800c010004840002002040c4142da4001105140f40b045100d20712000306510700b0407180c90304010007a0840c50200040b0402030003800c28041100d0202e05c0303806000e80f084071380421910b905051a400c1c000205090f10080d6103408011030ba0314002c0e00d001e911140c08031721021922200340d0b60041070341c102c11903070b0f411410422032644000e1036034980000e0511080d145c400003090540e5004c10500b80f40f814404020904544582000049a088905c0c2030304c8000007049815491070070610020802c55124800300c0c100d80b240015400c0f100340080049481603980c44a200105590021581c13148030041c008114030001441810b0400850320290360a11201e06000c0c469540c464480e90140c500b0b9800d8110645196100c00480502150705240c07016a00c0206004030713075000600030b100ba00d40c1c05c28007003d031b0003c880e00e070b0340c80c4140d000c00b9203591005c2c070204455802001901008103982001a00c00000b00d84803117007031007160341c400b4143d0307903441c07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 867230080 1250 867228830 867228833
    0x4050d0501060e0f041205160b090a05010510050102100c0206010308030c090316050f0906030d12020f12091b18090f060a1a030c0a090921090609090b0a03060b0103180f 74
    0x540108100b1051b030300e0054244005104082e0340c01c0b031703800f00050a201e102000074010700c808004094816401a0003407246080c90402040c0405050140300e005000e81044d110400c20140150440140954001c1009070302e103441c0c140540c0c0005e000040c24440c20007600c460f43d9000c0003010781c03810031842c201d00c4252900040180c2030003a0b070b103294060481a0100302407940c006c2522004c11901e82414203400303803003003e803400a115086640c0e620017408150039040c1c4103081900b40c031484204040b1509120b907400000035070603040c01041c0d8400d008101400d40c0c004691070481e0002d15050403100404441d01c0c2503410304000300d4003001001c1e562440c25421007240c0b000ca415010060b80644011078482c000b19100660030300804042d507444012a0040142014403110807103002002207141444c803803c000d2514003e4807649001540c0c4600110b440304240c811403c100300e00a016070481803555503840c0180c042d1030721003030605036241e00c4504444058024081a42e00c01c103d003c0310356225 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 867231330 1250 867230080 867230093
    0x1060902031e1605031b04030b0f0f010b1e040e0403080411102c100c02090a0605100309050c0d080409050f07080a090c0510050318060c04050d0501060e0f04 69
    0xb000c2c01c04aa0380d00e00a204509020a07141c0e4100150b52804940d6640c500313132260713400842e043d085c20001b8400100042444407c1403038500603000141c59480c5501d80516202c4408000c0c0141c0840c05020010356818082440100c2d010592031141e20341410f40c0c0348880780c2d81d204100c0d03050300481d5812080004000b1a440d01c111520001c03612406c0c401c8210b800140404d02d000300c0007a01d059844000605c50044542106449130001d0800b171000201c01d000406050341910120700070740307000010925291644c040c210a44d031018000300c6c00604000001c60241088034010b030780c42d000c0c850034480c081d10b42c0c10100b10301394081e600c0503550b5494880300c0b20448030300130174407807020703a0501c1440b17962640414030745e4000103210310200f1784034201c0c1000c4500c820309070300c140c2d801868840300c07507201d54001c0041c40c441c0c1501c0704400e1000c80440c410340e840c0c1030125a001e416850410080c400b03481d011080b04001401100001002a1242070500c04040c1c162401ca40640c880e0342004200510f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 867232580 1250 867231330 867231361
    0x5060109080102190e0a050a08030c0d0507030e0f28031b03020607141c0c031101090206041a0c010603060204030c091a06070305070f0c080c0607020619020f0106090203 74
    0x1401c002c40c44d0465030060034401120340d40b480c800300b14680026000c1c9565aa02d990080c080041100b00d04075540d408055603a8014040103146015540c8c001c0043c601072010b80f00401d800d5143c14a0785001202000f51015003a0f02c110780c0034010501c202180351701c8183c80507800c00082c481403141030860170150315030070b01c0114103600072800c28820300c0162180c200f990700941d031045220585089a0704520709020b020f840010390328038507482e0400c0361a0b11500103505076009032190204e0703039038407104903080c0c2d4183c01002e900902c08000030005407005c00b0307902c52581c100b8180d140c207180c0c2c244119400d580f600e90054400719004038052041c0078000d1404402000d95140410040c42d000420310401618500318a00c206004103000c000d15010300300301c2c1d00305030340800018400691407030f00151081c110b0244036090300c50408100c605050030710845001e103030004c002030b06249120204203c035030141c0c9150b5045008901c45084644024003d82001e0702080358056100c5c40c042c00c843c0400203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 867233830 1250 867232580 867232589
    0x14130e07140720010507120206060f030f0c01270b040321021002130806040b150f1e0319060603121d0103050c27030d05120f040219080105060109 64
    0x420401d00b400503100c0024192906200341c40402c0000d83c15005845c24041d65201401407002c040c1c51041d41a070200f0200d05c100f004072824080b15140c241410f43d108601042c01c14282d03c00c40043d203103980100c04120760f0f0001c0b9408007001c0360103000000307540d40e400e03884041210300c0450306008100c14085008511700d08041701000c50481d04d00300950740c8000c880e2460b02c05500080d40c1300d40f42000b200b00400780400b0300880d450750500c0e252082c601602150030070510720856100000318a054080e04111300c03070050109505110000007285c0c000c44404900d54144a42c850904114002001c07006880f0f0140000082d11495814a015142280403100040000e00100060300010b0403c2500341a10b0a2800084e2591244107600700c9120714600c1c050380359400d040c8504a40303900081104218002d600b982c5451540c107500b0b80702c9000c0d00085c1c034010500c040004984200e90301c00343d5446400104804031102e50481c1020005850b40c01c510080d03516a020040d555801113130520051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 867235080 1250 867233830 867233867
    0x12061a0d080301080c120a0b0606070b1807080105130b0a140f0a050f0f04241521030e12010b0d080304030e030d141303080c07050a06030e03070314130e07 68
    0x5c1c8618140240c0328147c4070002085505920702094081e00d400c01594100f5910614440e81070603d0700081c0e000b62040810000244110b450100f01040e040c0213040c0611a5100200d2030031125540d56014010b00501803002c841d580c22030048080c4124909034001e800d25009020f00e4180482090305807400200500341451101082c40f585002d210181c0d94003075004412410b1003480308070300140704150030010350200c03820710418200c0c0c6003180d1917a00071240d81c0140d00445506402c5000500000c0e06c20207408107400a40f0f01d282c90629144007141103c04400000307e81d83da80d400185030304e184440a6480b80e8001c4100000c250300328030350040610084004048494a0b042c000705455aa0783c070f0400d4284001c20700f03001041c070310580c2001031988030040c540c55080320600389070b50300443d2203250710586200e400040c0c0f00d402882402c0302030b034401d4040d610303000380d607142655440b04a600810518a04001c02001c40706001040d10150229601c054034034104040000c20310061101c0e0034416 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 867236330 1250 867235080 867235099
    0x90703150b0703080a0902010c021e12160605071412070c05040515011b1403030a0506100f0813020d0c0f05060c100506031e0105061912061a0d080301080c 68
    0x800d4004031401c2d4002c901205c04200720f1031901c0102d45010490400a40004a0440c2c18000203500c1c2d10a12405c101510880082c494850b409542c0300000301459900c481c0c240e1301070000305d00c170360010004030f03000b6802440c5d411546610580740c007a000f05100f4001101062032070420460301500c20040804407401c1c09142020f10707074614417039041040e40d4107001100e00880c40282000c0c90242800e43c12180e40c8160303485100076603403240c0c401c8034116140b520b00b8000030624a0030100e105c1400308190745040340340400c194140d5000c00d001e007400000c078062484010040e9030b800e007004e10040c898005503c9140c17030090420311064187e08445d00c00d0b0014001e4007091040016140010466004049126119800840e051408244694950000c0c60415860200c0d0540010f03000e9074080d2030b44c240c004104601e2148440c20749c01849862070f030110040c00411401d03000300c1c0c0f0b4a103541e1500080507103420005101c11801b4001120801c8020004103c02c00091110418548055980500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 867237580 1250 867236330 867236333
    0x803040f05122a04060e090708150103060c02100216030201050c0906090d020406120f030207061e0503070e1314010b0c07030b0a090519050607111b030c090703150b07 73
    0x11034400ca0128510145003a550211010200102400c3c00c190007500400c0030503264880010001c0046501c600f40e4070880d44005610000003071100383d51590414110116425a590b040280c50004000001c42c401c1183c04107040030680f0041c0000300611040c0c44182d4043c2c0b90290a40720024403650403100c0c00d0008515544500d800c48008960440d41c51040d00034a200180c010100b0303030440c414010521000360200400d00100d01c2066002e03808440d042641c43e801110110f81d0405801d000104410140b490700740554040d44d004001350501e000d40c0d42d000e1010452800920f0740c101e03a02030f240c015200400040b2040680504000c0180398071b018102550280e80358450303c4010078401501e400202d441403e944800b42c60b03940b00044d500e2009034405a91040c141e40ba0307065809008110101d20b040d801a4245c0010a80d00005461520017a00c01c140c03509036003010417a018000c094015005584001c40d6600c902100c2e00c000a191041000c005154030042d0002010560108031140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 867238830 1250 867237580 867237583
    0xc1806030b010611151009020f0723060a0209061b011e15080a0c1401022b0f080f0f070e04050903030723090613080313050f010504050f06090307030503040803040f0512 74
    0x7507c402110142e5234009080132403c3d94810600081c2545003403181441d5040d000002d10b40c20342100307500f10360721074035503108003002ca1062071211a40010704200710016440003e070301066408a400c00094090708100d41c8203241f141c01e00400441c540e849e981c0c0c1ca6600d454450002c09084603900a00b03103080c1966610b10581c0060082c0141600e080800044580c420007021000c0da2119259400392402e001c030741502850065190302c04289001c00d0100010310910304248030f0060040444829210303c9000b40410070090b001004010380203103070610540f078a002e0301c0c0c02901a0002583e8030320f46140020002d09803074006010384c030707000048007140080c0d6400342c1c0c46507041103e24503074894000e0104544060103502c907103454000800c2c140c110200d5001c04e101100c1060700d03143c1e000340c2044011101ea100304d0050641c407450341c080c80710607802c015010b84800c02d4068200c03142e164581c0c07145445d40c2c026900c6110b150740002400d12142100c1e0340a14000c00307042e0f03407600d5400414440507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 867240080 1250 867238830 867238861
    0x906030b03120304080c1207031d0906150c0a0302031209070605041a070c062f0312152d031506090901140901020a09120c1806030b01061115 62
    0x1c42da440c0100c00318007848120350458000b40c40e000704030b07a4446841480d00c551904021403d1300032410035a0440c800c10b02510061140d8000101584619a5280b00300869091048109022440148aa600364980810008030318a000750010340c0c07129600740810b80707154001040c110081d04003072002c100460f042003c0d5001d84801040c0456410313040110304000b0301850798060070810580d94001452600301000b160b01c5804403100b08250340800b0f00d058681704401c5d68206050307004111081c0d40f0002c6640381c640101000d0000002001c031140090103034500400c201280701c82000b1000b42605860540e0140c040096002c0c0400c00212494902c514100826203800303490740c0c0e130005884480a502040306602c80120308100c50800d2801d00e8000e400116500c000300c1c01886000c940d0f0305620200610903548100500d0321070303040514003103c001c3c2c80304035a29019114040400014a000c0740c46002e4480e50703546100701c90741508860b20300700b11240e194001d822440180443d44001c3e8080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 867241330 1250 867240080 867240103
    0x2042c0f0604140a05161409060604050103020a02070b040f0e01060201090c0e13150b012a2d061b050a090626190b03030a12050604020405030d0f0906030b03 69
    0x102e2035203d4116083c03030f05141c0183e00090180c002d441c0d00110007079000760141e0070703a07404c052410440644042400f210603800e031107032540b000c0207002c1084503600c40d030002c203030381c552902c1a00c0e02a592505007071659049078000700050501100203112030203004d5003140c0102070030320080c000d08030281c80d42600d5510301c2c014140c0c0c0440a400095041003459900c841441e8019510310300d200007106241300a202c8400d030240012031402d801c180d402c0b061070781c1d401c442000000750800d81c401035440d0303000f0403d0300104041d004411001c40303c20380301c08080c00c94581d00526000c505044001390701c0d5610001054030701d0a00805210100f042d42d8442662015103445081000c034100c580455162250141443c2030482c1c4135050801c000344042000501f0f000c61401d03010b01245119804051300d03401115402400034028850034054081240c0002d0707017154001d080185410b031503901088c2000c5501d0756910101b041281403032a003a9008006100903c03141c80c0420045000400003900c0381c8900c0c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 867242580 1250 867241330 867241343
    0x6023105011b030918020f030405010501030b090a0302100b0d0c08070f1a1207030b04090c1e060203030f130c08030a090801110d0b12010c0f123602042c0f0604 70
    0x9600e0b171107807030030360480d040f50318030070302807a12440c0501d0a0740c082c1200b40400c94807200d04801003504600005a024150b540c550040c0c0034a00c00850400b00400d00491280c1c0e010320364440c000003046d480c2c070012003d00301a2001d010b095003031042100c60081140c0c001d08503c008004065584020b40044e540520303c1e08071844c42036220010220003400404600c25409494400d003003040213200004103080343d0b0141c041401c00301d0019003103020400c184c403407440540c108100040b06108812aa1648030381125690000810030b9100c0002e820503039001104694000510603040340d80201d815001400402e000f8000c4146051064880703000b050074442c982511001030012513500c0702d8488110590100080200d4480d000c0c00030515060f250b038050104411140f00d5803610325134056841700460340004c94420030b100e080d43c5108220580a07084070040c191140038010b03a030f64000c0c0d4116a03115513581d0940030300c90a1005103907030400c03503041203540041030501d001d043c0031850940c07103904080c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 867243830 1250 867242580 867242609
    0x6070f060b0910030606090207120f11060403050301080c1f050904020c03030c0913090b0705091906110d03140f0c0d090b0a0f0e0a06023105011b0309 66
    0x605a4040c1c25441c0400c1d50180050042081c41090418001e013200e000e03000031b01000d0360741e8140e94100c2c03040c0000a0f088000e664921060640900c02d82c0c06100c00c5860708604000c03d0a01d92130a00b001520700301c0004400000400c01c13002d04202c04040343e2412540d00d100d00010816070110b0501f1411f8200030320402180d000e4050350307140d05442001c43c18605403039a80c5003c4200d40c2e034641c400300c900c5100f1200101c210140c030007180300e603801c9154030561030485510369500540c0c03241c1001200b241c2c08142d40041c56000c0e04401080002031040b0b07250015444084149182000340c10000e80c0c081502e0040c0708803042d600c5060980d040341d039000489003d51a049000c00032440313090100508107007065105801c01550040d918401e0b5022082045040900b8a500c4103135170b070040700040700f548060340700d4020512076401050008488800307200116440080e060090344450f02c40580c1407614081040b40d560003400524044001a10b1140a54410364005e045030103103001e410034609460 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 867245080 1250 867243830 867243833
    0x30e0304050406030803010302090c1e090d06090605060913051e070305030316030b0604080c010f0e100c0b0a021201031b260f0f12031b13060e0f06070f 67
    0x244210380180c80042d00602c1603507120304120741d1070b03442032100302c0c0136010b58000185916251016076038021501441860400701a40502001e40c00020002f680489189600c9001400b0f521a00564510450000c181d0b80b40c80010810114001851070240c003c00d800f071781c3c002607404210300880c0e032000740410a1503207001c041c0602c0c00c000d1b034000a11903c070004c28070440800c50038000403c0442b50ba4140001401e400038003109020760311485070700d5030109054420035070281011200d40b14051600c0401c1d14102c0f800680c0b10082c3c0d5402e10046170f045020781003070100d0913034903d41c8400141d90551800480c0c80100304186c0d0b05200c0540000c0c400c102d0301ea02c2c0f42800015100603c0040400d038000f40407150480d801101030001e10940d481020703401008441d010a00d4007001d0010b201800d20580345455080c01640000c00451905521406813880642841c0141400040a44030102c1140c14100041c00004410f080d8902c14040ea40d03800301c565840000702c6015551011001110241c01d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 867246330 1250 867245080 867245083
    0x1c0201080408040504020c03040f0902090f06030712020a0c1104060807120f0c060521090c150d0903031b09050f01050d0f0c030b0f040b090c0a090305060901061a0a020607030e 77
    0x1290040c80d8800c6c00011541003800000003c0c0003a00d4400e41d1010b8a240d0303c0404034103d105103c0f1054010107200311841c00741c5030090185602c28172604169000b41181c0c42d595049a02002011000c02c030b2013404032092108503401c0c242d005074159001c000c1b160400701007030b550700c0503031154485204000d0407020804c0b031214080140680c0c440303128a1013544850003e4510b070002d4440f241180f0310710f01c0c80d8036202803100d8507a000741c1051001d0000048108240000980c03044065008a20101301211507000d10303100c4c00c0c50301c40c0207580000f403031004090002c015200c2d9400403001c010808100703000ea95100b640301c0c0e4000c1c209003804c9544161400440010380341d1551076158840c82c1a8402c155280c054120b82c5a98a0448240c40405150801c20003100c1038808a10380007105100001c0c60918000e00600d00c0320224240745564030b075a03070707151860700310125001000d42c0d4403904100041c40d12048030400f04a000340d00c041c181001003030020354800e0003c00e000d04050311003c400300340600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 867247580 1250 867246330 867246337
    0x20c03070b071706041e0b0f15180904030f0e0f0915100912021203070b010f09061406070b0a06080f0615090103031706010e091905061c0201080408 65
    0x180180114900c2ca0b00a101030403440e4101a400c200030034140000c1d880d45054030407280003017507002d4051000707003010b403c0c08001d140c41201180c01821340602d500460b559101071800400c1f5002c41c26559054a120440d030842107000c01c1ca000d00c10103414040040e0300f040c3d0740c03d00c1d14900d04e0b0900d402c1e0404000070308040300c6241c08540080c001c0b8241f02e564040b9502c908070b51982510300032071003003440b078003141c0400e0705200b209644131203042c2030001072030002091120600540120703801c00d030305c0d074980c0e0004c2002a0300c06a85107051038030412000f00103016410007408a461000040305608010031014402c0301d00040c030f0f69103410002000c4003025880b10004c1d00c0c007130081300e402140e1541030070b9480500b0b0f0741c60f0400d40d010b0400040702d442c1200540d81070b40d0f81a42c8503000014940c0001100b90005070086050201010700c480903a2107100c0030034407492a44003201e0000c034404842600b11440034040754060082c11002c2c018103100001d50754504c13070382071810311243e41e510b045c5006e0710302 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 867248830 1250 867247580 867247583
    0xc0d060c090306050f061f02122212050c040c0f0806191503050901050112030c14030a031406090f22020409050c1008090604060506011b0309060314090a06020c0307 72
    0x21328080c03d0000428003007008078802c1c4d1050b103462035458403083d42aa00348a08180607401a4007490071600b544458801818a2100c0d00401d00f00d208541c1c0c0c1510207200030f90b003120882d00c01076440d005c18040100105200c0503800d503400c008042118000502c102119044401400045004900c0940b11030340c10301089684601d2148245840d07400f0002e6082034801039030006403c02000c1400c901041c441c140c121482440c412441c10318596080d01e51b025010343c1038644804282c1880c040c41001d000600754031280c0d07074000600501940c0d000884400c0600b09501400d240b07000c10510840c00381d0540d4200c1d80900c2201d503076900d0041c1c0745414901c0010000d41180c200947c040422400007401915088100d501d0741c01c6008070281225101c00481c2d84060036486000400c2c0441c082d80d1086400c8401890101c6039444090352082e01c415500c03508500103912071307000b0049036034148140540d03001480c1c006000c9050944a00d90ba0301981440038185c00d5000030100e21a040804c02c80e034402c0e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 867250080 1250 867248830 867248843
    0xf01170a02031204050103150803030601032a0905090c0a020c240f0405101e120b03250605070314030705040f08070504050c072001020c04021c06080c0d060c0903 71
    0xb1903142e0445603030f41d0054421140483d0812405103189804801c41c0b00c1640ea880c40250b08590342c50004501078034081d291002880020140c90385003441c014882d2081e40015114842c40c0b52501050202d8000014040000c804040c00100380550740400e2441c080c0d202210031010130708001001ca281503100b460310386418800021824035004c10700014004640c0c1c111903140149402c1171741660401060703c0c20b4090800d4046003141131a00440003000d40c0c3c4032690740082c2504c41400400e1421144000d15200c0e10782c038400d40c01c00b20340440002800360032030389401030502e0030341d6070007a012040d0000e00c1200b081021000928442c4240103840c020020a0042e05580343c0d5004165200d6002d805071038012402d120010b030b00320306500300708d541941d40514609a400c60b4583c00c8403100c0750b260203c0741140100d041d003103501c0d6554005812003590b050444641c00907918150344c200c40c526400703c0c4140d0000311884455a845004008030190810070200d84036001c00000c0700c0c10401340c1c0005102 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 867251330 1250 867250080 867250093
    0x12090f09090c1a1b01140108010e01060501021b060726130905190b0a0b130602010e210307031b09030b060904020f010c0204110a11150f01170a0203 65
    0x280c0c41940040c0e003058019041200b40c151500d40744140b042c541c1807020120b01d41040384428030704048100350400541040002020450811400005002a4002e11945c0e44880503903c6541c802e01c03c0400809003400101030483ca18111200c1031542c0b021034a104034004a000030a012850409001d512648140c404540400c0c080c10045070300f210800340c00c02d415080e80812041c1d50751090a010b0500303d098240b0304965031000d44090002c80d4003032074001030b10450004c1e568201801401c11000d1400c00032200d0741c14494000d084803048510350b051a031000c8041890201060070503031041521682d01c0f6503030307920102c00741c000d031603120f1452559141c6500c107078003003c1e403150b142e06c2660320501d40186c0544544080060040081e14040e500c2010b4241000a039070050600c1c48080d44050404556241401000e18094000d40c4400021925840c4c0b0395141308c40c1404005041452290404010300b4221003600410105008140040500c0491049149800c00c040800598001c0481d41c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 867252580 1250 867251330 867251339
    0x22020307140310110a200c280306020d0c05030412050304140a1208010503030c1f140109020702042901030911120d0f030902031c0302070210030207020310140412090f 73
    0x10203500612041001400661503040c403481d001140d500398620703580c01440303002800c1c81004400a14407008d99400d0700746140d1070740110342900000b03008600030300380142c44024618003031050351000000c100c1003006c10401c10000030640e184120300b243c124601242c4968a524103402d034084948002402d0b40305100c114070400801119298095104d40d40c1d180c126642e6000b455038074024405a582140c000e000d40b12030032003110408a05071900c050012500072944194031a03484000c1e0401c804c0a600043c058080d401d1601407400d0604040300c2c042c2c00b07009510441e807448550070a0540c109620b5040400500800c900e00714624040201203620f2040e2509550b0b036141c0f1a40202008070740d0b1501d00c44007490080c410309801503000341c0030f020095800c180c94050b5000d129600c1c0203141e4240080360258954190110341e91a00f80c0300103981b131460b80100b51600804c0000351000781d061095807060810040c00a582069010240e040078a031028000e80d44c1d681542c01c13210070030a00d0680000d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 867253830 1250 867252580 867252611
    0xb39060a0b04181209050a08010b040e0c0a030b040f06181709030a033c02070e04241d070e010b07080a0c031209030822020307140310 59
    0x902410240c401000300300d80040500040d03440000d0080c950540010320503011442d41102105aa0000d1401c0c5044649520002d402c00c0e441d500700c060140e54480304c2ca600c0d070401c1c0c81084030b426601c10041450400c041c00103400080c0600006250b20840e80110b41000009610b5801c0a54885410322200841c50ba403900c0d00100328000b92420203400c140c842d1940710352030844a200324050701070101540c0d03544003941e110004d5000020440001e10141c00514807400308420185255520804680d2075850000c0c6400019001078030030101680510000030005054005004d40d0140c44880c4c5410a065003001401020046800c14200041600d141300d004980340003035802c800382ca002d260340c0300c28140c0060b01800304c005200d60030420007450007501032180300d4207051103450404000c01c08a10120180d82d10b808089010805602c1442985d404030321040440c88003050f852080d50b00300d40c000998030303107031441032562076030f412030a007100e0340c406021020395101c00705000d00c410060041d059 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 867255080 1250 867253830 867253843
    0x3060112061505180108160c0c080706030e0601080c010512060607020919291903050102040f1505091f0e1e010f020d0207050112141f0f0b39 62
    0x2508090b044030401344c49580109040c07801040001005183c040f04602c2c10b82c3e224221003001e40c0c440d04809030001301c2000070080301c00502955540800c0c21898404070380c0c034140044c1c0080981c0c0e00324411400ca1668042c094440305000740c3d807081c0180d21000d01041d098451900062740080e625801c1040c0d65025021301899804e44c044204a203d50030000d0031000b50000008210b10006242080c0d250726040e21001b45549810780c003000825569a81e280c00ca03489580020f05a04405804211803000400034000300d010741d0501500c0c00304c040d80001c0654102200710b600c1c42c1e6034600040141845046854070a900140c0181032607054211284c41c40c50300d190b115400107040400c0e6110b4a03201003024204030344640c0007402c0c1c0c181003078015120a400044c05001c4150b81b05e000809052006420500075120f02464200460485a03100c800101c2500070440c4074480312410804a000c000032540d032080100080f00c00e0340980324501514041c0005807036550040001c12046460010419 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 867256330 1250 867255080 867255097
    0x110607021c030c140903120a0201050915090624100309120302040b25020405040f020a0503010c05090d11030f06010603060f050d02010c02030114070521060603060112061505 76
    0x30400c09004803007086003501c00e040c42c3c1c8000116603801c40f080400c15a8068840e14070000c041c1e41e001107080c0350500407500701000d20300c0141c1d10782051104e109010f20010007517103003102c4c415140b490031080d00c40d9590000b501041e50011021004040085515118001c05c04010611070300d1490990f0000c000d804c00850650700300b01ca00c489020b4207406482210200e400503a0200c1c2003c8091008202a88114882114032030581c9214001659103228061080e48500400c1c1c2c2198198014000122100d0700030a0082c0e1416500c80c10a903080300c16901404e00881c5c0540700803c1519012500384003c0084a401d40f1038000315203829400404c4d0107050b60000d0f43c040028036610031483e164121244900c0350040c106a5000c005544140c1c0301e540014000780000c00c00400040404248280c116035100029501041d22400c00b80c000586104002903064449010b05203100050501d20000e8107031418088140107070000e110329600120001d14012820094583c00110040e00c1584600c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 867257580 1250 867256330 867256363
    0x80c100b0406212907080703050c0d1503050f01020a02060901020406081506190504080c0609030d0f09080d0206012409090213080303041a0105101b0311060702 70
    0x1003140c0d9050601c82c0208036620102c100300141d50b81a0503004000c08600c054440f070500750b82402038240079800b03415203001800d4401e00c0ca8603085400820902000e00900c082504150a22840035111829207808400c01000010050761070003000e800340b140d07039100600b40d010b250401c0303005840642c00781812100940070b50b00f423035a1700041d645c201e10481c09108041890714021903026030703000a034405002c0002e000c0e40e10381101880c01e41e40d8115480b400710000303100007405000208090004104c1c81000b600e00b01c0c14410304800198503124168840c4007000b800030a4041128420048040101037090603103a240b0b204640c025103d41d0b0034024505442001c050f204c044010940358188020f03496645e1450380b03406c00b41e502c4065800307440c08603c8000b0703280c4042600c0c50b051000350b020310b1040c0c03285e1230f02841e25400c0c1c01514205034442489008460b90700420681c04c1075960f041c00c1c8054800c41c0926229250071740d0b00c0701d00030705200120f2094608010b0840e80016150481e0381c139001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 867258830 1250 867257580 867257591
    0x130c05100207140d02030a2d020d0204050a110d0c0e010f12050903040807121502031306020c07031212050c0f040b07050f0102070c1502070302011704050109080c10 72
    0x509104035560840520801a400b00d0410043d00c0780440d01d202c02d15000a0020503032082c1900001e103090075408040c0c594940c4114080001c02c3c01c0031401e2400720344000d6482d0040400d400154079170741c2d82c03403002c0d004031388a10005040d602c055200f03d1444c81041d017103e44901a030301030140101a0610608041845508112081c0d070041d60ba1044c480c0325941c4804500f00c0c010303880400b40c02c01402c50b8100b84810711000c1070b800300074042d20014000b44401091b050400e0700701814406d0401005010162040090002442e00151a2015180c202d60003503a200400000c0514144181d80b0240c18800104091000c641c3c0c00440c026889600500c1400182c1720514140b983c1e00c22421305084403c7c0800c07003041220210070142490a000c1c1c03060b225880400c2640c5400ea901c0480d0485070085c2102007031210207203800c00b01d00d0845662006180072030846c1d0020340340d040f01c04c2d03403da00c04e2166400a020400250070000c81d540c0d001ca651500e640c000c43c00650740306280482c00c0840ca0506 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 867260080 1250 867258830 867258839
    0x40e030414090c0904180501050c0a03180201020316030c0b0a14060f0a05240309030301061206080705010c08190f0909200c1006030c0f050315040813080105130c 71
    0x1890000d01400d44541e8051905113100c00304002484540d00300c3c04010410445100410021b00c5128868030300e01d81601d1703031a2890300d4000c04403a4071101e01e003042e0550301602405030343d0010555821b4020729002140c20041ca040507544011092802440381d10200100a82458190001e6519140f4256540c0c200c2d2604802c0090b460a10700002e5000103082070100702e01d00c2c0890b0055004c80f0103000340fa480340d2400c422201d580d481100c900f00c0c0ca030301c0000100a5240e02c000c2182c45104c4460017048011709160181d0b407a0381790361080a0401c4130000402c003e02000e0421599440c90071600307150030058a90014008400340600c0c003010506030303500010f028549000d4214000040400c2d02a0f00c044070340c4602007a0801d1846600c18819100c80c400402c2484c070440000d94000d452902c41c031031030640c8100040d005074002e14001d800141050044850111203103402513842820703991035940c54082046d204030198000301d01c6600304024400550b00d00c901c0c0400b6180120401800103844 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 867261330 1250 867260080 867260089
    0x8060105031605030705090a03050c030c0618060d1d010b1215010506070c0305061005130c02100902060918090115060807030b1f051c050c0a03020702030705040e030414 74
    0x116030341c81c2c0c0b0030000c624115107039100750004d40c0d03c085141041c904081080002c10350288540c1c00407206035021a54540040c5020044248134003001c9907428580b1038400304900801240118983c0200030101c0c2840c2800c0641e00800310088180f9907070218101c0d030010043c06031101d04183c038020100d140f0301818060f0041091b110541010710150a130b030746048203011081d400008140c1c0c4882c002d65001c40028804d000030b40c0034445241020a80c02c2c108010000c4400272250020001031420300148907880d004501d08903113181c0707640000740c000001c1c00442d48174890401155400000b1112040100303602c0000380307018601c804c00070486d60b000b8140400d01c0a0320382c010000420b59540010741443c2c8640c01c4a0401c4901501200c0001c1e200e40000044020420909020446c0868203840728144401204030080f400d113000e001d68281581c0441840c4100c10324802016000914081552401c0140400914014104006658403140d0080d00da4003e40141440b641015040301c0c0700d0700c1c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 867262580 1250 867261330 867261337
    0x18040c09060e1320030718060c1202150703090507080613140109020448030c03110301081507050702090c0334350c0c0109030f08060105 60
    0x1c9a4a0310511090b0740001c121900010700c02154040740c031801040e0f1400d42142d02c400d120560f680304140c507801c050b840030304007180c020582040b40101c03d60800c000fa900c801c0150b0b045401010702c0c0040204c8000c100d041c5850310300c004645e941a1414031504950560141110138006d43c1903445454aa40c1c1041d11844141c1d000b103a918032200e940800b1070141d0045440c04203890b07000003041c0201394007080942d590942941e03070b0811030607001003484d40d501d00c0c5030710b680720011401e510014145000c0103612850b030115104041d80e800b00304031114000c2c1d02c40c4a0300050100c0340d5841c3d694076040c456913541c101c000c581c03a10740c0f09004240520301980684030420b50003820b80f80682da8903014030119800040200f12540000d50242032980751240162400056070f5808001d240d500000250507080085130812a500095541007845180c5120070f11074040310b40b4001c4459201c000d5558458000c0c1d89414042d54a020f0a490405400c065001420030b6682c54083c055035401006441601 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 867263830 1250 867262580 867262589
    0x12040c140108010b09100c05010507020303012412050c070b100f1a03190902040c0804120f02060a02160b0f0a0609052503061a0408060a09030c170f18040c09 69
    0x1800340705c100d443c1c00707a060768014402d45000318040745a51a85401c0d92010341d20f83c0b0142e0030010040c00507060031b00e156040c44d4402c00c000d040d10041198014111031058100f800340590300c00211320008441c10844010b903070080503100b414100504c90950b41952881074a640d00e4290800185240b40314804441c000584030b041811580c071408569000011441c1500f0410390301c10350300d00140d543d0b00c60002035694954402e10b551038145406400c02c0e11880c0d9000522910b0031658076040c0d4009040ca900c003900804c00350303c1c1c200000244003100708580300281015281d40070081806032144105126091000b000d05c2071564500554040f02d1040d0386240040440c040c103400b4494030b21460340c03208051403400080340ca9588035203850001c400400381d824294001420041c00504100341d58100528040400898181d0ba0b40075014150785000100501ca160044004545014003a0382c14620b995120b2a03641d0704c00300c86840c40003030400c99148264074210240c10903510511801c01038a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 867265080 1250 867263830 867263849
    0x31c020319091802123402070e070201050403111c0509190e070210061206020c0c041b020c181602101d0115050604170109060906201e0306030312040c14010801 70
    0x14110038928000324506e024001003503202d10b80000a081440e45a8a441034840b640001214201031030300502c02d0304540003000c0700303a0102544135070b47e80e05009140740d010954100301f80d0b550f5101e0046001c1c640340360700040c40490052000941c01001d040e0403441080d05038240e07070b11250030314034060440310316001d81c1c50858114041c010004103c2e9000b090610003d034110b0b060907003d03a00040079941100150200300405255a02d00c560301013100304400441280c5e5007241009c001e82010814500801d546107400d400c440400c0c06070300a002030980121080d5080c000fa4a60003001004100e221001090322b618001e003540d01d041c1604008415100010705051405281c024411401a843c0c40040c546545c2c2d03110307000000d1503d00c1b400900314030030280450900256140b1110661040401464400e030400c6950f0180d0b00d84480c8900b00e0b410002402e842c2e48a100110303245001d49225030949001c0c0b101032001b0310100c40f00e8030044442545000303d004161200458030004c0030320910381031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 867266187 1107 867265080 867265141
    0x2160b091201060806041b0e1f120f120224090607080c090d1e15060503010209030712050a02060315031c02031909180212 54
    0x1401e80c2101c02081440d14029015442e0b02c1c00404c020824610034490044641c6503054402c082c0c01a40034a80142c0742c903820285d20315400000d508420303600a0000100b008000c1c400e020719552020313580c0320610720b035030742c5541340b1507003010200a5000c3d01c1c0d11142a000400c18031071050304d080c95200900d080200240c1d00713003140034000904000f40d84003080000d0040b0401c4520766507040c1d8041d403e200403810300075100a02018800800c242018140062002c11405813582240b98081000499569005c0500f00d00c208042d2940581244208215261278920a190078a0168040e9039090000e58001882a80111390880803d141d421120500e410300b08130038083c6440e010a0080350003080c2c10b01039130300d01417403d442c004042d494040701348607845586000010010311141031125180740003020044e4004c1c2c09a442001503500c006407000b1840244403481a03500c0800114 = true := by decide +kernel

theorem cover : BRFrame.Cov 867086330 867266187 := by
  have h0 := BRFrame.cov_init 867086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 867086330 ≤ n) (h2 : n < 867266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
