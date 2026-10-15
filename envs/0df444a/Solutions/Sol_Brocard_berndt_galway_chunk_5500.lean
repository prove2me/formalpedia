-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5500
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:04:34.621982+00:00
-- url     : https://prove2.me/submissions/5323dab9-c522-4fef-b5dd-a8569b9dbb63

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 989028776 ≤ n < 989208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 989030026 1250 989028776 989028791
    0xa030b01021e060a0504110a0f09150617040206090907050306030601060e060d180506180f01110f090f06040801060e0f01050d031404050409080d0c1403070c0309090515090a 76
    0x25681d070307240b024100064131a56540000c013031001e811800a6480700090100e6940e43c1c0d11108444203010034000c040e02c003850511181c1d2074040c0c0040a0381251259100c0d01c5078a50359189000030a04014410380e0007090402850300c0540c1d43c10b000510032603454540585030300304801410300e4118140c02940900c4040940300d40310b50b45d18000e0342e600c0e080041001c502d0680040d145040f907031884074002c1081c8192802c0c041c20566020084824290702000c80707c0080e032034000c41c0d0036907002005032000c0f00f40801c640c0040300c00d518001c11700b40c0000703003c22541c414400c01003055035104d5480b004150b550b030749080c040c221000307003940d81060b102d10200c1c1e801d5041a0000c1d911181407113004042c41845012401449042810345009200041003000003003441e052129a40c0c2c4004004405285056030071708065001c0c80c80c0d069002080d03602203003181d40b646425511341c2940401a000d0011100000884d51400d02440e4070400c88001074a05816221080c04401e01001c2c05a100d546d042240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 989031276 1250 989030026 989030083
    0x6141504060f180204030519050d020313061119060c1b0c0e0912071110050307120b180406060312020732131a04020708090607020103110a030b0102 65
    0x140700d4280c43e40b4515030380300304182e0034540703009201d1940003c025014140421011900c411100e00d4098007980c00e807101505003c104907140d100360320484600c031007500707024060340d0700c5a41ca60300b44000b508103c0d0080d00383c510f05d921603050455400c40c0c442d0344500b05c290030640d01c207060300e8501c0c00100d040107031001103540c0c407000c17001603000d60f181581d640c10010705031042c10040c01e2840e01e20322040e290784a00170f080c1150ba40d00500d0606000307100620138192214030a02c11039100f000c80e6942c580c1151840d488110113031001840b0302d64001e90592182c22510000c010717a600480c0315400008056103107203420103400440040300000d41d004001c0402002c91540d241c6540040c107412005040e00560341000c040310704d130f5900150094001400010450900d6001d030004070000e03650a1507241103d001c100036031159100c010080102804090780505010b006000b4139441414081200b90501d030760004140c01c40702a00c0c00080c0c82c0c5a01c04401e58048c041c00a4240c0340078400c1c03444980c80e80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 989032526 1250 989031276 989031299
    0xa0e03180f0307150206161b020f040204051903120c170304260c060907081b040b0409150b09040f021e09010602010212130218070c0614150406 63
    0x14a0900030014128801d906940c140300d40b0019011004090164030703156031300291b491000b12216035142c2c0b9172188030400f980c00340c2000d18201d0321240c45520348024603801e000d440020381da034443d000b91302808041159561500c9114810740104041c5003004e1441c1490380d400707900340000e0018065209000c602140054845a2805031502c000a41c2c80d201c03840c3c07a41c0c40050b11708103070030500c00c1000c00701ca410b0003482c01404108150011500c43c1d442e1400e070704e62600600e104200140d401a02c503413084950482c040311115200410026071045840041001d17038000c035504450940c0d40800140143c03003584a250302c1400103440d004518035056941441c42450f510300030380308aa00060980242c242c0244011f10140c000d04941041d503920350020b4082d41007080d10300f41c003800160000f09855200c085140c3d450b50018045107840b107041c03000c4103007104041c1072001041001c1c0600400b16005018060340c00c0084503001e4280d20744401600603075450522181e10550a10008015034001039 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 989033776 1250 989032526 989032567
    0x40305070b1018020306031c050a0f0908060103060b100905061e07172502090a0c0207030c06050403030f0e03070e0a0b181005090f01060e04020c06040b0a0e03 70
    0x3901c0310070152164400c4016012907940505642ca800842d003456001207034004d58000c3d481175088800b0aa0314405101c003010700c5686038800904148100490340e4881c00c456006900a410040348454560961509019098006540d607603141c40d030600803400c00c2c0c0140039a2a2807803400c03c8201d030410000990300d114070880c40c1c2e02d040350420010400101c0008039220290b21011140320185020313481c080380d400c032140c0c0380a040d4200030f10a4200100744507503094a5401015550950f9880441070020b201e50207244003144030740d18000c03000406006124000d001c2035122203407600c0c031f140380041c91000d0945840040100003407002d0302640b0f0003d0f80406480914604440c555a48540a402000c1540e00b01d44c1c0910005600c03481850410394940c050001c0f66401071499880300300740b151000094030f00314003589210004200e60b030f01c0703840907030307401c040080002d4581488030114500e00042914140c500756040c40500210340302d244200e417020910340015509003400388050b1414003604 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 989035026 1250 989033776 989033783
    0x42a080c07030c02040219080115110a0206030907051504031725060b06071b050301180611041802190e0d03050304080904051003031106010e0403210501060e041404030507 75
    0x855801c001c568540d01510103040401102041f005100d2000a040d41020302c24403104a01d8054007103900c92048440303c0511904000500b240c08050742409401c0c0e00c010100036103030299800104981d915105210594405031545a84031800c3d42400d5211b007190700c0c00032252034410043d600e0000046440030460120140051400c0381d090304288003c0c1500015184e4000c01c001114400c02104440b0300042c00140d00104040d25150000c3c142203842100d200100d40030031050315800190369030844042e020b075401445052a44d101c5800815829050344810707519008686800e94008800c000541a1318625111008440c0d0401240044c11260070180821000000203014040440308540400310082c100f0001e030326151b40b9441c9040748134081200003d102c10382400410704000340141c107a0307403c1c01c080600340c0c0742c41d5402e4544a0706c0303541d082c61180790000c204180d207549101c0d19009141c45e440e0080b440310544100400c4403070b241010700c0c85c0442c0005020200e688401901d5400b42d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 989036276 1250 989035026 989035037
    0x1219140c0a030b09010f090f05130f050f12090103050f010b03011404060807092c070620010507020d14040e0a020a050d11090f100806011d042a080c0703 67
    0x80e014100c014040300312909070400c1315500005018040751a45100700c1c1e40003181004a1458841700b0415a01c05603403030304050171181031031800300e5000c00c407180c8400d100e4007c0b2114003004100391803c2003258641a42c0d00700010078201c809581502a09902c504001c071108010740c10007000e008140018000d001070302036040d9103990b007500d40354000c074003034118501140c4800380d4545031940079101c1d11181b001045628011407040c105602105082412040081c0145500b003010851f400100c824180000c0c642104801081d40000e02c5418024640396014200f02c25140e03c003d000710686109011184400300000c10502c5404032419800c441000c001681c1d40000000031115401003a405031151460800c82d401ca91500c035005019419041d9001c050b44000721040020003103445407400d01051465000441541c403c03007408058038034880310300d01210107800c0410125200381e64100706070601080000c680c20200c0b603a90015140e640340c80c090618010320861054001d11038001c0500c81e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 989037526 1250 989036276 989036287
    0xa1101030b0306090f0c0a120f020f06130305011b0507060c090503100b01230d05040c0b07050a1b03020d08030601021c0f1d01051204020f061219140c 66
    0x3031290300404840708004007121a00c3c20a0000c29845451882614405c0e21403480070ba0041d003460506030044030b002daa94002110645c0c1c480c64084060540d0403a4044c610b003c0e1003900d80c0c0d403d000313000140a000014441d4034210b00d4414215000310030014440e40010304081900c661000859a0f5140c1c800004281c0610280c415500035102c0d40140f5454054104100002d0606511240c00c036a0244d803040490814441c1204070054440742800201b1000c000e00c0007041034641045400610030303420203001940e50451b04200b0381120300200c0307c5030014400d11007440b20006d210040c0500c407009805040f40f440d03001070b1900c0d4454000600d08000800058030580c0248100303501c1d1650308000c4d0381e010f440380000806007004080101c0201c0e880f40c1c104900801c030f44103420012401a10b88034540035000418013000200140100d0f80645854105003031a281e28010f09402c440028243d6040e0800046414504181012001c071413031816407840000c50a0711481c2d5040f100da03a200c55520b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 989038776 1250 989037526 989037529
    0x81b0d0911151b150702030d0614010503180a12020102040e010902030f0711030f03130203251701060305030a081909030e01111c09050406241412011d0906090a11 71
    0xb02c1441001c201031303681c0008001485401100506141d01c0d1413108110031a00d40d0308c0c00f400424003003038150000d48240000380e04061803a80da0700005102808490300364006a80702d103140000306400c0b000603500402c0801050029150440c090448004103500b1464100820546203800616960401c040035440380b00c010800c0c0100c584905000544a549103080c2100340d0100c400c004040307000380f0030100c103660f0060681c0c40600050356240042030b5164944590034004000b060b00001003956a004000002441000100014071440c2c031042401d180c103015412000c500103454a900703d0814401e0030000c0d0f40030103120216002400c1c100030525824400e145054031402c2000790b0001080d41a0803200c0e0031a00c0c120403076104075030070b0202e2078039218010113000031000d142c10201244041d0080701c03406000800c0c42071110f40c0416007420702c0034a13503603490407013a03225406080b182004ca4200c036610304c404640c4094688010310300c0d801c210724030a40d41c00e6540c0c0c001d80f60780309115954206 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 989040026 1250 989038776 989038783
    0xf03110c01020a020d080f3c0a02061f180605150a0801030312060909060b030d0c030c0f03030e16050a090e0c01032f030f06030715081b0d0911151b 65
    0x481c08c41d404160114100a2403c04c5401c4103003c0c0c100e60f02c83d00c6e110510580e440f0804440300080140d0180030642c540344650000c000c031018150310b220b030040101040e4400c2604002d0142d40341c040010070a6072506061000d401116030080c1c0102408000d8100165080400303541166410f103032105405151300e001100070504d0303422030507846080580700d0040c41117580080e06002821410f0314259091743d041a80d10b2500c45000034042440c000610020458950028000b07601a0030080b03035a640104031f19003001e680d0744822002c80d0000009001e02d00341501d0510242100e80c500300000710001080715921268541024101070b00c4000c01941b042c64810400140d08001303070900c51420b000121400c8a07041241c00e0050b01b04c058001030303040d03e400141c050807150211100348098030300c280f04480c501002028420042032007041000568181c000902c03200c001154002440348503450042c1d0210000f003001d038410900451401c40c19205001201c00754980000324054180c000c46c5120704 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 989041276 1250 989040026 989040037
    0x230105090409050f15010f03060518070e1008070e01050f0a090e030702011202030c0a0c14060f090f0d0504090b13090b090607090e040809010c0f03110c01020a020d080f 74
    0x200207040c5203000b8104800010310050641c40304003600c0c9889104080400075110900c900d000d02c49520000b0404a406c603404030781c00522402d0304038508100010410b1034408141e02002d10000700c0380801003030740c440600d0603000e04081f2000e040740e81c1c50480c030301c0149501030065903c50211940c003204250f40b0a0403000007000101c50034800c000070b81510382d032a07410401042e404a0121034400d5541c00091084a03c106540c2c100c01d402d214204d030f4101e40724042100211050710f8103035a150843e06081004502c200c102d90040c0f40185014100e040c1822030030200140280c5c03000c0d50003419541c108090341c0030354081d0701d000540c8540ca900000d9a4000c050343c10341c40c2e1450311028505104c95203006034031420031401250b200e519091b108907820700e0188201c03d00e01003501c02042c00503110b078000741600700c01494802e40030503554848501a819902007200802d52101c0d0462281d60144440c919106003400030705909000d030740100713540400c245402042020001900c1c200c0e203804409440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 989042526 1250 989041276 989041279
    0x240405010e010f060203070b040f0f051501140f100806010c060e0f010b030a05030a0309080d1e0501050a0b2d070501060306050105150d050907091e050c0423010509 72
    0x2100396074a04076002250401e008200c0441410745000c03a0440c000002ca03850301ea449500c503582c40d0717155100c24103a4140003c080f60784490001008003c0350301000900a981400050503010754901240328800c01e054029032806071a500300018000e5613100e40c070403204142070074001c090b69240c4004031506d03080810014581407801c000404aa913001070f640405106000080140900850815541c5c0200e098014803641c07041200309000362107a00158002840360407000d081841204050003540d0815507040140021f1107900c00b03103801940078803401001c064410b14411800c00441440b5486441c15600c500d0710301c112410350f001c0d01100b83c401000f5072445c90039101d65080c03820700d000e07000600c4161451804d180c000b15540c03802c24581030307102e07121691091805110321003003405800000e042800d68054007000185c00080350180d4186034003403141c00d080210640c12203d01303d42016100b11031400c400c0c00107000c1940f1044016000d107948594500760f10240380300403902407240c4180395 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 989043776 1250 989042526 989042531
    0xe01110a0b04290a0b010e06030a05060a290c030d06032f061b01060807090b030f01020301030201051c1523030a11010320071b0602030306092404 64
    0xc400303000141c100c2900562041002611015201500d51501081a026400c40c07892880100e0f05420040e44020356000041c1446412245800c000820a420840f0442e44903034880701080210301d0010701d00409080040782000340403c0361150040d41c1001d0001d1194150000107034002d0340b4104105681c112455968288140e648038640280d1600ca01c07121f00c802030820a03000605001e10032a11112a5070140259003000c115a5106008025241440391907550b00c80e4080f40c00704040c08241301400c03074000081245580c1209143c035100c0c0c800292441030b4418001400184ea00104031400046078920030340e101915a4032080c0146164042c14000d0a00c284000604040c1d9051405548010741001071540d006082890f8688481c10401484401c800c5501c2da9a03600a034030111203541920345540b2480d020840c0d20310319a1085505465500e807481d07008411911040003c0040c0906202450a504210000c0341c0340b034001911516a140210072074003405008c4649641010400a000703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 989045026 1250 989043776 989043793
    0x60305013b1209012f07050603040203190503131805090a171309060b0c01060506070f08030628030b070e010504170309100e1903080a0e0111 62
    0x82202007120810032481c280403000300788542086000d085030300110004040c00d01e11681c0040b80140703a0040c6003043c1400048a43c08441c00741c41100c5600c41c40317202116103807040d8200d82103840c10321940e00c214841c0e81c04004000042c1c401103081d036040103a1103140503410b0300324074005041d40104403090f40e4070200320030005a24100d060444811500c85070082105032135100000d5242c60361150050855401c8007100513040c2006801000150800b0f09a400f000d62544888010b5031190b61040065450224081854507000c1c8200ca000f0202200c8152030306610342e60b4068000030340c0c240600403400c0403001034a10340740d0003258900d07500072200c07111100300d50500400440711030340015100c81b100300d800100d0180c010319018807941d005841d40c90802c5e10f4080e0404840640c1c10000195010030700591800c2c1d01c900c1a2680a8450750b1546480c02024006100002034070845c1c2c0c19115104800c1000030400400407940c0300403440c40c1c01d100000f000801600c1265460542c4030b03031480346c03190 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 989046276 1250 989045026 989045051
    0x7030903031202030603060708040302030d140f01080705010c0f0c1a070b0901050c071407150206010e0601020703020f060c0c0604090c02010509010509070e040f0b010609090b1e0d0606030501 84
    0x214005403071190701c03052186080b00b14960124041219000d81650000000c541078038010020164070500c2481100d00d401c0c490a021002d503a00800103c4844900005020900d500c5180d6130717014061030f0700141101883c00000a04954030300d50090b142920a20010041c441c0d02045000640002c40341d03041e442000c1c129010481c1e001120903100070000d03a01181080c88107010316130150843d400480d042070070310703181c0001c031115201d1075200c6441201c00005400780c1203406003c4550349a0041e120543c9005800850184014482411900800320901c0180d969100324541d0107000c0c0c554507140c2d15008882440c040c0c04a0f04c03190301407000308002407584843d400000394911140d00900150700c640c00703500d0903100b040d50303202c0c1c242c3c00100c024001c8145614880754020b0040340740b000800384980b26108103007000e801002c0090034850b4280540d03003850103405060070040d229008554820701000c150071a0200d0f00a22a0074190491020711129820000c003860b0800c0c000c000510340d001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 989047526 1250 989046276 989046287
    0xc03050f070803161d01050406030e240601120e1905010b031e07060e0604030212120d0c080915070503090109051f0c0c050309130e060f040201270509100b0703 70
    0x5003400085c00a20107000d51104419840b109280c181c41c3c090400f801e1000079800342441061098951180101c00e01e00460381c030442d110000b030a101602d115003008000100950080d44840000070f0914154225402000881130380d9190b007411035004040103407400300e0250281c0c0e540c480e40b520400d8200c05043e60184500c1840a03070b41c50485481c6503031920250340c8841d05810446d8400c074103000400240c00d101c80e40000c0250804150759800b01152011007241c1c04c6a000c500c9040c2c0c0e12a0b900032035540202c00c2c1038103c0c0b05d03c1d000380721070060203105010040b402031442042180200c08950f83d0f0209410400c906a408002c0c8c0e40190069880312544208040d4099003981c103210070110345d64020000407141c20b4116014502d410002414000048907610089085035500d0803a00e45040c0c040c820f02c1c1c010112602d04a80d14141030000424005009011641000c40c1d0780600c243e01410516a00441301e094460301180d503510503908400c0580c40e80020503542c0001003080c101580311 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 989048776 1250 989047526 989047561
    0x30b10080108011d060c070501020408120c06100b0d2f121f060807141c050a02031306050c130b03011a0711040902130c0c02040e010b010c03050f070803 67
    0x300030380c0e40ca0003892060480544c0d848074842d0010b00120f200044404c00805502c0c3c010701c005407078207546121162801d6181505141098800b240f0061502e03030a01c0f90a40080b40500d03070314031160400f9000380032481501f00c081400c550345d01f2000c650400084090300d824296003e050504120700c441005158024170007040341400860000b03901901d01c0c04542018070f900e20285070400c1c2050300036142c8a40291000c030900184026111064180300024589168112410601708006026407030548002511106185005004000c00c0307082d07002e43c400032190082c1000c16292114181200184200b40c581c4416541c1040086040c1c020b0000441c1250500d41c040524001c031f41886680da802201801031058000c0e0f078103507017146050340046100c540024030b030340d15902501100c0001c80c2c81d0088040c000c034801c1440c0300c0661a09116030132130607003483c0003448004281c0300000c200003003000000381807020104000220040c0c1c41d0568950319400380c01a03942c0d0401c8603400b0402c41ba0b5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 989050026 1250 989048776 989048789
    0x60302071407080c1e06160618200105040509150a0602030306010f0509040e0f010f1a0a052101090b10170601150201090c030602070201031d0601060c0201030b100801 73
    0xc041c0c05520418002480d4411a080e0750054140c60b540002040500c248034540e40101134210040302c0c00543d02d00c002410b0018a14084501c48403840c40d007202521609640d4480f1036103444026404078110040900c44100004191500702c2c81000068449001e960003140e08a4035000c02c119682d044d00c0c10041da074003412508020300b01d54401c000c030307640d20044542c180050026240381c003941d8095006803401c05002040030030b00300c0d10445c0032484c6c8070011119a40301c0e9143e00d80341c59500520312401030025001712000285061281c08101c180044d071081d6170103290300b600c90011152070174501e44803520006000388000c007000c1c248280e150400341c80840c003590007a24000341c040304180580218110304e1002d0400e50f884e0085454111000219440030755484503615400146c81407030103c0618412840140c480040f80001400c641c11400310001e2000e411400e20844840040c2180c11501c6500d0440c8030021a4170048000d40480061f4503005010b01c9920a4180d4000801e241607465 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 989051276 1250 989050026 989050043
    0x6010f0e180c0618101d0402090105040513090b0a0e100902010f0e13061d060607030206130219060503060103110901140304050f0f06090f01020301030b0609060a0902030106030207 79
    0xa81c100124845031642200384140da002014000b05414050302030607421a001564001c0d05440030049a00c400c05000c1c104006181d1030400c0702003c01c2688a51031102043d20114100105500043d02500c6030740500e920400d030451192410b518070b0380042d10080ea10800c107580070300341580490060301c0100b100c2212801000100310f4107c0c1c0a20500111030b030160f4489186000000d0113480c002382180400d81c00110003015002111184d000358802420304103418061b0001c2240c641c010760501800461103048200100800310b507000440940101b664040c51151103003510010702100316150440d402c0d00030780701c0d002070b109402c4005184519000c0c0c03130600081100b4141e8680e03070310464044034007081300c000307884030036006180107107034098800c07401c0351f08051214101c90303d40604264240c420341d100104200500754180030072550340305a0030081d0308550440c0c0c1c0d84107074200d000b02850701441c02c9500080441e40e580013000e000b843c007008115600d58484400402950081c1802d4500c1030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 989052526 1250 989051276 989051281
    0x60b16170a08010320030313170c0109031e0f03080604050a05040c0b07050f010203010801051b12060607110405010b0d112d071b0501200d050c0f06010f0e 68
    0xc100d012600108035a6450720807980c00d682d500010781426117070400b40010080980100760b1400c100800380c0f81d07418005007900034504051007442e9030b510800780c500358000f5800c0391001d0740c024000d0340a5a41c440013035100d40c507216020003c20301c441d94000d031011014491440134103405ca54690300401050303034240865a034442c03030502590303000d4800403c0d02e10030050401c11001d000e0040d24510344200f0540340514402810030b0300f641c0003a0041521a5503403024028080d1803c000c00d010865421a0a41410294290f07140f0508000b00000d00030000000c800e070411007c005190105240104104203558403804000000d400201360611a5468111101d035164401c0c02074811940c2c5c40e1001c600400007025040c02d402050720b440341c0080c5000c0c00100002001c004110992909800e001e6000a1a14000616101103160440c13441404100400007541001c00c1d444200707100342c1050b81ea1b038606861078070b19160742c03104203944ad8003880c0d001103200c80110040504407103000c86440780c140c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 989053776 1250 989052526 989052563
    0x906050a18110d06060b0d06150f1b08030f060310090203060606130e0a24030506060d02150c01060f06091203080411040905030703170603100f060b16 66
    0x60300c00760003400d08044074098a20004410b00b800800501010700907111804a55031020290342d03051308a01d40c00c0f04040ba2032130100ca4288216001880345412001c0c29035003460000e040180c00b580d05104106e281181c016619428018054040c2e60040001e90f6038038004c0301081d28550243d55030780c881e00405c0034100c8000b5140c01503e003140e80050103401c6c1038460008200da61340c400700008024120303c150004247c1110400644079124000303020852440c1c0c60303e1518490740304000c05190781e011407018000701d4800102540e1059042d101c810307542d0b100d40001098483c404400e50080301001984100c41541904540c003100c030302c650203c040765141c040c01d8503445c506014000d40c0c181c11501c0c003404039204190640d00f2602a880c0703540d03442d8010000c5403c1d60110310701500c0ca40c0c4001104030030954444940740301c40c1506240e14195040085c0002e480c0c044000594031020303121142c0055003051980b101c0300502d0000c4440d596071484d0b819120303007880f04881c1a2811460808400380c03c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 989055026 1250 989053776 989053781
    0x302130225030e01030c180b090f210d051312050a120914030f0c091806010b0301030212070803030a09110307061e090f1203122a030902060a0807210906050a 69
    0x4100c0c00340c2c000540d0301b041c81990231500404d284941c07110100c981c900d803546410000031500f0540f005d040400e80591028a484d2a68081ca544100300b800c0000452800c82c0c484418290b882820b03000915002c0380c2441442c0c0ba90030440940f091300b286280881c01c40e0410a50741c102c0360030032015101811040d0406448826104d0b1000c0a6000030311034403283e11b407a000403a07204400503090080308441c55034482c5405407d0300058020f48002005009501e4125040d42040d20441d0060201d1420051810b441c0e0201404447d100703900c0701801d00401003058039144111001030111080c2c42d80d00c100060050042a51510164140c00c458024a070b105084c0c030420307155441020007040346440201c03074004001d40310903000c11018104044184c0004c0c0191070074608040c09001c01c100c41c600c0d041d81aa240d02210b0800c0c149483d5001c00180c480100b40c516150031410000a1a950b04005441130f1562140c100340d1170750b00d036508a40030700c490b51085d2034083c0248010030a903680c00b50840704 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 989056276 1250 989055026 989055047
    0x1180e0604020907050705061e090118030e0d08070b0604051e01050f0402040924140f090c210403020d09030510110c190212070302130225030e01030c 66
    0x15a03800580c00a00076080030408281c02c0311407854040d2030f000d01511810b0400390285c540001d10030031004500300c00361210080c20742000380c81000b007003194a8201209900000048020b05100c100c00b411003030340c5d84800e00c0154072a0030588081c2d8411407442c1c543c010000c01c0310140c0c840d601e410041052054040c0c01ea40404030407007a01d5210741d00349010400c020521207046980030340c00300804101c65206001d0b10180c680482c000c40c0000c00c110030f0300391098045803c420400e01103540a0605130b0348030340264404013010b9440d150580c860980c1040c517885100e01d8141013000e000c900000150005000c00d02c164081c0d0300392244848651400c48584030359200107441503100e4940c84548100660002d0b428049924146240c00d010510450405c040049550b1008080403003050030750401e10400b40b0744a014802505101e8215800201800019650198016404540d010248485803d040f4100114040c9581d42412518005048002c003e1044d40060b040c90f00c1c44d244140102c0010a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 989057526 1250 989056276 989056301
    0xa0b0a200711150426061902090409020a060906140403080a181a090307090c052b1401051801060e0f180f070212041805060d0215030118 60
    0x10318141168994910a0150b1084603900060585406101d081039000500080c030410b200ca6262000100300d08401110340114042d903900550204480036021075071200500d0915980103883d109104045401084030b5640290041003010f40030940e40c5e000710ba200110358560ba100c16202909200b950494001c512005108400a001e4283d246008030f02014a400d030300c900240c1c600d941e40351840d90030ba101c030030b40c8112501c00180c0c04041c1d040900400001c0d055084044c0514140e101c0020b015101d43c000031000100c4401c40495150b08803100ba030706082000740309000030840741741d1083d0494000c0c030540340710303080707000e070107610101445840b0b4100d44003503d540c0d403008001802d020003825000341080e44008001d00306814a008074a00a00079040030b202c17a649890540ea001e0701d04040301c64102d50541007071000f0070603c106010380d0780c800060f000340490b441d1203e801150500c900400d0080d444176145260042c0f183c0410045c6040b42e5006000904800a0854400c102e551a11142 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 989058776 1250 989057526 989057591
    0x18060a1506140d1a040b180f041a0f01091805060402060f1c09050c0111070312050408030d0903090609061707020c1003090b16050a11030c0a0b0a 64
    0x30020240038640302c4440c00849901540b800460f402c0d0b01c0c2c2150b41c140c080740d0045042d6207510b12142050300c03031000348600a032142550349043c450190420749004100001c1420000002010440d220202d03890040d001e03c0c00c9000ca007406214480782c0c01090041d404081d140c112800440c0039030121010040350040c1c040c000b1511140c00380a02ea038040c1d14094092a400c000242c1a100440003010094641c0000029141000d282c8182055113500d40541089070400041c1d040c144080b84513030841c1e078845240c15441010001c15106070040b90302200c1d06000c08106141280d5040e044151107e119980d40c20310252903020959500c02030740269000a40380d075000380385c00310400400c0ea400c030310303c0d004036141000c0c400c4c0007900e43e6010000c0c840c0040d468218a03000c1041282c0496000700c10202c00c048440c842c4000204075009280c00441086454a04400d908900380103c5842821500c10f541060169081401c03d40780c09070b80c2a51910b181a990300e0f40c40340d601e8501080d000405070034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 989060026 1250 989058776 989058779
    0x905120f031f1211040b090105031221011e090c0c06020d0204050907091701140a091103071e05030102040503070e04030203040914160c02090106110a020918060a15 72
    0x5010a0b00c0140000007a03046002011420b0703c140101c04145600c107144036101c040c0c20409200c240e0f0749820a490203059603100601151350b01241d40107911581514454aa0400c5058040081540005052001014000032030103c03c41c030888404440080003010341d41e81d49080003400c8618551821000503808000d40d400035403282c00409060f41c0b000405410242c0710750000d0300d1800180d4181c40824540d240812400d424941c1ca9038221a50380000c003c010032800301781540c5500100100e000310340d03940c602c07020410803170709001e0a10000740854020f161580d55990703428240020300300b00c891060200003080c4c90140215003e540300500a825610b1400200c108014400380c0100c0650009120101d20705c81c00b48184000c018040076003041904118103c1c10344e8000301d0307110004010a90301800050303158010114110340c1d0074600305141541d2018041e041181c9610000c0d80000b05800780030020034445003101d00400f11005440b9582c842141c1d0300c048448004050010f107104440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 989061276 1250 989060026 989060041
    0x9060f140a0e2e21030e0d05010e030f03070908030304170306040f090308060a05030619090c121b06030c140c030409050f0402030601082b0507150f05011202090c0a050c100905120f03 80
    0x48548824842d81c0085001e403590a20315046070400833481c40c2c3e80b0004410010714071782c402c621000602d0b204001d903255003000c3d00d44c0c40d2100c0416000c9500003d000001c02c0c4651142da0000c0c0c5a10300e202000c00c0700ca100d038a0000d0608105032100740c0b094041d200081054034002c99483d0155500140700341080341e1007444c03030380507066122094a411050a100050100007a06c078680306034410303400c10412004101040d9030071541c1d5041a0101454038403007816a0380c0140301441c000c0c4441481e030742c541c851030840030314620a940107420b805d8104028408a00d482425043c09180300b2810342e82280c5c1c0b55000160384010403a05030311240c126a00c0c000c00c08180303a0302003d0004692030001e20744100c64503003095885211001c4040d09654000030000d000342407103264090440101d01c400d0640060700084c1d107580c4050030902000c4000030704100c02d02c0c000d000310b0b540c4600c1c40e41980c8070f00410a2004c03008010b000ca0998281c0202c0c0103a010305d14143c401c43d040c81a0300303149981942c0710b120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 989062526 1250 989061276 989061289
    0x714060c0604140a0507030c03062d110c030a11240a090c32010905101b0b0f150613060f1809060f140a0e2e21030e 51
    0x70304003c240201003040c4040b038400d00c84400694040d0326445d8049103585042c50032201c1c0180d60351a4400a2240b01008130400307060744003103034034800780480c041c01c2408640307030644104400c0301120302c000154468041d03005000d02e14a682c400e02512181c422140d20900007411841c1445543d20f18100040c0c69102c1607801190128002d0343c249601b0b6448031309244074030184105039842c00344000b06450941d09a4408021981c0742841d01d460501d01e0100801d2823906000c0440c1d050201000807070b020a046c1000044545030000c60180e0380d82001c05c00710007030000c203407159400810410100e000c9814403008464000244405245040d40740c1001160054008070110040003003510b0351120f880c0508640344040c1c100c1c8840051218500044482044001ea002107036074140c0f0300180309203590704007500382214108032402d149541e4000038020400c1c09140c0c1403030303242501607845031060500c00000040d942c003000c280000004044600b00d01031150308006001400a5020108a04246 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 989063776 1250 989062526 989062553
    0x3161719120b060307051207020109030806040c030e1903110303132d0606050a06090e01060f09120308040209010605090915010c1e020901120c09020f0c030c0714060c0604 75
    0x11100016030451410005405071300a969060016102140701200f441080108a40055036400200001040c5960160884038001c000a02c10b6070740321103c00f40300340a0b07000003a044444100f40c0381d50a10a82d04071618600c01141078001039200c00944031024000000c0300d008114024400c03021501594807110512401c0000c842442d02004007100740070180d90402c8401d522804000c24064141801c0c0a000e4034254428020007103031035001c002410300c0c43c030203a05449607840d20f00300d00034041c032003034483d8050766002c888028064510003041c154400c0d4098005c0e84210703070301c120300d0340d850074203d0b82d9010750016503038005080c0d00800c0d80d903a0080b03619890210706061940004125488083c40040c00482590040030345942807000c40c540840c0b428090040d000381382d400c0a059440d000c0a03544c1c0b901501200300e500090303403242c00300070005032014411600c0840713030340e8041a00e25984030f2869101b8003680303a171000d90050b0f241c80d014040d0386800301c1c81402496030f641c4984500d840060319 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 989065026 1250 989063776 989063807
    0x70806010f0b032413050a0c091a0306030c090412020d0f17040c12080d06050603040302071208070c1401020705101209060906020a09080d08011a0a090803161719 71
    0xe48414003140c030356a0245d098000c5560000440c0d02e07044c00d505c010746502d55103100400c41c040e002030101d1500d00d04400200b080090b008e54495444d00c012070315021190415550240c880700c104401c018220603418851035241c0d003a41c1c450030904406803103400146205001141d021100340b03001c0c0b801c04a40552060060386681c025907528541d02050110645081c2c0b4030070300000b2980c81178000c0e03005450061034240d03055403861410744ca00075101d00403800340b002d0744014a0444028040c2d10b800380d4203c02e800c1304052091551b00c030982c030843c50000e249240540103200c40058280780095007901405595113441620102008008001740440d080c1142d65075942e64002004c10420b2005c1c213009011500c0f001003070303420841800e1811a100d02c00f0310401c141f441c014822801316280d101349000036007120755101c96002e403060b40c041d42141c211704268800400e494150014280704401000e0082c041201489910320008d0308a02c0f800764480750f078441202c00d070010756105e80f8602d41c40840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 989066276 1250 989065026 989065081
    0x50105150705150c0403020f030606090615090402030f0103020f090705030c0a021c0206010608010e0907031101020a020d200103050408121902040e01030204050901181b09050405070806010f0b03 85
    0x607200d202900d4650251104a01322030003243c240118100101c5840c1180c104800522140c5002c600080c2d42c0c0c14003c100354020100d0f217080400e41c1c0900710603034105401c0100299141d252841c0b002e000e116003480140c0c4103104225159105007800d040d0340f4042c64450350780a00d03540d03495101c07a0595002c890740000b1441682004500d141000806454405443c0e0142c291949052070040c51003d040c0c0291400181880174004401d40c0000c455040343d62205028040e40d210600507402c0519080000e50803052400a2004000c01c1c4180c130b1003800d0074520100c0b401129040110205c0b8000c550080424008001c00c468103800c0c01d40c200c2e80030420705c601084020f4890820400e9030025070003840d01d091003030700500841c605800f0325a8041d1309800204881c0003558200c08030040d0710200900501c103411242d0088881c04901000500040c20b014081e9041521b0301c01c0e9901e00c01d10505565000703620000c2003002008503020202d5924000c0d0324159100d00201d1545451104200a000071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 989067526 1250 989066276 989066293
    0x2105090f1e1c0b010e0106020d030c030605040e07030b090d08150f12060604050c0f03070c020a080318030c120714191206060b031603182f0103050105150705 69
    0x41d1005422000e0050750907201c440d4000c03c1c600883d410030181c01002003a0f40040042c000603070f0000ba40225209603140104219021007030660050505410075a085420403107001c070420030000e6a181140d00c90309088005640d8904150344a0090100d480d0008081502003102401c140030b41d42c004a000804200a49101a0000d100c200100e250444c45402c10420080203142c644102903008a00380c0c44a881d005c10031004004c0c9202c0103002d101030106094862003592200c81001001d404401c003125920b415242058003210090340c06103109201341b000724205070900565100e2840e25580092403035604001941e4201c5910f285680c0d00100e1003030b903020800c42e2400b2094001d103080300490510309102c0c200f0368291f58049e00400300490b0200306000f20f41203400c2154512404034a4001506074032500c42c2c40d440e1000f004080c200c4030320303030080c45240300112030a004102d025008050002c484200103600b507030760912a040e440764a048000c003411941800a2510510540c1900c5106c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 989068776 1250 989067526 989067529
    0xf03010e011508060106090f0603020a020a080f040905060a030b010b0a27050907020f0c010507150f0b0a08070501051e0d1d160b0406050a021501032105090f1e 70
    0x40b5440720111034a4011100b080006490510580d0f000d0222407416150035410510300b02d441d684648505820107a0020b001c581c4284203021602d03180d540566110b40c2c071201000f200010381c000d0b002d030328951407138000811064585985034200b240c1e401a44201240c2c40c000e40c5040907045404060300f4844011211405145900503512140c035a491401c1c0031607041800344411060300501c40e1040d50b00c030148500d45188005003107110301c2400d181c01540c81d001c03840c0611780100b0b0750b1041c0c203050b030900700a10b441d0803258224840c620010b441210039542d4600310319036142558451580458401c00142110207110400c2052041c000c0e100310b454615000c81880440d9201c42c41c0300313021160308040704280501400403900202c1c2510741c1c03103401e90a02c900304c501840759210b503030280f00d40028803141c845d000340b011102040803001180d082d583d581c00c2c4544041d060151210705002011031050341d0718014800c1e224a010040c00c1c103019186c110741800424881c035140d00b0801e46491000540d80d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 989070026 1250 989068776 989068781
    0x70b090a150507290604092315090622030c11010c0f050106033e030a120306090b04020712030b031009050f06061002190c12052a0109050f03010e01 65
    0x41146000b409403038036809013880411014040c0c0081c4c82036081100e094080381010844e114070000702540c0d04102c200c142c060915100401104000c031036155420060301c42c0e80803034a0340c4a501c03a010101503015010f001092050214100100801c004400841c007041c403004901001c004103041203440e980070341d10d94454210030010210380c02e0791106014420803003039007a1a10010f101580e940d000721450040c40c01207101c0e40044c40500044480e052031203650400820003041c1c0c1140c055440c501c0ca030700c401809403110b80501035035541087c0009000742040d10864050a0300a00040c3d00d40940c1c1808401825135400101e515100390f0900608a03203d512442a40c6032241d00240540c07030701000201c0c20710704000d22051003668180c15440005402013040300140a000440003201d013a90b1900000107403c0e50014109402824003004c2006000164524100d55a142200a6540e5400d0304c4a00c0fa05580b016800581154070402031030608014040f240d900c0100080f400442c804d03813103401c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 989071276 1250 989070026 989070053
    0x302040c231e070b190e0309130b12210304170901091a070b01051c02010809030d0507090509151003200f041802090315180d11070b090a150507 63
    0x54081c1c0b8076051110201c07003c1c01c0450100d000b60b205102200000f0500c1f81c90340106480c050007214001900d180341c0b08035074001100d9850081c04a550910001d48403965035450071840650310383d00092081c0803c0d2840103491055600c00d00207610031103454480301d840d42100c549581800894072000c0f401e054050304003210500c413982815100d040c54181140d02e10710691201e0f01402d8011900d032480803841c1c3c5002e030340540a003040b19441d12120b40d041d1a504c9440d815200f100d2400c03080c4880c0d036910030b85030003c0f145c00311070b009400e40790400350310410500307081c42941c0004114014030034036000360090f00c3c20304803008d0102c1c2c041d2500796856043c1c4e40b008410301141000090144030303001d902015005501003e032000c500308a0440046980c0381445450000b0a45448002035030385840c0502000035a45400207461a050b2198009403000b00b190b4003030000c50250341c001007941d03c0f040060320700003c001040c40d450301c0c0c901070710100042e0350301c104001004010032800011030581101e940 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 989072526 1250 989071276 989071283
    0xb01080d020706030b060706020f0d0603061d0114061003111b16030317060d06090510053d080a080702030106050f0f0405100512070302040c231e07 65
    0x9208005031000381004601e4004a003410b18020f141800d684800d815036100590007500107070b0b50100e84000300b205c1d014180728210340a05100300801041050b0300b1001c40d44480c1d01c141b083d1207005d20b04041c2a01c40c00120300c081c01010754000358403440c05504242013103440d4200000c010344001a0700f00079034420050003004001200c1e0209a0250400006080d4440c45a00c1d54410b400c542d4000c18032951101403507131000c00100403074202d03a01e1518060019500c45c1c000c00010307003103252442d1207061400b400f102140c81c2100207034072030400e4500c40404020010784100e611428079114030b0980c00640030030000c40000c20001c100008101b2000014038024041c10b6100c001501c101030964506130400c1d0700810026802c0c60483d102c1410901070664101c80c041116507540c46086c1440296a03c0356a0100c902800e0301c1108402044100c2500e009503414030642260740002e4524919400c0c003409151130007c045000440c1440c040c0204011030a804640340c003044074040b02c0e81d0000a402e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 989073776 1250 989072526 989072533
    0x403080a15080a1205070b010b0904020906040e0406061e170705120a0b1f090f0e060c0408161406131503020309010b010305010b180d14060103121b02040b0303070b0108 74
    0x5414010841c4045620340329628005e860002e240d9514840088103100700300c6c9803100402c11018554481c3c0585052000190000352220b54a983c2020900c0003903c00b9100c581c58604013241740030f41c3d403400c0040813600408186a051034200d8080c0c80080e6050702d5030310340c02440c0f40822180e0b03440007501510840c91000b07120708040b43c20074014000015140e0b980075102520701c81c00f41481754003a5000c9130702e24480040c03147c1091503100d002d000e115024138500d0003124104a080500d44000e403046d00c4241d022102c5a20500b009801c1030880790007040c10341140014503610625016004180784031110403c25038195840c3c10b81003120b81304649410100b0307004030404c01480700074403c0b140181000d1a05000c43c7d454054810300d41e2145d030916001000030320311600520384401c04c0414040350710440c20109404102c46440d01d40c071003800111048000c2c2149000350324400c9107582260030700c3c02ca065450540c50f82c04c110061146c01041d03500750000707000395800316103d8190070b402494020040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 989075026 1250 989073776 989073793
    0x1050613050a0909150c141b070e1f030b0c09060c030d0c0f210e030c06130b01150e1011030a020a030207050607241e020a090f0e0403080a1508 63
    0x145c80c4480070005010b0141e107403040081e0407aa202d404443d154154500d45d541c1c40d9054101c5000d10101e810b100c910074800d1800005508101c0d4807490f1160454001c42011081143c078503500c1030550b440060610848038007c42c0d500340032907005201048004200619040e0071110003810b40e01312848088011760f8a81090f1465504100948818007592501d400d880e40a000d5400751000c101d02130103003403595143d80000d50002042103801d6144606c088800c1480c102c5041c110415400300c1c00c607180b8010a000041140f21010341c40c52080040d01c900c80140c004400f44105803d18106041c10030002102c4a200440144000c1422000030780c0a46030701010786c01d01a181209590000e4041c4408110040110762044020011506010b00e5400318a4165400e50043e007020b20034100400044405403000344125802400e282c60f0907120050401e5035800789100410f01b92103000c450300308810010340080c0c41060450780c408032148000440c1781d40d0380c1c02c40074201c8450f0002c4d2041d9004004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 989076276 1250 989075026 989075033
    0x1203092109040b181f05150c1006050a03080c1908030f09070b070f05010e030412060c0302030402010c02061c0f0609110a0f110a020402030f070806030109030801050613050a0909 78
    0x81d1580e642c3c1c05544111000d251008a1112000001d05060400c44608210703286000381d150642d005020003008100c407200440c17482c100030ba1100204030050320034540c401010100728000c002c1150310042850b41210f2864441001e643e10201d118499801074034001c800c90105805003509140c044c80c6420340380d01c2c00c1d6100343d080c0440036000151540c0603034000c0212000c488119400c07190301412409225166142c0036014100e09041134195010200d000304908204520043c10310740110810b1040750b0103209c09030101d110640f400790000d81c01c115440c016041500080c04851650349400212a030009108000c032086200d80b4103156444030000c10051301035004a0510f20034410380740c4e00d0010618005802e9014081081081c0410412402d9a03a04280a06054140c015105642c3c034584084405081201143d820000c500d15102003216810144a81d404c0b050b8184c48984040c2d003040c1c200041c0382c01c0710301d1005a4907503c0c2d0000c16151151007803d03008103507400010503490240d25 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 989077526 1250 989076276 989076281
    0x5040801050112111207061202040b340203030304080307050d050c0c0714131d011e0621060209280509130c030303110c15040209090708120309210904 66
    0x131465440788002a0320454401000700d0b121007119482e04191400f13880b03540c1070402074005c0341d0080403c030340d0104010800703281b520811400b00002009000d80404c1030400031824040d6404041c0d01940300f440060b0004030039900568105d01281001c40c188800e81d5140e0090318001c03074180144c003401003040d00c1420b40030000040945801e940120f8020316070700c0030403513001202c541c840b507150711030104010f40c1c11002403801100000c2e8009128482c0c0415800f5000300841c00ea10580c240342190009a17402d01e4800f055000e130b006180d240003040151940c1001e90400301c02170380c0c800140382100c4004100e40706203000030341c0d400c20074800041c84c00c0c0c104440b02c10018280100b02e41d011161100003031104218005403503250070300244013450020900d640703004030520350110f807058081075081040c560094612942c421204984d0641d5004a0283c54240910a144441e40130425101c1d0510070040503607404075443c82100d00e500080714003000140082200d581100400041c1344a0900705030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 989078776 1250 989077526 989077553
    0x4111f1202092422080d0c0b0a09031107030309030b011202010f0c03031e0b130b060d110c011508010f09080901260a0c031d06070f05040801050112 65
    0x6503000c41c20309503000b000c640c6800c0000800c14112a0b41d020101200380d556090b030302060986840310040101c4041089825a03180c01108998417803140b020400c07605c24400700b59550b0340715011100304c0d2280103031223029207580c00048050010f503840d200700c0501b0800c1000003c502070f07921a0001460350528419521060f00004420b038a500d40400150342c002106a08172242440c2c090820050790500310020000c00903e584031840307a189120300d1842c07540040090035012280d6260800d0809100011207a071201440d4002030107121005003034100d6031000b01c1032000795000600c0c001094152508490b10214290111000042c090016410074401c0b8080000420420411509680c031060250700510403002e04109a14180340d445c130034124600d040c80350143c1240049820910702000c0030701300747c00c900000240380401e040e080070311070b0408041d65100da60180c000340c1c0f1600b404541c80315082c1004028030008000018507590300f4450b0754020b00f800d41d200504092580741244c50750940 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 989080026 1250 989078776 989078807
    0x5010f1d06010f36020408060a06210215030c120c0f03040b06130606050324090606030612060906150d120e040603050703080306090c040e01030201050304111f 70
    0x4070040c8010070003092508140e801c0d01c8818030740400c1801250103004007086841caa8458450081e0960089940240c01590140300642e05241d550200200849c0d42070311407d0025840c0300c1c16801c0c0e0741e030f4001c150b00d0820300213020315594070071000000c1c00d590700607207400c0c40101c4009001d9030341c40900d40c6c216420441c03d1494a1400745031400da0801e6000180010340500e420301c1c0400e030b180e5580b680c619040040d00c1420f01140d641d506001c1d0064000702da180c4c07000d80704000d80d90341d20000c0f61010a07819400605a2032141c0356041800044d400040a880c1c0000e0502020b454041040080d0b1784501700c0c0b10001e003054a08201c034884042003c0380000c0c0592802d106450008680c80d0503012049220314000300710b05405030014025001c81d52000d0854000c1c01c1c004000c0c00002c100840c487c21040d40d080b1030781d803600e00d04002d181c4103600c540741203d0100001030005620031340081d600a0301070b101021100032405c0020b05801c030700c81c0311142a4424620050203031504441d16030702c600c12 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 989081276 1250 989080026 989080033
    0x518040f020f1c12080907050d060e190f12080c0a0c03020c060a030e06100f030303051e01060f020607050306010c080306060c070b0c0c0f0d0b090a05010f1d 69
    0x14a5620000114140c0100a100e001d080c1c070303400407540358001d80c8502000b20300d0b602c2014003c14248180302140882c1c51900241c00840000c101a2000a803c8100c81000d461400580340329104c000041c84a50340b921624002c80d110354441c9030058030b244030b01c540241c50503203602881e03160282e0404441080340c0240a80032013041111124401662031250590501c040e0100503860224100b40202444036032014000c980c25508540c03550110071040811070403140300d51520101005407400c0342c0f14600c815085c1c0230702840001c1c86070b00100e4021048445c0146003010005141003041c50980140c0c000400102001207200e40c1005615041041818010302c0e6042000c0000d112055482d0301410600b000404240340307494800c11980c00c0000d44080e14102c0e5100d0300c42251692140f0300c480481c2c454610f26582a02d4240207015030600c0090603190442825a9008144c1000610149807401204810345c0410300c00c0c001c00c00c00845403640055541c440706048080d80c5244001c0000030b03070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 989082526 1250 989081276 989081281
    0x1008031b06010e011d090109120f090e0c03010312030605060a081f0503030405060a0e061603110f19110915120f121606060b070611090a090b0d050303100518 69
    0x459445c0146500086010301e42030380e1a04c00c018050b0546000040480c4004201c01900340e90040300f94070300804a80c1c036004041e0b61131b20802d6011400b41d03040030b0104810001000000c4410307820b140c0c0c4042078180410140e59450010b0800c2d001450444089003130b4008024401480207101e1206d048030303403a080b07090350400d00801d51b240614003c2030b0040c000001d42010b0103002d041500256003000b0195582c44120b80c0c0703d95600c080f280403c0b004220003030800ba09507600811080b9244a1070801440e01d48440599aa441c020075581510400040c865181441d01d0315101a403048401914810103981d1a9040c0280d813003c41c500c40c0310700e0b0025901846034940214401c0400d00d00d00e2846611414014880c8580420300540200003524002000840c150400301510100d40588002c000700c44a460764102e440c41003140d650381c00482040705004c0c14800303502111151001230111007442019546491440d4020389440c85001aa4201045140303017022920f40741c0401000c00b50700c1070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 989083776 1250 989082526 989082539
    0xd14040f0318170708060105060a0206040f2102011d0f03070206250c1a070201020d0809010f0609090c0906050a0611100906090b0604050c0406081008031b06010e01 72
    0x3842986001010081c0108031604020142410380000c2c1019492024580f000d1010310b640d113035050322039031100340281c0d4000a86441c0000664408190307980140c000c0d6640c1d940c7c3c00e101081e00381030403941406110520901504d12806140c000c004680000604120355000e50a0001314035a9a20783e682c0410440b00307a03014080b054550392039050f01c071541c0741d00f508945801c4110f2201c1040700440000c10044040c0001c0b000301504690fa4002c04840c6c074160107098441c580b0401c0006030142e07014101c04100184501101c036408901e4900001d84900300b51850340030760b0a203a0108605544500c241c8040c04590030b41940101540c41c400c01c203140c41c100108420320298070600e010f001c1c400340e911869180601200b00c20700880c5074200031544076482c0980080111081c00d4605c1c0003a03c00043c21070030507205503805020100340490070705140036811100c2560060034a0260700d05d001c4d00082409040002e40402c095401c0c20402d03c50059140a2400905a00007000c3c004242c0042052 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 989085026 1250 989083776 989083793
    0x408070311040609020c03030403030605181317160308010504020c12070c1d071106070e060708040504140108151003200901062003040503060a0c0c0807080d1404 71
    0x45903030241c01100010070503800900181502d90190440c14000552104a0f56011009501c624406d4074100070403a1603038148030800c0c140048880700b10b011140402e2032070340c1220850068074800c80c45045201074109031b00c40c0c0c44c0c01428174544203c14035002c603400c0607001030b85d0502420b02580d04500f400035500300b0076643c40c01100d087d04140000101e100c284800c41c84518058032080038405035800351403040c860100411100d440000340c41e19012041440d0101e40c581c0a200265540d0031024190010000103a2020360100c801c000100700c001555210350040300c400035400d003400d00c00396141c41e01280c24a4241c4031201e039011140000c02c0360700301d00125080700343c9810004400146010aa486001c8960008450b07400314200000040b1990f00040d04000c0d00d03504009007104082c0d0060f500d40d203000724020294140c02c920000b0b5541c0c0001d500091600d04103181c02800b4034015101c00c541796010540984900e0f800285a0300200e0490040e51040b00c800e07940d40c0c0042c41c05481c0c0541 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 989086276 1250 989085026 989085029
    0x90a0e1b190f020a0c0b0a0906020309090103021c050609030c010c111213090f050702010c0306030b1b0f0705030919080309040507120f09021e1c0201140307020102070c0506040807 79
    0x10b1040e04041008010300c01c208501841e64021710703820103103032195012aa0768005081100005e0040000412403a2000c4240c0c1c0344600064007a245c0c990031942002949401c080522003100c0103e221800032807000c100150059505502541c0e440c60304150749401c0d07400051160040c0309110b1080201e1040001c4c40c0703400c009a42200680301d00c00d40b90210f040e1071295005512081c00c2100c00c22200781c41e640501d02824140e0020400c1c0d8034000e00c00c0c4c4c00d40d0700b40c0c0300c040c196480300000611007540a001049880404800e4039181c14403413446209079400c51441940d0b15840421484090f0400740e045d2220700851103500c03220b81c3d2920135055902d2182c1c086013070091b52035502285035140207540e20b200405401600780900340703031a80100010b11405a040c0c0c131808a07038907480b4401906e002081240500a44140a90360030180c100c018807040850032410003055000c4448499201c201a5000d004141e0002da03076501d09040880d000c2c01c0d00e4200d13604c941806c00040090aa00040500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 989087526 1250 989086276 989086327
    0xa06091a0909130206190f08090d090501230f071403190302090d06060b1e040501092c10180c0e01032a1e080103020f0d0602090a0e1b 59
    0x31180100752000c6105c60050507800a0340d0100312240c90a07460704100140504403040c0e131030611543d5943c03480ca6850607403800645c04107038115424401c5500c40e1110064140040c0c60b07080c100c12860f03030138a07419403203007544400094010421204221440c01c03041120000b0350300542c1003101c0c10400c801106003c0c2e04540034994001215606510740700c0351418400d400c56010001c00790788030380e0104594480342c0300c40350010810b10030f400c3c402c81f20000e5400755401a034811020b20b0400f440148900050360140e01000700103984a1f01d800c3e2100815803103406a510510701c445d10b03041c00b07100c0203005485440d07400c2d1b00342110740307003044d80c082400040302d8824030b0301040b003150b101d880782ca184a00ca0340010245c0340c5403112080d00f9401c911012079501b04d680fa4584281000041182c8901c800e0100940c0031014080c14111881e02008914005004110044c0342401c614001004c903561a800340d42e02101c0c4004000c500e40ca1144c1e1002d0a064141015151142c144400703410303400481c0c0c025 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 989088776 1250 989087526 989087551
    0xe0109053702280f0f0305010e040b07140a230909060f060c012a0807122d09140a0f120e130218121f02090a06091a0909 53
    0x40c3c800a1030325250030b26240b00b1107491036a4001c8000c10b9281c0e000180c3c408624400b15030340e84a4402e204c1c26048a5042681303110170b0725299a070105c0d2080203000c9500b008401c41306200e05ca02d0f0704000300001d4a498132038030082c00001020786a140380c2c5c941c0a8090040a100c24a0140c80c1e01000683c03104080700c0002c101c0b400e00c800218140a280e425110319864881d1407045038000340030f00d080c0c10026250171035015955210480d05603004456220026a000700640210520350704002c01004120b4010f4402c28088050411801c031169941c15200740c0300c20720321040c41188044025111007070406062513100301c1c0c840d00b00341c182e905030007490156041d084d841c581c0c0c4034280010390650014444c90582009140710f0000e5008182c8180c400d440c0021011458074015001042581d610405403042c000c001c1e40d400b413400c000182040101c1d4007044034030743d640c1d5000c1c1c00c2c0018007410b4640402040c01d0ac00c030010500a4142e90300d00b80300e0704101c803500983d070320803800758051500e4680 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 989090026 1250 989088776 989088787
    0x7060f0e0109080309130e010c0e0a090b012a12020c01090b041422050f10060503040f06021809011205010b030703020105091e04050c0c010c0f051b070e0109053702 72
    0x5000040c4029038044d801e55227044100b003441580058180e1034901c040301d006800340e864a910004548044501c1c50100311003c00320f03401800420700d00000000b080724049264500b50b00d40361801c10f10100700500580058020000315038114900d41e0140001480d03441c202030900f07112076100d0040c03110840c490008040310f09114054a1251042c00030910f00600c440e0528050210075020240d821110340b81c00200c02040e510301c610152485140c100110049400041d01c56000a44c00041e0440c1074071800e0340001c8507912403580722802003249003a960600340c6681009400c684c466020507202c0c0d00040300800150f130b400002d441001d41d08449900903112254201400205008000d9401c203081c941000340c0c01806102812508840c00002d0010141030441150001801d201d1180860170034000c00404038592386c041c1c94821508002ca94103640c076021241c4500340c027684000c02d40d58841d420002e84140c402c0d41240418908041015075003d50301000d0aa022003110191a0300c0c0d01160 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 989091276 1250 989090026 989090059
    0x409091a070f051308011a10050a020705040e0c0a080610050301140601111606020706080619271a010f02030309060403030b1309030923061902030c07060f0e0109080309 74
    0x1811004101201c0200041c1f8040d08108005007810802c0608c0382640d45d52030300d00350b8011822160380011030b5000d0306402c0d0501d8100001812030000010f002d120301861540e01c0d4070345071f5003130b00617150900c01440c41e0310304031031680c16801e480d8005038043c4c4d0404840500c0e01d42e0141030301d03070440c100342800e5a0801c1c0b00c6048518001c00206003a182032401d18001a21980220302310f4240d0b9015941c01019507101c20901401c00c3c0c8201c0e0118071084500401c020704800154200030714000b6546480700c8040c5e2100f61420b07a11880c140b03001d0500c020042d2600f568114600c2d480385800c900103541546001160903441d0135004002178185070310384d0b101090559904201d40e0b03503502581c10810881341c0c0c0c4d00300100783c8a02801070450200070440b03981071030360010842404142c0020b01c02c1d480c050a101c078040010030307000ca050080d132000b07000390410800700b440704802800890b80d407000b02c0741144800500c1c880c5d94108440c180211071009020300032022049840000e400e0b20960f0351181c1011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 989092526 1250 989091276 989091307
    0x12060a0f050d08070f0c0b04030204060608071e030605061b240703050703140a0c02011d1209060f22150804030c03021c200f062205030409091a070f05 66
    0x217100030402c003021100801e4006c098005441524000d95003080340c242c0350107098811800035108c00e40441c00380c045aa144409408014408501d60719001c203402d80c1d580c0215415400403002500c1e03048126521a60b4a03008001201021600c00c00760020b40b14003010306074441901421078001c043e12103000030580ea000c0d401c40c110307401c07015049807080d103445445000204254003900c4015402c021601d48a10884001031110b8181d600c060b0046c140b180307048206a0303100c44000c0fa0040401d0010300e142820b03900260010050700c20030044076540f07081060f020b005464000d540540303c0d2100e0f918040d40d0040303c10394015890309003126003c01d5400c0c01d03441d00d504403001d10080da00e56240c0b03000c1c0d00d900c451814038243c030003980183c40040d24441181c0729003841411120301d6110100041c540030f4000c4100305c5803030042d0b102e1861030a80761280c07821075202d900580100c0e9150304030314007006000403071f5a9061714610648902410a41c400038100c4c0c00406001c001c0100c08192465480100d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 989093776 1250 989092526 989092553
    0x91401200f0f030703090b0901091112100606050c06011e03060c051b0d110303040b15010c080703020a030e060702030c0919050907031a1605031008010212060a0f050d0807 75
    0x8018a0743c803450203c0c4002d000d880408011150340c2c0d0840f0100340842d80500a500b821907000c4132001c45412000d040c03001e00c40c1c0c0d050f0b829080340714400d03000f5420040e82c03050074043c1c016503803207903514280f91008034035110060348051043c101c29002d41c401540100814001c2d039a100c2ca0101d0400c0012104441901504000519a04802220030301d88100024000f44400c0346496089090b60b890501d03a48a02003120064030316001d903c00101000c00c503a405c0d085000050400030003c0325152140e0351560460f4030102d01582c80190341c80141608040c1c2c011280c4021600c8900d440780c1d9901007030f181c10003440009e002d56034a4001c036880110b03400700422900b072888410003c51400c0c0c0d03c2240c0c4c0b4030780c51009071642002040c0401d26103440000e4544120302c01c5004507024041090115815400144003110844541e08081000b031020700040408040001d00c041c55402d00608002d0020024ac0c002005c1460f011010400da40350b07c0181c2580c81c2e001905141c54005030308200c40602d405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 989095026 1250 989093776 989093797
    0x21516020f0f2d0d030b090a11160203120307030501230f090a021c0b04050a110712211a100c020105070f0b04030c0605090705090105090402041b03091401200f 70
    0x4d1801c0030600d1a0304d51300070080c01c2c40c02c481ca441c0300d0703e60b0108035085603902e8000818101c400c100d23400e8407000ca843c045501074030250407540c4009841c0c1500c0e143d0340007035501d00002510b80d80108940100e926059404140300f003014510740111000084610070b83e44401400b0b04501030004201c0480c41c0c2c103441c2d13108403c07100c031070850790346004840080c0780044120b0f108915000c00304244130400c1c4503a01e01e04881c4240c0d03d24042c01d03a2190840c89071001d1400c001c100d2074880a5a088204c1c128940140b048088003080d10003058209408481150b20340368000c0c402040b45401ca07583c03014082d903010b5020300340716039142581e01707083c40820f1056102030b10364500b60003400300309980300c19010541d90080c0f4080019458641c281038a4041034070959611002c40d80041c4907a15001c2c01e40b1703400901c014400035001e4540401c0d070003405484850800402da0b241c4408040c00901c0b400d4035a5089414020000c2551a00c0c1080e200e400e41c04090140301c60124214644c0c008000c11107014040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 989096276 1250 989095026 989095033
    0xf0b0301150e04021c06080304052407020310020703030c020d050a11030f0c060108070e0105060415050904090303050610082a1b1f0e1b01021516020f0f2d 68
    0x12a80c0803100b08201304170991240300c2c035220000a040c034000c0252400c0d40c0c40102060000f02044010060400c0b814507407030f07581c26041051800507030381000000e0741c88400100141e122007503030a024044621340405101550084545007103099030060480301400c00c2c80c20708500d8031007009a40c034918059010140f0103103400080329800342c1c000140c1c1034100c606004c1110420340e01c514a004800340288030711030701f11078203110502c02c03d4105440d4410000f001d203031a900b4a1401c600107130640d0390b506402d80100342e0b181c3c20b0007070504002600c1c1074505000d04100d682820100c46000c500301c4c3c6980380b0710303000d08080125a207102c414812a07420f80c0500c0c0304004440b9040c500d044c1c448030b01c21240c200324503904014080f5800c850181c403003001c400002400e44402010480c0403d03140386000541180a1199000014000c1c02c0e0494000e020341c0c000e0001c06100c85038041d1a060b4900844a06a40880e551640b4000d000491009503070034105483d07402d1800060601c800030007529255042e00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 989097526 1250 989096276 989096287
    0xb0912031003060c090305030f03130807061a0d0305030612030c0607090f060e03030702041d010c030b03011406031b0a090c0804120905010903020f120703030c05070f0b0301150e0402 80
    0xc00d5071250029a80030f01010054070508120684d20459148002400b40c1c0043c08007003504c490340d2001e1940084e2103c1141e203440440e1355409580e501041080f00e030550741d18030020a050300103c40444c4500103039422205661240c078040c010340801007425204041e50703414810310f080d00b07100399035240202c1c004a50003811302601c09401080e1038001d00843e0340d0074440000e0100d04c00c52082501c044054050f501d032407020340a2101620036403842c0c40549401800504040c1000d201d00d03000c1da081594001804a0a0704c101401d4880c00030300c2421102e4402e01380107007a81d010490b1020700b02210103a006d4841d4400104002c0300c0151311180d032061600407150384554012080510440c8285034031042106030010a40b0584154052140011321506040c00103040c80c03200486a401d0003424040310030825410b0a2134114950001c80002e088640392208210041104002500c00146803185d00da04116504046000520503480c080b050f2a4400340d00c0c41c095400340c85500030142044d9070b1103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 989098776 1250 989097526 989097541
    0x705060c0f0c01050918060a03050706030b0a173a080403170708180a020613030b010803040b0304030e041d060115080c0a0e0a09140613180b091203 65
    0x9000901c45030035107008411a25031950b00c510110398000000600410400b0301e6840d03000050b110041519800c103c00050100102e04100303c0e142c001c00b0940c1d400b1030180101002c3c401c0b958890380c401c44e003216101034140307512040400c0306104040300055000643c94006504015944040c001000302e01c1a00e148280550340900000c1c0704a001e81c5541001c00404c002c1e10240344004c0f01c050303000800d2200401c06092505100341d03000b40844c41122030a0b0302980000d1900d600680e0006140201c60b0750400400801180d42c0d030041c1a05c4000e0340c00c103450019245004e1100400080800c950740701802d0306a51290311494408011540314643c40c105c40d00181e035540e0b000e000e0702c5c41880c00c1c031642d90700c241e02c03031403040344101e030960a02414030a28140554250b454200070786c1d40421054008943c0b01d6080c442d0410b02000b12040010380d0505006110000c1644003050082c40c0c10030300040000191900d003640c08a0b40311040c027540366100c4148070309104030090080e140142c00018000c98 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 989100026 1250 989098776 989098783
    0x7060207020f06120a0e07051807030509120f13120b0402010e030a1709010302122e210203010204081509010b04090c060305190c02010e0d030b010914030705060c 71
    0x64801ea45800d0a0b481d99000c002c4103005280b07500005818040002d030105500342c009040ca0401c0004a0b40035580324000294240c504503ca204075802c86c00820480a03414090305812a045c40060b0001d116150300241c030a1140443d91100101c1c00909841245001d910a000805100c00380ca5004031007031824810700d5809640c160300142c09816070034268136000c11074840176079100d035009440340c841d92403001068000310081b03818907509102d04a0002000d080451080c6915110f0341c0c02d030300c00782c04100c501000800074484881c503186814004031002d0310741c0c0303440480700c2c00c40540d0300c214520000c0d01902c80d681044940d40105041d94035001041510b80c0d0088288800070700050086100f8041180d080c080054800c0d040c0d800104034943c0280d00c8243c0100a440c0002c20190000c1007003001d40d405461064010307036581c180c0d90700101c4140180c80e40004681740911105040c00c000802d03900341401451607c42d0310110f819440d1b0b03420004a40180b40c05407115440b000074098498a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 989101276 1250 989100026 989100037
    0x4050a030b0a0c030209181306020301120c0803211305031314030613080706090609030806030105150307050f1206331503040623070908072301090b070602 68
    0xe24100300241810f28028006e0300c000b80c03009080d01c06141800003240801000140c40000c01204441c02d40700030810600055028009040c0100c100340e840b482c1c2440d444c462540910400d4105102d04008800c42480d136000ca2001c90f00640016191a0010b8030600c40c10304005065201c00528003002e40000005a0115410001040c1c9118080410b041d111b01c81184c0b11f41c1a4003504191000041c400000f8105050140710001044c032800d41d1040201c4454180030740100309048100501031509004c0c1e581d010f40f07010348103842005550082a40d501040c0034862040e1004210030070a62a4a40c1c2900c01c040003000321003442c10301d400c2200f1030161989050742950358160600c01807c508004000910380060900707410300c0600803002000f5000600110b91494840c0001c500308040103000000018100e10010042c0c00c0a02020b06008401c0e400a1030503000300d0810070081d0010400c80880c02122034601e41c2d48010000104c2d1022444d0304035192003403000c2228424440590f020b400d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 989102526 1250 989101276 989101291
    0x42307030b03071a071205130e01090e011503080d0212250809030d02030406060801050906060901140f091513202503021c020a1b180c0504050a030b 65
    0x4907003a803200c0c43c034810444c2d041e4601014a808020320000210607025041d070124991812034204a040d0707100c0c131031800035a84050621410400140000798681c407690000b6040203000708040081e0803c41c02580d5658030001d4103a60b00404c0307904102d4525011246c50a0070141c15040d107107400200d0003072000056100060100c0c82c0f0034900141030146888a00829a060080d0b00b03002d02407032507001a5000600807100140c4032540003500000900450303010310144009041c2625100050144c2000c05a03c02203c0500c0c1030350385d03200b03600c0768000d1140d112001d85000150f036a512021940540001403480d400154101300500880c1850344814885004d40030080502c19140c20056075501502c54042c0010058007450745003268039540b0810b02500c43d005a40030a001d440441c50a0030100c402c107800340c1c000020030002c00038494400c08034075850000080c5506d0405003032140144094070b0280c5134030b030744403178062070320f405001a200202002004c8140054584c50320400d0b1a6041d80d004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 989103776 1250 989102526 989102533
    0x6121b0c14070e19020301030507120314040608061f0f080a15031a01060302250309030602130e0901020c031b010912110d1d010e010e12030901020709020306090402042307030b03 78
    0x142130800c50360080701d040703e8000c80140034141c28091880c0341d40052000c00c5040c0f00310b1640750580000d1850140c0001c20668803441124a04074082c402c280c08c1e55180b80c940d000200100700b00d01030f04a404244008103624018403903903200385211005140218180b404100d079044000f003044001090510b85504040403603e190342c0e180001d030280e0203003644103030803e040b0340c41d00c4400f807580040c8400c8080c06440c0908049a480d114141240d00c04152420b00c2201c01c0d60511104d1401b1100a2300400c12000841c90268281d00064480c0240c100002d094250901c440725220070941000c07440b26001010b0002100085001030040800c6240780062400303941c48000b4654001c1440c0101805107500da1840c003a40c46c0d004540030086503c03a40d041c45014507050445884070458140070014044c02075076501488070000e8034158807940081c0c2020f004004010381619010000c80d0130a40c1520040340284c0c8141010012884154400385009540e400f0004442d500d03401c001a0400254181c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 989105026 1250 989103776 989103811
    0x3070b07170301060f0e01051b01060602010b0a080606120a08160201120c0806120f061f0e04200604030501021815070309031704050303070303020406121b0c14070e 72
    0x41c024940000d00c24900450310340d5002440403030068260105203241450520719101700619a2140c504069000c0456695200d50a211103a024811143e86110880d42120103030f18001200e9a5400c0c018060f9004625000714481765040410203104896480a1034030744920800032840d8441c2400711090b800101c091902e641c20025521442c3c80c3d11810350b451040c1c69440d00280040581c031604030502070321400c16418440c900a01603a8000c1802c4502c20340c40d600c034041190f1824016812021004500d03109000000c1c0e00f501d505d11490791a6a00b030000090103400192050041380d00c090000e500020300518200c1e118004101201c0c022551140c13030000501c940398450003400c000602107041c20606202040d01c0c0120400308215a1179010703d080e8490340030a055030044a801c03404250041001e10000b0380001070320301841140e03001008100f40102c003d1500c940a611150b0074045140c490505002250703880c840e15217406000c5405407541d501260b16084d000322910300c000102060f2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 989106276 1250 989105026 989105063
    0x10b030f010c17060607030f0e100c02040507020303091b06040510030906050114210c0a060f1106100b090a0b0c070905060f240d050103030e19061211040503070b07 72
    0x1000780260344c050030150a01110340d409961050024205100340000f44020078500e070745600080341145043e54902000180610503c020b640d40030300898203640040c8104041180000780d088075041c06100020701039102c480c08606944207e800440d0032010518465255035010f40000c0780203031041c030381045242c0c0d858008444c82e00211600315030001c0c01c0c0002c026081208120401c911840109451500b041d40c0d002400e4810640c0c0b0a2001c50503a0004a05450700185154600c1d000d46d00074142078034220105d8001c03003020b03000d840010107002c80c4494203a143e0500b481d02034480004001d80d260180700349070f42c0c0d6250303d2007013040083c1420009990b5041074402c60b0005d0802500d4201d002d15915540301d250300294100d032000e5801030112164a44007405058001c41c000c1d2140d5007225400000c0c800c0031004c2281016054054103c00c000440e0302c1b202d42405000c010344c1c0090074101c4107600542602c074590205505106034803002c20010421030041507082d00c561a07a483c1d610392180d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 989107526 1250 989106276 989106317
    0x6030d030b010806010518030d020109140a0506010902180306090f0c010201021206361e06091b040f030c06080f0c030103021c0203010507090602120408031b010b030f010c 75
    0x7044640040ca54002185565000383d001c0c04600350385c2c22443c00b0b0503001001003031030070300c59111b08070060b03450b101c001c41800303102072070200c600010310041c2c001c40d251600c48661381e01c0184180f094241d030000301141a22840a002440f1480c010140c1c1c2017400c14401040d960380040800f074440303016400e40083e081d0f005108a5000d4400c0040d80c0e10640d40d2801046070b000039401c140036104140204141e121081900000600d0200c01c50f61804c0e03007002607084407100046604403006400d014240101d580c0c44118007940312203c1d0303d070100c230a44210b02d0143c050049a00030030b000c614080307000c01040b800c0b40319003094501c280c3d00c3c141d0b07503500d0050307030440e4110940d0081c02d010000c00041c009410120541805e1003e159085015181d241d40480c0c2100c500701c45c5140009c041c03103001e100b01e903030511104100f4440c80c10443d04090030540160381fa0b1103000c030100c00450a0281e00d404a00080d0840c0401c0c01d8014140c61605544a0509020b041c0352342e200c0c00040c141901c0140764140c1007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 989108776 1250 989107526 989107541
    0x50306132c0d080a151505070501050c03040b131b18110403030c0b04020f1216060203271201020a1106070c08030705031308030108072606040f0c091406030d03 70
    0x40d80c03441d0864841c104c1e120018440a1114110340b0b02402002c20800d911040355103020380c50f541c810b46c5e00e8049041060841e00d000d0005540c0d40340400520010a41d06402c0c2508451034114410b40c0402e41d15000f50601c00b02d1091a908014141c000501106400408031444d965680140020303032001c00211114070803400001d0105039000315410110700e41508281d03201c5d20140c280034030441c000740000c04003a0a0714042d0030079400034925a1244c8201300f00c0d14000d040b075000450401c0d40d05029101e11b82d02403880058601d007400688401030f41d07041106002880044001c660702e00d90144000d0010418802c0d01189110b098003050000b03103e00d414100d03140d00001c0a9046882d0807400302c95642c0003610502208910000e201d0124018200544c0208541c5c401089043e00c2c0520142c0104402c0707140021107649840740810301200458030a51081d400803846601c80080d1401d030103003d0382504001c07d410b01d06800a01e83d003087c186041d0107900704404890707080c1030003a400c5090325a003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 989110026 1250 989108776 989108803
    0x2606090106051008040c051c0201030b010c20040902060c1c2d0c0c06211107060519051e060415060f2a141c050306132c 53
    0x3011007292912403150b07650070a02c0340c02c0088009079034600151503256000c090708c010440c6040e04904668151064104a090a0034104080b0b0442d403110356104841c11038644141c18852007115059641d03603c1a540c00b98010310070303034550305904141941c41c0701c1120000d4202541085d443d44a034014051020107090710703810a4150241c0e9800d51003d408000700e0071091010304565a80000d072142c4000f0094a4203a40b940943d952100b0030f40008c0d10901d054210441c0790810f51420110484210303103403681c100c000070801d5202c1840070898049000b0700b021180c0c0c944001d000003c0c24401801d046007840810041a50f280c80d410001180c54a20305618160710354401044008c0c0503c1c1110303042c02071420a00100c00380600c441d100036110100902075030030103110a00c00c0016844a00c40004d00c440700401070f400c00c00c07038004804c114121500301806004400a084ea69801301a500401202c0600f8015910543c0d0101310041c1020030342101c1d281d0b42d03a15854082c600082d4081801d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 989111276 1250 989110026 989110039
    0x140708092b1e0b1807140105090f0d020a120b01090506061614010c0509190b1e13120b0c1908042901031205040b0301030201050c07260609010605 64
    0x40d550114014400c62410b0694468a00c000010030180c2c680c4503c26013002e828001480c0303968602e1410040c242d0005000040b0b041c10300c40712668040b0941e200d81c2c1068a8070701d42a842180001e46c402e0140000079071110ae045d102241d10b210302c008001450303115070441c1d101a40c03a04d0000065070412107200e42c000310280450000c2c03016000d0911261405103014080c440a1103032082d0075280c10b14408808120000784400c49401c05000f101850a090b641c400030382ca0030809840031506c02e0004500e0068100d013000001001428116105044810441081c19036160102c00800022050588140d030b0450001910345c00c1c2c04040359000b0483d206130360140341030301000ba00c1241e0054001d55a902810400e40d510310501403021844800030350f032a41507585545484070b01c485c5080744240c01c20000740000c00003030340e40d101524152582401c1c42511014104061454a151a8002720700d4610010340e070380f402040c4190204180c0404c000b40d4549646103502c4a0030f03a5402d128650700285c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 989112526 1250 989111276 989111359
    0x20f011b0c120c060e07171207080a02030c0307060f050a060e18030705010510080609160603240b090f041109060a1209030f0906020c030705040c14070809 68
    0x103021600d0b81900c07422600308a02180c1c21a260030084900007460718035650300c4110148000d0740c081c05101e8424900c0030003024050079203284803640303016403080241071030320108801107124000e1003610340c20300e0000100c0340c60300d00d1403e0540c0500790140c111044107140101144c003022041c000d180079140c8040b4821140e8444803200e400d507480d140e900142d280000d0208800040007802030394090400040c40c0c4840e541001841c13030400c14090090000741e8804c410101e600c0188805e05012104c242c240000d126108140754a424184114203821203010341c1004154018001d010784450001503e0810f00010450140411a04103c43c201941c0d03006002d400c00514003c2c0040103005182c2ca04141d45107040c040400a070b4070307520022004901c640894183c030b260700429100c010540d91000f020024a40c1c40407036111003050081d14015502c99003140360950280d0310405801c00071410650340c0e5136440c1807c0030560004640d0900c00c00d0b0781880a40410080390300e03000960009052030321a035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 989113776 1250 989112526 989112533
    0xa1119021003110d020307031d0c010f0c020405090f010608010905030d0b120601090c0f050415200709091202160902030916030f0201110f0c0d0606050303030403020f011b0c 76
    0x25400034200001c150f00e400300d1070340e9400700b100a8602408003940250710390034a00c0000d01a1030f000d0360404801c002c0016a00c00d402e400040f0340792500401c1c245290740e200c50b403004031042c900527003010350414106030030303c100660002000003012031018001c0003107546403c10507007a1070130204003418982c0244045504c00c0c102c1d40c03025049140052031103884d0f20800007602e0030004241d0040e081c6541d00d40d800c1c40c03900d80040c0d1304000001c042c5001850312381804c0e280240d407480655610b080110100111303581030191007813090300b404201e0890718010380c4d50840030040c0032402c0c400c646440c80c00764520380c0c1600014280c949922141c0300191014188813448000b50002409000188540031000500c1943d40d803441000d18019244545042000c0c00050080da4001000d54415802a05080f0101e00080340d170781c040c070303604407521142a455401d00c0710103007840c0e8015a030f2600001041c041059000110040c2911100b070080c8109084049108058404078030080d020580d482d1961002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 989115026 1250 989113776 989113789
    0x2505180c0705010c17010f05060f0d0e161e0e1816091a190909030e030d09152a06090c141905030a03230309030a111902 53
    0x92110380320030308140890312450309492240143d04046190708440c2212842040841030243c524a52204041342c03410380400c0c45407155200c3c03030118140c0800c0c03146500900d50070050390000004115048103006031540301c95941d00d40f148840005820101f02c048003a1009004125900100140307120350b9010700a203840d074030000f8001002c0c01400f0580052406d81034601014100c0004e002480541d17068401d08a000c0440041c1d1184040c40520100b1b004140050001d403103500c0307070200b100c440c203203002c0d210040c4511010740c0c0340c0281c0c41244070083d40002c998045500303070b2101240c000580802518002c002540d90303110781c68142038080110880010000602d4880c107800543e200e8580c548060040064218042c84445003d9104440c07900208910003001d825900032052403034000020307036400c4d00c00c0c40141840400c030b0752405421440700c003446031720304072030f00855591514100b00c07502c1e5801904070304003040001d0141000c0c15000035603007150503142d005070390f2404080c0e02040314 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 989116276 1250 989115026 989115031
    0x5040221190602040603060b18040c0c05030f090312130b030415020a0909060b0c0703020d1b030602030618150d151e0c0309030504030602031b0c250518 67
    0x1601c1542400406440501803010070180101c100680781e90030582c0040556040e940a1844210305100328225580340f00710844145070110b400081d01c0d80004000d0316000383c0394601900b24000401c000c0e4882c074119009010402d0228165011200f01030100c6806024480c6102000310140c64180103e0788002d00954102e4020100c200d03419007441c0800099a200c14140000a0003c03c0200701c29400e6019140140c4614000541000300d162000355858040f440702030f2007501414406014090300ca10a03030311749012907050b01035564890600300065032041da092401303002681c11940040940b0001c00d40540d03042500d5848401010f0304218045e100d402040d1070100d903084410031a42410302c1040039209040000401140b520005d0204591070100391005040c20110b039000040d9201d0210703802c1d070741c4c070241c0181c4036110440004100a410318810940402c00510b800c13140c000024100582c0c0104003001100743c51445040c5444034141c4503481d0420302d040b4a900309a80c0440d1401c0c3e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 989117526 1250 989116276 989116339
    0x302190e0102010b2d12030a031a09070903031403060d061e05090d02122b06030206282a03020c060703030e120a050f031f0f0503010609050402 63
    0x8410f00325400040c50801c0d03001070038107043d044800d10106040e000790b40c8100c00000301d644400600c0c0313001b00aa2688140307042ca400301a40c403294507081015a40850842c04406410003005181401c0c000d0070915483c003042d400b0a59258044506101c1d41c0300b1203200c0c3d80d01a00c0248030128565401024001e41d504140d0b03508140030b40200e075000b4500c18144982c080000815010b411180041d0038000d80d8001030484182c1040381c4409051031102c04200c010f0340d18452092200307510352010041c1140c0d00b0080d805400020410f4080c507455010300c1000e10420780380d11910043c2c0406852000f15000382c2c140d20b8110100301e200c001420b408120b00c250090040d03a003c024000009040c40c2e0003c0340882c01f095440300313000c0071048100310001145180c4039503640b500b40ca80300084c0140c040c1c070300c2074400420000001214ac1540c02d501c010703e00d90200d038281403103440b080009596a800d01034240a07602c1d18400080f0102607000310340c0116006420845500c12085ca50183c3c0c544121021 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 989118776 1250 989117526 989117531
    0x111030f07242c010510030305030903040b0c071d040302070303031802030a12031401060c0b0a0e0a03020a02030c3f120301050a050906131e090803090d0302190e010201 74
    0x11800c1e800940200070702c0014010200d034240c5034400c0d2600f12842c001e06a0402a032406081050010190894400fa01c1e01360908685981c0d03240c401502c0c51055400003102c00d0340104820601940c000b68203420b45a146034030b2000c0200009500400084c1120080d005074403180c01000072074001d03403202c452011203015852049180341c000c00c4c03424110300c1c411140710107804e07200d0502d10780c1882404040c54540c8200e000075490004001c00001c80010b002d0a02074441c004a81a0105075210b54005503406040d112804d985043c042c0d203800341ba00c2e0a0b4040e00842d00030046911b0113030102c210541340d035000b540480000d007520410780e40c0d0141440d482d0806080019030412010058450710320844907085980e90f04200070300c9a4540746a01c901d0090310750307005016031030f50340704c240100c0041840c0000584192100c00078010030b0000140c1104140b4260706001440020b2000f1403003600b88904950301001400700c2207080348a003010705d1130443c60010748100c0042c444d6101c2e13450740a051001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 989120026 1250 989118776 989118833
    0x901090c17071404030b010e0114060d0c0216060203071b0503120f0f03011e14060f030402011e0203040819050a020d05071805040b0601020f0717100509010b0111030f07 74
    0x4201d0552140d0015a01b50240400400c01c1d08140ca140601615164112040303018035a00400c1550080e1440e400400783c640d00c0c0d151015108009d4134018400b03860203000302a564040194503a4080082a83c10092503600c24840450701c607504011a000034004028280c0500c24a8009400c4200c2c0f40d21126403c0041000608038500036602130080c0c0d0105a041180f6620201444a11940304185101400b440c0d203100740e841c0015602c01c03400c2d0349641076403a6138510040726080d46c11103021810300e01183c510175040c0e0b4000080e109481d040c004aa07010700307440815a110083ca603e004020343c1c0142179000050601c40011092248a04212000c45840e92540080c1150107500d95454560f41c4040006000d0806401b41e08601d080c0050052060340e50000c644416036805111491030603a50111071241041000240b2010b031a0010022800d11040440c042c04c810303851103002030702c0c00800181401d008011161000d40050020307207840d80a5954080307004410010003000c405240301d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 989121276 1250 989120026 989120057
    0x20a121406152413050111010e0d110a02030a063804090c0906081b04020a08041b0506030a020306042d0b0d0f050705132f0c070f050901090c1707 64
    0x5040604c0d0804420700c81c0d6818400014000207a032480309895038104040320031004030108412080180c5031800d1015034188002d145e1030401c107001e00035050705c80d40802c0d0b070901003071303500c02403804500380b401c440c04201010403481f0039400e158019041604e42c804010640ca060781c0903034802403245a00300c0721240d8641c0010101c88183d40983d0454205803201c0c2000494031025840e090021602117003012141000108030b603c00901c01400d00e42c0104070310011030500042c403401008001c3c000346e075a25000c92035902035001659240c0c01681049060f980800000c11691140c07005d18008040200c0604800405041803400c01070f080507c542d0b800307000c103944400d4409402d01590060004524200500036140c010b140502a100d15111409241d139034195005200465024864641c915003285044464030889070b550210703101300c090000f0292049000001140c3d411207030307200d0f641e030303618040400e496000e0750041c006489081a0000100c0000d04150403001c0c5140c00d2031117069808 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 989122526 1250 989121276 989121349
    0x30c070203070e1f0b0a0f0f1806170a1103371407080c04060309050124060801060f0525021003020c01050a150b0d09020a12140615 58
    0x1154003604d49140031240071122000000303c00141052441185840440b610040142d091040241d0405c00102120401c1ea441411406160030140480020a41d46c4100280014004010020315a001c440019203425201c0c4640b4040311402001d081c55070380c0e0303004a202d20110b40c80d02980410b2038a81220f66a140380361000e4407000d00700d0400610041c1400c000c5c0ca000754010600001c025420381040504840402138070308075005030402140c0c18001780380107070140c0b500700a00c80c1030701022196400b020400d2003c2c801259041c0c3c4400d441a40c8900d000c031001a602c041030740101e0f104003c000509038a8058280d41ca41061f12024044410b5500042d500300c1c230800d98100082d00820596a407550a1180c541c000b40041010008001000c2c1c0980340040140f0948030350031404540200700040c01e81080204a41c020503070100503480e2400c03840015142c4900355016008540c05104010f00080d4560040c040c480b20407820315902030401044c250488402c81e0084510782c1441035081c41075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 989123776 1250 989122526 989122531
    0x622080a0311190c1a09060f04032105040b03220b0106021207020d12050f040f030b01140f040b22090b0c1908040809090412140a05030c070203070e 65
    0x2542d45410b903500ca20031040c0340140c11590803d00340c2001040c100081c1210032200200c42d0b01c0d0b040642c1c0c0a1500c8642c0d07240c0d000b80d000359600100009151001c0c0300c00940108107481c400c68091005c1c0e6001c281c169a4079030301c10800404210104402d02008201c8400355a115900081600c0b01109103c0040000d07190300c1c0c400c0382d2800f5600018002103405100402c0c05000212580f4180452500058060500c900c0041c103001c0d040c100b40c030541c038410003c5454030441d072a050f0359229a41c11200000e035085220a03180300300300030700124901c003691844c0030403c0030003402061916001d10804c4002e041e90800d071980603204490000340c0d82e8040900039281c07002e9420000d568440d505220450b20001042d04000500c20050141c0c40111030300c52203584101e51605031220fa41e1807400c6400c0e48540c0b00c400f540008204100001c02080e0300401c041540b0340e90310914080d80c50307509000e481c041c1c0b415060100c1c00c28000100d503440c201c5d01810039035000800721040103542e400615581c1e4002d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 989125026 1250 989123776 989123783
    0xb2803051005010e09130303110310090b0109080d080a1808031015051602190b032a09040504080714030a080f010e06010503040203010e19050c0f0622080a 68
    0x450080061052415407424010003007030928090b039280e1100083c1c03440301c004205c0840b041201100d10185803103540040b03803440c401802c0a580341040070b0481e884032614440c00020900717250b140c18881d41318521550442790b180c401000c00803181c0300180d070701203402400586510f5844031a4203825030000c0762005003034065214a81d4908140141c403100c510b098200000010200500c0030000d9032003805c40b84403540a2603400100708061000410320003880602c2d1890403042040401c030254520000c41c0140d61103155440c000c03001e803900400401003000d82d0000c0e18420300c940c2100b801c09800c4290b01c14450311025150120544c1e0b40495600d510130151141d07440406d40100180d0440101608103030003880d03122056242c10107401c01003c0c020003180c10020048007190864500b500110301401381d410503100030908122030700700f04540000050b42e440c4103a106125040c2804071130f4440d0404003600c424682107400305c8a403040440018a80703000107141d48009440c020a02203001280d10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 989126276 1250 989125026 989125031
    0x51b070f052106011508060405040f080d090f03050c010b12030318210c0d0305010305120f16051b1503060d05030712020724020a030f02070302092e06090b2803 70
    0x717078210010302d004d80c0100524001c03031a020a01c0301040c0d5603c00400e03540d0b072001c0c0c065075840210000801406450100800a800c0c0c50560300415401101428418905034001c0041007026402c00c486442e1120103112030b0b401c02c0000c10036904520000f002701c50844012a96459070b0551309050701c41e92090045441800840c140c44107200c1400300001c45103092606210a50440e19400c0c0c4552602181030003040c03002801d426143c10000640b640403180c0242601c0010840c00c1460712102c0002502180441e03401d4001e016181c0007160f0000c40c0d92117288942140d545000340f00d08920300240c1a01c66201c2441040005144040d07a00d08080d41540030309400ea01d043d44010750b1720940302c3e0303140143d03c10540061650398002209168150113103841c00152416907130690030801d80341c002a410040c81801c00010040e411303100c04400c0008003048450309a1000e0450b05c5000b90f014083c001400d21034100008403440000c2c1480c0031460714542090342b2a48405130000c0300410311b1001007034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 989127526 1250 989126276 989126309
    0x27040201030e1e0f1203221e1a0915040f26040501030c051c050402060913050618071707030212010e090f030a0c03030911060a051b070f05210601 64
    0x4d041c00f11040c4600c800300100e040d81000300042c1104002484040902d4010144000a1091000400c0c40e01c442c841501d0120082ca410409406240c0c2c44000f1784400203030b00401d01c400340005600c941a080c4038420502034a43d5070303622007030400001064900c2e00005c1c507091035450040e01c44148012100c1e1683d9600d134505400581529814010041407080c10301582e800404680ca010010b040c0741c07400014140c0d160700c0014100e000d801c150300c2c1c2040040d10f202e10030b5001584214000c1030206c980b580c18812510300e1008502044a4140014001d81c3d49019030000700280c1da07030004500c0c1005814034080c10b00d020090b92099102041c0707021031806129040f030091180154580b000c802651508182a40247c5020713800d8100404055454540710184601e10100c41081c01000307200c650707074010307000c4002e0550300000280f541c00d030385616440482d090700141d26805c860540039018441413030001001000c0303004401400c160511114010548007040c030805010b130100101005921 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 989128776 1250 989127526 989127553
    0x21204050f06010609140d05031305031005360105070807080703140c0a02070f0b09210c100c05060106050301090e030f04151103030a0b27040201030e1e 67
    0x103034107071040c9101d41c000e20018409560f200b40d110040c1c81000000728401c03401c040108880e615045400b178250700020843c4030700c071703d001c2a040040740c01c00c07000c0712011a6000c05080c129402541c844041c03e140c80307200341a41c01010121601d0150085041c40314500c22003040c0d0946e1001c441100001d03034801c007040362081c1c004c0e54207030304110b0b03502c0c08014150040c500386014581c00703803441c0c08880d008a015122503200308803410180c0051030101480303941e1407100345005d80060031002d01c11400c05d4440134404080e40f0b03810780303d40c4660000f061300340d041c0810301c1512900c402000042015900040c2d003c10030800c4020f000f08039546d5015034039031422031f000003140c421418280d2550010400300e03026000b8001030301d00b40d030b6080070460400e958206082d00d600381c0402c001d90150201100f0482940704a070310940b0088e40550f6030940e84030700030703164400d0005081c018082103448100854055442075116500703040255003115040c040c41410300b110011400d03000165544070008455a5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 989130026 1250 989128776 989128783
    0x518100f0e07171311031e0606011b0506040809150c070806071b0213091211150c1e0c03040306050603150402180405120a03020d060608010605040302190302030102120405 75
    0x514881d501c3c062032900744003840c5411110440c101030326003441c000d401c0c1e0540e0790030702c50449500c4c01e03080307c090010342010800da15140b088404502103194002141d0880524085117030704c50368810050205a6100d035144006608860300950f00900c04a01940c000d00c003050091003401040300c01003008a01e061031651a01c0401000300781000200c2c9122100740b07070040100305842e641100c0b05541098500b10407801484105030180c04501800394020203541c00c500b040c924946103c007550554640c241c0e000156040582d030f80c40825004008a5403c00c55003d001d03e1040c1340f00902618120003110100e2550304203400036640c1035a0345082c09924501000744440d1f040055030070980c50318003030300050b5031015070526246c00c407070131000010704000081c030000c405c030403500b04c40a40307608001000600a402c800c0c04141207615141011415500a0710302504880350341c2c1d2901d1626040d0742c00e03c140420003031500308241e0745294021006940c2070015240807005102c52038018a41410726514 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 989131276 1250 989130026 989130047
    0x305040507210803060d06061d01050619030c020c0306090d08060405060604031203090b07080412020c0307170c090a14010b030601020a030c021c0501020318070518100f0e07 76
    0x10002c04450301100b00700030010294a441d5000361000d5160740d940c002103100701c00c02031001040c07945800b4021541b0901100a509054030803210012103a03200d000740100c1d0320840b501d1442c0c24030b100c891100a2071003900070102500091041d40c00d0b065944020916089003036079040b072a42c1051030440c95081d8080d43c030039840071040742c003031000c2d05000000c40d80510840c00040c0015040e104001c5115003e60080007006500100340d850740d28108000602c1c80a050710100e07401951f045800a101d403001403c103000c0907004020b020321503d40701038180c0c02001440c80350a180100a0411203541d500212507200f211803000218000410b4404001001c0c0140c00440583d80c5c240240201c50764002603c45281d641818030000703c0616000003203003240003580410060400149032000c010040d000740d40030b0444203440e404220f000390001901c41c4424020b0540000b20b0743d9464150258040000d034000440c2011014045c0d298a00090226540c0d080101078010203800d01c511540d12582921 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 989132526 1250 989131276 989131289
    0xb042109030c150903050613030e04230a09080c03131d01090203040804230102010f091a0705120a02220308031b1b0703121103121306020a0305040507 66
    0x1404a41142d072035440010803402880300d0101e043e004201858010300d10a00a1a0090101c5200d864200c01035044201c0c0340c40c0440c0003420140b070080250501340161700d6441c84070401200d0141d48040c8003282c6420007403604141c0c03a100c03d00c0102140784d00e001010350980c141c0141d0f644080389407450b4144082a80f001c44c00000702c00c1e074407001c1076a80c5083c0b81944c5078103102581d2503c032410318000a00903034004a02c803202c0f5042041c40f611038500840e89040c0282c0080c000c0180010000007258100b1a0141520748424800b0b405000300d000219031041240c14494181070403982c140d524070400301d510301240c580c0024001c3d1000c19a1a18000401440480302c910300d081d03070303075510807400040d200e18000c0142000b15040084000d0036600f406c00d6221603020010f07400e0a0450390348452f4401910903040d104264101c0034443c12001c0010b061000003185004030008a00280c040c000b4078822070100500100e5002038510300082005078915940412142801c2c1000360820503507601c000e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 989133776 1250 989132526 989132537
    0xe010b120601060503160c080f0304020406081207030503130c03031101111801052b0902150403020f01121407050a02060f04150f0902151306110c040e0a0b0421 70
    0x100f080e00d074420100e0354029110807042d01001d00790101683e000d40c480303000514441c000315a401c2c9005440000d1740c07041d0f0081380d0a210440c2e684001d540c40c4c0e049528070304581c1d80100300f4a00800e00a00043d038200c4104808a24101056104c900c0700318104e1304101c0000344665000b1544107070900400c0035a00108095524000000925003400703807404280e54184500800d0444003146406101c1d8440c141d4a5020319140001030111802046034107000c9104642d10807505990385030901c1918140d0b58080c01c000c0380084074a005444070362007152601c440c81d48910454681c0455561000d015070600d0b200c2c0e03612100b18060280c01c240c00280071000e015401020040840c07140d003c040b980d104803650001352030f210220300038041c00200c1c1c1c019400100f0151114400040440200a0201400003540005440f540100c603070903450030311032032035074440b0031407103400d1034640c1c0140e0200442004480c107980980d641c5030b0006000b2a8150342d00240d00202d6141308080c1d003003000c28050140f408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 989135026 1250 989133776 989133779
    0x1908010203092a210d051e090d112202130e07021e01020408060937020f120d080604050105030d170a0b0a0305030304050d09140f01030f0e010b120601 66
    0x5030905040c030303803c641c0301d84062465907114009810400d60100c6421060300d500000c1844084c010364004141220255044001040311455030000d40d0aa0310f401000340c00d2000840d20b40c0c0310790490485105503c0001103252a01007c61030829015045c080c039800341e2243c0b0048004400002c07250302148010300c220040001c03241d404242400c00484090015400301040301c0168021701443d000b40103144284400c0c04003029000920320907180b10340c000707200008810000103042485a48000400c4281544038000501e8803802e040d20717041e409444002940c000201085ca0144444450404140450240710031401c00d80552400341c0400d400514500c0c8030007000514000d00208814001000000402c2d2140c11075004200c44000081c1b6042000d9103d00f01a6125401907404441e24800d0010b01c1d00c110b401401d04100311000324002401c0f51540409000364040c0401e807003410556140d0f80d5001c2010b1174481d5081a0b500080002406031164040c80800c050b44003c842090f03124600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 989136276 1250 989135026 989135083
    0xa08010e062e05090d0510060b0a02060c0c150406090c06111914060108060118090206091215010807030b0f04080702100c0206070b1f031e02190801020309 68
    0xb5811010050b00c07003a000340e410040c004503042e0081c080c9059200e0048048002807150000e650811441d0f842d0042012a6680394040340754454554001c3c00f5030040c1000035542c03411400601113201e601c1c800d90b00c02c0d9400c4480c58032024001c0301c0840c2e41035074400030b1606024004490201030070080c1403521144a0b40301c0620743e80d1541c86080400411070b04850b004000318094102c035201e581c5822201c541d41c554101c0340d29190240204c3d0781c4a243d2002682040005000d02400c803a0041c00c000d01d02424030081c080000c030f079103a04422510030921802001070700c2c151524001e20440c3c01900006045261046000001814014041d06c9000038000403550038000c840314240e0448444051014899041c2c40c441749451001e0b50141e00462080103028640c4040c03403003180205401c00820b0003000540e441c44006000141c0742c411402440845090f0068500c03820380d0000344920f072020a94561405c100ca15900419800c0e5004414001d4054041045509213419903500b690f5050200c10b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 989137526 1250 989136276 989136319
    0xe070609050609130203070806031603030c14031303120f0201150905060109090c02060121030c03050d0f020d0b0a050a080a2306070c02010e100e0409170a08010e06 72
    0xc052148a0004603e02107a603202d82c541490b40c2c8020b020740d201c3c034000c000585801c0b41155080d01a001b1300d0400c50011f0404442c5409496154543c490042c120f40c9580d0241008240490700501c401c120400180c000140c410004503c0741030302d6901c42c0f0307079054000c1c80304c15079a40c00815a07050804001c00a404502000c090340c010780c40008650780c0318001210440b076640d11900c1040d103003452036012507a000c508a4142e403802070718170125040c07a400305c80a0388500c01d40600014010a8540000707845080100b80414000b18081400e40c841403504089030302c06007030100300603a51103401c84581803001007130005010460700c560b6514984560b26403181e607204001068801404140b0107102c02500d42c5461080c0c0e1641203903101d1a0000c000344c056101b280c0e0070381c04294a0502d000ca03601d84901d48a9013904c5540e103007001d0a4824003444081d02012204a031115a9200700018803a0248058030131002250707200415545000307414901200c000e040c16004c0c44481c20809066030104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 989138776 1250 989137526 989137529
    0x60a060e01122f07120906020a1b0b0d140105040506031902130905010b0f0405060607170c060f0a05060d020a050d0f020306070c05010b0f150a030f020406120e070609 73
    0x440000c10b5151045080d41c400c1c4003101002e9405103150f800c04001442200c0140610610a21703000b1400c1c080004240e0b1000d107544070b80401a13001000140000e000754451140301042c42402c07000898a80c100c0c0c0403150803040c004076000e940c505440300d1031031400354190700510303090760200000c3c207064000c2500c84040d01d80303450f001d28008020300c0c00c548941d01070b50a80d1940c41401c00c10442c0d6480d00074040c05040c9040340c403e00042150f4003640c641886a9805075a0081c041842c2c41841d80d1040c2d48003c09015810203160180000c13415074a0a0003018440d400c00403807540c40b80f40011080c800c07904040c080b24051a0955410b400580303c1d00810b030203a950413a10306d1144005407511010810014100a405000381d0052040490700b11402010b00d9100394000d01c061610f02040c040c05500c483e40c80e59008124140384401c040703a440040204400524011031804010035500080e82c1c000d910030000900910340ea055007902c00d2140e5480c8505070005407181d18600040201000c02c107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 989140026 1250 989138776 989138807
    0xe1c020a0206032203031b08070914131109090c0a020d05220303050903010c050702060306100c12020a140a0c0605030a0f05040f0b0c2511090906060a060e01 69
    0xb180c404d1501c0c482404015001c0071644d42d2070069460001c0152204e402c144903042c80801181680d18007403481e0705c0c4a1011650381c0e05d10b5600d01254507200d108959031894206180c0e07521160300d98400d019021801e01c41d01e414070b0303a600c2600c0c280300d15028010301551a60000307004900200e40e02140e08507440c84c2610f072060f05e0b2820880b5800113945541460052005d46510000030150040050500c042e0110300800012001e003005507003e208000e402580800100005803c038a0710b481e4202d4030421a2504082202c540c0d5901c11aa60440c041c0c000542c2c400c0305144200984c0300740044100014a001e04a001140d03070b00c141c80c0c02424051042400b00200000d18075125a40c00701c1018810803c0500c1103052908005840241d001001d46140300304100081c1d407020510115111242c602c009000340340c041014208640b18590011180b0800762143d0364415520412070702d021301c0c02c50002e4151810b055040101c4400c080d4040c0e001c1c4140c1c85184051681c20100d0128007020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 989141276 1250 989140026 989140039
    0x80c09060117100e16171e04080301240f0f111501080d11070b0901121d0607030e0a02090619060513080c060306060c0f100e1c020a02 59
    0x140c000040c0c1e0b1441a42400541c8480384204000921100c000480d0454207290514485030700c541c0c100075440c0c050202184003151070b00038242c040d0041012501e42c05215081d10442e5070540c821003101d200400d4070241c0e0a0b01000c8014402c0c2c04110724007a040d03000c1011007039144085960080c1c0784554801200090103201246002198068130b0420550031180701511800e40d000c8110304038500d001c0c001e40d84a80714484500400318021450080040c1e1180024642c962410703101c0495548400d80c110304212482000c1070303807900107003d101c9162107900d07560742c04801d00d014201e01d4900020503a2082600303158411348030010205205424540554904480707550303010103d0010500c00c00139003010b520403a400030307295170700001a09148030038005448080d581c4842990f80c3d100300105540d8405000c0001c6030842c82c080f00100003a0407103000b41da07a22104c0031041420300440c5440c0981d0b15031902c60609186a003404100c01d00f20a41545c0c7c01d040b595004001e5603070b40700410090141c203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 989142526 1250 989141276 989141281
    0x3181e0904051e0109140c2b0819030c170106030c0201320c1201060503060d140d180e0403080c070b0916092a03020c0304090203040209070504080c09 66
    0x101c140f107890b260801020320640c00304203a0f95941e000344803c01060b5181d10302903054120300315001c2034900d030b4690001c0400c81580780034841c84100043c010441e8000e0b80f180340d24100010b641c80003500151030300c554402428a01800c0c090203981712505000100000c140b0f100e6010100d050300306064035054640060003644417407059006000742410556941c41007000e0021002e11030805501c002120025014551034041e23602d070290040116188001e6411401400b249200c0c4d8043c43c0d2080c1c006123484042c0950351103140941c5ea00c5020303000d458208081e61065143c100250f228079007111141c0140d1249041a207401e907203400382006081104040104015882e0101a144050f0f00000c00a11310f08006844981d18082400c20031107403400e1000015031070884e4410b1440596071072144000f030b1070503d505200c3e0030060f0107262062682c00d01c00b4007048a001c0000c1c1001d4030800303200594074109801081000c9100510000030850104000d00c40d90a011400c0e0080247c00d65505038180c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 989143776 1250 989142526 989142533
    0x390609100f02030d180507050907020a0f1502030403030f0507050703080a0903030617100515010e0f011103040b07020f0a0305030d0216060e012406050405060c010212010803181e0904 80
    0x500c20220441940c6050001c015070312041071000303141c414030880445003400d0f038900a09c445054100c0340c94001d0f030001030003d00404c2030200c050806e248205941c0c030f2680c0d903501c0000200d0304140c0e401da00080d600c1004415918080c0300303254008055081881c1400401d9600504602000300882c0146440d80c402c0c60401d4002d400c00400380481d185808152450030002c240e440c80d24207020a03034281804040b542e005540f08805c03075100c80c1a035817503810f4401c03001400ba2070021901c0b00d80c10400c51082c0d128a014061010b00003402e000202b0315621700b41e03401040f41307045144041c10b00c514480142000000c0e0000b08071940c03a050000050380300c4104020407166080d2800010780305a051a40d40045182d040d801440464003400100c860710752155003c5030b80407568000d0b5804207101304410311141c9040c80141c50100c110000262411521203204000610207030720840882e031000c205100703e09a01c40141c0d00041050b07419482e2088501003040712074007405080c030b000d900c404c3d0118007031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 989145026 1250 989143776 989143783
    0x3090302060609090a15020f190e06030c0d0b030c120c010207051e120a0501020304030909140c1b070f06110d1704060908071b0503010e01021c0509390609100f02 71
    0x123800d407503000c030b80320a0400036121240047c601201e000030600e101c245031600c0c08809403130082031100391031814a82c005140b040242404100316a040c85a88140b0203e543c40101c1035001c1e603585805030109813600400a403604c8866008035103d10f40c00102c50260030b09407610b0f800000000c0301d041c5100c846101e4928104000107102804c254000010001810740010544044580b0321204001e03125004009600c2100140c4004c0007442040024081c0203003034040c030310748040742c0e00301343c484c5075540711401c081d404115030045001c5085d0030390300c1c503401c50103024024a05505051617680da480a5000300c5130044000c0c80180255520088030782844480320981e02c00c00d502c01c0103225070303803401482c0c005920424801d00d8400d40c203003910f0500c2c040e018020b4485e95251711014000346000d4038030b058040d000c003d1002d0308a201e01140003860405102a244000d440298a0842c1c4000840b11084580d1550000c41c016031081140c0744030350b00d0b040d011713220300320103480c20503205107541004906 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 989146276 1250 989145026 989145037
    0xe040515130f08040608180c040c0908030d061a070b0615070503030f011509030b06040e030f032e030b0f0403200c04271101030204120303090302060609090a1502 71
    0xb07203410340c0300746000c018030310300108203503006602d840d003180e80c503d094003000d50000c0c2181e005942083d11130203503d05142d04152100003007401c003030031510746914006180d038008040f40100240c039151300300b2031846101c44480b00100e5043c10342d89404410744406462820142019005040682480310901081c8041d1075074568020300f03580d42ca080811031240050021301a000031140310b1100040e4040c0034169000480342c1c070003078100c81e80da15081004014820610301030710700d0008126110038100c1d031000840c4102900c1d5081a0009000345c00c03d4174040c03c5400b070f104031440002c000d001051681d4401944120110450303050b980c0c03070703103821074501041300c4104080000d00d800c0e00e5000d03032000c585404a08026602044100884905020200000e6082162003c0045001400b00c1d201005141c0c8261040c1005844c1130303649c212802c00403051410540c00242c3c0c41d1000310406034140305c0030b82c1012040301c8514150400007100b0b9100c03000c04100800840c0c440e40c041c0c00c140183e4051702c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 989147526 1250 989146276 989146283
    0xd0f0e03030c09060906041e170c0f0402040f0806040308010f05220b030f030423090711150a020c06070c080f130e010e04050f060403090e0c1303080a090e04051513 72
    0xd1321160786860324178042d8540f5003e02c40c56080d5013004146c820271a400780b241d210780301d0b000341403a0110340305021901c000107201c0358104c0d4080201264042e40302500c0c00c002d200c540000d20883c5010304009280c1e12040e00a682c4444240c5020081da1362040c24080c2c114007403500c6c00202d5416a01c8010040c125000c83d01d805000e034000400c89000c000c00600b040343c140b10345a00158007041c42498444407140300c0389070b010307903d000824090b5104041100300c030b40706001150701125000c60000c42c180b1086502c480036a8001529845651040c045a82c02c070060781400c01150203e0781c3c0342081781c06902c2e0403180305040482d65400c1084c203120702100a00e45c0e405241c0c1e4650319914105540c00045405403290321628507051806040016401d02c1740303405a440248180c14050300882140024007804680d513424405011284019071034a802180709220b2581d0f120305030385014004041590100001062800030000401c001040c00080740440c820340382d5840c2c0e180b40e072903101c0300509440039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 989148776 1250 989147526 989147539
    0x303020921071703030f04080915030f040606120512030618010b0904060501020d0804240f1509090f0609031e050d1508030d0b0f030a06020d0f0e03030c090609 70
    0x9001c002000c52044159280d00402d4940c00c03101c03541199880c842614100d070310010b00c0000801141c0b010016240c1104010141000c015004440d5080391f0002d6030810300304000d90b82070100300301e0355209000c0101505200508e06403c561a104c1d280c404014960400c001e0000001c0c1c1655a02503400080024a074403400e01542c480041144a4003d004800d000d50710b444000309481d800000e186041404c15981c83d26581d45550703e60f002c02004070408000300128007900c8440f005179004c1c8541c030742001200000d00c0c074442c4041c13228580c000d50184c81c0c65403074a6141c8001c9001b43e410024816040349000c1110a5546011a800e000c16a0707000301c00030003081103050070b5520500030702c9001f00d007002c240302c442c0402c9101039052200380309100290380100040303107580c0da89402160f10448002c1c28400f0403596503000c0b0b41807000001c1c00700e444a0380016440d00403542c1c1d104190342c445500c20200700b000051030150365203102c050900e124640010401e03400310b030f0310319003190308020029012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 989150026 1250 989148776 989148829
    0x9060e0a1d0a061e0b210106090e060603101803052101030f060e062e03050f01020706060b03010807171009061e15140d0b0907230303040303030209 65
    0x100c00180959121090512960a4004c00780c4101e4080c0d002c4540e80140f40512250f14210401d00c031118400d00000385548401c00019502e205100781c080c1800d203280074015919200e0101800c00c030b4075030181680e282c40c09141c4011a1143c5108070078241c0e041c10011794500c21108241500d984064000103d004500004010841e242d02204005e921640c0c00740245c01c0350a54640e2521800c0303541130201200790071007190810301d0580401c90504084c0748011203513200d4590038104440420689044d0b90009a2502004600c0c03107904001c11604400d42d08550401d0601512407409204005e1108510341901c29540001d0051075911031003030408014140e01460007201074442c000d40310580020b41141c22103210181d0061040310303110141000b2106007800d1840240101c24401590440720302c001001c0020700d86031000d4060502c880007060003a2a00c0802c20510b40014680280310080281b80300300d50714004180c0d03096990500b80580c5410081001c031382108a18224203500e041c10001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 989151276 1250 989150026 989150033
    0xc0b2d070207052e030216061103090706030e0c210613030e10121a12210a050a05030c0d0c0f030f06030f02090a090b0106020c0a09060e0a1d0a 63
    0x1551003c4901c02e50322801610f4280080104070a101e0040400b0907038407034961081984070758018003500003180380c2070200d100340c0d86902d0300f01d0b600e0068010394100000180b0030740b400104145401000c1501c1c050094044e42a440c0392180441e13003200e4010794048031450000518420602800070755041140d030a071800d407003001070740c82e900f14090300030680101132078510b400c11000f00168402251074800416a22804042c0100701d102000540301901ca010108143d5910900d031810341c0080c0000c24181413000300c01e00542c46000091004103004029921b00d09070490b05582c008a0700d414950b840343d0f902901c2e000315104040c100094030b0300c2c0c004802c0c50300d9049103caa5141595a40401400d440b50840d0b4044540e00d01000d060008040014001803800482003036004001500c0031800040c1943c803202c0b80344003138100401503002584800090700f8132081010080542d070b0024400145003611800d80c2d03c1014120104054803065001c2d150701d02158200034a103009021118481700b5801c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 989152526 1250 989151276 989151283
    0x30705150a08010f150e04060b160b0c160605070e0a090509070501050a020a02060309070509190b010e1305060d02030709150906062c0307060518010c0b2d0702 70
    0x4a107200411007010010030190303039a031413000a49180c00100411404000390036982030001d41641d6600a03110030000c5000c4c4907040181c4503800500e03c1104054829152244030845d0060000040d20014803031881c811002c031264141d51508840c00140c65103a080f42181c01554840080b6048644000d0000720704d80507a000c14030402250065811858403a40110703107a1040d0022000164001105100036141034402940c01c0300e90f0004558685544001049240208550448a180b125031000007510180e01078101c4900c424078040c90501c0b8500c001502181d0001807001841d556000013501d0354075103c0080c800a90000d0441d01e007960707101e81c00ca010701848001209820700c2c40c0c100042102080c05140b0981d540d607112000c5109090144000440c0075854107084a0413032055803034140c805000030406000305a44081e0389588122910b6940311110310054100b2003403440c0c2502060f016201c0030740050303441114201065640f00b01c01e0380002ca400145140346420824081c4064000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 989153776 1250 989152526 989152537
    0x120a0e0d11010c081b2b090201110601031e08070b092404120819020d0506090606032401050f040909030207060503010e010909031202070c052d040b03070515 69
    0x100020b00c00b84451002c2104c1e0400280d0300b0a084a115040a120820b806405030250450b82c0f0341c40490808202d61604040f101c0e0070314403010075a202d4080095503800652800e04490050042c005549181c3d20340c80d06001200010240601d10001c000811001c1c10481c0c4106070040618449801c000892985840c0c0044803d8442c2c103086815200d65507940090600c200d0b0003024648d80314128140c2664032000c02409d425884440440c0d006d8040fa442c40504501703e602d1070000303114503000b800e100e80480e019000e40e2013a68140b0400041c89c1c0320584031600c000d9040c50307804480b1403880040e6030501803c5100f440800021a0100e112040ba80c000e6003007038001d500b21101d55170358400a031541d100a0007a03010850741c000050108110176000000e0171403080c9030010310314100444c7d8100720380051208403175820903108104070070300d800ca018080c0403140f01408403002e201d56020040f4003030300d03030006800f40d0b07210110700c810b41e40c00744030100042c000584106800b01c0c5140d40d05001d0343c0714 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 989155026 1250 989153776 989153807
    0xb0f0f0d051012030509100903141b040b0d020f06041805040b07030c091a161a01050f0102100b040b0613091b09030b04050a050d021f0203060303120a0e0d 68
    0x102d00040d10403032000803c4401c0d1309034440c03e1a0880d80414066040c10b00b507000014005c2c003040010000d41c00c000c0b4200d0020301f4801900060303400704c0305098001204440c10b48581e0501d030710400c1a55807002e415a02d00c2d4102c90081c0e1800c03804003c60b099001d55400b0010581d10b07a0303a104c5e80e181c49504441d20442c401c0d4001c42c00c0e039031980000d500b00d0750840c000c02e00003002243d0511000802c1450302102024410041d4108000e40b1100080306503c4001181d942d150540d403c46004c0558410902401c07084640014071900240000c0d030310350122000641054941258481c943c54981c020055040c003c2c000a81d941c2d8640c54a0150300001d11460340c2ea80c0c5004010614000d0818584140704070b91781c0c85030901c0b071540d224190405405402541d040c00303041c08800005104100e00e8200f05603039005022049801800c05c181541c06902d0580c1e0207004200f009000d541c0802201c2080007800c1c025880341e141d040701c85000301800003038078000e071107280390baa034036990040c0010440354174 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 989156276 1250 989155026 989155051
    0x92a1c050906040b0f0405071a0a031d060a15081606120207020604060507020f100818010614060a020f07030c0e0115020c010813050a080408150c040b0f0f0d05 70
    0x842a2000b9a1244110781c040c2030403885101080c9090151203049030072074050320440d841107840e0494000404072151a00f01280c400007807000c0d015815005110803405502c0c0804040311030720390f0050725507000400d80070070b103a50b60184c901c8465018182d03101401c50ba07800c44800d085240828100140c01c0d00070b50000c6500c5005048076047d0741d0003140d4405601500e084d0a0502c1c000c0241c4070f035004094100da002203005000301c904d45071a4085890079409540300c14103424030455481c16500307102240070a990400c881841070f60f040305103001c421a0142c441d00d0f603504001c00d089040c40302503040501c890080c54000001c0c004503088400980e0311420b03110305143d03607903249200101e41078118070300980c01609141c04c080d805403030143d030301401c502a9a00c42c08403903030b556810f102c2d02d04021108980f01140601c01c0440c20021401d59480c00300700f185060500504003c4507004500c00e00f01d02510003e15004500850815102213011860f1129116000502c810f00038000445a1100d100d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 989157526 1250 989156276 989156281
    0x9030c0f06040807030507020a031e140d020a0b1e0403020f010b180a051b12090118020d080a031d0a0212123f041e02092a1c05 56
    0x100426950b0050b0791100340c8600d030144a58040e142030300400c83c240d90245c90514000701207000001c511840e81c542c09081241c2505030310f0a900510358096034039019074011014a8091a00000e60710725854101c1500702c03040e030b541940c40540440120925110880403002e1000301a000a882c13281203d100f8004e21101500c070007407020310040c500e5808041d03407200000c0303041104960700c042e030828469000c01072030200441d00120385a2000e402c1882c0c428400c4200310320300341f081c4511041c0d40e4141218000031800707600010080c030000b01d0090281d0400250101c0101c0c02035022032403541001000420854112881944a01714914240c0c014003004c4242d85072500d010511042e0107162010305420041341c00751100e007850305264100400e03607409030448422100c0410354102c04100c100c00000750319052900c01d6201e0348019000240d0320000b540c039001641c1e80b00010784d018200103820540026125045584101507512082141c00005031000d1000c182e81d500d074404c3e414400301480b194 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 989158776 1250 989157526 989157553
    0x60b030f0a0b06190e06040605190305250b031302090403030b100206010e07030b03010914010209120f0d080c22052407080703050c010c1d10080402040c0c0b09030c 72
    0x10045034104122065081c004d5030710001c0c17120b41003003015100198294443c030204070401c0087c001c5042d40c1d0999442002040010445c0d803000c0c8001000e04120308120002442200000c0e01800184181c084005606425000c0303110440540040c01c0c0f0f007031400c0c103060140c024046200058000d1a151076041141d03030000a11074100c680c10905814190b0b03c0000c01c0700280409c4440036810354982485402182d20a244507400c18401030005035a280b2403c100580c1d140c4443c205816074000320051040114041802d0040c40070300d0038446103d0b0b80c0d11407007000034482c40c1e07031444850004001100ba4851030701341070000d40c3c000351082d1101e0071600d03049246aa0380072074001c2402800b0858140060020f00103040124440d040082c02c02191411640c2540c83e80e14041e80000c0031003062041981d840d500444a1210a9410281c0c00c0d1103044003c01101004001034091900d0b1800000400c0c40ba41080c1e441c0340d0088940d40d82418500401034880d400b507018031b4003612800d000d04070503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 989160026 1250 989158776 989158789
    0x60924270307030201030b0307080604122307120905060313030201051005090c070503120702010504020418050c0405180d080412030b0120100207050c030105011e050d060b030f0a0b06 80
    0x8850000c00502d0140d14650044003c0c0c030100c004560907024010000650020400415020b40c0c4512003403840c50340742c0d03000140940d0b9140c0303d9585e4424201c8000818000c0078003115101d6810510f40c903031081003000c080d1620329496115a42000e00042040240030818550102a0f48254028006900c91003c0302c01c18802601440742c1c01030301c0b4004601780c20194401400741a02c600182d0381407840c5030182c4400058200c6619025035103603c10441146818860b0325100041924007102401c0c05441d03e0366948c0d07000403880c2c0660f9940000c510115060015044001002401c0f992010b2150320300610400c01581c00b00c3e005d60304480300f510068000d0040c20741d5460b040c4d65410388003403140710000c00205110103c40e1907001d007441c400202d40c0180010312465010384000c2850040600c02d141c21114142c4c02031445058520f1840d42e21003820542008030750040b2040111607130b480c20404010700d0b1442481d50301d48224100713020503a401041c180e40840c041e1108045035910b00c018001c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 989161276 1250 989160026 989160097
    0x90c040e0c01120b090421091d0601020a140d03150b030613060530060906060d03021c09051518040e34090209030c060924 54
    0x1e03001801100c2455100d40818210f410100501145241203000070444100303003542c007610102c00700c009241401d0b5004206600462803464100100d900d82040309608000c013000c18110500d001c800319010740e01c00c121001c9403d40002445040887c5054030329070342e904210742c00d00032a04203034130b203500c2c200000c2600049030004003405203507607682010030089140303801407003500e40e5035840b001c00d0548842d00652456120081c001c010000310b0301c3c00f40502c40000002c5501035004c1400c00c0103032000800d02a411141c107940004940c6800d15043c0c1c10940c0d0325060b41481d020080309584841d501a02c140129101955038024040700c00c16282c59603c12170200844100790003072048494140342c0c1c81482000c00382000c0e1400c8010ac0040021101d82016015901d0015020306001c0c4000c0144050018040418214a031104880229840f1184590010303c18a0041002001612401c0a1100040a51140d4510503030750028142c419040502154800c60321281040110702c4085c21240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 989162526 1250 989161276 989161301
    0xc03020921150c0705030f0405040506060315220e0102070215040e011e0e09010f0b190306050c04050a120b10051806150706020403110102061006050f071406090c04 72
    0x580102c00c89001010701c0c070140c0001c2c030702d050422980700416824406030881011044949646603d810108400d6883c058040c6210310000c00501c00d80c0c030700300c0500342121003090b151480740e0250031841042241002c401c0c240d003103082c01484441148194010000c60388203c0d01c0080c06001c8000b030414070b02a03400f4010b03170400c00703000600103c90003034103144d40412030045840c0b03806d469180f02d100040d0140c581c0e91042e9111095004140f00a001c3c240c0d8010040e1a200b068032071049000b44400d8031803102428840c2d982010958440300d003001c5401915025010340d01c6030303070768135589821119182000d0340d140f00c0310000318004c41181c4039071600b100c00c01000c50742d20010801d1005500d00003d061141d108010b0f40c00d90103842481805841c0885c0560700043e110be1841c14582c80f40b05001164a0443d003050040101c083c0001060406448079843c005440b080d002441000601c03840030007a04204034050486070607030002641910a98000741501c40307003030601c1d0501056801401501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 989163776 1250 989162526 989162533
    0x90528110c101d370c08010c0806120a1b0806090706111207030f09031209180c05030c03090c18040618020f060f0d050a27020d020d020f040c03020921 66
    0x3421070886050216030f9046404440780c03903132005640c51060305003c56010003402d9448458584001380c10500460f40003d003603500d43e805c2550500780503280c40540c48002e20a600540080c04440c8000060320701a20580b02211842d0410b1181aa5038140c0c0c1e214a0000450b40303108401a043c020514050700020240c0c3d1b142031000350b81d02940c3e014070b40b5503248108541c81760000301040b0104241d040364012a256400094105440b0082c0174141d1603c5a590604215103168042ea004007142d50080040f40440d4684e1904020241080040440c0592280c0c3c00600a24680e404024450140748600300030484c561400070300d0190307901c0020740a0b5002c0100504528075041c0000100500c00c0c500905d10329101000c0207007801ca40c0305403403031381050b03982d0380900340011446160324820440843c2e08100c0a0000d500040032458081e50007800b440483c0306040854903014458540813000820a000c15500e101c002002508004250351060b04801e60f2400c0d0511583d01e1481061642c1019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 989165026 1250 989163776 989163823
    0x8040e0609100f0b07031806050309010b01080603061503070807090f0c080603060103140f010e0c0103110f030109090312090b1006170c0a020a0203070609090528110c101d 75
    0x12078413990000794080c2c043c010320344182940168010b4201d00605066255143c03241000420182140c0544c1e0889043c00441c2c800c2c083c0607500020b495038000c0d8032074501d0141c095038030702090400e0309076030201038244645d0b1700100306203019401003030380303c001c0d641c080000420310081100c045000380c507683d0301500f0250051000c12030f001102c465406c6440c0c101c61144142164443c2115004c030b20b440200d4010701c4c5030103155a414001c130401804400f030502e0809040200ca04030620062007003010359603582800c40d04150158042d5076800c0c3d404401002100554104840c45ca0340868070044600d030140c0c40070400c0c5000310721007a0101701c82d80c1604816628000c104010b80e0000e50544190301c1450b43c1c00c00182c1d002c11100019004075515a440146001450003d80303501030081884a2a64080c100007402214501054401891004500d0b10451040459a80304001b1002e5044c000d60b2140b600c02106504052202c0c5131202d0305d614580317000b64660f074413202040440000540000c18 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 989166276 1250 989165026 989165039
    0x60a20150105040209241c0b210325060c1e03091113050406050603010615121b0504060201050604060614030601090504051602061305190503090a091b021c030c03020708040e0609100f 80
    0x2c3c441c89d03a501103012289003514188050000760901c0c0301807000d50802d0701d0a80100b040d14003a060880010f81410140303000107000700341c80c00d0344181d04001015943c402c11400e1003060418240e4004002c1c113581448016200e82501a103800c4a003529118101008550f2034241441414111540000c010062641062040303c20400840030200031580765100340d403032241c512104414141c0325032640355445180c910040c1c03d44100a00c06403042d8640802042202d030011401c2808001004500c2d030b903955041c0058030300401982040b50010b00e09401c00100f80900101d01c0c0343c103900d035002c03a030309552840600880c0e580d0320780005100d03400003190004425254a80c0c50203892148043d2030400c3c800c10b0214400010350740c0b0480300a6200c064081001c2c207c606208101e000e10f10180040014003039106a02c0c00f0501865001c255a4480182c100c0c1d1080e4107540030154031805890391542d9400300d606106200703844192003108200d01050f1910040c12a13802141c460300c8903454050314100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 989167526 1250 989166276 989166319
    0xb03060610030b03010f0203010909021804020307052806030f06092901050f030a020304060c02160e0c0d06031110050316120b060a20150105040209241c0b 68
    0x30f0045400d5929a02c2441001d500c07800a10b000e4280441e00058840681c0100030024900360b220b24400030081090002603240400c6010031f4500a90303110041d6202015641060030002d90b00b0307912001083d10110b079a0398580c0201c208180700074400d00c982c2e91500d620b2000c03120000300c042d000780c1a071027008200307900402c422002008141401c500300003480a9008541c1d00840d52054550340c0041000200b000b00e206000710030700c0034801012000702000306c081019041e4040c80d0b060051307250008100e0b8914904994054000c0c803410300100b07940b49899203081030410155071041003150550b41e840380c0f1800942303100e072100b4660500340d111410001d5803201800c03501d07034004a40303030404081c2d5519540c1c01403207150544d82e1030f40302d032400d52415440c15000b400d024a03025040419204103441040449505441040b036005030303507d0b00080040c203004010b03000003100c03079200710380c1c828a9079081b0088d1000382d003102c24046482d05507065110442da584503c0f654011581e40302e602c00007241d80e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 989168776 1250 989167526 989167541
    0x9031106072c0a0b04091e0501050906040f0b100c1104090c03031b080304111e060403022b14060603031c0c1107150e0904031b0503130e07030b0306061003 68
    0x1034043c503a055211500d200e95035100d900005c081039111403180038420484038100102c05862041000107504080001d1a50203003c0c0c021807045880f00c284101740c071007540c01a600184000d0036a000b061034004040c2c14050340110944540d203c407951051142130501459120541c403041c14000a404c5503016201c500c8540c03542c8074003e018000c0c960005245c10f0003103014900400f51650418034040c1000544d00d176091074aa401019040d2543d0107441c1c1009540a807581210038451109004008a460303190300e025100d400d0301a02e9040d82400410150412150b4925068410b01d03561481415a01e1160024090071441c3d0070074040c1c103240460f440070360480300ca0b2a0902c0310710351440c0414039200c0e450b0011250380010b042c160810a800c81041c01aa12095568440e140340c1500c0c041c22201a00056042139080e050481c001c1000074000c0340c0032641c00d1070019541585a034000304640300c08031a8840481c7c941103480350b46140004503603100b028010400540d007551388804401a207802c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 989170026 1250 989168776 989168779
    0x201230a0c0503160c181a0f040f050703061508010302011205062d0301060f0e01030305070f06020a090509010b190518090405210307080103061a0409031106072c 71
    0x83c804e613070b801c0c001c82082e91007090181c4444d141c0c0134100684c0131402084203540c03000703551070300d400b41e03d010591700202114004101c03200c403140302154021074084c02e00000c14480c01e519144c04c00c003540b60980c0c0402c4c03e89072045440e05205a8405041d1510242804081e0229108a40000518071103400032607003c0405090800f85502c2e240400402545100308070320843c00648080c0d8107030800748140d10091000c81c40704000c60b0701c2c1002c850001801802b0203420403030300140250070b003c224840505141c0c0c1c8030300c0440d99090441c10090440c2401d0069a20412659000046030a4400c042d0f50740080c031030104601c0c0340b060742015150b0358000c45500c1580315102c503250505903a10365040b0b10850080303000d41400c20751040440201d081c41d00607401c0e4800c0c14028003604a0b070110030310b419a5408900002c40040c00d84002c8460419a43d039a13520506080410382050703440b403da103564034503000840c0e07000d443d010420b0702e00320210442400d01001e074140240040400c0c80265040a80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 989171276 1250 989170026 989170033
    0x624140d05131a040506150f0405100b0d02180f030d030c020c04060e090c04090b0f0411040c0c0203060601090510050d0204080303090a050c012a060b09130201230a0c05 74
    0x11141d9400035840b030f002007410303400003280c4108003c1c48014448a135100741c0d000284d180040048002544406050440601503035803000000e44184a80714508040d04000316460b0f1a818164581d001a5014030510f040e61001d0f42165101420f10318451080d5071030041c081e055420702e01c0403c9009040000080e4214850ba004041040d142c0344500c4001e03140201c24102d99103801c580c924a440240745c14180610f01d008240c1d800300329201c0103150130403400600094261154140f00c441ca44143d810386078082c0c0380c4168030f0b480a81200c0c0d55900281300341c06503800c0da601e00b030044d140001399106140d000400000d90b64030b86441035000380080e80c040d007001810192120740640c07840e00101d40020081d070000704805c00348030003040480e404110901e07245000801d564903001d5003210134950b4006102c102c01c0b04004101c03098000340307005500600681c0f4180341015030340c2d00d04d4651070010b0740030032007203240071207040d291204d0b00c08412440355013285000082c4130119840003140300292044e00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 989172526 1250 989171276 989171311
    0x904201b060612060f100305070605030906070c0b06040e010e2401290307020a050d030f06080712080703020a0f030e0a14010206060f04020d0624140d05 67
    0x4451801506108180e426404144049402000c0c50400054161031041c0c46403440c030200a40d00103071065004001e40704901031521800000850220550002086409010307408121180e10601440c81000320744110342d4a03440300942910104100540608002180b40004007141442e0b04040261151103000203110401500d0840c00c0202c18100c2542c020742c0841864103a481716822303140900840c00740360000c80c20300b400c103481d00070b250036440d80384400102c005a011030003400100c401035000802e0301c202150814009004001c524501d6075440d140400100340c3c00705c009680000c0d1401c81210312210800c0303480d040c0712600b01ca501113045208180a0b0300000301000d9555491031301c07d0700c40c2c0c1c0c0c45600480030400e4000c85c9030400c0690b01c110b01d400030001da0740002c0807500160142e45012001050a0108010784a40140400c0d041d042040c0080c142078005500b0442c280807204041d0342da00d00c00e00855000c804190001002d86050020200d8011554417483d000710105800990a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 989173776 1250 989172526 989172581
    0x50708040906030302061b070204090c0e042a0b1804020c03070605160c051507021c020a020f0301090201141606110c071509120c0e24090c0904 63
    0x254015002000000e89802c401c00c20950108011a040051128400c110900500c281d01007401101c2c0301910131504c3c0d407040e0040c004800b00ca43d02800c1c0c0360444c05031514007030400f04180c643c282e2580c1040103201d816a4044c20200300340d00b0039114601056840c0103c1c03550b00c0c0641007882c0c2078960340568200904210250300300014640103100d40b1000c102494035406c6110801c401c0040c83d014030511070000c1c000180c01064020000500e90300319545038a640742e00b28a400d1400300c149a04060300f00d0110505a00050103405043c42150305012000c0840b0600d400e94280c4a0024003140640307800701c11068038800581410a8802c001d10040c0c042a21540183e45ca110181e80c0c1449001908050420b401c5c440f00018048d00f40c455008208039034001400050284608045220170031900300c1040041d8003194001c0c400a1265040ea00741542244455040804a9806508480c14184d001e0a00d010001d200315441800c8906240f64641400b001e031103951300e0740030221403403d01c44a41e0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 989175026 1250 989173776 989173793
    0x5030718060501030b060f2802160801091e03021002070606030b13080f09040204050301050c0a0801143006071215180c0c0b07050a09140d0809010507 66
    0x100500c0354064500d101402600d01211125040281054103194514420342c0390b140440c0e8002020140c02c9035180682d00b5081d00b04820300c807c10301c200c1104501485100e41c0018400c800c02c00000e40c000e0a280c0e24440907088031101c04d4010694400d00c8003440c06034281902c025042e80c000d00650350748102401452040303a11210007200c0a565494007401030114021007641e1001e00d803076081c0c844696649540c1400c0c0200d041d0345034030500c0064000d2140d122038054800900d400b8000784602e04051380c00c0b50350b0341c005420900003d6020740c0000340180e02045e80c45402034020300800f400d1703c0e803940c03060300410030355281c0081c1100e280e0101038000010020700e40324101958030a902480385905242c00e4403070440035440514010001440119190900c2d200e9001100100044040503903006481d00c2040d9840035080001c43c50801c4000c54125000f000103448030f0b90341c95465525660800b003842084200c0b203070402c1c0c1d003009103030004031300b8001000b40030014140b0314148440356849440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 989176276 1250 989175026 989175029
    0x1021608030315030d0c26040b0901022b050a0903050d03051801090c260303040b0a060504050c0d110d0f0f05070305130f110603040302010203070f050307140f04050307 74
    0x21076100004100800a0b092115000600120090304503010940740040c541c24592038060106c052544558401a00c2e48200380c003042903000e022a01e0f0340e92102422041d41005900c0703400350003590951002e1540703110301d41107607012000c40303c04981031000040f1401c0d00a00300c0d0000340003401704040046042001b0108000800355000318041c5840d4840c490500b5600260800c1a07040552400000d100000c0810940744641e0440b4085561400440700140d00000804102e001c0001800305009201a88503c1131461036800d00160703542e0002d01c0110b800481e50040b0710581403080b2040030300c15402ca070174103040700d65101d42490964290481100c80b440c40000709166030300c40d182110b50341405003070f503c04585d0030704019a1034104941c0034080303010070001742502283d07401ca0302003100c201020000001c001d00455224542841d010307000303500654440740070400101d04070f09000c4c41481100d03c18880ca540d650402c07641081c1040c0707107400210041c00340200034400801c0c580c50400c000310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 989177526 1250 989176276 989176289
    0x60708060301021b0c03210417030909101a030c0901110c0415090f1107140115030606080118030f0c06240617070903080711040e07082505040b010216 66
    0x8240745171001c140c5400381e0b40c00d180c4030780c08403003070054503100e414425141224035140c0301d214000c0c1c1600c1a40d065105a032a0304cc1d000681c20f00384406005945081410b64480f68042151449090808000c0307000031100030642d000204400025944560703503200101100004440361500c3d900006025a60403807010500d50550208c01c01c040c15a5004407205004040b10170002202980c82e40d0701c85201d4400090040c13034002c0540705510b00c0941c46400d1394217400603d176143c16207a10782140980511b1144209a41c01d003e40e416103008140481c2207140e9140c0c907031021450b00e0350760544030002c201405070380f1940d541701c0c00703076154440006a206d10000942407406076810944003404a4503a140080d801c000107504109040d82c01900e4101640c3c1c0111016445070445c0ca0645005001d0030021341d040b42c00c1c00031503082c0707010006e5030006407580042594016000103502d95814981030440c14101c1b201c0b07910030007003030820381d00200c0c01c148184141d07002c0509075080c3d03040c00b28003648400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 989178776 1250 989177526 989177533
    0x1030e0d020303241e01050d06080105040201090603020910080a02090901080a030f110a170c1c11030a090b1305030d0f1404180b130c052505060708060301021b 70
    0x215413019000740d0600c41040b44618400100c03c100701064149900280c070f0903590071120b4551481d81c1c001e006072420060700840034048280c55541c00b9000c1c0605aa080703010802c1c0d10382c00714446000f03009684440d0000b4102c1d00e030280c485076084820400107025022000c3d4200060304407a140e0340c0300e250103007071703442c0040c8031600311842d000b00108a158210401c0111075a1001c03208000855005007090300103254402e095040c81c00141d0a00c540441603101d4171590003031440c105540558811403013441d44403a01e5a20019040549a104a00010000441035501802070900e000d014008854124560608594079240468035040f1041811b03004a088030031601b1501d607101308100500c0ca144100b543c102464004640c00c200744445210b10601c0d26a0b084000940790200c00c000205041002484120310000000e8050340c80f615841160b00d0750b100c1c030200364501c03801c4098803840d03002000700b880d6910040c0881c2d004070050301807a8595000c000844034000054030107800042c042019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 989180026 1250 989178776 989178781
    0x1806040b0a0513050402040807031403121504050f011a0c07030206040303231903020a020f03030a0608060a111617030a06052107090e03090d0b090f070509060d0201030e0d020303 78
    0xf42a408207540072500c04c0340100014000d80788003041c0441107035400303080034030b01010b409030003400c0d80128110a80c0144683d000c01c20103e8001042034501c030707010380c0c0800c555140c81c1550324025200b4041c1090400c10030303144d003410660b940001d04582c0380480555103003d859a0014006500c140c2c425400284204440320386403038070240d40c811074018424020720300040d00d005203840d1100c80a4a805041c2d0104884150368024040e04501034000c0b0240c0b541d82c9002c40215000f0706481c0640443d0b0b02c5060000f400d0f400d481d100e1280030110000e440c80c1848145a8100f548403010002140c034201c21041311209400080c01540c0607149206010540302e013400107021013003440822040040015020300f0300060004108501920071200c004154280d507008480d2a5100340c07104240c00c0051402d00030b051144e850203840c010107000d02130f168122003440c88244d0315120f600806600050982c0401c140d440d0842c5694062441810003287c8035000c000002c3c104a004d030340120258000004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 989181276 1250 989180026 989180047
    0x3050328091d0c0c0604031d03060906041b0e070c12021603140f0a0804152c040e030a08270705040209060c160513020a051806040b0a05 60
    0x11480d1115400c1c903010500c186000894000e00c4010702484411020792008194480d044404440189240e00101d030b13024246860000d04000c0d401b180605880212030004e8168600407424500410022008001039140d82c2c8903020980f01c0380155800003282120300140d0040800c816600c00c00341601c1e181241c00460900030920844d217504001150800d107800c1242101c0594060241c0c0d40101d070b1403240c3e021020105160050702e0501d2040c0f84a850f078008100030260b001002611205000c480007800c075248241c581c020340f02161409040b11060004d1001000c090350010b061000b030003c6000000d4080c85810f507880490410005001001000600d10388001015401009079050009011181e0025526400c0c14010b07584510780010360552107980e000c0c140c6a440860009488051146074201340c0d0005a0b8403038903000e80c070940c540340c0703002440d84241e9511200c0c2e600e80342d00d080c0c40d000442003295040300042ea4440c00520000c206902840c000e0a601075190b21207aa4400c020392 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 989182526 1250 989181276 989181337
    0x711070e06030709111605070513151403030319110a0f0e030f1e01020909010e010f05010c02090621030c010f0b0a120305070f240506040c1b0507030503 67
    0x4001d9950f250031702001c0262468410111061070102c500700c2d00500b115460040c1c10a02140d011f00d80c050120f601020b4041d82550010310400e503007200700215540d94140390350550f0745802c0e4107035040d0000d00c00074604280000e2071605e42810340a001030761801c0c0342751030390790341e0408607030340c0300044056a580e01c4103074000c1520f4884600c21030042044144e11548141e40b0203224003c03803002408011540b40c116425015208be00e1001044d00c511913840301156407480509209144c0101641a00082e442d4002c8142100d42d5070040c2c0f88a4480e510801031102031240811505800d0700b03240a50001251b091015040103401c0d0f20010a00110407580d0100355401c1e8054544982c0014004100340480350b20109181c1e5850708107680c840d00c2604204604c00d84203c0c01404d8540313403104404003008104040358000e81449020440c03038442c2001e0004071071407080c0101c08145070b0400b80611700c00080c00f4210091140040710303440ca440c0d175103039803c5800c00c420b803484a5201d110040d20780e10580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 989183776 1250 989182526 989182529
    0x100c0f240e07150f020304090609021309050c03010302120f01090b06011709030304170409090c0f091406010302030612010e0a0b010518070810150c02091e040b0711070e060307 77
    0x740c00034008070707040846450a08905101e001d040c080c801c041c140200c1d0003072090710000d1542080400c20144c0d50310291020750f005509444544011103000300c0e00d2085c900c6030901804c0054101e131b0640e8250f80c20b111482640a4002c0b50030b10924554081c0b80380c090041d00c0b00c503031082d10890f4090901c00005440c9001443d00d04011031090070810103003807800402e8039402500a040400c0400391035030720540c40d12440e044040882d00f800f90407002c1c4400c001c08002160401202900c81e1039036580960102c0b401c4500390000410a80081a6258802d402540d086a801402e0501302c0c20b8080301207007120450b004c25003032a004210070070180002c40384801e005081c00d0342c42d0744007103a494403d41c0d220000102110705000620b1302044150341a0141c82003d46078a4143e0844042000c0000d400141c0317400007248900345807000221106088059022701584021340c01c00f00d03032100d90700c1c8100d07604010f105408000c0e030400c0c0c04c0c1e40200704105c29002841c81c0400001a41800320500d8201403d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 989185026 1250 989183776 989183801
    0x606040207050322080d02010e0d110a0311030f0403060f06060216120c030b0403120f020a023307080708060102010612110103060810020a1805100c0f24 67
    0x50118501049010040751030000c1c03020402c10340c44c1c10541403201641e450303411403011441201d01c1c40503d83d405611410800d2660401c90301c0040c015a0200c0b034204c6426101455600840703403c100013401004120700c10411142038a0801c401043d034081a034009900607100701e0b0303c58185c450f104065200d00b601400d81c91000c1d1501c640d05070003a183c000744505c82c6520303810120150070f05000706d00005c0006158840c1d42c400c824101400c0040152890107080c3c40814602480384a0380e42d5180b080700c0070080242c020b461022080c040c0c1000c87c4512015841c03c4503040d00c1c1620b68071030703680105445000562905480c0b802d20003401085141c0003010700d819a0f02d440d20034031003d002c0102012003d0740c0f02080264031190240120b02400c065400030b002e51180c9901c0d07000180c0d068001d041071001a0b610440070300c1c4d060307a0207200910f180c4107403900000755609041482d482240704070301040c05000041c0010010307079140707106540400e0390b00c0c00c03c600e8050483c0c07262450b4002d03a513003040c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 989186276 1250 989185026 989185031
    0x80d0914100915150302120a02040230010f1e1503020c060a0b0d0f11040623010201060b09010c08070b0705070b0f040b070809070f0b03060907020d090302010e0d02090711060604 78
    0x41d054840c0c1c02da0710600003c0d11426181c030081150348800c0141d00075440d030250040d502c3392007040901120141880290181024281000701c41c030494092280c12682203044120307403a46460314584942560710441041503140e2031021410b80031030050b69091310303015030b00141e5598079066800d00f8150064101120107061041c2551141d68440c4504035442d04000700300c500c2e0711a4544131900b81441800c2d80c1d00705007080d40000d18000c520039240c009800200003811102801001282240c80b43d000e50300c030f1010203100c009081c4d445424815507140c407031a000c03850600c481e22000d441c44c2c401c542c2c80000400019401c03040000c08240b058001000c403c5000c105e082564440c040341100824030400c001d0f03d800040c1d10000d040080200601d10303041c2e50300340c141d20388050448a0740100d40483c09100d90b100890602c8c0d1000070104890012592420009401c60b401120502c2c00c66a00c643e00520058401e00540e58010034107000390b40075242c6808110100180c0703030500d840180700f14403961 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 989187526 1250 989186276 989186291
    0x13081f051303090302010e010516050f0c19030b0c21060109060c030c02010804111e0906030304030c0b0f0403060e06190218040b040603080c0604030813080d0914100915 74
    0x94008100e4811380340c1c2401e0019882e0200d030300482c1c0e64080c19154032480705a046012050000200d0507805114012050b9031f44404690280f1000003203c0d80310f80c2c40c0c43c0c0b07801c40400c041050181c415402010005445183c41d19a14001d02a80a400c410b001c101c0007210500c040f540c0c001000300010701041c00d01009d4402a42c45c05003400c030b0590800390510500d440040c04014020480305218080204054004800d11010a0074100c8540c0f42e503008000003c0400d405240c008151000c0f41c0e0700c203ea240751b042c1401407a20b0a41c1007241e80c05010001880b02000081e510b00840b0000c40304100100103d1600d49105e4041c0c1c410400d2050000c0d104105000240046102400040e102034501040805110005c034000300440da10190020030003180c1e40c6000e40c0c0210310203004038007a5030780205e19115200e07054038402410500070540c04040011900030700c2e041c2c014a00c602c5c0183d8803420741c030540c10052400c1030440840c1d021115521151401003240030740801c1050590303c9410405030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 989188776 1250 989187526 989187533
    0x9150519200d0f0605060a052d04120f06020a170f0108060610140a202d010e07030c1a090907051309020a03020301140603190213081f0513 61
    0x902c2042c1040c407100e5280e90400c00c8500b91038201d44000c1c400604025501c05010000802e140c00c10141c0320356103240c865007440c28034003030b002c01c03900100440405460305250944000c49914101011614160095051008540d00d0300c043c24406015032160901860b00801c0c10403d40001090546c46504038001440810000180280e0007442070714800300c52480300100740c4082c1c407410040141e2003c000341141220f94850310500f0518001602c041580c00341d25100b503141c02062850583c0300e02ca030a04110441d086040711003410f03828400000d06000300311307090340c00c0600755007094800140c80e400400842e1481915424800710102e20641011090070004110f82001740110341040800b00b1023002481074402c01e80010003401030219500c0c07a40c04e0014029402c00d20039910485850b0030305003680d08021040301d104e00500303071400280c0006240c9a400a42090304c1c000400320280c240810261020005090000b4201542007000c2d030000c2d6000d03040d600c0c001c2c25004840d00aa4124001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 989190026 1250 989188776 989188841
    0x80114060907020c060409020c01060f082e020d0b01120b0120070b0c060702010f091a19020c062401170703270506060604061209150519 60
    0x10900c211081c84594681001c12490100c09100d01d6a11040c0000c0001d10075106600130b10103406254020301c44550749642c4054240b040744904070098000c120b803020100c4800b10714408090f007a502010050480503148812070b084403d0071401c241e44c50071004021368000520b40880301d01454103016401002c9e000030420152030030309190002c1500412201d201c41449070902800c000e846c55900d0f00d00385141c05985a00c2030b03070400055443c10800b040c1081c014090b507102c840d040506030200361402039030320078246001000503110701034021140c00d04203030301e000034000540744e0f8000346454240410209008480d4140c82c151030120012452903076600841100c801c040160300c8150f0b03559400c0815406020842e0a030f07941c1001c10b079000340301041d8100c185000c080c09402103031142e607101c80030b100651040d4000c00021680e1514041010500b940040000724401d985131052840044030850544170103444030302289408440c1080c9100207485030300800000005176903000443c02550514 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 989191276 1250 989190026 989190031
    0xc03130b0a032406031a0315041a07091701094e050f0403020a031202010507080106091a120f010e0f06090f09190507150e0a090b031009050303060a080114 68
    0x6141c0c4605035003034a20713401e0200001c2d03180047c0903258081064406118866000c82c1d0840d404110102c04003003454036207101501c90300c6507448000c036050402038850704000400007503801d1992513401540000309100601050111580d60b08501c5802c003607030320030120f1b9034070380d032000a508680c00c0c01060502244a00844149504003030b5a181e510901342411840385401c0079410003c43e601c00800c00c0701081c1a0314000500d54001c20094a070711f941198500000c0c0316880005003141e4080c044000740e080700310330300c2070003046a51900c41011030500200c1421183c4264a0880800400014990008266000031852182c0205213003402c0021401000a0403605a2000c01c1e0300045c3c0c0120100054591034004040d61602c0c0151468000d545d103ca43c0a48820012500c244140d001d0051091844103c0c000305140c210908001d80d1000a004d10900c9560510400303214800b00000792280fa00000d0103a4041c0d981c074500326003400803040380ca03400058540c4c903061201000e000380385422174 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 989192526 1250 989191276 989191289
    0x3030313020d080c070504050a1404080a0903060510030606050d0f06200c06061009081009030e13021909060c142401030203061b03010b0c03130b0a0324 67
    0x4000c10050000c10542d41e90418014030b180000182500c0900000442030211074044405002603a103034414403003a564001407002c8101e0a00b000302c0c0000752841c0c0a05010102440c245501f0740d641d46404003030320820f946080d04241c0c4440c0a2052142030b0041c4006484155402081c0c044940c3c1c4a028a1148910140401c0e66801b2860441d0900c1381c0340c006250301e20050903031104040c0545a49a0505a0b80f480c0b0900c0c2280e9525003583c001e0400b1011611510041c003044072010801201408441034128200203940f22880c00744e0340d80c030101140074414003400684924104502030f0708003040c050100203021004074200006640700381818041a4003c2080110b0304540710303d42c5c5881001c060084a40d00d01034001150044200c03022412203008404032000c9440e00ba0150440303525950119440344c20030001802a210008010903030b9220390740c100c928002400040021460298004150b4124001500b4000c01d92600a2108841e000010554000000355000440803600d10554 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 989193776 1250 989192526 989192551
    0x41e05070c1a1005120309060d020702041d2404080c0a050d1214131209150305040b0916150509090406150e040c09091509080a0e040b030303 62
    0x9154288202401401c1541c41488459140c1c00155604039200c411100001007491034100041c6038500301031551032400040c400342d0b14201044043c040b003a40125004010350750200645001a102c52041c0784000b18800000305000000c5900f035401c1c0003d00141756416060107a01076000d04a02c500550400d91024019a0f1103051216450511003000400b03000c074040c0e0b000c3ca008058210400d904010701d454400c000e600c1c01c00c41190042d280030390701c0d24241941d0803a00000244000a5001ca8120a0500d440450755a081000a04014164480020362107a05000270880401ca220340c00402a00107010758500c0c00795862601c0519216001c41c00c6c0109814500c6540110f08580b182e060107840103010b403605007406006002c1ca04041c02140d000c030716001800d84c070301c0c0ba10f640c0200c0c0d0202c0c40c071a1480c6009003041c040d00d4081410f83d42c440c0c09000400c4030940501c03601109a100e134170311a0f200c45240c40080d102d140c00036541d5010302d0820500f07421654020080b40c0c0c0c00103949800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 989195026 1250 989193776 989193781
    0x90339050f06010b0306040c11070b0c0f06010303020a0b0105010219020603150901090204060221030c030a240e1024021903020105010302130204080604200a03110f041e05 75
    0x55440c11107140c1241025010b5000041800300150700294440d0700c082c2c5041c40304880c8040301f1204042290300302015070704240c41c10302800a010303008140f046100012074405a0428401d10308002003a40f003180940c2c00615004e08214440011900601c024000380031b224440581c014003200001c00001e100f884000001440a0042883c9d00c40303540300640500c94542c0c403560304034000c0d849805010003610605d0f542480301d010400800c20010b6005014a04580b00c920440306903820207070808101644520200c00941c902101c07514003100440135820a1a00e0014400c4206801800300200714007001e8051001000034405a800c1c0c848140000401f0101040200d0502200000c107000c1400540303003ea052517815040326050b20300844460411141103001e1508a11440c89074a0058105d44001800314407032003000c40150303c0168001200540080005a406001d90411102000742c0103103007403141420360044406e1442610f04014208100e00c90084e4940940306584100340c49100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 989196276 1250 989195026 989195033
    0x70f020f070303020f0708010606050706020703030f1103060a050307080c011b1b03050d0302070218060a0b0d020a090b0c0a120207180f05070f0503190e0f01090339 72
    0xc4400c2084040080e2101652640f038025122505404034482070b100c0d224001c00c050780c0600c281c0045642c00d0b264517150003010b40d15500a500510303010b405065032215156410f501e10b0151244401048403181d941c0c3c60250f0801c80703a03182e05c0d040b0601a41c40701c4014441400b002404100c115400d0900c07801d019441c020b00c2014122a19000303121400c0c058050101d11030b007094a005603031081003130340c2000f112030302c0413803c9000c2c1d4000654840040000742ca4110031660503142c00040161803801b07102d88801110500c2c1e404014000381d01680042c403048000ea200307100002910103041d40616040c40910301341e607614501e0b800500b400300008890543c15008004440007000300340f000240c003001544201d0000d2542402c45120a401d00f000034900c140700d68501380c0c0d580c0c05070711000c0c19500c42d03106c00611613862a0003480c1959880304841d0904d0000c1142c050000070000c004100c00f201c80c540208685810341e54007030000a0b03d45803500d4016030006605d158544407500703e02e08100c504 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 989197526 1250 989196276 989196283
    0x10605030712021b0607200733111006050a05060c0a0506070305010e0f1b09030703020d05100606170723030f040201260105040506010e12100b040506010206070f02 72
    0x300e5440c0350401800010f10f060030109850344110002e440c0c110950385405104200c2c00903070091031f50305400c0b081051209008040303050814158030012413803800c0703029020445c000010364656000c208031841d0812031030710801031403e29055420003884110300d030001040b07140c0c0b07590040790300c101e101096040a04000300b000d04001508441120f68a00705540301400800c420b019640654031440005540c2880008416001d00300312590358041100070041015990003840301c00c0c0c0d00d40906031000000d640c901c100c0e01001030040380038001450000748030504681043d0300840030b000350040900d144544a0104a91001d01410324030700100341c002555000c0318055101400040001c424482c4031243e426400d4416403007a201c90322400c22101701455408a819076101036070710140c0050140d4240754011a0f00804c06051240c1d00c03500c9a400a0950f1403003010440040d80240079000f800070490195001c4d2401c2a0340400c418205100001e40b07480006282c00103100400c0b509102291081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 989198776 1250 989197526 989197537
    0x501020712030215190501090b06030a0e0f070b0c060601020606100302070203030412112d1507080c1b0a0506160f05030f1c0522050a0501050703020c011401060503071202 75
    0x9104012543ca0101d030751180d176050741c1c8240c5281c00e280000100d070000d00c6104030120200028803280c2507507180d02c0900003a1000f08a40c9540e8090800301d130010b0030b000c10500c0c02030720094003d60f0b213440d4400343c55403821400030a898115441071040c031030143c03642c1000768061427081c6009070fa034601e02d0000c20720314800c5600c00c140a10006030060f0a011440b0301e8052081e004031071310f004083c01000404800140b09080d01c50114035401c1d4040e45140c1241c2240103003076035224850909501e07495090103a00b010240b800c0c1500080c0c2d00c00e1855102000c1e01c2078004040321402c0c2094113141c04113400340a1210840c00d80c0040c0400d1034240700c1080c80610746654003104496440781d6240b24082141c002010307100c40621100c44610000e5814003482d481817000c12000c02980c010f081080038075000500c000c1d11a80500500140852310a02800c0d12a208030703100135a54000d42e011131400c40b0303d01c6078042565240d000050080a0f13120b01101e030400254a0804e100342d495007280c03002880b80 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 989200026 1250 989198776 989198803
    0x5090a030321090308011e0308030c04050a0f35010e070f05040203041104091b06080114030610051302160c09050c120a090f0b0907180605010207120302 67
    0x22140010070507610071446200704051039036031407040200035000010b841e03c011004012612010040c043c003908100f01c2e104101200c007825418aa0365180d20180e54000d58000801420000341400706040c40c8503200000c1450008404945142c00000e4100c5441e1241141048151560f040c0c1c1c04130040d410a00701c002004020000541c00e00c0c500c40c0d40b00401e10505416001c2500002028503061080e01e01c110b4002c0000c2c203941c002034007004000c011007102203072402d0203486400310780c41c14118844064600c64540136059414007000d01d040c22154181c15100e0b500c24000c01480d038603010a0300e001c6480551b0210b44090301620a40c0190040341481000c41d21040b03502014000281c1036141110084a020445511170f25032480300c1d4442c800e045c0f4000142c100100300c140d8219071141d41d8660150304004d1051519a030b40440d541025242c1c04040c1d80425800e00180040822000302d0310f00c0b041341040740718504000030792184d94034440c00340c00b6003581c00c4200500d0b00030300100e50303515030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 989201276 1250 989200026 989200039
    0xe0705040b09062a0604140a03050d0b0a032003121611011e200a0b010b03040305130e090c0108011a031e101508010f140a03050601080c03060f04170a0509 68
    0x4c403d9a601da0b1104121425600c0100006202d00d144070301080801c15150141e980c00e01d071103018203200c00a4413400703186a40100c02c040700000420708103400d450703e0703c4846a100c503103c400d4908051600e0242c9845801c064010010011002c088150302c0c1c10455200011681440c41d2800580b034a02d001c016640206031300070b19070700302d4550000303501d03080c88110b40c0060300440c01c40543c80c0c4e5442d1114002000074416000610075442914040c41c2e1091092521904c3c140b42402c0340b0100321000e900000001c80e00d00e0902030100018800300101500070710301403543d50303d4410b0a034004c1003110315002d55a500000801c401e5840311407103c40d0030454500c402e0407810b21080342e104041091160070080f0314000c02c140c101e248540d21721412a03d6045c480741e07078241481c50f19a05140007800d4036501c849042400000078030b05006003030080c250607002e003418040300d20601d82810801030414141c0c0600c40c040000040746141c0200d0f403024406031a80c2c4031417601d01c0560b4148100e103440c503070020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 989202526 1250 989201276 989201347
    0x3070305010c23030c0a05180a12030215040510090302010b100905011101020301080705120102091f1403010e0c3604270602090301060f0f0e0705040b0906 68
    0x64002c001c00c451a8032500304511418100003d04000d03000690f26156100b100f00704400146210364050260b01741d44118103001d944820300000e072081810b078003001c400f1070300e0806c000600d41c0600403035440c160040c5000719180b41a035952a242d00e841c540c842c0041d030750ba400700307401d040c400d6010a14080c0090840c0c0c0001c128200050201c8805e8032442d8006240400210036410060007940d0403507820700d0080640a04001c10070200700302d02c02d202c41141d9424803160503203544850721495030800c041014448560911001080d0014104181c4070082081004018050780c20424540c80b000c0b03022b40035200c040c0d4030061200d810035000d41c0d40b1035a5908403401002c4040910380060000c0440341002200d00d5028101c5611100c000340c00540c008000d00034021414a800a01402c10020000036840c0d41f1403840082e00c410310380003407251215002044c0000d20900322130a800103590304180d800d0130b1400c81001d000e44580300300d86000e0701011661140000403000b089000455030004020605c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 989203776 1250 989202526 989202551
    0xb010c08130306060e0a051b030a09020d1a01050418020102063103050405030d0c020f0d08041a0304140a020d1509240b010f02100e0c03010c050c060703110301090b0307030501 77
    0x10803003641c40341d50b42071421010400066140412031410101501c8c2e00d0f00310b640d5001c108009059036142607800c0b0007442010000a2145c01c0091844122086607070100d5040c401440200d51019a82e0203d10346c60142407000340c1c9e00000c009070310111541000410150111960180031296503560292054000b03500d0301300758000b0090010766200b41c04441c0c4071700d0107034400c482d1040b1014019400036a1080034070682d0402e0107103c0b0001d0702442c00107140070f503a00c604c0d9000e050300c034a98078107041003c0107200c20071100e60468407443c0d005030002e214001464000a6035600e1054005202c00003803140c41c2c0d910451600200e0803550090940c0001d420041581d00280c1204c65080d4965031402c8a50b440c158001c440f000c000840d01d41c0201481030010744a40700602c04803034218018440d95840c03680c140d60900610410002d19958942c580ba101c1c81124a00a005055881410b0600c441e10b0381025854043c0c82c11115000380100d0b040d07480c6004a418100213400240c95542403844000c2d10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 989205026 1250 989203776 989203799
    0x5130e0a0c0303120b09040b0105060711030f0a050c060c0316062711030f070603020a0c0b1006080f061e190b04080c15030c220806190b010c0813030606 67
    0x104e9941c0000b482003016410400034a00c4003100c00408031710140d0018401c3d4140800a050840d1250303021b85455985100020314010711466180b40f103a1010718480204002031280c828402416a040ca060850052740c107512800f41c5115074451018000342d240c14406142c110450031303800001800d440c0100c900d1320f9144594644020f480c0110f6941c00005581000509014140300b01d40182c1146820880e04802960200042c40c00704219416550301140340341c0041030141c030802c8000c2c0c00b024504900036142e980d004244444012400082240944500308800d81024088042c10044000400015941c0680324842d924202e0300c00004074880010030010310a451440d01110985a160410441040c002024000c40f068051000c00d0042010380e016141e0068031442100c11604110141625152164802c0e10203a00c03070010300c046840044143d01d080810341c20f0500c94a00304e800068452950048010001030300041d0401451900d0101036010310381c4102d060000350354443c0301095 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 989206276 1250 989205026 989205047
    0x402042711010f1d24031006080c1e030406060803030a1512020319170a030f0f06050105070f08042c01080a1718090c0c150105130e0a0c0303 62
    0x3c02c44000b034a000640c041c00004000e0000d224981c028078030360400340044c07030042d218109100c0c6803418040c0810360040002d9485a10150043c4c807c003480d0400081140790b0261060a454200304002540344c1d0207403245c010a0350071100c41956036151484c1000c0207280c1580301e034009000c04014800f007280da075040341919030400038800038681e03203443c4400d400500c4003400940c140d00680c040100e2030802c00e403c1001f680100030417900b12225001680007680020204400203030368411004101d800c070310400c00c2c0101c82d820100603040c01c06001901c5845200d1010300595100086401000910300441d806000c034444043d82e4808211031070304c6c49600e0340380c0380324100e0010000425546d0000413902032542d04800c0c10000500202056212a40140e4492112151000456070141c03590395a050154542900c81696161403510050030880c048284146084940004220f2503803603a5019100108070f1200046804009000b5071070240800c4001304414210b00e0000305241e002140c408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 989207526 1250 989206276 989206279
    0x40b1b040618080d050a110715020307150908090d06201b0d02030f0f0f070c0e060d0305031503070e131202060c0a030207020d0b0a0c0e03060c030402042711 69
    0xc8840b503d804282c0d4981c440411040001102400007800d000c0c4280310304020701204006948100791100b480210200d40c43ca12040035910001d5010304004000c040c50942116800c0100a040300c00d07680c4041510449569511a0951001050621040d640290403011080400141c1d8041d0078100c08a250800b10300b03680c0011400e4045900f440c0c2c04605d41d80e45001c590702840c504440014500301e150424003040540718070501101203544c40000051000b98000c0001a80c1c40c0d240003621640488c0003406940265095600c050000b134000003500d400680340c403610040400101c000c6403505c1e145a00c001902031808040c44801c00020502298444c080c0404001d0512540b605903a1100b0a50384411296020814154458802d5025080e060300c01000e0340d09007002c6071a042c031103800a90f02c0490b01550b5004c10f03031364bc5401c1070300c2c0b0040283c00e8010301014545090601d4060000071300c080e00030f9843d071001500d02c0810110543c000c1413507407120308085c1040c2c1010544005200b0310745 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 989208633 1107 989207526 989207567
    0x6070c0f06021e011505041d1002070b16050906131520011404061512081206091314030c070b03041514040b1b0406 51
    0x940091215a0041a000f160350480c030718008107015086039075a142c210103c16801d80c2c2c800300e01c225181100d00040035144507842002e005600007403501d0038010f007100705048202d01d03406000401d02400f4650801d0342d880c0c0390344031200702e003031041c0c00414028001c9103464036004d0010114070103407128880000f0341e10041800090a0032184070701203114020380f1180000c11181c1500d0f400d404000911445180c5146e00a0302500948042c14468072034800c540544020f859800c010002c003914181d021240e1f09284500390045a010f610049914000c20b1840c5082c002c2d581c0140c8a03c58241917240b125603481c00344601000207080c080c0020321001c1030000c4184200e0004200259800e0b45c1c1e460503140aa400d0f051041040071802d18200040000e010702c0c004603a4096803280b0281f80c0c64031001d44c09007032520004588851f03200001000308109520000d60210112540c140c1e = true := by decide +kernel

theorem cover : BRFrame.Cov 989028776 989208633 := by
  have h0 := BRFrame.cov_init 989028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 989028776 ≤ n) (h2 : n < 989208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
