-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0198
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:24:13.640068+00:00
-- url     : https://prove2.me/submissions/fdd6d317-40f0-48f4-a0ca-3d4ab25e8605

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 35431659 ≤ n < 35611515 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 35432909 1250 35431659 35431673
    0xb04031205071a01080c04050f01090e0703080d0204060306120c0512010e010e0d1707081f05091005040506011b0f03140409061503060b0a08042f040e03070503030f0403050f07 77
    0xc1a241801e01b124000c0c1c0d0303030713204203c1550820b803800c0e040c010007500180070b81c0140340c10000060b030700d100031181ca41d9070f07030354845c0c0480c0c1c4072914040d011580402c0c24000c65a160203040c008107041140103000b0140340d103404201c041d0074840c161041607500040b00840e0000e401c8028243c1e1110001c0004040d009542620350b00c51440f400d00107a1005250369440000e032400a00459066685240565400f982800c10702002c821309041010010700c000350a070b54103024240300d290f901e00e83c0c104103840c08040c8026110050101c50600c5011a1400f114050b803020f04101c094000000c044c992036141801d0b03481c812140d0303c403141d074400081c02050701c040c01c2d041081251616400c18030301004a440440841d580c40c02030b141d804904020b1a07c0262184031202d400900030300c80341c10003440f00069140d648500c0b0307041178620341d51128609814542480741d50003101c418000303507140c94005e540307032a2a03100c002d100d1510002c0314400b03c0e003454882c0e419180d0041c484503149a03104d00b1070411503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 35434159 1250 35432909 35432911
    0x1020406030204050301050a060807030809011707020115150e042a0c0b0105010201050408070303050403090803040603092108040807030e0303070c03050105090a0b0a0b030c1c020907090b04031205071a 88
    0x5000f9807e04001c01c0c0301c003003684500822502100090306140341180e8070401c081e84035045190400903282e560051240350380d1071650141c40c440d00009440000980d0070b0035040510383c001c40110300b13101c01d55a00c494002c0740341010140216000281c01c0c008030340e45600b100100e2a004404440c1d264100703e03d41e0801d0410310500c1c001c0e04180d903da80da40004a082e0380d422100105054070500010300003a0081c3c01440d0000d1007400c0800e6480e0301c8480e4580745400c03a07400280000d031211070910a11a014100c040c114040140034940c607145414054480600038000801c02c4c100020381d801418801d28070000500ca0041c2902c5d6221018103000c003c807801d50200392425442d200109009035000136251740e54903403124200c2020758032030541000500c01d14080c1c5406001d00c80300c0d140d0030317552094030181401c0a1085800c2c42c2d9045d006200348400020262001d200b6441780170701260306400241c1d82126401640c1310460915000f044595000c0c0307140042c440049604405401c844401d469 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 35435409 1250 35434159 35434169
    0x10609020705060f09120f1809040b010f231903060203190b030309090601030c09080303040602041a031504090317092808030a090203031605030a020106060302070218150301020406030204 82
    0x1c0304070b5031208039009031a0040f60003100f00d106c00c10849024480b00302c0000d0525004107a2104440e60f1148002c202e000104590884202a40d2001031185105c0c04071180d011b00792000c041d42c1c03d05210441c2d0115181000251807054000b18034803400c104d02003a507a0065988640c0c290740b2401c01c440e0100c000c03582c072031404401c941004000c85980c2000400d480d00c55400a03c03074501c80d198440103400800d1280d034010304026280c14081104081007004500451062000507921482d10a8500520103041c500b03a0b500701c010414010714030040f10821011120031240003c400c804c624054648210320840c2200c803980d00d03000c1017840d85021481050b40e0005803080c2d0360014040400108011100700003c04084c0c0c1403011420491403139219441180c4081e04a1785044842c0c415102c0f408140d410448003640f00080c40540c00d942070041e04010031140c14254101a80b6900040f01420748040140ea00c110300350000303d004111008007004040043c00856803640c0f10300c402006580b01d07002e5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 35436659 1250 35435409 35435431
    0x405220624030f1107020906190608060f0102120a14160f0c0504020405061b03070602032409040807081303060e010207020f060c060c071a1e070306060e010f0201060902070506 77
    0x2680b100d45203d000d111410601da210403490500f05c0e42c00c0180a42001c1d1190740c100c041c11424410040341c6500c07440c0a0541038940c1c2c7d850345890030030031250314400380c51281150014000d8502c0811864103441c001d200c1c0342418103521111015500260060044a052588452071944103010741c441011070900d000d9085240110784400c10b02060f48101c0c86a25003003a02004000622180380c1900c030002d00e80c1d00e00741e920305001500d8290680e0010799a04c0c1d160005d00306200ca200d12500c122201c0c4120584421186240a407143d82050040b410050f00c610310024900602c1c0c81500c001502841d0702800c02c1000c1050760102c54000d41200c0001c900a01c0705110400c6039141c86025940c450b0010b02c01080255606200d40307199030060711040b00d000d64501415101c0c10121900c85203e00d405c0c0009518070040c141d08840c45020141994082c146860428840d542d0300241039540241c0c282030400386142c000700101e0042c15160300c00440b15102085c59801c020b00411250301607080390072 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 35437909 1250 35436659 35436671
    0x506090c030c01050c010b030d030b0306090f0a0b04110904060e100218010e0303070b04060912032c031c0c020105060105040e07030504020409020913021302040522062403 75
    0x4481035403891904810380d810350114421420300c0d0720880007000d601484000228155999a010a10702403144150102213602c0d2190300d0110f0804200d400c2e4852200d0000303010b0b010800c80c041c3d0f00e9442c0d24002500300d003441c1000030280030404500c40655030014240f4299858641041001000401c10041160046652002d207420550098451030391050021001d1614041d00554180305201d180a0f0580000c1c0034100200b164603910504c42c600500c00400e4508451900c201801c041d41c100d05c081c1807030110000300390100c076402c21260342800c0c0260003400c154400000d00c0d41c0105070704d280b5500503d588501d0083c055401044a81070b02d9002070055441e4500113681f02d014501400024036203030350005940c0c41c866042150801e001600014a41c04950003162481c1c07400ca6501d90300e94242141074045081000b4915015940c48800314202400e000014a28040000d0480b5014140b502405840e101d142d004500804001100701540300e8003108950001c1100610038000c0391401c2c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 35439159 1250 35437909 35437921
    0xa03030c0306150203041203030b0901060c020f150d09060e01020a0909140403080c0d02040b070308070e010914040f0e010905061803070308010b0a020106030b0c070c090603021c0f1a040506 83
    0x402d0f9002c4014a6070040d509150038001040751003011080180c04240c0c840b84180c0c1e20740c84100a150180001d076403040c0320951107005004c4c01c1d56519903282e00031841c104084070114540020384207800e01d6003030041071010113814000702a10503141c1803c1c841d4400a48212402c0c3c2181020b001c4511201c02403002d0742c4c0043e28081c0001c03007268054080f034100400105d044188000030501444041401130406440b00f84184203904180000c030302041043d000d01901c5600a01c1400002200f481c016010600300205070f0310700e182c1500b040c3e0265856078007582501c40a60051010107103420001c00000c0c8007410034981e64071050391508440084080c072446000c501008882c1d074250180c44003c426403a0900c402c00d00d50101c02d100c021950380d05070100002d098505000d000c0e0441449a903205e488500f00326801700882c0e405111041d10b000010001611040141122402c0c2c40402d040c1c50211400c0c8502c0e2804004801460a82a007804c65402c1081031b19441c0590701510841300f031030343c0384 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 35440409 1250 35439159 35439179
    0x20f06070b07080703061a0a021e0304050d02130e031b150732130605040f030323040603050f15031b030307050f07090b06030f010504020d0207050a03030c0306 70
    0x4564041d041e22040360005074420b00880c2e0f91600140c1d2850000b498603519142d50050a0700030008a06000b8001000e142c126810881e045100743c0b5001004040d2401000a0b07036640314600c102805440c1c00c3e000b02d4259520f1440083c1c060004400c140003a0041c840e02c0f40e101e0703020320400302604c02d0501c400200003000091504c0b10106445030806c4035159850700350340310b0003891520f202140302d0810310000c002c03602600d90211032911030b0458456600002c031420103105a0080d004100c000e200810280842500302c004490301410201120307071030442d209810407606030045581034000200001e800e82c0c59800244210f908180d030100603281c03a24510150b045a6005035815807080c00781d0368000040304544981040020106ca151000d150b5460742411441d14401d20560003049007048000524081c91140300300444149240d882c010440210070300707042c02168055075010522041c0300c0c25a03812251800e401c01c2c200e510742c14941c580100908550414800000c4c1000400584100380c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 35441659 1250 35440409 35440417
    0xf0408070f1a03040204050402040e0a0b04060e0a080706021303080705071401050903100c02010e0f010504020a090507050301060c051501031b0e061c0c0e04210801181a03010612020f06 81
    0xb410aa14680301c6400b04006420b0241c010b90b800ba685549641448104010b90303024180b040507540424036050800c0340032280c0c2e005040300745030001d043d06800600c3c200100c880c0244c0c007003401a128417001c0d00b41c200070001030b00010310016000071035100380706002501604644034048010014401800112540e0081a0ba010b401d0341c440c0e221075044c5400e542000444030154070001446c4402500d0040c9800c0407104886103d964450501095040168000e0050b0040303030000e0280b07050410b0010107e1205102d0202000981c10754901000700600c0451550002c620264a513175843e418001d40c8607156002060700591a07100c001504001c61414034440c070002002e0741c810f001014608400d1171100c000880344048000300110786001c0c501c2c1c0c0b1b5402a0b00540f04618a4410560a5a0521054036241c0b0501c11540300401403ca08588118601c2102c00400300e0040d480c4409030240e401c40a548640c154280070010685a28070210820414003c80d40003d08821050a200e907500c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 35442909 1250 35441659 35441699
    0x90c03020a0912050c04021b010f05060a0501110a0b0106120b01020106050a05040b0d06090302030307020f0303010305120c1c0e0102011112131a010306020a030b041b140f0408070f 79
    0x1c600b11042062040c480c28850a10307000308195000c1e6007000001401b06e0b480321500d183c182101c44000452076100f40300d01026015500010441ca040420014052540a205043c10880c074601e101007480310910502c004c01e540002410b00c01e5031a080040c2402d480c07110303115500b23854510784e2402503105002e214100c03100a0a062a060b00702000e20010b1f04188852a0300b1002401613540003d042d440348d0141e060081e400ba5841c0c0c101210003d05103054104021590790052006101166000c00d03e08a46030702d401c1c070903559600405416041860210102084c2c40010031142c3c62107820500c000c4094409074001c000036542c5508042ca18050113158042940850b40010302038448010342c06078503801540f6048140350070324174403e8401e500340c2049400c1c1b41c001c95030103102509401146c0180b20111000c3c0885c10741074049558a003800c00c030b1001003043d1503040441d40180e1108031030f400c203111000c86603680c2d00d03026500c0c1e80720340034450400b20912404e4001a04028004d402c03070713052 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 35444159 1250 35442909 35442917
    0x705090a03120507080f03040203010506150d020313020d030305040b010518062e03091b060507030e0613060801030209070201060503031806040b030a0e070503190303150506040609090c03020a 84
    0x50650325580702034a502c020307041c24054208100c00110398418046c10106a50704491962443e00e4814142500c070080c0000b401010020007411010b40178009641c0005569500140c90355114140d01018050300013000e90444000010b4405060381038000324070440c000d0b0788a001b1070341c0e540180030505441015400d482d81d80c1e04c01061191030300d614415040b0005c400c0f45540350864007071800c100d129460b007200103e9a228200d100308204200101012950311074403d043c980780140181461003451030041c00c00540e10001c0482e07595204c2501d8000821040c8599820f4480c0c9005e00385201c00e0000368419003c13900000d8140d88140030362016982d0140282d81440310082a406074008035540141d0b001800340b002103603a0b490000954400c400031403002c50707200b104c07e107a141481159080030b80281c001480562207510841d905859080d4185800a10a4841540b1400300d030595009a0742c05000000c00041c901da008400c9420740f0040d0204000681c0300040036800c81c858407200038003003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 35445409 1250 35444159 35444179
    0xc0303071704050301140a11180f0d05010c02010b18040f030503071215150906051b03070206030a23040c03060c030213090c030b0901050d14031207020703020405070509 74
    0x31500d40640581d6a080390605081c80d031034900107030a48210007045082d4011400801c8104c3c480c600412800070134060180d031070407605007000740e03482c03072115441f0b40940fa1100314000980c0302c00c45a650307d070341c2180080140141d8090000d0280c80c85032181445030804600c1c200010389038169141c0202d600c80f0800c2c000303018640d0140d88980004100406101030000d03030215908045c055600038003440c4110380041c60800d14500c01130070801c50030034200000b03d101480a55008412500c42c00c088644052904054070701c1c01d465032140b02402074110001006000d103688041e00606400213406c20240b90007030304401422540c0204a60141c0000c111401c20000b044c043e61111100e404946400b40c60901007019409211826600810080742d541c1c8040141c2681031103a1000000120ba554949500d408009819043c5445001d0241c0105030003501c03800e48208200c1d50600c200e40d10103003003417a002101039104c5115100590066080c80300141c0c0843c41134003110317900c3c0c000034040306072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 35446659 1250 35445409 35445413
    0x5030d080403020f03160b0708040312021303080c0304060305091b010807090509040b04060606051303120e0a0b040504060b0708030a0f0b06040f090c031107060f020708030103050a140c030307 84
    0x8524000c1e00560660081031441500000280300600c6104461043c2400107034407031074810038481d801828501003203441c00a100000703a1003c2141c5840b841c00381c01684590300e0035a459118001c69100070302045002911540c2100048003500488596450802843d62801c840c40c2d04c65241c01400d4400240310370030403082d03600869446401044620300751071000e490300085801000d05640c140d03505620741003003208100c214040d41015088614049003048001a1100700170303251030000505440c1001400001c40b48078020b042c50103140141660505039450410100da82e009000312405a400e0140c0402d545d0a40310442d0a2107070702245184ca0f654030803074404002c004085160b20103584613196151190f40c2d400180c8050150b040c061400390f840c1090500071181c100d04030b4420306052620110210b40c200301600c46d070507040503011038403500c508642402481810002000c030304003c00080144100085d01e4680b41c2d104c1c506200250001c4440c071a9140020050184c0c1544100841c0700 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 35447909 1250 35446659 35446667
    0x5010e060406152d020c0301110a0f05070212010c08090705040510090b030703061b020c0d0302030901051b0106060c0302010b090402091801020904050703200a0909180f0501060602100605030d 84
    0x41da4040c5502120300840b0001e00c2c021840e84407041320f0016031045c021013031186828803a1807442d0f00307556806407500000940242010400001c01018082d022408005540340d588a030045544800020001d1074040003000e410128251110400c920450034081568141403060f0b5000d040c85015122046140039100c4001d04030860f482c6405000303480700000090054021040c00f240342e681c0b03210b0031044460000f450041c881000302d1284070f443e8148408280c010040310102c04080ca4030725550b00b0107030901ca85c1c561840c030700c101c0150320700500065403e0340705060b034100d2840bc1d03009104040c1040100070f1100310a07074010350300c0380011000c501c0340e8005c41c034610310f81040c0e00b0025040107a100c0004089a400b00c82400c0440e1707c0c1c52000c182180307140e2900000c40051020103043c1445558002c001050034050020103503590591661141c510780034180300541d004000164100e0507142407400f80c281442103e0140c480c0000860ba616514064241507800150041c103190002c0d243c116 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 35449159 1250 35447909 35447927
    0x14090414010515010e0d020a050d140f031306020c10030e0f0604060b090105010503010b03040b1503030c0a030801050406050310020d11030907030201020709020304111908070905010e06040615 84
    0x121035026840c031030080404280200e074855030100310101202543c00700050700004940914a100b81c40c5504100c6c0140e03210381004046e1807050b101c4102403241803801c007089a0b074421001c2260f200305202c040c1d02d100008001c10640b02680300c1280019070f585000d0340d46d44a0091307220380c41048580e4030318000c0c0c0309038004034941d1230010483d8004a1014009428000107a4040d140191070b4480000c060401c00710890040c042031a1262441d8500300c04080740c0e01000d040100003012010110348400481e80048400000c0202580d54402e41c030032402e6958030015008501180307921000084610301440703039408490000d0003528001c2175240c2041c0080d4480c4081104540e507840403040704104800140d4803540d00c2e000185099030641c000a490111154013411360980100f00b0040022041c1e01d00d41d0750407038162104032000141c1015504094141d800004c2581b10300800010640300b2038221904a480c1030303050f19100e0700c4420a00050b9183e46c0220b9a801a03140002c5180510a940807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 35450409 1250 35449159 35449163
    0x204030b060f01180801060f06090305070605030a020f0301060c0501060f0f060c1e0302030c0f0706090b0c0f030d0b040b060304021f050f04120221100e0f0a0c0f090204140904 77
    0x41d5840404c0c400b00c4040780909800c2454169520b1006201c0c5880300e014a00c060700040c10595041e80c55903440b00d0391201c0901943c1e0411801102003052860180c05580c1090b095012003508c80d030f100d034801040518000341c00ea40c250308200c80065244c2c021816581038030082d114501400d81405000c1d610030310303509804c41c0d01803440681c010007952502e1400e000309101e0360195a42e4644100e489103019401c09600302c0390741004008000003034000a80c101107494050390261100c441888050400812203d90842ca00000486620000c1185d100c60749107801150204180040304007840028002114002d4010b52056200345070703540c4c24030700d8049440701e5281641c90800c084c1a070080b541c1051344880c00ca8940921900304610f011401a1550406400b0000c1103000e18158142d58603041d4401d43e140956501405940301c0091000c440d0300d10107042141c4c20010145131840300d440040c440c1018441c40c081001c9090845030003103404a4240d4000140d405640714208000c41c1809801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 35451659 1250 35450409 35450417
    0x60607080706090809090703110702010e040e070905090f030304050a0201050729040309050913030f05040b07050c0102010b0306070c0201081504090308150f03030301030f020d0b13030f030204030b060f01 89
    0x46a0700140490180c9600326110740b0395207403120311074024018002e00150180d01818140102c0020b00c9050000382c0c0e611030340920345666130000032400325005146c402c051032034a0149240108146140e070700694012107509049500c1088071001154480c0020344000740383c0d81050f0f41404c0075611410140107100d0181d842c1000c02410000c60215032148400e10404600a8604100070700d60001c0405d40181400d4a00208900d8000030b1641c101c8100b52004050080720320050100030f20600541c0c000e80040e0002da40e0b11100e0381840e41e81c07002000c1100740150300780f50fa90511400c0c04222036016182c3c07034a60f0000390f03406070700548110700018190315140c1c41c1300522405a6545020300c0043c0d6010351103070140da040242c00e44000180ba142094017a4141c4020403020340c400004032411650042e1081100076001e00c0040d603405000c4c0406003400040c01c060040e004000304801c03030528460f4403491308100d0180070076010383c003440c03001130000c0044030f0010740181010348181c0083c10701450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 35452909 1250 35451659 35451667
    0x30b010b1e04080f0d080103080913060503070b04050f01020c0a091a06120f0705090607140c03030a020304080105010609050d0f060b1002070e0901110a05070305070b07030b090a050c0306060708 85
    0x70340c100e42195100c404944d110708030040410405100d400028513041ca0700309215030654650344134030310941080c035002c1d00300c04088684c030b501164092406070500034140c071620740e51200c403518180c2050023094410001d00180d58101d60002400c040d58002c003904850a080c030300321020f00105107100151403008518400040b40d603641c18000c242d0500c49400e2688241800c0c014903071660002004c840c2404010081e144c8590785000c107480c4d42c1688030360b5141880b03070103910417410100c1031000981c040c400401d004182d903402001400c180c3d00840c0003045541c1e030360034049400404500c1140e4109030840001c1c0082014a690803480c180076600100c4c8424001001c504c03582c3c5012030000041c1c014200510840c0000c1d6503440d04400844000d101c00c0207002e40d04141c1d840344418001c2844000070300c101c1014000c6058481d12a042070501009190182e406000b800c031001c0e82502c039001d414000380400b038407407140c82d00800d00078842c10704580e26181400201c1d072200c501500e800c07500b44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 35454159 1250 35452909 35452957
    0x50309060301060c0b07030c02101805060907031a0c090d03031d01020c0106120812060109090e0114090a050c0f01090b0301031202190b060f0109030605091b0307030b010b 75
    0x100254020f01e0355a58240005072a0305249a12401c094001d00805080007078a985d615400249064000307598100000d00140144c010542c070981600b000301503000b130700200401d84901081c100100c034092846512441224440c01e203401d1421501c291886000303000c40c1c07002d801c0242c041584a8400e044c001200300000b030282c0e103545101065400243c0d00010b0320181c04000b80101c0c0010702c19049041c1e4007070bc035030340d4100260181282c00418041920001181c0344c0c401c0294000901520908001e40143d0701415400b8044c1210070b01004400d54000c82c056980c001414055180c01c0806049102264802c0181c0040001c1000d810081159804202180454000e600840c03081e80c0705440f80b207603214045e00301f02d000c284d54850801c00546500c0420000c81c0700d1540400102c6100301403c204e9130040c1c51115080c3c001800361442e0404000075000005032620740072000a03030841030200d00504150f528840c03070000400240507000100308203400200949403003407131541c0e04020708a0320 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 35455409 1250 35454159 35454169
    0x51c26070501091202010209090c0c030403080a030504030e0603010602030714010b040c110114060306041e0803150a0905011a0706060306020c0a03030506031b0609010903020411040e0928050309 85
    0x1600c080d07031540d5480e41140100511102d5610103007606000075410000c0b00350010381241d00080c030540014800007003407544200701348120341c080c1d580402811707122414440018010441114203c1c08100100c1195940b8540082685e0482d030495008528028440d51252130000c101c510014166480301c0c681480e0b81d503980030b4807440321800d9076030b00254001f1941090a65108018103440004000180500c07a140491311691040c2c000d09031800e003d0080d680c0200030800b03402c1c0038241d8800401400b025407026005040501c0c0122000303926141ca4a407000d08444081c0300d25010442c2c00c1079002041d20030540a024054080c400c00148607603a9140c940c140d030302c0100d4826943e04030300c50318020150507114003504802d06400500c054034400c1940710b01980100c01d070920075403001c01c500010368491f00581c4050f66001d0000d000b281c6080b060f6a41a070064000c1d10704203003c40c00040c2d101440020f1021900c2500f9046003c400700303105000d00035010204042d100e50104000c984499151 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 35456659 1250 35455409 35455417
    0x1808030301181a033a020c152502090708060603130309030b04060c1409030d030f0e120a0e030114130c03120905010906081005010503060a030209011806051c26 70
    0x2a54040704117491800348800d4a080310151000300c1549120001c160712640014050302441c0195121003001c0d40e10910041e10340201e0070040c0d5280520b80f04030400d40c0c9400b820501a078400d4580c182a40c41e826015140e2030801c4a1542e004003080c80060300c440c0c41c01d1600c8070b0084c068105001415207d40702c02000700d000320750030303a0703540d0310b41815a1500303610510620b09100c8803150f2609000c001400262035040c0701071b0b00020141c80f41c440d913401343c1a039400440154900001c07141040250315142840350440d030948400b1a80004802c501400c060140c3d48411000380d690342e14660b00d6a88a065401c400c44040da80403030070190100004100082c445510344207a00c41c0d51100f841d120004000c005660440c204202c03010003448101c1904881b03150644000f424099100e98420380410103402c0103031f101a601005010001070803002e0403c2180c0e10b801400400e0015580780c0d0203016000800380008217116003030400880125005050b240c00d40140300c8820594110410012070203070304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 35457909 1250 35456659 35456683
    0x50c09120705090c030106050307230c010c1202090904080318070305060402190806060906060c0304030f0c0504060503060705030901020405090c031905010609060e0f060304031808030301181a03 85
    0x10044000740b00342d1400e08089948010030640003499503040500040803800041c00341c0c070500261903013070380c82000d405074103244045c1a4100301b074075456200d11140c064611005a1404103484007582c404113a168000c0750011030001c0d003101002d8a80e0f5842030042e0f0310041c440400544070900410318400c09010000003940a00000c02c040c2c10503004000a2040880700018800d2000104001c03150700480ca05c0c4d402a02110800580e0341c403100882c00364842da4036800e605000002c1c0205c20804c101145c104042e0040e0301010403c0d032200b09001c02c540860240e5907041c0d001a0001d906581710740000c5511000500016040c507564401192191b24107072240008000007004104007034907405082d00c0b014a103500e0500855162480181100445004c2d160400140c3d846a00b201d455012448410b404058005035591410f41001002003400b001103c0c00d11820600010740c141e40041524141ca541e45000080e81d03941150020040060412084003200c8120b0901004c0c1d5040c02500d107015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 35459159 1250 35457909 35457913
    0xf0a0f05011517071e031415090d030e0102310815040203010c0c03090b0c0115240f0e040509010b040606020d180e0109020309100606030204090c030c080a050c0912 72
    0x100c03940101d83c20180690811425008a40c517941d81c6080b024042c030b02201d401c00422081221016825400d0010b1040381e00388545042040c03202d05d0b4000504600720340907664040050351001141c0509070711a80306066003d052100c00d010034084175450400300780c100182c1c0800e174503903076203a03482c2002d034601c403145c005400b044100001d50500b809611040019464250f03800c0b83c3c250b0b40605a0841c40c0142648504003003041001c0c010254031024082d070949482608041e07a4400090403800054181401c84d030b04d800c8103d0f98580580158941c4800e941c4400c510070b410030051000910b8000c0c50030710706640302c000d09071039a2110703c1003601038580c41d400b91042d240701040c05404a01250f1210995021f45201089000c41600301541542c083c0a03001d41c1e42e40f2403640d420f180a0f505d403540c203290f80c07420700b0002d4440d41650042c0119100300d2001d00c0318941905080c2c0440c0c3d845240300700490a00400180554007642c08280e00170b2220b08500d0a00121401191404844d00c224681c59 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 35460409 1250 35459159 35459189
    0x501020d050a0e06041203090b09070f06020307110103050703020403021f030b0d020d08030705090a0f15080708160306080709050a0e030408030d05060d020603040b15030f0a0f050115 80
    0x191465000d62a80080041c1c0709000c2c0780080380c403d560301d920060000d4051021110b051141910940001100b1078000d520641942041c070176203620751903076101c0e42e03689020150340058502e001100391003125800c07046909110b00340324015400303010300170311a0302010703400c02011005a03204e24031605000411250035010314019000a0210343c04001461310440070400440b0060391028030b10100903600c20310b441e0b140d8481c12002d80e96800380200580c0e12490121010400c081080304440403036903000c189100c19005904150f80b500019a0180300003605007002070180c01800c10748506040c0f00b0320300010407540d921226814018150401c81c03400343c1328814002c1400550081c200d40407035038009107150a24224a95a0782c0c464160318261b895112000182c0f0340e992440325660281d0081c040f5035503482c16103410854004c040700c1024100c1a280c0e0400c040f8140058090b000c0310100004041c8441684c071400e880400200b011625507403980101c7c50180b9602c80d91900411100c6241400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 35461659 1250 35460409 35460427
    0x3080c0705011112090a031a1e010e1305070f08010207030e030c0612090708010f02030610180b07050f12040e0f060d060207111005040504060605040f21050109050102 73
    0x24a00035901441c1042455009000615004111070384080300c040700099071040c0410108102c14410f5002a14000c6100003d005280802c41c0d1244100300f42655400c51808166814000302420300859501c1020300000982c0000c15143e00c1c81d006001c1c0741100d0b80250350f0280300e9044441504644902e940100d40c903001c260f0404042d41c070b42c01c42240540303500d042c1000400c0f42406014200035400c0308040c003140582800380125009807103098000d101500f18000c000c4069801581c403d40140858034001d14058865015200340310300440c03c6242c3c0303900e030107801e071025000001c080e40c0ca0b000d81e0f041000c507018100f010343d0080d030345002115151740c03a0844c407070031004c401081905000c403000c04111803a503c00810131210381d071200005850b29454103207a04460011640c03660880f2440540582c9030360090041d000301c038811070302400640c2d10ba0360200d8450040303210704404261071490a201c4901640c8111081082940034445450240e03100c0740c1c259200c0840c00d84269500080760382d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 35462909 1250 35461659 35461663
    0xf0c0501020d030218010e0d050d0309290403081f120201020706080c07150609140a0501050303212208030a050114030d030c02030d090507090b1c0609020307050a03080c 74
    0x40031407642011400c0405d84442d00c078003807150503031081c1084800100c2a03c0b59844030105120f0b140c0010880d45903039001140070f0010034480e0070685030081c1011a01649400507901c403207124482600d03070701454840340c0e4162403003c3d024103858915000c1c10302d012071408129007040001c1c0b41c400001002503c81e17000184c10403516801003010000902e081150f084140001c60745410b238400352400084444400e928000c118030307005200d0756824030140021124120000c68010074000d0380030030003070342e845040560741d00c03032001d0000f00003604441030054020158403070356000100b980c400d281e0a083c0026602004094001164034503808020303c2903e0b01c10f44106400741c1184c0c041c1104c186080d03000207680d40800c24420007003544480040e0700f00d41c8240181e621084914a00348490302a074a4284d407070f10410b002d001001490003201a13040d16015811000d11620011500003074005a1500c0307010f00801c01060f40c251040210020341e603101c09460900450081d000d0544880200e00824 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 35464159 1250 35462909 35462923
    0xe0a05010609140f0408090103110307030b10210f020d02160302010b10050405060c070f080c0405090a02010e090709350c03030406050c0a06020f0a231606090f0c050102 74
    0x1400d04041604210032044d081818940154121001075100d01141004a01504c160b44030a441c80c00c0c040288140c0ca42c05422510314241c04940a0242c0c1d80207990448003030307074011031900c0c501c512441e44030b5400030300d40d00580818a001c00f0240c0342c84507149846003030364010700000c0035018450300e5010500d0360a00c1400c101a00440e901201d200f01c0842c020071034081c501510f1300c664800141c2d201560750811108000b8201c0c901c800403001e036100001c984420f151382109001ea03080c540015060103010581642d2503505031200b0a01b41850030600c5469407004000209001362102d010402400d5040000900c00265034114a904000c070700c4d5500140c3c005c0000500d540c800300c3e825899590100586095a0861404985508051605618100281c04054030240c400280422124103040091022800c10b072507240c80f0100380003601409421300160700011b9041444103400e410282c0c4d460030600d900909011611010f5626002c841945501080314074035040c0f6810400c0756014030940b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 35465409 1250 35464159 35464181
    0x3050a11030403030e010e0d02120715050f03160c17092706060c011401030f030e0303040303020d030209060403060216020306070c03090504052701140c07030e040c030e0a05010609 79
    0x103581810f03c0c5580c0a041d075031842e84254180304080d9926480c0e038845400342c4020503001088061480031030000151501c0007801841005c40710b03c1c5122581600803000c4942c240403403040740e0302e159540881742c03054a070030410050030401d00d14600b1003c00c10756032882e1110380c0f08450761581e07402c0d100b0030400285041d0800a640841c00020f00401c04184640d86601c80016501a5982c86003495918018400070b14060711046404002105100b00311410400d0a4440d40340c1900c60140380040556030b001d10700c00100107034003911155404512079009080154800f03040c190034180c8940d6400e05907040242d00c011528103c00e003010a615080200070b07003003400c6082c003403c0b02e4a2a00e0003091100c590184a01560b1108003044031081b83c940400e250384000a0743c4c1e1044010280041c0c041e11890842c01194060346020480300000380c000c07103010a0741603e6112112450708140005060b00141c43c20505984003085411035206004403440503204000001d09281004021021900d03a40c0d05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 35466659 1250 35465409 35465413
    0x50405060303030f0a18030e0a060206060d08180a060e01090e0601090b0705121303051209060304031b0203070609081509030717091008161d100509030105010303050a11 74
    0xd10080361008021680c006039401480009656140322420291100b117040741b0a0180d00d00846040c154012070b140206c0200300c1c0c001d00d14554a010480c0e550034103071071055010b20814804000202040014803007090300000900111554500107521811070742e2003d0045400c04901d80001e41c0d200c042c59020741101d40d40300032207044c000c00082607019103003c1c4d2818020300144034070500a0411001c1c00d0515010a003940c0e40d4600c0920560038022803008880c01d2142c0d401b541c620303101b01030030348082480140482c1e0a40d601e85e2421120b00f85203901c03103451400140454000340c1c0f4140b0855025101ca51035820185141c03801261030501c038a410304800c0c104107814030010020100485050b917130807a0b074013004a0010142d083c1c462003001240d030780c0003640340c0700c00980b03641002c00688108030603000c0c15002a1000f00a0715a140072164041308540440e40c564aa071614600c0c01000105a00e45281010510710109086810030380040d00400e201050350041c0780c0d4040041c04d070410403100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 35467909 1250 35466659 35466661
    0x60c0b0f070203030a0b012106080d1103090906011707110d030605150901090b120402040b010c02030717030d11030f01050109030302030304020108041a0a0504110a05030601050609040914030c07050405 88
    0x70009440f8003016040c040903540302c6100e0f000760f0380300e60680c000380e99070004105907501140aa080017007803548103048160140700319980042d0300400d400910140f03900c01640ca01981c032010441e070220001c19072818401c1058009200c80104104a44140b400f41c80307403aa45034901d0103c40c50241400c1c1650101828440180b000d501c9159141707803000d80d800f40c02c584400c04031005031051800c2c1c0d081104104400f20b600c0e10b007181c4088119025900984040206002c400011141c1c0d194008000e034059000310001c006d2030ac510105c031043c8190382004e982c02d00c002140c404c81070b100380c0c009080c0c1c1c0142c003105100034828426071050041c002420b01a180c6450342d9006500c90000900c081e040c8000c0070006400c0c080360b01200b14a03d0701015040c00b00d4a00b20781590000c180c165030a9031448404104c0c0c03622410886201c4e01960401001008aa8a080b040050302d40c4107014590300261154402e40010f00741034510907207950582701441c2c4440403800303035602d8201d06034421407007281094 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 35469159 1250 35467909 35467921
    0x60f050907050a05060a02030c120d0f0b011d010203090301020a021501060206040f0b10150c0b06040b310501030309060f0203180108130507080d080907080d0c05010b0a060c0b0f 78
    0x1c2c076074078220f8130280c071807075100c9920041c141e085004459112059005405004241e502640002c14510740301c0d0000300306100c800c10065080f200b100d2040c9001c03544000c400300c10320562031002072480c20140304507072600d807260000c2800d90b0040a80714015078070001002004072640074400d805001144010b2910349843d0b264201085c0655201a01b010b050a010441d10201a1110b0000e0007007003081c51102c1000203001000c0c81c7c851002582c00444580100c0d507940b802c3c1c01150382e06000145407600c1c56141985040800320348070403d80710000c41c0c81046402c20600d0050703a000310300039216035555a01d4150094032507508d070710f8a07c00f150010004100d034184652442e024480c8286045130702541c80028140c0ba01c5aa00d41c040c00350f00c550100012041c0001035010622401c5543d10241c80c0c0303400c071505a40e01030324003840702c1e150010003038824268400c48010b400c6501450001c1841c0d60b41d47d0101341d102456801070000500c0c20f040140038001c0c40b003a86a001207080b000764a0074a815 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 35470409 1250 35469159 35469169
    0x5071d01050d0b270717010b01030c12110919050102100b03030406110a02090c04060905061201060c030504150806040b030a0b070509060409050a0506031203090703170f0304060f05090705 82
    0xc0c01c161000c0304401c13401e80c61101031441498014a0441200da640e91503141d06005c1901c5a04003814560a0075015002035209000320041c1c000b042e02e41321000c51603000ea14019042040c2100c0c80084140002100c540d140d204803130309103840b04031404c510340c10300c40024104000003080e6a0403500304812a0a240c030004201c60441e40c181c0340c5034982c00112074070142003c802007006580141c11b2818010301c141040000c00444803161158840c0c5076a59081c4140e0303024999203517002c1c81140c0700400c41e66000d54010b000f014071030324200b03142035150040c0c2c540209800340358000140400003040301608261140480d00301c4103c0040142125903500d0a4102a00900402c1007000104d000b0703c00b51688015034019000d072007002e11035450408283c200034032089420314400c0c803d281ea2901c03a48104d10880c1c1c090580e800c0038103809821500c8400080e03402d2140c24400d51801c002c02c0481103480d01c09103015511131140468a81c0903008980d05540000d014a980c0c2d03003007404200b002d41c2e07030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 35471659 1250 35470409 35470411
    0x406090c1211060f0c03031e07090506250507080705100302042303010b0406080120030405031603090f032004020901020d030e190b0405010c030b0112020903070305071d01050d0b 78
    0x11030f2601e60350340c6030003103800e1540a252001d660502c0088144200d0720241d041911200384058545101c6a640d03101c01c540c090868441e00740c002d501042040d0200084c000c0d94103512079a40d10880b416400d541c3e5007803801205a0002c14140c2181c0001e12440c64030350a018111100c61070294105402d01e4107002110300807110001c54041910b8801e03d1685003900401b505901c014805c0145503a00e000860180000811045001040410b400101340d0000309881c00340f80c0090040d800d111000b040b0000c10050080241c1c203105502b030b40090180c0005106401640c4120040f90311f20201ea000e40c1540f01d41c4204481c03082e4014040106646d0780080c030107507040243e00c1c010800c20171030700c085030400c40d0340410845580c00356501c0006201164100318080c510403c001c1003201c1c81d900c800c03421507490841040c00115107054000f484180c43e0082d00080d60020305a401c01c40c0ea0b60b480d50302d426450382c044581e120300c40304828000500d001c5558014a001c0d21204c801248a6440d0095014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 35472909 1250 35471659 35471693
    0x6140d02030603010b09010f050a08031908040f051002040503010b040c120b0d0503040605040e0a0203160809031315020c01030207050a030804050a240e150408031902030406090c12 79
    0x5030210025580c0d50742500107030801c480c0a03040c031000d961035004858020180e8040c45000c1c1d6030b85400021040c2000045881d00c80941d582082982c5e204901222401c2d4080c0003034034640301d80303d0140c02140e4144142c000d5030b14030380d0300141d45514007800e25003520b4102c0d5129110358600641680c3c01908082d811401d204840000990480c000b0b001485405002c000641207202c04039010940b5a00100140207441040582074569a03400742d0300e00c1644002c607a0050041d48d07484640a0b0107014590280e004140d040c16681400854070041e185a5620703030062880c03840325030b501e4074207a0301803000d03900e0b56900303103820361401a02e621002c1d601e0800c9803008081011200010301440f106025026036140d0020713000c4051503154a20340f098890340c2070b03100c04007440c0c151920390941001900c1e442c550030011384240c4c4d5950b240c0718204281c1009112540920500a50842961292008500c510300ca083c00007554501402d0002c8404101e030865001000d40541a60205200c11282c0b01034038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 35474159 1250 35472909 35472911
    0xa0201080c09040e0304030b0402010912171605010507030c0801080102042306120a091106030f04021302040f06090317090102071203030908070b04050f1b010e1f0507060606140d 78
    0x1e0b42d2001050082410142031049130001003804070403c008289540c0c0194001d989183c450754070b6110780e078005900c02500612991024445031081c200d0403019011182900710603114010643d00c450b8213444003128204000780d5901410380500341c002040c0b6001d48680c0c0c00841c207050400d45600d000c24000d2410b401200c040100e001030640d125001ca0301c019421441008003801d110130304c500504804101100c0402150010b81814109002500d10a04038081c81030b04913100c6030203000543c0751240c4200f002980070080406d2030720a0b010400300504090b60340c3d20b0603529604000c00310145d44007503004c0c45841040108181d030307400942142911603c032040100880d092070158001c103111680105240b0010822170140301051402d544910b00400c2035424240700c2a40450721001039550700f042c80348204140c5072403075100c5c00014840000180019a4046204090240e21910652002d00040e40040c0300000c10505001300c800a0003541484040e4224014580e07d0702d014500d00c5804c51 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 35475409 1250 35474159 35474167
    0x1a03070e090a08070b070f0c02060702060304151d15011214070f06030e01150533030f040201021006080a2904110315061f0207090e030a09080a0201080c 67
    0x101e80c144400200698407000295444010346440010381404441c4040070404101005000c6030141500c9980c0d6580100914a85001d503420443e02d42c202034000c0e00c0407050604591203000c1188510030501406d600e01d85c202141c8141524030303180038204181a0703003510038010410f06140761540c1d60699401224003429810204500303180c601141e01555042000000000d10a90958400c052140307162000380908003c000f500103032010341d44a1560003903030400c40794a0045c1c80b02e07079000041e170000d003000b44102e00340e6040d034416801c142d40c054800941d0310280402c668040122854141132a101845100c0c50003450544407580310380c001d0311404d464038000f92003070003030900c1d10090002c0354a440183d0034241082c00710029040c02c2c041c000e2080500c040003071225a00310368441c0c00000c1040d003200082100d100d0070540c905840c4415071040e900c01041d07161140c01201c03100c0d02d50800070360312680d00030743c02132501d0b1140d48850090f400240490340540d030700c03e600d10b034066491350415503a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 35476659 1250 35475409 35475421
    0x5010318080301090b010e100f030506060c03040905220c050603150319020301061e09020702010e0310020d0b010c0b0406090201021609052502150c07020402030a0207061a03070e 78
    0x1400c4240200141801d000100119220b02150b105802c84a800c0c2d035940580c80d007072001c0c4203058220100000204016508000c02644203402c82580f064014103014102410380701c10615607040390b00031010587d1500100503080400860901d580380c0100100540c060198a80e08444a03c90040b5030048500000044a80500c2300302c43d440c92002800f240c05010030032907400c012200b9a0422407181d4244100050385102000100301c2c5c4041118814569a1030304403040001d500c0a5412030602417045000b4000d42d5061040c104100c3c034049000d0390b0b0303030032900300030085414030801d81c0c0c117014050301181c0104604e0791140e136005030301c82c03800110b00d0b10b03d0005130702d4140c0c1d0421000032102140e601160609003a00010702030012211004250340d0340e000f0a880310607035004a140140c1c07001002d03070407050910324603581140d48082c04605e44000c68002c141607a0003101c0300040c00d500007403942c00b0400d00d803290100d01e01c030500c001104240301c0310010761954114407800554000a4002c210 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 35477909 1250 35476659 35476691
    0x604060305100f060c0317010510050c01060801140411040c0914040902040e01140a0902010c030c0303020d0203040c0303021015050f180411190f0905180a030329030304050103 77
    0x2020700f140034442c40c80b0550b0f40c4001813280d6142c0c2811400035a022241180600494800605072980100525400b58405000700e950760000142283c031076480e5800041c0000081c407800801c02c4500500051500e0f241c1041d20405107036101c2d00c3d01541c68800c20241655000c501d05040d6003859a10141e0350b1800c1c00010090001150080c0d030041c50140c40748140c210551011450122804400020366144202502100c0030004d000e070100c0e010154080000348102000040e05210741801803c2c000c056a0309000c0b80c01c05c0341c0403204501302403c00c2c0241901080100d80e1144c3d0444140414600c041000b0501081403082c540520030703044584409603a0521038030401c60092051019504d020b007007039515041d1b9551000d001d82c0d400c403c260f41207400c0e1031000040e10f4002c09280490348c90003c10b5401480001e0542d03c000a00c40301145a4410610520035154020f69001c61319040804420f0030141041d0350840b00a40075601e01d4003561004015902202c50900b0002070004400030904 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 35479159 1250 35477909 35477941
    0x501090b0a020d110711190f03080307110105160e0310020f0301030b160f0e010c080c0f01050a0603020d0206030a110f0d1b170705040503070b190c020604060305 71
    0x91030100c03000100448100d070742d8050289038942e21414043c50380b000864503028400c03054080c041605070100381517503042c05640864041d00c6020444a429942d0784060024411500220307190103000003440152a400320031001e0603002100200071904040c4420030140c4800c448172400c0c02224080b42046070750612112446400c2088199039039614944080074550090000312281c003030840101d4134020300c0203012900420103440710817507042c103c482510030241d0303640003d042142c4503070101d00161000010b0050b105500c401400d00da091030030032034259940144024215842c1c0702040000d0f07510001a020340e250180d0320306659440c1c004191025021030040b60410880000700e00c12110702000081c0310580c0c1e0031000700824200c0384c503441c24050120905800060244044022041e00001c209801c04418200303d0318127a0380d500800d06040c05a44602c0e92804046050140e02d010101d03c02c03620711041c5013881c140f0040341d0019500c0d005600a2900b09035446001030134203009180c1d10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 35480409 1250 35479159 35479163
    0x60414030c030d09020a080a0b010b0c07050d030e0102010b030f07062d050a0201141b0a03090b0903070302060609070c12050c0307080405030d0c080d021c060f0608090a05060a09050109 81
    0x150741e0f90301d8515042c0e0082c01010800302d0040c003160200090b01f031400700e442e05040350f2200441809901c0d0101c104219048581c1c00341e4180901400041c1d1941d40260150b001442030311201d03002035140c000a801c5581d0341900501079008034108006d4413501180d1101650014204220507141a0907134541c0e101d80b502c444280404810300e181c42094000340904034022107a80203100c420380d00750840361034a206031440060210110310101c10540300c04013402c90f49285181c00110100c0c113480e540040107007594130300880c0d040000e4010505a041c0301180e8815170540c2c110b8000e08001800405150448002030300300d0300400041c5106070720450840d24001d800740304494982c000b50421505030b901a10600e482071190f100c901d600c0b64041c004c0310a2041e00002ca15040c5080e0380d113110082c0d402141c3c4c0e000e2008070301c4040b0b1000d00700c92041c2c2c0081d158400c070042005062081c00361024002402c00002039200f92541c00000d08001006544841100400300303a0171120b03c1d0040c091b100d6101c5c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 35481659 1250 35480409 35480413
    0x80c0a0305040302030717122101060504080706031b080402030f0312071e0906030f06091e0b06031005010c020a050603040605060f120307020402071b060905090c090102060414030c 79
    0x140034158414050300549008506852803142e9480d5501c0c03420841e603001d0350302904a282c008c10317900c0070364000d001c2c5442c0c4e6100c01800c2c00c3c0c1113010448488000d80010002c10400305040c407000b80c4c104a0900a4101c82c14200700c0c00f55009005060382800c000d40344100101e000c0001d0454405000c2c0140140952086a450f00d805500c40b41e00e4182c00c55401002035000149008880442c0d203805030a0141910341401ca242820b100310080c0814403251000300d52185400158580e0600c0340f80007140d08440e251494024891140c400d5820b0004aa07203e02010301c24440d082e00b004040c0003c540003401c0c0310309030001303a102062a054141e030000d80d204801204000c14000250000d030710800303040340c0f0741030380103564000c215408009022140a980c402d20504005043c00ea0050440b84d004079544645800400103445031000b181d040307400014807505081103181002540700790000c0000400760704082170040002c1d0740d00c500501c0074250b48a4844c49403640072080c022644040c0007241 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 35482909 1250 35481659 35481673
    0x206090a0305010c020c090c030604090606050d0606030b06010521060d12051207090f09020f04030c080f060109050f0c03060409020301020406090e010b12012606040b070305060d1509080c 82
    0x2c25a0080900760111005406040c003c41d03418030700411030302d1040f55808038603401c685071802404020900444102e5209644d10004603c0d5034a6000100e201442440086403650442c07034030900480010b000b403814031105106000489542022251416065514904103960741c040052a101a0b00c8000b078180c4440c4203081100584c05801044411300c041481d1219031210302c004c0340d844400d4810410000030030306060010118a030005e224058401441a04064503900c400502c440a0740c00506103a10580300110101c50600c034450041c000410100203510b403e602035268400e00810f1900c0000c8000300140f1159119400f814030290090003c54550781c8a10780604480d026001d5000b409070030400004c0c0c0c644905046030b40e25060154172a541e42d01c0c080a403013820583c0080924000f0640c101d0315071002c020000c1c1d61203140988607490b240d0404407400380031600043d000d98001c1442c0208800414000714000300c1c1603a50510001e40c0541904100540380507803a5483e5290040300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 35484159 1250 35482909 35482913
    0x15090d0804080c150a0e01030b12010608070602010b010c060504031206150905041b0f170c0414010c2105070503120103140318061317060912070314070206090a03 71
    0x3402900c15aa902d038100c501000c9500c2c2003001c026902c0004e070383c0e4800304004404405115110909a0410604020034210504c034000b5401c03110450701810313035030340d550020814184104103010040c10381e40001c01100324102c0009112080d55200906456261004030701014420007403140240f40030070301040501e44428078a800c480c150040580011141c52002c6007a150a110340141102d2400c0d0070426083d219905403442514071600c441071001c0001284400c40020300c100d84202042d041c403590b154101800000c040800404445c10041042d44d00c10004460080c82c880e0a848a00b4084040b41d50328401c5802c0c1c4201d100c01040c0b4040071994051440c0040302c01c5060724460086071800180c3c1c800410741c1c0c0d002d00101001000c01c0c2800c484014100080100001c80c18490701404c0c8039140d0024580d01c4100c040c086034164440030820030009004c1c0304860090b10b000c04141d203810804d40303005140c08a1220610103000e400140c401c21580c07050119000782c00050002001955a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 35485409 1250 35484159 35484173
    0x7030c020907090609050409080408030706020403020a1202060a030e0f0d0203030604060626070309020405090a020909030a020318041407120506090f01060e030f0613020103060f05030303040215090d 87
    0x86001280116051000b040c2090b010700c2450741a1084d6582d0010050718241c1004040c0401040a882d445030030040412039601c280000e0200c1d50141d100076a50300d24510505c111882658802180190080e55402c01603071840d08031000101549008a0040c41c820341040c24800c24212401c0580304400000d00c1d025008401b0354460300c0129005c20200e0303552001540c00e0000444407015504006841c0c104074101003407241d40000040c034001030400c880354041000c580d81911810b0300c1c0c0d840307200e0000852511505c503561002e65000039504124801c84003958900a82c103540108a80c00516410251605e600070410240c405900c40018100400d01070304081c0f8110030a15054240400520581071401e180b5003c1c02c2d19480003d4180c0c41c200d004c0346d0203005801c01c10b5060150300c08500c009241003120714060004806080c44040b901d10004d8119806a840701151580007031040102e41e401206886d4001d405035042e48000103560640c07034480c441d0800281e0f000c400350518800b44465 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 35486659 1250 35485409 35485427
    0xe101a0a0303020307020d05070306060e15010c02090112020f040903030203070f0f08040b060105071b05011106060a0308030601050c03030109021e0306030601030620030a0f0c080c1603140703 84
    0x14118024015490203115244403203000c0600580d004000303460040c2880f2481d49103450140042c1c645054172a81e61009649580c1e00c02c0c28400d8540c8244501700c0380401c156145840c0900340051005016408a10002014441c9201c40302e459445681592079122141c240307004010810030a81c05681f801400070b40080d10441e00103120145a180000d01440c44409581410344507219155266038406040d030130000c003010704101e000e1287d10001a181c0405120240b42003c8101d0050300b8180014402044928400c0b09903110b4414400c2035154400c05c0c1041e03c1e0007042463360303a52a10016155032142c1d0240400710b11000000050b4050240e014001400c46491010860000108540114013041c0c07901903154000000410015259603c1040c10148908841d000f0241da043d0021285c0c03c100c54186010b5100c22060110107400e00c90b03401c81c01c006092004060a100d07101a000d4007901c800c8000c4408032030804400c0c10b00803406401ca5480901d00d06a5504007881d005000d03001e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 35487909 1250 35486659 35486681
    0x3d110c010c020f060a020310090915050a060b0403080307020c03060403020c03060609160809010b0d230604050d030207110405041203050708011203140f0724020313020111010e10 78
    0x4030307050107400341c1480881d0080d10019818000d20098032101c420000962000d0115000c8180070500020031100c6409031465107400f070200401013400b40c801c8002640e40c01008124114903040f014401c0380d58080a4406803600500e4041d00e95039008802e03450404441d0103c0d6240c07158004205c20540e00058850400038150141c5006441d80c5040c04030115090354071082e50100c084915099521441c681c542c0002041c0c00854060119804104180c0c00600240c0306044c42d600080e4801201d6031242642c5a0301d140102954503007130b2a034a4a03229504940410990001208410b01616000c0804c003035000420401003410145011021003005842d8000800d0402c0002000c8901602445040f030b10510300318100e01c1904e0313408407640001001d00d4610701505202e094801d04c800c0c0081c0880074070400e00f2600403c0002c0071700762040303100d066030743d820350040003003041010750301150140702903080c240b1240c00940d581442c0c0c0075014100380c5181600c12044104000304080c0c000e9680d100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 35489159 1250 35487909 35487911
    0x30312010b0301062d080916080d0305010f0b220302090703020306010f090302010207170a0611130e0c0d0f0209151306020703110607050f0706030603060c023d110c01 73
    0x7455a4681680030846280b0001c4031726645a110341c6805000019031001d0f10000f038900300610b40e2000e6084034420740210381140c1c4003641080d00c10b50984241070140c101c01450180441c07030400c2110f5035200e40c4504c150400300c0f205051880417904400311002d50340c018881c400a14080d10010000e4004a071440e0015601c00c101c8504103015901c24000d403030301a800f40c2006800c03d808110000c40d00d103c1d20483d8454a17080c0004111749105880401000420030341ea2000101c0e030200280308150002c50601d4070007002e00902e1200c0c079088030340254503c00041039801d0116011303c024015000c0e00303a0440000c841200b181c10b0110003d01d000754401c40b1080c0711545401c0c08a80da64200d000062061041603a00102e0745404406007030303c24440d008980400444808481c2410410380c03002022984a242c28402c006040c020400710319002e100904c0764880300d00e00d202090b94030070f10321840d1030102c0c000d400d043d02040c00d2507025500c1d0070b0000e002905101504c00c03115803240d1450b007000c2d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 35490409 1250 35489159 35489177
    0x703020c09060612040605070c0606080105011403031305010e06040e0a0c030f0903020604080304050a1208010302090c0c030a030b01090f03030801050306060d031d040603020d0615060e060706020306030312010b030106 95
    0x9450401d0613a801c468800b480d401c2a50341ea80c2c4d81030020b0001416000610100d404074038001902400340d28040c204000010856504d45600c02480d10030380403009110707402c02d0080045e040c01c3c10351680c0450b071003407a00007030243c1d0388004101c481c42607801c49080135190380100444514190058541d21500303540410245c0c40c0e200340b040c111040803a00800503001400410b006c1840c61000c0d58105014109036460480720b070ba42e4501460307200b0f26090100c0c0700d40c80104190320302031644652104002006078640300250030999164450207038030105040e5115400400fa034441d00b41c081c058142c07910f44850442c0c0f01e00300a4010242445901c1c440d00c1a02e00045841c1810350708030718641d61588816070713403103440d42c0c0040103441c1040d625030f00b00f5910400000941d8604142501d424042e44000596000d00220700b1340308e031007541080f001c2c051040d540a8180e25a01e04403030186421180040c2ca0f0307150400041d046102d8142842c084000d002d0002c00c02160034801503040310015111400e1b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 35491659 1250 35490409 35490421
    0x4050915060102191502090301020c100e0a170a03150f17070617150a1d090a0b0601051c020301030309051002010b060403110111120c0d080609041101050f0703020c09 73
    0xa01c4035142000340e0101c6904d050440040c036410480440d2a80c4003902500340f10410300401d08a0b0056462030340c0a606c10754014400c1e01e400e110300c01c0c0021805018003c40b5001ea00c0340c40019001c100388420340c0000050382922a4401d621124040c0d100e030518031036003581d600700001c1d541541e0041d01180c12010340500c000c0382000400034200c03446034545a080c03002c1500d04620043c002131084110708040032401d00c4950302e41d5402c2c0080c0800c00300070688011241d1107801c6034800281a030b6082c1d407207007581d00c001c115000b8080740c1c00542440c00c0e694600d0464003200403403082c108601d03210b074000700c0040b04054000607442c0c00e580040e10f01c01c2c015110b40c48124262804c0c103040d0360300003100300014030204550050991041106040c9a2820034800012501d4283e0f07014603211301c08404a500d500c80c1000348070160180646140400f11801d0120011307007042c5002e00010301c101d41d21500c052587c4d000341c00340e494cc1d4508811b1103844103c43d040182d00c800007995100c0c46000c0c51400a99 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 35492909 1250 35491659 35491663
    0x14120423010b10091406160503030403020120070b040209060406030f110103111305040f020702030604030804060e0a02030c040c11030406210e030919170703120201050c2704050915060102 82
    0xc100c1707901c0c2408024180c000300a00003958032020040f046040c5c040d2013000844d5003080114001e61095000203414182004140c1c4805d80364114411140350400049010841c1024404d070860380481b072054060322500001402818140e00003000021188804018086aa60310301680f020a072022310010029078600307903c3d8400c0f408004060720130781d60248034500741940b101320b4134404884010700c2c2400d02d07000139142a104880c12400152003100300020003041c1e01900310070b41003040040111154603800251142034a0915034007d5540b0410050705c00d21901106054889007019030340e8441c2c840d28003d1105c0a00c6d1051010541d40580d524903854643c45901013101a50002e14103101c010005c224a0380da64407081c0b25070004244011070803c20280c26200ca2542817801451084d1540c40e216000e0410840c6003419a49800104074280b18203900320349034484041102c00040d0210080501c4000240a11f0340d00545010704018040d040018840303026103529024034141d0350313603000481e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 35494159 1250 35492909 35492927
    0x105030106080f060d06110c0c0306010b04030303090f080a051b1f0c120c0201060602010b030102130b07080f130302190f06120e030c0705090714120423010b10 70
    0x10000a00000000741c220f038082d078034260011401000300000514a4031350001b5180b018805044503000003030303401ca40c01c4080110210148095000c1d021542c94045100107502aa20003d0b00f81a03e03201c1800c1042804000b503244260320040240c0c542c811000001d100740c024002d405110901a5860b540b0a180010710072001c03002550200c900d00d180d00403620280800181c22000d0025002800d2011680d41c01b441c2c501e82c1c040d50001410b2440e0a10003401e4400c1c0504050080e44104484982c501c0c00204005c16520100141c071303665030903854210014452400340000056020480c4040a02c3c1d0344409001c9070f000321342139079490200c1442030100c00a240702d1941c0e9601c4403e010000c0c3d500a0fa1000446021444002007040080c0003941c1550701080070007503d5040b06c8014403c0d49407100d0300b1a00884070b4585107494551050700340d40360f849458a40540b401c962000202003103240d400b00031202e14580042d50003610ba04500314040c0000300d24040c41002c02c01210040b640c0700c0c1c8480 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 35495409 1250 35494159 35494169
    0xa0803040807050f030312070f030f060f06030902031018060b01050c0d030b1c060606031401060c030318020d1121030415090305030a09060201060b0703020c040f020c01150503060601050301 83
    0x41c01d0864034000c10040313420801440d841c2c060006000614240c041c07141480e02c42c0d0001c3c0ca503251003080d41c200003006c880d000040d00400626041040c070505004081d6201a00c0444c1800282610302e800000e1030b018404290724000c5043c10441d60221010341d90040c00341d4402d02e001c1c07200000750b030300644485c0120701d042e00244d40221b5880001c90f1007500043d191000c0503103050403010002d4402150501d00c8401603400c161585030822501c1d0b41442991410007000304550034031b5040c180d006000008281c0064209070b00d41e101d12003201c01506405a007180e00601e80001401e0b50700e07158035885226810503124011110065000c546002580f24041b407108000d5441c0c00d0401c21038014602c428942c1c07004000d500140031000031000c0008055142464075009030316854918000c3c03d403001c2e40c0016400c0710050000f6400660005118280a003088402055075801038039584000c2c0921000d2111035801c003000070104051280c80d02c0c05030703a0141c0507100903a4424006450900c401c0c864 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 35496659 1250 35495409 35495413
    0x20d0801030b070305060a0512160504050708040f1e05010c081b12100305030304080d06050109051503280207050c12030306010c030507020603040b33060a03020c07030503030103020a08030408 84
    0x40c80192181d4081540210018154247d2076100c001040701c0482c0042054090784c0030300c44203405050404c0702c40700201004c41c0d00340000d28004100906000000d0001041a00e0528910007003114030400a0013800c3c4a4034102c00b080e0244c1000d034003a000420400300419a10340200340ca010681b51100c0c03002c0401c2000524000e0b00d40c0c0c4501d80458010312965210b004084040001401030004501550080e118940c40d0707201c3e94012412140d03e0384c049410f100c068213041180b520303030080601c000014060003d4a1b546c401d0050211015821100c0f4000300184c89400103a135581c0e03001d00f0080780038004a0b030880d030541c400d101e00840c608001541e0707a80103000003000341d88143c00d0360000303500c40d240890902c0d905502040d21500259401c460713400d0f819040155040809220310713070110000d0a00700340d82c503a080903082c50031820070116000f1072000400c8001a4000d80460780c5040340c2c241140e4002d175413410150303166002800120311a060f098400200d064000082d5000d480c01040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 35497909 1250 35496659 35496661
    0x501140106110607050a0e22022106010e0409031106012c0c18061c06050112150302011407020d0c1403030408030a050304060b040903170604090c1e081204030201020d0801030b 77
    0x1005480b616111600c260380003051903190241c03041c0c02c00000c0e6061240d450701589544040090300ac41160400040300d0000b140420000c49070b07440b112030200c615040e600003810101da41012500c103840c140c0307a403100388580c000028a0040d07040300d00704c4100c2e850014002c000403d11080107841c10039204220450424002d901c42507980c02da09000c9020700034041c500c0c10350139119440380310466042d82101b141d5144010851940c00994071540303030342601000c100a40080d4a1312846181c540400ba04108140c084050003120700c0041307808881d001001c1c88441c40092426100f40c805038000c1070002d032400340d19103505080001c1510f09480114002e14102401404120b80d0b54000800036a07102d0380f01c3c0000c9100d40c0700c174030030f0b00d1240e400303503452024814000c032608160b1100504160f010303900d04640c1d60080b8180c0c0c1550382c141d680c808450250100201ca010303190380c50070307084901d0900136003440c0204c0440540062013204d10070b80035126604070152054910000034071001c0e101006006c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 35499159 1250 35497909 35497927
    0xf0c010c080a03060509041203110f0313030e12010905070e0f0411030709090302030705010b01050c0309040f14091606080f01090e120d0b0f090601020703020607060207050114010611060705 83
    0x781c06400084214a030002c4c8955440380012041c0300c0541c1c090300c0c0b610b00401e0800407181d0501640c1e030f618249121251410a01604040551100501c2c1203450002c15401004041c0b00308010740741d50703000500c0d0300301001003820103500070031003810201d566115000f00010700c040b00900d903d00c201104203101c0c2d42a5510707254081c0c0842444880c540c50300498101140f0b0394218404c107401c25004c0d42c011a21003c80c2d1506a084444003015075041c810180003501d0744c0100001242e050b6502903401007012042c1554180180590800132b40306100075004000d011500010742048070301805808400c019038980302030314a4007054400c2844600e1703520060101040c10340003810060692021960812109004591141c00c10350341080c169448038502e00c690b1400322981c4a271801c1c12640c0340002d080c0140003035511007403840000c0c01020013003400c0041c0b04055060750743d03541c0c010000b0700045060180340ca8160b07200340a0000401d5148244070090f040003c0c542d03118584130303242c4514203a500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 35500409 1250 35499159 35499173
    0xf03010b0105030612010912030903110109020a1e05090406050402030d110705011b05010e0102030a150503150712060623030f06091b0d020702040605010c0302031e04050303070f03020f0c010c 84
    0xc000d40166036403071f622504005811000d0700d100b00d00c07503a40c4c000b40620302440d00629034020010000d21030381c107044480001d80e558000400442e12184914043e0300c400345c0b0700550182c80e59111f01c0d4010000780c1000180403098010b58071441c4203d0035229030490b00001a1840700d07020203945450b911081c2c042c01254000c20000001c00380b0383e01c2c49003861607247d64407820750703442114a2803265000b01c24000a81000d0040d42510301888000d0000e81d0b081001280d074545980110201c2c074011200030400d002e0141c28810a0300856540910401e0b4684401510500300e0b450030740042c50a1024216000c0750440c02c0d05e0040002c191054501c1c1c8a0004004a111010709142441034140203489940c0301101c0040c9040006183c0c0513032901c8290040000f2905543c0c0542d05000030b940074880002c0d4040704803001c480e0590011544a9903200000303240e4020317600683c0d09440000340c8817091041049001c0c500600c281d00300d41d0000003d04990751a03201c1c0401c11404104003030070840028000b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 35501659 1250 35500409 35500429
    0x306020702060d230903070f1203020f0a0305010305070b180108040203030d0f0504050705100503010b0309100c08060a0503030f070807020303090a0b071a01060c0303020904060905150f03010b01050306 88
    0x20811400c0004810f00320341103402c0900b03115255240302d40504043c8039501a8680c5c800220300c00b440c2482519220b0a000030100c00c4001c00e140d03035004480742c000b4040d9042c1c1703a01c020f002d01341c50340703803071150901030014030b400c0c0400c0e1240d1050b90000a0f20000e407108641100003029040003404404d0300055400b44800f80c003c0f0b0340b40c0414007810141f01150321031014061075503280410b941c20036007032980c24826613400c20b5001e12818141030f14102d4000b070880741181c844002c0a03079640e582c0e2403045d0800d28090098443c4c18100243c22205590251245008820444e0600740c460ba84404050b0b80741710340382c10450601010f1195001240ac81000342c55858000b030b00780e07494010710740002130500c0703441c0e046240011004070392035050080100c9140d00613000b045442c6e01550420f9000b605150003407100504054002400c064162110313000000104240300007403000d0304000c41111000000c54190500410100724155000d00e814002d19403c1320f0103842d11032075600d4200c203004160714 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 35502909 1250 35501659 35501663
    0x304111002070b0309030403020f1c290c04060e0a080715030906060f03050f01050f0609070c061a040b09060d060506030a0b0c090a140108010e0702120d0e0c060a0903060207 76
    0x82c0780400140c2d03e041c1801540f03d040b4001c065559a4290301c100118645407200c00e40c0a0210414004400310b018140c848142d41c00250314041e10001503c0c0500101140800c0c203004101181801900c003139601c040d00070381c0e41d1178803090a081e01c0030080c8100085144903003041640055270400c0711a41d40048112129224500420190308546a80080e00d015500629414a40ca07a0030418040240414054400303564002d100c242070628401c0b1682801500b0540304000c4035010410442c080d0151200640d841001440b0140040580c00c0d140f900f05241940668100021a00070340340503010203101e260002e1007140c010b5030303544400380200402004240c0520560340041c0100e25101080c602c90031441050540c1c0b541c1c2c00b4240404082140d100e151182003010805802d41c0c1c02c0341503641583c080304c0c0e159a155440704d8003240703040c030101401c10301c2c01c4000540c500d0442e441d4210054000840040350607040708001888000d129509040c40020994002072001440300c0d001001154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 35504159 1250 35502909 35502913
    0x1030c0809060f10030f0c0302040b0a1a0f0c0d0306030308060a06021b06070c030606090b04060815040507170c091005030a1b0905012306030702100b12030c0f0c03030304111002 78
    0x144d260f58440c1e003060031b0a0340a0380c424091800170411440d25024855a101e41a00c110b1901c0d854a1051402410098802a0b0101c004501b006903940d80106a400340400304044810300c05012002074010b00281c001640050100707130020301c05040c0200180e00311200341d40104001940c201c1500c8645203030351b050b80e610010402002c0041450449104060b40c0103000000d00c044c64410400110340c9610b800f640580d04240c3d00300042000410912180d000150320b1074110342c0d40b490403c0c140070154221803030700c0349115a010030713800b00001c0020904405940f11185030311280780751030301210948038080d416440160801c001078000d038074501d1101202c9140a4101c0d80b907180c45400c0e02d000740c00c0300c10102501001c45020a554003d00d1085101c1038904d030703145007000d16000303468000001c007070021280c41c0c000468464071a912142040a000c00c02d80352503000c40740040b52a05620f100b06031882c80b498420b80c07500d203404000ca900959001c1e03000a020034071031091000102d800c8206500754 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 35505409 1250 35504159 35504191
    0x8070203030c0609010606021b061303061d010e01020c1f060906060e01021b0a14060d02030702060403180501090e0411040603050d1b081b030706090309030201030c0809060f 76
    0x1038400700301612480b450840a04510301c0d00030324407421209690320140c02c543c010101140c401c101c0c00c0311040136007801e80704070780d4903c0c00260070030399212260300c0100618500100244d070318080d40c2c13688843d0f1003048028051440001c90b110f00b41e020745044004650824140aa656111048811b14003c22540042000c03a52201d204045814691008000c19002c0d01c5029066034140000070804c250b000f117a8404e109107001040341210070b030055460301d070100c07428802c1c10358031841a01e0341c40d02d40c540c2c25940d0385454103009449400590303084002ca5422038402922840f07034250903081e2035042c0c0d296000c0900c1d0042111849001800c1030312414010900c1b04c1040d01c95004031f501441c050401031000d00ca01c040b00811084214650341400036041101d240051440790444558001c82881d54450007401124181903101c4c0d880002c080c21316210340724080541006001048038005d0700c0c1040800340e1024140c4482204413100d41c032540042c40060304d00c040e0840c023140c01c610242c0140c580 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 35506659 1250 35505409 35505413
    0x3031f0e01122405070e060307080a020c01090b0c12010b0a0210020a120911010f030218040906061d0a050a050103080a0c051c0210150b04090b010203090d060209010e19030f0807 78
    0x11401000d10a1481c1d45420410189a40201d407500519201f507801e80d2452801e0710004080780e0303000d803060103200d4001401c04240c1100350032044c80203800844142c020b09041c1c4613000e155000001e4030307102d01805000000c0045032801503401c1c00b401a0042c2007801e402943c0700c0d00a40c400700b03180301841341603450480c1300700c0b45202d030b001010721540011425040410001d84500452090403003010b00400c003200c4603076901078489100c030f10141c502003204070700ca10b015000f6100c3c68100f550000b4203110000c42103014030001074020341c259001080b82e503c90a0602003652400d000140802c0c4041000310a4684240d02500c2c4075030080050700c211800c80c3c00f002d0144c0c01d88042d0030b00117074040540e0b000c1310320507440f8440080300c0c2e50361030b541606e280081300a0300c0d006501c540f00d100755845000c8607640e4002d00469221600091440040720140d190040003904440c1c0305d20b000900381c440c41c82c0503042c0000b40324450549001810700082c5140d98810815a15000490b4521070030700c18400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 35507909 1250 35506659 35506703
    0x40201091a0702010806030d0c0305030c041a0301030c0602191112010501090209030f0a120807021204060c0b150105090d030c020405070201020a02210f03060102011d03031f0e0112 79
    0x1414001d81c0d001c540d920b000d030000500c9081c014110603c00d0300002485a038454019039100f8210b81d05003082c944039a00d90b40c100009002c3c651018140400071070a0204481643e80214180d074407030741078120559100e4104a0f40c48814280c0300030141c02204466003c40e440c0c0ba1580d49005000b09a24142c000d00101035003541c0080c3e000111190300418802c050b441c05002c40328404521100814850300b05480c0c40305441c59814010301408000030200d000e40b032017440070200251401c0d44460743e8558583c0002c080d9154040140d075a00b0030100440c1c006060540c1070b00d80060305075202802c0140120800030448464a0200d050210041000c0300684aa009051294810342c0006845815280d80a81401074808058918611040f91141100c4400e82514030345101410000c0d103e0345c43d040140d004002c2c58142e45600084a076041c80780b0b10000009501c141c07000525541400d19003a1505580c000c3d50103413014000e805001800340e4428403048081c00b90260820303040c25841c81c02214 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 35509159 1250 35507909 35507939
    0x3070306060f1403030307050c0a0b090d121506050d02070506040b09060c030702120306040b190306110901020a060506030129041a0d02150903030a03021308150103030804020109 78
    0x4401a072140001c004102c64090428002c16070400809007500c8248000b940340e102c01042d01046c404e0100720b442c1541810069a4804c0703500090294660501d4042a40c0e10b42102c500007001509051640622208600030200540f10b4640102c55107401c00c0000d0b501a005124481d0704c445d07007444514080381d42000b03042e00642c0520341d00c08503070910110351810305034004c2c88040035110400500501990008090000034107071000642c480d04c40e5000200900703407003201c842e030100340e21804100c0c400260802c1c1c01128420a0100500040c41d00015180e000b03040e0f5590150700038034003002c0440d80d01d41109078007c000600002c1d009080f49008089400030341004492201007503201c01d1070741001e10400c03003c1120480991550300c0004002007580420340c200034000c1a40c0a07448444030b080030305503000781c3da004003960346499086d60300030001d4110041c000014811001700048079000401c0082c3c140c14200300510309a070030b60b14141c84c40340000d0030484c1089800b03400014500075120040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 35510409 1250 35509159 35509163
    0x30a020d0516121104050601090e040807060614040e0d1202180a0b040801050604020306132c01090c0510050403080c030f040603050403030b01031b1218050607020f03040803030601050309010b030703 87
    0x38a1083d01d003414105090742442c2501c60242e85040e060210aa8004520804031a050440305215558910741030155020b022001002c0364200540462035081102d0b10301c2080c0c4040da0104003c45203054a039a03144503014100020840c05e480034030401c03c50350020000b254002240d41800400c10b0b01084d100b5220b83d2142d41c1c070b00804035007404081c00031b010b400c0e0880c0040300c0a50450a11302c0004819582200709407256603078400414004a442c0f000c1d241505503c01c4441c42aa00032070a41030182000c1d14040301c0c5810a01c01c00f08691400fa03120030149000f51361081e041c0790a5a40700390483d48040003040e520700c418461000d0f40c082000050020b4002d65070046070383e08007443c010b800d590241010a0602d424019480040c440d40540385104803c50301d030503000456920b01ca000240500014400100301040c0e0b80c6050000006203107005441079801c440303d501e031621b00c0b2601d0340600d010b15543c580041012076410341c4100095600166400000900f0030030004c0028901441a030007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 35511659 1250 35510409 35510429
    0x301141f03020a0221041a04080c01051606090c081203090a0308100b0d0603030f0e1005030714040e010f0503060708070e0609060a0e1302091f0c0b090102090405070905030a020d0516 80
    0x414003880301101d9050700c0d84c2800c1281e42303003040d04107981552120b442410b25810001d0101c0c21001040c00c801c0c41403007840c4c101c182000381c01c0315420547c542010502507001144079095271820301d0902002142d10590022020303000c10130039540c003110030761030203000c000c00060009404605000c00702c00800510360480c0d0001a07040c40c510740078101154000c00e500c01e01050400301c6005484072100b105049a8520340207a4940d18440300b076030200b00500b00c545034410081004511030504000c080c0c10303503420003a140e0701c003076076802096601d01044503004000b42d061404a4039150107900000c60490000b0901400d04007141d0109141f038000120340d500142840c6c810311860305103d9144c00200d000c2d031006500d050391070004513818110703c284c0100381e0401c41d00c0d91051244141c84003a0101d900007060340080c100804581d001c0d42200d40110302c103501e400045000640281c000c44106e400140140861070200e400b0051103009210094500740200d4003143d050b98035203030040000d4000a55 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 35512909 1250 35511659 35511667
    0x50f1f0302120708040b040605070207090606030b130225060b09040f0c05090903041a07020a030b010906090b0f0d06111b0606030a170703030f0c050301141f03020a0221 74
    0xb600301c0102009032049050000c2c29042c4000f00300c400300c559601940203d004a85500d0750341049103011007551041881c5490140003040d626410b4101414111003240e10100380c20044035800300704d124914000424180c104100d082c07800c6802d020078980c40c007800c400500720341660007180c0280c0c4229411100521248a0b420400129020007405041c05644102c0c00f4580b8080d000d550b41304902403500b0511f2103916600b40041d86808540343c055002d080c0580f099aa45070444446a0a01802020030b00744040400c442c3d03501c3c880c1440058000302300c8144800b0030028881e0b0082c0c02c0f2030580f001601e8104000740000c00b00c2c0107001c481020341c126414442804032040c10b020300540a80d100c2e410040c02c25022405080304074400e5624031060658660061406800510100700030045039030402c01c030720040d1600140030358100c49880e080350510340d9036042000f604009901c08401d50a080ea600c000000f4800c0d40a8003200c1d10900480f19190a901050b0740507054000310321305440030001d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 35514159 1250 35512909 35512927
    0xb0108010509010509250503193509010c0204061806080c03030301051909060305150c0702090a050a0906060b07021005030121020103110c0601030c05010207060207050f1f0302 77
    0x1205141d0b00c144810000c10060502d040043e44036040c41043e941c210703091540e80c804840d441c2d22250010040101164410502a040b2070310f404805a015145903403954014201d0680b005070710107030810040103e2a540e1101c190510598000204040c100418018480010b8980740b2600000e82200202e0134080c521002d01a404d81d0316682000406400c00c0d803a24840d0b4078004241c3c3d05440046401003103021000b14031038000c0d05281d01c03030b18050b07041000c000240140421481e085a00c01c5992102030750fa04001c0000301c0c480c42000940006410001071700e201c3c00c590003a40c00594403d400701e098100ca40b41e0205488840d040301c2c0055100184034006c600e031403071034140750b9400d600349681158075010505100000140300302c0140c000c184514811a1320940c04500c000a0038218261155803c07501c46995407401d01088a850402c25000b103072075800000c04c0d07802c84480c0d074028541c10b0304010620841e20704000803550000e0b420003a072440039402000000b119009642d00580300e60703031a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 35515409 1250 35514159 35514161
    0x30c0b0315120a0605090703020a0515070f0606050306070c08071101110a0308011e08100b04090609120905041e0b03010906050702150f0106080a0e0a050601080304050a0b1216020304050604030b010801 88
    0x1420200440c6d07c5070070100010b86801da0381d441200d000701c550900c466144030ba00d141c18454080020042d203da01000020003403240d100c00b096807404d8044500c9503650309000c1e91081685100500401c00038048030000510f1113440008039007040c94160203140b6042c01c5185444100d050031000306510710010702140403511652007050340784083d1002240d01d0640c500c0d88031900300103140003482d101e1840611580711900403039000c80d8400340c02c01044040f0304050003c0030800c0c1c8400005030310610009107624150041451150001e910400e140c0380c0c2031242d2000b4814070020726059502d442110b40070079603c0c42030078840d406a4020746400d070020806e294004800a0181c09904d00302c1005000703042e844100380c0d6000d0699440092210100010540303803841103c001019442054000b144d00756021004c1c008540f001d4484c01c080d213880d14028413040c091400240381446c0c50400241803100a928900200700450058900d01034803040481c0c401d50107074200361404115200100320064003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 35516659 1250 35515409 35515411
    0x30a090e060316060c1a0a020405010206150a17150405071e060507080a11060114040e01330308030c0912011803260405010903030501050901030c0b0315120a0605 71
    0x1100034103400100c240c1100804401e078041c00c4c042160460a100030084004144584602c940f140c3e159903152050140001e94000d0090134018028040032409182119140d428030210090420006a00b01500407500e101c5480d0044c0d103a100d5044d80d00c03241c4807030031410f9004500540c042d08100d82040c04507040a1844210f42010b0120502c041240c0b45d070250544808a500a06155951808000c2100e540c1c000d0305411809000743c0d400000c0540350814503990540041d582440f101301100195400c80300d0140a01c064000416281d00e0f24178111001c5220000158106684181e1280c44144558108440003004003600060280c0c240c0391038600841c881c20707018000e0102c0c40030f45416080a410b101001810707c000d400900070140c0c0e1140581c205144c10281014041c9800d040403070103000c050405402207880c2c000041761905256024078140c98208820080c560700d040700c80000c07544010001c200b5050356100030b40d0207036900107400c1c0c0080d2100004202c1d84000382051030465030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 35517909 1250 35516659 35516671
    0x50a0501050f04090b01110f07050102100e030403110418050c0f04020c031206010306051203030117060f0112080d060b0901120c0e0d050c0405010e04060b0d0b0604020a0e03030a090e 80
    0x15080c442e0402d01c9541d242258252074600c0c0e4086550b02d044401618044070001108000340112841c03200a5100014510200c4e80c090f400c03500500c4c00d202c1c40101711210f065440c0309170b401c200030520205005000ca0041d030304001e0000542c048202c05c1e041e0030074030b480c0d804950540021829081920742605d000b03500c49011681186810709a0312800d98074070a40d000f207041c000401c1c00190060b070185d03002c180182000303014221008070b0300421640f42d40c0240a942c0b682c4544c544c3c500b862010010302544a0f071880c00b80d0841c10390920942d140342c00f1001c1d508480e4040b08102000c901c2c2e25500800e0000c080859610742c0b00c000000c0090302008000c0500c0c000da6103883c510686c00355104440610000054840c0c960101c100e0901c142800542d00c5500e802ca81804000100c00a400c1d410b24402e03401101c08000c0c2c001e161003005014601514068060103d10022455619295000301071000c00c03400c1070351301c00b007843c40801e0a580107034126101085407410100000030140c040306034450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 35519159 1250 35517909 35517917
    0x12030115020f0d0804030c020315090708160311010804060e10051e07020627060702030405130b01020606010e060d09030809010c02010603020306270307060b0a090902150307050d02030f01050a0501 86
    0xb8030b03682c3d00180105401000a000c00299a43c841e00350b407414020b00d549448240311510440c079102242a5460a03548210003451227007d8001000c09440c00c024001e03283d01c500c0c220b4009502800445920a01500c1640d0541d95148001408c01007040101030800000c40e000c1403d180000c01d40100d524809400280142c0c1a0b080000c030381d03804100315a0000120645000401980340a00701d0039141c800f000c10188503403400c1c0f0403019000409403007103a100b25102c40004960244003005d850f481d0842c980980d1289003c95031540c01203201c100c0402010b0510380c10304100540c41400d43e0300350581a8080307140101803080c912400e018901a0070390320b0000740a40307482c5d0350121b5a501001880604a130f603070343c03100482501c2146500d001141060084030385455440c104000240001c1451503c0b640b2242d6002841c09000e0165072442c9030001d12541034460032022084007940b000f4001010003604001c0f00c20550303030324409140520200c00c281001c660410701800300da10b0701904140e041c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 35520409 1250 35519159 35519173
    0x9050609030a12030207050f01091b0e13060905060406090209010b040b09120307140c030607030b010c030c030e0a09050f010b0705061311060f0c0606010905030709020c12030115020f 80
    0x203440000b844900b280e40098511020800742e5400c41c0240aa81001040c41c003032000e40b10b4905205411402035917000e81490310342c07104d010795501c02c43c1c6503030310136410318082040005100220001e05441003d01070b5502049142075541c8443c103200f402c540454100349d0394075124040d41006240b2038090103489103018034042c00e200d544c4109000c0c0d050854800e950348103d4031901d034001d1059178001d90380210261405165144416200d1194240b0b2078000c0c42048002a10325201c0d01407601f80d030b08181c66064203d0210348003141c00c02890441034081c4400d5081040058503180380d5030006201c00c802c0000d9608001224411804040e840b81c0341d410f00501580011510110300c2c1a0040c3c04074900203000700b8180b6080302001340c11030b480341d8051000f150000384c2da06020b00400940c46000300b03640b540c0d9107200040d240d0b18100e01130711b501540310001c00d00410505030700900b60340090408039941c020341e810b0151801d501c241c0141d42d41e03034500c02018445c1501000520f00702805500034210b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 35521659 1250 35520409 35520427
    0x708130f0b0d0f02090307030305030103110603040b010506031003141e0a05120715050a02070201030f0c08130c090507020a0c06050a05092b0c06090509090d050309101b090506 77
    0x700c0c2c0101c2c00046551540c4080c881c0603440c0c143d04442d1600c0c030140541e00c3d52541ca06001e043d0703070024801501c0c911103010b5001414580007040f240b14550010b01c0345016400c2c070061003515040103142d8203240b404040040041f82ca00c10b145000300c14268000c200030002103040b034081c0c00440c2641100d0781d100c0000503000610102c2c0681f9902c0c8010700700760301c2c0c292600b8801c244402c1401d007403111500c0d12051007061031464000b012100d0003a2810301a4807200071000c03040310303281500e407000140d40300041484407607503000c041c10960154034480b8503a07842d5007041041f1070054404001507408020800108140300142e0001440c02e07003002e60508580500103801071040201051050000f20a00b440c40140070581c0d140000006400c1c0740d910f805490102c07504a07c0d8090400440c3c00b0110003e0303035140401040348a01c1040000d801c80d00794080c026512504003502010042c01044e101070980c081070320071494180311a0400c508185a0302c3d00141507001c3d10b41040d8000e600c10400106 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 35522909 1250 35521659 35521679
    0x170706090f0504050405030d0504050a060617070302040e0a02180402090c1201090903050d0c120b04020c0c0f0d02220f2705030d02040e090f0a0b07030507050f0708130f 74
    0x7007221000e41d004141070741d4514241e415442841c2140c1091780c5807909000070700200091300340105126010400449458044d1242035200043d0709550a17030151800780014206074121000e0103820301c0481d8621407190740040d501c081800054070000590380d0401065280c035140c940e0b08070140401040ca8188030950300101e20704140590501079450b211640b04140c40740c005c454140c8144da400b00050602c0045c014107804003000703480d40c59030800c542c1c000070b4038062080711180703800940204114105c00084c03102d030b4400d1040542e0711000c0900b040740540c41d00c9544c203a0215000841960166800151000f125402d840e0100750505c1e10800e100d08002c0129029811204003910300c106550a00d8000e01d5032080302200310b0b10500105002604003c642085800742d4420130a40340504440c0140704d41c5d4400c000006005500500003043d190f034001d5004c60b0300f0102d58607007145880309800031300000d5072041b04112403001000031903c0c0f40c0702c20000b10b00e010b003401c410103800191428115074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 35524159 1250 35522909 35522939
    0x20a0b0c07050d1413090b011202040b07020114090301020a050a0906080705070f050111190908010203040b01050d0609020d140609160611010603020d0501140c070803070309030c0c17070609 83
    0x1428420311070b205654052405080e20310b0694040c540c040e2064030383c3c0005001c3d00e10249008e0119020038003481c040300d200c1c002e440c152420503010909000958004403000000ca07000d66401c0325041002c08650345013070008040e0f0ba401601c40540d80e401c4114020951480c0303500903801c1045080c103101080340d000d802c1724030490300412000085035443c2050b0340101107c6288800550300000d51b86040602014049140a0309803a402c8546544070081c600b41d210460340100750301040e0006001758600b25041c4010b450091300d00040da0728595000ca00c0000c10710b5001e540c0303190f6240140324164400c115160307225000002a24547c42c030005150310850f521b0213408140144040f0b541c668a809510000003140c00604902c1d0043c15401e0160082002c07800e40d41000400200007400c005560007203d51040d804904a4619501c0342c50840081c0007036041241004480c002903008170b003c0003201c80103000c0e00b126a64801c4a0950400e242850950000c0d00b40700028404000d1444020821 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 35525409 1250 35524159 35524183
    0x1309050c0105031906170f070b071e0606030c0302041112160315170106080a0314030402011b061514030a061503120e0102010b0402121303030e030703020a0b0c0705 72
    0x21501da1311000c005020304004070085680700c03880c080d400a580c441d469202c20503003044200b038606440c441102107860340900e006182907480d003040344500244440c6030910f0700f000707102030101c3e4200d80759507080c06036003c43d0b205950142d174070300f018000d62a0621a5442c015a80200c041c6010706008811381c61a60003481103038095141d000b042d40090090304902405159800540ca0b4991110f60082e014080842140b80e1503103845404109443c0019a0b04151501612400007203075081d0340c03081c190f905c000e01c120b040058503007401e140030100b0360b16400390301e22800002c01e0210a00b0b5040103804901e03802104886c00e15618100103850200f0074646064000c00086118445480101c000d9040e99200130400c80c4054240c3d01e90701c0c0d104868234000c0c0d0090b4004e100712107a05003000f040e40120ae92020f12140e86ea0046800200c411501402c2e0510a040c045030304262000c000b41160012002503000d81c0240c500801000005190a03030b00c02ca0a41c481c03410040c898880c950b07240c0520f100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 35526659 1250 35525409 35525417
    0x6010e0103050a0b040c03050405010b04050403020307080f040e0c190807090302040b1507031107050303191206050301150302010210020f0415121a0306060301050c030a0b04060f0303020105061309050c01 89
    0x1091071101144c0204200d030001600c14841d842c40910024000d290445040c0e82a5203045900c402d285854040c0078000d035016030096052056230b031a1190103074400b04849440c176808100c000380849c900e042851264001d54651500e07009440741c0103440d540340c0d600340300030421040b080101694018101a0649406030fa0008160340c6002c0400c0400710a60344c2c2d06219000031a401e0105030303200d814500c00c20046070a0300c4490b642c4ea0701b41a502d0103480c030942d040c0d070f401e0b0502c80b04140c4030314104e00300507060001c085103071503442e00400c1c21545003c0b0b8400f005402d200041c004c1d941c04011219004068640440c500740c00700c108820b550140340610140100d40c19400c001c10f85c414550b284100342c0d10310040000520503400b591b0040c5030703030685500138000c020010b00980341c18403800e84110307400070402d40340d0380d140a80c550081540c40070942d48180d41305408a5100004015400914440e4000107200e042c40410000059800f81c04546000e04211150700011000315083e000c000d0f003828 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 35527909 1250 35526659 35526661
    0x30109110705031602120d020c01080405150a020d0c0216060c020a0902040f090b010507020a0501030c0207080105090601060201052503110702104a060705060108070305070603020306010e010305 85
    0x3420319184030700440904603200c00b094506030040071168881e1014400c56050204482011020b0346480b040b01c400f07009600998503001955000c0c103401d41e4828400d0b401d4074246103c118071407440e80c409581150a0590208000c910004203114883c203041143c0000e01e8400002c2442c0c150056071402413504003c0c41003100b000719203a801d6a42c0182c040e0100541d1100d84841201c0081403041c80b400d24407508001d620003c030b5004208a80d803054010b000c0c01d8065003040c1c0190050000c50401d2021481001c1c0001110b9901388079085c020120344002d0b204551601a000f82590781c007400745541e00c040041001c00204180324075034900307105410049103040f40c100d0070911034001e0351000794224201c4400c560708103078804110700b610807401c00201098007045d0413902c1034200c02005242c050000091100d81c81d07081040000b00c005004004919190141e41c42c1d80c01c141e000e03441652643e101d08030078001c1000c107028042c0544910700e421421850000002000b40007007445275410b0540e148 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 35529159 1250 35527909 35527931
    0xa0f06020f040b04030501140703020a120c0207210c081606080c040302151e0408070b0706020c0706170106031b0c050c03070b0702010806030a080403171201060903032003030109 78
    0x140c02d0314010100201a00e850701d0b924104140a400e50030051f60352082030400044d10f850092003aa44c2441301e5544260203a2003011406005016841400307040d0b120b501d100062917150610881a0582c0042a40a1080180ca031540707601c0c4083e0807012590b0000c5101240030201d024601084a00034504030302e443c1c464901d1121584500d41010350481c404820300c44c4003004007002401c0c009240d00e5400d560520b0120040e640b8080d078007815180742c0018800f0031001d074000c8090449607028070401880c0c042c075400010703c8c0441540c0801c0107d145510700e840e2200314030340018014440d83c1424091000d28516940d00060317046c940409100d480341c02e80041c80b00030000c0d21080800a42150040da480b0000207040e074020041c100c0c001088880040d005040218280352200d81c40040d00781000e0a6944921421055122400401c00c00784180003480240c200305900034003913a15449466410341c10300514041c00031004080c01c02000c500d00d000b0040001c222411a55031041c00030f451070280b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 35530409 1250 35529159 35529187
    0x50d08031b1b0613020102071203030f0212010501090608090a020907020f060f06030d0207120b07050c0a030801030204050903090f010e04021b010b0f011107050103050408070b130203010e0a0f0602 86
    0xa000d00700304000102d0064000103034090182c0c0b0455070441107481d6a030340e8911000341e071440400000d00603000700e64100080c0b0315200400100b58424100820007448203180035089800c849003c0000f90002c17001004556000345501001c0e01191501540d03e181c04201c0c2c641d42c94442d00000d004e00ba10350b000070800da00c2440388220750a060005e8601e40e003800203070311440f110709860591103400781081a080e81800082c000040740e80c0c0d4140b03101c1740040c07500c41c82c0500c00010300d85000d000080041d40f03d04001031102d03007012442078a80728401d50450051104031400144090301e154000c00000c545c598500c84061703140002460403001820003035010078003030b00a0300c41100310305030240c1e4420b003207141c10340104078001c0301a0751803800b414844004417501315650040b10540e8001120610665200b5041154040e00540585180494550b510603e07003604a0700d08150130319003100c413000c5240a0080030110074409008250895940d101c08405803140d03000200b40e180d0000e8000341542c1c0b9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 35531659 1250 35530409 35530441
    0x40f030306090207110f1206010e0702010b0303070c0e010b0c030d0506010212070b040b060306040b010b0915030708040308010b09063004030f030c080c0703050912061302040510050d0803 82
    0xc0210941d10380f8007a04d00310380b102106811080c07140c80c1c1082428424244140c0180c0d081da04207005148c0c40e4601041d0014002014100344219521511a90002d80b003c10090401d01d00c504801c80f8218604a2098041001031b0405005038104000b081d150110010a42e18001100305000030f45449000050386040150000200d11020200b40320050010441c0006e110700c1c003801460040da0b07076200800d030300d0700300032980107208050340d500501c441000600684031070342d40a0501ca80c4001c0f44500701d5681d41046502e280024a00c00801040582c4084124014018101d2903800c0c003c0d40d0000400740d0060490755000e041c15010003a00d42c0f014035641c110804654a00003031a4182401e00800d031494009004020034240708003030040600c1001145e00c51002c608040341845415030b822211a442044030300c0c1e01130082c209020b401c0c00d0500c9414043e4500c020b000c41807403e00e10501040d40c3d4010003048280348483e508101d5074880c4c46600c0422507004ca51550399079112819940e55a01d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 35532909 1250 35531659 35531669
    0x80a08070e0a080a050606060a0512100b04090506011107140402090d0b040302010903020607080105030c010c140d020c130510030201050304290601030f090c06051c0f020702090906040b040f030306 86
    0x8404800051074000c046410f54031a4011025141247da54000b4010f051150090b40800550104404002c50800000b102d800140608004015540d03419401c4401d802c29084420310030381d683c0900c82c04e5a001023140007400446406070511354a060482944c044220142d280202d4000803452203964134000034183c0c6c5584441c40310034030304050900038000e00c6000310881c00362160a000c607400d9401020041e0403074500800425110920b50b004448680205900b1607850392001b400c01c00c87c130f00038040058041e6a03a030081c5199048601001204104621071040851501050150000e6800302c0002520780a003841603030380d00c0b145820001c105060700c41d842554040c10b441d145558440c0e299078010882683d05100c4021005003040489110001c010190b440082040100318010005042d070101010382c030910140400003032100b0344243c102003250090f4002016411840c145014540102142e03000340700b2032409940b00c429140e0041c10203070011601d1340643e01014442c0d008000900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 35534159 1250 35532909 35532919
    0xc120812130f120201020c1605010e09011208090d020607060c09050d03090902090303120a020703090f0b0a140d0e03040314031603050904090f080c011406010c030e040902060403140606040207080a08070e 89
    0x424002203032311418010356000445001d000c1c3c5440c607001e803106050340c1d840f0b00d0351030300c80074039070b860035035540c4405201c5801240906440003d60354540160801d1805000042104111084001e00d034442a030005071043c043d800d001000302c0c2d03100b031800d402d6800c82d1200580d541c8c0040c001a00d175000300c0321040d04400d02c00c010440600700c590060030159120761501c4810720740351140e442c1448000e0048004500c02809050799207071203607088804007155081c05500d840d12924101c0d00f03991108408410b158400101041040010f0303501600390499180030318200900300722140c155817103070b440c040c081082c01300707040603035030394a03808600c4c81ca910240d000c01200242c6040b2100da00000d41480d50381d440c2c0314083d40501c4150444902c540d00503943d041e58203081d560700f5207403c100003504941166543c0e80031070040c0c607038800401c09140143e030713200038403005420002c2ca410401402c0d42d00490050014400165901007a0780404100b1305250303090383d50b0400c0850301c0e81c0268501039841 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 35535409 1250 35534159 35534173
    0x4050a050303040311100b010c0222020c0a15091a0a02040b040f06020d0c08160c080102030421020d02030d020703021c03020c01060501030b0a030b040c120812130f120201020c 77
    0x1d074104114110760400e45c0c0079140c09002281d24103044460044a003030100307148420100052070842040b03a00b1102c1281443c05090158194000300e8000f4441440250700211a40c000e0004148240d08a01e001040502c1100503a41e501c0a002d42c00010014181078040c012540107013050b0140d402410038004000e0b1200d949599000414849100b148007600548903088542442030300c02d0292a81c0002c2c00354a050601c6c0390401150310071140c141c454000300b034000b0540c523a082c002140280d004000e01000409550000121b020031103540f07000b07642c085640800b0040c0c020003524868405441c0040c1c8030000f5042c183c1c00c1000c07100d5450310100c80b5602d06481190960701a1a440f03030440002c001715501c0e00c00640890b0082d4880580c04000303605e0410000b10003802603980140310720485040140c0c2c42e0040e000202c203d06045a0081002c9050b517000e0a1880c005648414848a8a1001c0d50680c6074420b010103101e03006044400c0f8036031180c0c0294000d40440b454044001e04036040c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 35536659 1250 35535409 35535413
    0x50c0a050a0b0603060403080619030506010801060e10031a0a0b04090c091d03030a0e0304150327021c051e01090605010504061a0703030b0603090c040608032104050a05030304 77
    0x11450790745000c8071078840003400f060072410000740e0548101d5143e00c50703012030b4071860200003100b024802c060161343d02130741000c0001403003807000d1402880f036000089115800c0945442e4403500081800d9100d8943c00700802c0412504043c00062103420890403025071070f54400034014020229151b13030400e04001e4448200100001d0040c115400c20100f08111403029030000d900d440d40001c2c0a00f642d2090002c260850643e03400380d03c0c0e620355041160328203a030f502e440d8010424890805004240c1d141c503880300c0b140842354482c0f0000c0a1401c01c00003002c05500107206d1205170421380c52180030000754041005801c01c45c241740780f000e10306400c89400c55004414080c022a541c100d071001c1c144000011542014052842034540350b50758404500e006450002942e004088141e04040e16102c100205440c2d01d00114013516890016019840310384051205a0b109a0f1001019034000c00100e030300010309513619021324580c0082902c41ea11142003081c130380300140002410900001060000b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 35537909 1250 35536659 35536663
    0x1109040c05030f06010207051e0d0507170f0712152c07080606030d080a060b04061106090a11040c1101051003020901080705030601090c02010f0912021501050a1401050c0a05 76
    0x3100b03110700d1801e000340d0b50f920001203888070301f00c0c440d49400c69034500340c1c0b154507008450a0000307030340050328580a80045441e91450642e150744511040b07003030a1080f42c80c1c0481413100300304208030000203021091a0000160b0381d40c0803004094207140114002c6200f21001d40c010403207204000251400c510230200000c002001101200121403141c040d00146004000c0340303092081c40000c01900300c44511f218150340030032005043e444195640c4134042201c54400d00540b01a1119079100b18294540c800090b141540c09020403219500c44505480060101e131107001100205480200301c90601d500107803204108402485103a509140401c1207944401040c1c1084074000c45603540e003030340d8807141161070328421b002e039a81540042006202c0303032200780c0201465038014400080c0580051400404686400d041200d8000904410204882d810000685d000842080c4407002d5490100003071800c855034410503c5d062541445607489a000380c05540c1c94200320015240d00c0d43e0f0510b000c82e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 35539159 1250 35537909 35537911
    0x40305070b2511190806060609010c060c0f090608190209060c03030a020309070b0418090c0308030403110106060906170402010215040506010509070f05161b080114070507030804061109040c0503 85
    0x140c000c4c0d00114034081194100201c103001c60b2107140241090b45c40700801d01106a00a5802c2d9041c02055800b40000407858821050000781e140e0303c0302010189103c0003000c035801c0c0d03400071080005140620500e1420035032138100b00c24544800690315425007005c00d4041c054948060014000802044074540705500210f01c41c4040310151039510392501e40b03400b510302807070140130081c01080d02c984040641c03e030b0201c802030b0b014200007911180d8075070300c81d031050f48202c6007100060b4000b20f403100c45610034019440a4003d500300401c405060110081c03030440c1140340c951140481501040a59000740320200302042c070030140d00c049203807a06006945110070300c24207000c0c40425001030305003446a050211400783c0ca036140e62510040a002500310300b0b1801058501d44400400e10004003554050345004000070000428041040884003002e208010061800e0280401c49000000d500003040e41d07005500c0100090321650742c8607044918007031318441c644c225140c02020110346070480055 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 35540409 1250 35539159 35539193
    0x10060f08090f1204031104020f04030f02030313060e0907020601080309060708040e0103030207061202030f0c0304020406180b0102070f06081b07060c05030411040e03030601050702060d0501030f020a0605040305070b25 95
    0x143c6e0290117042c20b010881c441c06032003024002040c4402c1c000113000110350020640018226400c3c00341402c0310710000420ba42c05440440c1c401242030310b01e420f014001c1980048140090126917141203005502ca1007a403a010340305000000740401004404020703070300030780581040e00000d50384038a4080e548508501442c00404d0b0045c940c90f000b00814002c0301e20a4007800d03c08809030711205610702441e080076100300c2c1d0140d1103c40c04552419446290207001c400d001000c10124510707800a1706080c1e00b42c0001c9100c00c001c02080c00200c1d00407407265005042e1040802600900c50a0424280102c400007403000d0b0801020001c03c0360b100000d540124000c1050110307008e51340041008641e00010702101640040c800680c056014001420034580050600c514102203202030004487c070076001104d54903030381e180000c00e42c18580c080c50b0162045040a5280908507112156140560304c26268200d00020704454a00e0250083c1c003040d044061543c8455529440c00201d207202031001c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 35541659 1250 35540409 35540423
    0x51003170319091410150503010203040203030a180b040603020a091509030305030603012301060e19050d0305040305060f06100302070201050d0203040303060e010602010c020610060f08090f120403 86
    0x19488030450840740038104402c000184020104505400b400794240251076400e40c1e0864542d006400384204a0402c0799002e0018002080c0980005045842d030481e0780613038070500401006880c004210317845442c0c2400c2129100307281d0f90000c46014425000041ca01c8000b20300045e41c00d0b0141c0242c902c003c440e80752015055203c41a42c012448050309c60390000d805541c040011074010310003581c05c80e10140010440305030b07809028120f030300d8007882c03501028003141c0101306050340040500c0800408840d0380900100000c0244030802c0b45025a17417080c0310303e010080403d80148102c4000b554031000351042881c0030318074a1049081119214050301c1146507044142d40b10f031088801c1130361705854082c20010004070800c02500010400c4003410f0b501c0002007140700c41d4004490003031013154000704007001c41190007070070b00ba00030b003004480591806052001541003030040300e01004912b0450081e039039008c00350b0300d0300b10413581c2801c481c00384c1142c5190400d81710380103109690240722 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 35542909 1250 35541659 35541683
    0x70f050f07050d030215070909060b09030d020106060503010b03130204110a08010b03010602030d180516061818020307030b102307050c090403020109020619030b0f1e06040306051003 80
    0x1e0100340c42c00f40381c0040068008075800010300c0804000c0c9034028400d81340660714180c85800e03036401c607002c6070060380401c20046a2401c01d860100088041c904541c0700034040e00d89856001341680c0410b001302529030ba00840083c840c001014400f5441540042081c0030158645140c40240d6000c03400c04030000d103003c000031588a041070102c80c100c0300c0c00e5008501d4000c02010400003001d811140c00541c201890b620700c04901c0c02c101200d00d40c2c1c0d82c040140c400d10b1078100081c0480485010100108580b058100011103151403001105403c07890302680d2561040000c400500000740340d550702c0001490950041c0c1d0740400c0384080450714000321030f1381001c065242c034428050010020310541c80703520005414288031800d142c2182c4640008201d00c00035500094541d0419609043ca0307000070000c1280d81c0c2d601d4090501e01e00c0007946c0009100c110722010520341c0203a03100d001030801c1e04841c1035085844a4044400864100c1c01c104180e0904130881d00d40c00d0312701e01c401d0b581210811 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 35544159 1250 35542909 35542919
    0x20f0d02090415030506060d061803093b0603010209040e07090b030609100e1e01021e120606090d0602070506090f03040f0e0c0c0102190f020c01050304020904020402070f050f07 78
    0x240f441c5042c3e03600f00e03006010650300c040400200c007840a43c1101d80b291500702e8075226800c00c40c0d20101d4a03100382c40700458142080c2004059851b078405001500c0000d850b144045041e20310b803a0440d0841c0c504540c0c0d1503542c500881c0c0a0700c0340d030300c0244c2c0051505440680d00140420000c05136030b000542401403038044d00805540d03120586805085811031420007000c0c800c1540482500c10b24002540c040e80200c000140400d1172501aa1000381d40002e2240310802104c414110070b600c500303800509026215000d0b0f250034800a152600407100016070f5442c03542d858034480c0c0502c0c0d01c80710940d83e900051170300a8031690103440b010400c2c4030703401034044003e10120030b0b41c040c0c2d281643c124201520b1f04401102142d03010f850b030002d00c1030030800308610740700038002082000b400c40c144010003003044000402403030010b9040004c64100d00c501814980c0d01004480d00150103c40d03502c3c030740d01c071130001400034880c50700d005200401001e030003010080c0200b0341c003000e00e6801e4107a80301c199450b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 35545409 1250 35544159 35544191
    0x20f0102010209150703110d11011404030206041506090e031207090302060f0d0b040f14010503121c020c0a200603040b0604050907030501050112051c0507120201020f0d020904 77
    0x412a49a000d114040305611110844010b0f1013064082c0c80c0c17400420441c0b0f40f90303505101c0b81525903800240c0600340131070400d100740210b0700c0e890bc81080c9000c0320310305514000d449000181c001044a0340307027040707a20f0f49402904000094141c2c050b04102400e14500c000380e40340d001c40038003d500c0d202070000404190066424130103c90f00a4942031070000e045050b00410703800410031145d21940c035084c1c0d140076140c9210b0b01e1041c80b03040400090840541c540d0078420031050b84544d10a41c0441f00f0499418125415182c400c0300328641950300d0342c29503c4141c041e0180d00c01d0036082e0300c10480e03810280500e20100c5c2205410700284001e40c0401d5800f44a0300d840100c8024100c0106240418640d042c2584115800034403602501d40082e1a5a116401d5800a034028100102d0004110040c04070500030045581d04000c1c0707103258034200309000f80450242c0c58002d0301c458103002d10a08000e0013901218a20003202420365556400c0b4202d8070003d4000a403007a004501d41039008941d848a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 35546659 1250 35545409 35545417
    0x71a0106020a03110a08070605040501140403020c010c020102030c01140609151507030c21030b0a03050a0f020d0b01090204140904022803050304180e0a150c0504051903020f01020102 80
    0xc0740c0c090441c0040540b4180c460110740f80791880680314205078100818003040190245a1054601041c2d504003828840c1c2900c58191500c0454003d20040c040000c3c1c00241d0007a100e48c00f070a00350074030042d900050381540201a00880d095091018003031541c0d00d0003041300d1042c0021180003003203032140080c0031082c80642c20070b96000f0304050715624aa24000c0c004d4403101d44686883d2240e018107941d404002036171407411510707a05002c00740b1b071b0b03149405008840707004000f601c0118031645180c442594502082a015049401d230701c0c150000d41d124a0725804200b6081a841451540d59411120096110340301c1d52008003009154a0154503103442514003071074009102c0500740d02c1c85100c426072030301c980c910134000c4030031190000300207441031000c0c000608100704034213038500800d2540020303103040a11844968108809141c000380c4080708080c10802d0400001640700841c0030151524030651b0440790b4401000f20b4444410900c0950300f13402c1d00e2090320805200b8083d2001a801d03401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 35547909 1250 35546659 35546669
    0x70903080f0d0209100305090705120606120c09010e0417040608070e0f030703060212010909150b010509120c1003051b09060f07080c010e0a08120601021e03071a01 72
    0xe04108000030100071102030458460380310001441c10300540f00080c1240d1000b810800401d071510100903442c5070500c00b483c02444c081c1c41d002071394400c0900441e15400c0082003603102d243c1021540d0300c0d030344007007050507407050020700046600e585a840958038400200c804560410300c2651f0f541c0e520034080240c0d8200d460b2602c80701034540740c240b030964091701058000707504000301220880d01554200070107402580100c1d0010382c3c0e281050682d2801032016000b0285950501321800c000941d0000500e050041d031110008a1034100342c0125200c1c810a00080d90004101261011070310b40803850320700c0705408403425503040c0c0f8064000c0e0113031034048501c0541000446140c0303810070b4801000340704100004048500e88101021082265001418151000300c404207460a002200344508511000c44000401c40700c1c03240e5403100101e20500002003650442a000700d51180d0082108521485402c1c19001021f500c0c92540c40d601e4021890035206c0c9000b1000740da8422040c800c2d0307203050351 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 35549159 1250 35547909 35547923
    0x204020c0a12030207120f020f120a030b040204080705010c0c09050109021c0501050108070c06020403051002070201090b0313060b040b0904080a0f030e0307140f030d060303090905070921020d0b0f070903 89
    0x3075940c3d01c03d80701807890411076410341c02039505441982790140510030f4000c00c00032800780c03606003c00700102114501c050080c041e0344100300030f0010000008020381282c100340b0749400c10003100d241c411014002984409205030a100000c1403281081d0040c110b10540036111351001a411264003095850030700c106408180d03d50301240c03000380711b054401c000c0b034080c03c005880c1036a20765610749043c0d42c0b102002c0102c2d03400701d0450210341e40904194000c085d40034a4509505003618200c581519140e00185480c1c4d4030b0004035656111034000001694000f46804464982810143c1322940214001c00020380c0340c003d80001c0b140a07104035200484c1d1a40194185881541ca00080340e42c2500d000419210718140c07403850702002c00091410500b1301d400880d900e844c42c40d01038000189a0130000000741003d08100310340340d110b15840b08070f4501041c100c07d200d00c1c8190300070803244240406504172000714a40e01c02d0240b50789509000fa02e40d900400e969a0310b46c1022a4510710600008041c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 35550409 1250 35549159 35549183
    0x31518010315020708120f0108120d050a0f0c0206010e0a0c021b0f030d0e010305010603060605070f1704030b04020a08030405090c250f05070b030702030a03090c030204020c0a12030207 81
    0x10908078000e40000c803080141c0146000c186403217000540d01310107403000141d030103001080b0301300c01034a100714010441500103154160800340d041b400b81c011042019040c1d0f544e0400641080050707001000742c40007142c41040f49a01c10309001303454010034000c1684468802000c10700c400b46920031074864101c154041c046024040d6030b004003020629030102c0d8840c01c80251400503503030501c070307402100301d01e40c50300b0b1018080003001605840c8146d10003418146480d01c03c0180542040485813102e80c011103080b1000f001d4500124401ca01725000441c0303000108004c0104041d030400580554000c07600c500c9010380d2004480da40703104600030799810109210100c1c00780510380300900300e07003da4218041c0c1c5007103031403181c01517620a1004c00d42e030008003100110240b00c0f00780000c00240c40c180e40801d1035403812000103540d070300ca00c010354400c241c1d46c0d1258100b4050386003800006151300400565070381582054180c0d5400486070142c030074151803680106064000e10840e46802e900130382c0034483c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 35551659 1250 35550409 35550413
    0xa090e01060503120a18051908010506011d0609010201060905010605130e090a0b180307030c140c0906011202040504060f0602071d060f0105070605070504080c06032421030315180103 80
    0x2950206d00041d81d0460620b4000c01c2c16919012500c0214420034441c200d19841c045e401420756201401071418000202c0140348044546140d0031010b01c029180903584000c1c05c40101e004105c41c0e4400e003959072604001150342a4031038000c0c8100b2031082c1000044948502d4504400803041d01c441c07180d07512090030600001d424240351680f00300c110596a41d4010014161750440e4080c0300c08500194840b0740c2ca100308820700c0d2480d40c0440400d802410040325800108800f0103014102e10b0510440c0c803980d180d070741801c0d0111405098040c00a0103401c2c0d071158803004000e60350040a0150107000000310312031582c410b50b0741c1000103280c0f55142c0b0f600c0d21818000c1c092500c40c60356040100800104011a420b070113064000c21141d900c1075a50351500007440c5c100452500b07100e100f09820010300404a241041d4504000f26050350380380300c400903000080d0119903446001480c248185410260400040041c5115013035034000f0003c554144070800545d0049000fa1141d101502d00c01800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 35552909 1250 35551659 35551667
    0x60f0406080606040510090c0215090d0e010e040603020301230c2b020f1b0705030703020906130b030a0803040c06140a0c06020f0d020405030c03160905060307050a090e01060503120a 80
    0x14000b0f0000343c2c100c0f01c2a8459498500350345c079012403113015074807203018ac10030f032410f20094070780c481510f4004c0d20300f0300d03007030500140030708880481e0324100810000c280b445690b65a2141008590060007003207640001000300c40110076568402c400078000f82c000490550508040f9140034603000161026100d03500c6801c8403140c0141e10203030215a00788190440c01c500b20009015a05513040c681c0741401c10300401920704542d5801403030098200210420040c0c0302c440d015600010211461844041080c44000c001c0c140300c60307116414480c215260052055403002503008a0003511200c1940351620415500e001c00202000c035460000c100522125110300c65017440310744501c0c405454554074441d10401e83d009a0313058162554001030400052034104001c601e1010268090807030f003a01d40aa403e80011030b441140000c54940f40052940d075070034410b20020b803500411554071750f074852001100510031018080060340c07070f1080104407840c0014100014160100405e40350a40e5048221 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 35554159 1250 35552909 35552911
    0x91a030604080f19030506040b062a0109080307050a09060201110403030c03090b030910060f030201090308070c09020a08061c02060a0e120d0203071e080405100e0a030b060f04060806060405 83
    0x741042041c007441c4c491207009034100c40450070a40e404121400d0080401048424003403070303c1d109000420543c00100380044c20321407240040c40c05980b11070a05c4441c80d000d000103810042101c0720000400c510190840091300140e080380d03490703070b411544800050742220034040c441184082d0900c420800a8030942c49114524031918000c1d5070350340c0d80e40011400d0340056403032520301d80010703c0301200884644547c00003030800c6801041e44916580018103070b45201e010181c01d01400241c10024810807607a40001480c0000003155911845c25004002c21b0342074034490701c905507201940150707110710100260751640040c80149001030541068445403c2d02265170b42041c401003152452800038041654030301c282e0307000340d80e6480032860100180003900301551a14800002441c02064605050324180d51782511418030101000c0b0703040d10381c40001210503501410207000401040044c41e05203000d4401030713400c404018441d20400c801d50780c850140c076080368080400504c041ca0550009 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 35555409 1250 35554159 35554177
    0xc0a0203070b010f05040c180302040c020a050d030603020f0103090510050a0b0904080406110d09090209060904020d0c11030a1b0f050a0c0e010f0b0307030510080109030801091a03060408 82
    0x32860911103a440c0060504240e202440da007000602c1000103041c0f5014003804100c46181203004000000701d03040d0140140c4c000a40560760316510700d81000d00070441042c1291b00b01040351014180c0341d000801404181c00120701409174500c000030307554028090070180640c000094691030f11031141000003004010100310b401a01c498201180e6111041010f0049004580940d961b900384200a0040c4000c14841c248a03402705000e49281940030410209039014170101582e40c80080e4001005401081c00007a0f000c0e00c001501100321855a0046038400c3c615110041107021648049840e030050100c2ca07404150b03d11140809170402c4401100c140c0d20891501069041a8884603d001c482503011140001014014000d01082c940414010000b900c151080340781030201e6a9800d00000c1c01c140300303040c0c4640c0401e00840340d480000000e4a1200c008000044e050b04004082201c03e20894500c0c0e45800f0700c9620039560360400460201025008042d20345696440100c03a6105101d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 35556659 1250 35555409 35555413
    0xe04090204110403050c18062202040506041401020607030218040902060f0c0601060e03070510050c120c0a030806060304020306010501110a060c0c050f07080c060d0906150e010905010e0c0a02 84
    0xc07218010700c60744090303c080c50040e4020405001c0c0d1300b040c0032405a42d510f414018407900720400071036640d0350381e1803101111074030b5200100554404002010b03006d00e81240350700800100700032403c0742300c856056800c6042642281c850752660303841034049202d01204800c0c04015002a0b1206003001e81003681c0780e41c8081c1c00940760445000341c0c0b102c65082043c2c0b1620613003150f001000056030004025140d0403040700902280303854800043d10102d0003000300030600c40f01080f0728071802c038140181030f6103030241c0c0c0300f42d6520342e0703948017103504c51814160480110b0042000b00e2002e04001082c2c80c402c5501800410150b42006e0064035100e507400d6540c00d440c850501441c0c00034000d03005500080c41d0a855500f145411440c21600b05100a05100040e50010904102c2d10200084052a00205031881c5965400c08601d04007c2c00d19407a0141c075070307814043c01494030b503142d000300c1045a540070848181c4c1d0747c0718804e0310142c0d003086c41503d24000900c0040390a41c240b0200030040340c0d9442c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 35557909 1250 35556659 35556671
    0x20d08010e0705160c060c0213052211090103030921022116030f020a0501110703020907110102030c030115050703020303060f04180506010602061003030215090f060a020706060906060e04090204 85
    0x9070301145d5070417503006200019a0078003400114108441503007240c0a1855080c0b0145c42d00340c0c3c0c03060080c0242514074080c410061000001e100300e010100b40710f61406040300c686580c490a001c0d040f100e1510036610301c1c0450440000c4c000c13602c2c06d522128640e009004241e010b04540c5140d0098841c900180064010b080c1c80340d110320102105100210311880d080341050340d450041107000c2180e070384500c1c18401030600e00082c54101060030810b607641240d100c0d03c80d44642408030b40c007150302d0425044540c400404e00c9101c600c414041d44c102c1e450000554010280c0d11380c220380724013403618000c000d6482400031499600d40381b61410100031028000041e4991a0981700b1501642c0103025911500420014016240d06201241c1e1003000c0c82c001d095490724595000f983d410070306165001c0c407590b004c041800540180420082d030600c150032541c01c1d040111401001754429081107821900c0c008000600d40828003030001203881503103e25030246103401c00e1101030882c07404101d92081c2e80e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 35559159 1250 35557909 35557913
    0x11030706020f1002030c091c1703010506190212130e1806010b1e1602030111030105060405010c170a020601140108040b01060e04110301080c09010503070b030c070507030f03050a020d08010e070516 86
    0x11407180c0e12100c0c000d98000f94a40b40d0030000e5a407040d2409d400c1c02d90004100500240e10754804a41441e03400d41380c0034010002110040341003140c0700c0200d144285002481046007203106000a0540e0010b906c41d0441d074403a040064011080b07007000d000550031040041001020100140040005403422800c40c12800c2858150f554003c5468007000382d128054681942000d10034940b004040d000c001d49154144000500c46006a01ca00e038100940c1140c04030030003040102d80012041d587c0443ca0315540200d102a40300d1002f4000c0100e5400c034041d64010942c4640b41080c00382c1d40001074540707580d007419000c56041c0c000701c034903a4009448650810000141100940c0200a28405000c1c1c0305100c908104110750103a1040344684c0c4031241c02d01085040744102c903003281c1a181c407d0794071845460030320304200c42035001610000f0150a06c02c245500000106904615035080d00c00d02c21028006071001c1500f805080d1841c0b008000240d6014040c400422041160020954001600d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 35560409 1250 35559159 35559169
    0x111201080c150c07080607030905010e0105040309182403024b09010312020c03011a06030709080304080a02010806030613021201090803160e03030705033411030706020f1002030c09 79
    0x10340e181c100103a030789c82c0380c0740c207215080c0315096000100700d00034016400c150300d00a05441303090040c820508070703410748044d41c40c0c81503011080c111604819004140311400c0c0554100c0e40c5448103a00962881050380400d2400c9507400c82414007060700030811050f041c10890382c2c071411104103101142c215401206558590741054025440380494041c00b00040100a00780503da0f0803480c000da040c405500200d058050f0600422001956155120768480d641180d03000880c0d480751600d8000000d000c00c0c7d02034081350f800d807403074001c0c0c1790b41d241030711103405240e5a00380480704000d840d075000d86001c00501d0002600d41715038240f207001068201007611892891307071040c0e48040c0079449464003440e5640d0000182110804202d01960400c032203622503c0d101c0c8620080c504440d00b00360b07250441001c0c1d2244100381004001c00a840108081c0b80101c10f40809640c01c078420706c685e4400040b15840000e488026907204005019a180016400c9019420207400b02d014210140b00c992040d441d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 35561659 1250 35560409 35560411
    0x80711030a0f051606090312020705130203040623070806040209060c070503070602120d0b0303040e130c050301150902070c050301110d050c03010501081909020301111201080c150c070806 82
    0x1594030b80b200002e45280c030320328048071000c20103240744001108000300d5400c0342401084031b411100b0506142440c01c0100c0c02d01c03605403c56907100e50050710711280181154083c6118034802d0100300800d04550123100c0361600700ba1074501009580d50009040e40744105007850b00228003034009401c001040c0300180d040e03004803c2c0c00300c031070780322060420640c07408100100080c00580098119003440781380c1c140540c0300308040c00e1107060701c41d49010440d40b001c1044600034000802100d60314240b46502d05082a940306007603c81000303449001c5141d00e018420b90200f115010340c1c0c0c0d41d0b414501170906011350071565059500c41c0a41c4000505a04d080c0103108281c59005c008964401701c84c111071007120700c00743c40c0380e0104100340014042d698020914941010794403081440b00000081644050030740c02c02c1c025055402d100c5d040100d180d509028110080701d2250410260b80c0302c90005668100f13004600d54080300003c11000e2042c5001c00400d5105844810740b840e00d51103032000303841d00720 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 35562909 1250 35561659 35561663
    0x3180b0c0d060b0702030c0d03050403020904080910020c0108220b090a02180f010302010818070608010501020c030a080403081309090305031501170c0307110601170c030703030903080711030a 84
    0x4800a031000e8a41d04501c07802001d0408080010304011064011170fa9484000740786e20701480d110304050f0240340c01441610001c1da40108100400d18081c41e200110b07802c00c80920f4081d47c41200c200650038004207030745010704ea060350360140380e544541012081c0101240040300d1100348a081d6404100315050700d501c2180a0300091061181d94418821a070782c16550030a654510300091011040c40807844504481d02480c004030706445203c02c860803080300d0040300c0041d10440100103411074202c41c505040740c07007d03000d03501005181000e1580b101000c20b002014004108800c1c400140c0e0800540411340c0848980d074112611600c07502c1c00ca440215003503012070404002c10101340c501d162400d041c100c080c41c004100803105a1f9040d40114040d00423918403001000003085030344500c0030a002403848000300c6c2c0d07040d6540c850950140e01c09008610300fa00802403d506caa0800180c110116a8140d407030075401c501d035840354221030b0070907801154190003800710204680e0f400c12545203468 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 35564159 1250 35562909 35562931
    0x60d0905031905070506060d03031d0615010c050303010504020d0204180501210209071d0406030c0905011505071202030d09060f05150607020f04090503040f0614030402060a03180b 79
    0x3407503a60b00c4482c0d003203242009010070404100070343c0020f0000c41c4140d0089002c0d00d00002001d40d40c40d0035030190195221149900c0201900201c0000000514500034400b014150010340e044000441d1001010b400180040c2c1c8100010043d504280d40185100100c16100508007920758034181401c060240b0744941ca9502c07400140030700d10580682c1d02040c0d0403003c08008101040d4080b80300394800410401c1482610700301048500d101556655600100802c00c06c505900d078500100035015030f01a41d8451440c090000c100060155000358003026039403150344c1040075a99840280c249016104c3d002c6010901c1070195282e020301461310400e2082d07070045001032104400f0390884200400d004544171041d000e03c102034407840107ca1f001a0141c1c1c460038642000c00204000e0f11035210002c0051100090000d0783d08145074405060303844507070342c1c1c0c907491600d4a10584103000c1518040d502010030092244c4071406030b07001a00c00701c0113081043c100c501c1d5803601c407804002203c02d02c03014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 35565409 1250 35564159 35564167
    0x30804080f0115090203060109031704030302010f0501030c030206070302150a09020310060e011703041205150702071505281116030b060d0c080a0c0e06120d0e060d090503 75
    0x8540c0034042a040608440d008011140d070b980d41c0c800190b80c151003210342c429070000202d00071364814004207000d9500040074009c00129462600d0311903103d440140d0055103800d1020a101c00603005035030480350000c00940f0414256001c005003030380130840071000d500c02d01403140c07806503017102854030a02c0341c00c4002807201e0312030040c9824420088099070402c0d250200a00810040e824a98155420b43c829082118403480700e051440c404c82d006901c2c1000082c0314501080800586182c002c007e18525040603191000700381d03601c00141c0a104206034513104212071541c802c80103004005a0b500000b03a84040040c5005290f5080d041d40e440002c440082080c5e42106c04c100075000481e0010780c5c1c2c00c0051458644100f54040076128500c52074808011506221001d504000501488002e0350303642e0080740340292052655210350f00341e01e034070340001942e240b07403043c1d41080441c0301c0c1c400345c444400d00380000c94102c800d010640b42d00c80000e0010018803c86c5109007062144228001d540d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 35566659 1250 35565409 35565419
    0x90c021606090f15021005090f0312070e0a0b04060c0f0b04050c100e09041103070302130e070902090d060f0612030309060b06040605191202030406020a0905061312020303090901030804 81
    0x2002840c0c0000c030400550400d03c0380700590010b06c3c07a1188103096000151519070102d280e083c0b01c82c80820301d003a8032011548581409a80081d2805544aa2100302103c6c4040040c80000c0e004c40c07083c1e0b403c441003484200101030044c6001940f55202d450380141d00902951183c8115105075429106640324400b030f0001e60038100600340c207100c5542002203807071605000207100d10800410007020411414290081c64030300300507001c00b17164001c080d000307020507115181d070003481d0925120741c50f07226000c3c00141000071442200c41c0700c18054440f1005840075111b2102810080d41c00110166031290b0018140507003001c02c400891095030046211601410000180d41166900318401c1d00c0070882001083e402c03004440059240144102c0100903545041e07840c80d10821041c1e600c1030001041100300715096000300280c8c2e40355190444c00c1070316030042c01245d000700000d03058920100103083c4004284000712000c40c030f20081c00c81e131800c1d084401003040144203134022901c008000c101400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 35567909 1250 35566659 35566679
    0x31704031205070513140402040306051f0e150d020d0204020307050703080108150f18010204060e042d0f1803020a171204030e060c01061509050603010b0301090c02160609 75
    0x7420203414500241001e01d42d51000b4041c108510a000ca0381106c800101740a0b203072074040c0ca0003180c0202e03040106141272916025400c0d101a4080c8140c408c4500125000e0140400b41c0e01070070b40025204079110450003403280781c1e0079000c01680c0c06003403080140d005030307100e0004510404e40d940d02c43d0b4a8100038038020f400e490040e001079442e900500050560070080e5058aa840003510960141980300c92405503228819000b5002e4107500008010901c00e402c141444503410302624200203807418424050f10f009201c8214082412140415104170106904000ca141c8d2240100141a0484880c100c1d003c02c1480011409a0400b005d528240000080c15441000c100b940e55868aa0444100003c03810000d20080500413007040e02046502e428042e45c2080d07045200802c00130f902d6444420084504c0d01942000584a10011503942042d0054904aa0389190710600310b9003040e0840c0064034001c80c4240c11031147d090003036084004424a0801060782d0344840c01e01794100809a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 35569159 1250 35567909 35567911
    0x60501140306090a02250506060114090906152106090f0f0402060304030933020309060d0f11030109020a0906030c02060f1b0a0503060a05010201090210030207031704031205 76
    0xc4504106100304601522a03401c002d074000202440181e4841c0b0b1140c2c002c0c03040c00d550408400c2c03160102d000383c00300040020742c2030046000341c076a4110110084c490403450702c101109640c00142ca000411800d040c450a482c050b03c010200050400185100d528554000e01a078000c0c486103040c240141424181240364012103541000c03c8185050040b505803004040c02c007e000381c00000001e4107252090303441401910b0020400c2504541c019500d0200b0409503d50144160341d04405801c2076000104a031900c40e8080c040c0350400c1c100d052000700500140f05407481c50390300c2d103001c0050f100407280110301030038090304016140c1c0c00f100c1000700007181d5508000180340c500300841c0503490b000545203a001d5070114102450b40ea0300c01402064405d800902c18a0303a0300411000d0070181c201000d54071444007654640c244940c0c400c012402da69040780c019401003d881e001c0e1041d9031283d00113040d0140a0304113004007646010708aa84620115010b800056104405041d020000d000300c0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 35570409 1250 35569159 35569187
    0x131b0b0f09040b060a02030f130f08150702010605030c040f0b040903050d0f1401090b0f041b02010b030d140c0c03030a0f0e1807030b040e01060e070207080604030e04020306010e03010501030303060501 88
    0x1340781400140c0802950307034401c40340283c1c9042004103551060207000f8101d1006008200c00429010343d071200103654030811451003082c0410440001140e1310b1052041c00110351005000b4070b03200755620180f100030100078080031102e546400c0400c0007a100c0717024141040380b007503179282d1340c442004c0060700842e41050801d88031142486034515624040e03142c001c2c1507842d11500081c04100d8400092003c0401b184450382040c10140d40d2061406150040201e0010703940082c08401000c90801d601c0b020f100d98840081044003000b074241c4010310004c1d01d02d05a0000841d001d0f55036803000a1303d036030004148040050341050f10075080d0355020404640100c000e584100f5105841c60300c1040020006100c0020140d454005001950301c0c0c1d0000c080c07510100000300005620b8a40c0007201d210f0032110b000c00b6101d0210005403441d40051240e1245801d903a62804c2843c1300d0041001035800a001c0604202002d16864010b035001c0c450076008500c6a1400110b0714980b40003d45980e808a880c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 35571659 1250 35570409 35570419
    0x614040210030e0d050c0a171c05040b070e011103040902030109060e0907170a0605090d0f0f05040e060109180501060e06090a0902070f0507030507050f09131b0b0f09040b 75
    0x10f071000b05500041807550fa0065090284c2c0381c03800450b086140c090705d100c0c080c24840081130b01b00c800c420760070b00500e0070401d4918643c44d01e545190b00101640c1c0306880007001203a0010020f4001c2d8843e6044100724001490a0254100c4846560b40740d41c019412809000303900000400c8104d41d030388211001408060f103070204a00e000000340d80c071502d40e84581501ca48405805014400040c0401d644890780311004101a0402d1043c0ca5a64080d10403400b0201e114100c48618250058451144c00d0340b640d940c00c0c1c40c0a0820322a103000d007402a2101e07044c400d220b00086840c0300403031440c03a94900988000606503140c404020b0880280810480c0688020001295642c6641501c1401d4034000300300540e48210f185850b4450340982c140140490103290008020040040b8000088680407a1a2141c030740309a4204200400c0a4031608094000000000c0001c5d4040c0c110020640001e22444040d954a02c90811280d02c0802c0c0c4446021000400c00c54502d880d1003004501f18060754 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 35572909 1250 35571659 35571671
    0x1020705040b0612071b0809040c020a0c2106020d0b013002030c070203030a0f0f0912030806010c02040507030b191505070501090c03030905010e0f1e01030603061404021003 76
    0x100d1071134414901210380300381100b00040c80a0340242e002890322825401b030460100507078240844150060030105200303500b0580e007000118400120702c49030b19004280b42d080305240c200565001081c2d20f0165007801840d0040e02e0100d480740c8040c162038030304d107000858000c0380240010401801020640d1002210711070707203a040d4401c010810754000050f1401a920744403921515800d004e0440d00952510002400c140001e610802e003401c509465115000c03078604010050359030240e01d00500501c44050744600000c01c0c880c085076904410706041004115146802040035590101e500401082c0c03a04062026414103081c0522500421030000d03032110b040018103100e0076104e010241c100302010a040f0240f2800703510031254a9840080c8190340303580ea1801404000b101c1c810031380410079100070561f0b2406c1c280006000000024000302c1000103d45101f041c0200c50b400f124100b6964110210000b1703894400c02c0c00c1d4401c04030f04007000b894140304101048402182041c20141420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 35574159 1250 35572909 35572931
    0xc0405010e061207030c080d090b090d0f060f110c071205030301121a09060709050409050d140f04260325020105220810020f0708070c1802090102070504 67
    0x1c8102508118202d810041040040d00900d00c0e0035401e410192590b00100d070001040d40d000a01c030305803044191202060996144030000791401100e00140e003142c070742303402c180c009400c003112403002502c185000507840211200040442d90307071152810343c1d03a40016481d014500700300003d100429620030790107280002980d6464aa002c103204075404d0024114500c401c10070311503004045026040c0001d00035150401d00207642c0c510603202c040203d01942408640703414103001c0e49004940050003083e908540b10360480c0c01c0b51540041901c0910107002c0c407410340300c1141c021f10060003070113464862903c9800c00c82c1d0440480c04041640b1790720801c081d80001c03021110b00107404540c000038820242c9540010303100c82c4101444014202d0080e10004000310100d150001581d401d001200c4801d2032241400003248540d12101c2840c9005012001c00134542c24000c0c01c01ca8400c2500070174690703454101c00d0381101c03401503204c0030540100704000656810058000106811941404086a01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 35575409 1250 35574159 35574179
    0x17010e1908071403070807030201020306100804021e01030e0102040311030607050310060305040302030906030103120f18050d021507080a17060d020904141f0615080610090b0703050c0c040501 84
    0x30510060980c240d00054203a1036000f4400d1701d0041d9000200c0c5c81d501c0c113007440c00070b0003548100c074843d2148290480c6806424851048180709035406402e058204203d50343c415442c4d4001408075041507140d0403005a10b00c0700b030000c0c10007544201d192603161b003d50010141000002880a003c1002c1030003007281c8800a041041c5c1210024100000c16860b5800c1c100d040d485401056504040004000001c01180401c64141d541441d0707168083d40c4003850040b50400c031211855003005085030740a205c03604e803080072100505d02c001c1c00003084e0300c800b500360782a130b0b0020101503450940200303c100340203400611000150400c0c0c14200914034003030000030f4243e19080300182c02400c0d2000040c0802c40b00b020203601281c1a8800c40c1c07806c0c10b6184050320082c40441800a1070360802c10005250030030320340100e800d090640ca43c45203503602e802c20701070485914004d407030030040b42c03900000b002034400d00188641e80c042d0392035503600c85440701140e10740300356400a0382c012407074407004000c0b0b1545 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 35576659 1250 35575409 35575417
    0x110c0d020a0312051e030115020f0d030e1005040c050108091614040e01050103050606040e1c0516080c0102070606080a0c05040b0303041a0306040b0a06020a080d0617010e1908 77
    0x844030f02101c419081c800c08907070ba03001c2c840c2c0840090300d08500b00207141500d280514100c490f01388039072190032031100089840f001c142c400203207117600c07140400300101e00030b4111006054011040701c04107050f00b5584401c0e0ba00661f016980c8501e140b000744025603000014aa010850030001e081400d4090785c1024034031038510130030301d0540907448005843ea80f541c01c11034240c0c040700d00a1286503124103010b82c44074001da505511551034101c03007415407100401d0341110081040c422010118005200382c902d0340c03003120100802c120f50300241c0d0024400102038461400e02200040e2a140546020340c100d90300d44c2c10042c034943c000d0405030002042d0302c1c1060156041518045240c80c03065000c00d180d8081c940143d10000d00c0c20380340e5660503000c0c10240d4414001214180044e0800c8014040b440085000d00c000580000500d2000302e5501c83c004c2000600343c48002a1103583e4101400f01000d460205180d141d45a05c80782d440700b0f000b0010441552061000c6200d42c0e505603884070a1442 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 35577909 1250 35576659 35576663
    0x303080106120623010206060d05060c09180a05010302010905120d0c11040c080a05010504020708070b040f060e03070203011d0a03031d0102032502030913020d06030c06110c0d020a03 80
    0x4a0400000c0b00d46000f6040071000f40f180481a0451100703c01d0010f81c04100c80f5103950042c4a1180000c225281c0007001c048a10b4118000e006035480c0c2c4182c0704210751118440340d800021503010074841c68507c44d0500d2280e03401050000e615415840014001800307a8040751084030541d148125988020a49540c215850306103450603161614107503070f0720381e0312070708184c0c0c040d1412000d41c10715038002c50003500c6212000b9041045a0301c94040200324002c2902c0503010090900c2034130300081002000d690018011071103403944901b40e0b60380b40203540c113000c0352a449070008661070b000c50400b4020500c0c1c14013401c50b48160503000820381c690321030352250003904150300c0709142c0c40a095220017050940318030100941d070341d181c401c925001d28103031380800e84440e014140c0d200d5000d910110580380405c400030865030654000040c850083d40080055143d050f40d035860010000e81c1220300c640040000d0b8075540903801d000c0c503405040003c45543d0a000c0c55100003420b0059881950b2241581e07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 35579159 1250 35577909 35577917
    0xc090405060d06050108010606021603030507080a090b07140c0906030d0c06020409020309060402031e07121a0901050601090f120311100501060507290606180d06050604060b040303080106 82
    0x107510301c40000c091042c0420040c140c40c0c40c0c5400801e01341010b400200c1030315000c1c3c003242c0e00e20102100c0c0041202040c440580010b00901504c1d00007040c14009048600c440e10b4810704850321440b03805202da0098100321035a0b0300d020300540107a00d040c800d40480c036a0450300000c4d146010f002181c2c95665003072002040142c804584000c2018a905540c040e1500400442d00c900c2c1101c0499610402918240e100348a140c2144100700310038100c221407500840082c0821526112400340d901c00712070b9040310b491080d0950304c0510700502448a00c5600f6420000c01c0074105540054069429038020b81d00001040900340302c890307600c0504c11a000d5061415036628131a40c200030b130601981c0c2d10340c0300495080c0310001903965400320217401002e004080004035104960810b40c3c2c0c821114445400c00c0100354000b45180c0b030940064010303c0012040202c24a14200004201d020b80311301c100c41d4103648500380160b5040c2845034102800f0340910b0207107020308649010340384c0340051003032000704 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 35580409 1250 35579159 35579161
    0x30e04020c0619091e0507050603090d0c0f0515040204050108070f170f0d05090a060504080604020f010509040c0302130f05010507080a0e1020030a09060c020604120b01090b0301050c090405 83
    0x801003aa01c00726102e03410911790400d4550040d44a00b00840c65101a2641c0c8545040817079245000c0303080700d015908000c020300f500d00d44124113684104042c2010b50741852243c0098000c64810700ca403081c100d40840c031509051600f441000101c0320103800c83d051b0b5600c24134003884200008c0000310700303442044103500381f89000001100d1030002503007444102405803644600f00c2c0d580040243c5807040c4115149000719850f078404441d40e02441c0b04800081d8000004100075040138500d0003010001031420901c0d081071000810242e420070552080000da000034a031001d80a43c01044010b4600351126441c003e1411300002c0c80ba001d050005004a140002c2103130301640110b104810500f80a0446a40e0300901c41014200d5544440010441d04038841c4200072034002104403000710380c50340c55481c416400c00700102d454441c0184120f80110082002007a540c03000e103070485070a8822803d1603203960400300303080183c849944000740243c1c140014403015000d04020345d40c419505072400242 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 35581659 1250 35580409 35580451
    0x601200a1b050d0b09121201180e03040f05180f0408030a02070203060408030402010f020106050102071a0405090a0e0f010c05190318080c1504020a0e060102030d0c0507030e04020c06 80
    0x4006041c0e4415a0b02000c0401c0c0c40f0104044c00d00000e203e1400c601c1a22103007145440d041040303100b242014048201c1810040c4442851000740d40d6048000207400140b4944d2419038521b958455013011600b045049020081c41c90b000500d0800c50038102d0b000f0307050b418103c00003010a800503000a1407018040005198481c0350313410707150320a4006003115240d0600d8204817403207034006d03141680000c090683c00441b542c0140100011500181c0c01030120f98581401445160000309000c95400000c00000600355100300020740a100840000941c0528841c106c9180002e49120b8480c00c3c4d06003800c0809103034200d0b003610401c000c088522840e020b1001d00440082613455818004405070b43c052505004c103600280014401e8070045070342d28180e041103082d000c001100d00a501400e94803043c00841c101d0b008160b0484010300450f030400016089120070f0303a04464024001400c08601a001d143d1320401040710341e0415201180303000d004030744a9884e14002484182e44035841513501c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 35582909 1250 35581659 35581703
    0x1817030d050109050103110306040309060e18090304090c090810020d0612030918090206030a09030c050d02030d110c0c100216090b030105010608060d0f030c060c05030601200a 77
    0x2154031803609080001e5030311100b06000074003082c0000c0d60a00744404001c10641000106180100d400d40c032240802481c201c4120340c00c8841601507500460429000e00302241d040b0751050050350381d00084c540307441c2000c00007800c50b0268543e060801486a0301080b980c1c0000c2003201402641c04000742e0345600380380c4107034090076541d0710001003130721440c2c0c0c0c1500f4158006100d8042e1011101001342d0581c1480e030400640b0700c1440f0181d84403804002061800e0f005502002c03c8074400c0c02d2007a4545d1158480d2401e1088c09000e07000903800000f011581c0030024400c10042080401a0a0910804d09802c90b0303182c1400c900c16001c0e000c10b8070010b40c1300c0e00030494905a070803016034036070144d5203d10f601c1d0f01501c1d5030f1003802d002c0c1d07080c4400403c445000f400414071401c4045d0015401c182d07107844e6031481d00c0f0030900035003d0103880d125150100b1241e00034910507c5040d21070598074181200018075280240c0d012031b40c102c20382d84813843c0100300400c902281c07540004c018400d5040584c0807007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 35584159 1250 35582909 35582917
    0x40203010e010329130201120e0d200d1205010602120306090a0f020d09060b030111070f080d090b01080606010c21020316030306030507090b0f0402030c0c0a050c10181703 75
    0x710418102d80c10442801d000f130043e05d0807a0b100b0313650941c03586132200b41d0006a652440030f0700340d0354028002c0b00ca00c0e2449850390302040f5600c0300b07000d191414001200c5050824848ac62070002d40d102d2900c0f05002c02c140200d03801040d103840100303034070102d041c01014140000740599104035158404142c003001ba0760030000c04481044411035803001c00320b0303031080140740302c0f10116001f40c102800042c85287c10302c03640039042c0b90400500e180000680e110707502e02c904140100d451144c20301030200c0319a56880b500540d60302c01d01e00950194100800707103103007020040c041030401c41c204090310f0004a82e201a0b00c1c00e41c000503440b800d02031610006a04600500c0b050032030070740c0d08402c0403041c154544c021400b02c0c4c0c05401038620f40c58450f8030040584d101300300005d42180200c00300051a06082c0d0045a0103540201ca030303810441c1518459060410011081c3c03040c0d4010100400d051405940d23103007103240d40d801d0048065480d004a000c44103202d115500d0112031007071030f20b032051000740304403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 35585409 1250 35584159 35584223
    0xa120f060e09010c0e0303040902070f0b010f031e12050327030a0906050a020309060304110904050109120f080a090c05130e0c010309030819020405060f040e06040203010e0103 77
    0x911005440780086400e80301d003203503502c1256003445803c0c12042e0080014502c1288083e0241d45014100100040a588049070444000303508541040205581c416424040c1c01020080142d040c510b0070054505c00742c1c200007841264001e61135000141b00e40380442242e80203800c181e074807036942c902e1840c00e41103101d581c0040d108426400c1c1000e4840400200072007905a100d012100fa00d40800700c91600030f1003820005a03000b0086d8140c185088009540c0c007502c940c1410404450403c04140407000a035412544d503911a00200104500d40015003055602d51400c1c0035010081000100340c0407001c5c080e07084ca41d650341079141c10b101072140c0410117404080c0c41403155600e00d9941000516040d0b03003903000e41c001c0b2118126258400d014003600e03141c01d651000b00646800480c10700a07402c1041010032503900300030000b02500c074a00035028a40e04018010786442c50800121004200142038501c11481000103211034004d08901c181981d801801141c1c06103503e0000407404000e403842 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 35586659 1250 35585409 35585411
    0x1120e0c030a140d020706020709021c09060209090c030c0d1509020c03070b060303070201050d0b010c120201060519030f0f32150405030406030b0102160303020106061b03050a120f 79
    0x40344280f08546144004203010282101c8103401100c5040781c070345145004440060300809810803550142c1e4001d01444034101107408203030710010881c0400c856a01c0c104a13130303558021038600c0b07a528140c5056584030b052512614a0361038118000b040ca07100300941c85a943e5502d2210245e00790b10342030002c000d86200314045560b17401c10030145590750080b040440300c58020342c00056036410b001c4155a22150306840c1c107420413a003400b000c401750600140d860b04010020299102085164031280810351003034000242d50382c1403006220404600034074440e0840c01e8000e080001500750700001d10003e0700603010b20110a40c2d45080c0e10443c42c0c000603501209100b6121140204281142035404480384049034074403841a001c00e603182108039030151142e007003480300f002058025040808480e4051060b00c141e001d140c400c3e80c240c80d80540054005030b5482d01e0500100e0f41040e4140e81c551240900c1610310000396034014014410700390304030b04005400410240707002140e001018491102c0d18 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 35587909 1250 35586659 35586673
    0xc090620030708030916030218040f05060a021305120d03180b04050114011203020a1202160306020309010506030a080901030b010e030f010929010e041403040e01080114010501120e0c03 81
    0x40000f42c0ea00241d650580c81e0050b910a90042040442a0800c40f079000c0c00c03038211108423a86500d207888000300b05072200c0258500c204006141409000e100700c0d010900182c6940c00031078031140040003a0802401201000c5190f8246400001e500c0310079181c1e071070082500502c40b4011000d1004140c00184a580184244020040c043d00711a4001c628241c6030316044e80d80d0b107611071078246001d070041d0143e000300111070042090011740404e400c6090041b10b1862425003880382c9038038915481035035059808824010324010a0141c01e400040890080c18205500d44650301d02e4460869400d043c1550f4400030050759003d4000f098000c2c07002030541d4034020984100c20301030704800c00c1c121130b40d05001c041810154030600c480c000c00c0444820f9400385a003000c1800303170400b00c05003065410061000140314000802c1000380050443c2c10098100703545080b03c0d0030301b910350381019290010b040000500c802e90f0720103441c0c242a00b4120307012a52400144c489800c0c01d04100505401d40030b0f402c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 35589159 1250 35587909 35587913
    0x1605040b0303120c1207090905161d030708100e01050108070e01141c1b0501080c12150604030f030207121101030b0409021e0112020a050304020d11030627010c0906200307 75
    0x40540c00c22640070315010320140e03a230808900d50654001038410003043d28a210451f07601d611112f80d289100d07001c1c00720b540042e1a070f4400c41c0340c4441d001c021000e032501d5061406002c00e0a001c1d0f0760040c95424018070302c60b03042c1514071f01d060005015250310035555003010307209562901c1000c4880301013081c100300c01a94074140a10305050804068209c0c202d240360010b80ca5105141c03242c8540a003040560402c00000f0030303080c8a140141c00a15850200305640170300b40d980300c00400003903202d860104030286107494064280481a40600c1e00d40e044807101c0d83c08911000c001c00b044200900c4c0019100524000090080030040401ba4001d42040081c851030038a0a02003490004262182c2180e048502d0f9820107038400c43c10f90500050b4240041401030038250041c0d0b403c6441240c001c60300076400b10110b4030f000021140700d8071140003c101850082c1ea00040d540c2d042000034003c1c026107542d600b002e401b030030040c801d8504000e41d04010201d14403504243c500d0021200081e00c2e61007400d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 35590409 1250 35589159 35589167
    0x2d040309031a010f050103020a020a080c0a03080c0703020304030f02010519031e060302030c01030213030b0c09040b040b0102120a0c05060f040309120309050f040204090504051605040b0303120c1207 87
    0x340c0011540d4005211580c503900c2940342c0d40a0407110a000707882041400e110045000c2e400c5081c00d00107522a0344e0740321000030451b42c05401c0b07004901c001020845207504000340b4194014080c00f0442c9000c200e100040b960200407142a00c1e0003049684050045d803004845512a010390001c03c0405889038540c003952540002e00100000c8262011200d074601c00002280c40300c0c4402580341d40304081c44940c03035000740c01422100c03006a100150700b581e01d0711044818002200c0b08550b801002480300c59070b180510540030105020790342003019141c4c010010356102c0800741d40d079400640c040b400b10503441c850030480150a41c40801c0ea10a4108005140004182030354200e02142c0351450200e0440c038a2044080c04982594451289910742000c2c04025000c01441c541c00070740802001ca100d030098040c040c05180328000803e4510020075003600d0b14025030300814400c03800c0a600104641c0e0000a0b40c0b0b10210401c0300da032198443c81c16444851080f40405074504a1140030041f20a800c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 35591659 1250 35590409 35590427
    0x9150309010c020106151205070e0d0302071503020c0604030c021917060901020307050d0b0301060e090c01031a01020a020603090304050409080309250603020904060503030334082d0403 81
    0xb039002400016201d00190300f080103040200070005000c4203e000581c085600425000489400d104e04003191a0300841c034140c46200003170700580d202c002c04000c014503c80322181101c40600e4214208850103030003607103c840141c405401c10411840c644207660b02c10b40709441003604a886c120040740d448030041c00310101c0d000c26040038001d0000260f01d449060084900c610b0343c550340c1900c3c140b071000300c0c28020040f0341280c58240d940d6100c04902180700d20855805880700c14000c1c90042000130004003594080d10056220102d210040182660001603810f1415412918151070390303214004140796000b80c1d0701c11540a81881e61840912034030000560065002406540c00141c0d8041c1c2c0c48004164400c04d514500f111940800c0390900c60340c00f4140c1070300028001300f1595036401c000b84c955041034556015961400b0b41c0802c140a1000c4400d20340c1c0e104c00441e070f8a400c401100502409401052241c07256a050b0b222210050f05c203000c1080181840141c0410f4100790800910700b042c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 35592909 1250 35591659 35591681
    0x60c0a050601090b09071409031203190c0f0507020f060a08040201020d0305010501080103110d0b07030c020c030a0b2a030f04060b010201091101141209030d05060105041a0915030901 80
    0x1010000300300e07820b0901800350840d0300170b0b03c2c002003031300c411200700c642d0401e544200410131300a03c017503441580e060201e2a20201108882510303030500c04900703191450014040d46040703113044240c6c803e451300003243c074000d2807560a010351100001d00116020500542c4a950f2007040040c00d9420240c0180d5074500a60003030f4200c80c1c0000551000780d0031258280207190104031a60010000a03900c01d06d041092400600840d480d940d881d42c030250030000955008000c00d848040214042c1d80c1004108050001200102401c3c8115114002c0a17400500644400d40040d00504e01d007a0354041440f407840d8202084e07503564a410080310780b030b0302c1c001e5500b03d41d52804e00e250080d46620501a00603200d0b0041420385070054608015501140340500076030403400188000c524414400c4501485000a0b4029680c0c0c1c01c80c40c1801e500f10703000280034505008080c001070164a04400703143e00b01482a0b121942d43c0c808032000110f0340c030700390300c0c8070000c0f00000420803c801d401034008405882d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 35594159 1250 35592909 35592913
    0xb0c03180603010f0b0a121b0e040c080c090312040b0301091104030515090c04060314010e060c0a0c080d020d0e01050106020c1008060a08150709090c0e010806030c060c0a05 76
    0x1261003030820000344000e1007503140c3c0304441d50050142410360390041c8440030190400200d00c046101c500415104e40880740750006901c0e440c07135420b058004042c01350310501140d080040017141003000d4072100014005800281000c80d858101d518200061a00d454209045031784882e6038041079200340e4000d004001d00281042894000042c1840594041c0d96000000c3c002640607100501103003040280004514410801c3c00c0c1200d40b110b100e0f213800b031401207401c4050829042495405c0d181c0100b111510303603000004105207a85164103541e0308192501e000f070000e82c0e03203040c4199030707016540e80c0c624501d10006440032219000d5004019401880009110340d030317078820f0180c0e10703020400d11040c0c010344600b00c2c0343d2003140315800c00d961108000700300c00344582c1c0369440e1510b802c3e503072506103558050160611000540104000c401482d900006000b07082c0480d50081040301806041414422140c3c08a82141e40502115281681c064004c40d141c061146085940303101c00b6106072414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 35595409 1250 35594159 35594197
    0x301030c090606030606090b1602041503170304020d0201110a0b0f0114030609030d1d070801020703080f09070605030a24050109080c1c0c03051606170709090c05040b0c03 75
    0x110b1300a01800303084171026190200403a1a281602c8038030751107202402c1c0b0403171351103d0f02c0d00182d44500c107000ca00880b024005078030343e05500d8804030f248003102c1501c80f81e080a108200040e620001d41c00c203041c3c1e0a180101002980f980740c02e15240b01035000130600350858040142c503000c5556101e04072030701c0c1000310302100358040600d42c568600741e03040c400a0300700300003004005100c0c3d0030445022001340303030804030440c8030941942811086c1c0c00c505026500007503080c051507402003100b600401e0350b4041003038a09281020b2540e500040c40b0321030500201000041b03102d103080e440385055400a042800341504240c0d030034103d9440714003440740441c001c10b0b004208144000750300340c1c92841c0030f0000c9000c15100c0e40340300808015044100c401e82c041100200019101f440595008031004124442240c04c0c004050a01400d5600509840c405c401c200980950f20800c8401141c0b130454000460040100d030444580c41541c0299800311400280c50301c440c2c0000ac000d05624210040e10800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 35596659 1250 35595409 35595419
    0x1080c0f010c0b010605030606040b0c03211005011202041e050a14030303061c02060f030f0106031406100e0d0b01031a01080d0f0e18070e01030b01051b0709020301030c0906 76
    0x9500c1c000b500c003900041419005002c800d00074402590000c030003e009600781079644e60f03e00040c2e40314040b248210307000400d00c2d030001c003849103803408854144000b42070145446200690b00004174820141000700c040d44000d10031a540e03040310003805035040c15280c240c041d0424241036103070511525000f25000d05d0001120000c2011410781c1d500c004000c0e601d103441e06c408009408011803410551501c1c60b40074600140d40e814002e103588124160741c142c59192402000001801c141d014200781401c000c000d002c0c8407800f4245952002040340c0c4a4581441c085040b2034298244111941001c07540c07041005000720300b0303851030480e8401d1004030045840c0d0902c5c2d1700000001e00c00d01c1c40700d0b4008401001a9805241e000b0400d02c0c40c0e2900407030740c4620400086100d8002020b50400600c41020f20210550048861640460a00302070200c61400d0000034454407a034079031f1900101005280500c02801401040020015103a003076440e075071a0300340a004002980304140c2c101345003100000b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 35597909 1250 35596659 35596667
    0x6030c0e040e121c0606090801060b03010e070c050a0b090102070501060f060503070f1806050403050606150f070f05060a0203070f0905030d050315040e010605040b010306030503030a0b130501080c0f01 88
    0x81c0790301e12080500314041003c0b010142e150020207011a9030440d00c50341d8100b400042c8a040010001c66132440b51492506820f0707402c45110380c2106403800c0c2c040005010304c0400280150b000342d5a49040181004a4100b0b6803c2c103200d028010030006540061043c0f441d01500a007104078000e400070000182c2c3c801c0074540020f02c4d031103402c0206006200298850b40160303d05d402c0b82c2440d0901d8071042040c1c01c02010300c2065a0000004942e0100301441030000c100141c6522a4090760551826841c01c000c1d08903c2c007840420b811501e100189140c00c010212004044140e80842160000e08040a0dc80042d40048030310100103020000c0108416100c1c26400c000c9a80260160403000d090080441e507070b81c4003c00c1900701484800c507101c1c4584440c03041c0410244204000a0120300f8041004252110082401e0405003400000d1000c42c1d000b008480e042503260034000b604422020200310070007890310002450500c0c1030000901d8007004141003030b036a103040b10900340300780d80040155 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 35599159 1250 35597909 35597921
    0x60f030613060209060c0118060c0518100509041104091413030c061805010509010605060f1602040623091e13020102190c051c0506040b0402040b0a06030c0e04 70
    0x190a00907210a00010450759402000e000300301030f00c80d80c981400200f8140c00d50300100820403c10740d08062450500956200c0d0441e5008a45445454480a50600c40503512407200e03043c0320700a010081400240108122035450748050024490301c0703200c1070400030942151280385881b9041114607920b05041c507070202d21503404201c10104004254034220b518140b00c40040f50101e641c0c41640d0380034214200740c0840284070b00000318462a04507009405c1d10b0f6158851801200c3c01e020802c150000c0001b515403a02801e101810144041d0002401900b825403020016900d54540869a000150742e81c0407421350650f6609129101d84040c0076850a12483c001910864100424014000c444005019900500c115001c0c40d01c138010030f000844c0240c00444280c14014800c000e541082c0008080200702000d0f0600103c0050701d5881e203991008200410000c41700b800181159140c0d03114000d00ca40c064a10281c0903100e00700a0010585034100c0c9000c40c050300d030302c820549024001c030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 35600409 1250 35599159 35599171
    0xc01030b0105040b090a030606080307021009061709010b0d1a0606030408040312020c0324090303010b120901091a0a050f0103050c0d0204020d09050109030f0201060f06080a090501060e060f0306 85
    0x110f00d4a8541102c2520350f410941515500030704400e000800700b42d031401108060802c22000c1c0d55204003501c100725210444040304028010040030401416801c100c40030041d4216032038003481d030794400e40c00c00e0050409078451680f02c100061803200b80701d448400c105241060280c40140c41d11a0006c2202502003103034000e0100004102c14800103421200031110a80c1500450300d8500c401da001a040c84050702d50300104e0019a50348011106805610356049144400918915418008c0515440c0710780d4030003400700401072001c5500d600d02540040c1c9900d4009800d042d0b020550f03003d00b4461003003550854541340c2404003054058180500b105d040760b40c031100502000c0c0005060110300c10845009984c02503084c400e680e030203041e41c02a0000140300f400001a109920311b00a08000d80c01d40a210171a032401d07405220034000c254002c0c00f034502c942010101c40c1d072290030302d8000e0902c901c0010700315424a140041c950b450415050700030441210088401c08000c2c0626980f59012612 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 35601659 1250 35600409 35600417
    0x90609080f19030c0f03180506030105060d02092202030103200117070e0a0b03101e1a1b010501050a05010f080f060d0b010e0403140702010f1101021905030103050c01030b01 76
    0xc0c5184000c00500700424051103801c2000001502d600d840300360085c2c0303080940110b6944280205080391a070704120203400122020f50840d418030002c00c5860190b21008440d10b035000884002c0e07170390b800e402c0640e03440d400f1040792050b100402d02d43e4081e400a00c012180044441da110b00c6119005008a640300750680d034072140b07200941241e800300500541401d0a0003040c0104100548604009002602d00c0a00c0709569081c00c044c544002036055028174032156134a0441201c105503c10030310200c0b40c01e45480c008082c010308583c5203d1041a03c2c1c2c40d0121150401c0c0c01002d801034020904a070f4044801c012102d90fa103005441311810102d07030740009800600012802d0100c2c40d812034000354080e01800900c1340c035075194140f99500307800c40215040090100320800d684810442c0c460b0034441c0304d040c00c0c42c005900291152507241124010300451901f9516007a000f54143e50142200400c4046044180000901240e000f8081034a031030103142c9c0380201c0c0d0350107802821600081a96 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 35602909 1250 35601659 35601673
    0x50402061c020f0703020a0b0c0405010c08070c0b1602010e0a0807090f0608030a050c010c1b020108040302100c0c020f060f0306060309010605060414011707120b0a030f03090609080f 80
    0x201c58040c8600160a450605900380710002c0c1500310a400307444018460b070010500c0304514209003001003c01080c8a42c3c260041105000d5641e200c3e0500e03514940c019000d0f91200c2c203502e40306d40480540d4000440c01c240c0810480700c0d810914009404840c000c1c0c0b00e07103040710107030350a00003400828003038042d05510030030b02003103000c41c0d982c00008a5000d0300c1000a040e40c4075068030f421540164000d0f400500c010944d941e040340207104840d080d41c95402c11084983c0025005801d082c0081c0c4041c0c1800780c10340020302410700078014200ca084001100304010003103a007001e89580c0c4066005d9004141e9074020100c1c07818118200c03481c074031210803a9030541c1e455004103c4c1c20ba100034010f80481d5200d11000840d62504006880034040e10302c0340340382c001110300005050000107140e41c0d181030f40031b400303020b001d503005201400007005440020903074005400c0030511031107165000034020982011001c01381a031144c0f00a00b0780d20240d843e480c61658401ca00340e9551a103207020703229504402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 35604159 1250 35602909 35602927
    0x1050103030203090111150702070f0602010603051509011418070905040506010909080d050c280807081e0103110111030403120c0f081803010b10020a02090a18030c02030d0305040206 80
    0x2071546d5551360418012649508500b9041004030001a40c4140160f40120404d0140c458500e182c800688460300c003c2041a141d919480d079510340144098a003040800c012402e07015080d0001c0ba104002c01c0c1c040d028500304000403403000e00002c0b0501c00c0341d000300680811205054020580582c1d0004000c081c1642000e034008001c1081d180c040740d11101c100040e1420079a5030003004d219417200c4405613218000051040c1e01b0320125907241c80102d6448400c140780641220540e40c1003c43c03031074038096076500e80482c8400b1400c1c098410034903550280001041298501c50f000440341c0071b0b650700c5103d00300600510b9490145003c000d0044003170280c07000b49540300d5450322181c103000e03405c50100d0b040284ca800c03c096100340407000780b103100070301e12092900f400d00400148000940e5a684d0210307070110000d454246502c8000e12504084021132000d40d0950080c0c3c1000d01c001c900c050740f03080b1a00e00900061950103040b03001e030050082c42c8520078040d1040a21035500a007286181040754 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 35605409 1250 35604159 35604167
    0x909011401020c090a050103020901060c020d030f03060f030827060f070203010209040f0b0109050102031317010b030d17010506070804060309061d030c06010e070c031110090f0209060102010501030302030901 91
    0x3404550741144a4011003404940d50100c01c140500740c0c104000943c1e50545c0140035040034141c00510601141602c00c00c0161201040f9042d4107070540307443d20f48044c901d40d044028101d140c1c400c0c0c2c280364000f14040140481c203801403131824a81c8810710007038500110b5280c00c0640229200358847c80038415003468031070034801018690b01c000d000510b03140e85180001e040b50741e1340c2d5240c41250f0b030300c1c0350311410f5582040c081000390100f40015401d100010341100301c132940c0c07400b98441600c1b8074a039100580500350403c4540c036400030169690044a00b400034210500741081e50919035480000083c141410000ca4051580141040b450607062a00c140c01510301c1d81c600303c8010341d0301c176890f5290200090303260700c0e6a6180d1000d1666080d016441c645403c4060b0841c0d02c0101d01c0600340301c8200d0300110b2030360b10381c0d03854100070440c4990380030618140000c2c1084002d5203404c10b0350003010405c0002c880d80595208071146003094a5480c012402c80d442408000e015074000c108001e01c541c06 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 35606659 1250 35605409 35605439
    0x70522020904050414010f05090705040c0c2a0f120209040812010e01060f0327170f130915090b03010605041b02010506010809030304030815040e0703020301050606090901 75
    0x10992015181650400110702118001c840030f44a148844001011810342030241002c00440303048188418280030600c10707291a082e208447c4038950b5440c0e540207448c001d560300f031300d10386d04440b2980910704210400384506800308406d8521484100020a0f20102e4804003010b40b00050707806440400a54280a130217480600107803114031003070102201441340500824060320700f030403407035486524005e8090b1142c0000d03101c0006040c105240c4888040c0071404600c0e45252202801001e5441c0f03007020000d40d482c0e00700328240c002c00010200c070540704c4200140038039102005845a031750380d115035501c1107600303014021400001030f150802040e41607411640e450400140000740d810b5441000030110b40c0003181500c200c5203280c03100c048035070f02072190903030114003070809100c6841c04a01041d164400201700405101225010502454002c0341d51201d99101610403c00034981850490ba00c0d149480128869030803c0001151400e10905a65180d03002070300140300c030790a1215812000c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 35607909 1250 35606659 35606719
    0x30c030818030a060e10020403150b0612090706080105150a030c05041d010314070b040e0705070f0b0a050a0e07030201050c03090a03030915050702010806010507020a0e07020f01050105030705 84
    0x71072214019040c1d9028050307011014440d00f40040d42042d0403160b00d003083c0b180b9440c903544501c10f200c20030110b855000d81030160500358000107030011038800050b1060203a013243c7e4442c1203c42d0b08101c0b035000002042001e60356107840f10030950fa40c4004004c1d00d804c070140070540b0580c0c20300200c0346481c0681c200581e4400d0509016041c1600d03484036810302450202881c1802d95401e004006210a0140c4100d91036204009081d90700d003480d02101903841a44140c108242185000a480900c41c40c15100e0f000da100034600c142c1c0d021800c0001d6401d4094404030341072403074030000c9040c00c45284a03c0071503c2000003d0403900d0b10307580040d0f42d103801a0011260b81d00003003208510315503806200c40e01031482030302e03880c200a04007400081d0703102207000650b09101f410004880582e0304034010a51108003464090364404852010072000c10442d444100403800d90fa00340000503070041030034920b03000481c000300003680c4c0e21010103944022900c0307619000422460202d170320307440700c0c80402d861803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 35609159 1250 35607909 35607937
    0x213050d02131505040e01020405090103030f030204030f060c02010f090c151205010e0702100b180c090301050108010203070f0c0c0306110c0f010212060607021e03100e060406060807030c0308 84
    0x180380800d50302a584440c100250210007080701340072618082c402c600003c9075540007141000e084c01c0118040300d20600024050080e407030400c842c814801d8044038040c613440741a00c0d17010017003881d0034000b03040d91020100240d42880424200c0030b01c9440345422858100b11450202843c00d170114420100d04685a820804e0110400c8103002c080c0c000c0d54000e02c1c2d500303941420f9160502c030080c208034200110311391281c02c12615160507038416800c1c3e03080b030b440880e1000243c0c44100c680207071841500192505035080400000350544198051440742a080e1680c0810b00c088000c101c9003036441c2d080040840700c01460900c0030900c00d03807100508107414000d45140142c0440700c4c2e85458001d019940c1e45030340001307840d61101050b0590541101040d0398440c144151540040c0ea0001c0703124484200381d50b4480e82c0c0340d042e0707410480c804003054411010852070300401c0c06c00313880728000c40341524590306000d400205c4401c0000c07864105c942000d40c41040350308517a50b8145a600041c800441c00d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 35610409 1250 35609159 35609179
    0xc05031302060a031d0615061c0f1d0a02040f020a020601120503160507050312090d02040b062b0608212a010203070801051c0f08040b07081c0213050d02 67
    0x20031417080019a904046005001e02e00d4000300030b080228015241c0d80c018002801440c1c060008485801111a01d6000106650f07080c981c4034001003010844900a00d50003400110b213500d0080303400745d40c503070098030188030060440041c58242d04c81d00008030010307400480108103c1000700340009000e4030070820b403483c09500185d01007040341380600c141d070640c006802c2006585401c02c001c2c55010007a90145003000000c0b000a04000c081d004064046c644540c8920f106a40b60030440e16061420110358500103140d10350180b800030b01500e40001e01d840c1410110308000c0020722514110190070040c000f030442c2c40380b024a03d802c84401c26510000c07260b003141c98032b110310784c005c1c0186440c6000103031039181024000f000034806a21440c0903403801622403c48507031507044c2c40c249a400080300c110411441c945403615204651010034441c801060003400c1008801c01415108590784505408081c3c0c0d07512035049105103403000d20280d020203020001420b180102030b1b07003d0700051a18001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 35611515 1106 35610409 35610431
    0x4140a03030c0219090f0603050f01140402011101060e040b061c05070b130f03050d080a0c05040302040903020a050f0105010f0b0705030d0209030709020f09040c05031302060a03 78
    0x10300d0903d901d202e8040c04000e04c0401401000b50400948216111000080c400d03401b00720385074010000c506440c42c105010f00d1100400280d0440c100b0703102c1e90300541e0801402e400c40c0d1103654035a000001e07540c410700c0d1043d12a07401214501a00d20b040000c024000b5400480e0b4102a904484040013003400085c03440c040c4c502c10709a85030390310441706401c8500303c8658040801c117a81488080f00308580400c0014407107515840e190000c0d00c0b1503049030180e0301082004400035205020070800351078103401c10581e250003030041d42d6242049840e00350a14980361540800783e0b4640c00100080d42e070840821005111481585007084543e90316517840384110500c400da42a008500000546e40500841c2c5c000c0151910466031588a50b14111058004092447c401c1d132604007444c90080c0140300300c9102d4221410b2025110b40150708014098201510300d404165482c03541c009 = true := by decide +kernel

theorem cover : BRFrame.Cov 35431659 35611515 := by
  have h0 := BRFrame.cov_init 35431659
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35431659 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 35431659 ≤ n) (h2 : n < 35611515) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
