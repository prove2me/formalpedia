-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5446
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:53:26.152989+00:00
-- url     : https://prove2.me/submissions/c33aa15c-1b80-4349-a0b1-f6da64ebb37b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 979316546 ≤ n < 979496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 979317796 1250 979316546 979316599
    0x9092b11060c0307110a0206030108010c090f080703020904031709031902031c09031e031b051e0d0608031321150c0c02130506090106050c10050c09 65
    0x1420242251081034000451500404030603403880d081d5038400380c0071944003022010121043c804d1129103009602d03403000079400b0703000403400840d001c01008806820148107a20001e580104044104074504022551005403681100c91080744d4840e07060840b0b44c00d078402184e1549680010a0001a041c008001c0c03032482c1000c107208100ca0300b0a181030f0303240d025148010714a140b1402c009501140a980700300750880c440d050084030780400451183e4043d10000885001c41c0d961000f0380c1056410301d000e40c61030840c524001d490036803090040e01c6031204620801410640126101c010314195402130317009855505c0480340c075640410100c1c0182c004900c240580034503407210102a84800030041d40089402409204150b5560a0900000c5c40119221010881112803400c010313564185002d500b1906214007060504180d410400c030440d040e4801c1090110400c100300301c211001c83c07694507010035180c1c00540c59403601c1009605201e101e5116503c000e411420320a000c0b5901102e81c1e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 979319046 1250 979317796 979317883
    0x40e1e06070314060409020d0c031a01090207051009030201110703020303101e061b060e01020c0c010813260304050609070b0a2f0607090302040b0a03030e0909 70
    0x14181d0300d480d1826000c4808840085020a10440000711030b0f041981141400600c05094040140c00e1a2a0b01070310b410a50821100c02401c2d00c00e4030b01c00403d1244540c054010001e045252a541d82d855990314411003007401c400a499005201c03c1c58000e51100004540021039107940b1810307407a000792254811a800488107489030310210300722103544142c862201d003806072450340300d082100c01e039640e86508007000c00700160b0051010000c0d1060180d684071030a402e0015031500301901c500c60820f030040c00200d0402c9036130010490403107800040618030f00d4001d90b0369542d00c02d01103090300d0081540c131810844420000b05000c100103000815a100f14508000c2d02c0035540c6a414040c1d043c07240201010001d05003040700c01c40c07513030944500404000501c01c000113450380c010449040c150100c0f203031008541b489908109506080c0110f56a05074101c884e0744403036055581c050615000004924010394607500000c5941200f080821900801001d44040510040000d4800b0038216504070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 979320296 1250 979319046 979319053
    0x706140a032301140a0905010f1a040902070c030209070215060d020409060510030b0f04030c141011040f0501030603150203060105370206041104020d0609050406020a080c12060609040e1e 82
    0x246c007030389a205aa040e0742406500010042c98600b0380084000c2c1514060480307142000006407141e128801000054807070b6892054031842d42c010002c0382580206441c095401c12048624550244103859500c07100440b8000f107804220300100f0002d01807840c009180518110038003481d81e5000c98240304880c0305040d10402c0303030b44402c0c00540c0100e042d1401004105010300000000b00e84980c3c3c00150701d082c201f01e51401d01200800c100345e603030840d40001440c03000030f030074031001d585400700d500a4002030909003c0d0b46d19507601e200400070140c9520712465800700c0407d03d02d80c07040381144c00c00400782c0304140b144461040303482820040d46031f559103403d0148180050079400414070601c200d40080481c0e44000381c0d070092101035446203241003113403a540e03003000c580500366104d2640070394041c02c070060b11650200c3d0050860035025003180d8070f800702448825130b140034504c2c401d64002800e4960584842c0c8080c04900905000d22500d18103008640413a0760000c035540900c41545009000c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 979321546 1250 979320296 979320299
    0xc091a0310051503060409060908030a150501030204050109030f0606170601060206062b05031e120a1116170f0a0f0306061d06190c050706140a032301140a 68
    0x2000814203d002c030304180c1803810301c0003603c640740503401030601d00d014010100342c0000741d0391510100d0740116048070300c40340c6e80e007059651082c8030040032010740000c2c00d003145400d080c0000a88000302e64071001300040c6804c0740c45400c000198001174000c051811100314181003041c229a22107600f40a005d0046c0b00304800500585880d0300d1007080700d601b000d17501002515900d18548006020032003903130184405c0080d020312095101c00d0348980310112455940f03805002400500c6100081c0ca03080206080005c84d0395410540350841d81080450b0814011400c1146004504d10311004140030035030201240d148000740c5004020031b85400183e54012442c05c2c00032080e02280e503607000301b000042c002100360b0000008000041d5100b00028545414178400c0071040306410181e0300004005040c018421040010400061014100c02d007824181910030400349012801aaa011020162240b440c02070b882490703a0148040c08104485c078040b03603150003200003100400840503001f02c150b500b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 979322796 1250 979321546 979321549
    0x81b100f020a0909020c21040302010809070e160c0206040b0d0c090305031b1c0207150302030420040b03010f2408030414061209211801030c091a031005 67
    0x2140d003449459103440b1051410030040300b00a411a0701c415107584103082c0618402801c2c00c12030744112808451f800d98490440c400180342c2d10001e48044400d0740564400e00144403061109030784151a100c5001d401c00c00e1010803a0464529403010390002e500040105811003517038001c040c1c54503980c106104018480b00c4c100c503004580e00c0042e02c0c0b070304244400c9150300304100002060703600c1c140c00c8038070842d0a52040c000c2072483d0454400941d00a400c00c014060140310a0341c01803809090850452500703444a0501d80ca0200c80324140c84d140ca03143e41c2c007a9485a00c0040e003404090020064060031182d10001032042a2070305003d2507585000c80740040030405a00c09564101c07020b14202450070058408040c0818001d648c004024803004c0304084d25a01900e102c0c00c10300c001001300c51130090650407421040004004150800c010b0103000550303418003441d00c403000f80ba0010381c0030b034142d00448a801e8590080800d810b04681d030310078090b0400c80614000c01c4401210300165583c1d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 979324046 1250 979322796 979322801
    0x4080921011d0307110f0406030c0f030c080604081602060d1a0103150302010219111c0308060409030c0b180312060f04061a070510181101020c060412081b100f 70
    0x350091144088000038440342c01c10040002c180f401c0540f000c84d81d10327103d5999090104d0745030050141019014403c1050241c1c0f6200070000300401c901500b02410161910783e0300303104031a0220704404404503400c0864a40364100e49007806800c004004084c01e424101503011400c0e82c01e58006402c148020303000308105003002e8102d0b541600240824100d01c559258224a1203106840400e5800100e620b141c9804240e0600181c52010048048005180c040c22079040036142502981c513001c04080000c0d00501000030541c0c018041041a5030707601420340f08001c0c01150545140000b10315a400c1e1914545068040d100480760645030080103030910086039070724483c0d11070902e1000041d42c2c0441001000b030070b0050282050719846040c03801c007401911803c03456003410403102c40c3c030241441115480030042c3c01e0244080c221007211b500000e491800355018024940e5240d444403030400c00f400040710798410441f102c400a460001010fa91140c00341c4c05880350032800c0110928003c010f51 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 979325296 1250 979324046 979324057
    0x152506050a09120e2809020c030304170304020607081b2401150206060d0809060f031e010f06030b01270e070905061b162d080604080921011d03 63
    0x25108611000f01c5c00002c8820780780c1c0d2840c814044010f000c0c0400c81c101140000e080103e800d030015035030b07410a490551680101240c1c244c558000910500c0010391ba00e00407500301c10740080f14180c07a040110312844030710490140342c0c0b02030f220b8000720882541c00c1641a610000041c0301e00415682c1c3e615032041201c085009500041c2c122070009103080ca0103000300c2040e14014004241402c6100d40403413080d5020380030000c11241d021041080d18005036000070300035000b80000c00555450325040c1481605140601800d250321380c424001243d1042c031100000c01e0301101ea2449048032241a081071480a0068020700310280d40000c2c0214010000d100440d00040c2020b49002290354130803540d41400280c040541c01103203583d19032014403802c038901a041140300000c0360850058031010803685c808031516901000d070010012000c0211300542d01c00e400041803982d842c44075000a400c070b0049840d41742e2400d4100c03481d610304030741503210750404240e034a0010071101d000302e50760360b8071f0251 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 979326546 1250 979325296 979325299
    0x501060f0c080412050703411b040f0906230106090509060103020c0607020f1c0e120f0604050d0201050717060d0c05030a03030f0b152506050a09120e 66
    0xc02c010000b0501031a40800b00783c5c002e40c1a10341241c0c0303a5848000c0d141c3d4800c2d43c440e092581d2081c1040d40ba14410b01107041b00303030303800c0942155140814000e8072040013a40e140084041c0c031407080070b50303280c13608101405240f0100400207034001d840c24000900c2c1001c8003003d4240c09014403400241d19074402416201d20391904406103140c2010001c29030802011f25041603000e200d40319810804005040c000c0c1c2503900540000380604015600e40848100300301c0d80d00070030800c1b0a45c86900b10880454040c0295a04002d004411136a18906910501c55002d90310403501040705200300420142e1071311100381d0080c003c948907900c2c215403001c564840c1920040000300801c03981d2808441c00750105101d40d44240c0001d03620740c0043e0600107044c02c04c0c4c2c08680c071040b03000d200c1000307032240d010205402c47d8013096001e001c00514043d070107803410040344400803d10840c503d0115001014049500034001c1c010781c80c0c590315850182c00804c0c82102c50349000c62040e5600360107a407411143c202e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 979327796 1250 979326546 979326563
    0xc03070605070201020f03180c030313090203061207120b061e13060e01060509031515060706090501050403030b030f1c0c0f171c1803030c020c090103060501060f0c 72
    0x503511a24010036010309180150b640c200040c41c171144080c40a9403050340300c41448103400021018980c02e1102591a0602c2074100f08100052548000e05010554103040001a10f035a03d03040820700203641c0c1c3e210400203101e00400080c5150f1a64550b50586206114102d003c0d15080d06010460a804020207030a031b8964040065500306440d109410302603904021031200d58a141c5280c09000a810071310000c0c40c00500c2d0851800c04210b071402a050510001c5210f250684a011074200040c903624451840000e0800500070540c02440403e50400003c10003812b085c0b8003c0d005020000c06e040c024060526210300602c03011903805403030807000048020380003d114088500b2401e07450f04544801428a24001083c140c4e00b0b00028440c4081c0784c0b540d10075072070a10034410307130348111003290480c100020000d0070101400210500c1d0b5041c20b0108100030b000317400341d04010389200b5840e0003109280000040c01415007090781212013139111105004041001202d4000c1d030041d001c4c2c885003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 979329046 1250 979327796 979327807
    0xc020d090b072901062708070e040c0f0807090c020c090708181b09090a0f0303110c0616030605031216060605150a02120702100810050310021e0c03 65
    0xca10030828102c0c0035820f2004030901c0c0111000082032102a00950001102c241c11b5102540074203845a045401450390704800c607280500095031004103008401d20f0845550100c0c041121900303003103024103040340200085686079083d11b6950801e51085031002420b09504000b00360000c110b007440c60070050720b580080e558400c0d00391030045010f0240e603e06805040c40804000307060143c902c010701030740030591003240c1e01c41c10003011580250140312150416075441c00042c54040c0003c0e0902e51608000c2a01d010402140307a2901480d810b1844d50302502c03080200800a600c141100301c912a101007049603104c2c000d066560480400310b400307400c01000b801d000c1204481812510a01c2038101050160711580070030303402456502d0b50350302d10b207003c0b8103c540e480d0144000c06010303034180b031207034200101a000508980103002406d0b040c402d0130004691a00207807000400503210142c21030705416141c25403a4020744c8060201e4248408900c01510981c00314011200c82d81080b000950611 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 979330296 1250 979329046 979329053
    0xc011b0804030923090c09120606040f0c09030b09010b0d0321200c07080304032d0206030408130b0f040f17030712020c18061008061c0f050307060c020d090b07 70
    0x140301c00b90041010b210103107c60070941c0d54541d69408400341031400307030202d03040c40000d000964000780920008107090895001d800d075400440700341101e401074194002611038850741030051000d00340c800e8111103845115424150003040d00d00c0400c864024194074103410384201011229003150743c040703198000f000000e0301c5030503102500d140116001030752036540d95030039114a1a4015401240c1902c0c0e045003000004d03450700840f036844072074041103204c50717143e6600080e894800200000d10a480c00b15504544081903120b04015050300a18280e40e40b20700f50a030413154100740b2400051400744000411016100601035800c90b26400003141001e80995031203c0087c442d0000000310b100f0711040d010b040e5542c0080e1280f1041009010740541401c80a00c080c04103001203050a100340d5000f4440c0540303560440f5140c900038074440300355070901c515200c0111480900050003620020920348180038965101c88045e803182d4084480c4005042d50613520b80c2000e02c0f918aa0381c2051080c040070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 979331546 1250 979330296 979330309
    0xf0c0105091f20160603050c0c0a030806030c03010905030403061d0709060906060216031212140703060608100e0a09020616150204030213020c011b0804030923 70
    0x201003004061010340d00b86044001030003048000d03164006048042d0004800f20300710080c0a00300e420300040c0c0340c10700c070220740c01c3c52a01403072294104041e501c42c005045880d1144c05d842130000500251000102c19050080c009a402e8684621034001d03001286924903051003540f03903075036128000c0c5040910316100e0600400f1020603a00481741d4124030280507107010b115800280000400001e003250034203120408031a12608003000b998007a0b040c1002ca08a030101e81d50403240d000d201c00454105400040b510b038a007a801ea203010b1420038201020590307804480174442c0710f46035402c000d010380d221006c5895007010354a0341c00038041080240510880841500c0d8021039102001c81c0e084002e0b400720300550300c00041d1908101000c200c140c200070105554095403a5450015418141150005000c0b10201707040c03800da0940c00620407060307400030b400400340066035180d01d160307010b908600602601c108880440000c1d16518021942c2c004e8648007220324842919402c50c42c40164051002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 979332796 1250 979331546 979331557
    0x100f0911061303120503090d0e010c02210307110312030f0a090c0f1206051005010219060f06080307030e0102030310050409020120030d061a0a0f0903080304080910020f0c0105 77
    0x10450b0b54200c08004a400c070728110740c0c0342c2542c4e40c84a076640f13000c400182c144031100c200c6004200c0c1c280da1031041c3d83c2e84030300c00102954041348e0450807030700c05084078a40d9507141c0450000c1401301140c3d06c0c0911100c03c0302e09003280340c01e50550b02800381040d00e0b500e0354441100d40c850811540d40200e0251000d50b0301010309030344120810403940b42c440740c0c03880340804580d01076551100400c0d8098108400350040b84e422150059810351113505010010303480d2041a90b41c00610182e4003560014082207030440720f401181018100501615849100c0d22a84200c0c001d8005c90075106180300254800400c0300d00c0b52013100f81001601d420101040054039280b10709034100540c01d4601c090310700900c808200803210f098015a83d80b01451900780c15104a0752040419540200001c10030f40c415000b140e605440034035207170105001c009010341e410200c0790005855a54044100000c1015880061404840449100e1206040725034200d0340c8040c40c090b9030042d0b0b080500b41440780c0d406000a000f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 979334046 1250 979332796 979332817
    0x11a07050114090f06090c100e041b020d0e0117062205010602010b030c0a030b0603340e190f0f14040c0b071a040303061205100f091106 60
    0x52412445850301801d44010144080014000d0300c24441240c00c104a0741c51407040754405401240f50945800351070f41c0401000390302038000a1840c0b1a004d200da29100502103005108028400d125040c00d81d20351307010080c18016104181100404902a2000c0840140140d440d8000d41004d11002c1d2540c41018110f541c210001146200101015000c1070079212001440001c0c13561400304001d0039110341c61016402500805160304440d103030350000c03800762031f041050103000743c88c0e04020a29114071441d8030b0100c070020042d118209818041c55a110388440c2c041c0300c41c9540c46104011b078a40c3c041c0d40d2a80780301d5020426102c03262054010031100d00a001000414648a040307407030546071104401050303003410208000c10002015184009842d43e000c3d2039080c0b40d0710f9a0b5400b01c9410b1001c0103110010408000b0f02003500ca900800013810f907080c4410b0b0110010f280040e5200c1410003030a8040341414030400800d00b141c400d9903840d07a0092006d410f6110140c040c40600c0d8883c28841 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 979335296 1250 979334046 979334099
    0x203120118090501230105011715030f1603050607090b160204240f090b03060f13020d060f0f020f041208090a0e090d020705010f0807120501080d0314070801 69
    0x62011681c00e00c0307401903284010004020045c842880041d0a002c140c022030706109102e1030000e048143c4404c480d0740841d46820b0324001c1c1d1090b0000034944004154034091922a0380b800000c0d802540c0c168008072440b5030115855038503900002d03034110905000e409a0304000340490100e01007604208200c8a00207040026144448415010110000400107440000a450030000d11040c0404034008000780c0c4400c20100b682e00340000e4481c10301500030700c4400700030001f06044007051001d2050555008016006001413454488060000c4007403003565180380c0604c810b4482d01c1341c000c030f440616451441914141c02c1134407050314201400c0065504400901407201e0540b9980c440300040c1004001c02041841c2140203240741569441003642190070905040150381d8200c00300c1c52030004c0078140760040c0c0d510048115100421001e406080c00c0c201000003d103c1008542e034511010b0f6a6810b1060000300c10b0800016501619120001602072740104000c90300031508000740d41202c0d010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 979336546 1250 979335296 979335311
    0x3120f0908120a020f15040b070207151205060907050d151706040c090b10050d02070c141003051504090c080303010b0d06080a120e0301020705070e070f0203120118 72
    0x82490507240902c0c15196180004041801e80e804100400d034928105004260648600d0b07150b03802c442c40540000c11801c070f0351020600450007481100c0c05000c5c00ba603107000360200311600418030742d002c4490307040d240c0c90200402d00c1c0c0c7c140000b1141c417401441d1140d602e054200a0864000c011513148041030741e05148011683e0490342035800141009000200303518241801d069140410507440500040e01c0e169550820f07880d1518261103c90304c60800c2a02ea060300884900a48070b002c0d13006003012021800421043c8070b99800b003210441c2514840d0520205a005404862056405451218581840402501d840d82002010510811380e03400c1c495558500b4519580003a04003903074001c03012918440c981424441c1390003c200c200e0040000d03130055281c2d556405800d4102c80f04001d505a0181c0d002d490035012a0110350703114003244c861541d10a201d614501c41074130702c00d001564070000c41e008140700001741c8440b49003103110805503920305440402d000d0700c4110f104d0b8659071034959 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 979337796 1250 979336546 979336559
    0xe040606112d0a260a09270905010c021e0318010e0a08010c0323340201060816030c0b0c0a0c080a0c0509390c15070903120f09 56
    0x1d0706040c800e101205104e59425150340801d86803c00c00c03401064103204030302130144e1107a0500c044600c5083c5803821b1100340300c00380082100e48011a4040340c10440850204481517000c40c0c0c1c1d0152560070382c1d203410000c03c0302d0010102081105041d40e0700034020480d11074074030721030241401814148009209013201c003040700c1d074a0581c8a6501c2d650340c2c104004025406010340300c2c0702d14055410844040708a0131102c1c180b08050100000c084184017542e00418541c4002075092009200002c0e039841d14400080c080e281c01d005058441c0194000d0603660b4603416030080a5a600c1030455030140c1c2056070b040c10b29000803808120074420002d1030000306202030b04030009011400b016110614290620701004459588114000c00381d9108105101aa0f00c5c008491044e1084030040b128100300045c400c83e0590740030741410007500049101d0b5010002601503072402282c150a0708554441106a8ac115034902c0040c02a80440c90404201881001c41180410303050801450507a11800c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 979339046 1250 979337796 979337803
    0x110102040513021812030c0c060a0507061e0219090504020903060c0a020c0a060c11091009020d06030c1424030a0f090614011a0301141002030d0504030e040606112d 72
    0x4050312065000058607160780003050098180c010025249d642c60103440e00b400030181d2041c400c0280040d651201c079401039002e011503510340320982d00f0082d5150001e80c0110444948503090b014041845c20300b0003e060301380790080d01c480c90001005881c01d41e40d58102c41b40300d030340701c00e10350011401500710016070355550401c2c0101800756139580303500d42c50303081c903160301c854080191151055000b10208865031030030560700e03010340d10000c0000d0b864262503131444015190a400003003001421010128142651410315042d041c0100c801d00f0340c80110742c54900c1125910000d91518083c10400528148a1a00306401d8054501d07400600c044241d1601000c4424590701c110340e1080d64001080300141448490400502d0105003038036552500d5460302d8a00000074809001d480d08010f8504001c3c020b100703484081401d480c040c010386c641440d00038111030a01510a224528040011a00d81d102c2d80342c0740250703c00c0500401c480c0310b50645c03c19200181540d0203078804000e0a40021406062 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 979340296 1250 979339046 979339069
    0x181f05030a020d170d0510091a0d12020705060c0c101b0b040f02060c0f010e030c0616031e1b171305070909080702100206060d030c0611030c0702011101020405130218 73
    0x52414048142c203004000f01627550104440b140c0800440c102d0b409039641c1240e08800d542c0c0150115040005a00141d050041c07542c80305522202c003290202d0154400700c4c04c903194801c01c448441d45400280700c16158007046007a09012020f0741c9408500180d402e0502c1500240201131030160100c0355800900e06a000341d400c1c100c00d4014004550041c0001d01680f03003d5040d0034055400c22035240c082c1030360744030020300d4100300d00c00c5007101c2140c482c003da002c245a40070114022310741b0140c17080b543c0e001e400d0703030b4a2203c8200018418007028034030403032100c40c482146021030449901c645c100080000740f0a50f00f034445001c1c004000800c0d184a03c03403509000d101d85541a282c3c0b600340100200b0740544500c00c01590881d404000e42942c81c0000b80d010142d042c1000d600c80400b0b800d00380d00038075510800c480840c0c030000600025400050141203401c9c400d90741c0700b00040e1802820303030907401207214451b04072081d850500c0018104e600134240352610002c9d41c40302d10b00d100b0005010f42009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 979341546 1250 979340296 979340311
    0x3061203050a080606160201080a0b030a12090b0f03010506070203070504020c0a02040b04050411120727240b0702030309060d0b0a0602010b010e0f181f05030a020d170d05 75
    0xd9403010507401420b401e83c4080d0172103860341002110544070803102d48501009042048010020307208002c83da0000001240140840d0302404080c0b4018001000c85c41c24a0f000c182100f030002140b0b0200400c403070510000510032421a460003082c071501c2c0e00014012a410300903101c01240c0d03905c90b840034109031921403004001c0c01c0810b005020480e06901d2a56008900700020000404c00781c42110202010513030790410f801e010442d07c18100703402900700b00700c001d40c203600b21280d411211281c0c4808601105080290350322038013100a41d10074113001c5995040c0c2d40c034030811424400001411155001400f6030f85428070100c0058000d0703210b10314000d492555411105158200440c0c48800380c00e8900080040400b0600040e0000700120841c40c0320341c9400e1404080c98584034500f42000122a0080e0b900c6d04083d080c8014519200c1c0c0c14030806c088040e00001d0fa842c0018603003820b0741d005001c0505080f000d4030342d41d090340303100c3c01407200c203600800007401000d410b13100b0580325402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 979342796 1250 979341546 979341557
    0x72a150501150507111005040e0a0507110616110724090f0e06040506060d02030406090b07022d120d0e0714010e040507091d0a0b010c2103061203 64
    0x1401c0d50b550044145854280400c0f0041c8051000076015072400c90492034204c0702d6a80c01180c40c0300444e05803046d90010614401c030001403061022440d04454000c0b0001c1d100c80044090545a03581d41740e20807204051094000034072071203400c0c0510000ea6098034014240d8000320307100e260031100c24840e055030f560000050b6a50a42c81c681c081e100c0c034043c2410604140d0800e240c0f00502c070007901c028000c284125902c01c0483c15560b1182d04079241040d080724150345a1620b42400e03001044414800e840c0400c00c0d074000b44072244041190f9900005044080300e0307054a020302d512000b05582d00b012818400c00c1c0c00d107d90001580041c040310b0201400224501150a002c20b08014250b4080b03804104151201d4006a0f000040c140f01c1403810b803000a074030707612440f003150303109026400030f00001c040380b803010841c001e480000303446684140c00500c0f0300715030324004580714140782c140607001c083c10f43c000442d035940c500d031058a490203619010804a494968800351107042c250100c0201d80d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 979344046 1250 979342796 979342799
    0x2120a0801030b0a0c0512070c12180f18050a02090d0b0a23132607060506030a0209131b0f0305160f0501030905010228080f072a150501 60
    0x11150f0120368031005154082c403040ba40f002c00540340307004250a01540030720b0b07040041c41051140c2c420303510707480d000100080d0451200d80040c00c0c40c10f81c40c80d03044090102d218003041ca4010303200d2000480c3c221110001070145403500080061001800300c2031083d408001074021699171040942040e80074018442d007604202c001102150302400b41242c00240b07001d1084e9a5a40b00604580c1c040c000301e006080f040328a1800315224400415541100c021a0030401c004191b5075024100c01403084804100b039440300802c05a80c0c40324040020f5114050400203503c85440c040d50350445807003200840021543c0d10100c048415050300114041603003071004109201c020020400800d03034019070070800c00d0600819a040c12020300545042c95210500703801049030944c111002650703445001101e1041d074000c03040c4405140303004200081c4034a008100e0080110f43c20038010301d9262109041d284c81c5500d600d450100c0045d580c03091404c1d524036000460010b0300d003000041e034541c800240c40d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 979345296 1250 979344046 979344053
    0x602070602041d0106020a0b0a1e020904150509010501050f0c060103030c1a0f0c0c0c03030d0e0601050a2409032009100803070803060f1e01021b0609040c02120a080103 74
    0x1280310900440051144801001000d4001c2010041150041e12458484e980c0020900c00b408900c8540c0000c1c0c01c5c210112005800c44bd805045074220484040c01032982c2107104d000900320f180601030b03200c2e00210042000d58090802005c40b1076000001e20b0034a00c619007420704081d002d0340f041c0c0c003045150204604012240d00a03480c401500003c050045c1010b1902040f24400140526506c05000550a9820324100800540c0140040c00c40f981c42407840f900001400d400c1c0c5400100f48220400464a49072014061040e0380c1d4050412030070744002e03462203851a42c010031440901c800c0b80800b0003c6815001c007130088041819501501000a01c18403101110080c10ba1510604840e800c0c4241a000300403101900c0d002095070b6101d484000c0012640030003240440e40c03055011413001c44604c0d010038940b00040e001d80079100c0c21440141c00d01030500c3c410b81103d0b8400c5042100b02214503080d80300b13804900091045031040d505421304402141d00400d030b5600030400070f80040040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 979346546 1250 979345296 979345319
    0x3020313090e0604060906060503190209010905130602131815050402030106021506040605090f2a0901050d0f1a13180b09160303110f0a0506061c060207060204 70
    0x18034103031070200001940c41c0040c41d201c200140004180d07036200c0c003007041804030a030094400351000074151091407030542c1c41100e00004060040b801075400f500000340700103403071140a10560608650a0b405003460f5a01c0e002036202d8044200654400300c0f01040846585c100d00641000708100000d0001c0e45141000950f48560710151180340104010300c4502e501050340b1403440340140d003c1007151034220010b0080c0c103040e00041d401565500400403560360440402d07026190400b900d24414641084940d083d0f407a5881104401100b0030000312207506c524010316082d800064001400410303109d45400b40d0710031601030b150741c00d16141114003501d000380b400f2007002d0408108000b140c6200e404443c452160500c00b1b025000f5600000c0c9401078140500340b0182c00c1d00c0c3c80f2640150b02d900e0040c03c00fa410b42900940b52007101e0b40503840d40d9000842d0b04070540c03c034008001c135640320ba00304a00046401c2c404404060705581c410001929400500700203441180e0151b100e41c100b8545580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 979347796 1250 979346546 979346549
    0x20f03251505011401030f09020102030a1242050907080a1d160f0f0b0306030709020a1e08070903112409010807080c04051014070f15020c0312130f03020313 69
    0x40d4510300590000141e030004102c075080c594038103113b1395590303121070280c004220100049a80074111070306115554078054850050002c44d60b07001c0030710365055040e0040140c01d40211900224100c000ca03001d41c0c01003500031752018000c42c3c08904548192004142c8480c0c07440150079913480220565081f54045040710302400070349800c0c0030407902c1d002c03540410301100c0c45901100b010001c08683d080d102032001001038810b41030155a04d07003820000904140e07412441949003000c2101c20990f062040030b659002c3c503041c0c1c0d15034203101c1c00c2d6292058440e4694041b40e41c868200c090b9514001030005032004403201041400c0e0310b44004d1000500100310003011041001a508200042207441c0002e0f034042e6182507821541c1d0b400000410b5400c200c09207000c0040280120b204004c2101c2a40101c03c1244101c4209080c0e12089640d04180d0050191240d26508203020780c04100951501e0954008403018605600c00040d13151106441d600768400c1c0d0060300001020350a00c0c01d800305460 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 979349046 1250 979347796 979347821
    0x181d0a1b0210090c080604030801031505190c020f12040f050307080a03030911090a0504020a0506190c0206040b0703020607110a0b010506070201230a020f0325150501140103 76
    0x51020004000303460b4640303a10304540042c1e4540440003840f4407911584003418128045032040d0030503040203068804d007484111100224502042c04c1c6508030301845010382001c0450b9101c403000009c40354040c00604201804500c0703412410400c8502c10800e190b404540c910000381d5036070400c100c07001044015040304c1d000342e00c11042045003040008554208a0702342c9030002c0c0844641c500002c1c4840307807620942d0711407400307801d2004c038200325030115000728400c43d803120a050f900e00602c251400307441e8502160001108508521034007501500340b4151004010b14909500c07103540403200d8001c110154010391146042155684c0c2010300315100c40c010400a1140101a90322580149014010180101d00c0070802c407003164007a007584c00c0c8400c10751920b4162508003548904603508214510300051051001c0390109603000700c102e8a17018201040700100c01c0f00c1030841000409103410841d1401200760a0b000c0c140c015206890107801a40c409001c00c403245130005042e60305810840 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 979350296 1250 979349046 979349081
    0x909060b090c0f0a0201020409020406110115140f04020f1201031406160e06090a06081e0f0a0504050f1911120c15090301060f09110406020706181d0a 66
    0x400702c84081d00c1034451103a421404560788525042040340a0300a99111402c418008200801c8158012005c1c03145074207518003c121500d81c24800e4070300c56060788a1480c0ca220441484400390030314110003043d40c00044d1015180c4040c1f400c0c02c8507560f1254841034894411000140104800800c6140e002c0c1c0c0c00c6001480503040c4101c1d60408840c4d2010784105221040041c103070f503078881c00140c0e20039401c014140c0710411354809003c0c0c5005005c43d00c0000000601d06d29081640c01010140d0046600b21510206503031104640f400808004e4001c0d0b40a10513524407a050303080411184600c0c03200d00b10041c032948001c2c074044245008114060b0b104201c1440e0741d200b601d1740001c42c00f01c8560125502941c4900801047d6054407e0040c496059400e1040118548100e41c0c85001140c1d02150208400d50765080c110189010f14018080140c00010081100c03600c44e140e00f0840900c45045201e600da0744503842d034241c68407628420241800803080003004e007103520600031b600c040c00c3c0d100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 979351546 1250 979350296 979350301
    0x22201c0b0c040b09010521070f080601020d12050703091514061509090c0d0606030212060402090d0609080d0501180c030b0a030f1b182405090406150909060b09 70
    0x30035049000d079130381c0541040000f25014501d051109000c0d4a40101d9280b42034440c2428000102110241c0030200702050310358010910300c4d48006900b41c03c204003560b0b03c000314018402034034040c290242119041584500c0071202050072070b125190440218800000c0d400c0a8500901011100074034146c4149400307910006a40494021103401c04411240703402c850340c801c006403066016100e5800703001c528014010420704d40560007004800b03411404030203036070780b05c4040000340d203d0041c101d50000380718103018000030390540060034054842c4c4c44441c1004d96411100d012100240d0280d84ac200801c84c2e02600c08000f031080000010144c5000c0c08000049000b1482e036209600c402072420040b121803c0501c8013011451183c2e0004000c0040e03142d42d0b810080c0041c8140c03100c0024901e02e02001d00c980c0c0e0140404900400507103010354118980350000700421500c0040c010381c0c5054450804000401c0e1034101400a8020b0280c00529a04a4200320086480d0241c0c550301480700c1d03005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 979352796 1250 979351546 979351559
    0x2150108070f031101210b0a0e060a030305181804110d230319020c010215011a070602090409051011030c040e180f070e22201c0b0c04 59
    0x80c010580c2c4c3c110f41a403a44540100c0104c40c00c0348050300c0d80422005121560000c074070103070424511010300715652540f00d915204102d0a210081c1c070886c0e440700c040002000068001c0001e007c40d0448800018800b510a0b004603040e171640000c2c0e201442074540c20007081101c0c402c8161140c04060312809100c440548d03d0180000c10400d10709540060f0000300c4d20b40c400c0800807105100c0c03c024501c02101c80030300b03001c0c0daaa0160040d881c05406000ac0545a40310f9603d00b4604880d00b803081e24018480081204a0130741c0180c0054603403640030811224691a2130261810b01d0740720f64020f0004244000d580b80c01c0b00c84c01b02c424900315508000f0320000074102c000b5038003903d03142d05017003149803541c000400b0300140c01e60a086a500559102c5903490801040840842d580201303020400d54a000c103440d080c0e4480c1c0300b8100810703104d13246040403910107900c910b9144098001000d00f250010000364102c1c0310000602c241c0c003910703400c040803c2820750615800940c041e0b08181042d0a109 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 979354046 1250 979352796 979352819
    0x60801050702120306130212090c15120c0408011a100c0812060a0e0a020703030c0c02030a0f0302010608070801050103060e0f0a1103150702060406050601180e090f0601060215010807 80
    0xf00d103c6507114010012440c56591094445e82c0800284000c42d0740c1c980664501030b10304802c45c0e09d1912402082c24512250400358070a581030f09040719594900041c00c2250300e5100b4016044040c4400e0601011809034400d10880b4500341403454500c0c0401c2c4d1000403c00300255002002c0e0401001c040d2060002e410042075540f072000343c0403000d03456a124008100184a1a03218a500503480c8017030001c002c405030700500700d0f280695014403400b14804d00c141c070000e4a44070000d401d80e1140040001003518000600f0f00e882c420310022076445c0d034400c02980b03485040d4020101903503480004208011880c07007044481144030015245214440203142e031684000f4901511004900203200215070f000e0250f142040707010030002d4142c4c20407043c008e580307880480b021241c0724900f0b00401c0301580220000103842c1d848a08410303006051580151038400f01401100c1c481c4203441c81602192014452580605429401041d00d400c00f103812144050040e4080009038104400610401c1040c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 979355296 1250 979354046 979354063
    0xc020712060b0d020d030504081902060703050904090803091501150828020d051e0118020706090203192306180c0a0b091306051011161206060801050702 67
    0x106001501c09080740202e000c414200030020352006000321704004054114003d4404d603034800b0101c0b800080301d440d004e034281d004960302035805141441168002403040000700318000010f080400c12490983e1401d000e500240c607000e0068018028400c031800041d40042c1c01400081418903030700a002c0c8000c0c100c04000752601710003401002d50390300d8241c8003685411030080d0b40103046540f2400440204010310003980c1c28110100c10640000040310f4002140703043c0c9142014560901c10b216004038020360282c00c04480c8180c50b081d0741c0c805a5014030178a150911645003041c2d81c01d8980c6050383d007090152240310910402c80c508514a04000101c00b039000080c1e201c891420000c02508a01d8074101e0000c265000c90342c91804608100c50001608942806461000300b02c41d8450501c001d5600a000d440d4001c0c01920040500341d2055001500c10603100f000d507101005414103042c400031250700003440054030b000f980b00410600740700b018010a0a01c000700030740e05000c44025224041d6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 979356546 1250 979355296 979355303
    0x60301090f1523130c030c060504090c0302090a151b06050702010b0d0b06010f0528030b0d020f04090204060b03040308090607170a2403050a02150703080a18021002010902040c020712 80
    0x501001c08100841703100311034081c5402810700300003107545150052456116000d0f80c0007582c106060804401d019009031401c091000706911036990508180150501c60305101c2410403040141603088818100581281c40e4001e03407021629140169004e403d4554000c00c10f4000c0b800c0c0c003d49400b04802846203500640240ba000090384802c0c401192940035014884c0c10220308007690fa00780710a0540c0c0420311740100d45080c440a40c100d42009005900c010001c0e401c85003c80d04428149440d9004188007480288000740207034803030002d100d09403c119012030204034201c0134402a072a0400c48564414854a004a0444007544003078001d060060b216034801e58441c00d901c511035058208040c80240070781046d01200d40d0364109540c0d01c07980340b10285d0040700c04a0302e64074001c004c2d00840315200e0705512202d8a54681980003c010500d01245d14813034840d10841000503502e1080f42140703a42d203980049009605401000203d40c0f4128112040d0750002d20200604500d14900030f84441e017 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 979357796 1250 979356546 979356571
    0x303050a02010b042a1110050406020c010207200a0b09060d0e01110a03060b161b050607200a061b14060c04081c090e060301090f1523 59
    0xc10410680c0501081c1c25201c3d449401e09424040c40b0060441d00d1540840009001e22040b48422080d0390a13030344644806d2107500800b001e42c14403e6940c02658000d403003028014904802001c281b801c80e00050300c200d59180c503400340420404800c040030485d4120454170311003a00d1034042d0101d03082c899580c281d8001c00c8003040c481002c8002d07500004000d040c8500034003200c8014400148190300c02c1da000c4bc0824038000001c2640030304001a117200f01c040c0d0300707040d1205c20380d621031010361510341402d046c903152440c0001c2401c3d16050003800c0c00d10702c51403001501c145404420319106107080001402185031120030054130b0b41c086000b00d1400c249564804502c0c42e2410b00707080c05c00100c046205103200d08018000640350100003042280c0240c3c0035180461480314624a00c1020000e4050001d40c00709010702c6904284100355070072000060000800e0140c95555101080210400b6510340300c1c1c00580c840018100d000c0d021368001c03c1500b01e4451182c6140c050000030020706102038508 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 979359046 1250 979357796 979357807
    0xa02120912180d0c06030204180e07052e020607030b1c0204020f1308030703030b12030a031d06070228081606020405090a020702030c090708040308070306272004030305 74
    0x202d0b40a040082681c0095001c100f40c1d841c5c184c0a0060343c400e115424404251004c0802118010710444d85a1100100644005880c0004019002d102c00c5564074a030b80e440e025100d038040142c5466500480260041c01c8185040032000e02211540042e45000341580c02035040300d001c510328070801855040340d0045c0c480000f050f050359180a0000303505201c02d2010004602504004003420750f07070f88a0740c0c081c0580e143c408284080310840c010780001c3c030342c014040c0504590080d000125041484031410b03800d4000403100524250080c1c40100150f040381020101950402c4802139120b8168407680720070f00c1580e61060130501c10308000c11f160f00810b4a02e4020030000781c040f5001000000c1040750700b803c140018800070b61040d079049100340300d198100081c9090054102c1c1c880c0710f4944480110303907a2600c05071800c0350000c2c40001055915100480c1e01c5e24041215034410590100820b2032040d005003201c1120070b1600740015000090f807101b0340e0004c880c01100e0641c0d615280035500c4030b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 979360296 1250 979359046 979359049
    0x5071701062f030d0209090a2a17180151170f0c1e0102011103010b070b06060c0c0d05070518061c110f0f04050a0212091218 55
    0x80702c90400a1a46020001356006030880d9074003d4002100211001c21403a1150805d00088501c1c0c0f841ca41903108413140900c8105501d04035044414002c0d041c08070480b03160781d40c080703420117040361103280d0783d6002e08054038012000d03c901c003000b00c000356810301900c00c844180e10700070418001c0c000e080c00a0310070310711020301c60440404400e0f0314541d4080490b034440c5161941c1d00300c0e02690420501c205240084440c0d00011032800c1c85c48043d042c2c00e070680031001070041d001c16015030f003815992030305185202c0c4c1c41e4105c000c500a02040c0042034681d0024940380f031800c4409000c0314401d9105200c805c0030036001082c00c001480040b111410300203410700d0840d05141040d401903901030300c15106105a070f160740382d60b076104450844e10400b80c1c2c054005150140102c612018000e0b0582e14120400ca061005200469072001042114190520800241620402c0381d07035510450700802c400e561840103486076504050b404018010701d51312135505140318040c0d401201002d40c05d0324207000c200d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 979361546 1250 979360296 979360367
    0x50f03100501091d0307031b020d120f1709030d0c090b032505070b06061605160e01060906050706022b05070e010c110d0302120301090507170106 64
    0x8520200c80501c600d42c0c2d58001e182c001c00e12580d00c0301010004814021007098080f00315266144e0584944031400082c501c6c003401c40192a0003203030816450b01e4000041a4007040c44104018980d580c0c55804150610082101000c0c106400c9520554014044503060200c181c4000700c03840705e000100103010311401c17200301025030f01c803412903030002082c480b010096480b028100041c4e05103d051400b94108201c400e80308906018101d004480d0219841e031808800501c1d600504c803034103171102c5625466442c10000c059900040d00030600c58100045100000b203c1c1c010301690030700030b100d40d00d4094050010b01c6034040040c54941c6c0098044d0b1074414a42c546200b401150002c0740e101400f840201000b0842a10504040f03050b401001c0c1c240c1d0f00c03d0701d114038841d610668010006072001c0c2403008000380d11030110190300170745058202480f4190007550003086d21980118490800800c0907101402d610321100f0f04090351001804600d0704150f1007032101d40d050038180c035062204403081e001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 979362796 1250 979361546 979361563
    0xf060906090f030c0227071d060d0504020f040e0312071e030c02010e07080d080c042103120207030906230a0201060e01150e06030709030501090c080124050f03 70
    0x2140e0b01404040107069000c0c44c3c0200c2ea6100b80e60f00c0081400d143c040c130424580340d520450104a4020006000620880d40441d600700c2d016015070200103075200061554000b41200a0001c0e61030303007007000350300d44502079103c0a00142d07000c109500035800c41544a00c01c60310722035232032808040440c074424070030901610708081c42c104111800d01ca056005001d007083c91540340040d030900461549862011903004200c400f504000c0204200c0f98505a40b0084001d001c1d40c8860800d200000b90001d005800390f80203800704d2950690401c1074980906102c2681c2001807072144140401400aa080301404050f42d5250800380700d48481c0c0c1a0451b9210007413030401032610300c08038a804445030150441000d40700b01c6183c2000682c2c82e050400e010800012100e1700082c9100010b08403400e1100065421807a03500d0410700b07842d04d80c2c5903a0300391600240211130764a40c0320810048081c0a05c9055851500c0c2c66881e1015005400320980204840c01100d109a485000c3c60f0b0b019501008001c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 979364046 1250 979362796 979362803
    0x1030c0302011116090504050606120d2a0c0512030f04030209090109140d020c060913240e040c0b12070302031801090b04330504111e15070f06090609 66
    0x149442d17880301805000292400c441a01c01c0c075000c07502601d0240c51b07154000409500401b4413042020b03007215220003440c2c00d42c040c0d01d40c0349090880204c0b03154900810b6401085035100d140d12780401c3c0142c0d1105076000340d003943c00900c144803003c800807003100d040743c0c0c049660640c2c649465160034018489030000800c50302800e0220b07081d4800c00300d218030380c20703110f80c098071944517034001400801d100e150001948a61132003202daa01c03071119408071520f541031043d200000e078030845031b1007920000341e0800c00c40d0920990400003001500303404080503120101e60541084100c6600e030f00c140002500d21402d050700800020128407103820ba0343d5078141240c0081c454030304c441c100701660850696066171850502080300d0b028481c04021032040004a5112114120b0b0143d0b45034010030000d0821181103c3c980c00c07050f22666402c0101a0300d076484007075802000c8008041024940310030b2020154400103203c00000318034813030443ca00940d0800000b0039048543d1034420010518000c004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 979365296 1250 979364046 979364083
    0x303110a0305010323120a1b2d080a1238010e0901030b040206270102010605030d020d1404090204030309080c010201090b150307091b030b0901030c03020111 69
    0x56056035803640110781280c1c001c0f044800e85210010b50001c1703142c0c0301c0c0450700305640b14820f10881d00c51110b001740542c902511340b00035034192081101c943c00c0b04600d0207658412030201a12442c54440030300c480b0700052180c0340070900b0850b95903050a402150845d0092245d81d80b284400010715800810510404c8030080e1071b041d1401c03100d800303030003080b1102007401e4150714090304165000320381d6981041b1000b000000113070301c0d66450390700200b4000c208030307003004c0188030170082c40d10301500120081d8080b030000642c1c0b8902c00c0009084444a5020508c607a1003603c0c00001250085a181c8002c0754a2400540f0b14500c1c5214038420f1056a22680c040c510014001040c59485020304040d41c89120a80d103040303015500483c2a1001440e0190461040601143c24124520391004000c81e01038103450407aa0381e412280300719202d583c810031251402c018000c0700c0d03982c50311901c15038800840b8010019415074031002c1a280e80303070000a051051840da803100d028810400c103004a007030300810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 979366546 1250 979365296 979365307
    0x20f0303090a053c030702150405040e1507030b0102010b190501090e10170a2013290a090603050a03080c160605060d060923060708040609030311 64
    0x3542c2c07144490810b4a580c040e40045070340d4900000c42e8120a070300c0818140058521010448901c0d501c48200b030350240c4001c021010041e103070701d8104100d40b4103c08040c0c0c6c03603c0c030345403d010903604100c0b2a21400d400035020b030a00c01e4801911a504005907140010f003a4090f800141d0040003482c5040383d001039111106002c00b04945100c03419036200b80c0e12078a003195110034900201034192003e103900402d6000c2071100114181c050150b80000404580c1107100c0e42e00c3e81c205000c4041007030743c0400701c00325241c0ca00303080004104c0101e03900c43c0410408010100c4512000c140f03884200e080400c55030002c200b140d6100062000581001c02c0c0801186a4a180c610340e01d0400c01c408802044039003001a03880e500038416076220b0b4074100010085203400d030b5500310040600909072a0f02443c81001c4801103003091184080c9a8840e415070142440d079101d2102c01039403244451540c0d41c1c0002e0410107031560054030705401a510000c08202107681d45004d80c050004000c03410003c00b00400e5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 979367796 1250 979366546 979366561
    0x90a030f05060717371e05070e180402010c0b180c04020909040b041412120f0714130e0a1a010e060a11010b0409080d0c030b0f010f020f0303 62
    0x92540c040e54403515130541041c130038441101d003610105d440003245076000800c00f40b0034417484907032801038614904850140388070384403600c02c944034902c003041c0f5410032100101034840300d80301d080e41028050608071100c52035400001c200b003940c10351420100c254007011a0441e4000c608801c501940207942c06c1281c98026070600c0c00c1e44041007001468491910302c24841d041600c2190301ca1440940240c410740e5550321410504a0b019004503000e00558055071004c1c60140505071480341c4941d0116a04d58401248400b068800342c11110040407090603c100181c01c14440e00320000006859500d40c0307000c4620742c3d5000580c1d4007080c01c1c0c00c0001304008600d00658004801041e01e1402040700b0740c400401121114044448550820700030000c540c4030381e000745402606000030b4000070907150700103004101501d0381c0487c2158800d0012691121075100340c012a4103818061408101d404503032400503500301c61118400f410b000c4407560041c486c1d4400d1104008040342c403c00c40e0703035a05080a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 979369046 1250 979367796 979367803
    0x504050a0c2727032606011706030703050102040f050a09020414090406090f0606080607031a0f040e1507110c0d060221010303050a090b0405060d11190e0f04020915090a030f05 77
    0x210729039690614090111a000c1e6080175540107020684d5400078820b03503074820245802000d404542c1c107220307856000001510900040000e0101032003a00465032402c0103000221801c2c1d00071a02803401800240282000101c3d1000c1d5420300b01c440780034544032818080014942c1840c0500458114280d030401e0100700d40081c022135196008560450f55441000c40403100582565013004050b0310b01c0940504c0c241c480100070f030a008200103804032003541c566103440c040120394611107011404108040d03400202490301016004c01802d02404150001401580c0e20b8170020309056000c42c030300c42490000d21120201c2d10002803c1d4000796120305024019422140480d0000351841c00702250036108002a94204d880107844141840442c950a1000e400c0510019592a2040c88006441280d980107000688507a0b1034505200001a00b40000b00c414004018010fa004121050558a0721b0304bc1c40700100b0000303141900d41c100040000c0038400294005019004912609000d104010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 979370296 1250 979369046 979369067
    0x105030c2511041803140d0e010f110a0c12050d02070b04150209151e04060f030c0f17060604080111121e071d040504050a0c272703 58
    0x110851180d00500c4003c00080e10050a240c1d10080c60316a80303900024040c25154802c0c0c400300580c1801e2120220701d2000300c135051030304013445a445c1c020300312424103540b2a52035580ea0700b01d0894981618400050201d0903005001050220b085010750000e80c420026540c1c01c44940109554561003401c10b02c0d00b6040a0303c0544038624080c001ca01c0d8200036200719231480324050480142000100106c40142d0000c1e655003420307401c04c12200140313240d03030b03030043c400380400d512055044250030310001d0451350352260389424080d050044901d555040b500510340403102c116200d12690741c51021991900450348490059820302c0e20310401e0a0900e0098410302180d030104e1040c1e0380d980d80c452022981a40e148025651644001c2151039100d4440c81e01c0980c200700c1c11201015441d0082006c4810844044c0c45642100c90340b40e0812500758508401024003035428450b59041c002d01040742864801c00c040d0032a643d24421810869200c408045000c82c0b241d0f40c800700b070f218140949042d201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 979371546 1250 979370296 979370303
    0xd050c09060406081203040515160801060513140d080c0a0b06030a080912010e06040309060807170106120b090403030b0a090507050d0504031116080c01030203150105030c25 76
    0x82600003045418a4400e14013141e000c4c100500a01c070101c02d0b001c2003584060415142070281e5045078070100100f000a40c0108011141e4403181e07146010001d14605042e00301d402000030400502e0130348184403201409980d002025030a84844071710000708141c265010081c80303a000800d0140f0100001728201a150b4040e480041469613184201600c0380c40c00d000080c40d04d2402d0182c0030f180d0608002000c003440b01ca0000045125103055420703d40a021603007100020b282c0c0c0806d110590340070001035005155818030048100c882039503001e40040c140981c00400ca40d9801203c0d4100d0660801d01d41e101c005051a5031030f060504000b00501212005107028042951b0b002803078240d03c0c07085178407a03c0c10350748080c104151003010790b02400025000b40c0030042c542c9446806d6090500c01d241101a1842803010300700d150452090804040c41301c00c605241c07062080042c1c60f440070340c2c1c1e05038a000074a403080d580e5403001701c0010103024900d94042040c99014616001c1807400341c00c40c02c042e00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 979372796 1250 979371546 979371559
    0x70905030304050315071107090501060e100c15021c05010f0f0602031204021f110709060308030c0c010e030f07170a0c02040b21060103140c01080f0a02090d050c 71
    0x485000303140c0c0c1c030310a6101c0e90360503030303c0083c802e00300c644022880b940204c007074981a041c503845403024a00c0c0100503000560091340d61001042600c0c2c01c40c10300c0182d4403064a10520349081c911003e08141d410160160101300c0070030b4003a03c91202503040310b050301c800c00750f01429072003070210003c0181030034002e8066514001c000032841c000c14100f040101c0e01e06600461425054002c107070350061000d4000c907005003000c25200b145030b1880c0101c2c10b40301d200d941c8902d26944a01603040c0303000708035400150404d00c2c0660510211341501c04981d40b001d0071000707083d540d940782465207004101c0b46500c0f000368040402c131030042851020040c04070b0340c01007075104401051400741903018440c3c0345071080811003044103000181081c0d08031080705000200030341c0403104080401c4507800003181d1320f0321003a00004018010072081c51001450407107044000c1103210003500018007280303805440e2002210501c000661104982d8048410920018007480b9503400189880303a9074480361201544078a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 979374046 1250 979372796 979372799
    0x3050c13090b1206040b070e011b0305030618070f030e160611251401030f060617010f05060f0705070807060c2a0902090a03140309100f020622060908030709 69
    0x20300000d00540521b400002c884030f81d07281e2100954480d041401d40905101c480c0165000351206084407a2855009403201c507541d107040ea0410520344601507414055000c0708007030000c6280d10410403199002a03080004109000301d4010703160900c448014002c00307002c4070010500640c13050b90454902e114404803111200380b00810b203401c00c3c082c103d21022103c0b040e01003000032940752302c00410400c113045c0042e4101e40c00100209854503500310b140452050904090a04250818140144900d01d5500342d003c1c10280060302501c60a0682c3c0c0818002045480070b00c10188044802421b61108580d4500d5039140e0280564880074030549059400c204c10a8070725402c411540d01400001c11070716240350500c0ea00a009410001007107401854603000400010b0800c81803e503004198802181c403024814208103442c8012542e0104120071002c0520382d840d000210640c00c01c0d040a410795004840c0c050300c00c4c402d15110030140080d03042c268490180a03142c0011801202c80c0d45c3c1e440e0449 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 979375296 1250 979374046 979374079
    0x40c0e1504140d0317010f180908090904050f030309100b010206060a2303011112130c120f0b0403030b09010812040b090120010c03060905090d03050c13090b 69
    0xd00072407180015046801c024801585042050140020310a041c1150800f05000c0681821403098200b0800c446861806010180d0810365400c0c50f912007440074049181180d0b00e50300d00f40981c2c031000740501c1c40e5102203410072005000c2c9405d00c004060480b070300c078500b0822040c0e4641101d014406d50921300583c0003819480801e115104120142c5190044d62504072810307c2c040b6a0440c0002c0ca900300142031003daa001c2c054a00c040c40400d10481c0c8404405002c4810080081d1504521421021518001a408800142c1107030345000d61034070000c0c0c4600b400c820016585100500d18111501084101505544448034004007951401c0aa0781c0b07a8140340d603601c945800042c0002d405100411200e85610000d20007241d040c034148909807402089401040404c0c0c03280e20381c59440d4020741d1002035052013031070028440c512083c01903003080452107454000140001c0304254940e80054848007095080343ca0655280401807000c0c1e075501c40ca00000c09440150078810401c819400091 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 979376546 1250 979375296 979375339
    0x50310051f030f0b0606190903051c02070311031006060c0510061a070c0e072313090504060b061306020609030705030a1d060409140a0905060a0911040c0e 68
    0xb52644918100000741d9242c0b21000642d400034411035205108000041285003807004441503540c841d101d149019017903140560410084030701d41a00100e0001c40a082594001201801c90790004a414030075580308020a04002d800162900640e0410b403000580b16808904a801c0c18020300c01c3c6c40c0322022400048060f242c03944203603881c03c05030000b4040c14088500c0200381051240380c100b00d00a690f514085d54040d030840b1500e02103000704041283c0142c2545250848441c0d0710300181c6041c15000c0b2800120034580070704540680c1c0c40340020108034a650140030103480007000c05488842550100c0c1e14140c20780101b00040c0580740c0407819034080001501d403902c0d405401366050400c80c480484684051104d1013250b510800f115403680e4031810f00a101803c0024000708200b1440100b00010a1000d45000d88440c0b038480c01401003030011664070b8010f054880d0200d810a0a800e104114007010410103a0103480c00c6c10308000603401c00741e030600d41c1d5800d45180209555110308100d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 979377796 1250 979376546 979376549
    0x1605070c0b0a112b110307050d030e0d0305040b0a0504110916030b06271c0c091d2e0e03030f1b030406200a0f0e032a0307050310051f 59
    0xa0304e01d1004841c516004241c0d001202c0140c00482c1d040440300d031152842c0c4280c40d003010700030035a600420310a00e9410f0000d1b9813018141e040c207010324281565140d081400050221230101d6035180030604000c2d4256014040c460300418200f60f600b4111204e841c840d14070ba9009001ca803401e403501080b03052034810f0719129140c4003440c0c0406441241070701225107002d00c1841d881a505002102c800401f45000ca44090042e02000d0020707050120520448000e0324030f003120001002d00128407a14001112241038000c405c62807110b41d017000303000b0110714400055811050074486000f524250020280d803241c100c4803526180f50f240c0b0007500003690172070501d00908142c02c100040c017159980c1c1000340c0703840301d44443d42544500d013207122501ea0060041d440008039004800e0f50943d5002414640c4200e04a000c0c01a9074002d0b0800c0c4280400b00c869504550710007074061080307075402c3c8050002450090280c803070140390140414002d100846040548801c0304000510207098208501c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 979379046 1250 979377796 979377853
    0x1f08070f050702040906020f031302040f090b2a0c06041b06270e040803100e0907050d02180c13080c1021020c070e060402031605070c0b0a11 62
    0x24a011035079003c4c0000b038011007809139907680e000c0000001d51403000d4001d40c03160700811030410708046180304110030354078150310044030b070750802d10a90013282c185640305403c1076140e17504c120b07200704507035012803042d5422120010480000c5010301c481a4080f4400d4071461080e41c0508951036003601420100e52980035090000704401d0901e000300c0000b5140c1d000c10400700380e0038901a50303100040700d840741c4100c4044440c01804820321025510110683d4040c01541ca10b004040c503001050742d603907903040e01c0384911416203000c0040c25500c1d1144045209143d040c1240300314906840c0c00c01150740302d039201c429401c2307081000107425140803401c3c00c0c44820041c071034401d05024401c00c49001d40d04429200c00407003881c6900510b0341c1ea0344000d0180324500c3c00a801d840b403078100715004c038100041c04036000350300400410218601b00440100455042e00304241c0b9001d90382021051482c0c1c94000521000002610100303503600440c080042429440445851500652015160840880300131 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 979380296 1250 979379046 979379057
    0xe0c07080c030c0105070507031209021e0604090c0807021213090c1209030854160e01171209010e0a032d0b0718051f08070f 55
    0x4500046000c0028504560001c048a050200c00c4859508403201912400003190000900c9810150064020201d003000b6a90800c041c026540204424004110000000e40d035600c2c407032060703a512401598060310220710108564625040f000d0900300c000d45140c80944500c80700c00251041042c11034442003641c81200341c1d8a450000601c015084085481c014411300c01c842c102034046c10f116000d00309000323540d812000c1c1403a50501d2400340c0c070b00992040c05150410a4400380507030a14060100707416646c280ba0b02203540308107480300050424210020700500c80000c05288822a40c00251540340b0f18840860366102d002004181c0030884248030764200f03184800807002d8503c0a001c8003081030600410b08428040003071000c10890700100c0383c454200c821007581c000b090189521854298802d0f65449101c2d4841c0209104010301c0754003001004450141004038030050f08005060191065103c64144440103262080f030707041060000b4401d80c0041c0f01c5900c03880c0354645295442d110b8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 979381546 1250 979380296 979380307
    0x5040f02031621020a15030c09060f2c0a140103110c0c040c021906020c0606150412021503010312020d08010f0b0306060f1b01060e04020f0609030708120d060e0c 71
    0x50f03d03040803243e4007039a001c100d107400041c03010303201040e070aa0070320303a503400007001a4100000b602a1803079820040070001d0603400041d81903005265049403076450107194180c0c8560300c9580c00c1142200c103409411008642c0c00103800d041c490202e01c3c100c0f800741c8041c400502d1074040c400490003920440403880d800a080c0802e80d0070b042d4003440c1004124415501240601007401034070030950401180d400303074006402401081c3c144151500001c04480800041c00c400c98100818001e90144070785440307035160240300710766600e1080311220743d518410039160340c0e50741006800159040d9a000140c082c003403400701101d108141042c1603514440681074040d062018044240e080240460b4001d141009060340b0b40e60f024025000e0007040308840d03001180591440d82c01d4402903402160000152000d20005a4540146c04c81c210410707140580c0b5600c1e4140001e107001e0315544031038078602401c1d0710084204892001070050003190344090184562315400b0341d9125400300d40144407101c0901c82c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 979382796 1250 979381546 979381589
    0x5010909081206010309080316090e0601020703080313151e0912050703020a0803010f0302031905060613020d0e0d030b0604030c033203030a1a0d121205040f020316 72
    0x2182c41e0400810300d00041c21070b0180d600c1c03168950043d50601000703065140c41c1c4040d540d120122101801c1e1101445090b801c206002039a101424080181100c1001c800500003581d10000b003142117801c410422032001d2114004401000d00c06001c007031211a0b814101c1001c245400303106046644207000e010511259281114903401000c030490440c001d00003000d0105040f400518040d11b07551101003085440c620400d40360480b0046d401c0765010804c031889000c52030104985621032000e45040403004060501d02c402031149a140002c5103140c01900d60b02c03070703800241004007102c6a44080040110302001c0104a0040388401008611618000d00000b149851720071900091080d464174068015442c0d000700c11190040080345d58808810850300c4000ca02645c116070301c0040c1c0e0805d200301008017180702d0400781071015000c000c0c195000b00b400c6d4480c200d02c0807440d0900e0070800050620340f801d8114842c1c00301c0280e20070701c40c0444a22a2000c042044012241000c0000561148441 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 979384046 1250 979382796 979382827
    0x906080c0a09020d15030c05030606010807020613030507050a0c17011512080f030a0b0907030605010e21010c18081203010e0901020d0c11160b043c0602010501090908 73
    0x440d0003c600d5200c91715403070a0f50346480c07428083e500c40d0b142203691600b4107051602c1d143c001800541009921003d201c0b0054001c00e070690802100510180481d0b0b607410181c9443c420420010043c1c4102880202401410354840047d600c00101c03410601e0740c040146401c1e80c0d0310043d0b07008040c0340e51904000700310518022502c140d1040d04030740d0a04c2c4941a400d0b10700c0e04200d5004030f10075105c0350001c80c1464054915a403001183c02c4c00c009842c14034000811030426001c103075000714072440014080e459844080c0c103103a83c15000a00503d803071448001d0010100d0f520800c4880e850b04000704030707584003181e5004621038070700d80b039400d5a10340354407069104806440780c002c656007000b001c80301001030701841e035811003241c071108405000040060701d048104200f00030544003108040c495100e8207000c86080b1071300c80550520351200c95141d007120341d0b9200c001e2502c907120f4101c4101801c041003050421281d85030001c124a0b80d840441806448020400034895101005141c0840e0343c82c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 979385296 1250 979384046 979384057
    0x405060d1509020a0807020c010302040b0702010f020a051e10020a0503190204031208010302090a1a1e0a170d05040609090e010b0301050c041a0909040f170a090906080c0a0902 77
    0x44100007a05a8a0700100304a900105504001880c1e13101080300c10b9030104803003401d0304030a19045280c24500140c40f8010300548400904105180c8040c902903071003004000403039500f20382a620302940020340c94421342101503e04000b40103550780b40d082c040541c4296812904c1c140c841c0b41c42d40c1d4408107d01c0032203541102d2003802c542e09100c080003090050f80c02c041e007240366072112401075065004100720060014441355100707080001d060750300c1a0804c0d80014449040d87e072008040d02c040311504444409081c2582c001301102d8001030044440f00080740050032103400e9806a0541d03510403a6103100328090140400c10200701006600035035401801ca0810440000484003403810009003540c2041c0d440782203625010070f0502170141e0034004d9180911f0610296454403a51201081d601b0400610160540c0c149080e03076010b002002507840002c4244404c42c40c0d07907044e4010050040c000c68011340060519111000c600c261000a03528040d4600030000c04400d4544502000650700a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 979386546 1250 979385296 979385321
    0x1a120d030905070e07020102040911090d031d031506010807020a0314131e1410140c01140f04210c02090702031b0a02090a05010e010902071a130303060b0405060d 71
    0xb004000030303c04d03852121a0340540c50030707400580ea6500d0f020713000068a0000c614443c01300000c210111036aa22012810304555046c18070100d5400d001031503c0610740b1140c0303604c0d0075001e640c01c401e2201803000301c0c4038403980c400d072603403035241e140c0960481e940c08841000402150304210300440c040c5480000c0e11076404000420b4020075150019120042c1500d020000701c01c0c403050007404030700704d000b1181c92060f00c03d07121038a81b1000d1080041c13540780402c05881c5110f0b0b00003141440304d80207400200c080c441c0b15000080c2818060719a01180a00711410344ac840a00101c450040c000c41d03a201000144e50707511740340c16000c160204882c1140141940741944800c00c110a610144000c000d6000300003807002c0c2606280c58014800f880400800041a461a110041c004c6400c2c241280f81559400d0300c005813103165900e021030b12503403400d125155580612080006810850f03104440e020b20a543c240019590f0f9000380009000d2401101c1d4442400d2214000c1b00d403c2e0750249160600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 979387796 1250 979386546 979386553
    0x4020702060c01050603101a040207050102040b070506010f0807033807170f0c03010b0f041206053306090307030b070f180501050a1d0406091a120d030905 68
    0x580d500246696000c0c2c050b0080c580d45030802c01c45035240c14840c01e91200705e450810b01184001c0d08400349119051802141f0856000c601c1c1c4041c0030702581602c005d0074041807107541e81c080034103082c1da40709403d1161070002c1200745030100707a228ac04681281141d5200c0184825840e082040d5000c0008200f0030034014600260102075000c1c4000340c96009035450340f10741d06d82d04e441006c146c07403850008050b0790303a034132124082c010070400e102d0441b41101d002010b41b58807204000d03030310105446540c2c400b0001818540c0c4d20014032005900940c0907440074840325a02800018241029840a0039000031a51004a2074801d80c20004010040140001d065a40407502ca68809a0129064038204002500181e9000555800001040c482005410906081450500020410310920214030304120f00070b40200c0300d5003001140326001d0a0b005109002054032500410003c10003102c80380c1070b04a01e00c0368060607090080a00c2843d184200180c040030030100d2041c1e01a010381d440484440c40f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 979389046 1250 979387796 979387807
    0x90b090a180510020a1407350a08010f060c05070e0a0f110903011409120a05040b2701051608071a0f04230d030c110a0f0506010b0c0607030b0402 64
    0x200c00384400b05043e0111000107031522841c0c14010f0441c18055810035000100700030700d40129000d40c541c03001d041a200d800d10701101040d4000041120021000780a008001c21420041d036003102e14641640e150707203010004c55659050460300c1018035103000e0069040354506100059500500b42c1c0d009800c1d540118074245203407112002c0b100c41e5250031400300b00224040146140c20701807048410b40c01c0703c4640c0d035802e04001c81601e404002e01c6400300300070001015070646004006640c014200031200c0354959078403202c5880310003a844c0005407200171010100c1840d42c00f92007a01d103a050740a508800040305a5a420342c0c60b4007030701c815615018075900001101e880c411640b4032070111054507042c3c0381010705d0b10182061007020814110209105801c0050100058004a540e4146004500c15001d640c040d564048520307004650390140390f6442040c040c0e08001440080e1040d41141d289a80e1082610746500a96500980340d40109001c41d1029100390040701c21408001c10040c07801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 979390296 1250 979389046 979389053
    0xf0c1f110d0c051e18040902010f08100e01060203031602030f040b07140d11010c050703050909100f06030c0e090c09060c0c0a18050609070e040c0e09010b03010f090b090a18 76
    0x44c19a807241d600200140c896505e0100040351003c29605580078840b01d8115070020300500d481803100b81c1003001d5000080c0107414031042107401490b01219102103561104030003034584d80304588405402170074a04000e0b6603807001040b034480c081d03100406401c0c90f0803c039161200381d10012003901c40011f451030b2404542c2060081110101240e02c607032814404003d4084d0a466150707201e8401c1c1712060003403e022a4010013120000c1008803002c440710342c0c80184114008416810002c2c2d517424080340800c103190160b10014808a01e502c1e00212080708508100000d13904032100d0054080c14040ca039a10700f404000703088494211016156204601c001140740c070051644900c0c904100740b840d050705452607220307040e003244054882c1c480c079282201c0050050741400100c140500d5440f214000850700c80c05030b5482010f00180034100550b0740d1503013005160020300803814612514800000d03180075900c920140782c8001303042010103a4900004100030301400303100340751a800746641d80d03001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 979391546 1250 979390296 979390327
    0x30c0d1704081e0705010e040b030109200103060920070c080d09050a060c030c20040f06084608360603010e0c0f0c1f110d0c05 56
    0x941940001040300301810f040a03080c80e1883c510002d0980c01001c002d00860760b021090b04000d000075580032442c3d02d03100021174014083c0b1100540508408500700300034103c000c00144050070242d030305104a6072030324181c004a0f4201c4107650060341402c210344103607c00403c0584000c501401c1d440e1110f544c1c1c1e840c0380b0305047c100c0c04610300046100500780054030b8040d0240026200d54504443d080c0c034103a130081c0c000d01010344003516000080a104039000c03249a454040b180307020300240800d50140458002900c4a409010300740e02591109075410003401e61101e1100b1200406c600080201014560154074203680b03011807000100321000c0071500d14402404010104006090082c50030a0112546580c441e011240003404041c0900d0b03d649003c1503d054505585200700e40f40c41d03401580c4254410544010700c0d00c2008511010000300100700c0000d10701d1100b50480356030940904190031075a6000c03d401e4488801e000c0010381e240140d00090b00504a800d03c2ea16002d11076250150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 979392796 1250 979391546 979391549
    0x6031406040209102340090f0b04060b0603040b0a0609380a030f0b0a0203070f0c020f1f0306121101050a030212040b0f1005030c0d1704 60
    0x42036010005020031410310603201c90b4810008035107505410b00b40741800c010b000142e54218100040e1219007240360303071160020b140c252800c440340c904607201120f0b4203001c00000301d80017015860b03243c2080d1105100380500d0002e0343c2e201c03d02a246040d0b9640e0f100d61440060403d0307a04550703070307031084406449001c01940110b02030a1104018584402c60f00305940154100207400d6061584480c009100f00301c008940c040480141404200040d10b503980d4140103c03401540700c0c0c01c0d201d000052145d0203030819422400746080364042d1303031603051200a80c0710944400c4005255140400c140343e20918041021604c010720b9a03408142c42400202c0b02c41030403000c04200b918001035903004a0b00341c03040e140102000111803922040b1915284400c044041c4060b040c444000b81060a0034800c3d41110f040d00d01d90244084681014208051400401c580400e621007900000c1450400f02200030003c0f201c3c000e009004519603641403100380ca034925011070700d00010f10200011801c1c1a0094030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 979394046 1250 979392796 979392833
    0x712061511060612120703050d243201020c1009290703050903190b0f0f040b0406021605030d150501050307020709021b1c0e0f21010603 60
    0x1a49403074a05505040807000340142e403080c945044220540c10020595607010461a240181c956000341800d681521620b00c0c80402a442c0040c0007641249490b0b548001c1c500d11089458441e840f020350f118603640d80d404400c0703c41243c0c900172038048609501100100c1043c0305031400c1d202c00e400410419048002e54001107220b40009101280c2040f21041c5100f240b900d0a5440700100b648102552160b032802804100c000110120382d40c404101c03480840b40404040010040c407428005075851041c1c0e440d600c0440350300e010030410009141454000c0303800070199862600d859482c24021350044039032064101040baa00c1011800c14400b90090035a60500442e4811403140c049104142c560003540c107002c0c0602c04d002115a00140090175103043c02401a07840000389030043c2201441c00c00407200307228000030000c2d211150202e00015851a8581c09849158041000156800c59001a4101300032070300003c4004ca400d5604802503600000001c0d48584a40b2074401c1d6000440d540c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 979395296 1250 979394046 979394057
    0x90615091214010c0816020304180203280509060c03061c02031f14010b2d0f0c0c040b1c020402220f03031403040b280501230307050907120615 63
    0x800d03100b408440354030707441b003292024500e880c3c204120f0721281e44403070003411801d6501000082d8400000d841c5940202404c0f04400c2c501000702c850031000e00300848803008680600c1d0045030064030541c043ea409040d00070202d000e0764810030240021360801c0001031b43c2c18803407a120818503c45c1c01078622444039404401040c80c100b0850b002c54440410303400130701088020010960100d804285104440e02003442c00b140c483e5480319504868001d003183c0403c02c684c00208000c6841e40000d03198041c5c3c605843c0cd1003903441000401c9128910740300a50500c0748082d05000c0180f9042d4002c0c85000340c00704100d03000030301a0048014030482500110806541504d0500615801180a0225912000c0454650301c2e265032420f003200300240c0680100c24103288035082c42100f0740c00694259825038000c1000f076039288184841c030041d490902007e001400ca1904483c2404510b0200b07031100500b80d500c1544890704112417550b201198105415a5180c012641d41e580502a200c141d6617031391031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 979396546 1250 979395296 979395301
    0x10f0b0c010f0c20070e04021c0501110403110102060601021b1201021603022a1e100e1302030405070506090a0305030a0905040501090e060a020d0e070f090615091214010c08 76
    0x3500c80302030aa050040d021741c84502c0030000190084c001c0d69001d0b5042e101b040700300081032a150440841680300808a50a10401c81c2a00954a01030411a400740e4400c3c0200b040b5800160388466050b105640140c115000140a07980510f00000d81844007900340030410015142003403c98001a010410f0120280c0c0e02400b4103604004500441d40c001500440511844019800c1403050000c16400b5204a4410100203507030421900260740b0040c000c040062942c2000074440150b85008520660040d64080318010403442940e04c50f03a8401c1c01032040b2070400e003c0150607008000d0541e44102e003201e01100080d802e101400c981c04503521010403007030400c800c101c1507810580004800030b281c61240c22182c24001031851700124451300043c1d490001d41e541302c0c00f40c500d04040d01c1142c451f003540060b000e034004515404961016104008952700d6203160403240300348580c404002903507002c041c024107401c04207118140d8883c40c06000074904144ca004d003541d0310f041c031942c0414400d504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 979397796 1250 979396546 979396577
    0x516200d0b270304030b060a0e040b1603090f1407030203151b0c030a0806010e0a0f05040e0601060207060f170c0a0212090d060203060607050a080c010c0206010f0b0c010f0c 76
    0x10140c000e2940c2c050000038080c03416a501c0c1d564090380c840030705410202400305140351140007208010b85018180d040080c078050410080c00941520140020b02c80c0c450105002ea1081c030441c03035407a500c000301c142d80c0d80c481d40b81d008501c0c0e01800700c15160b0140440000040e07404010241e1240644d9011603c40e240080514059200040301c880c49054100660804680c0100450302c0c44c503141c0c01c003c52941c5680c40102c4012400302078041d00550700071000310701d89400d07001e07690494508a8042c800b11621084181e22480c0a10401b00942d1080780f05003d85400345183c000c1805071032404c2c14000c0e103031307410102c1c1c0360340300742c0d01c0074800240000c0d100311080e1b05001c02d10038241400a814038006141c0080340004c0150500503150b50741c0440803400560303420086400098002c02180c25000b1141494201c5600c540c648024030361030517076a103128500108281c1d0481d0700203124803e84610345550044154421040800c1035581d40d201440703110080d01c039800903a01c06560b405664a0074070b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 979399046 1250 979397796 979397821
    0x11060c0d0f08061906030f060b0f070c090b0d031d0a1212080907061202070b01060e0a080610050d0f06060e07020706080c03060f1f0c0b070516200d0b 66
    0x40400b4051010a032024502e04c400c03420b02000c817a8640340028007640d103001e5000051a050300f001030300c510f000454083c0744640b03001038907010340100062544c1c00c0c3c1d90070340c01c4100d0700c2d40785c00503800040030350003034001c20b0082e405c2c0341c82018940d4140c814104c41a0004907040c0154028500d101c103020300704828000e030b519031404088418140300c3e41c0c030300f0604102c5903101550700c40c2c403040040c041811990000143c054415013135004203540320f075584031600a040a08011000c90049121142c006003001e400202d039030240c810110b20507a1141400140024038840d28010f030703490241301d0741080024459116500040c144244c03a00c81a040c0314000900703144403940020200620f043c10f10084d88560000c49400510884d0004d0742c007111200860001028000c41001070748800f4070b042c0005800020361400184101503001242d904c90720180d030903002d507952a121814070f01070444006051803080315420010541c1c00c1280f5502d210018411041c070082c101c1d00300e40994140489180e081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 979400296 1250 979399046 979399051
    0x103061a01030504021810030b01030809030c06070f020d0204020909040506071101090b0105332223030f1e060601031e0504081303081305040209010c11060c0d0f08 72
    0x240b9040c04035007040e07000030f121004c80100c035884038030719400812914003401c1100001903038030510078102582e4074100000c0315085206003038003038090380540303a40d51f10384041201d400326802015034455500d0350b001d00c440301c00214000c0360081e9003000390364115510819070502c990b10ad07038010000751424840c0200345168040f2402e42503030402100c88006004003840c1c905480c01581c2c202420a40040707014180c04100d52801e04555036000443c1c900341000004101b03103160251400e68100d564001c2c4030800d100c61043c42c20f079501401000086001a0200c840100307402406c0b05d40d00c0c2e040360b50981c00d00039000b030000c03c001c40ca1900c8800da141c01340400c9074416000d007420030a1000010703002c0d43c140f030700f036040e01010303031343d650004040254040a807000d0786d1540c0c240c4489a9160310300b14025a10034581700d03e0112301500009100d2506000703d500450060350340044915071903803a83c4a400d0031a16047e0702000c18061540074440412110301511030f9030791407620a402142d03000c1c00240d0003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 979401546 1250 979400296 979400299
    0x9010522081c2f030c040302131b0206161425051c09080706050316091e081c021c03060b070b1f0605070f02013b040e07050906060d050103061a 63
    0x84c000c00c82009412003c2e45c00f2650103a500807091400c2c0510351005003040c8400c1040380301140e81411010f98005442440b9080300400a0024500c402c0d081c1c802c0c3e10107407146a00100b040158103002e40c614a42030070b1008414000e1081e0207d90750b546070505020300e036414000008982d850b101c4540c0440c2a80080c10f2400182c242c41d424403c000b00548002800c00f141c5880c0d03880300c80700c950f119072800030043c02d86000078240803240c142c1d2800401c12900c0b900026206804251010b0702080814601700040c2d84c000b814904800c81c6511b18003015041881d0a25075510300001d40a02160020810b441c42607100040d50300d480c031842d0900c0c1c2070007081f000111003100b40502c14160031004803180180c1000100200700324610040380d00c410341003007419016a401c90080f6200c1609180d401c1c038507103034181003849a42c4203424481100e0040300000015402104204154200718074600d0700300e01c2c050009440c2c1420031407110142d0300213a00031107a40d075403010051262089100c050044a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 979402796 1250 979401546 979401641
    0x1292d040c0e132003040302010c030b0118150507051603020a080a0507091a0319051b0f060304080f0307170f0f3402010509010522081c 60
    0x40c0c0102040d20030910412403502e0a84d261002c80a51800301c42d50544204000d4803d6513900e4075160080c064a0102744034030200f400c051462156600804542d180c40d154424103101d064139016402d040800c0c40f40104082c00000c01c00da01c0442e800384a010611568091212449851131042c0f0200303030b40c150700500003900444070040c00a180418014100d8000c0100495a02130340203c0819480a400c0074582c944122401c1f05041d20014116011450184041d9007100210a54181800c928982403640c01460b00300c0140062600c00c000d590054042c0d0082400c141c600c504900099009580034000300e2619103003038060b4042d03980c071281d003c1942000300c00a81800400c0044188024100807000400c0214010400c1184900b4034031004040309018608440818080d00070070007a50f552f940c40d400c4c08005440c1c3e50800741010620403124114107140d29243c1c4401a030b40e00034085400c0801440c0b01034001c0700103a8000d90018400600b254038040307035126082c1c5220200c242488001f01c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 979404046 1250 979402796 979402817
    0x606171614071a0907081207060b0a03030807141e03100f03050a060609060614180307090b0909013809010608150307031203090510090c1701292d040c 66
    0x1c0020072400040c010040c1d0240e26a180d0703227000302c00791444070901a003000e820300002081c154019200750150020381c80340c142d030f218030310100b00c0341d4810040c0400410484003003038500a91004005d55010303ca4421841c0088c0e11a0f409801e6080d41c0c2e4000d580903407094100806010051003584001c007071241042040a00e844400351031101c0da000e0b02d41c02170802158a011030882c40215071480d00004023510405521504010300400251007124011800300c1c3c00100c905105104440004a0740019a812504180c4c141c070b6245440b000c180400045400c0d9001c995119841e00c00d000c0d1a1588400e03803c0c0c58212000a0405481d0011501c654403850040010988020b410007034240740b454042a20000381c18000d26010743c3c2912110201c0ca00382030130003031011031904102520200031501d10701e0925010601c0c02d80d0b0740592008080200c0d841e0785405404a00940700c04c2407000781c00404082c00000004222249201c1c0e03c1600b141c1d54020006185028440c12400e8451402d0070450030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 979405296 1250 979404046 979404059
    0x1031b061e050d0501290f040509040c090203042f0f190e160806102f01020703030b03060c070507090e070521010606171614071a0907 59
    0x140071101c40084808034100001d81442001140c00d90345000c007041c403841d40d40c0c001c01006c1c071050170078a112041c5003030204502c0041844c00c45036003603003070b03003003d0306050401041107500c0c140a042180c1c40d86680078000380076005030000d10301c00c40c025115001701c044c00c2558003c03400e0b126414403a659503030703000c81c0606548242e442148003200b918003689815002e40c4a03000031440d071b009240301c614541e0800402c012000c4081d84016560396940303040d03440d04001d00481e13942c40204a8040380f503440400d0128014441d50001c82e00c40c1c07001113440d12070994016402c80e032040c1000d0700020744603a0110400e003001c000040d008403501020350300d4200a41c0702c4540701c03002c50148401e6a5107946c812101480d08100c100d000d058001c1050305c13030413089840724a84d00d10003111440b075542080f600143c41401140207000c41004c3c1c03640442a0303582c0340170208818008500c80e00900003506460700380c8c00e81e258003810300240706a01e020300440c030900350f22258180c0280340c007401e90301025060288 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 979406546 1250 979405296 979405307
    0x50109050f100c08090d080910170106030e150a15060e0d0b2d0403080703020406090e07090b0f070507050d020f1e040203040303060915060806100c06090b01031b06 72
    0x4502c61800041102c81440c000c980c62007100310141d032000402c4001020701c5040401003c0c030000c1200c5140ca48000c64000f43d801403480c180d10390400c0030b48401040054000d410089102040b001520b07081000c00249203010041070b0b407045000b613a20705643c8103803028840442e001e01540c4c202403908200c1d16001801803030040d50020044180d9170041258045515410580240e04420040a22400f0303031541800c1e003005c072402c0e400114000d0100320118002d2085509658031b640d50201e005090a54482442c5406801d1808100d015000001c0c1c1d151008045d00b1040c0c007007010143d85609134140341c1e01c5d241c85908018810a65183c48100623514113081c1d5850110a40c2c1c444107803003803011002c410350700c080e1520342c1243c000810003080583c1540300109540000b40700b040054003c1d90f1455040802c0d00441c000325807c0ca003c110a49840c03002c1d062034004520784818802815a5004151011201c08a48801d000d000600820084103030300400840204580c160f541d1400800404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 979407796 1250 979406546 979406569
    0xc1f0e100e030f1614030903070603090b010509040816060b040b0a050f1c050109050a060515091b0d0905060f060117190219020f0c01030911040b061210050109050f 72
    0x440341c60004d110340381482d480450183e590b801c6540c01882081d05580c0540765400380c1006482030040003400700d041c6000e48240300000b500b080d08401c0b503a00740300602c0f00c40d160141054a1244050195115080c400c0400f0b01d5802d11800002c922000c051042c0300a0710680030685100c0d40304242c05101d50b480d0341c00880e445400484010103000c00070600c01d12140d44d00d04c005485542002010300502900084050b02ea0b440348008200b6680c0d582d507440407450010280541c040394640110b0300c0548141d009001281218460a1821000725002011900041c0701260302d60000e4041000d0400c00c0a0303669840802800e01c400b060104810b0b14141510007004030090a050030012450103aa56050311410b807004030480c0b4030100c16490280d0307940d200010f40703289031203101103210a5502c2405200c4800e80d0080b010710100c28400108400340c070000303010742d07004071007849802031003041c0d0701e034441c0909200d60b50341d9980c0d8140720004000107500e0304480d000b2540401480c08680360411004d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 979409046 1250 979407796 979407817
    0xf010b0d02042d0209031203070f0305060a12140f010204060c0605090102270405160c020906030a120f02070f0506040b1605120d0f0c140c1f0e100e03 66
    0xd90700c2001641c00045412080d00290381e064011495216402184e005006545d400c804807568510b001000e42c4071440220780c18000034900e101074140141c003079040203401c02c2005141140454a945541200120b2280309640c14800c0324101c40340c80c407040c0110a1000560402503144c1810004041c02850024600501480d0f41c3d83c000f03480100c0c298141e80c541d1541c048075004038181050b03904030103a007102c4024031592411003ca20407000d070203403806510443d515a00c42d44021502048068030000380025010f019648521000524000300303088110103945550782d18942c2410000c0c81c00d010364102c0c0b9407180f49100c042c016079495000761022900f0b900056540c510410007110925016803038028810720a03406a071001d000e522020b0450061030a40410003550010241c00544015106103130200324130800f100e14101000000b0403202c00c6e0141150390909490302c0814400344400d203000c858035920482081940002d00000012500301c50007440010710014100c0c1c1caa03c103984914 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 979410296 1250 979409046 979409051
    0x4020d0210050c06150102010b0108270a021c17130e0711100e0c012303060102150a0b0f0603070f2601080303010e01050a060c0b0a1404050703050f010b0d0204 70
    0x407401184140c2c2120540c000c110306840303143c24665001d500b845214000343d40554240190a440c9500c81c001c40b61240d001102c01100012403034400d8400c0351f910b0123041240340203610312800503850780240c105001d410243d1820701c035075241c10140c00c410260b80f010881c180b002c1015000e88410b50120300d0503504100c3d41c1298035110428243d0762100c0c00c0c1106c01c581d00450001032418403240c0d01c644c10008a0b801038404210242004461001c110345007051210200348200d082002400003031644000180103e840704040318480301864901282c10710407080d11100c18910034200a43e44840307444090700e4480c2141003c10018045000110100b01084058030203000f0140480d40c0f00100c8040b5144643c00390f50f11a11040c2d01e0342c1c800d00132101c80d07055a4000080c41d04004803110704686003aa40c01e0425199030b0386103040400050700707112410381c84042d0006089080c903007060049110300000c1018601c0d614000c0c5c00c003c0801d4810b105071340b41129400031611030106450403181d045500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 979411546 1250 979410296 979410319
    0x60415060305060901050a060f1a030a06180c140f2205060d060f0602070803041e170d0e030105011202010e030f06012904032f03061e0a0504020d02 65
    0x41000900c0d46620182551041c0424031a140f501036025501070700950000703114842d29218403080e401082e1080f6071544c0750800101c4201200d041c065500030590800c045280d555580c1d00400260041e503020700780d2035031100711900d0b00360030006e04031817400900c01941c2030074000c01740c100150040a0740b910245511a20030701e003101c613840202000e000010002900e44900c0081c840080006004a403900d01c0c407940c02081c41343c00020600b08446210000750310b00381c140003520001005c80b000d0901200d51492000c6407000c1000c01d01825240312800a0441900f40d034001440c48500d840c6050180e40360000520a00c41140c005000c45034080c01c01400e10140c2201183c500007803030108041038002c55001041842c000030100081c403040104180004480041e803545500c114032004050700048031080d06039818107a07460f0310700001000400c0c14000404003003400c8c11011202210040307105600c00d9015003403070089070341115851100300060702d40303540400e414070100d9030042e00c54145ca426 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 979412796 1250 979411546 979411583
    0x1202030601030e0d12151a0a0203070206040e060103051f0b0c0309031c180e070c0807021002031c09020303040302012007060c02180628050415030605070503090604 72
    0xc90341c0f403030600380211000704010402c018249400b90031300c40090b606040f080e10b00d10000b00d80c1e40d0281d502d84101a04004010503010722a03034032910840003940018080300c03002d60355071700281005007403110900c061071801800040c103e860007441c0f802085440741c018500100040a946d06803610b0040e8507039a84000800c080c07071401952080c0782e0501c03407943c07025540307140d00c58540001c1160381ca6403401e640800c03038a0709842e0401c1c00f81c0c1542110080005a68505c5142410006e0303008000b1246482000e40100c3c0b42c144030a2a45005039000240901e5202c2c1042d0440c0584804140708000042d0940c2c00a5280d1007203100290401520b03501c007890000032416040211899042107411165443d4006000c0030784d80c001c00d030710807014103081d001d561508400192144000518001e00e0060101145403940100c0c684a0003240c08800e01060544681c130070200007110b61101034900610314070740901607a0b03005040d501001800c3c024003c0072000040c4440e002680103110f10203001c021030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 979414046 1250 979412796 979412801
    0x50c010311130b0d050c03040b16050d0e0705030705032b030e0d030c03050703020a020d181d04140f0601090e01090c03060b0f030606030a200405040305041d0403120203060103 77
    0x81d12482e040c6060301c0c001000706000c0c0013800b00148100c4203000996500d0b00c40c0860b40403c440c041d202c270b001d02001508250520802a84107a00d50400a06204403c02000e00300c58905200c01030542c8120814801c1c0d2404000900080c03004800802801ca03c9803c80c107036081c5040f002020300300c0c10001c28030700c581c000e40100424880740c1c1e0484921071000700005018280b08201100868904004108103130f00c2402140c51800d500d4008196039000d6040880d00242e0340a114a4503c030180c4003c5800d010300d40c0b21469900c030207650180141401d00300040d452600381949a8241d00c000421801c420b000314030f003030445294500c00a2701c9207404000340c1c050700d400e5200a0412044900c0402001070641c0300c01e40301032068400c0c00e00b02041100303044d541d40e81076400b2076240d03004101180c00103207441d59803461904c05044258001d0803140100341a110140c4080b0041803001c10280241c0e604481c1560401900368160100c0d42803d48020306003210118a00b92100d80001c0000c00ca039000c2d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 979415296 1250 979414046 979414057
    0x91510080901020d0e151b030103020609010215090c01110105012d090513031805010504090b060912071503060621090b0f010f0503030c030f0310031401020d060909050c010311 77
    0xc2c50107010802c03440c00441d0b26242c417115800354600200000c11040a21f0704109604020300c00c48140c03459007181c0030061181c2000c4151b504502c6818500c1004c0c05282c19014001e0908500410035651004005041700d00c152607203410f00e0780340c038004100b503100c800c800e00b80d47d44010980e0200501f03e0903546000c000d842d045524480d00b020140504400000b8152503030324002d40d0703070f81c17045002d5041445401a1f14401d50317000441c240b009100300d916a0b171192208000003825245014030a002146039020061520f00307494202c41c9080003506a101c003000d8842419203000c01c038403810814050200c040c520380004506c2420000032284d44801d6120071181e40d00501b0110082c03410003941407000700309029041100030304001c001030604002043d903140d00304120140d4100540001d00361211740008040d0811506d9900d800030100300007048202400841d10009603442005800c131106962855000300740c06490002030401081e00031428039040c074000d103000f00300281a10681c1040d401070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 979416546 1250 979415296 979415317
    0x30304090c02100e15010b0c0a120507060f0501031b0e1f2607090e03180f1206160807020a15110408160602030418020a12020c0c09151008090102 64
    0xa00c1d5800410502c00120b440317039030401100100c0c881c0e803a001c84000078060031a2145855111a03500000603a101c0b60300e4014040c94035003141084015100c120980d032690480c480f015075104d0044c401d0101c1c1c410018010500c4c41040c10031a860001d212038261401003070640d03820100c401d2468442c4035030170034000400202920270070f0909803841d54050a141d00c820100140300b154000070340b0703410b94000d00d01d040d2060f44c00341d4245030b8007030611110750755041c0e5840d84c0410240d582005a0759016408404203a003c001488580380424071603104800060035002449121010054040d030b000a000200039880308503c602c004612510002505c0d40b40c0381c000510001180104111000260005284003414070712091940e8803101603071688258080d81050b65a400e00c003170050610341d001400c1c03030892403400d5012503a00707550341c1c1c0c126000796041000c183c00004000c4440d00d4590111604403075207d02d144480b1036085c0c005440000d6680508060001c1c98001841e8188203505a42d442d008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 979417796 1250 979416546 979416551
    0x140604210203100f1b02010608280539060403061517030c1204053a080403050f1f0f110a0206010326070201050d150311010e030606030304090c0210 65
    0xc040c4c1d165009410000c824003c00c0c5580101402064814010b210444207608084d0450280a80280846d041d0042c0202031141c542c142440000e02c041040307a101d60f91031402215403c0c5041c8813001800e04001c0c8451a162021914003a031f83e50b54000c603000c07a6840b00d0005801c072280f41c40b2551007019944040012020080c40380e026080200c010090f0020705d00580b401008842c0c054101400f8601035a900400303c420f41e0a0500c000000b2045089000c0c030030100c4101c6a010b64070401100707440121800d40010074200100281001445481c1000c0d0014056460004076100d1641c403d04482d10fa5458642c0020303009819540c3c801812501000c42441d036a990500380603544090a210413541c042c0c1550303007035003692012258280c40341012601c403490b0441d650011034268004821102c0280d80e11003059480080035000e4200451041400c8040310340050005044001d40c103840ea4000e030080c4003046550768020003141d050303603c644000603801d030544504902d0710150b100c010700820f2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 979419046 1250 979417796 979417811
    0x90e010608130501053105061b07080310050a050414070e1c2a08060c03041e0302100b0103060b0f130b0c010203160f050d050702010b15030114060421020310 69
    0x2031000f81303040062a2222160780d891b0070f43c54038640c401c00b460802600c0c903000700020420000c1c0c01d01d0b200503030f01e2441c84454101403040e2113440071940203440c41c1c1c10001070702004100f00d0524400d6003000300000c5508026840700a64080e0141000408100400210300d060844135503480d4241c110340c0c00d00340c19100e01c540d84c41c50404001100f92004407601c1c03600d00e20310044244086880b005441104020349050b4841240d964070035080580200c490183c07007244080e010880b0344d8214803080c002e5000300f04d069103018000d02115640c01c5011b041509000c0140700e0750b0011000c4074034020761029203076526620b00e581807408884640200e1104000000c0c1f4041c582ea05402541c040e51483e200603211000c411b0741a20326100406100e00412000e000a0b100f01285c0d070b020a501007024000410b0340d00390000042c0950403d150f01c0c4c5020500440140300f03400c0036244000d4010000c8c4c40c2a0310742420085180407051441d10000c10791b034801d0340090f085440c02c0c040e050304400e25840030700068 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 979420296 1250 979419046 979419061
    0xe07060306051201090807030c08040e15090c031b0903010f020f1201050906090402040903030b0a06051201080a050304120f061409010b1807110313031b06090e01060813050105 77
    0x42080b4490684503508220318070425500600c01c090407039a2290500d4500390140e94252860807184000381e480c66014400001c00c04080d04a682c0704200a05c00c0344454002841001007202002c0d10341c0340261024420806581580759080340d48800c9101815290181c00000034094080c0c0e0b00c19040c0640042846c50380075120380701410142c5807003003a8005a80c0c8031024801013a1048880f00da01080c404003040c05404e0035072004101501078640880c007200341c0d86c08203d401c610b41d80050000303080043da00c07090002c0c02040e240901030400150000c0b5116466055132401140100c920208611244904001208100050f1941d01100c14013420b01820a2446141021600c00c00c5c5075003000405039852404565245540c04200c0c2d800c103090b01e581400300c4241c0c40801040c7c100744010051480b00b289007003044001144a03070304a4030200088140509401441c4e8040d105006044006100b140c0c001d9002d40c2c15520145172401055880c0c0c40c6030755008600640c060625440c0500b8070800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 979421546 1250 979420296 979420301
    0x60c031b07230303030703050604093801030b01091e0f02312616050301060608090a122f01051b0712020a080417070b0a0816030e070603 60
    0x102d51201015050400a00400038602c9124500350380d4503800400008172400c0c003a07032100c0c2d008a030241001410304041d0352800e007aa0391404041014a0300d048814841c1c074102400c4483c11130011185c1c0c00b82d035256544181482d2010b000c0c06010548400900c8120074081070384079400c880b00302e01030164061843c18a4020b42c040b040114400c20041a03050401c0600800e001c02c0e0044203541601c1c1c1454044510a0160041844104130700c01000c582d258080c100904500300000d171540c5503415203803008150849101c0d900000500002030108402d501d40071031003024a51f0400341e2079188044400303044817511080c1c440012000800f0f01d0155040120321600600ca800100003041a611028030f540135428131380c0072540c1088820004000041c0c0d05002024184a00d0f0048a18146940e0380303807102600207030420713400225807401014507200f04200034070052061a5801d0324152170710308000d15805008288000809a41a40520a40c844e07404204250703140000d03a8100d5440b10303401800b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 979422796 1250 979421546 979421549
    0x110f0916020706030c081b0c070603020315010e090a2016060606030213120206120906071b080a0c03020a0210050a110106060c02101418030d030902010e060c031b07 72
    0x6200b50800814010b01912810207443c29030b85500c41c950342c5811701a55500000c00c0440803d401c14820411803600820001014101a4401680f01d14098010231260b1034414032090411107a00c02800d00c5459500701d46811036030101c008502010040b1080341260031440840f85078210010300c40d035010005440e0034401a01c40c06081c817510340e1740c403012070580c0550811780e83e40406040040081162000d64410b045101a10071030900c0c1c0550501044c40b001200d41c1d00313482c1c00c807000b0008075030f52200b2605810300c241c03000020080b803541c82d100e1050260780544000c0c00200d01200090600070444001d4140c1e0052001e1140d1101860052207900074003690780101c5c082950508800ca01030141c0300c02e45107141e642003248260345c3c0800034007420407000142408094030040c400f80010400074004400c00d0aa04504044a10149844e0080589040d020980340900660040c0c0e40400070135488041110702640f030f1804c3c1110103045100e40c6210124041d1900305410321400301203103840 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 979424046 1250 979422796 979422841
    0x90c0603070c030201050a142a0a030b010f0c1e06020c060a020405040e0708060f060d0501090609150b0a0e0a23040519080d15081603021f080103110f09 67
    0x2045490b007010390310541e08040714101201c0c81c05000649d072101a490084090034a502c1b00b02001d0b0071081d060a0560f10078901318001070b1701c0320a4402e0310b50304040518802881464a20030100882c0c45502440080c0d000120f02c0d00100b0035103038140301681d01036405034403074681519842c1c02d0115001009504c184542e0780110305041e1350000008001c10300200700c0c0e03410005488140d42e410041c00c0c0020300100441e5001d203120740d00c01c0124109202e104062440386d0f40c005003006885c1000c3c000344004d140e01996aa0a1a070042116110100900215250300c4150036240c1c41d0424010041c3c50101801c0000020309406444503100d5602c019000d00e001368260707914260000d0921a445032020805011007904001c480b0421206501840d100e9400c1e0315012809500c5889007030400750f181e0700300d88010320403290074001d40c98503010160460f48401c8065401110010000d40f006405100280062807c60740e41007041e20381c0b551a00b40984001d1107003030303145040c150816800e6154044003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 979425296 1250 979424046 979424051
    0x605030136150207171209011b0e0f0f04020c0106050a1226072f190504050c0915030106080903030f0c0c0114070c03140a09030803090c0603070c030201 67
    0x18084800205800c45080e070b0802c0550554a5622041c68040d50060000b04c850450200201c082214a040070300a112881a040380700350800b0b4030f149003920500012140d002004400351001a6009010b198074a801600c5042024101c40f000030440f5204082041d0041d000007031000d240c035010351040b000e0320b8046803011252621800707124014005c05000500c4400e010031000e14860030082010700489000306400d107442500c2e580c00b98038901c407109903164144081d141000c14801415204280744058414104030821600200307505085845824000c03552240071551010545044941c0440094100304025180e41c0c20146158000d208032000280c491011403054080842200d01401800d405003906450300305220b40b450740000d020b48030a40d130303401610b0314001136990524400c80050b198050a101d040c24080d03c0394010b0345a184030340d0001c100382c2920755088018402941d0300302c00c903a51a5074a032142e9038541060310304540c1d400748000c800c112481e42d10110041c007042c42036009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 979426546 1250 979425296 979425371
    0x30607030609150605090d0809222a0f0201020c0304170712110105030c090904030e0a0914010b03070c0501090503130e0402032e0612050609161806050301 68
    0x103c480c002d40a018039000280304000c1c8071502c5c50319000b00da82c0d85009503600d9207420001d10024100f601408100d0303c55080510115002d04441c2c03042504071405068019081b0900f071050f8080c00800e40203400501110328100303000d1034400d5060f907178140c00007000c90f0ba54980381c501103441910718036030160080c401c03807502003012414429890b242542c070028520740c07894031200550780e580006280c010082d205000c101f070160307100301c1c0e51781c000c6000e81c81d4003c04120520a21010031100d4024111003800e010f4032220044901681904407080428440d4036501c4581c1f08603003a046019003d0251742c05d20b1890400d002010008180c491030401d10010050303520108080780c2d91040720302070752541003c10030007014060010f907074000b80d06045403000c15100e03a0001c42c0c2168001d400c0002e0505120040100700300b010840300c4c1c0c0201602e4020620841c01060244101005029881414240c1220301440400d82e41200c1c0107008024001d101c1c600701b90340507401401d4100c2e194600000c11004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 979427796 1250 979426546 979426571
    0x30c121203040609050d05160b0406092907030b010e040b1c06020a020714061611040614040c05070b041101140a02030c150112030c050709091a011a1b0c030607030609 73
    0x1200e6440d02201d03a23188101c003154946d501443d100610903241d00b500e0340500c9001600311055020210300d210b40f450200030a0345622000e041c0c0040112082c10302d00420444640c1e0070000b042c074031850480d4089603113103030b150110746034100f05481100001c82c6949828100085500a095a0f400b240d0884042e1030340ca28401c9403600b4201c003090707002130081010308030202d0a0300a080031603000380030f02c2444c004100d0100701142c50315484000c034406902c0c0404034a10700740c001c104490059103403542c140182900ca00001300d41c040c00c018860350304881d00500b680d005902d01c40014004031a290b07240d019101001c0d403241c0c440d0701c001e0386030700a41d0341240750800e00b104002e050750f100a652603d01301c02340d40c080d955501607120580d80751080c1000002c4c1c0700c5941c09880340701c0740304a0142007510342c0240e1080603400d044c0c001c4030700400e2284100d055100c030300c42540c03005202c981681d600001e40d402620f007030081c8203170700a4040c003a82081058154058010000300ca50446c02005442800382 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 979429046 1250 979427796 979427807
    0x31605030105060403080d0b3a21171e070f051c0b030106082107020102280203070b130b032a04080604030917010902030c121203040609050d 62
    0x560b030340c0038800340302c1030022910341d4003d08442444003100040c002c11250000c0c8030b02503919101c2c1d549803000d5a100e443c400340000088107108180c04100d01d150000c2e51007150004640c484c107400d00410045c0b07586001d01c0381411214800c0180720036511820f009403d0380c110780d94004410b949002420100d900f1910404140b031849003207507645801d0484080e0541681403590039215603144c2c888815540554080c0301c0c500080000c44001c100084243c401d0385043d900703000c8100180b01c1c040c81403c0242c0d801050030002d8800c0310704202d8401031044c0301240d810f0f8000d500603406105040000c00c08820004c0100340002000c0801000140c2d603003c8041c451100b00c2c0e032440d050b81f000d0503490320b20741d15281195402001c0d540c10f900b0213480b80e081500d0042c045505a00085401c50b04001e0241560302000c42c3d030b80380400911600a1070380201c3e0f070722280c5101c100d01508684406ca10781800a001c4200c0b2208600308190341c904207402c000d40039080041c410388090003010a0240d4650041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 979430296 1250 979429046 979429049
    0x170d0905010215150f0423090d0203070305160f1103010b1921080d1a0f0622080d030902100806011b0303060f03080a03060e280615050316050301 64
    0x42c0c0101c0c455a891101a185104040410795086a1411440700c1190351ba03004000041808450000707103585144c801c0c200c0200080c1140c0f046400c01c1e001c10001e01c2d800720403500c070107801d41000c507956030312000e001c0f030341b100c41c0c4c50098075a00c01d2514002c1003000c580701940750207508900900500300208208000c0b5075809840540c9036184070400c0042c0c0c5040c078012071000c0e840302401082c540381c0d43c45030341c650f40c4414030b044941c541c0c40304015180c240000e048a2480c50135520a0088844040401c5092180b89024a80314080c0c4812080c0c148010441102424200302600c3c21441c3e13105014000d0001c26070124825443c01440059907071044a0492040405031343c0c1280c01038074001c4c8600313843c280343d40690800d501c03120301084500e0441c103120700861007450f00b01d5882103844c0c0b0041c100d915540000707a001003d102030250040b845081c1e4002c4404200e4102200650070300e40350024109907004056601c40c0c9403d901641d504000039620900c0c0c064100729042c41580000c03200c52209 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 979431546 1250 979430296 979430323
    0x30b031501050a03060f0906151502010606051602030a123b060310030209011220010f11211201080c100324081e010612080a09170d09050102 62
    0x102402000881d1040c0c1001189842c040c400140b1f10000351200720a4809680201c480c240030480c04128802401186441c80c1710180b008000b0181820001401031160082e000c2d80c09000c0310100041d90f4090180d004265445480d5852255440c40045e14030101c24440da6140703d6003041c4903c00610354444418454a005006203c000c400c0041005941000c0c2c1150b110322807113100800140c86074018640a091704110f0710765821100d140a402d654051200c1c04a49254511100303440d03600f0000203d00506141825070303c0d02c1d03003441c40b903161010441c1a80501d141c01d10f0b0505011034140000e00f8600401144442d441ea01c0300107a0382da03603510000e1b2941090104e40180c00f11446036100314140d9a026000448688141820414581c1180c00c000910341000600281c0140035100c1c1150f1048404000d0000f01d140215500310701c9a1101c0c0500070ba540003075600c200c14030409100002e4101c01800d02c0760031090802d0107548280300d50142010400317518020409600005400035100c0300c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 979432796 1250 979431546 979431559
    0x501060f030e072c070c0b06010c02030c0609010302070606091d0a0b0a090809040219030e0d0c06051806010f0f050904241b02150f0c040e06010909020703030b03150105 74
    0x3401d501e00c202034200e003034050400005207044c8100508400a418010302103552508001d01c80c5090102c0510307400340c911814003140f00b00240c01601e000c0b8000d02c03010300450b4020703214844840168041c1c492458010190f80ca440350105294100382e0180101080d0302808401000d5a103c07969a19680f4001c040c01d01e1030201d001421820254010240e09031049442500780041440847c3c2a80c100380e1003101070360340003070365000003580c188a000c1d0038026800c0244140615880068200522040040c001c603450b003000444448440e0b00035014000002c08031040d943c0d5805c0241c4a10149011f101e0b10075151450000d02882c004070250b004542101a0030442d54150303000880c580d0b41840844101074440c80000b081088040c07013020004256000b40c6640d2420407610024944000c150701c42c910040c2c01849081e11003c000c3c0c0b401c1c2c0300d0000c88211b003a12800b0040e41e0103d580d074000090075000103101801c0580c0350b00240c41000c82502180d603601408900d1301d50001090280340d0b0050b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 979434046 1250 979432796 979432799
    0x1401080f0a03080c0a0905060a030f1514060f1201030b040510020a09090b0312030a0b2706060a1803210e0105090402181305060a170601060f0e130501060f030e07 71
    0x13503800042808141030300b0f00790105659032012500607000b0780c00b400302096a5003103050b6086198080d51954041e002450404d880c140300d07003610100030316281640169004107103242d41e815241300301d500c4e950004031000c0d031301d40c0c1d285407421010030b00300c5084400d405a637211005c1c1c080113000f9102d100085072a0600c42078140f6140600910903882000d506100b110001504032184100840c050f440c1c0e010f020502c10340f80e00c00e0102001030110060400c01800300742410842262000700c0c3c10800440e20f80303590f40d040c00c1c411644d81d01b0314043d0f04521413003000c000040080b943c441d50b00501042d241e50142c0303440100e054880351a40a80300307000c1001007080488500d41a4010b05007110707611403100728002002e0104000c0404981d610082a0b17460090050a10788410b203000288110340700c1210410040c2085502c035035041c030075241401440600701e0041350143c7c014a003c01c0d0301400b0a60800300102c08280074003020320aa2012600c6162459005407080c099003021910b50350007403088a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 979435296 1250 979434046 979434061
    0x103140c2b1401020306120601030206120612010e0c1f0f110f07031401061a040306180f0605060f0f010221160f0302060f01081504020111011401080f0a0308 69
    0x114000040604424007000025030442c440c0600300d1048000103881e8900315003448a02c11076217a0002040d0b00580c01000140e0303c3c03a0486171188070810b03004ca01a240d100100310300d00c1041004080799402c041c42100400c900180da603542c141c007143c10b2034a10299800079400c0b00041c8a0303510004054032000c00c00329015090700c0c0100c441000c00c869501c02040d0065061004613001103481001d1400301c46030701c644c2401040003034440c100700080488522102c00d191403280340f100404040d102c2040588005401c040100080c0d048403402c458008a803078110028001102c2e884d102d20000b0400800c1d0703080c95020143c4042e8103030020701025030519140c0c0c0d0101c11004501d05540c400300988c0700a19104412248454441d40780c1040888151a000c0c1c14240c0060104c00180ba501c00108030020703001440c80c5101d1507181060b80243c4481c00100c56030840c101c0211829803c14115410300140c841000d03049807400c60650b8010260404081d07184e00c025000075000410780c074003003690b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 979436546 1250 979435296 979435339
    0x40203190902060c01090b0901060b04050a060e030c0d060b2112090a03081314030309150706060e10050f031c080c07050601031109181b0111030f030103140c 69
    0x150000f40300c9070070551403030601429680c6407070007110030601040c00d100020209024140183c0001d15075503040c40c3c00e220118001050a101d20340801070761545030052a1418004507072610409410500c01440c5810444003910741891201d0007019010844010142042c0c0642c00030f40910780a1301c5448140e124244032600042d1000e5448030980400200240340c600040c5509070aa1844a07007a0b440c0800142c100307000c500c005806900b0030800a400b564903d00d9518088030b16403905512154141003080c0100115017102c24100099402d104000d011990741c0c0084841c21a001c10411003040181a01c440c2e04640c840100300c001101540384a000b0f2007260740c0100e030700202505101d042c0d1541481c000c000ea0003581d03050b038214050011401e1000545070700804540c3e520203940703000c8210315030f10100b03180c3e1441c2103441e018040b21240c0c0b01d101c01000340d601d440c080b40c0c2c443c0c0c2086999066a8001c1c0300440300461400d0301c0703400c40c4c2d401084050180c04014801d0400c10360500358940c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 979437796 1250 979436546 979436561
    0x103051207110d060914010605310c0e030c030304030804030f080d0c051803160314010b2215080304150c06050708100609030b06040e0717030d050604020319 69
    0x42c1c80d190720010500940380c5a0303440c01024059980803d00c5007450a003014004400c908010550341407440511594503104182c03c110040c01d00344900017100c83c6e007009481400c00344000c06250401307240300c6e48640c1c0010b14914280c001c07000d541c0e040081c0010165240306a1000405001d0140410004181a00080300140c1c3c0a680d28900e854514600e09044401000590f00410070108800d50f29655007400680005800d070010059040c41c1c5000c2801e2200074880200041c440c02107070000c0d0380b42074001500c0c0c0d03032014081265050b0b42c4403148601d015945070041c401454407003402125135174222440b041340c4a110140d407906041460ba0403072401c80750311000c24080200b440b800052540e1051910590f140d9551008904011221148001055002034104556844240301040203181c3c10303504008100d0b00043c0c04c80d00104402d0030024940c1c40003141d02c5084105503810070003c0018414042404002c00c030035036074103040204a000603504043c80740f03071840301409201c085602004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 979439046 1250 979437796 979437803
    0x10f020723010203040f0b040807060305091005040c0b0f0d050708040f0b040f0206040801090606080d0f08090a120215070c0f021c02060316031404020d172512080103051207 76
    0xb480c080c0c0700c480c841c6d000c840540c841500c01c040094100043c04040c004440604190301c0c0900c542d0404003042660b07905668001440d05503070304041000c22a100d2444401040100c80031501c40d04500ca81440b541c1100c0d00420181c0d050100090b0000d04c40c9071802e1003950b1084031000140456210640a0240203004442c0d6003000515100076a4036480600000d08101c40042100c4441d8134020050f02e085e40e202545592008980c0407a8031b410403c00100c264462829844a560380354549180078402c1c4009054190081c9100200c244c2c08502c031246807aa403620054261201c580807181000c54041c05020155801d5541006180c4400f2040c5034641e4110785496041d280c1d0001481c3e60300c15642c0d201780406800d41488891340600030500708244d041c3c112076807850982c0114481112105000700700407612200c50100c0201b42090321420202c40e0100070000802d44800e44039840f02180568160f14088840c1c4a0702e4820900d06050700d5104025102c8c0c2411502c000007540c103d078004a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 979440296 1250 979439046 979439053
    0x403050a02010f050c04080c090705030a1a13020a02070b0703080c0a021c020606012c0411070606121403130603020a020c150307031107321b010f0207230102 69
    0x7010902c0860113058020180c4041d082d82d651f00e0004920b25240d504094030307014258150420a4054200b81a02e0303211242120126940e80054034140d0b1211542c00d4050344940d25a40351074003852568050310a40e0182d8085601d11078440c00c03413000c2409a00702c010001154400050201900701d000342c03100560500403140f58400300740a9814091142c2c0854005038080301c1005850360f4030040781e030805915903007060511008046907004214407110150701135510780d9880360300c2560385d1085400441d00400c041080c29101ca000802a84480301c0664410640804080d0307130003400f20448201030b1181591400301894111300350301135000f80d80020258090060301c3742a41c1c884150b9a03465101040c861550f914110754054101c1d01c00c420034078a0307030509001e480d000401d500b00e4a0b40000c070030a02c040019200045042c926000b507d0020900d00502c4100e0300407440080507450406000d88420032006141079040ba5503825610800c200395401e52200d000d841e144042401d810311061055 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 979441546 1250 979440296 979440311
    0x218150618091e060f01021c1403040506040303050f070503130503130f0513020f030106211805010f0c0207140424060e010207030c0512010603060c050903071d0403050a0201 76
    0x7801d448400c43d201d003030f11000d04065007410891020201e51000c1c3c120b85131202040040300003903503001400403407019a242d85000c268002d0041c64480320010400040903500e19081c6050354555005440071404242003e0100d11082003454006200b0191940c400d070455861090f68003c20078002d00c20340391400304100f4400e80104800c040400742002c2040841a580f421042c00b200d81901c001e290301851040c00300801c000642c10132641120302910740004419856981195640f03121300060030003515129404800211418513146102e0051000304441c840b55182c810548039101c008800682000c0c3d0144a410010ba01400070420003800010b4045541d010b01030280c2d50040908041214401c010030001754003e4244688403003e1026040f850703d1a0381d15001c401c00c9000d0310f8411a58160903000c41c0c50258810f0001350b42018041c03002c40841d40c1c0c050400c3d0704c020145402405013079404a00341a0f0003040072485c2c0a08181254642d95548040b1825000340001c3d82c11035494190 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 979442796 1250 979441546 979441549
    0x50d020603190906230c070302061812160b070e061e120406091202150c0309030d060b09040e0f060408030606122701180210030204050301020409090218150618 70
    0xda02084400101740c3c08000e5a22091086080c800408182c1004410400e6500003540485d90300e40100100d95607200e10b524100c034041c02c04981c0044c2c0b550724100400c81001940c4d01e200b004003082c1c015500c80c5920344805a00311000340b52040d207039801500c104031005c1c1c185a109008850106421441410540c101e481c50f005844d0aaa0030740301c10742c40e40800c000340400b440303414070280054001000c0000d1100107040d1540302c002d1100e51170701c0d004030010708141d60034002c0740d22000d440b00c401c1101c0e6444521070540c035089403403814001c91a004400c622140005030800301d2000c414000c00c1580c4d2182d1307610345c903544014440b43e0459420302100d228026a030300300341e003e0590400e00300c46c5951500c041849182200321398505a038180003242c2400d2460f01d5074a40c1e455010781e0100290328420038160081d1203035a000540640c400140000d00d800c4503400440c1381d038401c4951030200200000040200720045d07800140f604030195402119182410003001d01c0b182c00403414094100d02e50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 979444046 1250 979442796 979442801
    0xc0f050f160c0e090604030c120e0424050609030a080901170709150c020f010f031127060c031804060e090609010b0a061b060b1005070309050d020603190906 69
    0x6500310b80120000000b44400c007000d0f8103c503844286800181010300e055100140003030030010014200c000e01e408400e200c0761140c13241184100c0007400034014110700c400e402d02140f410540b000c2040480c2c0c00d01180c5850007000b01c0d0a00f00d40140109801507543d03c87c84540e512091080d8140300086003c460400c5c2c041c409188200c03082d803680b480705c0d45868408012148900100020000401d030030000581d100e852a580c01309007882d003541c0a103071511058005004070240d0564859003c107040380c0766114400c21280c00c907581142c5001c0a04140c3c140980c074014049101e100790000d0016040d441158142c099031284024000b0800070b0346c8010180e5001001e451203d1305030406010050400000d00900c00486000d03101c1743d441c1d502d0040c0c002c03c1e904192510b01c0100000158800600c0416045020285001428400a903c502e000a80160300080c003c5000c40c803203070300000382c03450010a684001c4d42c01415042c5540d40710030340d403544851000c0038502c009076224070003030104600c1d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 979445296 1250 979444046 979444087
    0xa08090a1208030a1410120213021602010207050a08120c011b050a271e08011404020a23060705030d0f0501080f030315120a1e150c0f050f 61
    0xb56146a602c1c1800c0882500340d900308212030785001002418071800300348050783e0304111441c40d4042e01009504c3e200041c0306500ca410700703040143c0042100e9607003078402841564818400d8084400b003569a900b808514031251040d51500d40142802c403d1500303103d0700800c1e502200f40000910341e15241d040c0e2000388040500100050b0011422006850304103405044440c02002c182c2c82c2a00e41d0312111040042500400d0800c10843c46001002009065941c01a1031701800901c401c10b0040088909010211426813282c0382d98007002403d882501211111035100300d40350f00d650070482060081310b5018000072580e43c0720030401804582074038454031b00400c80c1d544010032194500042c01c1d2501078160fa0403489900b08106001045c100c184980c0b210074400d49000b40510208010541031164601d80502284042c1c04d402030001c1c1c024005002a600c110011035500e40c8480840048421500101c80460401400740c1191070050000d012003040c0200402d00d01400740d000d1100e00c011a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 979446546 1250 979445296 979445303
    0x15170312010b1905070233120406180b060f1f0f02010f0c080a050907030f0602031009050c0901080901020d0603061508060c0d18020d0506160e01020a08090a12 70
    0x1003651000d2400c3d01d80001c0342500c291a00a0909045800040b400c07003480c0203001090b4000301400f0703170030802c460050060381c4001144d1a160444d1000c401902c0c0000c54044a449141000c401c86000d5490744c02040550010030000a40c0e88a106200d402240c0f1580544d0084504502004030541c14041000e022040d0740c80418032410100040e082d03c4036051121358060528115024450384045842d0340503851610100f1075849466506003000b03025000a0003122a0000380b8050008a800450041c1c400200c40b604140d6aa108481150001c1d2004440700704c0c204000c2400b507125460f080d13045004880014540003400c100c2c80210361456004540d12501d60140700c0d110000201c0c02801040d9210203000b851400000b02c1d9410b10a40c114501c400c1e9440348c0b9603100d002d00b9031240c00d020349d0180800041c800b85080c11a40c400c0115114080707000103c03003041c0614418005010b804d141030b001050340240e9540c6140e00c0c3e410604485420006254000030329941d000000d0515600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 979447796 1250 979446546 979446569
    0x10f0207051e030c0318060408060f010303110712020409020a0e010f030204060b0f040b1810110d0c0308070c050a0c0e071b03050d1e0e01150501031517031201 70
    0x24070620101d02c800d0b618820300c1d041d030030a00ca5440d0102d00481241e42030302d00b085115818040d4075000034814055900424040e100310002c0010040441e507400d07040c0ea000c3d80f9001c0c0b040103001c0b902d81d03654042d0b009013032001c08001c2280380182000e40024640520050009220302e465080311007072451f0903031008045a032599420800d40c1020701c1541c02602da901c401c3d51030300180c001d00d18103c2c400c51281d8070f00310030f0001e045005882100c907a14008640180440d8500c0131412000303028001c5a80d82c1c0c0028040c01940100071070107440d07038400c8242d054903009d00e140d41c2e0020503101c064076650141d13101c1c058901c03003400043c0302d006180080d001402c180b040b142010200100545a121400c0c0d08402e0440c030004040394021040d02d40c02da0300340d40042410000480c04180d10600c1034800118142820381d0844d03c0300040d0805810401c940c00c3c4040c0455440c4011401c1d51398890400d5959420b83c0414004580002c43c68400d901501044904c3e00c01da4107401d0700e41c001e00b64072000f00080c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 979449046 1250 979447796 979447813
    0x60d020907092328090f0c030c08060d061508010908190215040b07270501110c0a050f0604080a060912093c0603020d050a0212070e03010f020705 64
    0x901880d40c2440c3c9501d0b520400340903143c0045102c1c84c056200314206070141080484101510091920207031149240030700900d00d100e04510050500001c80c00d01080c1040000501d1a02c00d048451107840001c2c0841816440c0d03849480090502e822400e0703103800b0142c0d010400000034011a0070032845405010b654080030080e60000084d240f02a03000c41d00b140801c01d10841072004400e8015030410100039280d15031400a40e55280380c80c5040701d1009900031400d0f140480c100b100f004680c0c1c281c0b1000c0b00720f0b0315948941d07100d4103203400742503000c20208024417042c00c115000c191110700107860f0340e14180c1c64070021450151042130484030b440d1100307040010011a600c8070383c400c804509207000400e09240c1181c2c00d090840d0211814410702d48a80030100c050a031003a08451058440e1401854980300c0040c0a5405032040344001814100802d100074420310031252990070346c000404013522858801c881c8402c484001c681e0540d00c450600243c80f00c148000e1110030f1040d0010302c4d201 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 979450296 1250 979449046 979449059
    0x81204111002210c280b010e0f22080d0b060313060f1107030e15130906050603012909090a0506011b080901180b030108011401150203070b060d02090709 67
    0x14070f00402107404200c05000c007090441000801c1381c951002c8400001c110440000c8a03c041042072102815103241e00c000029070560910340e00d401034401e0301c0c03401c2c050307543c1c0c08640000c4104414521389000d240300058001c0341041c000b4001c075151800c5c0100344a004840003580755002a1403101c000b240b4142c5810070003016118118184075010350601502c1c401000d682d01a020f403140250600600307099050705a600c038100f1038004c1c50a03411450b01e41d5420811404014414041c06400928040300440c503483c100e0145c9040f542d07281d031401c41081211964462100f41c0408015030520180002c502a54540040314801d944c44480080c0c18038146c0001040c03010541d800640009800c202040491112400c64581c414282807813000380652500c446000c0720f07142d0014280ea80e0100c00419050410b4005030625107040d01c1000099803105061009802241d24408c056803042180c000082c1200c030320345a004000520b10301c40514160041020711504a40000c0094000e003000d1200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 979451546 1250 979450296 979450333
    0x60b03070f09030c142715030a020907052d1c0920030a080d09050c060c030a0e040f0c020c04050705210a0b06220909081204111002 58
    0xea000500e80b621002c0e1454803800c05201003406285c1c3d00c03400241e110300c4151100c04000c1d81541003075030864409004030702c034000130250071b6920440707100441c03548107440e00d030000710021655002001c0080e1038540003803c0d00e09501840c204450200300041c0555a01c900f1082c1d200b600c07403255000c83d80c8014407210480410400008000030b036150085001c0031070580c05038004041c0500e25004120f0314cd40000070720300f161102006190709000556440d000400d50800c0240364402c20031103640360706030000c0281c18043c104d014400e603441400584841c600c210082171801a01810018000b03034030b1304401c000c1e106100291400342e4891981d52995060a1007001e03070002e400d1070410700301001020320040c10481da014404482c5a01000302e000c3c03201980c001100507c009041c030b59035404140b51800c10542080381040200744249001809000c1406980c400c6644903403610302e00000040c040c03100b00b00240c000d41e504c3e150400c0c48115500c8070a841020100c06400074500d24040d000d2000c0e2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 979452796 1250 979451546 979451567
    0x10110d210c1d01020102160c0305010c0503061815060a18060305092104051c1e020d03110a051b0307050a06050426011103151905190801060b0307 64
    0xd9142a641c12956a07120741096080d020705040e040e0500d403200c0040f406406403080c00c04411190400450400c01407603c01b070101c0c0c2c8a00000e0240c2d0155030001d4841d03000c100c40c0d45401882024035801c2254044640c00e41c41aa41d0f110800c400ca00c42010400c03641104c00c411000c81e07417652820b04003103220580348001340f02518060045150403011240c8804040c0300c900003050324118014200003448041c0c030003400d00a08031038001d1250001c41100e45501c4001501c24146610b02c0711103190081c0d07054800319802900c085107104503540d04403800f0411903111001c6004a001100000c1d00c2444210201c00d4005101e00b80400000201410404164060361148607885010442c140e0400c0a540454440120403501807500070200100181003408020641d440c0c0800d280003805420061401030301021020905416080c050000b00300003046946580150150100050300e084004280d035040c1840b41d50145607038070780180c0d00751413007900105e10b004004010400725551006030b140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 979454046 1250 979452796 979452857
    0x1b0f040807090b0a05220f2307020c060a140d06060f03022a0c030a031d0f0d0b060613090c0f080417160c0806010e0601020303041e020402040e070806040b0414010510110d 75
    0x350103050800e00039687d400c0b1144040c6c040e50b0f010851451590182040b11401940820713b15076500320f0088a0000303080a010f4000800c6070b01c000c1842d01031191081d01d03c00c106444a42c481d80c0101000c0f4178002000a407903150714070170030300300c1c0c600c41c0c5090141c080c3ca140b00751200310180e0146601d500c1010040c1c00401e000391a07200e171000c203a5440d01d02820710503400c81810f8045850b810081f54103480740e0801141001a8600c00085204a40c0c1c85103002ca01580c0c7c0b699070036000b41e001203d01c8001036074058644011030142128080d040c00040826107801e40203045a4034640d520342c07058100320340c0400305a070410b900411403881d002d0f2183d640500f003413014500c0d40c41c0c550343e80c5840115580f0104800c1c2100c181d48411500e0f02d604480160a22168a040501d0310100003803906c281208d003540540e050000040c01c5003020b00883d4035194a5541c05912a800c041c20b200d284500e104070f4034100031860105000e40c1741c00703101024500106980300740480000c40705001c0e001125250301c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 979455296 1250 979454046 979454111
    0x609040b0d110a0506070b0f04020d0c0305060a0c0509182e030b06190e060307030c03061a03070501020a060b06090d0b01031703100308031b0f040807090b0a05220f 72
    0x46c00003a0080341c4040d07000301000b00b00b405503182c5001041c0f240c0c126940040001c1e00c94100401403050010381c9520450280d0b10501030001a014222070f2030285455242c0c01c103103d02c0f2071012080886030700940c07194809000d89040101500c01c070701c01102070301e4845099a00d00c1428001d0084c00e08110f50300074003c4e201c60100d2480002c4000103010144101100080d99001103280e580d01440820b00950300045a000c3c21500c03418204d0081c4910128101c0c0705204000f0349041c3c0c100400c0c0c5000b07d0704c0c140c018040310f83c8c241c1c5492024140c2d080c071040c0d010b01d0810410301c00c1d5441400d21080726004401c2083c440d070452601c2c1802107220305880c818403100341308000c0da041040d4a003c0640c1d03809094a40c5a03100e1900210020750800a881c40c1014045069841000500050021200c081046640c1b050351020079004803181200c0594000b002080c3c140181d09200000d1000401020038181091600c402010300b11034101c0c100030300e1a900c90308a1002200e1141002f602640d18071b206 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 979456546 1250 979455296 979455307
    0x11031b101a1e1908060f01180c0207150827030a03020702061303060c1202030c1b1207080406140a020c09060f19050414070c020609040b0d110a0506 65
    0x41030081003040340514803640c901e1442041c1d20841da00c0080e81d501000d0180f02008004070031048501c0e0250050042920a01c800100c01c9410408001c1c12521440784054680d410707220b0704000b604081c0801800d40c40f40000000311030511098080d42c0d1902c0765240c100070304003490f0a4000141c2c0c00415003000414500701510048007004a85c0050074a0400594480c0349102040b4607009140c4c0c580d040c1da400e0f00001040c0005138002c565180b02075528440820b061444543c2280800d40300c2d82e85084040c0035040c609886041880b8036688080704499509244001348041503000201c129820540802d0800115400c0300201c0b8221508003142810241034140c0250f44182050f40a4481c1c01341e6408140070b929107945582450304041c18031980ca0040d07140c001c401c0e102510656005926044d00d225003d0003403903800303000381c02503039400001c410340307400b000940d40003088425070180e96544081d00039035522161402c050f100f040d6006025200b1420040030b81ca031603102c6405000300b01706 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 979457796 1250 979456546 979456571
    0x9010c090f060e0d170c16060c150c050f0a090501020d030615080a020409020708120f0708041202150f06180c070201051303060507020f070f03030509040c11031b10 72
    0x880c1034000c1d20000300c0e07020035007019100c000015034a003105d68000600c40e0400c940100e011480b115440030700101581e40e176003003140c0281c18000d000d0480e0207440c407031400000458001c484559490724005040c420304135401d00a90b84201003100211786000740400040d601403040c28480b00190908110311894a00c0005001a0000c040020000b1000001d8200c01866050754090144031301f0854039039400c2e18046e81e055000601d80c11b44100c0e88000104000b080d4000c040c03041d00240d40d03c80c0036454079034907104102070310071100056018181e4440d1a01004000b424419441588041d0450510310280450601c1c104030300400c4181000801507848140310840d00704e1503080c60801c1d501d1035984540607000c249174100401075800d0200b44003c507a4000f895621240d804010344818544d50046501843c000d4440107000ca2001d01c1581401c2c602980603040c0a141c9041c04803120000180883c29030b407008a459040394050004543e600c0410081d0000c002c03a5108100461200d009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 979459046 1250 979457796 979457807
    0x7051b0307080328060b040e0609010f0e090f06040f120c0c1701180516230402210711070e09030316110102030109050a0c08040b0f06041409010c090f06 67
    0x1070100b5540d900099020704805203c0103130340e13484c003242d0008200c440d8807401380d10000d074007d02c290765000070312401140c80d91a00e6a4ac280c101d8024001e5203400c28609240030648803070052408001340185030100250790404c0c415a40314500c5a88100c040f4126442c013480714450031503180c020004440f4500c000600e2401200c0190756200e02c0044240c840d00c04d01074058000d803440c092039140070303071103900030080000f80c2d5540111300b000c8140c165913201d10303414802c0801d1204c021740f00304080c130164046040641c0182101281d1160440203000301040103038459000340c85910004a2075405038106001c03d00094010b0000d50345c400007242801612940d0340d020281841540d07192501c2241c034040d0090b210341c01050300702c000a41d203030f696400d0240000d043c125101010642040e602500c0c6c18410310051b44110751041d44880340c0d0321442085011000001d06c01e070740140e80e914a40c011181c0548610744a040220001300d40d122810a00601d2a8007039400721442011142043c0700b500e4000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 979460296 1250 979459046 979459051
    0x902041e4401020f0d110c03070813091a0312130b1b100b040614030a0f0602090a030f06060609060c0b0a0204090204090f0e1f0902030109020907051b03070803 70
    0x208603460306080400c4070301840340e81650780d18190761001a41d50f014407040c4020b007036503064078001013016110b40214104244566540d03103001b40c00401c00e100000b001c0c0303000b5003203506401500300c621645501200c000c842440301102c503002c03900b410b800c9172441c3c10416005c6007142079071050f0a01c4900202c50012000a00414050b9540410142c205410140c1914000c01c1d90004440f03081400d10b441a00410314081d005010700e0500e90085503a00390140300300141c000150003405200099241c1a202400003e030032a481d5408000c0c42140741e8800b030191000d940118000c1d02804803900e425811103c295001400f44480000d08000ea41c1c2c00030840350255070040720028040d80d5182883c1c0c024880c58002aa6051002c10003040c200d803d94080c480300752100400b04032140d00b48400704d03503d40c0743c565410b00c020100e60064441800d290001107a25102400114454006034000740c0d041f48101c80680020328046014019000b000240003100311381000614540443e5440300035003403000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 979461546 1250 979460296 979460369
    0x3040204150b090103051914090609030403031706010c0209160912080708030406020d090f141609020d060503030708090310060501020c280e1603050c071205040902041e 74
    0x4440c0061108242c8940c20000e000410300100700407544010400ca208c002030f80d050902d0f22031580010110f19001048800b03482e01502c0761605482c80c29016541d114000345000d04103c9002410360040e00c801401c98007440340c1c1c0740c42c08041c3d8401c02d0b004004401d5a440350081d0b0003044910804181000201c55085404c0b1600075942da0311403d0080c01f9100c1d0300340a0340d14501d0f020304001070006c040c0d80210120b03c640c0703608000c0c1c106243c0d8a50f0300d2882c010200750042d81ea50081006c560342d52300074500c44030030282c040f40a0f42c0d01c8002a085800c60101907920500000f002c0d0300070315003440b200a04000c108410001702d070a220000f0759881040d81d8150058000014428207007c4500400c01081141b18064607072a4032072040790384900702035840014038103c6002c2040958001e00a0500c9510041e020a00744040c545403480203880884202003845801c2101240d10421800140041e2000000b610b94500300341d001405400300b00d43c0102039800111940140e440301e8110030480050740b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 979462796 1250 979461546 979461551
    0x3110d0513030f14030418230f091e010207030e0d0302060705030c0403120f18050d0b15060d0c020715170a020d0903020f0712050715051e03040204150b090103 70
    0x5031030642c006420840c4281c01c51701c408100012451003d401040d41c80d4074001050100f20901c0043c42a0821030250360465800340e000001c0310100a904d03503d41c4a4041c8045594098080c82071316061860b8460700300303040e50006129402c2c5a005450b80c4240c0c0c3c000e40e181c00d00301407070b528021344500c00a4030b40410010b0020105d24201c186205072800346800c10012210070203800d80151101d00740344d010902240e00000d00c510b12030030724a5400c044810180900100c0100f5a03540700410310010107003000c140304581c800105469203000b44c04104c03884440000c0710301c21101d000e80b4207500740e4011211844008100d03900c0503846004548038820a1104181603125550031101a004120480804030b14094221042c158001080400480440706550a19403a81600046503c0382113024180b58055841008019040701040c0501034252810909002e80958144096180364103042c02c00c034004028081076203010b11510f039002c0981031082000d40d10b4040801840c3c0100c1d10b0203030505d42d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 979464046 1250 979462796 979462823
    0x1e0b010311011e0c05150a150806010b07020f040e06042f0a05040902010905040f0605091b03040b13080d0603050f0109020a090903121416050901121a0d03110d051303 73
    0x701080f14044554004407031201c6c0d072511021010042900d014a1440d40385001000150740e880820742606885250030a28506807503030b001e114030440c8090403181c206554400e25002000140149401280711307003803006c0620501040c3c40e200b046100480a0401100164400141e43d4882000d0440d0340035a00401c2e582821300059803103854039803140f41c2190034130b2610f0605075090392100c406d40340c1c01c07100c680c0941c80b5031002a1f03601100301d20002c0d8840040003c82d0120b0120003009074091040100c4841c01c040c299100341049c0c203e80030bd084082d46540d401d1042001c24440101c0c072000050081204c00c0c407a0f0001741c50078015100380040159200e01450034540b0030344208105000d408001c0c4225594078920003019442110b481c1c1d01c0c10381508801400b01e104008481e02179034169110000c43e10080d192100801c0d14400d00d1440151002c01d00c800c94035080f20001e00365000c0d480c0c4003200120703260841e0502c4004000c0302d0810104204034040700405550132000d407504180c000c031010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 979465296 1250 979464046 979464053
    0x601140d050c1e09090103030509060c010614180709050909190809150f0304020910170d11030703091503150b0d060608040b0604091e0b010311011e0c 66
    0x3845450185201242003404101180203a2030042c007030f8050010f49524254a41e030a400394601031800c099a01c858601c0041001c40c0c89107000d0280c01500070700061a06070400085800c50341c1a0303000e01161801100380b20401d281440303001040d03481858a4010074a4440c400a141010b2406014403238003900000c1095454108052481356403113004400710b42c2800d007824001a00203203c0684180c0124100c02c900d60f030341400350f036801200150780d903003075454640c200b0203001001030141e00010380b54a40082c100c01000302d07401032a20141c2c003410782d03082741d820f0003070502540d15110501c940c010403000000947c002d00306c00451741040d149400340341c03a11070304402030f08184082d50310b0002d118801143c0b120308800240410303081c00e04200180daa03034407002d40d140e0408550240292010f90005a11070401c2d41024001500c61540b01854541303440248074061680b8406031002070351400140f042004820100c00d00d00e000742404e00350790b2001d20030303e048201c007000300004211a829403c0d042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 979466546 1250 979465296 979465337
    0x30f0618110903011103010f0f0f030602070503070b0c030405071415032d01080d081308070c17010b04180b070c08040509040822030510110c16170f060601 68
    0x30b010014000d1101405c03551403880380c0d41080c080d80441042491000400d807800b00001001c448201803620305403441c503224800203400c107140c1070b20107002c00c00001e40081c05907401c0510600968800c246c0301d09060904e2440d0400541009030292443e0303107012420364480c8031202c6640107000e00b02d9901d80c3ca141606c0740313041580c044008010361000007142101c0e16518640d058411220442d42e03184e0b2041d41c100c0301c0e51401d54600031071182203007080f408500498020815540205a01407000f0b030f441715444c4400702610001344559564072000e10300342c605409280f0741c0075440024a0202c041e01e4a4400c0040c80180801c024090800c80d0182002440010b850040c44010544042880c0600300118164805d101e03e5460403c08546011a0a0940340080940ba0400c2c0200a50710010078600010140e00510568544c414800b079243e400d020410500308480d00b0140008240c0740218410b0b14660f50521000c064000d50300d4080d1f499800150700340c0c000c80900e0045d115003181c0c56903955 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 979467796 1250 979466546 979466557
    0x15061d04140f0613090f060207031e02070f2c090a0b0f0103030306081f0507051c02070210091203030b010c020303030a05090606030a0503090409020a050d12030f061811 74
    0xc1e2000e0900400110480360809184992400c0e00c113414070741203941410080b0f403810f101c0182074004103803100011401c00e0340074200d07103071107820502d04101d410401d040528408103024401039101410a1140463303001c0d03503c00500c1c404042c0c43c400c10168030143c1c500f00302c84107400c800e42007800003c4d01c41d4a08000c1071001e25000030b0040ea90313080501005000503000d01044e4040303070400d007001646000000d801984207548001c500b85013105c54000c803000d444040e02c024100001440408a9805090030200342c0e40c860030001a60303007249106111001c40d410396000d041c1b0a6441d400c01092000d6006407881c0c507410300d400160440d4210059505c2c030032015010b901440701004004009400e984020b001e851b15100300c551b02c0e07841e1802c156440341d01c2d41c4001d1494000307009401c1103081070380084003102e100400c1d44041d03980364404202000084107090b12042c0764281b014100c5609842603042040700410280000b50801991203880040b0038800300e40390f41d5507000300d0340b051010001e552 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 979469046 1250 979467796 979467821
    0x4030623011e0509070e0d060e0d090e07090501020a151404051005010b03090312060d0501110d0501081506090a15060903050f0102030603072912090115061d04 70
    0x1a80d61118010314550a151180c10b100324500360001c181844e00464180c400e0b103a071ba035402c841e9954030007844180645004101d40701c5403206200f00d02c124090091551120b00360b56902c0c0c036030b46442455071a0807000b4100710280240090248200d90740400c0e0b02c803009400c40d5016030041002945580240100d0300b0030010100080c00340000c000d008100c8051100d65200705002c03070790321070074500c09620041d50741203807580c01009003c42a0012060169106e407000304124100450343d115142541c1d04070b41e0f031031641c0304c3c00200c801103580903200716405080f46100400040b040401c03016200440035103064450620303600001c0c0703414425009841e045d80b591644440403942d0b542c024218482030300048560340911980c0500a21051080d6841400c0c01001002154604804a1008501c0000c8900941088518480e24148010040101e00c100c00c200071481d15160800c1802c640512030612000900035108010255004041d40c1a814071021502d801c0714400001800a065000011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 979470296 1250 979469046 979469111
    0x80a0c0c05030a03030b01110705130903020c030d020705031501060c0803190914210a0503061302040303090e060d030f18030524061503070302251b08030f040306 71
    0x2030f4101503060300405000b040a80b652014000f040105039251592400b42075002003c8100383c0702528203d030060100180240151089058031002003230a0111491414015a0000700208040d0808209040c41c0020040b880841d03541009070042c90340c0484040030700311010200104407811444401c6c21084070078541c003005544070303515059080080f00b00404a07140512036101c0c00d01800b20f240c2a00d0b0314502c81070a03281800585050700d080d040a8542038003c2d0000c00c0201086850388018405507009444807506145441e010200c00c1034010308407070180d0074441c49280040e8002c907480311002030341e00b0010341064040110030103000d02a030010302a885880755501003d01030101d1740602c00c42c038069003049942d40c0000d11180d01101650384524003001c10000e03008910a0b40900071101d01e5410781c1c1103100b110082484ca090303000a01340e404022400042401846c01010000101780c4140070b9420014070300081a00c1f0702641c4000f41c80692181401c00c465601c0341d11003501103c100280 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 979471546 1250 979470296 979470313
    0x30a080a1805060103051e120d02040b04180b040b0105090d02120706120f06030b0708100302060f0309060a15030809031c020a06062111040902091f050409080a0c0c0503 74
    0x540d684840a100c15942d5000d03138141c112141c0404104c00214036030b9400201904481450320700c1e46580980309c0030391782a60a00001c03580f20700030802440105031805441007152140d6138490b0441d0b94400302d10b48180c1c5800d03812149640c1201c186e941c404801c56270030004900030300100b188003070840e0b130400050040d0072000c145140c10032800164082000010400107010742d450004450160002500c0091441c0c00116a284594002e50340301042401c40007109a41c0e80c0071400c550014010307801e8183c03010003003220380d48081240e10792010b8104014030001c40c0109070410494954007000c0c0c48041d000480310070360740b010002900007c1a020581c1e1610001e82002912a0002001102c01a05280000482101000700d03c19002d18010f400b007070003030043c0d0b121600400f0328142a5002a01c0b0744c404009680c484600c40e1182414024031101c9011000c0c00e40e0210000e500140c1c0320f2803926031030a01154200d001c1da804100e40d070510181034002ca09015458a5a55020544c5071155940 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 979472796 1250 979471546 979471553
    0x90c0613061b03020703080309030712080106080f0103110402072901240906030903020a05060c1c0203220510110714062404060f033002030a080a18 65
    0x3000342120415541c1041c002c1c1d4a04006809582c0d0740e2000d001607004a5061012419503070007150090040c1f41140c0c43d080380342e5075062100d1108031030140440c03005d100401c01542c1042d1800d511960340c50101842d90704542d03440d03140c45542c0080b00d010719804103000080056040d000c0e500c0e007a40d0651400e4040d403e03a070103890a01c2c24021201703008a0041e044000026100312005c0c03820701c50711410419410007008500400c4460815400c500c01c0c0c01212010642c1400b20f54011001030305a99560034008aa11862200c242803550380c2034810402c02a460214898050030360702e03020030007182c7e01a941023030383c90443c107455040401850041803080b00d002c41c400404419200b04840a190118074403801d4071080b084514038030524030828100c1c2c25900422241c07400a80040c000182c0786d8682605011614241d001115032452714000fa034450300c6905240b0300702c80c01e0b40c840d900341d41c1c006c400001c0d2603000d410060700074001d41c1d401192075040da540140b0b2a0144000380c04003842294203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 979474046 1250 979472796 979472827
    0x5090102092e0f051e041805010510020712020609150c07030b06010c051c1e081906050d0321090506070806010f09030212070f06050a030b0303120105040203090c06 72
    0xb59003400355048074080e00d000c54000c441e40b01450010b5142c2501704144158041d10030309030807030030322000c800070400802e140c62984807540c02802c295400044a6050005100b98490901d00d088103641c0170300001c000c049502d100080c4a29815030b030751611003800c00b002c00c0203003d2240558100c50030205403501000390001e8401c04503802420603c0720b41c0c03196070042d02c400e952508040c01603041081d1044162401d42c2194081c51094601402c4601c00880e611520792900c06a580000364000207001d03009961150041d010480d0b68002c0100e01e20f4040080c2014044450080a00440516410540b002c1d040090203c4407488030a2107158240e141150329040e040700c080010078130940203e02c1e10f5204000410b40002a901c03912071190440d000c112040250159401d103500c1814004200102004000c00040c40030fa11802e03110344000700040c003a200c8110030306020b41e000b407080a08c900c03080340e400341c11036070292801652038994194030360514003811070b03080c0c01c44400039225211201d242c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 979475296 1250 979474046 979474099
    0x1209030a080919082503080301151101230108011b0c030324030b0906040510110c01060b0c0f0118030c033605030703081909080709020a080c19030509010209 69
    0x3e070064055400d030f0496100445015006c040c0042c0c1003400140b01a20940d50a82146001760074040c580700742581e01c2d01e00b941c4c601c00c400c070201070009d4071141140110000990150102400a0161001101554000144581c1c020041100b11121391043c140294005a0a0495001d10301200340c6224403030040c512140c401140e5055511000581814000c155140544c1d80480030301000301c0030030303042006001d0080059600650801420072401401d1142c200180006a40c894035107007031182c0c042c01c01e0480031400e1130310303414011803000d01c072503110300f20023000c0c4c0c50304091000702260300382242c540016141c00c288407000148132800051300c008401b004c0300b100c811800d0030152035000341500c40c0010703c4000e10720107061081807140600d5000201030010989004603500780d44813404c0d03242c80e07401c0d440030350903d0b0700065103010541d010a14961041210001520704a161030854940c0024640071008140d03440f408030303821807000c1d0121491890000c0a01d03008855003204559001400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 979476546 1250 979475296 979475323
    0x30b0a150206240904061505040213140d0b01030b1b0d0b0a080c060706092f041a01020a030c0c0b0409020c0d0201180b2d06031209030a08091908 64
    0x1048007840701d40010340c180380c01c03c400903026400c3e64036155102009040400d20701c1241581d45000840c50351114809000c110561141c1645001d181600f100402c18100603074501848451410f50007242e00d0101140c112039004940c14455510002009903e032115548024076800005607550990003c1d000900725040450308160010369884400d50b5402140e0107940e001001400340c4400324110307a003c0c0c1d60290181b07001c61042052803141a2143c1c0c40200c2c40d40703030840d20f40e01c01000c50420740310342e564452041c03001070b10182c8400000303540c40d00c0341c1000034100200d1150200400c82c280111a000341580b20f44c80c4d840d29180c0c109030000c6e4000400c0f2a51a1140081c0c0e100803d205000e0050082c03405518031300c41c151952103001c0004c80080964940c8c0f5900b99092810510500c1000d100480030740031305030141402d0003010704007201c0c00b8420f020700c0b10500c104030603654080b0b00c030200740742e001034040d80c0c1d454042d004c101008001024801c06e20504000000c0d071100114079250103030b11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 979477796 1250 979476546 979476571
    0x70206070f05160801022b1428020703051b07090510080609010b0f061e040b0711100e010c03140a0807180b12040203100e0d200c01030b0a150206 64
    0xc40d8502c25080b07001e407805802840c5210307400d41032100710b0f440344660340170b00c0500040b94140f0803018903502c01005449e894080c4038a1032040c91503103c40194542010105a4198606812034800074100c0c0214000108013294021361002e0207401084408010a820041401103203020022081c80e10103d00c10942280034010004121180c10b208510603500b009010900303a60b2003000740403a5030400c0c1d59105141281140c203012503440100908010540e0347c00d640d03030b00c40d410f140422003a415040d800b4040c142d800c40810f500b40c0c01000301d041e000028030305110650020f00303080b11007500346002116415400030340e40c0030450780110260310450042d281d0580c0c0c00001d03003290b0240c0c5a1841195205034060140c0314040c0c0d80203054070b400078002000c0b9200403044100040c21075142143c0c041d05036110602c40b03000c0c030340c214131000703070100c840c0c00d4100009018041e440e450f25602035005041564510540600d0764440080001a01d445a22480d07400e0081304003950320368050303a12008403074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 979479046 1250 979477796 979477799
    0x40920011209020a15050408160512030c0705010813020a030818090f0f19020310030c0b090607080705071505070b220b07030e010f0605040c0305040203030708070206070f0516 77
    0x54650042110b81a405080002070a25018a00500c1c501d150000d0381007000400000521000802804c1400c06101005481e00ca00d03000030011071590158102c52150010700c44109030450106140040718000e0a118090381c0c0c0d4010010018401e810000b0360261440c038003c014407240710041c4c01c41e100c40354628118410b140e4104106110222280700d60180c122000038020203c0c0800603400c00100100820060f2031b04001f88140d81088584810004002e0070800034804190300d01c8005101040d070341840d080f0100b0101d05684612000940f01e558009a0042002820408503009240b80d00540f0041c4103d008020450f50011a095614054140100d40a6210b82000f2000c080c0d060b05440c1e00301d0200d0f541c0c031100c1c44008050506160359035100a022041c00e00400c85998840b100c0014103a00b07103000c10044511384010740702050310344420000162800802c88040c980c1145003d5190000c520000c1c0652040ea5030080c25890346504581c01c110340000c0810380b0648c40c0d20400c0006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 979480296 1250 979479046 979479077
    0x2010605090a02041a07261c060f090207080921010b100c0624060f0206090a020a0b031003150f050703150909030912080307091205060f0604092001 65
    0x240a07501607005100700080035100c1c00307040c2c00001c0c02ca0300e20420f140081e80f801e580d141c2040305501110701f0300101300084c1c1d90801c2191030071794440c0408140c408010060420021441c0020b02d40aa454011350000300d050902c0180c006035504d548005020080207170300660055080803042880320900e40c00c0c0691103002d0b24084003040b050304110755444c0060341854564801600c3e803502d070140245600e902100b003400c0301e2818a0702400840d15201e0a03101406c10007450a100140000503075040071142400582c0c07003002d41d204a4007606107468403500d484506420300d03240d9520051100d00c0400c0ca568840e51542c004400941ca400c8007041180d44065003941501d0280b85141d0fa1030400b0501449138180175448034040c1030107464030304100ca13201c0c900b940c0070090700361050b5001c2d4400300070850055440300c2c510020740701407000e9141001d5141e942a41d0741e0701c050003c1901c06454000035550b5102c65120b001103e80000241740c0381800c0340e215541d400034402e0075500144410f0705140e0203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 979481546 1250 979480296 979480301
    0x20d1e020f120a29010f110709090c1203020a060b0117190605061218030406021f0e010207150623060a1701060207140a060e04050a11070302010605090a 67
    0x194036010200d4548160520030b189444801062800169640c4610710340880101c66100310741c582e102e4800070078909a50000d00301640404200741040300008480d04c0b041c801280c08000c4400402022034100f5a40c508446082e00c1501714044c10525a19400141640000c034829690700445040012505800c0119035044203107216103000b11640001c9020110b02d41c0d0560005074050f41e00041e01500c500008140d507001ca80d100b07242c21582014001803641101e10b18050800b03500045281c1072a0901c069140e900020307088109200c800d40300c0e403d0082d19081005c1c1d034001d84000319030707822540c40c10047d201d218905803008640342c4a00410202880d096498074950000b440881c00500c0c5010485264080c40840e81048141100b101c0c40e5040c1c00040c40c0070b0201900542030042c03c0603201d2207084113440c581441030246a004101c0103420581c4504130201c180c60108840e51841c2001001e4171800380159448940051000700f8164198040780039a20121200802a1244041d5a05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 979482796 1250 979481546 979481557
    0x6090102011404050d09171b040605031b0906030c1c0609080d02180102010b030c04091a0112050d0201110306010e0d0c2d031e030e04050a0207060f090c05010f0909020d1e02 76
    0x30b4548c03180b00b4816581e030010581030700b010401000401c0403520345001c241440101d952806401500340f40c807000707502d88211005e90150084d80284502c00001d0001064501c4080c0d08110703001907c181e00f418030140d60801d6110b183c0003c0c0e01951803600840d017900960081c80c1c02c425409049030004040d6106004410721080010001c20070016100100002880c1a04044806c032660480340c0d81031103030300c6e9081d50081808445a5681d041ca07420981c0c140148000d80b00700b164035140f0441c03c041d40726810350350808420b19056100030081c40200b00e840e24140d801400710100c00300006103400c2801c91031041d13200d07812000141551904401c0c00030320054000145031401c009404d4081911915a20031568000c0c074181710244da400000ca001c42c3d86c207440c292482a00043c501c0d003408902d000c0c052030500b0009003004514040d45071032450050501603981000300045207694603a00c03580c1450040c2c00d03003410456031043c3d0388444900a1000701108003205001c91b580108060442c82900c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 979484046 1250 979482796 979482839
    0x2010809010908030a0e1f1d030412060905030d151403060402090c030c210714090d03030f0e030310150908070605030705041d100b1806090102011404050d09 69
    0x2030641c0c4800411201409a2050106c160304c07460725034007030810316058201d1031607901150010f54080b02c1058040c140c00340d121820f0896104000070021620b03c10440310709035400c907400098110031468114194441c581c0040421030419403102e07501c50701081800110360b04141e10a4001c04000189a1901e40407a00a9401500c40307000421058898006680c09401c44424a192070052881c0040030300120660505503011501040602138021010541c46640382a4550404401800290440c240910001d04050f19203055484145494004400b40721003103064940381e240c51109056a030045124652413103100e0010141d010b1b018050200c192071041d005042c01d1800e10703505454991001c0c013100e0401a0421000841c00b0381d10000780d15555950808013030751700740241c120ba4a0f05054003d80e07011402081081b401e120a0748c0c00340300031601078455a880d000000c00503070050614198026000303460301d0401080080c01708160b1489000c0d6190f0981854490f0240c0300409146103410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 979485296 1250 979484046 979484063
    0x131e05030a020405040c03120201050a1a060a030b0102030f0f07050c090c0406030b0a0518060901061b0f06020c120304060507030c0c020628030b01030e0d1b05100612020108090109 79
    0x201605080c1c12542e40b25006d02e00d9030816a54941d51125485180005440141d5644c420302112625a0050700e0507071301d0300102890180c52000015005100b0780006405050342d030744007a03d26034020f00998a1004000003000c1d1101803003000d8844550105030105d0b410300176218441800c1c58050400c03401080e22814075030130942018030540c01052141d40d1154001500e22002886507211102c681420581004014860070502c0034094060b9042e0003407130500008011100342d0311108030a4514050b08003560107d240c20a0801c8402446503a01c1c0c0107080c000c005554900c00b603500c0c01035000e10b100f00c00400c0ba80c1d42c0c00c20300b10120342207400e9203070005500c2484400035107440d60203003030152070300802c0c2c05089070601480c0c4810021007060314082a1600400c03141c540c5c06109407046140203001a05608880c1c00000b03080d01c503505002c01e119081200014244482000f8210b079083e040b46d0104050f5440380c00704201c4c5901c4c0d280480c000740360301e00010702e45d0406001e44c8c0009030380901c25 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 979486546 1250 979485296 979485313
    0x4330e24090403032a031a030d050a0306030c03050105090618070b030c1b24041a0c130f1410020a02010e0105070c0321020f0a150b06131e0503 63
    0x1003000c0700078080c00a03400c06031103c0d007100b060b0381450081086180e1a10b16030307031880100b000103000c0c0d8140380701c03560b042d006081030124103842c04100c2551f08038242c174065540b005401402e800804407604042c10141ca408404010444c0541c40540a085440100c4085030b031880300f09101280110910310320f907000700340b0030000030750039002031038004820308103850074a4102800240c02701241c0c1c20501c1103a02404888603610204405542d0390a06240c08020a10b01621803120954030401c82c20076a41c1003500003112450303a2820380d9030301c0100d0200d046102d5a10700b4440c24020780381c0549009098100b5500c02e00d0700d80360b0242c0c0503e460707540241c50f107040c498006461001c1800903140c103000003000010002000d41900d0b00207103104000c2c1010008aa450050040108030ba00100b594001c030300302100d24500180301c0b030b40c1c1c59004900809008a085c4050090b191b664074003500068042041e0002040c2d4800380d406550820010800745564120000c1c1a002c10b03100c0d41d0b4254000301c99 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 979487796 1250 979486546 979486549
    0x6080d02070909021c05010906180c031b030c030318060507050c0d031b0605090d09030302120d090c0602010506010f031503080903160b070b0703110904330e24 70
    0x1a0301c3d1240000d00c940344165241070340b6015220a0072007110035954492080080010621030a0610303204200b89041c0d94482e0f51b5281c000c0310140c00060304580403640100302c0464a04c416901035640000c400250030390701c0c680a08503109a0100c0c81c7c604501c000d0200c1c2083c41402078801c0a43c01000501800720b000080c0300300c02a074180150100a400308880d50040030303842e090b0307020900c60f034800101d5140c101980c03401c184081081004001c40d281c030030030100e50300051290303100c50140340280e502c0d07160312400b01c0107002c139107001400300300c00c4880080c4403a019030080e40300782400e0303c46003145030118400f2800c8507580540c907080c10810140070300c04920204090400001c010f0300303e8600c009051190480c0007060740c4818102d144c00260f032000c00000580e4950000b8181c00c1c284a00036113581c51001501524508074011030b03403580d81651807a14141401103800700d0041c3c0700c18100755000c4950000b8050300504190485176800702d544008030000c025050b0349400c0c0c0b030300c4941c0031010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 979489046 1250 979487796 979487801
    0x507080706150803160c1d0f09150f0105090f0910090c08010608070f0e010501080f06031617070b1c0216081c0c0c03021e1207050a0606080d020709 65
    0x602e40440400d01503000c92400010402409000428900007410f040945070489144809800524540c070110113542c414403500ea0039190801c160140480041d43c0e51000d0034a403010940c0540d840da041d1105001c1c11400840c0054141c07101902c00340d2869a46c030380410741058090320b010005a016617902c0c0442c25159018600c0f442c4520f00723030040c090f510003006095486603000b1041a40010900b0445100c3d5480c65038002e02e4142240f09039585080000381000788001e0043c02c40c0120000086c0c0b2a2354148201c00c042702c4c0c540c107425091912440b0300b10020752986004040b9114400020646003142c80a6400608080c125446040c1c0450900f40c041e4109240c10b080030180000b400c80018000d81c0600b643c03c2415569240c064000440b2100f620b210740c4c084018400b2138056040030982c003043ca100042004103900c0c0f0403d1899680910345221910041000100400ca40c41044404100c5105042c000d102c02c0c0003894440020949490303060b803040c00582d001403001c01074490140c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 979490296 1250 979489046 979489061
    0x8130f0b13050604060f0b0114091009080d2001140606070c0e0c0a030606050f090904110a0b0306041a100f090f061112180f03010609020c1c0507080706 67
    0x1c0200040102036900c1524008099030b0880b0040c1d112100c0c1c0085000511903258944801d18008460300481005d400e054402e603030070746000b60300d450900480d25000781c00c040c004000e000b0407a040507188150040603025200170082921081d08c200aa0400050040010880030a00d0311a52a2580020060310350710107182110041c80c44d1a0000b0000400d03182d9078440c0c2d14600400340e48100340203009044618a40100c0188a82881224a58051941a1288140183d40c0b2054a4a403424a0130f41c1452200764150f000c07945501c0460600e412401440c0940710540d0300703002c3e0005007004142c0d42c10750366194039081500c4440c0700361000c0c800c0184205824460074604225501c0e036a50740c1c00042e554001e04085100000702015048081100c482c44071007080b0441d0401201a0032140010498105a84500303c1c3c4c0c2c0d440d514960f000c5d80914003e1107581d00442d980c03c0313544109511080d0150005c10401c007044844960700380240704850312254007072881c81c94206955202c20042601 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 979491546 1250 979490296 979490311
    0xf091b0d0b0301090c030b09030711130e01050c07020108090703020108070c060e01090809180c091504090603030c05060708010303020a0f24060f06030605030709050c07060203040b060108130f0b 85
    0x840ca4040740381c0d2020b11500301c204c1e0007610f0443c8410305600340141c0d01c81010302400c941d640100481d030702141e02000b98400400040b194090041109000035010341045a50244d1039441e0000b4058010a00d0004000c1c161007a02c03082d40c65610326212070703100c202c0703480042e01007038000c000103402030b21600002454510030100069151038045d07810b421982c4003041282d04000000d40c7c91001c4c43d01441c0c072500140441c44c90005032a05105c205140d0165908050050b05e0301d03105008000041e0301074802400312a2000c01c0202d60381e04008200301c0904100f61054020309001c15010740c880d50102d4140ca416030000c006d000c113250386400080c07462a030306a402b40900701410f41591221001c81a8150a50401017146820f100946c03c561810350311071002c0c50324095041110762408160f1208544002100252581e41d010030101544140d40b17005018a10000c200010000d0130100c5a0040e6402c0c1c2e1845065954400f0319181c1c100c82c0000174058444003500140040c04105503664003254 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 979492796 1250 979491546 979491551
    0x20030408092806170601020715110f03030a0e030427021b0c0301050112110603040302010b060a11120306011709030408030c0c0f0d0b1f0f0605090f091b0d 68
    0xb008407280c2548034040e1420707403110514803041101540c0f2059204030b41c140741070000c000b410a000040e559244074820340401c00e20000c00c0344070244c000c1c006042003100640945552160031080e0740d40380d600c00c9034401c800b00d00d080440551050000160740580b0150b0f004005c2d4514181c02c003400030021f80c500340d40c829030201314110481214140400c2100d100f50010f0201180c000201800d555050b0405881110300d08401408900343c00c0e807800c05144161030280da0b944550404034090510b00d170500e034111400254054106601803010304403001148290317001c4002581c64040b145c801a641a40094400500003840b00030390407025402110306400c580ca0a80d40b40a1241503402c40f070411842c5800031004240d9a040605400312041000c030307002c1c2d03511401030391060401d102c007603e0020b1821600f04c20450041a5503032003001b51824007080141d103550354400420981c03001d04028040d492105100016003060ba40282c0980100000038515004a18080c2e0f41d581100d26609075454 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 979494046 1250 979492796 979492819
    0x20306150406020a14010c050904050c07120206090d0519120b03060a060911030c071412070f1b060e060a0903061b1b051c0c060606020c03012003040809 67
    0x141260090004250640250510309807a04040c40b07410003508600c17903564146240c95071013175807010480f6402c84049800081c580c40e29442411b081c05040002060b20202e580708481d215000540c540c41102d15000700d580c14103010400321443e004842941c440190508030003100140201945401e0103d1030000103020070031840003038686002601c419406a60320b14007442805240e01031110083c00009000c0c0c5541071010311610540315008000d06101c2006440e036124020500002b541e90306c0c0382c1c8801e0b80b154001c2c01c100c0c58850304401c0c101d881c0840070780342400c0129901c0c4800121001c5480c0c404c041010f941c1480510391043d000036080040d264004400189140f040040c2c407405484100c03c00261a680070b41914081106040158003400da040001000001d61100c80364405104141c01d59417640c00b5281c44404030001054581001c0f80443c10560004410300040350890081c0b04051001d0300d2801c4046150048003014002040001d0110f0141002030400d03000c003510080500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 979495296 1250 979494046 979494079
    0xc0102060f04050f0114010503300913090615060f0905060a030b0d050c03070b0708070602090402040302220b01110709180c140108061512041e0b0105130e060a020306 73
    0x15035002841c0c0e10b86c050980c0c014003c0d41030070410394090b0050345185061001240195001e0507052800c0810800720024490304151100d11804010040412003800400c0c1246421400750910403143c0072407150000c4001a19445848035040c13159458803400c51071410942404030541c0015040403e054549220b82c542d07849004000110390302942c05000c50049440c2014200b8150b40e01c0310104000500400c0d01040342d0740101c440d01944900016500c00c07647c000b18019002d90342c03010351302403007040c02d1700420303c004400f080005500c0c4030200608000308005580d00100c11900c41402e620100f400e01503801181d0180c800c11305001c640302c004d050240d40301c4440d01d80d00d4202e07413013607000420070810950300840d42542064080380d455a4011030605050240d00840d15806484205840030a081c031002c0042e441c81310b000307220740c4d503038003d440e080c5004420300a20032036000722420030410381a985140314100b40c202c9540050645c544500b86414003a40028111540c080110844104503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 979496402 1106 979495296 979495301
    0xf06020c1201052401091d0a06060f0c03030b1203030106051b03160f1a130507090e030a0c1104150503010c0201140a020a030603050a230c0102060f04050f01 69
    0x50480580102c806e20780e07030303031100504903480910760800f4007280042c948100000b0ba018000c01e9030300d0004032805440704081d4800640802441400a0300c690010b0030200001450700394030210b481403e07400c40d4020b900041c081517001541c0b002600000c07900e40010000c00c00a1800c01c070305440341c0b11525030300500003000102c200160000f000a00c01d00140f01c00c0302c904690580e403600005410b44001804c00030b592502c100000001c0c0c41585004403550440320390051410810220815180840685022510300c100e90304000300b140c803184034440b900c41c9202045560186014245805c451038000c40d00304590508100e007581c1e0301d80c1120b6070340000c0d054600598400a240c002c80091101d5040101355004100e071030000d2000d0580c150701078940d111700e11800e8030070310760401d0358640021a0303c0f40543c22082c0003030f403640058060340b07500c980150151210148002903042c03c = true := by decide +kernel

theorem cover : BRFrame.Cov 979316546 979496402 := by
  have h0 := BRFrame.cov_init 979316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 979316546 ≤ n) (h2 : n < 979496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
