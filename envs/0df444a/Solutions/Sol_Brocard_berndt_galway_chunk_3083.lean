-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3083
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:36:27.639378+00:00
-- url     : https://prove2.me/submissions/04e0d4eb-3c77-47c0-8c1f-dda7468d9dd5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 554316546 ≤ n < 554496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 554317796 1250 554316546 554316551
    0xa0914070f0c06020c01060f1d0601080601020307080c120301120b0a0c0c0f0c08030c0c01090b1e0703030b06180103240b0d1103011e080c03030906030408120726040213 74
    0x1090340480d01410068101503540148c2c0700c8041030750000308014000604201c4803019050329100019213161101b55040c6005810410252010071b070800c1c002e0103c0804a411102420303603000009d0320542003a00541c10241c500d8100f1001e102e53b900007180c000780000010007062108000241c00e000343c520b03000340448055000441401680f030f140b48002c1800304196943c64900c02121501c8800c450a00303404908165000702e144552042a2660340c401612601140c805d4401c0078041908004822030805440722480790441e01c0e401e000d04030000aa0400c03084c2c0c1c841e40000542079031004000444074a000490300c0311070794510080a0304450a00b00003a54034160800d901000c7c1c05860000034000b80000000500c01d01c0081102c409202e8003032a4041080d10b4244682d110142400e205915034012f0124a03203e20340040110342242c480c907840e520304820004c180e08003800031980100400da19210f003114080103c00c08408442c1c12251010389803a2550008007404400c040030f070300f680d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 554319046 1250 554317796 554317807
    0x1051206030a060504060506030f0712060b121501031208040507031401110412021915051309090c06030f0e1005041b0f05031b010c140c0a0914070f0c0602 68
    0x210244201c80e0020f40002c4207000a00d010304082d0050803083d1081406407007021041002c100d0007140000540e02602c0e040303401c00e030703042d15164058140125295805030103800210500d503400c2004180d40707288040240800d40c91420300d000003034841c4071000d040c02205410030000440205d003000035030b907101101c40c800d0b00006080c24010140c41c40501050b640015000c1135203041c030300c0c8a5800078801c503a9440000052409082e00010500c50420340100b81424040f000d0701410103004c070340c070210304c00d841c090750354001420903a00c00c0a402d54040661a0080c005541e140c000c4d108941c8090101b0300003100f504107800d40e0f0b81c000110f030b1804d039941c5401041c200800160512030010681c8508101503840c1d1a40c400484901d03c10a4800e01c20b010201e1040b0702c0b8025401081030050716850380c00d50094951038080f15000a4841480c05071010500f060703aa10b800000291208410004008083e00d400500f060400303861b040903c030741100e0784581c1c0b55002203500070b110b501110150b160ba = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 554320296 1250 554319046 554319049
    0xc03090108040c0f03150515011e050904062913120609080408031c14011203030e030a0e03070e090303060105070f020d1a0f070503160e0603100509090c01051206 71
    0x3d80f0340c104091460b913070b21002040c081402a0642e05900d041340c204020b4071054400301c0d10381074900c542400703d8640c040c040c0201c9004800e160070040c040c00c002d0b1a1170302c6030307001500315420782c2c000075082070030620390303a175040400200074150f00c805854062400000030182c145d00603c41c41400400c4100100290400940303400c8200d04036030212000392030b03685600600e91603400543e0800341e1a005940b8404002d00540910440c0e81c0c151108042d842e42071203101d007100d80607640d0550506844944540024204200401d01191660303201000030010104041c00e00380c0c0341c1d10451410050344140b14030b0300c3c808404c90703402c40001d00b8440c1c1c1c0d4001c9440c1c090000135000d5400f950000813191400148240103040c81080f40000380300070140d03070300d10300070207214802500c0c0c007800103005000103014004064400c0f99000e2450070401c81c51004900040c0e003d5008690f240780642500c0c404010609141c030849820482d5100038000070080d01e000244107008030911070520000c6200846c106 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 554321546 1250 554320296 554320313
    0x5031209030c0a030506040510060b0315061c06060e12060a1e0908030613140121020316090c020d050a2d080603060a060e040602071b0e09070b0c0309010804 69
    0xd0340307020700b00e0b07001e05603281089511a1800c51f0b00391514014440358a8891403079210707020a480d070040403a8156200c102601c100009030484c02600844100030300940110942014a10400382210100f407603401c0500003044a21a10b403224000d0500030aa880d00f0080032604030342c0030480400014001504681440b00c2100111030601a0f5103480342c10410710400500031403003200c044d140362560a1a08107042d04a44807181c140010001700c20050204051381100c15041c1d01089080345200c0c0a42c0e000281000501d0703545000c410300b01002080014003d00946580101c07034000b40609000140000c1c0c000d1158009000070084071121302c0945c0031103d4503e0022502e1503c0142095280703071806816040181c071103e1180c45042d00003007809003a8040c05050309c0001e01c0442d42c5031541c0d69150080d4110b40700460799907280c8503001c442c4040702e904500040400700a4211076040500030107082c001503400c80d5010400070492800900030000072203040200a20782412550b0342c6042c9182d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 554322796 1250 554321546 554321563
    0xc090a09051606121a0f220f1b0306050a0e07022a01020714010e040207080c0a03050d0b10210f15050102070906030b0c030405031e12060a0503120903 66
    0x3100d00302c0c040d0109110354449144036544500e04420013500d01c89060019400c00c0362400d00f83d103e10242a4441c1c0360518041b1007283d0303c000c064003148200c1c079141100039100f0600c0c0300e42c44907544d01d01482342d0985190710741554150500301003140f142400c002c604140941e000d02c078032801c105404520380b90700c00c2010305109030000492561808444c0914001c00d419400c05500601c904400460120b124050800c003905050f1a503c0381d0100d480f041c0006034101020075901d820007800480c10740794090007484080d900ca56915a40c03004141c200104031001e455031540252002c44210585580090020003064a4208071411001d101c0e8802000f030143d6158000c415800c015070142c3c2c03001241000e90a4850036000d0b5050292644c0c005003c40c0c51520006d040c2c0244000401e1852402038010364010780a40b007540c0ca005110000107007120001341d50890752000000c1c0e20390500240390b44007904004200c8006111900e4600020790786c3c00c542c100304c00942e10001f80342409a904201140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 554324046 1250 554322796 554322823
    0xd0b07110a03032a120c170c030609010b0c0c040e0f070b0901030c0e0f040b031c0c0b07020f06061003090b0a060306050c030103210e0d05010e010e0c090a0905 70
    0xe881d40ea15242c000d0141c0909941081162081640780907401000390594443c2c076000e070350750500c1c95551300800c0003800130780c0411414002025000c1d2125400b41d4155440351101101c420f80c0c90501000303100540344141e202e1411001d003440407591089000c180d03030b032141c00e00b102d001c0390510315400c846061409081e0a8603c92092010024107095210301402d804107090700c0800005002d03c00584821003500010396000400304604841032600e90700a901c0351402404541e280c0803150202000c0851a15030700001c14007024034281004412101c096120710288080c01840c002031340c405568100c06099103100b104051003507101e00713100713500c4910016040f00c0071000c0c82c20100540301c0185035038002038801c00e00b0071001881441a180449040302c0e03001e40c80d602c01131a44290b130742030b4010800d0780c9020000c4aa98103c441c0c2c0d10290081c01c8103010310000604c3c140a03040a60031100749100203000ca0f0801d0003001c03125910600840da20a052010100b00180c00d883d00e9401c06200b50003d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 554325296 1250 554324046 554324053
    0x1703181c030e03190b01030b0a0207150b04060603020a05090f060c0102280e030d0518040606031a010305060a0302060c0102040512060108060c070c0303050d06170d0201060e01050d0b0711 82
    0x1080c1948140031003048002035065515884da041142811000c01041c080c203c001d41000400018141e070806a61103d00b00c2801401e0000641d910291111a05442d00606807110049074080c6007500c204801080c883c281140381c100c824602034528052007003114421496035642d411103440d004121292a14241300841d0b0742c040b44003c0345c0700c03405c020510031090007003250042d03600d41c007418070000449002001850070081c48001200e81e84c0c04542d418040e140210701450360f6490318000c0e0400b400960310086170b50b032444c03982c203c801c0c0c0002c40030360f0400d42040244a19a190392105070162601942c2c1690b40790004192a400b80c4250750085421111400a0110018002c24080d0580341540103440964617444541201409191405040c02400d1901000024010002080040751a41c80803800503500c400402c0120010860041c3c0c5800c00030722085540e6081c40390201900340343c3c1c0410030650400000c10b03006052030400034904d65000000c1201d4030302480580b1203124070700c07046 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 554326546 1250 554325296 554325349
    0x1403070801020c010606031112041203060e0f0708071d040c02160e1006030207051b010e0a0806010801110301180b03150c09040b03010207020d060b01050705010f15170318 75
    0xb0600034217070b030300c24140024a414005101080b020040b600120040d00341c501107502c55440381c0510400369401071042c155503031400a9842d0048c42c190b0711865156141c41d00b1840c000c0405441070030300900d540c042100c1001840f010000031040c40030302c407805481c0007a00280d41c410580c0f900e007215200403100c4800042c0016503090340503060b8881c07010b82e8140542c4984e2204d081c0d069000360f032801021a082040c4407401501e19803c40343c4445014076100c80342010800110300104400d400416076a00040014855007a0074000d42c0741c3c00c00700040c40381c42c541c50942c03401141d00d405581803003116100c3d146007695544c01c20400c0703880d0000150400950501c082050311903803000c10210f0080d030900850041c545018800d440540307402a0400940905540e00e81c3c0041400b82c002d41e0620600748210030104000b40b01e44040c420004030000b03001d603078442c1400901c601c50b07400320515901424003260100d00200c107445000714031051b0403612240c02c00000f902d104030035202840c0b0386030841d40c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 554327796 1250 554326546 554326567
    0x31f080d091e14040f1802040c020a02011b0c05060307020c040c0306060c12120f020702090f0c070303020c0a02130504030f030b030a02090603100207031d0118140307080102 76
    0x11110300c405000d0301d8180c0760940d0b501071002c288140780074054000c410b105081001c44a00340030606003d1000b440041d11021519a20003264038035008201110b048074007110440c1010b00c1020140d2403603000402c00710020341d000800c441b00f1041d40c10b104c1c1d030762440e4010412240b02c0865000d00300040815850b440c18410080d9030346000d1400500c15404c0000807101d0038001d00c0382c0340a44a181c1c0e02e0210100958450582d00480024103a040151810448103590340902c5000200c0144800142c0d8800081c010000e110b403001d003220040e04103c20903ca030020300c0380c0c12142240c1c0c0c107044c0513072a121402c40781030134071041980194020859040d072031f202d190964803c0303204601c07030384601a03004a80d840443c2102c11484400e40c0660010740200c0140ca09000142da000c80020210364400c0740c03002a0105a03042140220f0210720f03101c588900c80b080c207491500c41d014003072903c0b1144009d002c0c2c202e01444038610031120350010888001c016500d0030300801c005000e190009640e2019060b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 554329046 1250 554327796 554327803
    0x2802060417030c010c080c160201020a020a090902040e0309010e3102070b0921130306060b0a022407111006030c261b1306030b010603050c091005031f08 67
    0x4620741c3c0b154030300410ba01302d96008810703050198446c10070f01b43c00c1400d03c000645480b0031344102079043d4400d1201d203400503039078070103044007a0040440c007095070701651041c00207030f495002d10840c540d007041c09180c2850360300c01c210084000b82100d030b99685540c6d040d04c02088154480c02e40342800740d446460b0148000d039400030003007140b08071030080f42647d59204c00d58580ca5005007110492050a46405014200601038001c1c4054101a2509540e80e551044100d801e1030344458409540400e1107003500e44c040c09441000740001c102d0b110003a0b082c009210003014020010024004040501840014100907481424406034010440c440e01c900700b421480300c0030300c03800074451110741e0b141c981920307420245c0000c038202d18001c0c20796648407450480400310201700745070801254201b01c581880540126401103005001c0d500c06941801d0000701a00c0b00100407001c1400104900b40040d240d0007900c201490b0030785402d940341e4540764a9032101d294007204141802e000c40901040070800031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 554330296 1250 554329046 554329057
    0x20c0d230105040f03121b050d06081c0306050303040b03010b07060b190e0903120c0906090307090603050606092419080114010e0106020712021908010c030509280206041703 76
    0x9494007a01c4246c100402000d8484001040800c0c4c2014204100c806020720040c10408410b04404aa0140c55112540c038110510300c601c11003981c004960b049058252040a005d410300350095450603041040c0743c00144418131034410421000501601403065031351100c08840300060410000420174600e101c4480706078051210000181408038401040002c11200090700c0d01c00d0760300e050b954214030002d09400c18030030b59400c00400c101c14081a5010301000000e40f030443c07400106241907040c1146003100c0101000c0c010491402400b501c0c14980f05141c0f08003400031001d000800442d0045040140280903c86401c00040c0e40420b40d800190440c1104845a218411483c0e0380c3c2c0c0b8103081605c10a1290b040944c000402c148812010070680303400c1c0328000f61113076807640354980c0440d243e888540d001941903552002d840015661501583d900a01c422005003100680502d4041c1c00c5c0c3d11100207040cac25010305401104646400c003d490040c500c03140861404c00724841c2040c0c030f03503000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 554331546 1250 554330296 554330303
    0x1407120e0601050d0807060b0d1511160813090f0b040b040504351306020c0409050c0d03090b0d0c1403040b0105010e0d150204060f020c0d230105040f 66
    0x10180c4a001454002945604903500103001c10509021521809030541c0089026076019440f41008107144d00d407001c0c84000244110b002410300c268404070002100c051114400d20001d00700000141c0290500341000001c0c0c0206941e03556405100c8403c0020805a0001c001c0508140c21900e119005602601c9005025030301444410061010401100e60855009105182c10315029182406841c0100d00292408034403202000760f4204148140e08034412030010900c00301c0c802d0048a03410303c42d40009178070036581070194070102d5803003540314594010100e001d1030381c0103514414140f19250090003001c50100ca1035650015000300c00c0035210403000400400c6071640065480c42d072241c00c5a00c62900008010803590030640110754041c0c000030300789d0340804c00c8184c150200d0b4a82c00d0f4030b9403c1c0810000160b031180341c40d001801c41c0943d4241c1030190740200c0d0000d551074071140c12114045a11500601c604602406001c413200e89911403682558078140401c4100181d4000d43e0b1baa0600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 554332796 1250 554331546 554331551
    0x8070501030f15090e0708010e06151f080709210b070c08030112061d0c09061009050f01030207120e01120c020d030c27030210030b1e0103140712 64
    0x840941400f5246030410000710791403280d804204400e51640040740b10b905400c10364030100c1d619045142918124814640103811907014061240c0303a1a1410114030415280040e546030100648850040d046c4030351010700a030a000100d0891203100c104015007104045014011107a41521090b0b4003030042c2128220895070100c0c01490048070380e0001558000206480d6a003440300c880000d500b1084c084440c0d503142c403444a04400110394410148903c08020f1180010503c00c002d40044080c1811340115550f011401d912540803c500d4103440040c0d8003000e025a10070f00403230080c880d09101800400d0b0720030602c5e100540c8003501c640c03800d0b42603a80b8003d02c00221980c0c0200ca064055010245c0c0c00402c00340d00c20b9000382c2186480c18250f04018030b0b41c80503100349810040466034044524982904140214a45616101e099100c01e00c0c1c200319441c84800419020344005083e0f8001031000950010f90707a21a40109100c820076040a00b15400e00d02c0c00980303102e01c1020001c0c521030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 554334046 1250 554332796 554332811
    0x60103060c09050604031101140c0303090114131b090507180f0b0304030e2206062a0f08040807060e0f0d1707020f0a080a0302061503150901020904060807050103 71
    0x24030400126043c2e0f08000c080618051440da5030781605030800c104181405003040742000784941c2d2201130141e800c40c54020b52b68030300d0800d1143e402c440300070020a0720900c240090003c0c00c0d100d040752400c643e0780008c4d8031001c08407440350907100145640c0701104540c1003408018050340d0002090682010040040318240d0311071040c5d040d03004140c050300920301020320000340400d1040040713890a060140c50019450303000d02c43c0c038a01420301c1c1460400c8544504040001680c000030001e20000c0054891401c0e220800340c0b105c1c0f000c0d03140e401074008041c5000940038040028100c42c01092150211452640d07038200c05003002d10003101844c85441c0c2d031841e44109041c941040c203034541d480003142c503182c0c20a5481300044c0c2c2040005036041800c00080b00c9080e00c5a0a040c400740048000402c4800034502d402480c2c100c0c0100341201e000c9195090a12a850016002c0c07942211380d4417079806980c56038203042c024010b594815134081c2c10b00f40005900240801c1c02000d50b0400c0c2c0c0c00b408408c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 554335296 1250 554334046 554334071
    0x3020106150c2111010c08090d1404050f19090911040e10021e04080a0c0f08120f07061503052a0d0201020a080d1e06030b04111f0206010306 62
    0x1080031000180248143c0404490348088000e034400d0304080d1400d000e8400642541450b086940c0c0004510120311040c0a1000c001e0040100d1180c0c0c1c00c0c43e10f81800d62840c81100070825009501c125409641210016555940da010040d550751491000400307060360740b003840a02a04036a0780c04d4481e035400718611310450070280070300d51107800c8940082c070b0551a18081d0303e00075071003164500000c066903421407000b4188480108020204140201084422803c01c070004000c40d41c0052500142c44000b00200600812110020106940159114510841500700c1b900c1442d8000f40300c58070b00000380c040030100d0307102c0070252030043c0200c0b19040c22017407041c002155524010000701142c220b01d20761918286111210980c030600c180c569000f0282e899016642000d240c401c0740a454074214418501c0242c2c0002e020102803109000e120310b140c403568842c1e58003401c05840c030454078407102d8254840d4401c0344505641801404000c00038075078001c0d101c1d10207000442c2c0040c144030380f00115 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 554336546 1250 554335296 554335307
    0x925300605070e0d1109070509060703270e13021507030518010203040f21050d051903090c050405100f0909060b04061a0a030e011104051201330b03040302010615 71
    0x680e42c0000410071940e40e00c410803181106c02005181044001c0140345056150840600585403098544524090000c1000e9014404c00c0904823603030207031a40f04010344080c058070341c3c3c2c01070061486900100c1c1c0500120b48459540c00d26408680800522402015846001840d0448228800558000d00c20300126224444c510485a510072094000c1c460b19042c1041004811810000500c2000441e0758450401c015071481c100443c06c0403036007107094000200c0c0c20700195035602d4200812056560750308a0f145490044a0085a03904000780c4a81030346180c5e980603014006814000c07e07070365102d441c0500150001110301c03500b003540c500c101d0305042c0070324025035829510300400c8140030301c004980354100c0080341d0101a02c0d00740540a0f21001e10410155a01a1601a07500d03410302e001c0c03021220701c4050707241c2030760715001407206041c0750714a51841910001a81409140710710f0105507109c80e254108041407200003040c8000c02d038056000300210f0780d01880800c40b040250400741c60 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 554337796 1250 554336546 554336569
    0x30c160905060f0a05120307060c170903070b01060c0206070501091212090213150e010b0409050702060f0c210a0525021917070b0925300605070e 64
    0x104100000f01c01c0c082c1b0b03c5e100401d005008241c0c0300f1a030801030380d500c40304191400c1d44410004107510380d0105c92011840e540b01980600900700461030b01e08940d5601c0e81007801441080d080101c199103202c11581ca04084a40c000d4100b4002e1160752268106040480700100c421804035140c1401c0b103404078003d000d00140c290b0000d050480c2c2e41d08034000a03018041240b18104240032440e00070414802e016216800381003c035008079110b50603c44c41d00b045840140058080d540040d040044850307455200980c00011202c0a0307031038103020a00c0c01d031042e180c54030043c6c0480c00c0c9001c001c8184030079400a0b201e401c0e00901d042c0b6584d8210810425841000c484d8001604070102700c01a03c11180340d5038420611032146501051000b640e4041240c0146104803010185c0c0780600610400410034030446c4d1003189560891a410500030540751065441800c02200220070b4600780d00403000311401c03006132612003400c0580b44515022004141c01c6074603001143e24400c03000350038105005142c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 554339046 1250 554337796 554337799
    0xd020a08091003021b1c05121602070f0b0309070e01050604030803130209040303020a02070501080603151008010e0a060c09030b010512010f020f0403030806060a0818030c160905060f 80
    0xd00d846000814080e80c0b602240400301416000c00410419125403124011000844405856080d66420f4810480280c1c5140a001c01005100090003c04207283c0c86410145502c0710740136a229006050341020f68540c803034681908510b40c0043e041200c040150700c1505603e050390009038481e807040500050a001c1c071508100184410f10000d4003201c002c42d0801141c0c0da10345101540c030b41c00625003180480d001c8000940104816003455010012034002d05000d0800c0300032441d060011984e41d030a00184080020562400300d0166048129590040c040e02802400014503c04070340b0703038a161848040b102c0c203140900707542c034482c440c2140e0803d99510803100039599103441e01f00050b494440d002950701e5503a44c441441c000c500d0388014558244041c624507200c5213141009001c600000300104c0c0111b00400c80881c1541d8000103080c1d00c80507101c504c10704140b4406100e403641c020040c2d548824854203c4d1065201c000f040798408030b45800d00280b10075510791040c84102d031070f1500c026 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 554340296 1250 554339046 554339063
    0x506030114090411090c0a0e09090c1509033306150a05160309080c0301060b0a050a180609030b06030a0302211c0203010303020f0d050405010e0d150b030d020a 70
    0x200940b42281000d41c0050254038056942d03211140050515482a115900c1e114070005090b0340c1543c1000480740b41c1102201c81364503510703003001d202c3d4681800004691181d0146200c0011203c43c5a0a80341681d0010302210300a038441000086007100b040c1c0840614400700d2030b51030782d0b01c0c00807040501c5070002500f821004010400400025040303082c215043c450701784200d04078004030114800c0c030a8080d64074a0070543c58198041c1c00d0100444e2441e0181e41061400e200644500048510f1054945045981c0304800c01003110f82a001805000004025200c0081d41d160300c040b540c006c0d00d0250b400f81007152910420103a0b10001c4001c001c0c0540c11842001c980840803003201c2440c000640c0f1b00300c3c6031101c1d5900070841040001400c921050340880140185541007000701c8950988000901c4c410400000c090f016004600c603103810802041d10030a002d8403411001c1a039503900c20560300c01c402020804401030243d40c801715000f84500f5040d007102510004d0b400c0901074002d48030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 554341546 1250 554340296 554340329
    0xa0c052b2a1223060f04060e010902061c0e0303090a0b07110a0303110c0a150609050c07060e030d020f0a020c0a051e030106031a04030e0d0b0105060918100e0105060301 74
    0x2044040303009900144142c001c24560400c426109108442c03142140c407240140306c1c40e0500d4107104817050740f01040c180380c0c500802348006032106001c960500780024403001071f00180c4103044001e812502c800041ca400040140401c800c0001124411a4401c0c48001116034548000703d07505801e085c072404043c1d00526804000c24040c0e4402d203070315103804281031320300495500a6860100e201400311594509094070420134203591041e14003614817160248103d007094440509640250310380900360744d59074040c00304108404c00071503007144210141991201c3d03949004a0450304042017040244c0a100e20130708940c81d00d04616010390344000c19003070444003045400003608003004000c5070590340e80c1e40b000c40411980022180b0114004c44020740f00d240602c0c4c02001c0381e01102c0140e0046888440c0c15001030180906a0306650b03082c0d440719102d11041c2c2c001070885002448a1041c1c05101d02417100008a444448080d10740d0310031403941c0e0782da83d04244006e03844244540c9807100580c120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 554342796 1250 554341546 554341553
    0x804030806042901030621030815030606060d0e01050708150a06021209010207121b090605031b1809031b15010e0c19120e0a0c052b2a12 60
    0x4400a90319045c500000c401d611381c1c44841000202c66405003078180100003c804240c1c4c082541a44a801c2010381c02c81c40003204040f039512207016052605c00c030008514651545000c4d417100003d400c80400900480c02c145101901151084c0c480c1f003025040410b54541c181040d01c94541116026402807207100340c6503100c2046038022000083c114010084002030345008030700c5004809000f20101c143e0540041e04003024241243c0c048000c16003400010452580c01043c0c05880c0803400c1050724404c401303100055090300d0403107005d1403410140030030b0006400780080942100d908205004e40c840030200880c940d2072040181103400700d82054014090340c5104641c650708030004598240c01d0a02031003e040003c4040009000003511054900144100e40e0180c51601c4203081e0280014200701c0c3c40b019000300b0940030303447c0103c04bc9000442e4001c0c190040b082d254a0b40c201c2100c4e5210179161400f0101c00841440c0020390110042c0c94030078400780c0e0360b501240c2c00c101d050f1481007a541e6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 554344046 1250 554342796 554342861
    0x9060918011503110103140903120403050c1603200d0210031103130203151e0c0405060c030309060a0e0d08060f0405180f06070e04021315080403080604 67
    0x203089460a548840054031603000014241001c0c511652040c00602d102c10001001c0b221100441d1602400020510580c180d0100441e001155458500020b42e1348904041d2154445d8440c07426042c40358060348074810b03031641e1000080e6882044d410464441940548410007030401150341d100c151407154000519042140c5085070025040c0801c44013440a064841504201c81c607040c00d90b2140422821071a0071f0200210580c48040300000c17500b00301d84880321240c0314510f03100c6040c901c00041546070000e48140c500411009001a5032a8107a000f070644a810646980c8918030414000c02d0308885c2c031b03005a4400700180030040602c0203420f03008413241080941840d070441ea03076a072800341c1c507150340c0200b606c22a02c0441c030300c8241d203108024030b240140d290303403030b06080d08404180050389521044503440300a04031405600c404d4400c0c007440e0030324242d07405504020708822180e00c91940081c40244220b0107502d403c111541c600c410301055800d2100c00391549010220011820050103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 554345296 1250 554344046 554344081
    0x90c050a230304080d06080303071b140303010801020a110c010c1209031e030f020d0813240b09070903080d091b032001090f03170712030603020f090609 67
    0x100c01c94000c00c801c8038041c0309952050724151081140003900c1d00188215020700c0004218980007940340d85000c2c1c20092070079054001822603000400014030034402d00301d00e5445522505400d40f075503941d64101d014002d41c0290082c0e40411540b80002d26145804600a4070494040c2c54911011b045a80c522038070000056251090025080307002c80400c49030a450740303c6010500700050380c400c0a0070003810000c50603d414046500c404500c910080d80150380d00c3d000b545015114039650030380d103421822040941d031503030702030003003840001e00003816500309448554007603071008200d0700c036038500315003952240c00302400700302c1304210001a8403030701d034480c006040c040d151000131403986000589265034070364000d450312508a040803050228000b80695016424200101d2803481d01170700c1031064907141300240510084440301c110743e0502100321900c0a42c40b130315102c4103202e6118007030018105400168028126030306030309901c0c14920002c0d802054010311f03483c255500c028030b587c40724815 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 554346546 1250 554345296 554345327
    0x30c0f0d060810060504020a090e1009020c060103031808070608070c080a110106060e0a030b07051b0105100b0711090603070b0a05070605091212061c030503040c090c050a 75
    0x40150102003905440341201800d0068080e15807041143c2c5440161030389908124070603072040201c1c244a6400c00b4441040b00c10009840140340d850301e450030b11900541c4d0240e8034281c000642080412004101141681d1003030300e8207200004c1003c032400c2c0c402c000e0700810003150711482040c46024020307140c40d940082c80e4a050720211100b030341c842c0310030f0300301c140d900010818009030a003002e002030088001030b00e16841d00303140940b10f64000030500e50480c8005400c030044000421a50783c07140c0111490366000319400c8104a80b401c0040e030007000308546600401d03056440200d0100744100440b40c01981082421030761290307035810092071000141100e94507110f80400010441e4821003d40b502d24090303120b071602d070700f0305043c01f00035500300412016603a00b00d948150584480c000555620b1001904000004d03942c20b0049407400100340d02442884a181014508059102004503c01d40c4a1607403081400d0b0380c0c03c1c502d010380700100000c5000c80e105000c5003031014420281c0844003030384c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 554347796 1250 554346546 554346577
    0x30f0a060308040806150f0d03030b060d050c1b0a21090509090114090d080103031d150423011409030703151b050c0312090f010e010e010b1203030c 65
    0x1e5a990b128010f911660050a20703400030000c012800f241039400d00c03080b64094a202d600140d0050001d0b003080b0342c030080241810341c0c0d48668100c54403143d003601d4100f00861000c000038100b020544000c1c3d0071040008502c00c0011107014961500454041c14a0b54803495080303928000d40d24042c207284070b02104e07000b00541c0050000c1e0682d03944c03c4d014041c0440c40700009100c0c8010390800d4041e00010909a00d079032000300241c00c940e03800b10445044907010314100710500c1e19100c2140c80d559580405541c4001c2d00050141d844413940c0080003103c88290b0300410880301c0c0303801005003030503e05045012842407400c103420a04008001c2c1200300009080c0c40301240c40359540020340c0b100010440705503694a8800300d9440e03980500c0c8a80301030a00300a0305214401300301607928403502c0114154000c480002c140341d006c08012030a01d01950400901c0100e1907000e00900900b8000440303a042d60070902d0354446400c0c50103003080c40454002c051851a5203610140541d6800403440184081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 554349046 1250 554347796 554347799
    0xf050301330305010503070f0f1505040306090b0a0506010c3206090a0b0702031207030902060409020c0105071d1804050c0d0302250b09040c110a0321020f030f0a06 72
    0x215860078900e02200c5500e0000e183d5062805140c58140c05030040714406440c002c2c10300c04d980c650301d200303400c458800c4050200c004500404a41c50700682e40000c0c801418030520b482044581d0824070f00c9000342c14410012682d500c401120014040c03080038202280007503504203d2150103c02d0360751070680c5102144100321203c43e441c41c000d4102d80c00f4003030f41c01010450007081903c00da000d0b000415403004504241e0120160200c00728041c080c1024140daa10302882191035071019100103155100c411529222128120b40c0640700c1200c40d5800900094102d1a90f40c40428200201a0018044a46080c0200c2e9042c4030301c180940143da40c0d2180c10035030581591140040c042b110f2007070740548411030358480b4610075542605000b03603044801503000c0c8648e00d1040140c819040c0c2c110340204800d010304030103a410403001c1288588a01801519000781a0801c1e074210205040b021000034581e00540c81000701e000c0c0143c09030541c2d00410208400440700801940c10070522440010383d00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 554350296 1250 554349046 554349119
    0xc08010b2217101d030d091b030302030c0c12071406130609061e08040f0201030f020307180e010b0a11030f0301090e01050907030c060c03020708012a0f050301 70
    0x1420300b46000c6007158021824150340300380030301408038182d200e0002c944501c02000c0036079881e8060442c08050042c0c0c2c400031081480305900c6400185030404940d80d04960f202d080089d100d500100f03240142c1d00c50394203011101c0c24003200b4100c1c010981d00240c13510500704900404081c161900c81540100c6c2401501301e4850304601210040c151178662451141ca0608054100f00150104503461101540003900c4603410050a0380d000364804000d00e070703a0901d880140c00800b86141c040c0503080c80801001200c980110303c0c1c09070b50300d810700106985983d9100340c5100c007009000350402307064103105515035240156110202d01d41140b050b6420103144072103440c41138009901440007035858010301405102c083c132071030360044034040c0600805070030758079001c202e0552482200e0070003072600b010100303044c428810903018001c0c4400074440c0c015560b0404143d140080c105d000c50008003d000b0782c4c094042da024404a45030b688030390303003160300c0d004071080194014a2a02d000c844d0029101d040b8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 554351546 1250 554350296 554350319
    0x30c02030712020c0a060e0d08090102010222050111011a090c1c090b01050f0f060a0e0d1101081608070f0c0503070b0109230c03060a08070906090c08010b22 69
    0x460070b4560050400c02d0030403080151020340c9504c600e060008804412880d5212403448902c013a0f001180c9940d40c81e50440100d0080c49400c590b1010326110b403000f5506c03810049084401c13200242c0c0c0300c44816108400072030881d840851060400e101011801d0a541407804407154403501c401003450503c051403000014a0615001406015684403922420841c2c0340c6a128050b141c166a2b40c40c0c1003809001040c00c0d408440c103007620401c03022a10020440c40740a0250008102406a000305036851138610001c0c1c5102c040300340480d40440c001464940e100d0012218091542d40711009a190354600ba196184071100c08020481e4005007000070032004c000400a49206801030b0303016600d052000c030200c560300501082406154a0980941e860b51041150804030f00c088195803511038000140d1000c2440d4483d403a680141c60300026900c17002d81c041300880d141c11906009833641341c1350890b41f1110074002d01100300e01c00d1103d10300d15840c1406007034800021145143e2070544442e0802072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 554352796 1250 554351546 554351573
    0x72d030b09010501060e0306370f0b03010c0f0507081209030307090501030605130f060e010b07060c03090b070f0e030303190f050618040c0506030c0a030b010e0a06030c020307 77
    0x40d18142a400e200285200f4807401d03004201503e0316500c903c003100c000a443e1500034040c0000600c032075140c001d2008a52070801c0801d00c507196242c0720341800e102603901400079203000702d40342ca04c1c0108418040c02c0c180140303034080d4842c0d9644500501580400e0b00c40743c01610080e03840103401d0000140003024145030500031400f14005507241e1400d140001c1240409422950406040031406c11407500d0328000b1552540b1170303950100b444a42554101d00070003030381c1d20220020200354000a0092841e200802501d4000c0708148408102c8080540980c1d8000e803004207004100c1001800503481003081d40064900d80c544801465025030010340355030270070b03600048c502c0d08003141400c4d9201c803440380d0005204c0828003030265207407442c0000c0f188410451008240e074420340001d01007000c501015030182070300400d05502c1c0c2c01d001008503041d8008078003401c00b003850460b04000380d42c0281804402c0000050040c0d101500700a03088000d846080030349010361206004220004030181d24050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 554354046 1250 554352796 554352803
    0x12030224090609010c0503061216030809090a0204081b040b09040b07180b040312051e04030b3304060e01030506040b1b0a35060a17072d03 61
    0x49403800c0c44004142080005002c9140f107a01d84200d4921003900300c0e00f500c0c0e00910846011458145c410510746c20603021100860030080018400701c03c100d000d070701034100c01070b00340d0702d04007140c0d1206d101c01c00f00d102d01e01580800703911034055055482041b5000c0710340c580000d030000c1640f11110009c10f054180c1554121032598030300040003503203030f0f1050410006001500070401c2062400c00c82c45401d129900019103a940d02100761401140100201c0744050030260b4142042d40341403690720441e400900044131108001c0001c207010181113448201c400110b0004080d12131820f101c0488060061890540c01c40d0b100c01000500b2901d8408180c0258010406081c0d42d2400c0d250900b95180000c0603091042d643e44802180c000d0010103031540c1c809107043c4030449200002c100d05201c44201556a05c12207075107815000240e01b20070f00c0b406540291049440720340c44038504422403603003000c0390b14583c0c03104504212465000401300c807a051240113600380c4600e400e029501946440d00b096 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 554355296 1250 554354046 554354113
    0x30a0f0603140c0301292e020708010605270604060b12060301140c0a050a0909060306020c0c0321030402061209031305061e0307200703060b04110301120302 69
    0x7070243d400c080c080d5070501040307902c500f19800b0b10850034856101d1841462801401d00c030b0409052003c0d0144907030000350188022104031500842c000350395404a00406d04254280007001030182000072110b50804010300c1d442c1c4c86d407081090b4410601e00001c0c09143d10946550000400300780c600c00a0056041180709810645000310525081d00e09060010f08030000740804c008407880c84400743c94240c1d081d1b2400c15607031043d19800701c0f00070314550801c3c03003442d00c3c108000042001c00d9005140b295038041c01c0d03c980748500020942c07540b2400303220010f98020b80c201414482d0300e00e00256401403004180e2400c0011048419000c25002c0751103040c036920014080c0070305941c080ca101c0041004a03451883d00c200340c002991003003408590080403031070200100725004d01070880305204003440301241101510310303004140d45a55070302c400e64180d46420791050311400c180c003403030005d1b0302d0b1035040a00e10303480c00808502e82e0540380c5007a41140120009180b42400c3e40c00d0580d1001c0485007a0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 554356546 1250 554355296 554355313
    0xe0106030b1206070f0507060e01110a0f020c0102100b06120a021312120309051507050d0c0212120408070803040b0a06120b16020c120609070f030305030a0f060314 72
    0x1030010310403024204242540c01041040525540040001c640d00024070f441030329031f03c82d0702c1c02c0c1014021942c40780c00103500b0310a09517504080b06000e080c58003890b035203048070645140070903a2541c60030a00d041c0160040c6500c1040c506064010b80f00c000e078050410307440c2401802d030000380804181c070303054005500080c50141c0da0b00c5844902001d005085d400030341e000019a41c08804641070b6154205064403225501d0a02c50b00303000280540122901c121110301e4146001000f85d8800d0014841c807610349052030611130320014110302118200300e855850501612a07991108a00500803509041e003000f000d40000c0d0710a015500461040003100c4583c246008010141c4a06401216041d448940d0040104107c51402a00a0902c040c010310192a0003001c81c14450020311a513080101c0c002c40071000d52001074014404c50300307401554280d81e2100985240c0d129140b00c0a0001001840400c2e40308940d6400244212503040c4001303145556603030381281c0c015175200c101d009500a00803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 554357796 1250 554356546 554356549
    0x907050d0e060109060b12012303010c0c1b0e0103170408420417160809030c01021204060503101208030f1b040b18030102040806040507050a06120c03060e0106030b 72
    0x385c0003c0c2004164007030801c4a400020b03203030528144103018144003080e0740091000c0b00d041c0320021000c00a002403021040000e406041c9003240c10084030030240f2a5000e0b48900d1080d040c000550709203010302d40e400e910719111a8800c1c0c501c500b0204203030710708110015425904002c141400c00002c2c2e1503028100000e6200c0d0400c80410407403040744444465104820b00d04c0e10102644540d02a0b0003001c041c0e90741000b529280202d1400d45c03c08c42003da914401d1142d0300c00034000e0500102c0450340c0b440039031401241c9072031100c44000b018181c1070005210342401200a10341c001031160340c0449496450103440d86000c40c0348025244003000205120000c5c0d100050a80e0010060140d0170008031403240710881ca2103107209000790740d080411031414030307110340545201000005001703645540d02c9210050300c071641610210b9243c403a0035400180390400c030000408131901c54440340d03010b0814100c00e5001e051001c0c0e0805c02c05035203200214044840610300341c06052180c0d8000340800080f0f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 554359046 1250 554357796 554357801
    0xe0708060f0c04211b140609060702060c0f19120f120902010c080315100e061801110a0b091207080901140c0a0b0618040b060907050d0e060109 63
    0x60291019060701800c014090440d4012142250720350700c5042850500c40503040791262518400a0541002d60169818032080301d28a005035a056a09950700800c2c1d00208900b034450824690f4000f0001d000d400050300d4403501900355520408166082c480c804074120742045800352290024684c0580400c051146020114014207900d0410440d00100d07000003034100c100b440281c00c0420b45503140c05045921030141501c58540c030020f06602e03400c014050038400d000c80354103103000c0c018800301c001445214100301c050300768014050615000d4102c2d010384810041c000001d041c07100740f4092141e00c07201001074821030b500800c1e800c59a801e08088150414004042c80c0c10280c4050004102140001003100c2d40b44409090a136001c006081e0b04800501801d0703007010041c06400c2c8820140300d00c04010702e00c21801215486022900e06032030b940c41d180b003518043c08110800d0002000e9017040c641d0030340c000d0514148181404c80c15a02c060585406003401c074a6504409d00400181d2540e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 554360296 1250 554359046 554359051
    0x3130f0f120815060c0705030a081209070e22050f010b0f03030408070e0a061203020304031704270b1002070e0112050615060403080c060f010503060106020706051c0e070806 76
    0x501c2c18040c141409211010070f251072a020038800c4400040c00c0c84010000c1100070001c16010382554011700791800c2c01c69050b0440c140c0b00c88010542c00000710380700300100e00d00043c0c0b1008190488607496800400c20388008202d8412480c6000c24048000320f20100045005000604004035520f480d040034480d01100501c000c602a6100b03000c00d00810001207808000c0d181030903560001d55a45555650181a071540103807030b400703441c4d403041c42495404001001564003503803603007036014440700f040c00861203684501c41c1039428404410034403640c0916406410315080d030011a503061100002582800410340080259004c0d01e0100410b1500194450040c00e00d40504c2c103a140081d118561102c10050181201c1c1040c95900081035484505035409903802c1710792281c07906200350480b070b515103081d1118551480d80000001d054640050401c1c10303038260380d018115452500d6416645600003010f8880c1d190305e410b0040d08420018411b5500f0100d03160002c1000ca0b280001d90307410501c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 554361546 1250 554360296 554360333
    0xf05090c0f10050315090f0a06120215070c2301081803070b0c0d05070f11070308090607060609050411190503060106080702011506080601022a010503130f0f 69
    0x8048040078594504031200300d9110181002d698a94495501402460000040a0b40186050140502d900c01d55000741e10405410404004050f1075000e214414005824002e60012144000c9450004000060204140302d45035551456440f0101380d4000c0d02c01c03c0400310403005004101d4265a4001e80d0341d90400400f02d40c0b00c0c004a40702007855224031400102030050b00e0604081901400c0050450302040040030080110f0700301030f200101121074082035a4002244410040c0c820b040c042103e001705c3c0c2d405540a840c00310000305008040e0844001552031640c1e07802d0004859a00e801800c0c071480c80344441410060303000c01041010040c04510f0098510114028052a01e00060309415269103040c9560303aa0760300c400c12405408000305c020180d8040c05070000303503103811001050240d00d0036002d40b848200410422208422600c020011140b1007000580095014500850f000300c00328000740c80700c601d2031b140d280e0580c20300385040392000040c650340c4050044400900c42c04410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 554362796 1250 554361546 554361559
    0x10c0e0612180a121d01050c0d03150803160501060e0c07021e030307061407050f0d050702070e0f010e01150804060b060c0d0809010e0601080d120209040f05090c 71
    0x74010418961000000c0c2401040c210328151030250100070400103101a0b44400c86085a5403d004024024004c0e42d80d030885030700b030800074820250300650965000c0000305000b02080d04000030200c3c00313080d0071150b0402c20303045060086036541c0203200030030b4143e00c9111103640f0700c4841d1410600711401c0384c0c004540c403401441404400304200f412141140e070111036000202481030021a0801104124103074948000030307485080144640140c80400c0028500c0c140c56540c0c02d20070ba465101d40012101c05440c01c00090701c4038142c0e940403c3e0020824812121816110300c100b122116013981d16006074210306004100840c00d030203074a4050000003414410210000c403001d0b0950202070001440640c0b59280c5d022140c82e0340e0260799100501800300c0b0f007407810b4008082e104e82015110101e0a501b0322910b840c003007000240243c126410b6130003e1400246848086801d0f8407440580801030b030b000c20402405a03100d000c2c9101002c0040740c0080e0505203500c07030741e1901000d080094000d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 554364046 1250 554362796 554362807
    0xb370201140912071202030f1602040614101103040317040e0a020f04030209071205010b0c010e010e190c0f141804050d1211281d01120b030a05010c0e06 67
    0x40f464080d640041d5100c4c0c803d044100005200b40d08502900301078110300390002c0b814a03020603211a00c40341450080d1b404202c49a11210008030b409103401d83c3c950480ca1948141c800c05e0b00c40c8c0007500d0028500d4081c2d03402c040e201d58458201241024100c0e01e08000420288503250391001c400341c2041402d94110b1800701e01100038000e0740607a10029115803549d03c001900e65028002900c1c0c181c2d0b00000c100031f10f6842c1c140c0850290041c0101100c41e42c40c1020400903210148954038100768250001c4c9541440f001070142c1e0002c0c1b0f240100e0310791010310000221140e9080d0f085000e4945040c581c88101713a0740050003800170080300020a610b40f07403010722002c0f40c2c000c1410300d000c1c500c07440d1051441140089040140c1100c000c00006440700041185000104150380072600c0c114901480c101002031100f00d444140088400f8880070040a4445480d802600b00b0101f0a460a00c0400c000032040c001030b0526290f403000b503540340d444050310007040307030704c503d2000c07411604691050401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 554365296 1250 554364046 554364073
    0x1609080606150f16150b090405062e030b19020a1e050912010209010e0a150302090d0204051501530a0e12040b3702011409 54
    0x20b1010300d20100c1000000654400b02c0940070300720741c3c0300000100301d903603451103c1c6000c0c02e800080071080b00d0418a00b08682c00341c0c0c070b44818064001e507001401803485485d4003a84a244003603004000840c084040c00c4110302200c44041c5000450060704032801d54600b00c00103102d0420750250f1507a04074410089500031310307000300e9051100c0010410755044500c5000c0259003d2141030301c0258024040c0c1a50360381102d0540040c40040420b903529005604104240712224082d40500c118518019030242c120300e2203540139054140c0010180c22061149030049070442e8070a807100824505100b000c4095560420410f10b1722090000d070400c41350b20100c000a8980780c0e5031748826510440d0100540204404071000b0711041e40820702240c81c0c1c10602c4e0110014803d0300308500450086075800b1030003003100803d55044501c44003d95103400c54150072602484c841040203552582c4420481158003a030244905800340c043c0c000046034000030b81c0010001d6401070a003105644040c8550b0442c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 554366546 1250 554365296 554365309
    0x150d05062203122f1801020c1018150815120a0209040c03060c0908010b010e0a030b04050f030a020318090112031101110d1d0a17160b1609080606 64
    0x800602c00f000140201036040b1618141107041c02c041d050181d40400c0c400c5828142004000280765403051003014400c5100590702c981c0c98104450f8080e810560400800d402444080c0800303035441584224240c5070322003c48140f504106203000101c031142008424401c40b038680748400d404845802c41070a5103010503948813490030000703016595420200b000c121000e4400000345a11a0701400b4604c0c0268006040005030b1191544660802c01507012035402400c0707025541d0400b5182c0003c440c00c589840d160b594024000712558411103c440c5540c5d07905002801100581e58007a5941da10200318100c0304100700c225481c4140c03081001080111800fa0b0403000c100d600d070030242150310740e09000c0e80c01810703400500301c0c80c548006605182c0b8101d41c1e10401a04007181955440842e0701c1c080503a0358a0119001007420200409680601e802c0001621152500c6a91081003002c0360342d0300c4801882c140d90103e03103e6402c00790302508582240d062000b074241d00008007503510f00880090360 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 554367796 1250 554366546 554366567
    0xf0909100e2214010e0607030e031207020f0f25080606041e050702060106030f0e0604240f02071a0c0906030a0908070b1b04031a150d05062203 63
    0x1c1c8102d041c040c140354a022084442a0801c00118403022001a4503000c1d0800c8100414907025540c005030041e406072240c0626031031100029030410900c8010a00b480102409060941c81004003a1400c0d0302d041107403074005144d10b00500b1889039400155580005841203000075008208000d000c01800040e40907070110017154040341c240c0444144606403e00c41c1580301c0100c0c1020208050550002009412030301c06079070400c4407007540141802201c0714812071104c3d50f040400481c0c086001d014203010724400c0601d484884014201c0000c04640a5142c0044066000300300f0300c007030003000034000018200e07408400c056481c0c00802c0d00060310403020054032800020004ca010644c0d05d038000400a60f0002d0000e540d48540c0c20103010141003140c1d03074400000005001e5046904400a48084917408018086072041138000c2c0e0003032007001440c0050400314500c05107501e0fa80c054509005600440c081c10050400805452030401c410f1800d4104100d0320680b0000244d10004056 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 554369046 1250 554367796 554367811
    0x3020c0c060a0e0904030f1d030a150e070e040c0f081009050a0614150a060c0f150603080c060c0301030308060409140d030f0b030706091a0f0f0909100e 67
    0x295070302d0414909071080399400c90803c1d0081c0402c0c08000c01c06800c01030180d213010f0a910707600d04034182207600c45003418820444c1d41d09500316801c48000138003048040c080c140e50740c4e40003140d0090181c96052600609901015450340040b05000c01e00024078580005490110002c44c0303105c1c14650b6045c0d684051000b80302d0100c6d80e85510001307001c01400009001c0c0c0d4000824425031807120b01c4401101070135103041c403100d007660410361301d0341c9084100d40c021922181c0380c8000d020355a40311030400c20040c050940340c00d007a002c158145083d4038402c000285104110b038503141c80300118090700c1d0510061407120113800400c010b00129030011110382e48050100c4002c2103040c110f107014000b03242509107111491280001100c076030b075055041082c1d80302c0d5840c4100004006641050303900c007524412040800c2c00b078602404000c1c42c50f40c0e038001c20a640a841c5141c000d00d003a000410742d000340824000d00e480410300348054680062001c0d008055100000442420401c108900143c090440b6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 554370296 1250 554369046 554369059
    0xf0a092a2d09170129180601020606010c0204020c011b08010905091e030706060f1a041409041a040b0103060513120e01020c04110c070510020a0f1110030e01060603020c0c 75
    0x1031401d002d40007540480b1040100413240e44903940603003682c65088200c0c131b03c2014400c41c00b0110b40400104d003881100d059000b80025103440380156580108041e05130b8202d50200715034a60501c00340180c90780b0f9019185105024040c03d10001c1000324180c1107410384908103030078480c00507070000e0f60114902014104680308c2c1207010080d442e501c10032030000c1a841c2403020020724101042051011103003400c01c00410080d0ba0094164248210300071500080103000559005007051013015921911481001104183c505a02210320004541c101c40d6444080c005000300089401540c1c0c00c04035100748803050365890303070f550031080000c2810802081210840c110241e81700708540b60b0701800180c020006260340c0010b446140d0f00103410070380c40d0301c07a1920001d4603040503031b41044c00740e0307641e8068298010b407070780c3e05105100621070035070308000d403034810042d0382c0c2c4c403d868000480d506840008480d43c0510b07405007564080e84c001d0003407510600403916411408220200c2c2290121000e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 554371546 1250 554370296 554370329
    0x4260f160e061f0801090c09051e06040b0c0a05100509190809040c09080c0904030c110d12030c031104081203060301060f0e150f0a092a2d09 62
    0x1240312014030040b08a069000015203c81d00c9401091050507910003042c00d02034070051920035161040288607003604010102b001402240c01d8009002105030000c01e00740c502583c0382018101500803c81b041c0303d54101c44421401c1003420030854046214001e820b104500d404407569464155401c8000c16441d0300c2e110030401c02ca05d000440300d005900402c10081c640e5a884000c03c41c440c1ca0090014038440d60000301c81c5840c103424800e01c52549036694484401c841e96601054820301e220280c0c21450300c844086c00241c4450307190514182c2c0f41d82c0015458094100181911802d29080c01030380c80800c814008003101061070101c498140c503240350740b070301e0382808240100050342c0030310b2030009080d0f070100d288000c122505000300c24440e9007010952856040140301441c00d049c940d801103019104100c151420340050945a400d04d00d103201d032114284170194199106101c1030300044c18000e038441d0782e82081da1024a01140110440b800104625001d462416240140000800355480 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 554372796 1250 554371546 554371549
    0xd03050a182918010f11040501110f01090f05010b1e010c11030303040807120504050d1403070f050c040e01051e13120905090a090309150504260f160e06 67
    0x20725040080c040210400e8910704000c43c0c000d010001242850b1a50910101c01c0045260303024030902940c401d24102d1809107014015240c00821141044960054800c0003d00200a2044203261805010a913030040c02c9468100d0840789040001ca1143c410102010300c1560001c5040008180a0904210318a4030382803860b420100481050390502c03001042204001030007024040c158882c071000c3c208009201416545070007640521078111451074440030215010920304039803145104103030380c600a400c0d11a002c00ca89010810340b6198049542c1d01030605103842905c40b5200e10714000c10440c200300c0341e001d00040481d0a0300b02002c1d2a01d0204a1a0401501d803031000ea9029025034000761100201900b641c1041c407a0910507010340000039180806401170075181ca0381545e580c0344260600f2218180088100d0584d410000140000300350000d55001c0d03800030407a030300840200b10002c9500355181c41104c1d0365a1005420003650320100e1082000c8000590761310041c00c5e4940d945420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 554374046 1250 554372796 554372843
    0x2031003050102032403120f072f010f0504050f0d0303021c05071803080714030409060807031b051c031b14060a050903091909020307020d03050a18 65
    0x10000740595100106018845401ca000a010100c101c1c10704600e4040d00d404054072400c0c844040e0000710420400d2070403203075806000380b03070f01d902c140088200c1c02d044038401c08022285081d12a003188800d25440865a0456a1060800010326180e460b00b4109004034a42c0007001d80324602035000c0c0b1894000b0913009405441c036103403140402800c1c070800b40f900840949002d84a84020450214003070a00f42c204250007c260303078000b0b107043d1030540035a4a0020824486180f15480e010a10005c50380c0240d5000b0398009001800082101380c1c190b0502c0044460f42000346444441c0d220401c2009458400400d10744000d03080e01c44c1c0b5003840c5800c0030390b80c10204480054511040490700401c00c040345643d14000c0c8101403c4800c2903803244000c90807903001303403404243c6a10034080d1380100d140400a030b0103e1402c030307d01c20f200c01e039688548500b66001918064050303000b003a504a0b85030313898410182c0c400c000c000284110200321218101c002d80311030b409400015040c290b9400600b450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 554375296 1250 554374046 554374049
    0xf110a050f210103060c0923040912030608070f030201140c010212040605371109040f02121312030504080c0d020f16050906010e03100c0816030903080a020310 70
    0x40c1c10303041601a404402c0714820000b40003c031a00d61500d25070b42040e5220705151b0701a90301406009017424010140e000c0080101c440c002d52042e129000c00f40014490340750070021071042c0d2400f0480c0c5040840d510304080d10358200d41c81416190b10108050307030344525103449008000364800d0307490b144105113501902c04c0c1c04440050b010720030f052000300703d43c40e4442441007982030030458803030252980d02e0f607240d051041e040268005a81400d00c8070101540085d00008802200515001104003c58203a40d4080d101400e903680c0410010038040b02c0030351440d4491104d0301c05030381c074074116950b5030510004c0c511044205079984002404100100088840e0011114122072003d081c42c40c0003542c981c000b044140f454056803200100c0c1202200d061016220300811307119240c1d592070011210003c2c031242c100c1e45841450394640c4100315501c03d002c038022107551840603501e07201c0907000020103111016420586441460004613074231011180d04110b003100091307500d84030a2604526042c01d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 554376546 1250 554375296 554375317
    0xa05071401090818011803060c0c1515150f030506121c09090204080705040c05090d0501090b06010504180509212101050901120201090f0e09010f110a050f 68
    0x2420710b00414010910003805048802c0c3c0741303c1e58107000c0a00110768500400403031815000c418942071000410b150080b0515078041c1c03911000080894841150851500c4001c840d410b07524500112000007100ba5400075120112803403950700f0300740c0d00040c00d248440f040c0400b00356890011454980c1d41813203240b0102002d004640340c4507070306d60800c01107031141461080450040e0000284002450007904c08840c071550140c49024030703141c2800003500c40301e10500f0400004001f0721800b0b50b134401802c0140f90140000080302e50040c9003404000340d001d00003a050240510007005000c50509080a0011000d88041240c2d1116402c0f00d1903e1030040881c0c5003a010101002182c00802001c1c204011001280307110a010452208810f60402e0196507049111180180b000800c5015007031001c920600d00304032241c0d96540b10905c5032082e80c2000030115084028407002000c00d008000104100260030452401d00c80d0380c486c0c862240751a603009000300420603010070b40c6a1805e4401c0e2260 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 554377796 1250 554376546 554376551
    0x30a0f0219090c080609100302280b0415020c06030a1505100f080114030c061806030a0605040b010305060306150118060801060207060318060e0109050109200d0203030a05071401 78
    0x101c038400034000d8210b51a500f40054545000614149000800035024502c100741c440a0203040d41c081c0031511a03c04201d920100c0994111138151241944078401440c3d504000c98607542001c3c0c2c0080d0109100d199942194013030f60898400e0703035070b00d000c59803c4402c13841e0024907160001c000181e0310640da07010a80c42170900004010f00c9410468140c00010f40341d45500c403680c0c0b030700f40780ca440c4ca210f00ac0c001e41582c000da07040c51942c00c2c101c004000c0540110010401001c4907030010740194402c80304074405549a00301000f071400c007409503955851003402c0502072440d048000c669200401001c0004182170390381c45c6802c59002d1411840041c4100080c0003907981c1300d03140944040400e100344e070010701c50400b00050440c4070307105028001000320500082c0e0740380740c1c40c0c040c040e11600c000d500165694000060004000b4800e2000484c07044025049840c02c81103003a440705a50010940a6000074000f40d005980100c1111103218a5040207521a6154145521b002508014140e030755032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 554379046 1250 554377796 554377799
    0x7061b02030c010c0c08070b062b23150a1806060e0c0c030405101b0c0303090503011404021011160801051005010c031218111003050402030a0f0219 65
    0xe901000402800c04000002e119201000108844c02e60042502505840b41031003100c0000320300b00032690b00084010031340c0b000c00800301440011a24004049154041c189000808008109100200f10018001e2840c140c8164511094440b40308003038102e049035080c1c0014002340040e6000d20761411010b1105009810300e4541200100010301410305c03226400d40008410000c1102110b10500c4110061070a1030700d00418809082c0d04401c0100610844030a0b03502c0620541e03074201d05642c0100211044589542005800100d031604070b6030190341812a440b0000d002060741030707041070f819940d404a5038140070741156801000304036040c0c140101c07516000d40080c1c00101c503098421650080015854051a090060005204107408603121080090100740100080400344200401c0440c410017801c6400031100303900c000481c8c01d0341820513240320364103105c0c40c1c407880c00d00701e420200b04508181d00065907c512200c80100f001c41c03600d00c1d400c1152101c4801c6131079107c1d52420070030b0b0203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 554380296 1250 554379046 554379101
    0x3031211160813050303091c1502031f0b21272803080c07060e03030a0e0f010b3607080402090f0106080c0a0212031501080a050c03010b0706 62
    0x294481c00288503c16010800440e0500c2c1c080300711440c0b91001000c0d0582e200c51129100e070400c40e186c4090301c42e00244440c0d05605051800214456041302241c690040000b182000d03400c181900505031200050040d83c440b007100e92001c02c100b41c03140b10303946030355030701c440c40404110501c02c0149100894003402c42808ce000140c0c0303c0a1111008803c08082c58003101c000f401e45208001500260b00000481c0080030340f600146440c900030b04c1d012601090f049900e82c61980290352098001c0e43d1141950070a0304107004100c0c80c241c0e0070000340051101517001900c610f2452400782c0c5602c10069111401c0001e0042070108060803a600c82403034540840c0142003458100c9050b0700801059000403444a5804c2469069510b03907180c12189450b00444500c103070f04456401e50541c46500b28019441d000680598817071801602d03042000f04040000500c680320181804d5500350900d010b1003c44d1811505880c1500c0c0040c181075245c9030241040e03c040d01ea442c000d42d80c033042280055052 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 554381546 1250 554380296 554380313
    0x1a090d0309051014070f031209030206150a08060621060109020a1b020a0e1009050c040f06090e04030c08070b190501080a050c060a020f06010b0703020c0105040303121116 75
    0xc40300d08998556403202c400c1c0042c2c480c8090741055a804c004104903000000b008100b4600525009141041d0344c415055210700803a55148802e40c0541d22050400284213003082c0b0400040d0700541e80b58808a00d0015450359852010303226612941812008050225041c0c9565030b02c81007003002c40e0415695100071400035402003600c4030004018007100d102103613180441319102c1e80e01070300e21030005217010b200c00400301014000006249802c2c400003040c0545020312030040000109140c2e0b2181340000340f400329aa2648400103021b08184104503018003205c03d643d00581508003401c44d1391f1145071510040c85032400c0104044a0b45042c44411003211203680040d10706840100314590b02d54010580c0d800130410028440d61001c0e0a9140d00d0420341e02070b103600303046801181c154080c046511410520709030040c006604012409006065041140401c813000a003045841c00d421601e004102c1d0030b4421001c41c2060b160405c1c11841c1120b201241c001c02c0003405240b102d24506d25001d5103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 554382796 1250 554381546 554381549
    0xf02040e2406040f0b0906010e1215010e070206040c0605090307090e010506010210021602060d060b0712080a0b010905120f0102041d0a06050603010e131a0915060102071a090d0309 79
    0xc0b881c2c00c1803040440071307500c1000c1c20710200030304ea1219a0313102e400442d58440c0c40c0c0d80c030382e800080c62041500a558100012440c20101d40b034000c0b043d40c1012031040040c50010304203030465108405010101d0400790040c81540c0c500d04d404c0d980c0d0464030380428070f03080456100c0c03074a66103851f81c0c151128206500941c0100000d90a0b504100640c0000d5002d134000e040400362101c4080140700300621708480200b41c50f00f1010404103800d540e4940f640c00c3da0304080f005895000f002d4000001c1c0c140d03c203101c540e01c00303c960f4041011040103000202001468043e850040d10b041181000b4040c0c100401603003d01104020743d0b07541d49540300d958203904440340c41d002d43c04030480455440b0742d05001d80010703034002078140760440c1c0c07a150140c0c2103c203007d04054416074281e01004003149401451b00c0312240b08003200300842c1884c1c0c01d540c0c07030610400c005015030f480441c01d000d020b07a8041150300071200c03134006540c80ca1900d00d00d1482e0602c034064200d42e012403240d81714000c26402159480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 554384046 1250 554382796 554382799
    0x1155604060908060906150f0f060a0302040e090a0507090c050c07060f0f0504080607030b2205011d07080705090102070506070c0812070503041208091e0307120f02040e2406 76
    0xb10a80c85d1034444550b1070109407100003c01852400b1803020303082c490000000c076800100704007c4154403c0101e501540f00340135060003e03030002400d02c101c00003515001d8100e80503000620310702c01262286901c0f00d0450240d201f900e626040710b045620f105074191380c00b1807010710070b07102d006070348a0001d440d401c0c5a6044501045a030170744000c10f28001c1040d64112140b2502030a0956502c800450050500000c0d00790b000781e2483c244030492511100e08800c030070703812b4030000c2d039541040c51442d6a46d01c4204884044010301c0d0410100a03800030b141600024182452034841c090340005078100966504981e80181010526005201008140300100c42c0720401b52801901c4081200d100c9208220000c0e2660b0700130401040f01d40183c0c0e04c41c0c0840e5000d088a5400e150302c0c540001d203000d558120b20703107009151007000c5d001807600344580001440b04500b07800d5003245580c1c441150803d0924041c1c401e541c1c801c980c203401c0034188041d000945444401c9590013442400200007800c054540390b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 554385296 1250 554384046 554384053
    0x20a030906050c090906060c030f0315400f0c03020306120109050a121403090c13020901090e10050d03080708010b1606050a06030501155604060908 65
    0x1e04022055404c42d02549405000c81c800d5a440000f03105169211601814241c4001c00170304807440081c2015601903151181c032040500090400c0200200005105001c902d08016948180300c12107190946411100c84103c0751010900d80d181c4001d051180c10b4050150400000c041b08681c5680110b11502044440401d66030010740b00600325410900000c1055103d114000c0206c2d2601c030440040344032a02e0408014002d0a000c2c1e8059002601c0d240010781c010007003441c40385000310352490007420016085003415020f4000800c1c101244c8540c03c0b5090145000c601d010010710b003284d014043c003038000c0d0003d41c0f00b0b140c000c050500407140d00d070020b00035500100d6001d00d01d004450202d01504001544d01c40b5070788801d0b009080c060298001b543d5140c40000000e0340a0250a01d6800761061070b4800901e0045a944442c1c0c20343d5281d14610f07400403404018010075220310420000040528110400c5035448011003031a0f0340590300c0342400810001000c5601010030000d80704484281c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 554386546 1250 554385296 554385301
    0xf0e06010807030605010b070b06090a0f06030308092a0427030504050a1502100b031e1c08040f0f15020d020a0905100e0108100b04031209060c0b07050307090504020a03090605 77
    0x1400300070b00500d0001403249403400b0102d1042d1400f150352f66000303101c400c000290052900c460f00c00702c500700c1e84114081003600703080010615081c002610a00c0c40021040340c041140406034a441441c10038007403040341ea411101d00d0713800000004031880c0e6501d005d41808a0340c1800c3c054899007181c450503208400b04030b008905c0d0380300c4c40101003d10400ea002400401c2c54040f1240107420354030038080c1c052090b012202d08076000d0954400301c8405c514003a003018900348011203040f40c0d0704040361003800544c0040c4800100c01c4290728160980022040350000050301d8001c03030407582e81d888101d0241c000f00e0250120742040d40188014080c3e510380d6540942c0c1c480a100044403100c0c0141c02040031490301c03030081e5020b030021960000b05d10840c031403195103030000329000780c0060700255002e100fa0441348680316040585e0b01c0c06000c1e107081800d1b0050a543e6041c3c8810f4000300801c08124000c001704030341c540590380308006000018020364840042e080018014000002c1c140d42d11400c0a01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 554387796 1250 554386546 554386559
    0x1205132402040b1b0a08040315020c1504140a0203030304060f0615021b01030614100e12070302040510240c0f030e03011d0d032406110606010305010b09040f0e0601080703060501 78
    0x500300001c5e6440310086042602c0c5031201113041508400d080e0416030204030240c021030042c808054041d001b50403010075070030241011544006440e80720413035039011015460240c1d4000040d00d0780213500050110b10800700d0b40d004070140559501c039007c020700308060852010340100e008507152020609000300c2540d6400114240e030b0301c0b88104a01c4500c02c03141d103005030030300303540310000c0140a041c40c954203843c403c0852410100f42c035102c041500640402e0003185040e00925030058805028505058105140102444903d800040d03074068052800f002c40d07401858904da402d5041480450380005505001e003c4140b10003141d4071a51a1003071004120042c0005010751404140040c201d500c2d002c0020f4008001c6a2041006804040108010002400410000780c03126990785000300c91390f0180c0918046016080e541803608080c0140503039503a440503641c140d501100c0200d555144170000c1c1c401414a4440d9a03045e0041d0000440e2030340c80020040c0449110310b0040200c2e82e65410f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 554389046 1250 554387796 554387803
    0x15010305152208070c0302150706061a16030207051906030c090b0406050913090f03080a05040b2404290f0a06081008070f061205132402040b1b 63
    0x256450701c002c4080401d0b40c003042c0024050491a40700715401412181c5076000146561703054042010a100300103140700400071503015580040c070750907844003a0584c20419009040c00317480c071401c01c14891080f422043c0361080154000804000d4000f4281d991128540381c6101c085001d080c0120b0704080010007028414074503030040b40c548000d134605140c01c10000700e446034041c4840e154001d1015003000c100c2201d07482060f000030f100b000c444140310042e02e405008c441d0001c1140f03540518010801010640807420700380e00100d50034501d000c0000358044442d0b00e820000805401c03601d450501080300e884402003803c482c1010050402201002d404c2001040c80712076156000840802d007084a180200c0342d10b900a410900c1684800703440710b113140c1c54a0695480082c540d107540c601042800c2d000b46d11138800c8690034806001a29064002e1907072178905030001401c014910b44100030030780320303c41d0000c1c1c01003200c1815595103a58000031a825009030720000303036180458100900c0d003440003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 554390296 1250 554389046 554389081
    0x40e06120606130f1d0106030303111602060a1e09030507080c060403080310050d050102120c04030b0708040203031606061701060e0703150b03040510050a020a050d0e1501030515 78
    0x1891807140424983c2100080c09401e40c0941045444510506180307a0f02502030300160b580d038000150143c65401d004098480c43c000081850703404112201000d504010710080d1590150340896942e142684100c41d100c5d42d4009810340e010004a40d10305665000300010101d078020001c44e6809601d5042d015202e0a01d41d907000d80c071aa04010820000c0c102d4000f45030f011420500020000355100049a00c54801203401ca81c180d5000501c00381d080d80007020160013a450140490415045940d00e0410070406841001401101e000090442da000c10848100302e41c12109940c03010503e1404401610740c0f4003c41210703000b0000c251694041c144a103c0c21100185920f0415440c1c440e0305500405401200b014004048000440c042c0709600085004030300c19001883d965800300c60003002c60b0001b421000101e0b0041159032019036111041d0340c0a100301c07000005040c41c40040300f602d04007850100466100010000105000c13021461403410b00d64801d003e0b0340ca6859000040017900341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 554391546 1250 554390296 554390299
    0x110a080118030806040b091608070806060f1c1508010b030105090c19081524280305011a090702030c070e0403211505030a050a060203100308040e06120606 68
    0x104520007001c24070500f0f00c10340011024000040070b02c1840080b8095140840f803003400c80d40030503c41c1482036400104180c0c425803620b06100e0500f001d1000503074511882c1c01e40e41310500c02240000b0000c0c1000044030020122450400041e0544407644c04190700c14492210254602501c0e10030360b007018015688518201c20240c10901410700801003800130520314056800050000481d944e0300401803404d04550048911801d45007104622690000e2100201e0010b42007401c84007a58551001c1314074000e07014500903032800e110303000010030381e5950fa10181056082c045540001001c62011080700300b01954a05074a07940e070441a80d03213106943c2040e419500c007483c100f040d03007044404240c200e44207191030341b01644c00c01707034000c00345030003640307404010703a039a0004100c00000000080c010720003035000d0b0241d181e681d00c0e402e86035910030740040e0003140c00100054501105040d00d4000d1680403955a44503600c441d03401580a1080b61564040c030074000070241000d20004895214140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 554392796 1250 554391546 554391581
    0x1061809080306040e10020f07020901080c21032b110313020103020a2001060f0f0f0b070203120a180902040b03040f14010908070218190c090b07110a0801 68
    0x300c4209000c020004170944c400c2c0c90055410143d0748039141d0008041da4040c03061070702d80b62070780d42c010030100e120180e00058440d840b502c01d0801c143c440542c046940842420788200d0340f14102240f42c01d51060800d10000070500c004614900c05c1041c03030041d0740c000820801c00205c0007185000155200554500405400c01c1b6221801903111341c00820316a215441e001e0310014002d030300c0841500d07816241e102241d46607001407140442c4038082e45e00424178910090049840c0400c002490080c6014102c40440009403030020740d2401c1124600f00182418000e90303440d5007010007800055019031110080950030f00010b5034030210300a0720705842c554a011481c1d41c0360341ea075000e1050300c503100c2101c0c500720030ba00007240703c40e00384107030b1003101e0013074040a0b5100c61900c1000242410140001111104441440440e00204403455100100400001807250600d113082d158088158011a0880d20004a42040013008030441c501001c0580d0302612040d240d421103030a98244420104074941d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 554394046 1250 554392796 554392801
    0x50708090102010906050423010b010c020904020f06070803090f07030209060f010309051c12020a0c0308040c09062d290c0d0309050f1203010302090a021b010618090803 74
    0x480110003804840c00c14000020704d004203945003c01d43e10219800e8409400a40c01c80d030b01d016490704c08255200c1c4000081010341c04900010b45125003408001c1d005414860001e0110348600d10001d0120100504840c5c43d055140381003205584115076020032401107101d010b864550001d2107901b6a9170041010005594940501114995020025041503100d45291011a806001c0001e24603039600b40c8105180240780003500e01141c40640c10882c0b8410098603005951000c0c0034202203505181110980d220340c1480100c100303041d00088840d0345840c0000079201c201809000342d0b60407481031043e410640d294000c8017441c0394442e000540907926072030341c25a0450801246894080c0041030b00304000004290b103000090398112012070740d200e8550040c05020801018000484d00062000da564080c80f20141d01040c0710080c000c03034028011403298106134058480d903008401000c603500250056460191400d445000803020304107505a440f0b11207401100201ea802101807840c54 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 554395296 1250 554394046 554394053
    0x302071403031b0c0a03080405010207060504082107081204120513061209061e0e0615040c09120510060b121308040f060e0a0e071704021f020a0c0b09010507 69
    0x5006030f071040c581d280180104100c56a440f940c00c400910f009000d203a440e9420000064a40565a0061414440c0c1400704105200713001500000c00e89800c0f01200d0803e0000b40124031a019948006080410100300c10b40d20703515851080b803280740a0000009824259841560755100300c07500d84400e0007030400244181406254a84044400c1040c001007960b00e075241d1204032224000000c525103140069a02800b48501404070314100ca00b0103400d6a0400c070001c01110a410030000340101e41310b9a8902101c1d02a0741048000e08018042251031740f070354904541c4602000103070400312840d0000100700700c0740d04400d55282c0309000507a44aa9102c0d80c0c03590758040300c10309080b140158200b0020624100c5081704000420207501c501d5203c03501c900170800029115003105141d11640700420a14560044424030f902c00d0040a0010300e0701c40d800071031a0b4503c0699904040c01110b00d00c611242c0d0300107605000c2d503001d0411881e60701d44580c0014a144680c2d0750b090700043c0b040c400700021 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 554396546 1250 554395296 554395327
    0x1b0702012003040f180f02091f03021306020609060a06060c020111070801020a02071d0f01060c0f051c170c0405060315030d0c0201030e0a022803021c030207140303 72
    0x140da40c0e500302d0381083d58603400c0740c440381a142c00c500e040c820800e10007030203144180282549496081707401d5050000d83c50108402c5082d10490b2100c0c58900051044414081d5045466050036a482c00c24856141c1d035019645450983e108512481000b001543c2d017449442400c0968009035031380c0305814001c1d001164030182a600080c100d000f19840014102c1e003d00c001c0c06c4400c130940149c00c4907403a0540c166500c4541c1406155035854a5003009544185000c405055032100d09001c1c2c1c001c40c0c6402e00d100714040c100310080c070340d202e2490b01c400c0d80c420b4002d041e02500090b03681c4200d10314503241088040030081d01d000100010500c41030210307142040c0a5070b4440d4030785801c420035019000020b40381803902d05076076000c070341c13014012815135034103028000c1d412044070014200910a90b000c01c8903000c40c8203103081c0c1c5a040c080d072206240c010414105c010341d00109294594100d880c1440c03c1c2c51485d0703100300c0140c42050400100d04403101e82a0141c2c0a00801450030b164400442d00003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 554397796 1250 554396546 554396597
    0xc01091a070303110a35070c11090c0306150f040303111c0c140d0905060903010e0114060f0d0f02090604090213050f01270209030c13051b070201 64
    0x41c140c441e002034880780c07104d00250450342440d13a511103000d000202031550000b0f0100200c050446601c0e004038901c10308240786600b011151400800d5240d10303040098644280201e9507034441e007090240074900490b01c0c080e41c01041c00701c0300040307500034004281040f817280300030101c00e00c1414001080800d000d1100b84410110810076204100084a001a540da0441a0400100721061450802d0061000c900b0f010700c0f2013980100304003444060b000c3d01220507845050304c100c000203049509510213401a83c0c2030886c0c40001e01c14400c0b01c00100d40c14100445496000720300c5140b150000d0b01d080040820840c1c0c004208014102641d0280307d000c40004140a070820385131907440c001a01c8009030714900c00d04208000400d4182004000a00c4106901402005946260640d000452100ad14407907a04580d40140d40b0031045c40868140132550140366448401000381064040894101610070700c0c1e00301d07000c03400b01841c4807940424015128082c2c0040d0400386054035a80301c2c032451a8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 554399046 1250 554397796 554397803
    0x903020a12141b0c040b030c21030c1c0c0807030302030a021201090f06060e0109061206050603070906030f020307090e040303060e09010209180f0c0f28020c01091a07 73
    0x21100d120b071110501d0a07400f1031500540314018200c1e00b401c103a81802402000c00080ba070601140307492a0000c1e075100900320a280c491011940c2821840d0451140d00c28561140000c5e44c0d281c0070140101500c4a650135404502c2c3d0780400c1c001191a0701c0381c01c4040da52a40240700342e0400384c294030124029080101407a01c0305a003003094540300c0e10030b420020b00909000d1404544000380908a00c1501e000360b1100c000e002c044019400750303a070061601020f591540c40c1020842035000c210901030314080c1e2000303030010800014820a40e0303018000c007055640f20340342440b00c0d1648558100891000b15035400015001c044d040c040071402c10401074021380646008940c154640b04601c1540d0010b856005030360707500050000c21420540c2403c00308407119111220b040c0780c944140f41184c6030046c400d0500075800508180d03035070080000d845119001d500d001c1896070a44c500c90800511070300f002d070054801e507490002e0643c41681000c081c1d070382c04001007100400403a200c041503040303940e046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 554400296 1250 554399046 554399057
    0x19030c06080705090310050103030e04050408040501030f0603020a08030702190b070201120e0d0801180612080c071205010621020f24120105091312081003080c160602010903020a12 79
    0x100b10340c0d4100300200740c20020000007d403035403651078041c001140403525a40150f061404000100b1442c00544040391001c0c2070114001a540c07040314010706990704025070107480d01c0c501090524000025102452090381d140309480440007521381f84604034803d00340d0340801040400c006510408800c0072400c00e454010031004200b086403810081041d40740320004150b000100119208500c1c80955494501e8040141905084120820480c9402c0c00b800000c0005101070503600b0801050b0024404000c281d00100750504c0d0aa02070503081c4038802c0c002e4402980c881c4292062080c01c0d200960003042e0303018460305a802e0114900c0d80d0440005030340503102c3d01841050743c1d800201001110880d95040c20f41c186010032151040280c07030a00c040c0003c201d214001010018802903003200e504160505a48298080c0340309490f540004100c0c003030105410101200002c0c800410b010b9126035020850703210001242224044080070740160301c5507245502068014000c28080102d40c80d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 554401546 1250 554400296 554400307
    0x6030609150714122406090603010b1602060a0c03080640060303051e0f04120606090e06040302010509160e060f0402130e01051f0324060c0219030c06080705 69
    0x301140104100e4245c944001c0c500c0d200410350703410840405c50180b0440e61320b810507091001050085c0414000d01820043c0011040300110b41c109080c1061a03000b88080c0d5107940140d001000e00700701c04800c5003c645804041006840c2c900303410f1a00c10340c54220107001d0f844200e0903001c5000b18940900711b1440d198100d20090340035000f002c02460003a1607269892096010b42c800003074100400000c1c0d9107041c03001c1144988480c04a600f1103005040c11150840b240c101880200f140d9805050414070f0b1036610007006001041c07452080340280c008010075611212080d84a0046600c00e03903800c102044203100d000700307004006130010710152a884070406024041022a400041404c0301ca0385c01003000c01403080c08502c61400350000b6031b0401503090003000c40210a0310120711440a254607208100402880140d181507025401c4250f81031182e0f540388040c1c1002c40da480247d0081441103220301c5200e007040708420403203510003104050145003600898045401070b15102c00c21004004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 554402796 1250 554401546 554401567
    0x607050a08150a06170c0a0516060f0510090c020606010807051303140307051b030a03050711130203060f09040c0909020111071d0a09200d021806030609150714 70
    0x418038050b080a03180c011000c000300d05d205141e00c600030280310003101c3c1080b0f13440000f6407120540d0012000b00702c0e074611a908520f00f10001c4c0c5001103003003040c4ca107400200f1403140e403045092000c550700e82030f0400130840300100c126122142140d0345404030b014040410301a174880d00040c108115000340c1c442d5899280e54032080c2ea004041001140b41d030001c1510300603c48280305290485600c4458220f58803c180d02203901c88000d040301a05011021031003100f0b0012541400908490080c09610f1026910840c00001d400655250303014890303803041008181002c001a0b409503400c5500403001c64640503103000605071440d01241084a60070351010150f82c100041e00c09010f105c9400d80c01d802e010085021403002c0142542101400c0502520104601100c0c40c034503550210004610290040c02248500354100f070000d4101d03401c0800407405003464000f40340101c00032400e444240e00c071030000681e02c2100741180b124003194400404c015074040c640480e0648501d02c1c115007401e40001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 554404046 1250 554402796 554402809
    0x40302030f03070302010b030a0f02270a09110d020f120a080705011b05120708070201150603090b0f01360905010b0a0501140406050706020906031f080607050a0815 72
    0x3240e540769540042848000c1640a00499148070410350044c800b03846a0380b00d220301d061800a0103800f400003000001c038001c0d0314454009044000c0001d0851504200fa41c0740004d00000c5400d48041d045081030b07881c64a80880d0440200b60000e040b660000b95540070440092601601c01840d0310944903164001140200944085402540001102614180c08900561b00c00c10400c0411100700b2000f00c2051440705841e8020306245800c0b0215900d8030b0f81640101104a55900074516481d00050425407580103a5540c0344102d60020150b100e00040341603904d8203005960b4089260500900201408000b92600c602810079421401180344044000c50b80d4081c003e887d503035190341100d695030070700380208030003800286896210303955401d0a01d003107170199000700c2003045400141a0309001c46501600c80ea00030042c446a6281050400c0d14210080c013a4000c488400c1941c1c0001c400801042c1036102d889240c0383c40e481d100100350200c4040c4030080c184441202052a2824182c441c0c1c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 554405296 1250 554404046 554404063
    0x518044409030604082122060e071e051504121b031a13120e030304030b15010908010c020c0f0105120403260121020d0b07020606130203070c0308060604030203 70
    0x452046030313100962001c0700caa41060729444c050300280385080c041d4507e43c03095008551664007411442c40e40803031070301402501c907841d0700c50214400d0040200e801e440c0f1640080400c100403000d0891680c0d10801d103d9000d00150748164660000d1100b0440c11481c00030178002c0b40c1c4a4140c00807206101452000d134038070240c2060350124640d403200e400d4034254440054016651041d40b80301200300340d540810b2040d00e05801008c110207a4205615034500b0402c0e01c0c05183d0100060201c0d2030015002c0007851900e010240c0010004180011226070620179a600f03da580d9010b00300300310130081840034103181c4554090411008101001003c1c80003c0390a004503c41d80d42c1c1c2ea51000e50780c018a03c44040300001c40d10300803074840100409180c40030400320302c055100b100c00e6000c1d8030340002040c80c0c4111501401100e00700c0104034910390701085161040070102c0d0307046111180241c0240890204682280202e81c00c4c60004000c2802501c40c103500c204000c0002386404d03201d502080c1049140e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 554406546 1250 554405296 554405303
    0x1902240408030426032a010902040e03090109061704060b120109060c030609150e071b0c030c0b0f12190204030804050f0904020a090b03070518044409030604 69
    0x50b18980d140800604e400003001040719001941410f1b1009070001d01c41030040d800d160701c1c64401c3c03071560740c402080d04045413558004001300704803200980e05a4413544460304550000d5220074010400c0b5001d5200d030503e02200e02007410059031140d40f40b5000345200280c02d5071004c01c9100000b0200703000d01880d02828400c40f00895104138034074014017580c800c2d03048501d6030750400180c0c9171a15036101c030650807106e10b034070980c0664591076419904403540009044c00100603074012418031490070246022688181c010014240c3c1d00e4500d20340900400161011090041000d2050301e0f03003550806411007100100c00104885140ca0003089901c02c0d4003c480c3d010002c90100840c1c505144500322800b02074036103c103545000d42c00502030b0041801421240359940d255941b041d1001c00c40c0340c01401c00a04140c0c1501c04c800345c810a03080e0708540464000b0001c0e001d0401c81d18080b100003001a08070881c080c00d4446124000004081000a68031300310340078000e4603002d540420205024600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 554407796 1250 554406546 554406569
    0xf0b090c150703180b1608090a0e090601051806041a041d06130506060112060521010510080d050a0c050313030c060e010e09090f06041419022404080304 67
    0x100707440c02a00c81038020a0752100384e100f840c03040000d5004a0220f8010050009295165407000d14001c1c000e40140c15580e40c001c1002e0102203010001a091207018260710803c440d0142e989400b0400c640d03141c86a80954031040c036010a9150a051704001541c00e40e4441030624030704640d001c10210341044100c0420420380419401c002c05080c820030760000101101032a83c614241c81765580d0320b5001e001141041942d4412000c00b16040c0d20032130141100611002117008428203484000f0b0751250103442651818010404046840c04070500300c8503224003400805860034010342d07241d04280e211005010403201c030b043c0080e10500082c45150040103207007225a0540c00c10071800c0c1c6030354028905014070303542807003100d0780c1048081d1489002211900400d95503501c2c502d04000321542e03c0c3d0585d1094505110030001c580e8000826009041e089449007040e40480603280040e041c0c010790400d05036043c00001020500c0e0b0484a4117182894602e41750b580c4550601c0e541c4107600c0b0102c0e103078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 554409046 1250 554407796 554407807
    0x210705030117060c030f070c0501021c0f0203040c05060a03090c0825081c0504030213050a0b030d05090f030c150301061d011b0c0816210f0b090c15 65
    0x40d11400c2d1061100c00004040394a400190b0032868400038288074103040307106000070611807203040c02c8260030341d20100035502d1f40754103543c440340c4440112100c01c1d298141050900440580e2080d04c0c07107542c015140c01041ca02e810103100e201c1c1c0c01303d00c0400805841d0034a0030007042012043d81d00400400340285100da03811034040c80e007001d2680346c0000c10040000c04120302000090020f04011540003460760a400c4820b09a0725480346500c02074000560401112080700150302092040b44284401d001d1040c5402c20152142800e00031000454014407044e843c070f0400720110009040e000e4120780580d022031001864914050105440b035000c000010301009601c62410507008580b051141c000344584000a407504181c5070122007200606465101401050f13101e040050003540190743d8282c0da4a00501142e6100340100b40c0c20a0700388101203c0c010300e602c2031000180e000380b07050f403c1000070b43c4d40201015024080c00620b00c29000e040000760780e0b10480181e04400082c5490351072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 554410296 1250 554409046 554409059
    0x1207021227060a1205131406071202130315060801090b180307032a060218040b1905011b20120127080c030c0c15090a0b2107050301 58
    0x141d00c1c26405000d4a41401109841c9800190410000020358404200b03640c032045440762035001e058002d460f41c60442c50366600c191000c07a4a0740a2000e40d0f03a240c18059074003184000781d03c81c401481d217501c140000104041060800c4860f401c0b6112903011031865a0b542d4143e0a440819900b40c841c00190f03000c0c010300290b00c4caa90601801c82101840c04c1c110292006062200b289103c00c0e9011800c203d008401b02006201c034801c140e00180440d02d49512030950104401410040c42c0100c0c6403038540c2410345840c5421101c600c80800028004900304001141c00c2c481c2c40c0d026000301107022000c80002006140e24a2042c40440011800c0048440030058510f050200e60f502c140d1400000385500c0d001e928100c81c100340001c1c003440403010540713008079440c456220414014040840d0b6044030880c0821442d0149800b00c0d04071386000d407020f010078624411240303950350058146004101c3d11102002800c1001c91004e92401d030382e40d070041c540d040030008a07000c0000680000c01030204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 554411546 1250 554410296 554410357
    0x18030709050610180b03070c0209090c0307054e0307021c0c030308060d0209040507030515070207031b0e1e070f0c0b1003050d05071e050312070212 65
    0x448149243c0648034104c0c42418400d201e000f80141052014008005601039024845559689030b01421081140c07a1600c400f0303840d164480c141c503100780500317500060700b40b4060a0091140142c40c100b144031443c4414071520001c011140e445415201c081520840c4850b000b287e5003452141c1d020710340e6031480e48104050b02d109aa00a10040340c481d6880300030030002e0b050035050700d5042c1445501a12002c001507288800208000e40c03000041d0104002c211010400c001101d10403070440e0040d00c0384131421040014100c0d40107006900008040000c904082540d9494002510300641d0040d10f900300c1100d10801140c8101484860110400d903c42450001e1a8090403519000203a03601110303004040b4488817401400300090340012502010081c2d407002c004651050407a1018410402c0281c51500092000d80f00701401c007040f42d10428904030304801099100c4091031a2a030003500402900e2406012401103124041065008c212480010151030000d004040881807810b10409034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 554412796 1250 554411546 554411569
    0x3050703020c060411060c01020f040e0c120f040206070b09030304032c0103020d1103090f100605090a1a09070e0321161106070b060f030a08040605180307090506 71
    0x1010701c10420703101e840c0c8001c0345035904154010028000070711501c2c000340a5000d10400000d4a510009042100c1d41e1030303000600803102440003001866448001042d1309000702c02e202c400c1012290001141d0b40b45004103560b02ca4401007034035040083e652694160700400315401c0015903c008148824590070a800c0081c440190010250038aa554803070320b280400d015003181810303008a50411815444c0e0400c0c0070350340040f11101e440b031406000c1140c2d00c50708142200200d00404010b802c81440324002d0742c050f07850107020161039440f0904844000e24502e0310560300840f000c0380c0c0288540e614054075004d5080c40d51018075a01c0000201420a840513040318951103c205003103101c03100d018181c41181005201c5400040ca1a0810422484002c25100da2002002680c0c104004806028a001d00002d0318143e103038101160515540728084840a00071030030500041207028030440c0100702101803c80c0e41c0680454480200b40b034505603402c4960000e0710784042011900f840d489030301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 554414046 1250 554412796 554412811
    0x806130e070603020c33010f05010516050307051c090b030609130c120b0f06030105241c0807060b0a0605090d0c050616060b0f011d0a08060a0c0305 65
    0x404414108900c0341d4451a500c01c86051640229108150f10800d120610844141341c2000e8a84d206071104400000c5449a404003c42070303490000c185442c501c0d4400d010740314103131113162814003100c050f5104049481800c49040c0303c204207140015000b0b20580f554240c5107201480c039004480c0c80940845026005191110400e000300f064940ea04622a41c01086800b0000041445030803c00840c800c182c00414548042510800070444c80d2213042d0b100b20800051003000e500d0740e41c20142a00c00a0314154010446440d04641044105028245030a0b00401c00d801260300c20308080c54181c40c54501781c58074100400c5400510240340a500310300301c402c6481084082c10800082c1c154020721030b019000b19141c13881c04042004858640b40588401004d01e916001d5501c24003180350444c0004507251400c1801c4a04e04d0709101c203002d42c0d03903203050b168210400007648401c00448050320655921180621000601050030f002c1c0a01450020750049030036801c062002c2d041e40d07000790201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 554415296 1250 554414046 554414051
    0x91f02010c020a0f08070303061a0a020d0c12352a07080d11041502010b031605040203060307150c14072706050a09020c1e070608090a12080613 63
    0x3c0010104000c5150305036012840790303220100d5050440042441d504031600d2a44001400031021305003102400700f055040d42180c06807040030340c0450380c500c03007888003c200c42840c140100c8814090706082c5100c03264403901d24201c0605082480140c061900c0800d1482008410b100a44100c20607410b1541c001a61000e2000c0700300c14020400d1050001c042c108920104001e01b40c40301941001c0070100c0510041526a038a800c00c2c004a40801094200950302e41040000c044c180801c0b501c603420001c00d503c02e0031030710f04414440698402040742d98580520400800c50881a2500a07003882c640d9480010390324440c070f040000ea141710078000016600c800c40030003a603074000401c01740003400c0c005054030714410b85c81e1001c0500380700c0d0011030f0311160f8000085644440c55015018207030170741c802c8a0707006800c2c030702d0521310b800e014203041c0d11900703c0d41d8280f20040c01082d40b01c0c0c0007030500d801c6a840200c5611002640719042d103806001030040d0040c032226250034048801c82c1800d01004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 554416546 1250 554415296 554415313
    0x3030e1b0418080f0f040509041a070e0108010b07060207080d09140106080622021210060e04020d111c0c03020103050718090c11030705010b0411070f0611091f02010c02 74
    0x842545024a1130521030411001500500100e050402d0f04e004020203003062045042510b081c0d4090b42c5c0c85003d42510b404000c00154945120b100d01c3c0d02180703010307103800e11981d003019403480d4160b10051095a05903001c102000c0042c0e00c810080003402400900003502110514211804084004084415030305144041c4151000480c605030043e21048020103007081344060783c40c0510300c0b00030103548a421000800c0d43d402000c01c1407410814960340400482ea19910811410b440649000e90000011100f807000105103034105005814024000801c0e0600e050303001140005004007100e035a03c0c1c0c10010011560103024854200030b60f070034406a10003541d56500001802c0703219103d011515820080300590240b540f0030724030620703001502e549000c1030a01c180a8240c0542d09801030b403400c04035546c0d03035040f0710030340d041c181d0300080c050402406512560302400e2800c0c4554002481040340001c0d903a54881141000d0920035000c450140d00c188020342120100740800342550881160f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 554417796 1250 554416546 554416553
    0xe070b0f0313050307140706020a0b0408070606120c030605072a02011e0809060c1e09010e040c0c1101050c030909041b030b0117010903140703030e1b0418 68
    0x19920156942155162242c1e01c280085038060000d540190480c08002142e205200031420151030880c6203408031030080c0c0d41c80f1822681c41e150890094a040101e0004c200080c44060003011818000c45020a0094841c06000d801d020078200c200c402015124041007009020300500340d000d1050f0800c0b07113075000c030250740614a15500503d0003000c50341070b10240031603004513501d00149000c2208804200750b056805400e0080c1a5141c0245101d000b000440105e9150100e8800201f8405039643ca0503004035401d180390400349115060000d00440107181d500c45200745d140e621100e03039071040e08401c1800c00201100265000604018081100317030040c1d1000801c40e0741e00704065038000722654031810300f05241000f2811600220407861000010721604000340b60503a52a0041034424071028840ca500301d0702484002030119402003000402041044064030030b1501130b040200f08060b20300c0b01d1742e080507801449400d5002159810140c9803c0500c601c55110b06903c07003900400e89544c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 554419046 1250 554417796 554417819
    0x10e030a08160c061d0f03030402030a08130b190e030610061b02040f06060215070c030309020f03070f0f0b040e0609040c091103040308070e0a05060f071403030603010e07 75
    0x3403110108201403071142c040144284204801660030140420044c4140710512070749540941d001c0c11688581d00001504140202c00c50303000301d40c0100240b44958036940c518a1640100d90408840040c200b8001500c410141c001c11050710003000c0050b015102c007802400300c140f943c001034084c0d40f250b8200f0100d507103008600402d6130010b0518108500b036460711a84040350510009400501b44954400d001c16250009800d03280c040d000d544140c1545121000b8150048036103000042c02d02000301c0200f802907129001080c006030000070010200d1001c6460805558070001502d10380150410561b101004a0400303407160211041c41c240c54600c228a013908081c00042c41110000003040400444031048030003400c4a0301d060003000e400c400d0300d841d50342080341c090f40480c43c3c031070024086c5441420408840e000060803803d115080c4024010150082c0e0380109103060200f103681d011034222a006801469580011641c92a14800341420344514035010b0456510018040c06220030710b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 554420296 1250 554419046 554419051
    0x14010501051b07150801080325060e01020c07060306080706120e0a020a080114070c08030414190606031e050d0806010311031603060e06100309111008010602010e030a08 74
    0x91810076112400024481201d550314266001c0520581c0c000103800e400b030598803111305074161981429a130741c07170148030303140d1044004070200324000c950300342088464100740a0580e8000d03440041d06150b081caa040c01c9078011000001c05a0004d901009483c2d410b02a0b4006040d05c0c1000d41006880c00c1b501400d9030400c0514a18a030381c956108000c3d49408021420b10180c0041c400070b210307650398804600800c00010903000cc1019a4000382c00c450003410803142c80d81d807004c1e00d40e180d0740c0c882e11580d118020302e030784001c89405055021110980040141c50b405d901590f400542c582c59480c25440d50580c41180c0441000107440c00c1000c200c0100c1d00380364141c0203090100c00d5503285030048000307043d0b40004108943c2d01006005250ba10301c42c04c007286030301c2c4d070300d04002145d03c03071810464640c0708841280d40b041e08a1049402544627412460034907218040c210308054140e0b00050401c4200c119200016655a0041203011707424040d03980b03403100d0140a140380141d00312006001c01e200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 554421546 1250 554420296 554420299
    0x2040209040908030c03040302160302180615040b0a08090a020927160e1807090b01030920030607090e0402010503090a0b012d0b0409110706050403050306010909140105 74
    0x424461203688480d0010424154005903040c0d9038030780080c402d0001d0b0404d0750281d0040c4a801002810300c510100c59a00f580c1e0014a524404141c02c0141221420018603450b00701156000d510100c1e0020005000504140c03000302d80c0321015090300401c222401020b101117036001c0e020b54405600c4a035440c541082d0810000b091482e6803040e0040c03030740314600c850b000070b100e0036202d000d08440180c017030015194000c400821503200c03d9000001d540c18000d40c448990070454080080010a074400001c1c52818103002c502e150594681074458a42400b941c40b0b00060128804428601484400e80c0514941090385881c3d0400c0000030304080018002418402e001001c40c41c07410b03003001040f0b1172076441102c80680e03686428505580c00940303155001d4034010031001d4a01c0c2019200e4040603150302d0246513040514050031507010b4104101d4035410440100030002c0031500c28051544103134080e84525a60741061000181040341a42c0180303c80e0b8648800d114490b0000030301c03541103175070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 554422796 1250 554421546 554421551
    0x1103010e0c0a0915120c051c0308010b0a020c0303120915010b070b0a0b060711010f0f0806131d1b100c0b090316050c03070e010e041407030f060219020106050d0204 72
    0x9013030103100c61050311038000f00c2801621980c80d004200c4100e001c4025180705440907418002030030b1541104105080005022825040042c00f9100c04003014202c804210304c1254114005000841e0855216000c9d8002d112a40010821a0002048600c81400b07001e03072080c520f50300d0300d00d8001c050301032940001e001110200c041055900140c0191403e000d00801e55540d50405203070030503d20002001140c00f255030a0f21818203a40122101085a50301da15074070000e0f502e040c100018144a1803460210541c0d1ba030381016034440356504500c98030000d03002480002c441d01c02002e181c80042062510499400c4920810340741d00a459079030166222103030608903201c034100c2500b54080c00e41640401040c2c06603440c18044c000540d490700c0c110a80980324880e80741c40d000d1500601c2402410070031032a4801280016000020540300c5048001c182c1da102c9803207640c0c0a040300c01410341a80d04540100c1d1010710100c41c000d18284402d002e000800ca95860b0001007010a000310724064071032507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 554424046 1250 554422796 554422811
    0x2010203041a042409050301231f031b05100c080307030b0603131a0f072601090615031b0c050c04050406020c07090608070506031f031103010e0c0a09 66
    0x4440c60709443c041d10894030000140c0c810f001084c074198440c1c0301136000040e1061000211404c0621520781584203c071500541d101c0150380c100d16a99014003d461070344004003151030b4066400d44418040d41c07185000c0f401540c40f41d400800446001d4110341d00c2094051301c04008990070050802c61310364020801a00d80da02c0c014240c000b0076038500c665403c81c400004010454402c8125200524071450315141a1b80c601f881004008008480c243c040a10201c041640c09001c1c40342030b007101c2d43e404803520303181a10500006401200703a00ca4012240c4448007803242d4014650222010032980c6001c0100071403c02080c244992900001c2060104110316102401b40501501400300f601420601c0942441e280000c020344c04589010640d004101010503c03071041e0141c0d80850307116200508045003448200030440d44003404508500c2503843e203694040170030b400544001c50295403250f01102009041c10b0a449900900420b01d8009240108013507443c1c00c4050183d0f44105400203162 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 554425296 1250 554424046 554424089
    0x504060813060906020c1006050306040201110316061a120d0302130b03010f0608090f0304050415120b160327060b0a1403070f030807030e01020c0a0305031e070201020304 75
    0x407031a54405000d4505041c1d04009000050b002420540034550032036119001c9042203000b2505140102d0389c3c150420700218000d98802c840079032030141340c40d00741c0c0e160921122000e14202c92409003141d40b591621501e0400701070300080188652015141c00c1c240962601c4442d4507107080d840c0d1941811360100c0c050700140c0101c1070b8a405480c404210700d9481d40c46d85060002c550440c42810001400034000848030840400c07038002001d807250081d8145801c040411000d803040700c030600c0b281c038500d500019000c4000c014104d26a80a205140201c0c03c100708182c0c000b511910900d42818100941088040c0100c01d01d084030640001c1d00c000140c10510b001c2015045603210180e01c1044c00c200800c801c07410101001d5898002c03070071910380e00d5844c900020001e000780300203400c400c024400c0201082c000c01052644690520680c0d60b40c100540020305006850342040c0d403e07a00c003142c2072003009190591041d81c0d1103070034102c5052841541c0003c2d80c0744194024001081501c1840a40c1c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 554426546 1250 554425296 554425321
    0x41a1003051906061d1c03080c070b0f0a0b030616080405010f1103010906122004060b0c03070201030b030f0a020d03120207060b040f05070e040c050f1617040605040608 74
    0xb00165140a20406136142002005485118a900784400383e03951408240d10f05100e601d00c0b4000041e40f0380070030040360f0318103903405040140040c40001040110600046072201d44034810740301e07076002c110b0700d00341782540c0801c40300380c0304041e03020f60302040030700c0000c3c1c003812a14680b420f01490681d449549900e4290f02528500500700000c41c1402111800c28035040c000d1410389540b85020061a80d9855084155011b82d480c003511b9118418129221584542c001c1d082640d00030f04089489540e031034248440c0c5c3c3c803400c44c1101c0303504089034007021981d01d4041c1c401304007412001411018070465a20b5202c60300200000e22608494183c3c20802d401404540c26414002d0400c6480e44440e0600c1c50160881c203524a01c52454095244041e4140e4030841d8004c48495880c43d40d124051014040100002013400c402e04c1801c0c400d0f00403046288000708400300b041c8e03107075840300400c0b40740c0300131402142c0c0130380c0801e60000c0c002031060a5001081d5403c40e215450708417800e840d440000200c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 554427796 1250 554426546 554426581
    0xa111b011116140102040b09040207030e030a05011e15060c0c030c1212110a03110a0204060b250803060f0d1202061005041e05090c0603090606041a100305 68
    0x100060040b900780b00c080b002105100c900c41c042c00f4030084460710300c5941800c03441503009500c40e00c2c40901c41c0d0324203810258044d2048501c0703410f1020484400400003881c145c41400110307410707034403080800b02c03140c074040c10500783c0745400c6c50030b00504001001c000d0b101c2c1d00a024450070401d06610108c240400c00c1969070096410518000d0303880c0c0c5407000e260320849542c40603101500b1818041141c4c5105000c21400881003030003601561510b035408441c1c41d8a1842401800d10442c0d480402581e84c0c0d100f0307000100340c40d01a180d624450071100120442c0d0702c125845808a800e500340010852860840e135009400321a1071300f020303c6003400104e138880c000001620714107000001e242840e4000400c6030003411344240480d0501c4e619401c04c4196042003e8100701d2455042c0e0fa81407010842c1c101a412444803c1038a025440100200300b540d0421580d0800c5c80d40100244100c9090500c5a58014810780180c0c403003900c0300202280410801c0c000d140d04060b9644005000c58000401d50355 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 554429046 1250 554427796 554427821
    0x40315150303030906050609090a020108072c120105160804021c080a110706020705150c06160e030d080f041406070c0507121205180604030c06080a111b01 68
    0xe490380e49900300200204a070840c02c46038a8038160104540740380c01b440301480366083c04000c041021450740116107a00d4058012070512045060851038800c100007240c008405403007101450100b40010003014241c88141024280d2621052100c0341100c83c00d40c024002407410314a034180c032140301080a44080c405110201258404d5a80c10490040020989243c140e039520380c1d04d48007681c4d2503468004510a01c0b01513440540204000c0c10000220010042d00d0110641090410750b0f4590034010121000c07140842180030f00345807103800c246c3d41401207506400822070712091500c064491000a401001020803580004040240c05159846c2c40d1034044190340d114248104041c124042c10041101c00b80108140825107083c1008092002600b10a404122480c050700c00d68503940030200c40ca030415484680750105441380f50050000b58410842e00320000d14000e03006020400140204a441d07027080440007100f10b085054038224001c00e0340c1c4102c1401d121101a00600e03030880000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 554430296 1250 554429046 554429081
    0x1a0c030f1b0a0903020f031f090f0501090309060f030b0616050f070f0807060c051009170a05040905010e090c01050306031005190e03030915281a04090305040315 71
    0x1201c40320340c820f88a0003124400c2d00e03541103121405040580301c1a03c00c4154083e800821510303150346280b43c110842003401018040e504400b2500c600d802d60380003640541c04201300d00ea040181036401303408449011001d2804201d8403001e2400540907101d0b03501014482450025614207015050103140340040960045404159841c62640c1b510034261242e0003450045800000d0038030301030b50084402550050181000110001503c3c00811106000707540c00c0c03600284986100000c0d900815208800d520f0707603074880d0318002c1100240d90058110b0807940c03440c0420f005c4110b00001c1c0c1034024900908200d0703220364908011034a02241d0030f240e884402e04010900c480d407049032403c0a03d0020741d650601c00c00000d03500c5559240b1003602c0800c1c2943c402d00724403412602840c4181d420110380941310014803506800140d00c00d100c040d0502c4a076680b91201c8515074255082e0b550144401c1c0c509001c4543c058038050b0450189200c0606030031411041303010307a80c1c03265008141d180c440c0c1911 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 554431546 1250 554430296 554430307
    0xf1e060a0306080d02070503010c05130302130e06072109080d112b0f0204032303040e040506060a051c031b0203071d1e040201030e0c03191a0c030f1b 66
    0xc0d541c1d61b2900c1140d02039442d044440407a1489281260710f80ca5103241c0c1c40350070600d1070f82408803d50029030081c204903a52010b05010882c28480380f4083d0402c2d9030b858030801030058100380c980060700d0341d0400491800030064005000102607403034071040c1d051b000406c43c0e4143c035044c00900c1512a54000a546078200b488060180d2f0b032141203110f540c900400135201403816801c01c92040d404080c0404c120ba4030480708d10030001014120058088046d2424956a207000b940c003104240d40403034217a0000010003140741804c0540c98028801256407400c0d1140c0c04080d0200750030b800700080c042081c0e858482207030064000510303002d1507000d801c4500320b40da20f81c200700d4120091804041d0345c03c01640800c482c031005c100440c4019000f4007800500e52a03590054005240c1c101c0880c0c498052104800034035901400581002c4545291180304a90a0721b0070190f15486019924002c49190052094010003201034a50000040c4e100c0165078894441c000c00c902a4940301d2104000005413 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 554432796 1250 554431546 554431573
    0x3111804022e0908060f13150204091805191502070203070e040308070f020d091206091403041a0705030a08060a0b0c160602191e1509020f1e060a030608 67
    0x83c0031084a541000b0741c2d00548510710140740401e015924503955009519405000c01d005500805059680310001842c1c80c1d83d81a07403000340c0d510396100b046001601c6140d18107005081c00050446c1100f038120021080565070742c1108035070712030010f5180035808600102151400c215420141c521805000d110340b406140003442c0c840121051000244401c1a82c0c00440c000100c1581407030007a183e44401a003031507182c031074458443c6025030300540c486903220085101d1010a8504880d040d01450750355041c0114403800c0c0400039425041c4000412580c0003207940030054601c00021890107845079104c45000540164507508400c0c02001c00103511100d4050000b01c5408031a045480c48184541d2500240e8882d004013500141c005501c020711000254481c16446d0807008080c2d05a08ca10002e40324075001c512078903804200306aa8000510551408505050401e6004c844500080c4c0c1800707034200b42c41900c0204180108000b0603440707401d40c02074024201030803001701180e120b103000f40d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 554434046 1250 554432796 554432807
    0x20070e0a020a03060e0103121404090203130b1302060f0304030c2916120506150a03090203010b0d02030307060207021314040c050603010b160204020c0111030103111804022e 76
    0x78942c0003003403400500080b01443d0344555412a0f07002240190074042c1b502e020342d6030010003d628807801204100c0450302620131310186000708000740c1242e80000c91442e00302c40e0510054900c81c600b9120080e010300580d0f6a5040b11034940c2c0e2a07a03800e03217a440f14a01500ca003e0107540061080804050014800b00b580d0601400d0a64128245455845400c2e041c24540300d00f6154030001914900404480c1c107240e00500c0e0800b2020b071507441c0381c101d0b961862140b03070002940240003a45402e241803d5180034002c550031040c1c12140309000d220743e5400070342d482c410b84000038000341c0c02040000940d0341c0c2c142c040c14109881c0c903041c00304684045084804440845d8100d95200d1181c8000c1010304100040d40e05946a40390941d180c1121071582000d50365481200300d90045c4c0800500c060351100303018950040c001c00389415200d50551600d40303250b200340210540114042c00030031000300031344481140c00640581d41c41e02c100f0510000c2c600551a001c00d030908100080c10441519548032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 554435296 1250 554434046 554434057
    0x40f0e030a052706160201170a021b01110a0f09030f0602030621031e041502061914010501030207030e0405090706020d020f0c010e06040905010f031502030720070e0a02 74
    0xc84158078603a0403c441c5620240750301d290305402400034032001c001c0300c0010040c03c0301e6500505100078104881015a4413141c1c085070158000e50b0080740d456a490500d101002c44140360130020301a412801030001c04034007810f40502c1c2048808030300c103802240680d902402841e0800c81d07015103102c0c1da0900d9800b07540140e40725809146007803c00740034020942071f070b010b4044040c0041c6140200c0041c2103062040a00d03800600300710708200000c0c502401840c11400580960040c4c501840d00351400c01000702050b6505c28514100112b070034045d940010182e05580c4c00342001601e84e00641400c0320448045817445820600d40400e0040e903150000342c10045490b240e0864886800e09401280c68903845402c40c102c2d94440343c2e5090843d809500c143c0c4c141d0301c0c0580440e00b02a03a5440ac5c0044e18820ba2002d00c40b124000400c0c4140156080708602c240d04009040d0714504200390001c2214814911300c2e400d80b0a500e24480d203009052059400404040400035510f04000d1035020096115 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 554436546 1250 554435296 554435317
    0x1e141c110d09050907020f1e0106080a170a030e0f010b03060109140103060203061c03030615080118050408130308030105090109060b07080d09141e010e03040302040f0e030a05 77
    0x5040a40d06030400051408140d03586a0311081c4051405081c000c021801411900035070040b00d44003050400b040000390b4950b4021641e610b016082c0030f044030f003100c3e02a00444c0017034105100c410041a1155614140d9100c260543c950750440440210018604401d460b00d0602070a01c0300d48182105410500d81d540c0105c0030b40e409641e03144440021246011401c0c00e071701d0030030001000410240da01540d4040300c0600800007000c0b01f00708400f0030307004441c1e088011940da40018031901001d01442c10011305142001ca000c2c0d41400e003401c0c2d5510790383c100600810740303541c0050104135200064138291020b0200b00d410480e00c0e4030700041c95030003d0044c0c0d03000c0c1c1e445c0e0000254a01d05405003078210360b003070a02c50b4a80841c50b268040f40d903200d0084698840d0f2100c111400090000d0707100f514160032880501044000300080b0420420112030305040c503030401c00f03c80000f14011080381c0850754115000503904000780c4008001d043c030004a26240d01003c1a80c0401c0313500003004105003441c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 554437796 1250 554436546 554436557
    0x70e090303160912020d0f0c0e07020705090402090402100e04050c0a020606030a020a060f0c150204090e0f1b010207080601090606090b07080901262508041e141c 71
    0x10300101103911400500c541103901c3c1c001c1402c4c1c005410448980c881c00fa006541c0c41162444948400c2d0808810f83c1c00005c1465101e000c002010380d0501c003c4c2d010702412551003199007426000a4100d880160019106d211440c2d001100b0740e01410381c601c0c1007807000d401030045180c6a07c0d400013a410880b0b20034058001c80380002c10f0761602069000c10030340e00910004200d41803800c00c441e000e85a07140310341441210b6280b14041021010940790b01001c0320005070b59641000c48600c00d48080c03403501d5010b9400030b11340300071300750011450410300e16040203e4060205d4a20040b403400e1103680c4415841d0040a00110780300415030851000e03128161201246141d4034009103003184507004001c3c040b1003083c4041d00c01ca44c4561034180039000440000c002d444511a001c03000c002081e28251101041c0d849454460704194080c540f402c1490b0502c82134504c2c1c1038599054540d520f442000004c0f44490001003040035008542d0456410b4504640d24503000c0009842d100c046421740101090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 554439046 1250 554437796 554437831
    0x90b340b070f08130b07020a050304030b04110f0d02040f02121e1b04050105030601090314011d0a05060406021308070f081203070f0f020106210605061c0f0302070e090303 75
    0x42c0107100300c81c000c0d144202082001c13101e80d2198110b13004060102d408600903512003902060b42040a040074501940c0c082645051915210542c005c8241c0c4040c00782e0341e4403840541f00e81e6064070301440c25406540224948088030b601800030710034000c0d81d0340c0103101c03407081c05000204808002a80e04110541c11b0b5a42c4032003085607400b104003459120760003000c020501c10381d4845d502841e08104107040c040c0302641c89075900240a41032521165141e0754903140d0000101e01c0902d034480415802c4003801c1c1159150b264035071580c82c000d0014000b0b0760000b0380031031000085001d80e0300428410083d1040180ca80101c038a54021a11620341107126021034003006018801c2180d0045003e0703102c1400c2c45484400944030200701d134050704259566920300066000042d030341030101c00504140c51211400c24a0080101c1f680640690f0040e04050001e5000d000421081c1c0180d0b900b107007041c04003c1d05c902d0704034030700340060304054900c401401c02d01000c104004091806000400440d54405 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 554440296 1250 554439046 554439077
    0x30b0a091407050f041403070504110903062a0f070501050403050c0606033f19180b0f0c0a0210030203040501140412140d020301060905030d090b340b07 67
    0x82c095044d0002c0d4000c0c1c1088208020f1282043c0f805402030080c080e60800c9035110001003c680e0041c001c030034039980008683c0000d16062002c80d500030b103070802441c0303e490a0480c05280e070b03180c40081003000c8800920406600703241d4054508240c3e101c00240400c3c5407910f801045a004469084068442ca2020544901c0c0c0466003d040300c07074500c044807920001e410940c0303074040501880035080404000250380800c900d4010a4416401404405000c4042c40c0051183c841014441040100311409000b880e82d14012910801049200e803600d6000080d003041c10705c84d20300320095100d2008c0a81c071080d240c154000d107100d01d0013030008214413440b088004a0040c070031100201400c04001691318424002c2c080480e000d0301c1c5412250400c607a941e500401c1342d10030b811510228101e0301c02003155280030026825866440d00d010011709207081711800541c054440078105641d860141202464010041c818110030205503203241003c540c141503640321810340785c050010b00b48001020f0360 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 554441546 1250 554440296 554440307
    0x10e0f12030412080718140a050102060c0d090c24030506030309010807031109030f030909010b0c070b0702010c080307090f060f050315040b1305070f031a0d03030b0a091407 76
    0x242c0d401040040e107440c00003004844490006100c0400d105850611601c16013000003881c010349500480000a004803600b00030800c003566000904550100b02044034410100b01070342c410071034084010070503402c94a000080b0390441d0b0415040b100485c210b2140000c848001c6000307401051b03c04110316201c481c00c5c591030b841400203090100d42800003080034148240d01c0b01800766a4204150305112020000900300011048202d40c60380c408103030950180303006c1036000d004180300030f00545000c000d1080180c55a9241c07140c0c450010022407040d003564019028402a560b0086c00c0d150b403407038030b407030040c14410090050006490102d08045599801581084420040340c1c8032503095036160001007101d1400400e680e0340240d140c41fa491210b464500100003408040b00000c82d1a180c241d100501441d88244003004150034503d80303500c017031030719040b810800e4410f0303512005040b400e003000d402a00004c03100682200980d0000514a0000e0f844001500d144048045443e19002012240c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 554442796 1250 554441546 554441551
    0x80118090f02010f050c010f09050d0f08010e10090e060405070e01060e090a0b03010c051c0501150f020f06070c0201030b0f090c130909080414090f1b070203010e0f1203 74
    0xd41951030036454090340c011340d5500b018010fa85401803074282d2543c642800d480c80d81b0210b07001944c580c030010040100c180810f0151404614000f680c0983c1488003e009500601c26020742c00e60080c041545448666140400b50030800424003541c1d10b40c09000713540f80c40c1101e043e2114051680003080d440120640355048400c82e40d64000040c0152080100800c80500080e900b01e07605e803818ac125031000e0080e40c180c1c81403512185c0c1c50703440b003413201c10780b0709405050744001a1070700b40140880c140d50000840002d810b45032424201c1403454082c0d00e08000c01c00b040180e07210b40003c20480395807000201a01501c01c0c1c1e401d0000306060301c140540609180359040c2e0006d62800014541d80d10f43c03000e04454000d90b406400400da03284ca00004458081c8425207138100c00090521504035950a5200700b06802c0d02d500003245030441d00d400491030041e00b030840c000c61203142140119084001e5403007280d0010000c120304503c18140658990945d20060102e0042d030b084a0008038201c0141c91 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 554444046 1250 554442796 554442803
    0x62c1c050f090303070b100e09070f060323090c0a06051303060e15010608010306050c0922110c100e060c1e04030b0f1b0c150603031908011809 63
    0x1d041010010128016070840d51403035405210038010a000700f4091040d19020300c110790540780105080c05a0404546030042900ea1107622020017040200d5014030341004a400520340004c80295008070707400b602124450751b5850500310b2042c009503840104500300fa0000c100c0d0316800403030391864140c0307050041c1c65408222190740d0340d0420220300c070350b0801d1071485590b2050710004607800c0341c2c1181103032080c1c01410001c3c61040040c02041424400c41c2e401c415011081170800d513482d000a0250b02c0011078010082038103541c003181c4843c50740c0004403500031030b005042d100c0d80080051581c4080881c45038404078103080c1c10489840c008600240203103440300b1042d02d0b0444014038605421045902c00c03180c040300700030010100e180c440e0b481c5e0144010504045c1581011251020a41000302100300000b10801904d450000002403825911140d445103101c00c1d0b503000e00003819400303034902e5091358140510022100a80c004061030585050b1420703e4210802c00d818407089654250b0000d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 554445296 1250 554444046 554444057
    0x1908070b0f04080601080f070b030c09011d04061d130c0312140c1c0306141c0812041415010b09221e021e07062c1c 51
    0x5000320600d400040a032812403807291480e00780d60b14003482c0b90082c26800f0500f20780004281d00d00360201402450001c1c030143c070b001030550402000101191103840200c0e814002e070080070f00319038080d0102e020121040200200540d40e5240c0124414004949014a00702d41c2140020b5000f51401c4d540030b4000c0e00248042103c60440d07540c0d4281540d43c3c8990400e02049504101d24a005440242401000340b070146c411400441800b1072020001c550000074103082417018004502c1d4581180071b0100c7c2102d000c4070049081003000e508000360031010b090070f4000141280c2000d81801d06a004a104980408954500481c4d40c0d8032401c010310943c40d20380b402001040101401d034050000720300c0040c0f00c0c0000c0416000060302c04503e804104003050707100d007010440000e805800090741c111a01040d03192000b20603400d00d00406040107500359101c041250b10601100341c0c0300d00c103079202901c6414854074694250030074001d1501030101144c4904165244011003650701411002160323100c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 554446546 1250 554445296 554445299
    0x140f0601051c0f30021c0504091d100b030a03030203180a0303050a2403020105031b040e0a0f0b030615121b0f03190809010c0b0a0506190807 62
    0x20807034000e1082c44084500780302d1041c8040400d500481050b0031074070803030391340e102240d000818080c0c0c1204c420f00600030084072007400c1c245a07004a480508030003003521484d942c081e200d10a0303481d40101c2e045516914509207807443c0c01200300e50000501900841101c074011044078a00099900100782c0c01d4140d048072460b0000640030b50013440d04240f01407403081d080d60034462228a0580c101d00c050340003a0b120800c4c404480342078421061205540601d041c0c10140c1051784d841100340501c8003c1c10410008005000484030183c000801491000d60300c1e5555a81c0740071078140842510448007092601104070101c11051145680700b54010f030182c45603680d091102030070003e403040655000000740c40d0185a0b524103000d403840c2403100d80c045031050040d030b0087c4809011078a4005000c1d0b4808800303114410802d40301a82460390107402a5a00e4a401c0d0049410340315030307240100803003070001c02d2010403007103600040c1c070421040c0c0e0b404108107281c1c4142595101c0c0d40c8940b4880c0e8001c60070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 554447796 1250 554446546 554446549
    0x7111507030804060b060316091706010e07050c070b0d0c0c020d0204110408011104080d0c03120c1202040303050706050f0c070311030f070b0906010f032f1c140f060105 74
    0xb21a0b000340035a90014243d415140810b246500494214a100900c443c110010a13000b000550144c405140044085585844442d43d508418001d02c03d501d14070b007001403003007440f030710032110f840f0025416148440d544020154058100c000600c00d6a0709090700250218400c045868030be60f0014845031790324840380c0078400100341540b9600b526800801001c100c4031424000d00f111498080019580c407803030728101c03e0800081d100ca050401032403003012030200e40e0000c48030b011610329210018403002445400c0e030300150460030201d21a030012070000141a00030014011450150105102903036134541240341045084586182410b0148460404284540c150084844944c421285006240c49102925800201c0212100515041000144030081c4011801894400501c521035411039071030680701d502c0e10f40c20110b88114444110416940331b04080f01211014049002a000c80c40d200c4541070240a01540c2c045100c104035990040c00040f030074407009885000e032119909010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 554449046 1250 554447796 554447807
    0x43305090102281e05131406030609070306120c1806050102030a2304030b0118020708090d02061c1d070b0316140307050306010f080f06120a05060c0711150703 70
    0x4100410004a4852a5100b000100221038001c0c89038417110b86070000e40048020758400c0da0080381440140c03070010b00715611048256904014200c540c84005d5458450442c000c002c0c42d4440111004012103042c01d11480504900640b0354500c1500005c1c80240043d00588480d441420f00590080201d030307032800d104001d2002d8000d10140f903201c46050448200030740d1b41180d0004d0f01c1003041040100680c032003015415103076040ca0001981001c07a552681d038010301404032030a00400705d9040c48411555000300f2101c0820340901d42c0507206581100b01c8000308018000c1035600d1000101728594000c002840e00121903140309014690ba498486c00c06020309240400b10910040512080c1c500c1c002c003000d03600c00c0403540e03246a21b038036205000500505446150030288142d4401384041c0c0f41c5600703402d40e4031000982d6200d09808034048010703d4020714050140243c0105405d010007014444000c0c1515409164054944c00b21070081180c01c00382010114400329041140c0c2e00024001c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 554450296 1250 554449046 554449117
    0x1303080f07021f0615170c090d06020a110705010507050a080c01060b0c3007061a0402070311060a1e0509010b09010902090a1517043305090102 63
    0x1403050b1000d0200e4a0224609a03071480740466030103441d0b050070712411741c04040130034080340540741141c140b40034000994030500001d030411400c410005051013264803803c102c0e45100c1e0344568115528008550000d084400640100c00075008100c4005500d44c03080059960103508980074180c900318a0340c440c2e5903580b002941900d103540711a00090384503858401741503102619006440301001218080d582180f001020364504091814092902c800ca0070603684016401000001d40d50401d1800450b03c11541014941c42800052082c04040d80b00505801c49410a4110b42560302d40c1098a800e80c0c10003020031840080c04107504891a82a410103234110140d24000640088076802181c2c0c4004260801d0b80c1031500001c2c0b140a80c2880790300e000080003203608049080c0e08201c0300514501102892030140782408001c41c05010901c0c000d160800403d0708200c0a0302c2a008840042502c000c418140440c5003a0014566020600031960050740e40c2449040c03220242500b00c4820410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 554451546 1250 554450296 554450311
    0x309060f06080d030e15100806010905010b040e060109230f090c072006030408090f030f030405100504090501060c021c050a0b090f0706120b0406050f01140c03040306090b1303080f 79
    0x418440045946c03241c0c1c032142c02640343ea0f0902100da828101a2850404c0c103070711011886181400400220030700300160340945090a0150000381c580d100101e0fa008025001400f920311901010842c004103c22000e96104050b40d003d90401e16020400614513011150280e03028000c0010100007041c110b280380a45440c00c0c0880d401b502c100c00401d106403c205d4088074a41d070001400500c520b0030850f20190b44008800410201c00ba10000b40d4507809a8452903009480078900501d86034003581c2550041c14480e0b00c01c0000c2e69494400610701c4881c50344c181c2c0581d4006804940c01d04d01d5044202c3d5882e009001445034404a176118440302c107009100c1c1d0b0341401201c0e2102220101805454000d180c87d03540d8082c03490740041000200d030000d2440d1803245140c24810000c5845004035003035152000d00b44603401d40031040080c801482003a401e42000d0200041c040200455584829001402034010701c4450391007204800c02c1c0c5180a501401081e0340c1c00000c0c2840100c0540182e01680 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 554452796 1250 554451546 554451553
    0x1b02060c07110111010509030a090e04020a03080d0908120709050d0c0506030c0d05042301140c0a0203070804080a0c12050a0f0507080f030c0f07050d060b1507030309060f06080d030e 80
    0x13850000300e0031641c00341c0d0f81889079000003400481d82a440484600508414040c3ca5241c5c28941d00040001d80c25120043c0151030200d07501c3d0100c0380ba64400613150b50001d01c00c0340d0340c80703a09024401e0010200d8100e808151038000c08034160034004204003280d0740c82040485107500305820000203800003850000115010000342190703070000d0080c43d0250344038224849890241207640d107080505a230780c0313283e142c2c034140e041d08034403e44807145504003020420669a8400c007a01c100c0c190310816101820503180000e00144400000803502d100318010324030640c5071600c0e02072036250300d6161200948564004021900411a40e21401000c10b22920440300182d40d991115820300d01046245603241d000451946040c44040c041340403c0810301d400381040d141454005046000c082c100074003803c0d0b07909504501c5807185106074141081171500c81d5112511860700601410140038115812410521007c0c400e0109000c0c040a80d02628003424030084040800c9000b003481c1e5008111a20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 554454046 1250 554452796 554452817
    0xd060e010609060e21030304051027020a17100b010e01140d09140106090509070509010b0a0203070b0a02180d030206010b090d0c0e0405150105031c021c031b02060c071101 75
    0x1007145c01c0390550b091500d014607201d1602e42440c6050800e80c81444417000c6c10000f80500440c41c0001400d00380c0d0821300241c01e08205400824113102150300000b81d0075035070440c2c020417003000103002c8000c20b1050b43d051014410350001100d8641003483c00c180413440e00240c05181e54400d8000d080400e40f0031100207042184e40d01c55045880d01700704003000603551a001400101200c0c000d82d580100c4a070014254503150402090036404144504040303a240418280c03816403081c01110022604030310400101d0421020b907400070750041c0081e07800407500e52501d111509184464170000c6400d90064480c6070302e0801c0c10700703695025a520a41c0700f00c0701800400092000103450001e400050820380c41c0d03150514104d85001400841b4812340d80d52800104210b94001a0741075202c000c840046108a0b0540016850440801c003a00510b1a500420002c0e80d90305600000c40302e41e64407203141d050841400140d0f00e0306420342c2c00c00788008041004001044507000000b80e40c240c185040380200c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 554455296 1250 554454046 554454079
    0x32102010f0c03050709050a0806070e030a08070c0e01082b020703050f010506091b071106090301050711121608070302120d051501170708040203010b150d060e010609060e 75
    0x1150b00300200c401203a0b4078010b0014031742d44041104003410040d20035009140c01c024806541d03010007808a02008050100b0400984060000031815940040400d403104590701c0d1002c100c00340c60007a45040343d1000700005208030009580f031100c000c075407001d01410804151489035450b0213600141548a100300c0000003c504001d0f28450710400000094182130101c00c0140820000d00420a84844030ba24050002d44003001c0310580e65110f888081b81d58a2403011840034000c2d54940e9a25501c0c00301009141c0e0b402c008418031007884201946d50310381741600c0200c1350b805030701d01003018007400000040018070400000c14201e80130740126801c407040100c0c0d64a05503c6184e00142042c1c40740244000407202400490304500242054882600c3e125024000143d00034070b10030030000d180700810190740342907000141e071a802034598490018040110201580102801e1690b1460014005101900c804440d8140da40303e94070391208514005d804c40740c0602281c5043d600213844007c50241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 554456546 1250 554455296 554455301
    0x70e092208030a1505030312040609171206030d0c0809060c071e06030b131d070602030919050f010818070f03110102060606090613030b09070e010f032102010f 70
    0x840d4072070741c0000d0b030328648000201d0070742e0b401030303001d84580c3c1030428144a1950044196080d141034580c450300b10380d0742c9061000162203103001c09444c200c1d0b0310190012a08154008148005203094601220389601045c1552205503801d00400500440c1c0310b1270001d040c20006103200704004028a09100c50520440d041c600d06600500c1d4072000220010308400b2031500d448000c0406080c01c01c503020074800851105481c04680209a5541e043c401b00c40b4107285040000440047c42100c0d0b4080d101c4202955961200c0c14803846000101d001c00040700d61140d445054032006442411003c080c10019907a4460283ca40f41000402c0c90101040c80410426540200165000d002c3c1440c0b40d1308005144160759070456045410440410401c0e44501044502c20401500c41c141d03030301003080d800651017821b904024107040c2d0041c280a0782450000b00300068880d8043c00c405242d83e01d02d410985036a8510008000074522840500d52080310070300100c5003481d0b40004a01240d04041c44802c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 554457796 1250 554456546 554456611
    0x6160b07180e0403051b0a050a03120f05010f0b0708041e090c0f0206150307032003010b0604060c0305090111030a08070207120807110406030c0b0706050708070e09 72
    0x70301a05407080d070381a180c5038090028119105034400d075040a840040407407061442d00798400030001d4850001020401ca1248610381002c160307100e042c003902c1c00900b8a244120100641d0b4103001807100b11503958810030b4122106545a40701c150b103426485940343c0c10006003031b2203001d002e120010b240341070081c8004030b07503400060008085061461010451700c02c41d20140030405a2801d03030400c0c43d000990a44c02c10043c00c081c10b40ca0498030b00103440c2c03603034a0b00010640d07081d005400308050041c101c210008541100240811420001403040e107024500c01c2100041040c06070801081c0290010010f041040c5091004441c046507481c0c9142c1c8240c108200050740b85081010031981400320300080e1a500403e15558000c40c0c076980700d9802240c2d40070308000513440c9103c0380b45d9a582c0c0610005c40d031001100146650391503d805c080c0e080440103a032070030b04002c00194141e1007404c5440c420452a12106540b51600b4148088101c000308030f22448000c52100050900c444209041e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 554459046 1250 554457796 554457811
    0xb1e0f18010e0c030115080c04080d0c0c050102010504080d050a090f050a020102010e0d0f1413081506011403010905070e03030f07021906090b03091c03271106160b 72
    0x200d03030751400c5154220034100402d680410f44080c0014810b85002c50b40845400c0560303d0b010229840c3e50090598070710480d40020106d104075001c0044594000324410011405820383c03005c0c103542d600c01a0309858045900400342c0008000c08200d900080c0e101d290401200000022a6160b9a030342410042c14240e05481c0703640328590003011503a090045c41c03c108020310150410b0144039001a0400d00d00b00c02c032205200405d100e040d0421024400d40301c00098420f00d81206075900c804050300e50394600d0590803100780510000c2c0e8154001c03412101c2001880c5100340c40c2da860007640100501c0050161400c010201d5200e0240d6070702000901154044404415600c4e0000e10401c404040380264081070f00581030710421105030131005400850f01c03444001d642e641c1d0780307198081c02c15158000b410752600300b40d50110706c01941503101d0000c55490348501c5890454400c0602507101c02d4910003468042000680440c03403c0c04005811511401c0c004c481100346150f65070b034031f0030000312000e8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 554460296 1250 554459046 554459089
    0x13020d080909060a030b0604020715060e010e070203030c18030f0d200a0206090f120604210309050c060f13120b060105032514030a060e0a0b1e0f 64
    0x1000c0d6140402059403c10703011500880402c2c6541e0b10b40e84a008002c4c00c0300d10481c3e0201e810f5090215846141c1b4060740850010012a03468086103081c6003801e010780190000300c0c50004040302c0c000401c49006405030080c080c280b16154140790070101c0c502c440150035005540001400480c100050b025080198035081c1c4088541842c21070310340d054030520041f80e4003800034170000d40c562608994588200344c0d4140301e0742c9000804129100d18034414880c2511400003000140418829405442c9030300c10200c0d01e800c15035003411800d45500703110141c165000048030b061a07140c910024500e0300340e0381c0c043d07a05200c903440543ca0744400d294070101c03083c001480e1000030800d5115003140d116100b401e00b242541003051040c2d82a20f82050003a4083c0400328800450310301802c01a01180c0d00f030088156603181c1500311401400700d600c91022400b0500c0c2c0882e0f441807403401405d48041002d80302041c038203411000268121b00c4d42d60140d40004c09418400c101b43c41300540240300d803e00050f131 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 554461546 1250 554460296 554460307
    0x2120a120c031a010f080604020c0a0206070b040209130b0f07110d02010605030c030a170a090e09011407020c150f040f030f03080124050a030e07080c010801050312090913020d08 78
    0x20280c012060f003e40d070781003110f81d4081e1740009400c90880303504400305407801030300d50a60107295454888803140203503114801003040d004004031910114410740c0300361850f0360b20b03840780d0f070800c2051000c0a500411074415040024204641414000d61100d134a2511480c56180e4801803070401e0812101040184d454078018460360400304076410300c1400039801000400c035107880d06400f1030b060382038540000d400014100c425521480d10000070b00621045440c1034102400054000c0c44000710a8100032990800209000d00204503c04002c2d4080e210070010164143d66917426808540341420040042c000400c5c0c0055081d00344024500c5915050038054207428040c05844050303101124118104818111140b1030400c240400250790520f00e468125544064014021881c2c041e1a0340c410140f00241e41500081d401e50004170a803210300180e42c80e50280f680380c2e00003001544540500300001683d40c2002e42c4110351080c810103113980c88254039800140d03610401c01c0c083e16460300c003284 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 554462796 1250 554461546 554461571
    0x17040512060709180204030602031918050c211e06130f0609060b04050a020405011101021201061803080307090608010b12151201060b03011401090602120a120c03 71
    0x911248204034500107065614101030002d100c0c41c2c00b4024440d2984440160080044554042d00c001d180d2020f425510b903d844103480040304504021011160300704000c001120280b4041115404d8020780500f0200010a003401304108980700c030844405001080502e03070301c0e0140304511616102007140c000c6001003080035454100301801003010f03800c14000902c0020b800e450707041c000302d42c4400040b44512007802c00344000d00c8014003440d04036041404100503882d43d940144292002600c075132607410400c500e520700301d000d81e6203001c034096800d4005028060084d040c1d0070401541c80104400280c40781e03105913154205485460103e8660101806141d030491501800740031400191800c000811400b8201820041c08034400160410740500481e260362000060001450000b0700c10300d540d0315002001607000340321716050300f84411103645180d0300c1491804100c4405600421710b41c115806050020361110501c501406100b140380b050340300403406006044900381c0c80014012581d401c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 554464046 1250 554462796 554462809
    0x1201060e2403071e0210050c040819050d051204261908130206072607031121030c0d020702040e0c1816110a0606080a14060c0711030109170405 63
    0x12040c00904c1c90480d44e15541030750004118124201e0144042110740340c07030300851078511994020004a0043c80ea0200f203030052400c034154254800d00843d801c0000040041740c860050b001030005035012800800c000c26003400303d54030711000304058441440e0a40800f8802c607442110354566201c007506040b40c40076081103806502404612440c25103441c42d90005665205a400090030034540ea8000b003070401d20402200c0301005282c01d041e5a40710702d824090550310035105070b24058030680702d5105480d010307900040003642201082c0c0e41191076105548480d600112281081c240c3e0a01200c0050303030f114003e40d601c51b13082001400c3c0c5d107410031081c4006808242030b902c03040e00a003001d000c40c1510104560110b50600c1c5000010f00400440c22428130780501400f0317088509040000c1840315011034501c00032842428451000807180709450b81f00c0b6001c59031044101000d000041c00b040d07841b403422441c10001030000803541125580d004a1070310903840c2c403070b91401c08034007400941081e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 554465296 1250 554464046 554464067
    0x190609080105060d080d0213050a090e011118010f02010f02030a0504110f060412150e0706020712050a02090c0d0f020a020d0207140d050a0b09030711061201060e240307 74
    0x9846407080e40741d01d03848100c0c046c030901e8410613420341d002440e1200828501c11030005060b008007074095940d91a030203000039110060360740140d5464142d2644401201d00f046401080d030704044151214030040040d00d185001110030b4003503540b12a26000100414030040d482507030500350005d1941817038144a034a804c200e050381c2e40281a242c507220600d640d2501030b203040b6501984070901c9818286480028041d82c030344c541c402e19007451001001e01001003000c80035110741c1d500311407026035941804001d03500d901030040c003650400007646002d400c061404a0b440f68001041c2843c240342064100c0480d0f901c41c181c100019404240010001d50510605000c440c8a00c0200a1035081c9032600c0181080c10000c1031144c03410030240801c000c0c0a1142c6a0f42d41d4000c103000200c3d00d4560b08683e180da01060046414211f0000c40104a280c04010307034180b51042c585035910742e07081c10015500ca00c0341d14407003684a446034000181e80780c141c05107400313000110241e50740c0304d0401210161540089 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 554466546 1250 554465296 554465299
    0x1080c12070f0f031e0f0204020315060d09260403030f091d160908070509090a0519020906010305040b070c02210c0f06040e04112e2c0105070219060908010506 70
    0x298901c00c01b0603401740580a0054048800503035944500100101200c032042c0b20a8006c83e010407188200340391a80038002d12405400001d1035060011821503000d0280c070703002ca001200c01e0006201091160031341001e040f80604060303543e1500c54260000b181403600c03140718a0440803040080001382000d2240e4003060300c1c1131500b40c150601c54450385176103450040c58080c02c1c406002488209003040340c0143c43d03030000103403a003010ba4034000c2180d10b40b2003101a401841c0c0c04000c180d4a52081c4641340c42a50003000100e41134a407040c045442084402e0181d90202284540020180c1414071421440b10054010440702c3e003d6000d0150500d1034820b098800c4505000411024030503211081d4800e620016100315000030358000350101444606018140e032035280e070382c0c40903404407403c01450078840d11081040031030038240c04003038200d140511748140c0000c040b0410650050b40030b0440c5503c001c2c20b480030f0340310700008484000410b5100b1400606034100802000c3d800f84907042e013040e030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 554467796 1250 554466546 554466593
    0xc0e060406020705130f24080c060901030c0c0c1806050604080718022a060a0b0f0105070203010f0e0313090603170912010603050c040e0601080c12070f0f03 69
    0x1d07141c0d019403611010300c221070050401840e6905a4901c5078003490018804100c00c000c0031a041d101c0c2048200d040000c40d08104038294086000c0303000007a10b0b41c00800c010301e081c0c60f1109101c011405441030040319000c0c40010b491040008003800e4807480500444c0b00c0441c018114101c0325000e4a205038001405000d0400042c80040320110729001075170034000b42d280b400460190144002d100d1910500340e45030807120200380c00b0a41800164840500c18203d40c0030b40c40744030001007220401400207600003050001d075250355010304017034070703149000400005a030303004085440d055820429010405800001d144404091208103440c042c02c0401c408214260540c1d17102c07204100d154102c13010290010402071000c0c0e0300d6041c09002c0000d00740080c803886503280344c102d60f2107100c40c1486100e941410394556545000184160484026400074a04500d941c4244181c20000c0341440c004c0303018050000c03407582c0c0421b118800900344000000c2501c3d1550a0920014603440580d008051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 554469046 1250 554467796 554467799
    0xf02011a0603010611121303020f0f0f010e12010203130302060711070603051503100b042306061317061006030507120b030705030a030c020306060108060102030304080705011e0c0e0604 81
    0x21200700036a030640c1e00606003941e00500c0003903520318141000713007002d42c1d1038000258015241c0b48140f920741180d10980e803510034080d001003049240b1042079043c90304000201c0550b50700f503220b800c04a0b65201d0260841031001980152035013a644201c801103060812116030078101035040105543c002c2d01850303c0140e00c1407095440f5201c1d01c0c680308003410141c0391004910b42c80104800e80d85000402000c540341040c105d62018064031207050307403a20132480c100b0290310000d0180d841c000140d41c1a5079000003640c8150030404107400c8101218424920ba140228200c00b01413183d03051300b5540d800600c4245403001c1c8a946010350b6030010340425013000148041c3c1c0c1d8011807010f000750440000862143c20600c00f20f880c04d4075943c0aa0b038184641c410360007e01da00701c500e400026009500341c6100307941e07140055441041c15074000d401613104000042c003061080000e0f005c0d851080b0004102a04144010030310b4600519409010703a40e2901205d00c43c68000b9207482c60388400740e0b100c90419 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 554470296 1250 554469046 554469049
    0x60f030b220b0711070f06080610050f07031d0301090c1e06140715060621020c031c060b0f030f090c030601090c0207080303070302040e1515071a070f02011a 69
    0x2002c0608248188000c400041c59800e01c24800c100c0035001c07402c440300f04a0b40d541c400404012044d243c42e0f000f288521542c060f541d10480484851100c0c5480c09481d00701c1d9540c04880f412107024154100001c400b07441c0e0000e9078203014021040c0d01401402d030a107170400100925803900b600000d202d500b40b161040002a8020b983c1310b8000105c000c41c2c40d1200c807182030041030140e01c1c44900c0c1030036140c6240407400c10b4024a8412a0850035107200e4444801111980708910604e5601006940140810f845c5422a0384400b40840b00c07071000803a2165071260014440e4008105c0010b5079400802045910200185031552003010040109480201000403d0300c6d50320600503030869a072074030a0407504c0e6008004d42c4008003c84000c80b6682d1512400c002d000350880d01440982506200200701500c03000c40b00500440b400401704985040b180c0344002c01d80e1300004081b5440019480030074405003c2d04241807003424036840318030140b01c542380000d00719409443d41c144d2001d0040c40c0004035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 554471546 1250 554470296 554470313
    0xd0c03091209050d031209020904051b061e03100e0c0901080604051312020102070b2a0408031c060b07060e0f0106060e100c02092d01141003060f030b22 67
    0x511740c0500f45202500a00880507002e00740e41d00300690080445400c0c0420890f000a601d400b100c0c0c03000d8026526810030040008a00c28030070741041404200c031100d4a81e00164004540004108004e501700551718440455447d40c21100e4440d0b162001c2041103140d60812561a071103441124100f00c00d1609403c80c2c038210790300303020203001d0400c4c00983c8081a07001f5411103070100e4004584190b02e00d0110a006081d00031180e00c1c0401d500c91b14004000c0c00c41070710a95098418500103141403080c021007102d280381060038040041034445a000404002c4040200b91040c0640c0010031050314000380d02d45001079140c9101390aa1401c0410440c0b00c0d4440c8031070340406e008039004406003494000c110303110580701c10007950045da0f00007400310005545065041c0c00ca00407141c05030020f200c003020501401c2c244940c0720021300a2440e1505440d00d681041c80030000c0703060000e109a29640800815a031582044407014004010b001c0c105010200c0c2107070710001d0003a1000c000c00160748104d407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 554472796 1250 554471546 554471569
    0x31406011a030a0507050405130902040c1b0f030311030112062f03060f03011107050607020604230114070302070203060f01031106030c0f0a03020901081308041a0d0c0309120905 78
    0xf256a60348003140e5440c3c03007030040340d0050400a2072400d2400b1513221050080540c0b55080b8840d40c40c140a6402c21401885d03890850507164070542c9007501b035038035040301d441c12184048003059598102080044990740255010303080170650707803000d82030340c1c0703401c0d0304a8600402d803452940110004840b010035603008a01800c1005208039166161180490f4000150344461517055082006844640e148000540141030003041140c0301922001c1c0143d0701c0c3d800964024100d0318200f0b4000300000d210068030b4410050703020000403040003c01c0010100301d03043d5032401c0002c0e0001380301425480d0401549810402c86000e010081d403465a41e02c50130b80f088800e05005240100008141e822440c090f54803070200c0101c9180c0d106c81c116001802980540e181c02d0101d0803410104806203000fa886c121961303801100249001e003000c1880c1c030b0081103041000c111040c10054040c80004901406007407242640f0045001c2c105440c10001c2c0c1c03100120740300c003000000d0340d0400c41590b501d442140d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 554474046 1250 554472796 554472811
    0xc152d0f19060e0a05041a0106050a030c0c05070e09120c0a240f1b031e0b0f061216021f0902010c02090f010623030103111207031406011a03 62
    0x5214070030850409840300c0d0303101c50b01d04921103040100145070368004500c170300d2082040d1080c106810400c03034804242030064000081051220b562100e00962083c519140d90b030504442028481d9101c03071401949811001440030034505100360b1890402c6030b4003128006440050a0111031140d00c0d41c1c6521112001d42484403180b48605103840788160f201d1902c06c00813092140c40074400f601e0300908a9200b029000300b85000f04035500c103101c3c0c8140d6a80d80380c902685003e0020080c2c8040180644810141d400030312246400d140741d0f2105c0081c02c00c030105400ca45080d282c20031050300c3c0f003210038414405540120b0f00012000040c0f42030034528003a80640018644154001212040743d01c881c003d4024015805100c458541c10080604a40c070759507481c5044804030a80100c090112204c25518010900050001455000d000090480013402440c021140660217510f00f10700f0b6441602c011480800c0d00f017001d03209000280c050030403100050b800004020718001540f0006000c0c1c2c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 554475296 1250 554474046 554474071
    0x120e0a11060c0d0309030e0904050a0b1b0a02011515090b031b0a021f150e060f03010c1e08240f03100c020115050d02060c152d0f 57
    0x50100e6540d1005840e1201c0b180c10072100b8a110000c800f40040084540541c0030807401100d0384460f1070140030b014030075a8080d02908189501c2e0b62403c0c2000400780c0642c1298141003007035501140c40724041d142c0713000c8550003c00d05900b807190b540c40500f290b802c1035070190090345860b4401900034201c1002c0b078800503200d580c0ea03551f10601c0800a4035514000f5503401001030b61a280035030001d03500b0b010b000400030344051110980d80b80f2003200d220b410300081c0d0425110b030800c03205036041360244d1301003030181c1014410180500000d00f107070107180007400421510500500000c2c405800c069024059051200c1c86080c00b88801221401c14410034401c01c0070010718800ea44c50b01c002c424107840002c0d003250000350a5007811409041c2641d20600190f01c0c0207903407015803118011078012034030f000e13004c84c06120994082c0306182e4003071020588288901d180a5084007900f15000c1c2c4961078442e038500d2100c80344c0300d0180e10030002d808014408180d034828061071380c1000d072b101d40d0070001d0100c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 554476546 1250 554475296 554475323
    0x3c040e0c0906070f150603080a021605030d1202071e0c0602010b15090d05060103120f03020910110312010b04170d08010536010e1e010909111002070501120e0a 70
    0x380c080d5036200080500c1c1d486c20000300004100a90000d0000307940c6075025603180c0282080080b0040240d44141c981c90b0b4010b40713810f90180d020f0b8a0117005072212072801341c540051501c0301580c4111408240000e10308103284c503012b1292004000b00030344000c1c4001c3c403500d40034800096610358020841030840b000003c01911a0f5926204c0d041e8060703009003601c11541e501e04042d4002c00c00c400c40240481c411000c00c60116101340308441c56003000402e4200100da03940e004a40007004000e400000b48030030482812590384c40b503038640c002d01449904640d00c0c3e080a207250000981420701001c16030000040e0342d01c454015076414191081620f0201c41031401c103821a1041104e1481240801c201540c03142d0003000c5041c44034140c03100c5100d54000354813451500e18a142d0340da100e000c070440f901401440144210781081441e540a002c1607400040e003000021b8540c83c078500c0010141e4444502003046503004241002000f88242d805c02203070045651490301d40d10520401412014803449 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 554477796 1250 554476546 554476553
    0x20906010c0b10083313050d0e0a050a061b260a090f1d1005221a031c050409020c031309050c09040b040212130b0c0703053c040e0c0906070f 62
    0x6c545955a80080407107a100300c1d07185014200105104515004080b444004a0541000356840007100c03142e94030301070807102e80e001e540703481d28681c3c408031842c4004090034070b2458862811001320b02140030725503544a95403400a800c046050b0311940c150b82c6030901c10441102d488959080b00050840408229900c005000710750107099000340e40e018096102c2003040c4c010214422100201e1105c08001e1092020882900b6440c0c0d00c1600342c0c164816440703440c0500350440e550700c3c114801e0800c6803e054841c50250b082c1d0700003d4549034107601c00b1488586000c85c00c1032450042c07050181c1082103040c04094071b00c040c81002e410502480d210b0030f109403552181e81c110707903211007010001903603410600000800c0740768989040d41c0b80c3e801e02d0082107011220a04640c4950b40c56100c207450800303031980c000001c01e040002011a12001100024174072504400ca18464400d065a103684900308031421089a01c05482404d04280c00e2140c410350381c440310300311980140c101c10081c150000c0c030714 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 554479046 1250 554477796 554477821
    0x80a0c03060b0a0309060b030609060c0a18090e061302100e0d02062d09010e01080c0c0601060201050916030c06030209120304090b10030b0904020906010c0b100833 72
    0x10300500484500090f1a440c180c0c0c558410360360144140c10900c008101c1c90304240d511481562a080b49403c45d00220b041514581d000308410616801c103008040110f00f1a034002c51020b910006055451741b040460351142488039036030102800000709882c01250300407954440c1040c2a10301030001418046205980b0843d601c001c50342d006240326a0760b40010000100b51820f604250075840031039024503c2c0345800c3c41a96010481a0356141c050b0090600441321690043c00034511158108159001c1c81414030015001c2c145580011820381010729985261203100701070400c4a0a6000c5c05200044020310808200c9500b442c0c0907880d4812000001c0f000c04125800510600c80050300280c5c001d80303900080ba80c2030b421030300c034005106080702c19400e42c0c428401c0c0c42c1c1d008003040c00240040c07906103640d035040801894000e1641c10160764680c41a030090b1100c4010042122017003000041c20400400a800421100c02581c0440a54413025250644121205820341000981c5200c4041d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 554480296 1250 554479046 554479049
    0x10b090405030d050f01030b0f0414012f0f0301140616030215060409021c0311030721030204030816110a0603050709080304150302030a0207020405010f170c01080a0c0306 75
    0x420141850400e0710304140e5aa00c08610381c0070003810140003610f1182c0418a040c100e941100d4400031030b030f40302e02c0310b20b5a0100007002104d0030941d030701400010701001d2080510340c02c0e0031900303a280111601c4c041d072950342203026001c825a5080208c510310700c2400080e80d0459078401950201c4c0d25210700029614001c441d200601600e980d5401c0092540c00152003404c2200460002111f49840c1c003803005990500340d01070340040411103104100e5521018003000c0034001d01e01070702840d000c80481c60440d40111030540d61860541d07032a42003051541d0b180c06140344141401c501c0d152850395880d5a81c00750049003d550304c54800f00ca000d0040705040704410150040429004e15204c00c1d016004242c143d50480014004010100310320340e00108540540d600351100c000805030343c0d40708a01070340c402814841c0f62902071207076000688a900909c0d0203803480100d08a14a070400b0541c00403444942440c060f00c0e40000f0ba0b82140c0d0341c0201050741c1040350f1503804561000004025005003046 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 554481546 1250 554480296 554480299
    0x30f02030705071a191a1f180302010c08090d0204020d0902010305152407080a0815040b0112020721021509061b09010507050f06100b03101e0306020409020a03050105011718010b 78
    0x3c4122007030f2102054403007003031100d1f5aa00d680c0280502c032007610551030f0043c00000c0c00304d441000401c01007690740e8050b00000c4030040400d00b4410890740410207030f8100d58060301d542030b119000b8108642c1c0500a96a1140d0000103080700000c54900280081454079080d2142c42240385194a1803960307001200c1c0c2450708010442d030344200e0014010600602100e9180010240380c12100091505000d05141024140c2d501100400e9441c2c100b0000d40c00a0300031124102d0080c00d41900c0b1408100d1840c40312110780150450124004441400c0c1c40d00404181040c1c000b00108075101c9400034411000c1c4000e13002041d211462440140c8041c03080341c40241951103543c0315200740c181c0004845101c0d014901900507100d82e10b1400c0c08040c0002d90700f04502c0c04008500380440c0004075103808000030200c004e040c0d0181e03a600e807041280c0c841c2d00f04039a40c80e0000380c00551140c041c0500e41c01002c0030319050003110321240c4170080c42d4a02901d20054100b0110017000b841ea025004003e00303180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 554482796 1250 554481546 554481559
    0x7020102031213140303100b2203060501140607080a0302030403050d0e1e0708030d0b240403061104050d35040e18100b01030f02030705071a191a 64
    0x200301580c40c1044441003c21900185851036003d144c250110a0b00d00400445805440e050b040017480c254079008204595500da014420f020030700d5044c031640c503004500401e000615035052400000300f60b080715001500640c03003002b0444c005080c1004a4514580904c1d0040c0c0782c0d200d81c5012030303a81c4a01802c002ca00e5061090f84650b410011610006401c0119126981e40b02d07080c1d0001d480c5c9015120b01d2a407601305200c0a8070200d0181c200114141c0001c1ca8214084c19124698079900040a0180d940c2c20001c1014000c01a052040400b00500800750906041c40c250000c0c9000040003c0181030b08a440481000000c480074104034464000000d15443e403a1081c42c05400d402c603100d403010015500d40841e40008101d121005010246400740c900d628074040420b010f48809a242410141c0e51169103806040c00c0c07001c0c42c02640c20340d440b0b56032240b460521031040345d00200c040420340d0b890428090281d0105d0004264540525008103c04440c5004102c0459244a60940000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 554484046 1250 554482796 554482801
    0x203090d080609100e04150e070602060903092209080c0c011409010207120c0b0a0f0e0312160804150f1808150411040608011a03031e070201020312 65
    0x2001180c02004400555901c40c129035420040001041c0b00b40c441e410050100401809582201c0c03c845a02c03901a0000300c0c040340002c1e5400c021240c1030f140c0390100e60071500043c0101ca070f0603c180354002808200460401581c400042d9800405d803d00552200021100c00710603111900174882035070304039410315126030980405588841541c078204e40000c00101e00035201c000c1300003cad01c4500c01c040c2e000300f03062400c0c20703600c104542014406039004081300600082c0300005400600c071803012907646200b105401c034000350089210505c03452003a041a00c0c0311a4411008081c1c4800d480011020320b007400c403a05000520b449241c1024070b2100c024004901c0868200310305e400d4141441d510010795038038002131642c00c595640140c220075000403804400d19921003890030341241c001c8400c1140070a44d0800501103c0b1241c0c004000c5c0d035100d040c1c42c10903c905011003c149502a40503600e0004000c8485070841406140181c10003804100702042da4420026204035000c8900e0008050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 554485296 1250 554484046 554484061
    0x5060409022e08040b01060e011403040302010c120c2708120a080105091e0414160503070b0a0210020c070305031b0c0105040605090d060b031906060b0406120911040203 74
    0x152111035446084120b5441c040d58510404100b4807943e0070071880501ca034248102103444010200055041010340c3c0003405030041c04c00d0045010728030980000070308107aa042c1c060075000030b800e12140d5040c5045413214645030805141d21240354054107540040080855130f03088950f15801090840c49044000c4080c1d0141e080240f4082d00c1d19215214039a903034504002c0c000e00100e4034955243c0241c00b000c142405c3c2c0c40c075025045807040160318a40001d0080701c900e03010303240c0e2200d20b07111000314041005040501000015108403900107150807034070f0b0006956400e6203002c0040165001032100d88540051100c01d01441d484416280da80e65644000010b020309151b00d50740900508203500760542c0200c04460880d54103450362414021544204008038602c01002e0342c2940d01d8079a00072080c0c0e418070181c039002860816043d0500f41504003203040351500d41064800e10400c2100b4020b0b44c0c1c000040e07038407102c048440400c80682074641400f0410082d040709421500100501015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 554486546 1250 554485296 554485339
    0x191110023f04030203070b030a18080d05150f150f0c030301030c090213050909070504051e061014030a022701030c0c0206192c0a080a03080a0506040902 67
    0x84159200025040e022041001c107014070440c48000d50550112004002c0003120002440c0c0c8440c400000190019528444007401201c100b4111003403240003601c0c10f03070403d80d8410250420325510301032206190b2a00814221b21428203a644514002c4509003807036260f4508490b2005c2440400d151140808642d065407071b04280001c4072015140b000100f4090030701e00c00e0381d0344480c50400403050700340b80c10140040100301030040c01c03650154140c0440d050311140965806291600d400c1540d00300c18035100300e11204003030a80c0e4840c8000faa2a84206580180d00301c606030244007030741c3c0d6252038540055009104002c140703002c0240500407080c0382010314458011641c2c0a8030240401101c04200300ca0003103802100943c0180240402403010340c7d00c2e2140c849000c070604001c203081080301989084071503d884c200c0ca540920503030100480c1000500d2100a140000c0105182e607800d40e8080c16042004140c8929550303281c0010300700d5030301d5402100019401401034002000d5107030301c1184 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 554487796 1250 554486546 554486623
    0x270703060b090c030f01090905030d0e060a240e0702030c0d05030103200a09330527041b0509100303080108030f040e07030209061204020319111002 65
    0x416481040042c0d180b840f0700080f40c0c4600c0c90780780608038a80c00d04103460028503602c3c20988551005011445c1205032030f2054403080b8103444010105841c0034900b40090324802c440c902c10710408034440c6414081c084040b00305651210ba8484002e5a03503080403459800f0b1a40450072912554501602c03003600900203505032070042050425100d0302c030842c201e500b00d1402d03003583c00c6640c66400304a0040a540030680c5038403200d140301d940b0035103000000f21078480043c0c10500408690410422450302103500300c0d83c8503801d4162900000d0260f90107401c190b00038000350100049a0200e00000c80c14600345003d4240240041418103004090751098060380c082280494441400400d07100c03400000d441c544d50303003483e4107071516042c1081064604c002400740810300d502885851200d81d039601c041c24205c80101d058034010300d0b081c01090b107000c0c450740c0c034800154150525940412402c003100f450b0820700355100c207080000c42008a140c00d840c904c8440080c084032032001c0c0c40d000041e82107034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 554489046 1250 554487796 554487799
    0x40906050f0901030b130302030d0c0302180420071a09060601090614071401061703180423060111100e01060b0306060a081003020316260303270703060b 67
    0x5024000481c14408921001c2c00050f1448010000080110254007104a4128840d1040d24188003440b050700040e541405a00c0d0003003500400c0e480b0040014512240301003000300c030107028178903000c01d0420214250303008003110b0900000e44a0288050070f03070984c0480d080b0500100c040d242c0160b5080d00d0390425a0003500050140c000090260301c500034450300108080109498900150347d0356840c0800c06810064954840100051003445d04110704514554030010f1603440c0181154641c00c07aa030050894440c600e002030800143c18030005492055075046080c40c08d84c2c503407000503505e071000d240000590b881100c240307400e02c0905400040801c43c1d280700a001e015100c0807c0c280d64041180c5954001c0320600010744030038861090706403c150340d51000c261460312600864280300780075090301280c0003003060030001040c0c2c00b05686002101102e402e10441c509141d0b0540300c0c84068088038041e2014041c00002450560325603811003810f80c12504695a24a448800792607541c4030346 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 554490296 1250 554489046 554489059
    0x10608090d0f0f02150403020313060f0c08070620041d040f080304020d170304170703090308030c160c060201050601170a111215040606180308030c070804090605 71
    0x60448000020718411a40c06512001d07030603210340c1000c4484103641e030a0401144610641882c400c1c40104145008900030340c051566213500d0725140e500e80d410ba40c0070000304100007030310110840c1e00000c040c11280d402201070b13940d9051414031002400c8013140d45610092052201c2d180d2400c4240140102c41c14078060010075102c104040c00c2e4400100c9001c0c081e004550003460020b90b00398021540984020301054010a254850980d2074520100c444100c0500000344004c1c051024045121240e4070015076140414564000b4074407401d92000800224011000c1035806000c44240d41404509890850740309400741070540c24050a03108801c0903500c1d00000c591607501c903042904200c1590340c090145520f95002d0100100720104100f10a848240101d1001c1074444840c68064541c0314451703014400c1d40c4041200b103811a50101040c0014010710f00b2006855840c0c94040300e03080007189440c2d43d600814590702d8412140000d1400000080105844409501030810790f141602c80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 554491546 1250 554490296 554490301
    0x1006090605040302010e0d08040b04090207032309010c0c0512010603061b17090c040e010504020301151d0a11040611060606040b040b0c120406090e06090c121008060a0203010608 78
    0x59070144107602001c0d000920b824001d440c2c5013000c0043c8400d452003401030038a05540d0340c52420403500b0a0300441ca01580020300402850b9101c0c0080e0744d40d05260070324400c0007801003103101c0144500c40c6000c0c18090107048a0060007202c0d00010003e1034003403c7e8003410251412014000c0101d8081295001d1900c03c1c9000c0541041c244510080f005484222056612842941040c00010b100c41d42c81d108a4103004d0658035a401268842c1a04c3c10001ca0300341060f104041c00c0d54090305890b2681030400d0401c000070381c0001050a0000c1060b8400c84140c0c403880c540b88080c0540c03000ca10b403080b400203800620035a100c0054032040c03048500b40c607441c0c1c9442080086910403407040c0d840340c240a1000b4004100d0f604001d0403608030311030840d480040110b01048664001e035000801054076900200321803c0c65010090b8020700881c0d5205072803400c200c2040e414003803450105d010202450000b4406e400f01c80048010b070540b101141c078103150007c4582e0296000b409000300140b0090007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 554492796 1250 554491546 554491559
    0x50901080d0801180f02161505160c0c080601030b1609060e010e0d1a0928120c050106080105160203092d040e01090203120301062109050105100609 65
    0xa024203601d500d0b5495812a03440c055042c1251400d03040e030381c045070750f407060518040c480610040810260451000030900c5003401e084801c51400340c071112410781424204410810190421454a0194180000b90419900301290f521a55802030344085c8100b070004001c0c02800030001c0d1084200c00502d0701003508503003003120050143c1c85620302180381203422205030342c02140c40e40541c440150004100c091a0b440704841d6482d41c3c00c20001c1100b10380d007881010342003441905c0f030600c024103403d00703144482c80f91000c81d1080c66102500d20090200707240302041c40b980d41a09515008402840b595440c0c1d40101c1c001c11003682d81c4c11400c00b4074412036010300c2c004026521200c8000301703c0c0c00541d000c2040d110300c0440e000d07000780001e4580502c0d138107103584900c1240c4044d518200006581d030600d10600d45014003441c400c0b03000c188240010098507034000d411222001c0340e0450122000d01e05000c0c18090000044024a15401e05007048242007c0c0c0b0580006c55100e0f07940c60400995849 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 554494046 1250 554492796 554492803
    0x3061b040f03060e1c081306180309060f0504051c0303060b0a05090118270b120601050301140421020132070908250f03261309090c0905010f05090108 66
    0x5d5950041404240000d002914560600110300d01854000c104100440c80d0200d0142d1aa0320032000315506160074805103078001c16686000703450342045e078900384c10500040c85950b089080b0750b900d240072080407400c00d4442c0c0c20100081048081c0c20341c9900b050a03010b04550403603540580060942d041c00e9841e440b500302000c04846040265a68045d510844a50700d2070840a05045868441c240e1030604e441d140c02451640380c010703000e4041941814201401d483c01e000c11103490400c48014080410400050805030b9503a0305070440ba0120580d038168003600208641ea9081603070822140345c2c9030300955068010540401204400d85c1e42e5903011f075030804040c0203e1020b075204c184451100030011040841011205484182c8240c0c0d40c048800400d210750811070b00180301d01c01c2c1c020041c01c43c42094980180b00b50a05040400c46045a69807140902c40c07003044035111080e4509100081d01c0c00005041100d03c28011981c42c0c900c180c001c601548030351030044110701c0c0000b44006012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 554495296 1250 554494046 554494093
    0x50d050d0c02012d0603080a090303030e060402010509100309060504060b01030b0102010911100507060c02011d03040b070303050712050411011407020904020f060d020a0f1d03061b040f03060e 84
    0x81c040e032a860505400102c0000d0344040f00e40c06240e80341da0100c0801c8011f0050020001c2c2555880c5009095240040640b4198070b407059981d4003190034440181e82080030b4910400080d908012542c03240765046000d400840e401800c603920348002d100c03d0040a07007064210160a1b2400c1c4850940800124200c50080d100600551f100560301c0c2014901032425508580c0146401400c1109540b109004c5a81c880348080241c1e555041e070002c0d0104400d2001c03885c01040d400345003010b01d0200c04001911489500038105643d03003000400e020b0058045690f584100c03801002245494901519000380e06804280418800d01e0a0b4154004007000c6454460b4083d02c1880c3d291556030900c0401ca0040c41c045500c82c205100c00321b11039078a8400f60007241c556640d080460014405e02810004500f019412a000708560010f02c9480000d1526007140d03280d24000b80070548035204000e10701581d003020b813240303000d40400001d1241c9500100803507103080c010b079010088002c040c99945980c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 554496402 1106 554495296 554495321
    0xc04090f050a05070207030b0705030613090318050d08070b06030f16150f1b06020904020a0e12060f0f0718061e02010b0a030204020d0207050d050d0c0201 68
    0xb0b50180d1138100f04e00d4000381180509586440359906e00007030000c41441400800720300d107a10f4004607511240380e20481044040070500e07000b01200c100c0c00340c003400c41050400100d03c62804200c1440029800828503181c0139050f51022072480d401010660305005026807030f00c0001c0c007031124500b100c0c007106006c03229a0407c2102c084800c4031811b40810000040001c20b40320703800070604400600b544c1e1505207004035501c0c0c480068401c41645540003400482c0740202c8640180c540d403040030044403a0800369244c0c007205036462808984080300c0305544404505e849103240e200c079400c0700f01441c05204a0082d11444400480c0315480500025503012450807050300010071041881103034802441008034810004244811b01d00010b80305030b1340010008482c18040d81200d00c040d5001003682e110454008014040d5009480d00c0e0b1071107030504800014041c418072801161054 = true := by decide +kernel

theorem cover : BRFrame.Cov 554316546 554496402 := by
  have h0 := BRFrame.cov_init 554316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 554316546 ≤ n) (h2 : n < 554496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
