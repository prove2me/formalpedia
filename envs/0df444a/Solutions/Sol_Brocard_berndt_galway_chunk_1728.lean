-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1728
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:27:12.955551+00:00
-- url     : https://prove2.me/submissions/058f1a5e-0eed-4bdf-b7be-111b0cdb85df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 310611510 ≤ n < 310791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 310612760 1250 310611510 310611533
    0x308041716141504060e01140c1b0402070501110a02010e0106180209150c03121003050a17120c1809100b16060e0303040b0121060b0310061e060c0519 66
    0xa10a0b200000d40440e41c140c00c003086e564540000c1c1e03540c2e40303010700303109204c081403044200d140195444010303922150b02021804100c200d20250001d42840c0e955550300d1300b544e4601c00c5c8101001d10109103080503070742c240b1480280200a20081c0400c528000556a02e1190014640302103070b000140501180c8030301010207192440c034a40e042d580d100f80d01036151070740c005034048040c406049000c0341b1001c500340c003200b007681d4001c0040c25040007140c2d0780e0741c100c0038100820140d04c00180206240d1207404074402d0721402ca1070010654454000504642c0381807403000080c403d20a1070b0a025800082549a505403210205090343d0380e00c02d81c0041007050312015000b0010b50074080040721035040440035601440c4102d43c5020240d80b01c401c0082c0c5111000130700e0300085485104440843c1b0306401c503c0c6015800740543c4d0040c61107590010545a0300e03009034114282c2c0d108460001c140300a0300500422440c03a0803000c03201e40c0d541e070a440b00701070100050113449440914040c403050441c003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 310614010 1250 310612760 310612789
    0x609060a020a1e0e1e1203070206040510020a0b1e0915070f020a150e010c1b02010c06060302060304030903030e040b1c05010b06031e0f0702100504080d0204030804171614 75
    0x2440c2900b45240e00400c282c0c0307010714041c00c51b08074528070314900001903694180c2c0c010019400d080c1881c007440300b64280108500d04605c1144426008201550900d50040a8403112034a030006044600ca00c41d500107403c4070181d5120307c1c000d05694209041203a0032807500e141900c081201500c0c102d1602c0001c20020302000c03810700884104d40c400d07a0003031100c0340d10b00c1c00900011034400300c180c6100103628882c050707188001400300300540c803d03408505a1485464001412a1240c01048042c0c10444084000c02c540360414800d05030826074201010004a9061012900c52404a02030501c10010340012419543c04034007004030a42124000e403d0241c6a40c0c0c40707247c044c91074429146040044003090712200041400c19480380380786440b540c0d183e0010001c2c0c02000b51850002c0000405c1510010340c144a4180e40c6032841c001000110b0040c48000d8030b86081280201c003600301165282030580c8584c448104115503242000d0031541001c800041c0070181c107010450042d40143d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 310615260 1250 310614010 310614019
    0x30204090c08090705120303070309060f180b06090115110c040504080a0f0801030b01052e0509090606030402220902061611040608030322140609060a020a1e0e 70
    0xd8034000d640c0e000700003c0c0b20348440000c07940c00907030301c0040c00012000d050b0004003d0b0400c02c0014903150094220f000120f1089000080518403010325404a4116020125503c41c4000e481c1013440200310840c1d40100041ba0741e40e203c0e500d006400008140180a6081441108900a418000184000c0e0100304002e030081c0300ba45400d140407803881c0d10400d14100030860f84104d503001144070b03040980c1601d6014015044907402c00007000300d00e034a940d08103511240142420700e01043e05a5511000c4441511784640b140240070822000e460300400c8907028080500810000d40d950307076048080980c441400c03160340e116504021010f003e103030001941051002480d90070707403030000707030b0220040380540100358040381c454017000186ca5141c807030906540d00620110b00030100381080001034140b0003110001c4082c466450120b9001d0380f950014164000d9010024001d00a20070190b00c0ba88a100c114071b4400a4080500345800410100c4905000240d180714150f001d40d0000800c2032000b030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 310616510 1250 310615260 310615271
    0x2010e090106081905011206020c1f0506030c06120a0b12070803041a03041106030a020418020405010f020a0308010909030912050601060e03010c080c0f072f0a0302180703020409 78
    0xc006020102d044d5400044c480c03c40056500f500b08500c101030584d100d40d0b10144049085444400c042c0d0040000d405550091003c0408822486802000207410340c01c0c3c041103501d40310b000c15040c904080e91031805003c08001410303401c5103450f40e880d840500b8080010b1011400400314010b1009650f240e244d40c0f2802102103203000c8000302401c100d500230541c800070491424420600d500082e034004008004604001305145400b078042c690120002e07034010700b443c3c3d0b14048191051040d0f1132040a5a40c0000d0610195900203540805225240001c0c142c850b46681c2c010400201442104070781035460007600d04044c030030310701c010080864098a8105012038203081d03881e0402071040a01040c14081d443c0d0041c101070286031004052915443e102b60713102009a03140d9440358002c0c411000c0108400341c0080c4503024401c0c40501d100c14543d001c20300303905083c6662050303081050300c00c101000e404c0005a4815140c0d020348850111241d00340d40314074074117902a00941c1c000d07049190401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 310617760 1250 310616510 310616519
    0x210050c07050307151a100f03021608070b060607030918060306020c010c200d030b0f030a0302030c0d03050408040b0c0f011802010206100614070f050d030f0e06060f010c02010e0901 80
    0x103050400c40c041c045c1c0c003c014030016107440110301c0e20001010b40c0c00828020718401c4044c06068030460317072019410003605d4000c08407508100888483e0f001c543c42c2d04046002800c0c001901c60090344500c00b030f58828680002c40d01c01074000d04030780c82920180f44011042c0d0306540b039281c00c540019640f00006545a0785004991130180844035440da00180e070100c046900c0b0601000301da60700300c0c0c08001800011941c01030440103000c0c4040040d411080305202c6090ad9241081643d166901a07070155071601a101c1c1caa03402c00c400c91403000200b5007014141310119118030115001c680700305e46004c1d42e90358040c11541c209201c00201440b99440c00320111461544140d01d404910320076801d07038034542d07968460701805260500079000002c1e04102c14440c001d1000e8020600b150290075013201c2030b89039944807450031500444850000e0340f1980b015584540c00e00465903007450a030f018140314503200d00450b010b24017240000c4d0401c4020480f40f42964002e400c4040103a2018201401c40d40e101c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 310619010 1250 310617760 310617773
    0xb0f0d05070312031409010603080913110c160e1b070f0b0c1e070f0201080c0708031e0109090201140913050103051e0a0b010b0d0e0f1b0609010210050c07050307 71
    0x1c0e110080c1c5001800900011418410348c003d4a9008201508140402c010710008640c09040c1001d500e07543c400c55000341d4400c1028000c040300700f80040444c0c040842803261180c2c065808010100801c50610518440381c128030708502c10054956511600c80d400e0204011124500c09071080c0d0750300c800c1c8900c00303800000030071500d40484404c2c4850110312600c540d081c4a8294023502400c440000c05e801503104068054000c000c1c01011030405600352200003039980155201d00d0700f9490340350340051701c0b901e81c40490f0052882d040e082240030210740002c5d10042a01c034a05e00c0d000c4000072a01040d13503450a641d0208507808204010560316440d203603981c0c034014003074018104c07001c2800e0308802d000010161001a44540389401c5640303010303100c0315a074118a00c01c810158030783d0100d0004030010092006480d0f0090014100300300c0b43e0b000f9002200c07203204443d0186000f013103240c44998000800d0300d40000c0440b40020555206100306505010703511000b00240400107584091058 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 310620260 1250 310619010 310619021
    0x5041106161115030a0b06040e07030c02011d1507110a06060f2112121b080912090105070602040f060206101d04030827030a120b0f0d0507031203 64
    0x1160314100300000c0d80307000f044001241269018245481000010841a0a80c015010420015040030304183c0c54034484215000111200400284d8402e034218a580d82402040104600011030745401140c40207419102d04a17940300c3d00201a00394082703501c86200b0b1b100380013500540000c0e281c10440b00d252040140044d0b104000301104000e0000c1001c218400144c0003011005007103103146c1d03007250348200006401100e034809100700b106010b0054145400b076058403543d08248906008400300d40a014003801800d2802d140d803040e414206902c603001c0803a01450700900780395489111038038054000e4480c030340203403445203855400090200c1c0c0000b545402460006c40411009403614549065003041d11040405c110001e00401c6c0424001c9001035000041e4a01800080d1001800e0041c0b1040e4490741001b680d00009959130702e203501c0041800d0401ca43c0c402445043e641e140064491782e080b000141c420980fa4400c0700c100324041004100455024005000b140d9412101900628 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 310621510 1250 310620260 310620263
    0xa030c0b0d0e0606100c030c08130501031d0c0d02030a0609050c0a0b0a02120703030f060e0a0b0301090203250305010f061401050c0a06050c07020301090f030f1704060504110616 78
    0x60604146090042c0e0200e0100e20501014004010b450700d034138011220b561105000758203024103200c41c540450b6a08008226900a00d00e0001e00c2500c0c1600040485002800b800901d1442da40d02150f02d48020400040702c490845000c0282c140500009090001c00031000700f2041c038200840c42002004510b5035402c0d441281d80d00324560f03480c810b901446c840c1c42c0d44040180c01042806440146150252114500928000a070701c480b06d1b004004466440d000450141d04400400c0500b80c10b17070080316440718055000340b00c00c002680c0400d9035103a42c801802c1c54106c2c0d00c040341104c0841d00b5070311300042d07410038000c0c07282002d03404c50400108a240100c400d01181041c002034194010703070458a90000100041541021a888640042078003030200d900d180410885000540d4090161016850103141003110803c41442c002e490b5002400031034040c0500c0d090003160068a248100c3c0d03000303801c0200400c039541c852814090035940205103541c000d03000b2074440e00c400c4002940202c0d03603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 310622760 1250 310621510 310621537
    0xf02010e06040e0712110c06090c04090b01050402030a111801080a0911011d0a0f050f040903020601030803100f0608090d02010204080304140409120c151413020a030c0b 74
    0x8a02020a01106201c2da00652240d0140758001c40c0703c6610400a041031030091311000036100da00041542c941c2c1d407081900740c40f50b070b01c1103080c041404020b2203540503040c0100d400700460006656000415001442164440e40d0b0202c000b801c861310641240740c118030003c035030950703460100c0d54032022000110101c0d40000c3c2002c0006281c1c222070b10442e5900c2d500701162860701000140111084288006c01c107003041c15503050309583d5103a0410903800b4105004a000d26142044140b140d90140022802d101d1420181d48002007a008500e45040d00c0c5c02070300b1140d403991220007000710308449522000e5241100c480014806500642c2c080c000c0120500707560a00c0d9044504900f80c0c01140100340c0c6641041004110101202140c0c841401000e8008185040c554a07050301c0384020480341c0f808111403900c130100b000082c50074101c0440e07020808008581c581740006413072410052000d441746420207004010340d5204407503d001158003a8262099a80703c054940c0b80303401c004c0034030050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 310624010 1250 310622760 310622777
    0x10050d02040504020f04080f1f09020a0b0a030b1311190c0b01030b0103120e0109060e12060a090c08062403030c07080102090f09040b1b22051302070f060b1c0f0201 72
    0x10120040780b0f008024500b00c4027580d1040c8008103000007000c0c0224220b9104240c5d44000070310998013005040004615200003a404812009001c050040500c00144491500400c0c1400480003001d46d80c004407030392402821041140c4044e10361000500c809000f6140c0d040000080164003030b90b4a040c0c0b0710400c0810042c0f03858140c140c0e40076030048211400318440303400a1080c14854090400e030f50800030000201190640503030f40c00c0c0390055070b160394102e07101c5800350203120a4008140050402100404840c9080e4010809540e0110b104181540c0d114019401c1650200180d801182e089001c1d54140c3e0340d16406217000703500009085005903000425124a8a0b20341c1409100f42c4c2c00020304c02c140e0381c032060780340e4054644511500c8948400c0c05100d13808a503101812203170303030001c19000d051a410b150400c1400320100311800c1c0c043d0300400c0345c43c002610140600f810385078000d0000c03803e902840b00280aa00d02410b10303a00418440e103410044c01700501094a2540c000c0c0c858490 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 310625260 1250 310624010 310624033
    0x1b0709020a091706150d0f060c020d0c0c05090a0e06130b0109020703080a0b0616150f1a010e03010b0301140103060c0305040201050a08100e070513090b10050d02040504020f0408 78
    0x2ca950074102c03c915004040000c501c40d5806400c0c6020703800c000c2100485030746942d0f410000c806043d10590300c15039500c0100c1c080700c0c2c04210310f5403041e03907a040668014116030780f0540c001a2601400740039480e03010210300c00303a240c2d800440d19552500203958980c54404105082c0c012040340580740040110300000d800701c581d1084400941d0143d440c0401546c90401c1100544410405103800090401c0180380c44908141080000340c4603141102c524180c005014007551190302c1140c240c01c0c640301c5500d1440d40e00307a9003003010320020b0030101d061505610010b80180420320050350503500340000c20501a101c05c000a0581e8410031040100c01000070040703044170000c41e0001c0c04a002000300c850007a0180c0400307680302018180d0300034407a84507030300d4404410003510250f02103607010850050003041d4811002c0948080710007040803040001c00240b1003c0140740c42c20501500040c05070800619404982c06001d001e00203541e1800e84410a1640754440d100f00901800b80b8851000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 310626510 1250 310625260 310625279
    0x9040b01110309010c1b170f010612020108250302070203190f02060c071a07121d011d04051e1005131d010c02010501170604020907051b0709020a09 65
    0xd004072000460900462100544180e040d4a07801c0d0b501008070300c10f0880c0d100074800f003440500751402e42d0390074004031003c110740707061400300380b01d062a41006000d0181c0f1481500d0840040d4092a006040340c84130400c016514118215001d40039640e03000342c080345074140c2c0040030714510a034101e910400c8860074003d406080d22100a0400e2160380158015182c010050008000400107560480360b032074406013501c2d0000008108803103800300b481e0b81440f07000800b00c420100d041c11302d00010406c0000040c0302e100a08441070500103e0214401d4014405103c2c203041c58020f40200180d00300010040c8510300340e039905c04981007804c40011301d480c805201c030030103e400c0502402d0411820841800107008144049120060448402d9007a0b09090207822906041c03074000191550402c075a40c01004031545580c042540040c0a000c0103803107140403039900605629045840d038404c60601c1e0f50369001040c060405114440b404104000d160340100380b1061680c0765028816981c48601e07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 310627760 1250 310626510 310626527
    0x1b11030316031d06040c06080105060a080f18061305073008070b0a1e0c020a0f06060e0106050a0305280e1213050406050f0913081303050309040b01 65
    0x200320780003480d600340403918001e4004040210050b41c2c20480d994255031810300c1d100040354180c42ea800440020081180c0100321107000d01400d07103a862070001d4140014100c90009041035a002d1041c500042c0710074411083c1101c4c02e0707811020388040b42880341180c02c80c407244203000e0303c49000d50f281c0010000080c01030120b07008101c1c03d004002c04020700e50446d48a11040003034402d15401c105610010340300c44e503624403840c9900b00000b0b00001d01e0721000020f880c00100742035250310704192007816940008609907900d03800312246021a2007450814081c0c003842d030020381d0740f1703141200104000d50008040c3c1445081c581d000c010f030b41d0f241168584015044680101c000c0340c11130882885861581103403021a00302000c0361403d0718056408069035102d0841d0380b41c2803110351b00901c00c82c681401501d0080100301c502e54104411240080d10b6801c5c00350020200c3c08051544500700030343c903005d07200881c1c46d007805454181d42d00d081454403980301c8058144610b02d010301e8039100d5030040c85034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 310629010 1250 310627760 310627771
    0x71416080604140a0c0b030403020d090501020a060b240316090e0a05070e090106090515070b0c0c0f0a060603060e06010b041a1306090608011a03160507061b110303 72
    0x40907991929243c07060030700e41c65900c0c9507203409100305a00c080307040a11104000c5c100e074030311aa5607141c00c0c14003e0038103018807590800c21100400130841d81c2e900052054125130030100026400796204000380680e1070160482480e481d01e0000c10300c10003000d4000e5480341b00c80c0141104400c0307052400302c590782d0b105d00841c00e400004c007000c1440c0848076400326502c6545403c0041000d00f14900164228009a020b02c0000d20611010f00c03a5041c02c1d04100008220781c4038072410807510750740b1103001c441c00501500446c100402c0d60740b0903400421a041100420307000390f40c2c07820205d084c00006011a03020540e4414140f000818040000091550480300c0f928505070a041c01c20040102006007518a000c220a0500510512124003001c400c010120364540000c41440e185000d0502c000580c410400c06111540540f0300861000480e64801401c01c0031810604400c03500b500c2c54016080050017062500d5804454540d003c0314002808400f81c079607440210100b00044d6603032004650 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 310630260 1250 310629010 310629013
    0x312030106120b0d0b07032009010201060801060e0402011407061107140307020f041503140a032a0602030703020f0c06040506130c090506030c1815010f05090f0a080307141608 77
    0x1100e0300840d03404c00700d0305d420011b613141c040b07420442a10102680000001c444184800000d4150241e40e024400c5400800e8a03c001313000007882e040140300101d2000700007070b0620441c2307402d1202070300140080302ca65076032080003000042c140c1d2144801c1900117070703003c4070602500508040a0203000040e508030550080500e1401c203ca4000e200240001c61110040308040c1c1c08040001001c03041c42e268084a180700400c112145030600905c00e00c3d2001a4a0782e80ca40c03000c014038003014042c4e140000c0740d0008400361b5a074540507000c400900c00c80306203200a59012810250010001c0b0b146070149010340111405600d454908001c000703034488000b44000135170300c000c100d000c1c41ca801650b4054402402d884004082d0000b10f03140403016a450724401300d50340100301d08001502c41c40900240d0a00c0c21810454030514050101d1091000c0c1e1882000350b2151020103507100400000035020013003d5136111501e5160942481c10707203e0a180b141d0080c0c4111040c0e2212011405088840200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 310631510 1250 310630260 310630279
    0xf060e060d02060c1009060f0501030210050715020c010b0a05010e0105040e040f120f02120f0307031d030d140f1003080d020c15070206070c11100e0312030106120b 72
    0x81241c50342421004981000c0140142c000c4004148021000c29902d810081007044052a0000855211046241541d0710b001e0043c00542c9034942c2464820740d0a00300a41c0c0d51045041c2180520200c135280300e041030000959480a01040d00a540c083c1c1d015907009041940701c900544010394404442c90015500b40420028001d10001407a00240100c0c40090440a0b43c0c03114401c03072441503c4240818000d01c0d074054030560402460b004174109000060801c40d8042401c840e0340f1016210108046d10380442860000031303070801403810b610040450f6903549803010b104000c0c10102204142d8480e0900018203103510700700219104090080c4070021242c215a02c041c4a50410362041500c141e0a112400180d201004103c0c10006000000a418a06034600918190004002d039041010041d071040016804410028034000301f00e60b0b09146441c80785040715418145031400703515105010300c4a07101080000294141d42c102e0380c601450700c55070407071b80d0195400404141e0300b049101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 310632760 1250 310631510 310631521
    0xe070f031a010b0d020f0d060303170c0903120d0b0a060315050108040203120319050103060623030c10050c060c0a021e0c090a140f0609070903230307080f030106030f060e 75
    0xa03030041003a161ba0f000e0140c14890f4030790312101205c43d40d4100300c0101d1165100402d0520320480b0003503001c40c0c2c14400d01e00d040c40104c04280c965010076106a80c8000c0420003d4941c0d0481d0440182d4000150181054656411000703029081000341c07951010021817000c03031300b544108982d920403500130b00100000b4100ca6440012580001c1207298040700304110001d9127a01805010300842c0190404a59a4200742801da4503c00340c0901101401031a4296441c0b6100410850203400007200e84014854a0b08000e49840c4114070710004e250141d2010807003a600c0e241c2c050803000704250300700c1e00c0c3d070048100070f5008140c1101514146034040c804079000c070b14245106980c8140d95070004074a2251866000310f05c03c03400d4518803281c80041040041c10f0411908081c9e01003054074040300d01a14507108e4800c0805070f0404601c2d0020303081c6081c040202c08100300d078800d50340500030139920507031b5504001050f0028010360001a0401c2c80b0500c0c010701d540102070540c0c280e840760031200d40f03d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 310634010 1250 310632760 310632787
    0x30b010e0a0e030c01020c19031d01090b1216050309120901020a0f03020d2d08060315040b040c05031203070f0309060218180c030f09010e070f031a010b 67
    0x1850041d5507500c405007582111018006450f03424400740c00580c07100c1d541c004941c00c0103200003e030300d51a012110240046a07010b800e4104000075200d4210202c884080120340342280381d04840740c803810000310500304070940940c50784200040348152512403502801100e0911060b02c00c0300d0385500007005100102c40d101c00425501e1300500442c0d8050f00e99503500540079102a1050b00981c004003134810707255400801a140c240e4200c60340717140042102d2440c081c0e4102d1008130700b0400403841d00103603542d1000c01007120b071300040e80007491461505207000f01111000b110102d07154446603100103024140042c182d41d201c000c0758180ca003941d552442c100c40500b1508035400415441e204004086880c9200500300002800f07004e0442400d0340d03003400900c2781144003161741621040c003006003c0003280140e98115400a01c81c4549440d112003290142100b5558004035019000b0300083d05c83c4d00407085000c40b072088000c04c000344d0309080c010400003800d21808038244001c02007144140d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 310635260 1250 310634010 310634039
    0x201080402122416080709060e0a0308070804031202032d09040c03021801170109050c0c1005010905130506010303050901050708030c0706061a0901080604020910030f0b0109030b01 79
    0x80c80030403101c01ea04060840f411200c2c901601031000c008110a10452040c0701000324214115414600b1050902070780041c0780c468103128800c204028940800d0040d07847c5a48a8003c60704403a2480e12400b1a041110b50ba0717001d44800c640c408880010200c03258004800d5031001d1414440504541c4c00c1d802da002d0344c211414075440300e000d008200d4032506540e94030075942040c10b2960016111098000140030078050580001d0502c0046c0c0060b01d40610f25039490b5040d10340540020401d501c8980750310000e4001d5902d50220350140011707007025004c1c540e0040c0e0403140e001100b88802c3d00d441381e00751024184404090040c0c0c11000c01031000c40d005070024080d581040c54000c0c50044640c07555002504150f98444014a000444e8018400780307015203806080010919103514803818201c000034130030808041d040c0f0400c140011019965603041e64040100900b08030340403000d208005001b4440c03c0c0b0000722440c505034400545511400c0135801785d0b40c0c007940417503141e420210165030064 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 310636510 1250 310635260 310635289
    0xd080709210503030a151413020c0a0203030703030209040f02070209340c0c090c08010e04020411041511060c0f0c030d1d061501080c07030e03012c07030201080402 72
    0x102000c0709500040d010002980319941200c00041c099541c0300500030683c1d0a035000e542240a542c1a400d01c954880780c913600343c40580f800059440c1607800900d81044010031001c2e51500021a44d80c0a00d900764000700848501250104824040c14035914104e020b8400080e4002d0015000070320120411005007920003107071032680e030540b20645003002e1112007840303640700059030076184d900802c0401100107014000d400418841207070551001440000c2c144100500101c1c800042010764540b076000100000d1241382090342e551311800202610a50031b1003130303800600301401103440d440c0080f81041c0541303003603801c5504c1c2c2041c0e0450740a4580000603059014001000040d88905144c4140c0b080981c03000007a80030090442c0d282802c0c10b8004010040c08170702d2000c0200560303404200a9400803d07100100d4032000242001c64906100314026901903103850304001c1a03081e00041e000208013115000c0391f00070240e002590300d466031444001e001c50407540100b4010700d07084070090043c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 310637760 1250 310636510 310636559
    0x309080a0e1302031e22020d110d0b071b03050a03110d06030303050603160f05010813140705100c08092e0c02040c022e020c0106080705030d080709 65
    0x4526040c100b003268402d8800c02c000c00f4461441c03c5050100d40d5800740d0042c0c404c100001d84860902010502004540e0700078420a5200d00260421840c850707800c0c5014405002114260401c0c54805066038040d284003003c80c0303048201d91001c1c501c0040380d129190f4140c1e81e01d800c00100b100281d0141607084056040c0800c01d1194030440c3c0d20a110f03a2006501a43c1d01060300d041c44001c1c10304094200003011580601c1d50b4007448102c0c0201d4420048480a2a00c03000c20380d61800010b040302540c83c401450121079044031030210390700103154002d640085039001d04039444030308140c0701c10403d0b14001340350590030b200c00c3c00d1a01e0312946003184d100461a00c0c00302e0641074009090007144440d4881d002c100c2d42000d03d0294102031144985926440c001810010b07103500205010b406403506880220240341c4c10003000b9010340d01900d80c00104c150090160320385501a264680d280307402428080d02c203d22800410324891040280600d0a6403980d400d014200390a680d050080d000070611071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 310639010 1250 310637760 310637779
    0x503030105090c03133906140f1801030b030607020a0b0a0213050d03110a060504060b0402040b0702040b0f220522060e03040e07120b0105030903090f03070302030a03110d0309080a0e 80
    0x2520031822a05021094801207428134500f0020040d044c9804031804160740007040c007204021300d01709c0c4101d45e6028081c221155407600c030540102c001d084101001905405403d041c0f0000980028228559500c10034000c0d20a42e140c581080032401407010300300c1441500c0c0d4040200c0c5c02c0c004254501d041c02454014004030741c1c07860a03480c1208400b0100c8040c0d41c0d03a003c1106104880c032805280800403601545801c1c604489003020b4001c401c006842241d680040e54101d541d0503c840d04906000b4001c40d00d04100400c2c494214010380b2a144440d90030440043d448402c0c1b0540c5614207045c2028031001d443c10790321200c000b0034040407861b0f1644070420000c1210340d0403c1c10103104100a60703480c4440d41e02080004190790552020b141440020b04c2170040c851804010b0311515013064909464050f1450002481c5c00b40c17603440a9014050304215205040e444034404034418404000c40e0810a1b07050030032000c03500500800b034000c10080c45103041a62081140381000346004010b03006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 310640260 1250 310639010 310639073
    0x1309050c04030512040806060a06050301090b0f031915021201031e05100b040f0c0207050d05070902190207061103032403010c020f122a03040902070503030105090c0313 74
    0x1910780341e1103072901c04d10030106040118110420a0b540c0c088800d841c1205034600e801d002400900043c0100c8025646a07100b00c13606032641440000081002401c82d54075864840c3d0f80e40d0031121a00c3c01350740b08400900004240c40150003112040490a2400c62481e8610703200c041d00e89450140706581900c0401414003c21420010044100e6490000017288030301c1d0400c003c01c0f035409a80c50100141810001020103802284800407113405407950034030003000c0c0c40c1031760074400d00380c2001c0c1103079102003004e0158400440750040880d00e65000c030b8102c5611000e040d501621b079801d040060b0350042000840091000401d40b891804921900c0c2c000304400001a0030341e40c074030300c660700141c1c4201c8098048400401000c4c02c0c4e225008000c510704140d004207181340351040c0e681d1055507035900038041c0f032004041044400a041141c8215181d0905240c110340703d0303000b13214141c4256035400125001c503418408481c00b03603002c9810315050481554446007050140035401032011804c00003280f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 310641510 1250 310640260 310640263
    0x4060504031e03140105300304090f09030314100603020702010c24230c0a090f030c0302040c050f03061905030f1507030902030a1502070c03060c03060603021309050c040305 76
    0x70803180b4552400f10303001d0145269001c007510140d01c00e901c904111140b0001d09101288140c143d034194018001082605182e481d185206982c025108103240c5051210400d1103540041b9049200c1d0760140207151480c1940440001c06442000880d284420304005681c0643d008191075441810001a22400358461440400c1016010b81172108036030041c0c0d159055502c5110440c682c4403071041034208014070040d076a004001c1c00801181b01c00915190010300a004410003810700703050340da6007141c50f40703010910b04800f840101c0c0100d086c011484200c2e4055016582c0c1010340c40750311419940d913401004031307406102c90000044070810b8408505900d05000d00f2914240701c0300100300550142030052081c1c0001000201014905503400340107940c01728503001c44a4005103200049420071107100c00912626070020300301820b4072800001c0018a800121054280d91010000660780d6001a4240c0c461b0728900724201802e0724041c480001c1c983d100c10b40001c0c981110070b0500e034481e500e80d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 310642760 1250 310641510 310641557
    0x1f1104060c170316050714070807090605060f030a0f090c06020312090c03060f0a02090607110102060637080f0a0212120403030e010e030703110301140f0406050403 72
    0x800006103030100960620080102c00803041007410515455407500300400c500307059620000c80100280010404184086030460001340b54050040d100020f83d94440250754034064403c440015040c0140003a00c2d140c803106540c400e90448a03901e24543d58201801c0c01001480202d82c400b90f0369405d0304000c24040d0010340c0203010310f0380007180e441400900c2d04114010040214146500039002c614050702c02194035500b291442c004101a82c4403004070b035000e40148500b6030f400000c0890404148100040e0b41c4021810a030251891900d40d1018028101c0302d405611040c0b05e01202016600000003c0c903504903051000e12050094882210305c3c10324030f500c4e11880d019405002c14100b940381c0300e49041c84071902c9100801800c041d20140c40d009008500c80681400740f00407210050fa40144244041500d00a0a0354115030f10ba19007404492200e010700303402980703810701d164110014010350a010b42440c406001c2d403076440c2da03960f101621006204a041000d006a00d00070010108840d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 310644010 1250 310642760 310642769
    0x90402130b0406120b030c0427030504051002010b010207060f0e0307120c170d0e180a1506020307030504172103070806040207030c11150a0306051c051f1104 69
    0x802e03500c91030150028440c0088601011541c1c0c6048046140c903a0002014200750310142c50100d0a010140070104441c0d00700c0341c1003208941180720f44410543d00c08010026a00212018a1740c20703900700c0c0490803141c240074100c1c0542c0c058003041c04914019000b40340b85c0d011510344144158800c4020a041c848103900c101c61038002c0e403407440208082d640d5014050403281d00300710012040769805030b54540c841c000c1d14040c814894034108003a112a03113085609640104800f580c0d04003801c0c010000d00c44c546c0d988250b42c0d100307000801c0042c1302000b15080260507644c3e850a0a04005c00c1d01c01800a6500921162083d100f0400400507103a1052500c50765500b0100d40701c0c0741a4001070488a402410355114620400841000940215521200d01d4011003a52104288100450807100c221016a10011808141643d410b03901da0007841c280e4405842d0024190503003c2041240403440300010051740105c22000100d00914040030000c83c12018040b031400c0001303021a030700b035116070030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 310645260 1250 310644010 310644029
    0x3d060b0d050103150b06250204020714070509010b04030305130906030f0b1303080c0c010b040e010b041a150a0c0204020414190b04150203130f050916020d0509040213 73
    0x400074420440c12a042403002c4050174402c800c900f10000e8074501ca40c803c070f1000c80e00b1031000c84034604081841b56008940c0039008550f512141d0038240d0b40202109001641442002408129801c0100007981207034416000d460a0038219503003a10903820000e901081c46049040c0040c0317590b500c0c020600254010b00038207400380000c0c2400000c281000f032048182503c09103607440029072201510307510201080c030090316034003181101c50140c00c510050b503901500b0803410194411040d409908088000c65042101c4140101c0482000704600c107031030390001680d040102131580400041500c5450303460120940d03140c80c3d00003000c980083e041007006812081c0b15049a0404030801c0d400c1d0710700810340c00319140c541418041d10f449280034909101685081c0003185a0007007059440d6940f43c1d5602d80001e9807241c0b00420711800d148521031048070007002080e45503070400c182c03074030701d0045034013814403110001c005440542c095003815800c42d60030410403954401d02d000392800b07010001e5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 310646510 1250 310645260 310645271
    0xb061603110d09050a08010b0f0111101d2e0b011701030501051024120b09010b0c0105010608131209090507030515060f0304020409020402120106090303023d060b0d 72
    0x50500a05e800e0381d421200342c0f40e1402e0002c03103030f0385e4690140414817042460166501c0011803040e9042004184a00c2003246c20502c0100900e8480c040c00740e1401d0940044075082c3c000c0b4022140c002112441000e070f0602000215008101c442d0010b2002c0c55040c1008512140b5041c1d040114030ba00b40d00941da0759540748140004900b40c064180020f00000e25030b03089813503041c40e07400e80310400d40b000e44040c0808102e07070040751007403034202c0c0d600c81c80d00030700180081da524110b40803150310225504c003c0b5480d1800200d0054014545075004100301d43d0783c070064103010b075204550300941d015680144092050001081d10841c080c0030300c100c20310781c1c0224883c10719074080104c011041c0d111601c03600c400d000c05081612400152070380681c0480b00820b802d0101d00109000344169016101c55400030000800c01d1030f008151241242c1c46a030807100e99014941d9900302c00070f150500c240550a99884110184003031104800d481c0764a4800024919522100801164802d8000d0180300c0c0e1a407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 310647760 1250 310646510 310646519
    0x612071206050a05090c0904170c0708060109150e0603030409090629010c0803190e0304291204060b0325080708150a150e0a050a0b061603110d09 64
    0x380640e82e0020f41c010b41c20701443c10040c0c0c1464440002a211074041c441d800000380a0005c20301d01703214101040014580d586140b081c0303031512865a409412a58400c0c0000003800b51401c1c820451517a0301c7d45072290034107041004450100b1006011035505201c01d004c003103054585e80c0304480b2000e2080d14000307250300d00460054981c0ca101007441000d25a49459810f580c2d0704051443e1450758070000c036640d241c0c1e54401480365040304005010102c0c0c40c6c41200300002c040000100290b0301c4610710140e40c201d40c40901600200f0041e5000c0c426602403200d01481c03c503030b01444d504188200e1000c2030855101003c80d1401030ba40640c81d0320443c3c529401070244d0aa0394054000d419100c000d8100d550038442490b40e40c22000c820074000c440141c00040c40d6025035808640625420260741c0700031581c40c1850060303050140c071100040c52030540070a0741d01e005441203a0700810040d10181c1484009000d10244020480040d818007645030440c00d0380c8201401290300d20040f03519800d00d410b040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 310649010 1250 310647760 310647773
    0x605031605031b01020d0309030207030507080721050c06030702010b1305180309030a03111203040606050a0602030712030b120304081b03060106080112060204150c1401020a051206120712 82
    0x41c0b5150103000602e4000c1140d1641d004c06e0703500c00c41c4080d08021a80c4055803504030724004166201800d1740c01001c0c030100e2400e40c00b042c40c1c821554922601d038120a2042c400e001825840d900042c041d034042c08564a01e4184040615070005c21400002250b281f8030b404550003020700c10200f6132a039038900800546030900032212080941c1c40e40110300f000003c41c00f0960340c003100c1c00b01900740026080205a078203070800a0b80742145445502d01d8a0342400c1c9040c4020306858042c4030300c240709050300172440901c000144c0b00c13440d40200c14290142400c0304140c00514421402c26001041480510b031341c1e040c10001440101100d1004101101d212100041d900401a075418803030742001740104142903000c880e41c1d054070243c4e001808248200e142ca20004d100b198401d441c0703400328203c9040d80781c0c1c01103081c01e0348a000b00c4140d1f6a6410300c410306801c034815401c0703041c0401d1040c40662052010110042c0d4020800760110f601c3e08421140030745000202d80c0407a100d8400000900c042043c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 310650260 1250 310649010 310649023
    0xa1b180e1b060d36050d142205060403080403020f040608030d0b0402120f070806010201060602280b09160b03010e010509091c050d0e0609120706060503160503 70
    0x2038115080700c884041000400e01d10441000800140c0c8410302c0c9110a00030904085044140000408100f004a10005040d240d00c20702a18031307003c0d0f4142076140d940100703603603a89000c90700c0c411481d101c071000c6402405540401c1d2203006e8142000d000c80c0301e03140c44005102443c010354403540c5076803461041204542c034050f07002d80183e090200400482400000b13070382000100c940045080c0c032116010030002c0c01241c8292490310103441c140801d0500b20340e9010b02a1a265551030340329502c400042e4213840283c800d100060380002008009040a4004640303802c10311a0089200e1200b0b4a8041c5440030998040c034a507000030380b03445040c41c96010810001c00351001183c1c1150301d01b00e40d0070b5443c001481020302071040c540000f024a1818048440c0703000c00244512580380d402c400c01081900161030807043c90389000b80f540a851800281c03d1b10451104000740025880c110822034503802c2203908999841e1101c00204455405111000242491180040e5002d2400040600c4e152 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 310651510 1250 310650260 310650283
    0x6030222150308090d1a010b0903010e0a0c091a0402030708071805090408090d06060605090f0d02100c02150301120611070c090213050307090b0a06110a1b180e 70
    0x100078800704005103e01c026a40780c3c0c00b0865000d400f0000508000c1946c1d880e11703c0b155078000c00c3ca4000301d00820f00301c010704220704080e8020018201c01e61300140c0e54100500014004511410041104204940011051005682c2807913142c0082c10301107400d9030000d880020103d000d0390204110b666000455150310705c40703d8194080145810b01140013540e0140019100a0000548002c48c2d142d0b0b0400082050b44003d08118055035501c0061150b04641c0586104203150306501207540790800040fa4001e8000381481d420181600041d48c4010a01401f20303008003a48240c04540a880b101841c02088003080b0507070f00c40d40c20700d810f004903880351034004000c0d103060114501046540485800b90f9202400c0103075035282c40034110600340136aa2001d0b9240c46041c1d40801c60103802e03084a4144101500ca2111090b2208001e03101421010620640c550007001e40c0382c0454051021004c5a01040b0b2624400d9600d0783d8000605e0040b41003000e0986407243da245040060820880f510030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 310652760 1250 310651510 310651541
    0x10e030a032d05151002010b030d0e3d090503070611061308040803040b0d06120203030a0e01180b0901200a150e060709030510090206070f050106030222 67
    0x41c80702c02c1d282000d0a80d012064102c03550359000104482d072541c602c41c00c501d0004190841003154068001c1c00380642101440c001d00a000c0000d48850140e0f12041c0ca01000a02c4d000031311440420110320422148050300c0c90510701a65100d01c80448804040800081ea4800f241c01c2d0030003040c180303001d5056008400300034a040c01d40c0460000481c7c25600600c25520305071514107c0e0909103030502990704540098000010002901c1e02440020aa5803039401010300074640d8501990681c08400702019405030410810001c20510030381000703c001005050206102400c040d1311103c4181c00c0d041542050400602803901d036070804005003030f407108030300c4807100c001600324450340704c840d195401401d208080f0f41303542c09000280c0200380d42c0d6440008445440c0740940b001000d04e4038910058459000b5801c501024203a0790244140180e0040e1926241c00710951750025180062030058403155a14034000c80144d0b203104c2e25904846020b80032054117980903000c2c0e000c40c5c2b0941b0340c50255 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 310654010 1250 310652760 310652801
    0x203091606050322020d0507171207030504050907090906030b040303180201020717071d2208030c0702040905010f050717060a031202070b0f0409110711041805010e030a03 75
    0x9018060343c00342d075404644041d401304504244013181804125a00c010000d001e400d00118109908080c08414103001504a500c1d800a00d4842480c5108920740540020000c10003400f86091281485400000c9854140e0a440e600e00b2050112003d5410803149010140306100915a01d80141d41000c2000d44485080c0c5420b80c0c0043e5440840e132007038890b00c013001591942d030080280300351740042001100c0740340c1c04c4045040701d6240601c01c540d80380c60740945c6600800020f0b11144030010a5a00040701855500d84825500850700001006c81c0c0c0706488041c43c100150003030003940e24070b40c2841c4020846040148000c0c1401d003500c09a24a00540341040004981c0c403030b0700c3c9500304ca812060340f030320080c9030600803030a0010702c1d000345590480019400301102003500040c23089460081c010001c07d041884098080d22442101800060001007401c096146c80d900c15441d5005464008081e9075655841e9030940d00c0e190000c2c00690400f24828030841c1c2c040c0100103910700c0315010041c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 310655260 1250 310654010 310654021
    0x6040209090423030c0106060906020a0309120c05033a02190206070c03030503041b181512081b0705101b080c1b0103060b0a0c020307030602030916060503 68
    0x1d80741801070001e0500e1210841c1c07289180340203c5194216141d0b581a0382d5603400341140c0d01d0182c0b50310300c110f0000601c0a400001e60381d20110343c0740f000950640c4d5041ca010315202000c0380100a003c0140c0f142c040e100d40008044e581006840c5d4941681820b20341d40602b114000a41410b0f9002d8403400c40104540172100380e9400700d818042e8400061801c1003110701400482c0c0d480c015603200501c401c5030b594020040c13540220140d40710724810120b0b40260301d030329418071036151390354491900380c0c189403284002ca600e01d0f600b00000200e607528109001943d1042c003e0788100030910300303a420000c0083c03201641c00c522414546981541d2004281c0d8030320303060128640c0586042e104041005056607481a103521360400c80b485034000940a80382c1000c031156940720000300070303041d01d0300c100c0b90142d0b88194000d000e0030007120079115025050400e41360040d01e560315025800c0ba031600507584003100081c41031001d94040c0b81440000d055118105909522106094010000303000d0700740100301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 310656510 1250 310655260 310655269
    0x70908070302090a02040b1615180803060102120f041d27070f060807080a14160905062b1109040905010b0d050606010e0a0e070516060c030b01030506040209 69
    0x904590b81503e40043c6a44c49442c3c1134000c2c091900458030340c20000441c184208215201e103907459001c1c2c0400c4000486031362001c411507180c8008404252410461807020a0034400034690019040c015104031140c0d65080c42d96583c03000b20b0b10041280c02103424007204140e00c1e10034113050b280c628034001c2c608000c060000946a200e9040c0321022248025855170902404a07000402d0400d410002d00c6856200c041c0020600312481d00001d41e40030b000500060160040303c2000702580c0000c102034a410390000b103207038080802d540520646c2003001400d611494020940d07240408204109008e076049140084248105540c446238204600c4c00c0030120741004580b01303041d0460340040c000e0300c20316000c0d02504481800c5580060a03204e00e10510102080340c9120740700907a107412036010700300c0c00c0100841a0f030203840070780005080003a46150042008000f080030359908614012199a562007c2e03940468000d07000a8a800980ea1b655816000e1550004e50468080d802c2860440204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 310657760 1250 310656510 310656523
    0x610142106101a1806031801020304050d031b0f05030619150801060203040825090c0903060c230a021903050c0c120a02131503081b0307020321040b1207020105070908 73
    0x1503204280000207d007a42d904610114000410000207544034641410603a8a54030502c1002001c02c2c00c06d00c104031260018001c84924843c60344074004000d0809200312002d410003070025400000c251030840502c0ea0440c0c00c03d00600002c101d10707030750f5600d10f00300038000f00c010381c840c07001c0d903005000a11242c41e01050300c20aa010356043c06410100d4180702c0c58140ca2913511210756140703044501e00a89900288076000d0700e01a0106100360181003600315514024007034840100c040a4140c043c6c29202d49008020440c0c0d21310440c0ca41c00007824044060b5455003400300c1c0418800070f81522441c00c184190280c1c200111014417028019458994884545000082c82040352560600400d02e41c4d0b0b01c0b070803012924144c4600c20035124540107010340d200806640010350389201d415160300703001003150340569018000c0c1502019200e1110b00000312182410050001400081400d00859003d09121000c0152401c81410302c2100a400c458008e4001c204016802074203002c2564006000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 310659010 1250 310657760 310657807
    0x405030c01111209041401090903090503060106120b120d0c030915140a021509010204030b06030304050f09041104020d02040504180b31030f020610142106101a 70
    0x103d540c07850060f00080c014038010000c44045000b1500100741c0c00300a03800700d0380e4540b29884510a041d00c4008040c0c1d101d009100321400102203945901c10000e054018000c1210042d0210654014081c04039042c11030480c102000551010140800c0c1540091000001d20300040040c2c089045000020844090b00103040c101701c0001518a40003403080101c2100d800950a0005c1d05080c000b10840c042d40c001c4c801910f42d07032408008200280380110885080300c200518413070300c1c10070b8142032190402e8001c0c0b05031220550880c0038030701c6444034001445032030300100e4010317661410542000304035945c0c62806801200c0080c05003001035644403110341c021185c0018400003001c8410220740c109103001c81081e1000c01030b400700301016000306940e420200e098080e61040c0d078075040458139500a501c21002a41101ca4a0901342d04000c07691045411035100301c00401840e20003418600303402078404095443c1804020044c1d10480c0031702d5000c0c4954070801e18985605000c0c074140354241801e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 310660260 1250 310659010 310659043
    0x140108011a07110310050108061819060e03040b0304060b180912180a0b1b030c0d0c03052712010b0901050f010e030a110a120201050d050406020c01020f0405030c0111 73
    0x50503e59a410008880303540d0b00c80c0418001907854040340c80d1900c1c815103103280b8208601481c1c40c0d0041000c00c40c2403d500c4c0f004200c1c200306d0002e880340d80151800908001da640410440403401c0004980103502c5640220b602042d07142900c0c062045003800d052105400b01ca80300180030303c10340e001c00d03148001e010b040d1040d92244406400c0c038000e2148404050ba000b001394a0003c1c2c01c28001c0080c00a00f204501a440da101c0084c0c10940c8900c01e07102d064240345c010100000760306000300600c8039118024941103043c2901c078154a00c50f50080c0c800741e01342541403821401d451502c60454281541c0d0300000344503810003c0089a0714038018058540304081c007501e80c0e01746901c110031142d018800142120851001c50070306442c0007440320190b500400c60341d0000f08040030820b03040c12003603038180d40341803411301d400c41c01600401e0050004c44800e0340800003201d40348c1090003d0060301d95060310322039503945020100f40c68000c41002c0076050001e2081b610340303403520100f8080052160000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 310661510 1250 310660260 310660283
    0x50603210c0304081014040305070311070b03040311014b020708030912130b0901030f1e0b1503160302070c0f0608060d11060f13140108011a07 63
    0x15a1030555018a400000ca544404500000c0707090780001c913911a440303104401c10203541c5420352540b541c14105d030003401042080080b480042e00c0742064102d158085815260b440d5291105031140c0d600c20f440540c0010303807110354020400300038410000c60204402d150314005c1e1009100b81d40251440d441400c021300c285041c40e400c0d00c0c00c4c81c00541e0b40301c0440011950382c2c09620301100700340c10581d1052040c2c03003a0010b82900300d503804201e0f4150403283c2040e0420510304180182164071852000b41010303221300400b0320502046c007980c5085410401a040d41d2508012003008542c4444503c80c0f01d05650a42c00045284500c1280d40002100c0c1d2640000021004103901a01c502e181c000e0620051500025156078143d02c0203040e284a680c8040c50350315118200701c119509400b0160000d21030204403002484e0020050844228102c4210b040014081b10700c4e0903456a0350024000da250190740050669002803580d015001240d500c0005031040c00c043c3d02c0320700030381900a10252002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 310662760 1250 310661510 310661563
    0xf0f02031f1d0c011103090402131509080a060203071701030303060924030f0302070b0d050f07020105190b0d02090109050708070f020d0c06093306141c0b01091a04050603 75
    0x600845054540290080d56594990f42c41440c4282040c451888004c54980d04bc1c81031621640c44402100c0f8118024030048402c1c0d1243d078000d50014101c0070a01c0395922106c401c00c2040303001d040c000c5000c0d03280014541d103000c03004810b07280696040746aa15010911040f07461260200320180d81d004004a0341c00540c5140a80c42e0403d10340042214000110b80c0c03007140c44154002c54407901d0418600b194a403200802070703080c0d0780155560031003201c2c6a00b42c560180050303441076203c8000102916a1079003160040cc0718178800381c010001c12501c6e0410020915080724100d9040920741c54013000d4a0321440000703494480d0b440e024400c0146640e000c405000581d00000041504190400648050001f48031040044940d2250003404280003408456106104200440d0140400f02a00c000d8201c01c110001c142c100d03c80d501d400c0c8048101d00071840b0040380728040c0135800c1c2c0000c0e5040c10b080c4503103000c48012a150303100d141414104102c40c1c501049000d4410142032001e440074001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 310664010 1250 310662760 310662763
    0x3010b0f090417090d06091106070b0412091509080601060e030a0308060105091315090605060904091e0302151b04061206170c0108150a030f0f02031f1d0c0111 70
    0x68134981da500c14561202c200a0243c0c6600400d9050b11407010205a16441030500c002400b0b80e107400750a0071213480003e408240c10480076506140c023403809106140c1c9460740800d40d403030304e101403078009000c0e000103105965081101901410380b40c208072a0001440340001e1b070381d5000e00340044c10004148017060042e4003a00a071421100002c09178400c007664200c0380c0307000b080c40305158401018240300014001c2d500d84908000e071040900518a0300f2002c02c05d00000d401070300c03000c580341d03001801014261003a8060b00018a40f01b54040d056900c07070000036461515001c0d1000104001a080b0306001c0c0a40c402241c0840d440c50800d0924622070300710b0745000f002d035071348081c0500c01c0c0d02d4990b014040340415200d10144098842d03043e107882c0c81d05000020383c0b0803421590810310811080c0046241810704281991240c194484010190382c08a42000d404401201c10322105641058203e40765000b6120b510440640201c0b16200c103080c031594504002e10f4440c14400c0d01031010307058010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 310665260 1250 310664010 310664017
    0x71a1812030f0a031107030333050618040e060103020307090209100305041b0314071d040f0c0305010c081602030a0815060c0613020f0603010312080c09180603010b0f090417 76
    0x445c0c0b48143c448000741006005400d810005401700d50211365070285031000341d0b488035107140600c001070b40306c0790511040c01243c3d8080e109141c2c07c0e03401000f441c409550340c3c0c0526500c1d503814102034200c6503d0342c414146441c2e660703085540c1c1a401070055100d10b49400320580100e0300da074900402e09031640e0801040d0400020110314400300500c1010040c08041c807a50090900c40a00300e502c140e59820a034441002d450500b503400843c12400b082c040389910301d0345600c01e400b441e401c220b01c981e079654080c212042c1c010074401080140c400c100019285041142d44a5940d0014520300040800c0c0205685401440c0190f1418061b12071a29070704d0384401d541101d02603000303c80c03040c10004c44141c82da8a007007500300e100f00341c003c052100070304109003a60b04030703075001c60352450b0070728000340035600214000c003018092001032004c8940340d40c40045039041c0400d039401c0d0103a1402c10209041c2075a448120b000d004900c02000d41c0b01035141c0c0e441c419806504508850b1100d508502409414032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 310666510 1250 310665260 310665281
    0x2150708160308090309060403140102090a1211090112060c030f02040806010503060c041a030606130b09040510121407080f1f050601050904020903071a1812030f0a03 73
    0x440401c4084001010707480046060b0301a4070344070003658035070030007580d00e2190440550300240700388030800018030b003901101c8020400b44000340c1003a0700a40440c200941075882600c124044100b41d5003400080e014810030010140d407140029814600c0700101c2e41c48040005020581d100f8a0030410380c8242c2c00300e040c0b049880400e40d0360f00e580d003048a41c0c0d01400e000d0184607028480c0464030f003512803001c036411203040d55000d0042c0c0c1c201071a08880d42c1c2000702125041b01e400c000c90070240300c00c00c0e100f501070444031080759102c0b0421002e02c000c03280001d10341c0c0c030388683c0440140260f032281e08003510b529a00001a103040181e1000d03803801e01150f644040c2191141441072034565070007081c8c0203ca050b19030b06130005910312001980980c0d400790307026030106004111560307071030900340c005011410001e07040380d44040d511083c03042501c40c109900ca40d900d0002c00c03541036030007201e0640700010790101c8800c0704e820103e164090b1288541c003a4444842c000280e90403121703001c1e4100b1700008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 310667760 1250 310666510 310666523
    0xf060d06170a0203011a010e120f1c080601020a0302061308040504060b0a1e17070c1703010f090905030f090d060c03090b0117100f0e06041a01060203030f04021507 72
    0x8028480000b0b80d10026080c080344203500303041070b00d0140d4406c0386990450800c140c0d1303810b110803290300c00d00514102d45000816240075580c42c100c0681e5081000c0c541e00580c0910032810300020420060000502070b10f0141190020003140021170341c001035103600002c0920745075018040c586000c4401c1e11940e80301da500a4142900041c200007203070040c0c0203001c110b8480101840d4003030b0405ca019213400801c1c44c082125642103607103c13030354084e00741d85c41a15400d0980010135035445480d40300c02100c01c1c0301c450000000c01407000d00d0044091900a01c0c40c404140030711403141c0d4031251a801484e902080c046800300c0c8040280d914124503503030f031507000101041560780c2c58070001c1c00ba005d041c40c152100c0000400000b250724108030f80c404a204600068010411900c2030007001c2c1034082c0724003800c2501c0700308902d000389092020b20b00591289020702081a8501d80303003494a08140d01500641d0414010802d107090b4210030300b68826030403a0392001c1c1c08100302034480c890088200107003c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 310669010 1250 310667760 310667789
    0x60c03090c180a150e040b0c0d1a0f010c0314030601020a08040602070905180c090403030e07060e0909010606050f07021c060e06010f0b160c0b07200102010b0f060d06 73
    0x40b50b0700c4103100740540d10408041c8818070102000e24008905881030710880682c020000f00450303d000002c43d048a030303581c0b10b94988512144000261007215210040303001c1140350f00c030b070b540c680391600441c1e0150a081c01c100c1d0303074400c0e1005402e690580401d0840c0d180d00000081c1203a00c01d01585c110980d00c0806030b501d49072140802036a54113140100d65809181a000ca888071070ac070074070031f8541105c010080c240800300320140803230300780054411000c0c90f03112031030000012420310100002d0039040c0d40301e1448901d00380421500344805460184035901d010300600000d40e2280c1203c07014a402c00e100c0b42d8400091010450a40f114161000850354045404080140c150480031102d40040d0858954de41c94003204501c0382d41e030380318140040c0320420580c5a0704072401200010140100c2c175680c21182d546120f58503550080c0000c4800301d2504001001c4549608803070090010b0038402004403842000215070041003210501d07109480216580082c00700c01d4200b04027a003241d00740c4502 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 310670260 1250 310669010 310669039
    0x36030c0708010f0b0f0105070201140d09060f0912050a021203190e16060e040f05040b06011710230409080c071e03081605010504050c0103110903060c03090c 69
    0x40312100340c05480d40740e5081520f85610000640030b0348503000e10040c4480c4111513148010341741e9601c101c038100c3c10b01819003a4030201503081400f03003102c907411705008240e2103458a821002c50309103000c1503454030f103841140000f00d10340780d41d09800c030300320fa003081070f07907203030480d078203174038008649000d4882c81e0000000c10180c00030194040e40240607521040c08000700898081391620340ea8214110045007403401002081c0c41071650341010a0080e00c00100408100402c40c01da5400f250161005105001427207407a59000000d01500540322045030a1400c0420340c0030402003a501c02e40802d50b51080b24850100902e0304e40c1d81100d40700501c100408641842e0002c01a0024142c410356406811000038906400c0e4101c1c2e52558050100d80d40c03500d0a5940d040383c03070340041d03003580342c50443c00e480701002550922500d4022409600204210003a04000509880b00b40750800c1d1a04814400000c03036480c0080c2507504801585001078413542d480e4042c034502071106041d6a801000041f1031007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 310671510 1250 310670260 310670263
    0x11060918100f05011106061012091a130b0a02090604050405091c0207060504050d060b0303031014010f05090103050a0e1204030c051c030c06110c030a030605030636030c 74
    0x400700c40707001240d00c4050359901d00540d09401c0d00313101e460003174120b40c001440301c2c48e11040c86645032005082092020160412113000c807490a03000301c4400c0c1680844214600b4074143c040e1340701d0582d41c41030709100220b80ea9201c0303a00b0702a00608103140c01242100355603440394242c8002d407101801c10001840c20546540c0c1d00c06030030210b10304680e0400c031568010351001c90010141c03003054440d185494540003e009460b20f081c0001e4a0740c0755035140e6040030b5501440114061181008a15409400c2035030711540c1c3c80004220328180315642000cbc11b034068002040c0c60b580f0b01c007401c00180c190f540d1000c07007000e01403040300441180103800d081c403540d030800c0d0b01410540c0d0040c8083c44800e034a503010700011112603035400c1074480720300a0000000348a0303070801760f00300d02c01c000104801d118000210250741048003107103c1d60304040703081410b03680d141c4224801040c00710010300f03840c1410841140c005a40d10f2091007071009660070090101b4400e04824107465408046a0740d441d01484401e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 310672760 1250 310671510 310671541
    0x70509040e030c19020d120f02010f020a090e090708100903020c0a030c0e18060a061e06050d0b0103020906130f0b19050a030f111c02030411060918 65
    0x66104915222080848007000801c0d2151010710720010041241600c1c0c0c007902c83d094006080303a0000801001200003000034254000840491300c03003e03409816414013909450011140c140e4480c818099607041da03900c102c205e003c0310790074844101a61521003019081c503196812107100c5220300d50a264440b1241e620107602c01d8025402d90700c0c40481c060401112079003d2101404940f20b1810038443304040c4441c0d00d402041010780d07141c02d8522b500c422418144205c0308240321039600d080400050100c052440d080c0045801001100c90a007c000741150192141d031034011581c40f4038244403640a50b0407144121001860340b62261418102a50180e4850040450525061000041c09410502a10104c00d411001841c3d201c40b02c0c40708075459007107035003840c040540b034050f090686210361281d15100f00882d00c0141e0303524207441215203030560350a0100c0b801441002040040391314a00426010b400459800d40c7d00ea13050710001d072520152a401b803002040003410b000c001314110028 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 310674010 1250 310672760 310672777
    0xc200112020f040614070f0507091d100f0b0a03140f060411010c0c0b0a08070311090a0e091608070f150507020103090c0902070b091018060b13050705 66
    0x214105600410303940016401031104494000e0000d210034481903000d400c60030040905103441e107040401d030f41c4407d0f0381c0f00e00c03030001034510782c00c55501401850300c180a042165400400c0341201040341d203808550320002c5100c4405011743d0b4010004402005820000c0c9000c00207114001c2e40b034403402c1c8071003e036100c5400c40e00544610700714500701c14804200c2503c100e80000c0c1d0b082031542410010364000040001c100d80e86500f00901040e04032400380600300b845015590b5030b24600c0c1039a000b4003100c00a0740e21000c103260510409150355200c4c184103098400801d80644181c40784d14940d031800211100e5540003030030721140841c440350f00040ca2004c131410380118803d001d0340d900000c81c00340e9500c40c0b41e20001d40308106100265000e6005527400d144100190030f0341646e45d50320b2004a030460348080794403420030390901041041c104181d02003040d41800c204240f000c10501507110f105894402000b16481d402d40c44d20310f6480c4110001241e180c01410311062500764001041540315821 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 310675260 1250 310674010 310674017
    0x206060d0312140a06140d0803060d060203040f0201021b03070506070809060a050a030c080403120e25052e120e1e0d0806060409181202070e01091b0804030c2001 71
    0x600003200300041a500410342c1b0058404210380b030040d225291540d00007446c65030403000304410400099142c0c03004510560144070300d10f003a0b20107071000a05102c403400d50002460304400c40c000b280c2c1e4020400c0300460f80704440080d0350b6440c5150540f45402001c00031a0300000100e014210345030800000c20140489070750400c140b080036103094549000035503010300083c4280d900c441c0046c0300707030784907042c100c00c0b02007202c110084035600041021641181c5110303038a6254410400c03811300a01d014005818811520200792911105000c0140740b04030305820402071100300700180600d0b034030009501c64500c080d5040d41d09507944074000400d8001c10010316110b012020015a4480c082ca1070003894014a42c1d4a003905e00301e96000602518504400304003100885000020902550f8450000441d009094020b1401c150f08440e520141d1164410038180ba03075403c240c0c5e60f00301240c44005ca0b0750030080040d4455080c202d038a01c0000c4801040c00c109820151908100b030821800c59010998 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 310676510 1250 310675260 310675271
    0xc030302160902031017150403030209030c040504080703032f03070908010c020c01030b272505070f1a0403090e070e09010302040513020a031202100603030206060d0312140a 76
    0x80c040012071004031050180652170748400e1014100c500240c0c140a5520003c0700c1c41d002d561100d20b04403260503030b0704a001c20b81c00607241001d800c1c248000081801e04030b8081001c0d00d0262540e5126200c1c99030001c0406590341c400a0f48407850160f10114907069591258082548840c00f84107a44295428404214501e1001902003014018160b400da01c41e4003902e80ea0100200660103031080b209029030000d10032518980505003050300322400b54442051200e2130404a40803400b172005400d50303030303002c100050440708415007250860b000d560f4010086008035805083c9801d941000102200c8521529424032003416030129034001030b00c2030700c151030b0443d4840040507580000c4080e41030390404a4000104054500341c0d00c4107602540d0440740001c07032220340e40020303124006c0c0e42084809081c1c10f000d203611103504008401080c1e1526400708003c60650310007a5445000928091150210a42c0b0004061190300403c94210000c20300303009440400ca000c400701d41c000c40e00c1c0c181142c50720 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 310677760 1250 310676510 310676519
    0x60f0105040506030a1202010e030c0c3f070506070b1503030a0c030e060c011409010c05031003020904060e1006030201020606060a0801060f17070509180417070204090c03030216 78
    0x602c42c2038020b0b040140140361000c4a40da40d030410241e0604a08295503030fa1444c1e044540050004207030b088090800391041040300030421100203251039010311076040d000c5a101c0c0c60300201156494107218034280f10203c218800b4060301e00003141d0081030300100c011800e0381c01c0260300310a403802a55101a100c1c0018541414940d4038045c810040000803130000d04200032134080c48a0b950b4a10026210500e0140d0300f40606094a800703c0b08940b218080c0c000b0044882000e11800d80400b1302450420311390700b08045400020070490102a201e012480085000c0105035800380c2e28000150094030809c4c43ca11381c441006240512050b4094003c0200090b0180750102c210b03000c60180e521103492036424460101d0b80c549102e981c6030705100304494804072030540781916610a201c3c0e43d44099840317251409112018000c010107000156612080c000003648101c5440550001061003603100c038003500002c0c0141001030b8002d484407150703034008014554007007030038038482c0c8450640071440c0da80c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 310679010 1250 310677760 310677769
    0x70303020c21030619050306160206070201053d0b030a0b060c060703092a060905030102180103020906040b0f07020103050f07081603020d140907050d03090e09120c060f0105 76
    0xb4003440308518a003c100048692600080500400510613003290020340c0320800701c0e1508805079a96400300713644000c40d03000d2990400102d40d1140c0346e40b00922460620b078581050080c454800d00014284241e0015540c00c20030030384030030704031540d540034203019a102e900403815402600c4402c08107042046000c11801c1c414107c5001c0e2070518000c20b066620f03403030210020003a09004031f443c040f030b00680f1a030415120030143d031040c01c480700843d0024500000274160340c10740d034881d41c066401404050703800707003607800c011864203000c0c02c1c056078982d69100098454419038202994004001c100001000310190280c6107043c1b00383c80c100201d0b12446c01c080310402c000c8411000213000d507400200c0715042041800c0c403141c00707820003504003d50003150750192a80d0012402c1a8054a4200080000104021001090107844c242e00000703064400030074105150182600360316201d07010410840b01003180c5441d01010614140d01d800d864070801e038550300160b07001104011a000042a541361 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 310680260 1250 310679010 310679053
    0x14100f050108010606230417062a1803100c0801091a0319020f0d030314010b0c0714031501080d110c090f070306080d0c0b01090203010f0623070303020c 67
    0x22070301d0720891200d2144203010306c011000b4a07510222002e000000780d0160881485d50a907026101a0405180250103a030081c680b410402198130807940750000d0984c1204100c4521503802c21030914900901c20100385404414001c0b8001113240c403501c2003411364030110302810b9541c2da6030700b4480d4501b548010300c3d403040303041034003945500480340c00782c0400203104a10b41c100d440075101d00128108500010b00070b8103c10000d4000c40e403600c64034040501b0a0703004034058411109202c2c2000f01c01a4216a1002d403030140b6100560703c00000038050303030208801804040c580b4000c00456844a00c82c0f91200d000402503000304071081e260141304a0701040301c00404a000d4070214190740c460080680b0031002604200600d07030343d03240c0440d00c03a100740814504000c8684a1a100b43c0840c03a181d54840b005901480045205000605c283d051003d4480e0480c0c031035243c4074ad02d2a508030414082c1000420302032a020500050610805400d50042c1c0139000b024010b40d5910320314881d0303107040c001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 310681510 1250 310680260 310680269
    0x6060609010207060f0207050d15290f011404090b030f010b0d060203040f211223040201050f0a08150907020c091503010905151006020a03080414100f0501080106 71
    0xc004030f8080c401d051164030221001c2549204035203000b6950302c04134061044424050750300e200168852003894001d401284002d2141a01c1d140044100401c040e900308400d1b41c103948a100d40c0244c440c010380c03040d0013030b40350000d040b01c3d120303540d0341c0d200f4600e8002d12988886500078060203422200d42c40041c81804980c58002e0012060301d0f00d01c0e61400300035840104100c48800c0200001c4021651000900c1220506408090711801c42104003825810401080400d92403d002c0319103950b1a2110082960310400c100100294a41e880107a496015140c5003049030400032452403a80c90f88065420702401003035292480c400031190901c1250342003110118096070000d0740841c02414550341c0c040d40485850109014503005000003825601c03d6041500e423980036121030100200c0451503250408031414511410318030344071000e92102c040d40c20150034800103900203420f109442518020301c0001400303445204940107640001440d4030314445103814a000c00201d91294144116400e46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 310682760 1250 310681510 310681513
    0x9030d11060a0c0c0f0c0501090b0408031209010b030f0c0a0e2a091804020418030f030203100509040f050114010b09060906091507140601031203020a0c020603010807030302060606090102 82
    0x140e46080141c03001e0030311445214200b001800c4d03c02c01141015a03002d41c1c040c03044110302d03417941c907010004001440c550084503410000700010007641c0703c0003044540c100302005404000c1d65403031014600501504102c40e4040c004c0030105a464900400c10700613100c011140e40c0c5d40704d5141c03584a24030740801c5542074011182c0410300c6500d68503150181c03a540301140d160910b0030b50a0380204411903262114003654166801c240011403405024041e94000c0707078240403c0e2603a840d100103020304650314029003070503030010204022140c011204000350801805400160420349807440e400c100c1150141c034113500e0620100304920b007034141641200d54a6000700e0401c43c200c1d08014040d88410609070b070042e010403507582203403111808072580700b1441d10595210f8540341000c5025854901c41100c5a801140041c00091300c0d46104007002c50745864011b803220034401c01515513070051000070303602c02d10220000074007240000301364007903d220b40e007541d03003644802c002e11015014140c12180503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 310684010 1250 310682760 310682773
    0x623180f0336040c020c03071a030c1303060204060509040c0801060801050f12060901050610140f0306041d0c030708150103060509120a0201061502060613020918090309030d11 77
    0x10a907a620000001008121090702e00368030000607084035008160140540c010008034940f914041c0040d800601454418889030f0705800704500c4c1c94440184404441540801c0802d5154200f01000c0c01860348060115a42c40e129000600190071200071948075501344280ca440480c4100d4406048a07900c0c0c494a100384d00b0002005107101b100001e5540003a80e061400b80e00d41000c2101d940190ba03200300019890030414107002c1000e9007241c0c802c061040c1c400000c26800440c400b181c0c01024600d089540300c0d2952000034001e401900b50900e01040011a1502c0b00c0d0400324001c0b01e4104118100d4000c80d40da65038040e02c1d0001c0b45107a98207042e001c001000816020b4000d82d40c011818005e607410412100c0081d60290020b28041e4010303992540c00f030258500440c4e0010006460340014883d525000d40001e1048210046241006401082d22201c03522060509039151526412042c0e0300e00e0701c45011550394018031850340c828440c1c00d603401c40e801c0c060440444000d04100c0540310 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 310685260 1250 310684010 310684057
    0x40b120123010e010507060227181504140a0f061710020c031b0f010f0e19020f060a081006081909020a0e0103140f06070c0623180f03 59
    0x10f03d000b10b1a41c40f8184203042080c8030000300a071006141d410b200e0b000d068154203401c03200781c064603588a005801074071038040502d40740ea11075146ca5480300d1081c00790306880300d07075401140c09003030b20900e14400c8901c840b080c4080c01d50310360419000010700341810800c245d80e503401002c4951400c80a030401d41c1002044924003603c43c0c009100e916580001c81c2d1030444050184404041c0646085065070480880750340f110b00280508444400420020b200c50b10580344072a480301060103c141d1079400c240450021911415811180290000d10080d11089c610002a10303410007122108900403020340302103481340c00386a090307004010030103041a05803101071211004110410303050381e01500d0910300203a00700100050302d01940c814440071120200382e00c415850049100b96052a640211080105e1641c0c00040700da07005170807a0703000c900009680321280481c03403070030b001c003072540d07400c40403c44001e54150010f001058800c040b07034102c81d80011496100d009600c00600d054914190886c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 310686510 1250 310685260 310685267
    0xf0601090b0a050708090a030b0406181a040302070305060c0a1b11010503040c05061b06060405092d0102031003020a3305120708060f0303120f070212040b12012301 72
    0x50b100e17200344c400d68640360b00c43c000503050644c15442250340302c41001c10882008a02e020310301404a00c0d41c4d0320700442226070756060400e00c0a000100300042080300003001d15100704a580c0c015030300001a64800d081003041d82000383d0018002c000840d0721403940c0c00406039810259401e050704400c2d440a940c2e043d100443e1103030f01c00381c011f49135104180c5022176265a440e0043ca03042d10000903031050801c5016a003818400010301c142c0c40f031480d0108103e00ca03400030a01c948108000803d080c40660180e9814240707082c4280d600c0290361002c802c03c40b404074803100390700990307000b2a07041594990310042d0000000d100c0443c04007000c00d140b501c18480c2050143d0700024610717401c1850402c8201c0d082c3c00f0305a02c0c100c1b901c000040d0404280700c101d00308212008020a010ba014618051452550004410000c0c00549504140100080c0c845109000f02c004d06103803400a5981c5a07070750341014071180c0050310325440c440940310000a032001c2d1100c1401c050003980032a90300c992041001035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 310687760 1250 310686510 310686517
    0x60e1e010f1202030a0b09130507092708030906010b2b0207050a1b2309041b030c0806220f170403150f02090105030a180c0603050f0601090b0a05 64
    0x9052103210b1101c08000b00560000d1803250b2483d41002036880b4820301006025000602103401c0d8502d000440c002144001c00c4d1081a5000c000c004100c420080302e1141d1031030707406041d07482c503c02664046010040350400960141c5000800c84007a40d80303400000307015110f2150038900e02c8440c0d900114040740da12000d9064030001820050408010b910f860f41084c07030050041701c00d226141c40c100c2003806501c0440028140c00304680a44250340b01c441c4a1000c1d0085049114080f200c00040400c1071501d00030081034407445101040075928504004ac1e50b0250141e00864000e000002d114009601d8021214010742c1524008a80c0c0b151a008040b841c01c10b0240c8204140c017000001401502c00204019441500b140d0758140e02031070000c04030fa40f08503801403018010801c50722140c0e4000c06694102a01c2c030000280302d5030007180d00356103030800300c0010700c12401e003d00011142e4040e84103070720a01a4008004466071190011030305642c2500400d862000c2c28000341218512a43c0031703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 310689010 1250 310687760 310687787
    0x9180501062007090e01020702150313021309050f0a0c0801090f15060503010218010912020a0b0a02070302030604030e102d1b0f0c12050303010302100e1306060e1e01 73
    0xd070b500f1a5261002c0c00141d078456413003110141e4000414008500f85507804002401507410520704600300320040c00784051007200d0207841584404001c1181d00f01d40c1e0312005078550701108407003032140d015004984440c06440d0681e03403403e402d00d00192100060099000d4542e101c0c80031182c074003155441a0f06807400b141c103a05420390301c40e000710300740d202480202000714415103099401c040c1c40000404035510b90300900b44659200130302d9070041c0c0380d02502d4402d80d0341182a00340c8844096000b21300d01402c0c0d070310280d8940301d130506000a1541186901d0305200084e25012522032040c00181c440761602c1104041e001c0048039248007640784143c407a0390b80d110710f00d13140751003400348042d041043c0c03800d02094404180358030201c0100324142c2045401070110700103291100d15262101516800140310290103400c1c120400940e5920032580358441180080842858440d000c5594004140c1406880045900109800224540100c02c1418115240c51809894aa0100442e1848204400e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 310690260 1250 310689010 310689013
    0x111040b03180f0f0d031406121002070b010510030507020604080306031608100c0c030c11011209050109050c04090804030204090206070506010e22050d0f0e0a0303091805010620 78
    0x1210000840c0c01d1081c0400d4030740200081c030003064030613520360612500c14045400c2c1450802c04000c0f40800b901010350040701150042c20076030442c50a0390401d05448029203806100103410010802c1e40a0f0860503190143c55000d000c110000041e421280150752a03c00b60b80200c00041c001050000210703030107800982a41c0d14000268441e03031203071055421141458008402c2004c5c081c3e441c1c840c2d007802030268900b20880101c6a240030f04600550303140500b05440105680240f80d0145074401d4400d001050100072403680c90900f6402401c000e58111000e0264030320000451401d8054110002d42111900d45454510b42c00c01c0000d00080720100e801400600c40c80010070000d1007014000c1445024518461800f0603060196041d0081d4540c0c940d1964404440403038000a919006d0900c9420041000410f4000c1a1114103000c82c1a90f4400d0b0024008020580e000503000103c07402c08081c44c0070b010306005c0010681c0c074240a2080001c00b080801c022303074244100c2d8070000c40c88240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 310691510 1250 310690260 310690291
    0x312150504060b0306031b0604090207051504150b0a0521010b27130f0803060d022205061c02100507023007061b061e15080111040b03 59
    0x4074007912810ba00040741c40202208000d46424284000c4410030b0414440f540505100c40004038540942d0040302c2900390302180c1c8400b004810000d144404411400d03c00c61460710749090f0a50b0341105060b001d556007007180041203810000d460006035500184079800c01c54288003044031444260a028a0f40d640740c950102940e00c681c42c00c01c0c200d03c925141d20202215006140c96880307000741230340d00c0d0031b5640000540401d006100d4204080d0b8000011503594940d00000f60002c0a0b101d40a5480b89002c45502c04d240400c070001003d001910505000d90381e031b58401c1200b41100b007980b9107660b011940d030b030900501d00321a0700101d0281c0c80c204182880e031941c02041514038001d0303014603480c1045170040854503421058403001c2f4a081c006045072428174900070300c00d900f0304260142d80341a50902130108011178200c0104228450303d440c200600c5420b030031000d44a01c40c400d644800040001017482e002c18014140381100340004540380ca8980f01004c545523000400c0740e010b1481c140d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 310692760 1250 310691510 310691519
    0xd080f07050706060f0e0115051c0914070b0d0f0b0f060c0a0b160e03030702030a030e0310020309010209011404030804060e061902070602012f0d06080d030e010f09031215 75
    0x8031160024206c44098402c0940c10014101e104095094540f418008103020303500100407000d500503200080c015020421103880e29007200014040014058207006d40c0b800070071070741b00d6a405030400c0d040c110703024405c1c111404005022030302094015500322102031032030003542c1040001001304c0703d400000c8540b408560746504564038402e40f8031803a4900c640f404100450f0b07000e65598100241140618a409074030350000365500c48260f001414010090741c1304a040c0d4084c4850300213a4035102055503a8505036030390034001c4d031150350301e503010894511690050300b44c0c9000341c5041d41d9026903414034050501c001a42d4042c494034443c1d5010700300b040311100710901038900d01a081526001000300e142410b0020342558040e040f9803c03103907907112204107a0140c4c2d00c01400d0784030b40c4508030b5070b6403415003074800d02820858212001d80e1081501d500e0b400307945684010802c01490000708101c507091003007801590340d00200074001a00c00210615840da450380854902e443d82108090705e20380c0d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 310694010 1250 310692760 310692779
    0x603090c090a0605040b04181403190305010305070602060403020d140904090f02040b040b030a0609081201150f050703050405010e030a1721010b0f030a0e0a080703020d080f0705070606 81
    0x480b6000e407443d4a48008020500b054003620f2040b010489090014502109084044210000c0080c09200f20726020b112507450a00848e000729400c0c56410910408010002e07010704001c0c4411101842101000900e0a04c003180090007207905902500400302c510764203c649400e16000802003403010007008606540e68031800445078405c91250064a4560040104840306c00d00c032203010741d00341469084542c1c0c001c00c810082c0b82d408440010f8480c407a041c283d10b140030344280102c0c0c000103c000464042e20419691090015503a500410042040300071501402180c00050200b1010b0009104540c040c8610044841b4050115074180d00c0a444507040040485006101500c001030b0ac45c4020800340100307100000d942c68160f01951524038103103400c3c490712841c000c0003600840414100b0744250040e4240c0d00b010310464113003500030304052045c0d41c07013a10b040780035100d00c0043e4241d05000d145601d01c280000c0e0302180082d9190386081c3c641c0c3c1d111403000c4030003079034521011604891 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 310695260 1250 310694010 310694029
    0xf031806040609060507021c110a0c0b09100c05070504091b0603020d0b032407110d0e040b100f1101020c1b030d090b07030c08071211012003060603090c 67
    0xb0030000c01c00c4100c604110045603400380c078202c11908035141c154042d018001c9220800140b908e405049050640c5419090a107030740c0300141641100400003e44903500d6000d449508400c44071103030000d41d400010388101040440040040e001440e0800c12440c20b81e01003100c150082581e4030722072101d48420040d505194000b0000f01c3e6022036041008041403250449881c0285c006140b88407850620000c200c01c400c10306080002c1040c0000d51644c8100500da4000000300c0803140c803e01c002c00080c02903e180907075180550302d0420300241c0c0e850320501c0240c008550780c86911003428110003c40da0940390701004466903400304900303d90403e0411409181e0001d100501120585031403c040c10728100300001c2d8200721002c24107004110110b42124071140d8103080c045a10300c45454100d00500071140c1c080c000c114034405840350a5040032480503040c050074003c000c113130810142d128002e49040f0751240102003c0c800525070703040036001580c11402000450300020012000030b15401e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 310696510 1250 310695260 310695263
    0x20109052206120302060a110903030708070308070c0b0403030504080f0409050f01050409150b03120301060201050a05090d170402060d05070903120302040b0d24090209030c0a05060f03180604 84
    0x400740010895028820720015145604400450030000d85000350303206405480c0c034172410754a40700402c8489901040307a0342c0c1d402c042c0c1940e8a820203420300c070174103400c99001980450701c0c01001131040340c0320f17401040c180c0f42e0200414165440300d49040300100401042101c021008028214100821401903c001d06a118002c140c40c54400d0725918401d0f0306074445030007a82440344030400120054030b800e0b00c5034070b400350000b441c48141e0f00007468034083d0000d009001030008008100740380d041d04560703c0f4058010303040c8900e8442181465507040d540c4080c1c40007603802c40da518500d2000c443c4564115000404081c00c0c4800d4520140880d0401d54541c008121041410070803c0420b030f440c0f480c4070f619030070110700709850102000c0003482110b9001c41c00d503650301007032000c1c140d1840d5642c4060003411140c1212607110400e40b4000d61224000922a2085d03120804151400c182450300f80e0740c029202504108481500f04803540000d0800196002005198000c0c0c1c04100034061145 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 310697760 1250 310696510 310696549
    0x130f0b01060801061b0822181103070c03110307060219020d0c02012a06020d0203160e010c030e1206090f07090618021b060f22050a021207091109010801050607030905090402010905 79
    0x344040f484072000c2742c65003414184140f4003401004401034208000405543d0981010005000700228440c11881603600003800c8620104103a2407144002c0d40c0c4a480b90030603002c4030f41e03800780c0020039a107400c00810000d00088802040010120405074010012940c25040304188903241c1c0d81e60041e0b810107330941032280e9000c4200300702282080e02c22800d51030715090500d00c1e982c20b00002031101d02c0018000c3e0500500c1ca40014594442100507203ca100c0801907444506040003000d131104800c140c041018401c03000702082d00000f610490342100d5403443c0c50324904c18101c203100301035000846200c102910040303204481c20720500c081b034428440c145260781c07140342c010400005503124041602a040c02820640700080d030020703170360680c180c04403500e258224002041a241109035081b801050307040c0000b208003542004040c080110003604c0318040350380c07100103200e2700b800741140150000340c40d03a600300100c2c2004240c1c04e07041401890034800303040c0c8800c04940070283d8013042243d00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 310699010 1250 310697760 310697789
    0x4030804090b010e15030f18060703060e09030a2a080406030606030f1e050c0408150402100e03460c0923130f0b01060801061b0822 58
    0x191380c8588042c90000d4101d45004048162204080b154000180440d0444144502003205103a034080100000142c1e007084440030b1400b100000c000c4e24452048101107500c00c030114000d41c401105031000c1c10855560714400c0e4200c00d040c000003400e40c4510803290003100301c0903800708807030400a101070b0841d0385000c40c00390b103021002000c0710500c01080c0403443ca09080036541c40c0109143c00314903100c90602103559200d0355484180780c13140d0350080d40c0d10b02c140004640d11852045d0030a200d0340c003c4070908591707905007400381d1f08801c40d402e2047e4113800c6001004055080840d04542c00c0d154030401c0c41c3c00c140f6905420151000c0a01c02c409640e6210100f030f4100008803000300058031904506006007a81880391b600b8030145038403c0051405500009002c09910300d04201c8001c1d0840310303c0413400401c1c105010341142c2070041800103070340c10001091041c0540001014601c05103a4040e480d0301540341c58000b5042540703081c3d5401384030a0100d5810340c414071100007038800d1290080c41c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 310700260 1250 310699010 310699031
    0xe01030b0f10051c020109052101180b0c0c010e0d0c050c180c0d0f090b1f0e010504020d0e10020d0e0a110f22020304140a0c1a0403080409 61
    0x15440300501042e0100040c0009000d6904c0d02444a1031080c0c6a610a01c1d6180386840107031055142d64002580040c81030580f01d00c5a2000c00018610081c042c0c003c10000d0040151858030b5a40c4d60005025020303807002141301e540c217035130050144112102c0001001041c004129080c202043c4003400080c100410040c01d002e8140150191102c048440410f2101000307410b099054005040c00624034012900e607204800a0300000e11807800c03807c0400010340c29207003410110780e06450002000741d405040740e06072010384c1000d42c00e450031080071415a0f13290000300f1001e50300100101d00b009841d00c58000600a08001200d43c2031003414016840f030100780c0842c82140e010205c20035840d03010032a880f010880700682c04003184020749004800305040c90100700981c00c80078141824084400f55840c040800e540070310300452044034280160001481641c0e038030010454050852070101200308000b01c840401c9054a8261100d0181059582d807a400b146810580c8440802900c82d030a061 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 310701510 1250 310700260 310700281
    0xb0406050c0a0c0e1611060105060307051605031206030303010e0a0b041b020a0219050906040b0103061527060807080601140c070f0b0f0d0e030f180109061e08100e01030b 75
    0x100003000ca85001a110311b21003008541c0c4a00c10710a07140504800800b0940340c0341300b28222048000c10340c030420b02100983c580a6940e50203400702d5a00841c0f440003040151401000712412551512081103603a155605008000c080c01d1200680c01a40c0d0f504110320401c1c01158100307001c4094000c0c00403100c05005018070f15100503003150781e25520050510040e07951003000c64010a00741ea0000300352510344016402000d00750044c1e00114941b141d1520103583c090324a006401c1e22698804036074024040000c00031500f0b016401c045500c20b40043d8900e8464403c86a01603014502640510201d04078000e03154030000c1528003580244100303200b2410707003100b00b500910a00050341d01c0c011100e030582181d0300900d03295900403a02d43d00300c0f40810808205445d4a04101a00c1d0f69440803410000807103844580080b40c0403541005000031894058010f50b42c058402c00881d0f00f840c0004c6008444500008002d04040020340034007144078925401024042e610031a201c5c0c481e0f0a0610180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 310702760 1250 310701510 310701541
    0x70b070201050618090307080316090603020909011e0b03010815091b0114040b04150e030604020f0f04060e04050304061e020d0e03010e0124050402040b0406050c0a0c0e 74
    0x22819a0b04240a005141e250381c000b13083c0c0e02d6220301da0480f09031210341110b0304620a1040245c41c94a001c003c3c401080307002d03045400f440c84151500c510459071850140c060340140200b841e8807480b03810040281e04000d0720230051424006020003180c548400403426242c100380c011340051381c482958a4034805d400314410360014030100c0200460720301d01360184009100d40e07140b14108005016504500104441500d0260200c207007640d441e9922440741c19500c201100079000062801c072030081145c00c001c90001d01858016040c0020940c09105018458401c10074042d08180d4801c0001200100c442407280114030800156589070b00d0100000c0400d000140140c01c02a900d4541145a540000d10844a1150b5080c007002001801c0c000900504240150002075420480e581074082c101441074003500324451100c03d0034540f1002400124001d90080340d407201c07010001401000e000d20090003080c2519800c40e01c1e0129640e42c1d0141d1040a5802200101200000c0c000c1c40520413420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 310704010 1250 310702760 310702771
    0x516090b09030703030c051006060c020a090e07050420030c04050301150e0a051509090609120f1c15030602071703070503041106091503100b12040b1009050c070b 71
    0x31400c119039500040e407202d580d480020f06111b46440c0300070410100380310315540380c61140d50802c5102e0780c0f00700151440215001c100c4c40303005110340c0810310103404d124003e45034002000602c40d2605040500c070042481f524400082104070210422110001d0001c43c452841d0040040e180d07890101450300351034a00085000d040751300d1406102120000210036400020343d9001325107130311740250321008880800401904080f03040e0801580000001d1071a0148041d20304a0740c0c7c3c1d40401701143c103075024909940c032603031808012050741d5105031441945941c0d11a40c3c00078022560000000c40078450354011100a50041103030024055164006481100381c1c0148610f0b610745080001c0481c4402400202540000842d064050326200244ca100c10405028003051100d00e01031580503410032100055080c02240b000b01d01508841c00ba02c02e9412241e4521010352555030b1181001c050041604070020320a4400240c029000d001e10b0b8020b521000c046542e03480d140c1080d07410841c00516 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 310705260 1250 310704010 310704029
    0xf010617061201180c050906060f030a1b0302090109050109060c060207050c04091203150506041701093c02030a1214040b0a121b0e0d05010606080108060f04050d030903050706051609 80
    0x411406445100881d003000031100d510366504d0b600e102c6814010b00c482d20076803249090241810810710f4263f8001c2582c03000036200c910200d07545100458580200f402107400186001112000241c0d06401801c0024840d41c00c0e1010440382102050441701c2d5803500380c1d98044c0005010740c103a90035214201d01039011428050303c090038040400c1a41c444c078400c0c4914020441601200c0c03080a500c6140c0169109030a03031090004906481003c20f0700805408005803590700c3c18845400d01c3c1e403610403c5902401516044106d9280d201c0d0012120a42e10180000c0340c544109580d40c0400502c06071041c1884117886548113000140003040c2950582041454400600b6184034095031810003200070b850000021058840455003900d440b40f0001c3c855820304602061540d000442a03041c5c1d01030000320381301a610b41c004142c0120003503401a01c190024202105c0c1644a41c002c00c0300f5a0003401d01910703140c4641d80780411108102c40d6104404441c0c103501c5040c60384400c50f000101702864 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 310706510 1250 310705260 310705279
    0x303180d0509133804060e0f100b04180b040e100c03061805040201020d0206070e0d0206041214010501081605190b0309010c080f010617061201180c05 66
    0x4002518a118041d600c5100d546010320030303e031484441d000b00c11020407007515012281a0342e400035084101000789000514403c2481d8009401c0074801d080490381041401c1201c1c0e1103500010068000140c65121a02c00040000c115580ca6400030001405400030740808141503c1c0c40c2c4081b11840303c1820b100c0c03404d10302ea9170181080011003d00c6444600c5002440c100c582e1015401048103a00c540c0400d0034040079030030704040e01d501c001d204078000e80035102040b0074158201d0f21010100c9100300410030248100c1540d051000718116540e10240440c0d20b015202c541c1030a031100b82100403102c00468520011a00e0006c0c02018010041c0100619055103d0031554061541c3c45c010326000d6424506640512041031800303000406584080030707502c1c28a907806a01801c003001e00140414a00300c042441102c1c00000a4100c07600d650315440d29003200c601c240d0507204040d10080e806100c409011655810038072a418000e440308409692610700c0d480c150303a00c01c5030b50348024410030281 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 310707760 1250 310706510 310706533
    0xe0c030a0c03090809040507051c15080102040501080114010c080c030a02010e030a050409050a060510050c0c0f0f040c030b03030301080d0e040507050f03040c03240b1905010309140d02030318 84
    0x184c192003064604840101e40c0d41d640030130803126405182500302c00900e41c1c0290416106081c0d0048101d00100a001200161114070755402c1c1d11507403007041d0000e0300742d0004020840c41451081c01c034a40515181c07600b0441ca0b20f1f04030305904462100c40654000048000f1403940900c101020340314841c01440c144140f4034405441406144554120341e61500c000420070801d5510010140400400340e10078030710003100042c2581c1040040d60300911078940c0441031440c0c80c400031940d10100a100e00c600b09034150500010b0030f881c103d00320901d03481e56841c0995960500c0654080e255082c024426a03954003001441000c20304d088502451400c814000071940c04802c030b0780c0050301507050540d40e868618104004544540c0060026136a8100d00b03a081140420322800e01152a0010703c41f851100c001c0184005103413845881c0c1007500081009554001d40001c0d2550380607100c80f2100d00c5940065900f8450181103450060300008104860344500c2d0b240c40017a80d140800402035007050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 310709010 1250 310707760 310707773
    0x10605030a0e07081c170406090b0f01150302090d2307060c0c05040b131505010e012c0609150d0c09060206071b081204140c01020303060f04060e0c030a0c0309 70
    0x1148031442000f110070b86600045c900500c05004a0400300ca040300c07a078503240c10500b00900700d00c02d0489801080f54042102c8800311021641a030340c55161040d190380f0004c2080d0003e50101030280d400c100620740240c04500b00c3e01c0d203400e0f00200c00f60002071680084e0740740c50a01d0880c3d0800803e000561864801040c0769a804000345d650998000456600b245c0004101030000311100e01c11906045d1000340290074200b1540840f002a2580d8002600d030a0044d82c851901200031030300d41900344007000000068046c420780846019040c14a000070000c0401e002411644080c401c01400141d41c4413854040d214024403030889148c05500d143c03d010000f5141c0e00c000e45203004004d4440380c030a583c0f08075075501041041d4440d92043c1c1d110b000b0900f07560901c80807034043d12402c0410203240c0303e5107004506030b07042900c160701440c81d5a952030204900f40b0b2005d40790b2500541d54060100c3e9491031100518050280c400340a03031607280001c00c20042c1c5206441b05402c140c01d00340c08000107040d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 310710260 1250 310709010 310709023
    0x30b010f0f33052d03070e01090902070506010509010e01080a0b04150501081c14121003020307030309092f03090109050d0504030302070e151905030105010605030a0e0708 75
    0xe805404000c2440b080d4014041c0b560190396200b0003000864200c098941c000e4010a00d0b200780385000080c04071101c10510710602c401a94081c0c004080000800991161038100d0010350305041c030b80c101c41d0f03c4412076801c90b080100c00f211240c0c4481d00600070b41c82c14000041c010180c4141d0f01429604120109454844c3c0540003441320410f14041410043d149860011500000324100007a6a40d45a600d50780c0e2209c071007414502032010365843c5118810030740c510841800d407240501e0002d05000481c81400020a91403401d011040080010b85c2c090150b240118000e9070b03a50b6102e800c1440c0301080781d02c0140c00c000d161080141e620b14040909961141400c00c00241949030ba441500540c0035040c0043e0042040c0039030001c040a00d034000c8050b0054902a82c211128581c0390f883c00c038001c0d8001c1d502181c5424054880301304500e800c401c1242069094064200e00a03621004a42598001e0300407201088003c8104808900309100394000d0110600062501500d0a40d00c16107401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 310711510 1250 310710260 310710269
    0x7080604030f140f031302041b0207051009030b010b091002031206010c03110601091a0f030c0607080c060a020406031410050405150603011d0603070b0f0d060519030b010f0f 76
    0x2010110102150000044d500c1c0d1664903010303590390b4070b400c4c500f2900300f4900040c02c038444c40c540b41d07041451106c2c071502c182c9026501d0b001032400c80e09080c200500d0b070258852003810421494004400640105042e6000f88808013035183c503036481c41c00304031000e4480e104c85000c660060000d4002c0b000900310894010100382001e11903140344d0b04089520201000d018107080c400e03140009070380c44050b0300502900c01500049800c18282804004c03019080c044c2042d1b144e8005000e01c0004d2034000d0082481c00d108102403403a01a15180706400e001e8110307149900c0d01d6000c11304000c01170301801111101d4400c065045007900d00f1840004522042e4006c5d02d00440d610000102e980080ca0007146680100402c8185c4a40c2d45000d600b00503801c0841503910980d002011804900f0001424825618030700e10b0941400c203092000407041d003045c4030880c81c07107448000000706510380840210000210000c03000301d65085060a03040c0b5041a800085903072940701082041c056003040403001c0c0c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 310712760 1250 310711510 310711517
    0x30f120307030c0f12110c030703021614030709021605070306060f0b27040f060e01170604050a0813092c0d0c020607110a06050c0c060f18010c05100e07080604030f 72
    0x80400b1070311100c03d4010403200880c1c2c0d01c070000d80d270340a00d5000550b241c56548882d11000f1215200c2041005400c001409140c150380683c005014a05c1c054014085400b00e480d030540d00c210700c54039802d00d070a800360b00c2501c2865484806200c14007400000fa0040c0c61101d51305450869402003442c5100394040034000e0381c01a90b9081001503941e5002450050f0106c542400860b40300c002c3e5210600b401c2c81112500d9105c041a080041000b04100784601d0f0010042c00540c41301c0c2c1c88000c072681c400f110032010a16401000728a46020348280419800d0080009400030121241100b0300c003113200841c8400d034040813a070400c207503002c501006010750540328079494100d1850002c00d0300207002e04103540036812080100310f1640c0320010380600b240c0402200c00e000340c800148070103841132a01200703112200f00700386441041e8452001001b180c041c589258900e000384c850710b04214420969055650320386505401c102410000f9002030000030000c0c00503400e05a81c003401c2100740e1030440c0d050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 310714010 1250 310712760 310712771
    0x8010806132004020d020405040f0606091a0c01050f0a05150a21060e0d020d090803071103031903020c1e100504031107030c050a08010227030f120307030c0f12 70
    0x1c801d880802c101c92104058800d42d150f4104083c40780180d00940501030040d458608015450202c40c010801218586e403070300544103081c996402d80040d500c1b034010811440800515004040074801c6910640c0084d20340038650a0035180d500c15541c002e0314000e111608100480c4036a80d904000c2400c4400c0c1d000c44244180c860b9480d40e0414200c2d26002d0004c40c174107210f15160510210741580c1700300169080e646442d41104040d1240e0940d80110754180d407080c4401c90025a41c0080e039150f00c0e41c01001ca034108015220180600c072208a003540000b500031800c203a41d40820444a0303652913240080114021120001c03503a500b4084440700a81c3e42c84102080515004040c560f4003c00704070241c0d00c580e5102d06001e600a10640b0440380107642c00c950020380154184261480c86640034a4070021031007a0034809042071085032419894083c00a04061040d0100706c120b440f000381c840c003181c8902d0142409000c40b405540100144414845803501c4a40e000c42d40607594089828009030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 310715260 1250 310714010 310714043
    0xb01050f030d3e0609070605120a020d020a0e1507020d020607081b15070314071d0a0323010b06070813030c0305030d0e0f030d0504050114160801080613 67
    0x40015000f404503001d81524001c0380800305100044000c49800702003200d0840c0c0b918036403e69512810b1051500241c82402020480d1410780903458200c641c00d2400342c01c00071001a50022079000006103c04220031818400442c1004070301390011a204620703540c00c4c500d490b00824110304e0300c850024490350b80007074060304004440080d030340f00e600154104012490f41020b026520005014040b44403002880000e400780d100c0d01480301d0f8050014404100c4c0d4803100320546110340000c41c2ca400000d14510819143d1b1101c00640f00154003c0c0c040094480c020095440307900e130a150304184903418038807200c5950b1102001c80700d40c50390100c2c90715940c02c6600c401c81d0210000c1d40000b08041c400c2c150000912000001400140c1141c040410000d0490340d612236039400240800461a0000d0001c41c50346443e95100a600c140100004100e032803800f086c2c0000d540040740ca10845100750b00381e041545510400d964054149a80208120708080c0b1861112685072071005001e201203000707118 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 310716510 1250 310715260 310715297
    0x60603021e0d1b05040602010509060411011101110313020a05060a0c200418020108090105010e1906090606020f070614090402031306110c010c0819020f0f04090203040b01050f030d 79
    0x21030404030f080e200030440c2d0000c48024100d80c4180300342401582004041101040b010540b54000e9a00603100415030030940c00644068201200c40342c119580c821490340e50100305d00045201d8143c003d11940c0001040c4104400f45440da00081d010714400d0242002164200c00382601072500304205940e00004140c03900304c4046007600d1280c2050515050100040200410100245c0300341c860b480a0769a401a0600b02c45003442284440f1520f40c1c04034811600c40c00403007004104494000c80e4003921440035000340c0b650740e8051030046e4003103103d03003081010034400c10001e02003500d0410b034800720116140c2180d010b400382c2c046c8115800400308908900c00b0388045010355004000b400b00628031300740d140b019000121004140d500b80340c00b03590940e1044214520890025030000051038031030780d40900a40000d250007400c2c031020410f41d01c8603048c20020788024001c15001598a1a283c5400e900081040c3d000300c4c05481103200e0a85140d8004c681c150380601c0524140184105000030711 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 310717760 1250 310716510 310716521
    0xd1e050c0f010606122a14130e1f06092c1e06061c0506030106320111031b010f09050304090506090709060e03070e150103060603021e0d 60
    0x1003203030741c6032075800214190040f04095010019400400503c41d6190b5050464045031002100f40286d040455600c50700601e03c00c2e100075070001e1039506014281c1d84040406595420900c0d9281d842002c010142c11030303401c80040145503411076101c4624044000e003e020990103440b900340c555083c2c0b102c084c019900144c0003407100b2260142141050300840c012001c101c942480c1805c100c40005149040a01c11100003a01212020744500c050206803001050054101c0d0360654a803480003030504880360040408514800079040a81e078012096401b5144001e03c080c103020848500c509284400701c142c401c2482c0c030b0010903150316a00d0030200d00510511138440d15861521241c0020b0040000140c029a41440700400c43c50b12068104101c0b110100c84290010301c02550a0001504c2103c0c0c0d81b84100c0040e089801041d210301c0740e40a840c80c21140c00300f10419030310754500d0541e854096400207003d0750800314a0820a2506a880e140030095010740040c0009410000ea1134140c0c081e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 310719010 1250 310717760 310717783
    0x503040f1208060a080d0210050a090f03020f07150c0308040318180605040902060f0706021207030f0513230703020307090e07060801050618010c020a0e06030d1e050c 73
    0x40c9441c1c8031442502511640c01520302a0103001407034400300e109a40015104141955a0000c010005130010b0001c0503010013003840c40000c1d119900c4000048168403402c04d564400e401038060003001b40c1c4030600e041007a500c0411728030004200c40f0001600498403100540d010b140080640da40c50a040d50341d03000c1810f501c0c00c2d14141038400601c500801e0485040c44065010620140b5910010001610702c1c07090041d501001c01c00448c40c02d6a213090003030285600c0b540002d07052403807040450b4120300007103c8100109807a07141ca41d11500c003a10805500c21103182c040303101001c82c0d407034000c8151480c02c410308401007401e030320f80007481041101e0b4005590090884004545901203000500300030264038a09100c0c40c600071074003e018041041c16036802401503030034110003500c092003040070400042e040c03041030311050700035803648030060004c0c054850404605003440001d05180405040d915806c01c80000030f8a000c801258440400b04251443c00b142c841c40009451410401d04402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 310720260 1250 310719010 310719023
    0x10e06010e090d0509060301060c15110702040506060703020a11010311041707050d1113020702041a01020609010b010e09040206090d0b16140306010309032105150f100503040f 77
    0x15a03a04440c841d64840c800c10070945038050228001900d4500407840c078203612040c01e00c01840024411f00e9000e0b503060007017084460000f0600fa901044419800410b084e801c030000f40384081d82028012030780c0206044e60503925242c003a0301d00945130006c0038070040102070031400300e9446a200f42c009088103002640345aa84a070354915403404120009402031a600958200003003a2504842d90528150452403002031a9551410050740350341d880d1004040a0342440a01c015840f0351251301c82c41e11b02070401e031102c19012000a490060010191112a030500c1c500c60300a0341c1c001444800200151203250351500d90b4070024010340143c04d01c0300d41124140300c014080c4107400001d5400f0b59060070040ea1009182c4a00722032441038169040200d4601300b010503800d5110b548240c820318000c2ca01100300701c50301000039051000d050b40c1c40c1c80554842d0140b1142c503841407008603c42c5403c80720807840781442000f00746001401304101045c0840400000e0034070094441380c4020310b60110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 310721510 1250 310720260 310720273
    0x110408010f051e040302190519050a05070509010b09150708031f0e0c0f09120f01150f0f0501110f03130e0a06080304051002010b0a0b04170c0a0308090102010e 70
    0x1d01e10000e00046a107034140c2440106400d01003419511014000d40c2c169001e44544a160900505c01303600c00c817400c564911410502d080c0070000c01c0541d02619100c0d030046c2c42e00c00a1030818618142454100703d1141c0070840040201c0c4404400300c0c1d18030041a100d0b00701100304c401d5000c2036800ba030710000d4610f070703800420050001c410030f032204400d07100d0004122040d500c07041c0d40c19000c00c040b24402d4840d541080400040d29600c0c0142501c2c84008000418800003810101c1c01d0000301e00629185a454020400d540d4900000c3d910181072401c0d0308a40d15032500030b04c1c003064007651284d9410f01c644070410b601542014044001c18034200c20407250780b44a80030750101401450f10a002c1c01c3d0910303802166204801d4080c40048860302c40003076041c242410100001c031000c40d0358042c203640da540143c0c0c4003a10b4608205006101c1e424405498525050900902c900c0800241c0413641092584883c0d95844d003161000741e940055806e03840e44442001030340144107025503070442e0f100e0038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 310722760 1250 310721510 310721531
    0x10060e030f100603021e0609010806040b150406030e01020c030d0203100e040f0201110609060103060c020f060901020405040b0d17090a030b040c051009031106030718060507060b061c11040801 84
    0x20b07000f01c8200d034825125060001c8440911003502842e50718400d610940801402100d036110b8a0490f4020400800000340c2220000000f41c01c10028540441c0050300403404200e4540c2501c54a081c0c0060140291300c0d0031513001c6001d0312485134400c8103103800e6010011030308423020803030220702030001c45050a0090500e8202031840d05c850704022800a807059101c49405000440c0c001c0c007541d0820010030040c1d00719500d52014050aa69041c1184036401c1c400d410b15404201c007600402000d000140d603542000e0620040d901c005907480e000c0c02501c08160300080542c454841502101307041e45498a000c0703000204a081641e1001d86007101a80c2031006004d880e00400044810491300010411142c1d001500d010304144006400300c8040c02e58014581040070045600490f07914005203610030580171070201000303680068002860200d00e03807040002500c00e51941c0b03002141c0d400c0c1400070001c211050502185c1031031211030348400c131488807081050103941c054507085000b4002c41e0b204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 310724010 1250 310722760 310722793
    0x3030703030f0501050f01050d110f1c050108060403080417041505030906183301030506090c06040e15130c030b090a0501030c060c0809100c020907030510060e030f 72
    0x4141601c03030b07140c502400080da516145152000c0303c0030685803903080c404281c000b800102207032500f00c42410010810b2954204030704004001d401e0800b0981f0000c80542c181c04012250160400074031940b212090001183d00000e10300c0d44290b001981e05050880b803201e0504078000c66100d030155183c1048150410740c1c00c0b402651182000504540e0346a54a000d40401c04010007000500764025148403080e0780070b022103a0440b40c1044be5000c085020500d011034801209a0007940e00360820303c2802060841484040b5155100725400d60030541003081200612402608070340716200e2429804c0d49a403905800c1894400c6034202c20410402d00180241c0900391004221748508045000109041d410788551410f80707402c001d881302010f0401d03005940014203400d041d0348460041c0140404d541c1c80a1040ca40c3d00c880d541c0c0e01c42008140d105006101d03c1c05001001418205070030400d036000060038030011900369140c030003c800e0f17903840428106260304524084500031382d9454003a4080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 310725260 1250 310724010 310724021
    0x2d0703030c060b2d0f0d11210c0120010c0815010519030507050d061d06040b0f10051c0c02070609121b05090a050601020106090621030e0303070303 65
    0x1e40081c09030403a030000b08120005101195452100300d8100707186040e481000e200d5002c6000342c482280c842e00100092502c601c1528210f0381f2685080e844e034180d040414000300c0c03501a03081e02c8031401d118940c0c401d4441911070b201d5410031500c1c015031556120f1120b1f0000200582e80c00030044600d810400520358881110f00100c001903040404400c0d500c05c0c004c64100f14484900c020740c440303000d00c044010384809020360381084014068160300c42c0d5a407158100500d40d045069001d07082c070340c070809101200103000e91320503450045060030a456100840c550010700711050b180c0001802e00075503090103081518030551004240200000003141d0210694554030380880d01d80d550f880344111200301481c050303108071381455a45003001a403034001030029461108401c8480f103031100b010890703d8408645071000b1540320740900103c1d580a01c1404040c0440f0b0700140105410004941d200c6070071042e41d0340c21001700e80c002d80141481a50010010340300202034a03903507419070800401828 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 310726510 1250 310725260 310725263
    0x702040207050d090501020a15020a110d090602010c080f04240e0708060a110a0503060d080a05030f09061b0306040f050403021606031a100309020a061215082d0703030c 74
    0x40c0b10100101700c56000203002824180c0c131a614007284100e6070810300103500920121014002140c0500070301000901c4a50f5884075190354140800d841c0440080c01d4a6012041000b1300080400303000040041142d40341e402500091041c802d0905a245400440d00d030002d03004840e45131050454001c1801f040c00c1c803c0301d0130030003102c0312601c80c100414110b8600e440000c803a184204501b20100b03000d0700c051035004034000c221260204098449c0240740d4054040fa00009400004000c481c4a48000c0706421800000003800c0c28a0a4450701c980c14550013400000488084001041a61a9004514a80c002910911040c1054580656500c006075411403d050010704085000c0b4841d229695800c0c0005002e0b5061030210307c18860308540c0c031171030141019129001700c4056107a03c13a000005204640d145801d400c811032840041300c04049680700c1420b0301c00030400450341e001521161161144103042094842203a0241324551003000d41030042c001d01c80b0001c2419040003c120365036 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 310727760 1250 310726510 310726517
    0x7091215022b0b06040e070507060603030f020d090b25082107031b0f03150e1504050613050907090603060207021216030b0a0e01062310051e0702040207050d 69
    0xd408203220a010348109249803904a4001d0008208100c0c00a42c09500030441d408d0140c5400e40310344038101500d000c0d40013980801c403c8d041c004102d99042128010382071041c5049400380b8140905121036110313070115139001140c105c0140700c0c08124070304220b4501d87e001e0340d400d54460882a01e800284041071071564141155000248014000e001c0c2400804542206011540e10380c0c0098503010103290039042050394541702c45031001d900c88481009881135a00a01c41032510210081e0303171a1003185618000c83c00d08007401002d40f502450052a40d090a2020455035a40c040152030044280c0c4905950f5042c46800820300190790300901c1c015000303940c503006084481d003841e551540b02d0701352030180d904946020008a0700000e50507402210b0004040b550283c90300c592421744241c2d800120011075184015440303080d40c0f21031440d16940030746680c010302c03004442c09481806180200c2c018104482d0202e02c013030204208840301c0c00c0d8000d0086481d005e1908110703a07a030400480b0700300403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 310729010 1250 310727760 310727827
    0x2030c010911040c1d090a180501150b07081e220906090606050d1e1e0507020c0d0305071106041202090709080a11150f070c0e0709121502 61
    0x503070700c01c50412554200036260a04517070490000d00480381c400a10724160a60394000205078600511740200f07c4900800010a02054919600701d0440342580081c20309541000540b000800da00b0640d02e01d0201c4404000c00f07060542640e800714030441440c01c0000141c07080e0324140c2528100c0c09020340380140c40800c0303020f48480c2124101c40f964040e100c0400e1003030040320510f0515030803040820040340242c14029020803404801d8520b042090ba1500380d1040140c407031002c162080701d9101d1450320081030904000c001049022092840290401030000303039200502c041c146c070100c4102405090036603034a98858403401a0741c54010100e10513840d030030100c4c0c8242d2064000d1400c1d1503443d03000d003603924403a548818a02250400c50394000424034400110400c07440d01074021500c480b01442e9a40600340392500522415402400c500c0c803d140522240691004544081d911116809070b810a040e0604403130b02c2225034801d8110f20700016034850a003001400c5c04604849603a0354108 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 310730260 1250 310729010 310729031
    0x103470a06080f060307030f020402070c03061a090a0c35151c03080601051602040c080f01060c03020309090a1b020d0f09120b0402150a02070e0c0a090e0702030c01091104 75
    0x2220038140c8000343c0900b0380001d0034230251170258004c05247d84078000003241e4981c1c90b80c800d0181d855000f0240e1740c80710384812581a03401d211200035408005c40fa0700b000410b240800c0034005809101d840c82252000000c0389101c076068100041444198070b1003e019442c0250340d1812990202c091140034600049582c0000204508190355069240e1a03400d1559607400044805821075052000c040482d41c46440158071940b140001210b5503680310110351808034400309540206034014410080500558000720b5404015580300c204225000752481d1503a035107400c007600081107514189080c0200c92004075800049119480f140d5840e09424445000000d0320a0109446103014101e0a13001c004001480c070360701c00e0340c803d00c020445601a10b18000c10221078106150410169003d48818840c907401e01454a9225444000302464a1041400100044c1c21440b41565108580c0702081c5414003e206490290700120f008104085280c2000750700d41902154480c05a403600c0030240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 310731510 1250 310730260 310730263
    0x20f070c1203140309070e0a060302040203100302040501050a0b0a0f030b120c040609020901050d020a090b070309050a0e04110d021c060603060c02060c070b07030b0d05010b0103470a06080f0603 85
    0xb8418407220f8003600e0700a15204540522200c0240080c03082d49c0e48080100c0140c0d1188007443c0903140f0310008402d0541588148412138206070021231041000305410011070505c0d1040380c00c00345162620141510401c0300a801818444404a6011610010b00304800c03800268040c106141194140013550f59059401c0c100d2090242030390000302c00b0403100840e90400c1d001031503200600e2901440955403501403900503000300000f140024a5081c042003e0700e04003104e50082c2100644a40e640d003800d5444140075001ea942c44c50082255a03500025551140c8480c1c072540410f1035614014501480d101e0f00400312400f04403402440c110700d4280c0584005007e9104502505000e440c02034a511094481d610003440d140c00c0648404000c2182e0b1030740f90011813814030860000c40c0051000c800035017038504000d20260030082082c0e0003540e0884a11410040186803208100e82c55074840401d1004501d002c042d68100c404007000180d860b900420852040c041c288140c24503444036010035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 310732760 1250 310731510 310731517
    0x50306130c020a0809060f121b0f04031113020406050a0915020c0d06021c0905210313050705091806100315110c010e07050a1406030703020f070c120314 67
    0x201c0141e000c8040400013680010061001480c020521800e040320044822883c1e80000d05a180f8424440d061050100a11385049090402c195940c3c0c20319020318000c0c11a8015403001070810054401302080c1d948401440d0320143c01e0310035055550f00e84814015103154050132002c00019405080058040e90700c4024a0340c08071580d01900c901e0040104008044440d0035050f1040c0e9420000101c2d04070070960000d451000f141c0000c1130412140c01c220b4144a102c003c050105200031910000510b46c15049036030240d15024100c20700245c40c2055440c0800907002107410210781000d000c0300c0e20080c00704a200715016421152560780d012880c40440c00d5601c801000c1d0101c2c0d9191121404864001e000e0700341ca05c0814600f041201ca80c4a800c0d02c2b00c44a40011580203070009000c142004074000d0040c2c4687c40c0a040041440746c042075146c03000902e4102010390204600c04041c034034a003284c110366000740c4000e0010b070311031244030807950f4031f403800710040345110a03641884520072095 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 310734010 1250 310732760 310732781
    0x501090e040203061518040302070f1d010b0a0504030219030c06050a050d0203070c02030a030801170111040512010b0a090c021c081803041214160b031303091505030613 74
    0xd13002507110240c49580c031403003403e802544250784000d241d50b0100c201146030b102d64041e03030081c20f080c0d181400381c4500740c6241d08816804404200c072110900321100c8104e04440501c40c1c210340e00c015070001120706004a400083d4060840c00159600c20400c102c94011f40340280004a009139a80303a05644074440c920704840821002d10003209050500d601440d8423110b0703400e180349c0d03000759031340041c1c03d02c40301100031404942004014410b01c3d17410041014060301c00c600801200e000d911409140c2d01881c40741e980305441e03c001c50b24215400b07400000400c6405803a803a400354075401c20402038240c504c00000103120360718070b40310720201139a684400d200c85915160210f0711071039007407281c4809040703a00386103100811002681e00a51000004124003450300c0503ca400d1b600141803c100e106402c180c0b81c03410300c00c024000c0381d80040890b501f0011140c81207880105d90324056400442c66409881c1c2d150812007485600340d0004021441018100c03010328200323a01c4151101220b000128 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 310735260 1250 310734010 310734013
    0x303090a060e1305090607090812090405091203040305041a040f12020a0308160203060906010b03070f0309150c0f030e0d030c031107030e120303011a030601031506090501090e040203 80
    0x600304a8503000b5403074004034840103081d903404605a0140c0500390380c026200b00c40c1c03946c0800100a03002e030b0310425684c007500c81c200280082030141280002c1c103000d80e812141c4030300e030b6540c08182d2801040080c41d035542c1c9809183e035224901800d0103851070704144118807815000160581d04010814200c409960304010505040ba08289403014400e4920604a810111201002c4040381e03448000e448048251948101001d40b144141400c088024054007000e030301c41c40046c441100c07440c0a4130350100f0f1a241c048030007100040100c000e4104120040c0080301e05a8464800c0368150704840040c43d250307200c080b151031545000320b00b2100c0c074100c40107190300300c840100c01c00740c42904800e50150b9a898042a54800c060003128258002c5400314040f54a80410a1050508d080e0150164207900051815503261030014000f064082c000c44500c2000003000401c01d078000d510980c40d4402550311100e0792511910040c0000a05000356808200c0350280000c40b03801d5514482c0c811030f4082d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 310736510 1250 310735260 310735279
    0x10b0403140c0d150b0a031e170703030212010b090109030809180a0c1e0203040920030a0510090b18040807050d05280c0308061923030309 61
    0x8803100100c24040344409a00d000b0768070350382c2490751080c030100105806441c88141110541c0c04100403200c40000c01d500800e4102e60803c0400c024810394803245410b0010728843ca542d9283c807858017800e603060109001008034403070040c075500d50b000d4007620681281e5049241d072285100400341c021203e19038001106580c0a000040084001e480b68020150508410b1900380b050700d011000c080b2035901d01d0980e121544404603a0182c0603800c0e81c40750703165038481e6800c4040025203038402c5000390f00050751500c000044851207449520f4841c2c40e1016030548a0408886000190106035903504503c034450402240010046c03041d0309429000614810620b00390b1001d44501035002442034031502c2e421321450010500502419031051025907411f6030b11b15996042c40d02c8102040c240380030500c50b03c010244002e411203a2103a42e19050305080321f052751040c00142c40d0044071242e8400c21610301070001000c00c103c4040707042e4044015148038081d00030700241603980c0682002154000d02c043c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 310737760 1250 310736510 310736513
    0x1502060612030714101802030c0f01140f0702060a0804030e03061303080a0605030312010f06050f0324040c0201060602100e030a081009020310061805031b060d0606050301030515010b0403 82
    0x89132034541c8692418180d0b880640402d03503c100f2504403240942c011400001910110707d014060891554002c82e46003588000c0100000d0880c1c2d01d03507807200304620000548101c00c0d0a502d05940303613240d0040c16a9504d442c8d10200406070907084e10210085000145800403510b0b02107185440340c010107000162040194408665040c80500b0240880c0d0746c807580441c4d644c82c180001c045900c00e10110b800356500d0b00400039850811a401a41008400c0c404020742008e40300407070380c010441912800300c6401d80b400134010004074000c7e05038058a0a480582036980640012084550340d4090310207081003503024800741d642c101c064040a800401264040c3c5000d01da20719000301002e502600c000d61a04142c6040303a0054881d000200019031080001550007000c0e49400d60542200d4034050b8908404a599170f10700329158803034103a0007420340d182034032181c06070380e1a8400da6038244441550b0f0304000c0c010f94401c0c042074845014003003d1104124440c21200e0490b150a8221480c01703255 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 310739010 1250 310737760 310737773
    0x1201060605090d02041e0203070801080105040c060c020f0a0f1d040f020904032304141906080705130314010e03030f01030305031305030a110106060201090302030304020d0807080415020606120307 86
    0x115101302e0b803041e0341d0031443c811640300700304064983c5074180c0010398a01382084054100c0e441684185440da041404100c00504400c5000003222194100a01828450720024000c1904000b849401a9403118002040f500423405402100d00354245440f1580740001d0401002500302c4000d4424103039400395030018108282241d60240c0030340f48c07449402140102d21910601c83d80000103401c0000f090600201621640c3e04d003807000100c491142244522600c4c4a0540f500e12680c01884003640000c0c4007980100103e42070800d6070303c4601695622450110356951a2207610005907207807031120602160b00100701c81c0504050010165141e20710781c0c0894440e0320003040076030480b90301d204d0340e400a407040000c1c204030010b81e04d51381c1040d1026010701e0300312141075020008582c18100c1440100e50048122a08a40c040d60106c41e1000f603414460054818518010101880004c001481075800502e0000302c4182d6801d40b00591200400c000c0c907210601c143c104035030010806400050003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 310740260 1250 310739010 310739029
    0x40e0a0b01031b1212020d09050d0b07021006030b011e2301021207060506120d050a05030a0b060c0d08011215090c05030f0a051014160203070b15120106060509 70
    0x43c40300540e905484005424886440e02400c48040c0c000c080070501c0c042c0c051207140d04914031071828014603480c1c80002075125009001c0589a4a0101f011540a910030301403100e282c154000140040d55407403406120111007489007802901c0b89040450a80030403048020454681c005011044008aa01328414885000009041d441281103188000c400c10b00685900c5014000c000391601e050024001060024107510f00d0b15048440c2e07201d42c6c40d401105840242045240407601d07039540d80003420040224860b490761091000c07603080060f120008a5849000c00d44e41d03030411a1340daa000d44444120384010080c807034070960041e22504110350f44181c080c2805000076001250380c44011a00b420311048899480b070304000c203480b082c440c08102200759048141002c001281641e110064840c001074500688816154202c14031640b00700103850a41c0d0304040000d082d4201050900300d62842178601d24011440302920001500703044c800c580c125061a1a11480c0c912001c0070001100f2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 310741510 1250 310740260 310740293
    0x19030f02030d23060121090201090b03040b180d020c0409020f090c180a0510051c0c0207090c0f090504111e0a020105090a0f06150b07060605040e0a0b0103 68
    0x4000d0041c0511501140201c0351070b4460f00d0303006060344525000da2000800004d10315814050700d9145215400925901c85004107000f5000241c880c0040c0b00484108490742c0c806941d518001c820301061010850f1280c0c010b00354151074045400440d800151503030301d11003100016030407101c0103046504054004000f143d100424000501100344005040404117854a0b40b8001c4089442554200030701805101c1200464045c1c807910f261a0000e80003074001c88400c1c08100b800305440c50101584212040c0702d0b00b0b010300030300009000b588003e640301e22a1042c810101d05061880c00309034000c0702c0200e003601495071000341e541d0a04041c07001902840c101c0300c54200c410060345003000340c5200030b80e0941c50084492640d80f11901c000900352100030780000c480780c00500c040e000246080c0310340e468241d4005c001040380c4041941c0ca041920650f4014000c5002c001582c0040200d203034032460039500121020000d40418002c0c465480114250003421614040e0043c004540c09228103a03d05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 310742760 1250 310741510 310741513
    0xa06142b1a04050117030d1d0a05061e07020d110c0a0603020d050c040e040b0c0d2a08130f08040504020a0903060f0c0c1202070f0602070806060319030f02 68
    0x40c100031580464440d0111101c034004401c914401529140c010300d03006000011782c015a4081e110a0180c807846804044a03405a80d0000d0701280303072a04075003000c000c030b0440030b1700c01083d4282050340c1ca070f03032049800d111403040b01c001d148540c890000c4501e0040d1010b90081c80300400d0444103a521100000c51980940b2032007000004981c1c41f2440100a0200d81e40d0168440030851130341e1041d150060500480100180424813410009510302c5a010384c0140c00c8146546840810200610980d400800c4d028109000b0140c1c0c505501700102c1e0b01c24011580610380c00c020b43e0100d809150030b45580740140c2c1c00480c60340110300400c060003603c1b13001d2106035280964850010b0200c1e402a484c450110310450001c0040c82124884c00340c05420300c640c144025441540020260196030400600b00d114951002d20410b100b00b1201c40070301080c0070f100d54501e03100d0001030760b6144940314020551084500042183c100851544641c8500c144080703100075060303034143c83e100c0224202800f107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 310744010 1250 310742760 310742827
    0x306110f0706180204060906060e03011b050f12010e06031005040b070513090c080415020a090303080a0e0f030c01290d030210090f021806180712050405010b0a0614 72
    0x350785e65208000080c070b003081000840c50703d45080030307010f4848080c58910a902d00f07481188845400a00d02d64507022900d00340e40ea60645030801821805002010f106c40c0304100e0004c900e003030381038122a01078507080701103e50264201086030143d800c11640106010712420204c2c005500907000f40000c40c440410180c41c890700c0300140d0084234140d06420300007031000310502085c04007054540908070f40003a419840d082d003040700030f0b02c07443c8a88402020881c2030000981010f002d40c0c006a4203250000c1a034120306401c06007655203070800700a20045500e03010610070700804030502e40c0c2880d03140c1d040b1001007074070720010090000d14000d000c0d410f5004081d81d03924401454452090200d1003140114010000f50050205c83c840c41e40c0c0c110700c40c2c01c8000602016035624004e01c1d104503503020944545952b9948112680403c60340d6141d0010304100500c0200101908040900d040640d00c060340c00ba40c2e4042110b03040301d080300280180e0401c02c4406408900117054007010330310398011040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 310745260 1250 310744010 310744013
    0x90a060e030c060712090602030315060306120a0f1b0617060307080a0308070206010e0105090a0e011b050c0f0c091f030c0905090106080105090d0503060307031703010306110f070618 80
    0xd561000000300d07450000340c80322442c030076000300781c6c100901901e1005500f18a00000d000400150540c0c49038440c003004000580700d66103654404a01c03003400c0040c0c90720103055180c50039595070480d40031280c44049100b030010501c2404808130495615a503040c20642c03207103500300308400340a0602600b60060210108003080f08010b0310036810b1081c1c2e6150240e04c0d20301002820a18103030040e4a0082c00e100c010841c50351501c21650304a51100f00005660a2181501e0700401c003417210b02091420059103144543c1d00500540700a400017016940310410300441142c54119040700503600c480f8200220b51064012400320210030140c84003641c21070b84035107410719003000342d51200204640320002c102101100380200001002400020b200034104005c2441c6ca40754105480c0c8204000030001800f180d40400440c0020360b048403442423068a1b00124400c07941c400d00054444070b0410403142212550311040305e04045103204074500b80013080d91500c020300020302c01c01105c603410a00340d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 310746510 1250 310745260 310745269
    0x2011a03032d0c120a11010c080106080907030c06210501050d0803090c0406330e040e01060e010f1a07110d050a060c021b0f0604060e03030d090c051302090a060e030c 73
    0x54009400310315921000740d1500104040c51440f03401c111641452a4550280c0c1c001c6500e0381510400d092501035581c40c071a5450ee82442e40c3c3c0b001d0540311074098006603498004000300c040c9000d8003252068541455901d1064880a1003000e4004041c40d2480010551080c0503540008012003903515a400b07000018050b280030390014030307101e2590f44a0705580c03850f440d440444020f07481c8140b0054500204003070a044103050402d8000c6845102c0341004200070351101010f80b8640344515015615070b14101076145032030160141245008101040d204024815104190b034803050581ea440381400034400312180004d8121603501c00c2129171000102903000b0f440035452140e000f050003082854280f44c4a030383c041c0041c3d0040c00c051804007419281c000458080e222039080900d45c02c0785810101c0c1c40d520036101e500e900285440e008208010340c010703809045030303411103e440011088503a0802207200f01040c0c00d5004021020030041180109414614050001d05a40200d000200402c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 310747760 1250 310746510 310746523
    0x703110105071205090d020a0308130c0e04022404050f041413020901171e1905100606030b0d0204240f050a090207020307060e030a0c0602011a03032d0c 67
    0x40780407803044a02d112900310f40c3d2045540c04141c0d04004c2c40d01490b0008060340352206120090200490700002071076090a10b1041e5500941c0409111815030703551001003001802528128403038650b00e00c5c158820007402c00c0303200c3c1c02c0c40780c0c1e2a514a05031401f02080540d8181e8185a47c201340c454192017400c860f090505845183c1849100d412003079180704000c840c2c41305800c00200e00362518488402c081d130000b105d10142441720741d01c1c1248000c9103005450b1048041c90241d032000003190300c1003008000b00b0300c04810400c18605010b401d803220419070a59042c111400d07040031903043e0703030b00240c07505400c114255049101c9075008041c1a1000341240c0c1c0d05034205600e8060008020402814140d0000e0f004248490701141821034139070010340c40d1703806803181d00200134902d100b00051b40d506000b0101d005900090b98039106139580006406854921290144072068a41a956070b04010045420300f4158142c10b00d4001000351403058118608a0080c10b03440b000e1000410300c2c841006003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 310749010 1250 310747760 310747771
    0x5100501080a0c050102030a0f1b0212100609050615130b0414090c040501170403030b040218030606030d020607050d020c0102070602131e0e0705192609120703110105 73
    0xb600400c4800c0c18003041d0740d0065444a41194000c0100e4000039611840040170080340d454280505180700c0314221507c651120040d601908401141c6044070700020041d5440b1041c1405000083d51541c0d0783c0b048520413200c3c207030010400c020100645c144000108240c9416501038102d25840b0091904290040c0d008101c1007006400340308103915110340c601d035100350071001180c6024182800240746041c03103603010304036008034030215007014083c0d0803000b50408060001c54842c4126021114400141c08100d8068010b6201040359400c0c00700e2412003c1c01036070014001034485440c219040c1d4050b03070b103110b0882e5007409600c004900a000030b0840e140515409620b03007903905030915541c64190301c03800441a05511540c0c08896050301d03c4110f03503000780c0c542801d541e200000d42d43c0d8410300a17403c0001d00c524041d0540685c2080e0b001d40318440d5401c4581504540154510803803000f900ea101e140d612120500c2080859600105440c03882440c1188078540812425400d681f0155030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 310750260 1250 310749010 310749013
    0x11060906061806060d02070305070b071817060c030709030b010b1e04030314071118040b010503030c0a060b18010906060e01030218130204050d03030504050d050304020306130510050108 81
    0x41c0300e010714080d40101c4290002124654040c14003a00165030751240c26565181d42c1d070045107080a06000e8002c0e07440b100d8001362140b200d07181881c401004080c0c5964651031189079a180481d051096012503403811030380d00000e107001c5e129501c4640c0310303400081a400070081c5010740400002c02c07030042d4500920740b01d0706442d100e840c8040540715402074021104100170040c401080803da2042c24280054280311095030340e1582401c00d0031491a268140d1a0023440c580c40c100401708207001810321a03401901c0300792a0f83d8888003015124130880c0740c4140690300c52002710020900650001c500248010725021001150304880c82944809a00c031804180d500c1100300704040d000401c0c80c10341c200c00d11701145405100e00d500d143c031402d41d8101034007441e80c03100701024883c2c1c1a4100c6c0d0182030000c2c03101c500c0c0b00c25440c0007000307020b01320303000c40e100c1c050144501d24203070248080d0303801580c0c014060040f960b207010b485c0c080c60000c0e000546851064074811201c0382114450b8038040d1640300c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 310751510 1250 310750260 310750273
    0x6110a030e0601082b020309041a010807090b0d05062403090607050901090b0a030e1b0a0f0305030406050d1103042d0803061507020a060512160f0f110609 68
    0x20525800e2950582c004c8410b40c0081482080e0491a50400120031025500c0c107508600040c01c01c91540c0100380410340c1007482c12009991400c0701465030390500100340c1e1040b00d6656032103002c90302c1e42001d100d2280e2030b14050204840341700c1e06411441e8070140180040c1030401e82500e803092820840d004131800420004284000310105100040e44009241896864801d6200000700400d4081c420314500c24004903c0110040c441d03004102c50320050012942c107400110004102c00c544018040d00c21106c4001c0055007100e80303600c00b4212070704031018500b028500b60080d10f241c2d000315500e17040b00303a4030351104911484000295010300d00440b45040c00751145c1c0850208003001d07032803100491906c00c01e40000940342c1c40483c1c1d803140003511030098801c401c1643d401d441c019500d009501c1200c0d41400300b02c6551040140c05084040311030340c090743d00c8420f005c0f245100d00354a40e00008080f094030f44043d902500c000e100d09009417600c0017980c1c051210342410507209403003403060707900001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 310752760 1250 310751510 310751531
    0xd02040f0c030509150405030706180b04150c030501080a1103071e140108090c01030b010203090301060b0a0f0906020709020a0509060a08040209090c1c170a0201090501060b090d03080406110a03 85
    0x108201111744c451644014414105501c7d041e45e00d0145400c01000c0030b89440c004a4011404002c90309643d520140a800600b0546003040e4508080e114405e4803520b01220000c40e14032134040d4604851013900030707003140135194480005030200040c02503090300c00c061001503220000d0003050301a04980844540e01800e00d60203000441c049003055040251410078030080c0c280100b220703100031909080004055442c440147c0c02c6005c0c0ca81380300c1c1e00d940303010000184680881c0062181c10003e6540107644224401d00352981d0b61140511401640041c501f401030078a00e40c0286541511400c103a410004110300181042d4044290180041d02d40c00c103002c11070800002e469000804030014040c449808004114100b4034025080003055803110040c01303002004444030400c00c2d800c00351542c0e407110000040c0c083c1074086d004607a103602e00071000600310242d41c1a01c40615004210841c104010340f41181c0b00800a80280e0384aa80d90b80321900b0030034624000d08800d070040d14003041d00d2914 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 310754010 1250 310752760 310752763
    0x602010507091d1b0c01050a0b0303120c0a090308180301110f0d020f0706020c0a1214030a09060b090a060e0c030c03070c15060e16090506090d02040f0c030509 70
    0x14241d8424009010710a22142d00d840340b20b0740780c055450300e8005450742c8000d9010a43e01c9003050060039220001034211600e40c0640040c1d00c80c1c03121040500a001a240c281a9280710b1001016600304548000c00c00b02c828030340c01400240d0041c54107080c4580c403501c8482080e4400b2207180701640343c8030849849030800303016056031000c40200700d0f4200380c0b01c4a40c65074280300d00d41c2320003082070780010b503806200d0815003998500358201004645a0052109240c0e070741c1e42c843c6003a20307040c2d041084841041c1c0300305a07200151840011144c21601c3d0041404041d026030715040fa0640d40354080060161205a0030911680c00d0540c080780c1c2500d4102000346000000d005e18601400070000c02c50420075000c126600208145011800040075041480740d40e862842d0700c5402c43e04003000001e1300b1841d02d4149009000d262110301c5c8031400c0e50001d41e9000c000340705091b00a1418010801c00703103800f5100c442d03d2070019001007500e107010602001142c1c050346140012030303590001c0c06070f40d810 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 310755260 1250 310754010 310754021
    0x1317040303180b090d050106180b0111011515201b011701050d0f12020312060f01090611100608030315030a03020601030204090c05090403021c0306030209011203020c090709060201 79
    0x2c46428119801d16800980c10300c15074003518041d40d00d04c1000740802c10254040030007402c1c0b01c0303000031a000c0e20108103c050500f040e4000e000503600103402d88880810701c25910000049031001926070301d081014401045600c03159001e000d480495010014081352036008601d0329203001d000145541c816501c91a0f5005140904200c6030080715903040021121490655030221820526075171686031841041c1c908a000402c00105241d01d104c80b42e40001c0508200c811880070802c02c0d64070441440084182e0320400742c00100140e0341002182d000c3c400701441c509000c81900c4004203141d010700700343c4625a01840c920392000041000503204008868580304045002e8280411035850003540c421040c080a031141759039a1102381086a900918402014007600c1403d49190605000e900c41e82c11035440b1002d15004510541e03198460701c07801042e40da00400c801c149900340500e400e14000c0c400d00440c00d502c00c80818592641d100c6141602c6113041c9c4e501d6280c0141400b00003800d41c1c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 310756510 1250 310755260 310755287
    0x9060609080a14071e08100218120c0a06170a1e021809040506071e0507110604091103011a090112200d0f0509241317040303 55
    0x100d0300c0801c0c800c100c000304869140d41d4014010081c07005003100c03920305103280b90380302c408801c40403241c08285030010700141040300c04210643d0441031103440c0041c06d0303204154804122882250340303580f0515202c105411049840b004503204902410041344500c0c0300c40e0000d0001c0f41f00341041d24019819030000591100b03100c00c044c041e801c0c10000c03114005642056004031290042003041c480b5005407001e131032030b401c018485030007070600e82007031625000c0607600380340000d80003a08507403080780d50101619500015540c5a140c528181c43d404241103241441661103a010417000810501c140070300f40d0310420340d0050302d0303903940b401c15141c02a00301000880300144040c080000e0aa070401301c01140d09001410204040956001002105682d401d01a200f01e0020a100b102c3d07001c150320140320000761440030005500c60984a03551004805050300c2a00c00d04400c451102d10030b90400c54111031900c112003408a069658010103101c4403202d0307026840702190400c103041d4089100c00003030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 310757760 1250 310756510 310756517
    0x1809150207030c030c0f02060d1b0e010905131104090507080702060f0f06040e0d02030a030b0d0b180f03040e0a0c030c301506032d0c050415020601090606 68
    0x359866030b01901e0810111400b400748801112240c0c2444002000881d6460b03008140d00d030340304440400c82c0d008007001070341410701702d144550580c0e0250107151a83d8a01005031600d022680c80c010401c140480c3e00030713003443c0031512b44011001d110384940c0a0400350800860108040c60407290060124400a0115046500800031300400ca0004a4155007203031094044a800d41e40d168042000b03882d0004e42c5003a648281d040c0108902e902101070601c4080366981800801900400c0045841c103424001d84410a08004141c040c5590191100300f450202d082d0348a84c49862012030442e00300d50300881030b800300d14003085004841c0748540d031018640780c10100550311101800500c10100ca100c0301e0103036098040c075051444200c00107403001e1103043d2030a00000541e850203840801c075600c00d84010a080400011140c45c1c030a80c1121301c030074008003003071504c5810700403600545030a410078018402e0800000c600c180c0000717072202e080a41c03500103051715490b00c4543c000f01d81c8168408401c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 310759010 1250 310757760 310757767
    0x6070503041e0809030d08040c0816090e0f0d090302040506041812110d0509040f0608031e0f0a05120106020106080a03080a061e080601050a05010e060d0618091502 72
    0x51089204100d5003807654400b00c07491a5146800407091080400695051040e81c000051844c0c4c0428254401e0703110706200109903503030f08602a0384640d42a00350801001070041440480b000354440501c58450200b00d0302d81000a03a0300314240341d12981381c01d0004000307500510550510b40030b980c1c0c000600352020414101120290800d82c0d001c000c00400c1d0340440c4081410f0148900d10401c541c240070b05c2038404501e4610805030441d030240c0c1159000341d040404068440315607101d141c0450f900240503500e807440010809486c81d80e56442076034000003c0c40b4030701c900070508024001c03d40c400e4a5195488000b00754260000c90142c0c0144210382c1801d134240041400070544c1020719605040517003042e119000c11102030b0056400552180309480b4104885814a031500c07c1210f58203400d4401d0f9980302c0080c801b54001d81d000ba24082182d00750203044a0901500601c0740119010000070801d465400c50002c0550030b8500d41c080a80b18055103040c0594030a0b075024981583c40308618 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 310760260 1250 310759010 310759013
    0x90a0309030813050301060f06030f060f150507080f031503060603120c1005163504031b0507060f1d0409030522060906210515130b030607050304 64
    0x4030290100804900300072900780c4245038207440300406440d0050091041c3d0351100f6411003400d215203e0080040c1c1420660846003809124040c159400c941128094905082007d42c0c003034034a5900c0c0301002001c0080303402181091010708694010400416902d00b0078515407100b000199410921036081700e018001c070f59a000070f600c002040d43c1003d150301e07017143d241000d05082c1c001254a994a08100410050359148150b10000002a40742c0d4940341c00600d040c280403040808040307007014103180310210813202c507280440c1e101e4401d1410306c0351160300c000b040ea07103d514000201c42c164481c54040c800720340c000e501031a8030356a602e404500c2c002c2812a05442012001c0303018083c958440c5107a092611034011204c2010b100129180e4910040300f000818102c075104640c0080d400400100c0e141c1d02c070ba410441c0080806c0c3c1d602140c1c1400030a07100041c6030141060540b0020403822041030344560303540d0b08950315031080c00900f80700705405060425400070202001c01c0f03810800c220 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 310761510 1250 310760260 310760267
    0x12020a021f0c020c0108153604030504140409140709110f04120c0e041407050604240e030d0203030118020c1c0201020d0203090604060609020a0c0b040807020a030503030f090a03 78
    0x1c4012824a015144d0340c61f025040841c411212407010f401c41401d200d180e0b41c00c0c0a012000500e030004a2070079804403400c8010701aa400103540040000c1c00800c4100304400e040400401580380042000031843d41665a4201c0180c10380600c0e4115041100c4c100080c0007244a1100d07c1d07280107411501d081c2410074118100d115034000c12340c2c0100358400340c405000800480304081c06070030800805030b003884d04280b040798098001480c00c503c2820008502400c2c00e02c01d40301180e10100200300100507001109416102e2545030408101480203811220b580800c00403d9545444e00503550303950410700c0d8103030300d031900c10030012195004100c400c0043d2000103039a40240100802a81601910907049003e4400c140303104080b24004018044000c6001c40d909015501c1a4030802840e541c0f600894142d02403107548502090b01640248041884884070f50350141c1b0450045240502e80c0c0d000039181941d039002600c142c0e101004000d60014100400c94114400d0b0009000049080c1c1e4000e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 310762760 1250 310761510 310761523
    0x1f0501020d0c05071e030c08070f0e1b0f090a0510140703030e0a08090102010509062202031507020106060840020d0b090c1203040e060112020a021f0c02 67
    0x12000c01c1036100181050181c1030103c013016142d02028100d003410303000c81c4c4441081031400f003a550001005d81c005124040050490119030440650720001454840e00c0c4900b61402418a070f42a4220004844440a1031005184180d001044540c0b510100300074000e50801542265000c0d41174490b9040341c09401c1080c0d055444200c04c4481e0b650003051804034041c2c204805490001e00c03504800c0c40420100074040d02ca088400ea000304590ba44070f681031030341d9000a0714a490703007210580c3c4050b101c1c0c0000d004420881d001908844071a940102d1405201d4401c032800c030010307555880240301180d40400c41c1c0307070040c07a20010541da0901041d0f0031085e050004c4072035070000c50031001ca076092101d9010a00c1c011900103040c28040c0601e42042c81c003200c1c0444004142d801880c01240d1140340c00c428580744108110b00440c03c4c0b6080c00c0c440340c00e42902620f064184150303243c00c0312001c078041c00108040c00b10b070340c060b20300d0b2001c0040070000308c282c118850042034180442c2942d040e6000424 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 310764010 1250 310762760 310762783
    0xb0303030a020306180115030e0c0108011802130f1a070305030a09020a0b1209060a090c1e1a09041a1008180a03031409120304030c03030f050f1f050102 67
    0x183c0c0c81e1038150010300102010702c402e0012280b80d100010b1540c075a00903188803400c0945080c0010b9001c10a100d844002010345035012600f1107006003c4504003950014914024100040c41c10034280801c40c080d0a2990182c60100302c054000d202d000340140e18006000504080d9a091004a90780640b880c00f00510944585554114140966440030f0500300189820360540da502e65640142e00030034802120840a9813040d48041a0184a507101d001000364021254800413814894601d00340592007145a4205960040205410300410500561105d14041d01a80d1300311050070b000c141d641c0e004102d96591048440052691039406d92602070361000e1401c00000d070786e20300321000d00189801d100c040c2807140e103000350704254040d032240e480058400004516030b529803000035a107000c0004401c150440500205001030301800340030383e07264400c0c240807170303a04001c0301d106088900c202d44051050f124101802001518200e00018050120005009071400c0000117544c40242c01c20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 310765260 1250 310764010 310764031
    0x9040b0c0d0c030903091a09040e0f030301080714040b210f0102030702030a02060c03090a230109030e01030b0108040206030c07020112060303020609070b07050705120c101d040b030303 81
    0x2424004400200e51140058000410914550040080007013030302580c22008103095100c041000b00d10391404c99942c8241c010400d10b050710003018040902403030042000240301c0c028403107500c003030288003550103064804024007080341341401140010000c0107280e0300980c9002d031030000c2a00d8140d80c00e40b03102d02c00308248500b81c4ea209c0700c991500080c0f010b07012107948003100344080940c4c044003c210803c035680c00c40e401c43d00c072034078481ea013071109407201031032580042e10780e40c001008440d44603450001c40d0034284401c4185c880590039a841c41c041140007400300c40451000b9a058403900d800940203203816499860940c1c0030691910002d0200c0c1400300020801c0d0003160311231041c07142d04c561004000d0000c20f54038540603582d1541554401d00d58000e10307502150021850042c2c0e501941c11400600499241a051001e002000105560103000d0403c0c80e00094490f040403501c40151f55507031781d2200e10042c868808000249151310b2040e0301b04600ca81c03642d6400800d813a00102200d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 310766510 1250 310765260 310765283
    0x1082b0c061a040c080a0609021908180303010303030507030c0c0c090f2405032a0d0201120920030a08040302151201030b04050c010e03251809120c020904 68
    0x252410078208949407803e61260601a0054140740c1c0410458003034480c2050178071400c2d031a020382c030050b4042c0001c04c82084030006550034086102e00022500724aa0001c512184034480c03c955040d60310903001603000c80c0d141d2060280c140c0e45445810440e0003685460211156145c1e274040840c1c02c0c1c3c0c487e980d20141c0314290041611582d03442182440110500301460301d40c04803003190311800a22aa0f840780c0601d181c149980304410544031141d1000d20000381c00c00c0040e03020404020303500c00d4140c1c100003c0703800011410105100300803005c0d0164440702204d038054401403030456442040c02c0d00a41044c1642400030b584501901d0603664110707440d14a03120244200b038020300912503c004010907050002041c0f154443c0842d004501440c2078802c0703881c89200540780724495185040d010f07404030f840103010b000c0207800c951001e020b150a081c269503884a0003020a003500c0d030004c03445542d90340c40c0410003031340e00e1003049070b4101418440f0210306030b0307000030708c41200c010009841c040115 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 310767760 1250 310766510 310766531
    0x40c120f0605040c020705100c1a040c120609021905062502041b0e04021305090601020c100f0801050301062105030c0a0f0b063a020901082b0c06 64
    0x540000c1d014100242080040225110000b591240284102c0d401454401007540070207124581c6005103d420030b11500d0903030300d62003880402c10001007043d90b15440c00c00c0017080554171741b442007405501403040812216100e0040002c1041c00841d00d440c1c1881c2550200025204d84060328210311800411041050341102006da0580d90b00d01c000354060301d041da0303071414ad2603003a040c5c03150701c00d9582c4d400180a0313140041c0002c0b445030345401140110780307130410061840d00208c00c4e94012018415222807907200e401107413107400d0041100b00441d000c807001816856125841c03c5c010719007100280042c0d45000e040c0842c0706180800c041c071240260744103209111041044030395046031141250b50301d1b42d203400c5c29080914225800c8a0014800c40400c1030b9180134040c1e5040e6803040300404580c0b10358100e02d503440350a8401580276840c0c0c980c0b0342030302680d10b04440034002e04030b48001d0080e04020060203003140032914604284030031041031120450368040c3c0e018a0305da41c0f0010008854808 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 310769010 1250 310767760 310767791
    0x203011d0601022802100309050d02030f0f0c24061c0809010818030a02060a050109020c15150301020c030c011401231f0c0c0b09010c0f02120601060509030c040c12 72
    0x4503020307400113031040c80031b010300ea407542c8030a04a6000340241ca00d00c550001003261a4400e41c841a90201814000b020001c8100700c020480c50b172506046980180d006500010203da4290740b90a0301e902c03400400459061100784c1440110b00c102c0304000308991b41d41c07994001d00400c80401c0c100010308000900201200104d2041c41c604541103d4440030700c1a030080d80d4140c02c54658490a0030000001510340302c43c001e403000d1200d260050070404111035281c0c030701d00c42700420a130301c4404510000b03501c94a00780300030100b003558240556510340030041d6076400c0d200d16846011103224030307500400c0b2020340c20401c1101e1110070481425242240000107840324860000070203184400c0f400080c00c50380080701031600703c1c820080301c3c100702c0e5112410199405000300c1140841c148070421000a924150600010f5200401d564400640c85920304c2c50304501f41c2160021503000a2001103d14040005400000c000c45044c0f01981c1c070030300c000784074400450b2001032190300d9401e82031070482c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 310770260 1250 310769010 310769083
    0xa0b0d020403150504021008060d2a060e04051015030b0102030904050901090c0506031b03060d060603081c020424092103031104061e0504050a0303030203011d060102 73
    0x411003d034400040030b00341c0480003058140c0e412846950700540030703c0041c0c0070b4072143d8481c140003045c103181e00c10f150701c400881585519072441c40426644d01254901c0c9041084000b418259403140512050007041c4001c5610242862105070702011003082140101c48014983c1340c001d1401060018110005034514042c6607121a4001e041400f00102080150302c100013050180203ca084030fa560b8090085910003500c0c5400460350b002410050300c0440301c015508808042c0c0300b452151200d40f2284d0842c0c0040d00202c0c0c00140001e0224821900312800d045803150002c011850a45400c0203541c6ca65592001c05185000e1f10304042c6d02c25000d60207490003840039000640501d034048a84500040780a0004c8001c41e242050101103610b000301a141590703015201d0944100e144400000c1028110107071100300101000003083c0c03a2222a440c200842c4261000768580d41084002c44a140c0800954140350000d1410031000e0381e40050201c90381038681c2c6259044903a050b121440009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 310771510 1250 310770260 310770263
    0x130204030206030406050a0c08040b0604090503040305070806070f0504080d0806191514090f01110a05101e0510061202161202070e0108060a0c050c0105090d0f02010b0a0b0d020403 79
    0x200040f081006005641e0002071180306625400c1000c4007628600341c1d03462005560142a401d052400520f450500341e10040005025508803410260303079a450310300d48015500000e1858005205109580b6001022045070103260b04015040509003841a07a03108011144d003030400c46c1c80300c0030031016110f410070070003480c1e0301041400e401c030340310302c0d5a481c8448000c600d234000a1005c2c0034551000140310650302170000003483c040390144000300442d08011884440f0034240a10b0b0304050010b0f408109012001e800480c011508034000c030400700d5200680b0803110402401c0c407040011080b4240b03e25030546446003041000c83c0c9940a0541c024014401200d4031207072140031050910200038011922240f0707a41c225554252100031a40070381500388580314180c0e0102000c02c0a000d900d42001034030500528041e410001107400c41e41c00d640060311000d1003034120b40e80492251741e01442c0d00109070b000780000c1c0020000500420010f1f6405d11860085180106114290f1841a0100e03030085 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 310772760 1250 310771510 310771519
    0x70f0830241f08060402070c0504020309031603020616090e06221112060307050306011505070c030807060510050114090303040f0b120f070e01051803031b0601080f07051302040302 79
    0xc0030100d00303030400107142c42c0d806012403400390010f51a8038250084030710b069072060305076604034540410f11020350009031082c500350105000c500c80c40454100d400d00042e000b80e00600f418100000703660303104420b6014060400c44440006e01c801421b2450342600071800f80d40614520510071407402e100b025261440804905004800d2900070f40b1401601001c600394804c0c0d1a55211074040582d07800051147c83d03050f4100800420881c580d4554914000c000b40c10814a05409a42d509503003800d290011640703000007190560500c002885841e502c026a641d0001c4d401d800c10001030280000450715100311b4600055060450b1818401c1d100100481c5401c030803c0b43e1035468041031604440100349000c2c09400015041c4c071001c3c505140142850f84414108540e048011203c2e0791180c0349080030082c046859240791380b0100010a4890b45140400b040d0307075005102981403400c10380c0604c043d03a020503890031280c6000701c1e004080320400c49102980c8e1800d0140c0e18064012076001a511 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 310774010 1250 310772760 310772779
    0x905030a0c06180e010b0904230c070821150409050c0d03030f141e01050a0b0309010b0a03110111060402181b030c0d1419020d02070f083024 62
    0x2102a80f030003030242010100c50509c41c48580c41c4c5680014104000d241c15503092501c01724164403946002092504e00a1140307900d02042031200c1d202001d04401000c503100480d10800c80380c8200302c0100e00203030100304e90501503200e5940302c46540c0d40312818581c0c42411105a510201800313640692a0306040e02d80500003c42c1040d031070545200c0c219400780c1c000751103c84100424441100c00c2d4107072500107000010103402d1804070600c075000102200034540d42c030702c6401601c0d0b9404074207a0085100d4140036081c07280030790005100004054010741d83d58004400d100050381c68030001500d440e0105e0302d0350416595652480098210460710380c03108031000090015451898004101609411505014166445040340e141040403a1008005135a82031042852140d80d0003d0411001420015003094080c1d20303811121003040b403049401d4440042c4c0d01981121103001294400740c1c020f5030b0310300c06004021600e0b080350000c01c420091612a800256190420745175070140c0e0328050040c408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 310775260 1250 310774010 310774019
    0x618060e0f0414060f0105040e0f040212101d071d091903081006050a020604030e0307080102040f030c05040603020607060e1c030917090a05010c0602090d0f030905030a0c06180e01 79
    0x5520700945866001e0340910341703070700340a5005004440032120400400c240c01d41c3c681101184030180504105c3c0c3c000350406448a4810040140000305030101c54001207040d200c0d004120129001c01120f001500241c0d01040074039404e4034100120748040301449101d5a0303481d03450b400c0120300340e02c04c200c00c0c95039141d41003410b610412051141c40521500c417916a1980b41c1038616001d89030301d40005901803000540064800c118581d02ca610180480b0900c9407180221400d9800c01d401c201c0720080002c80810510487c509900c00500301510200115400d64010900c3c83c41003c0b001743c200794031180101c1c0780100400010010103c40080f40b540441c1144006015090b002811f4404a00301003600c00024403c10480d01c1501004060080c0e081c5030800548142042c031009841c030690900001c28240c682008a0118600c1540850080d030500c0c03802504610a40d08024002d900646c1c005002071070400080b81079600e1170400c07a02c0300620300c43c10b0001c1004c40e000a03988003170030000041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 310776510 1250 310775260 310775291
    0xd0f170415030b0102210c0703050f01020a03110703080601080c13090c021b0307090c02030c0303040302070305190c0909050c04150503150606070b0601090801021207090618060e0f04 80
    0x100c40328520359003400583c1903107004980d0b804900c4c4822081c0d5008071800c0003640d6514008020b43c14100f400d41d03510607900e0b12a10b0070071426032207a89d02a5000548501c0050341072180c001c1400c03801c52245d0608aa83d21b001385008801880141480700b03a02c0401e0a281003e4142c85081c118101c80e90f6000f503c07031188002814901d508003001d80f05000b00240012a6005a500901e03c09402000043c1c03030003029801603e1103542d40d1040d030100b0415821144000d000852003240250010140249980740c20fa1620000c201d9280d9510b440342d44002c0080e0203500b62004442c0e03804400305090949042150520000082903075000d03103440241d0000722401103c11048a50840c1030b21007010342e0006849101004480b1194010000c00c90b810014000419180e008030040c50842c0006072a00c1c0f020782260312070080017684000090030482d40320f030300402d1040a04002d103060954141c00c1143d1102c00401800340405019071500c0300b031000e440d00c02c0e2019a80c90000c009115036141040180d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 310777760 1250 310776510 310776539
    0x90304060305240112020405090c090a06140f181905030c100219030c1a090111090102030711030c060f0304020414070c0605040201020a0f0b0601021b0d0f1704 70
    0x40001c6030a0000044803100c041c1c16141e1401038050401803030303100d20030045072201c0c080400804400da00f40310220b038540301d108c403144c841c25880c060607a85244080401034240d4245d4043c00c100300007071008860350342101e020307220f0702107020354155103600001c1c24102c0c014225642a5400203241400224226261455071049442c2a006d68016901ca2030900243e001c031303c01c0b840003581c8004084071203000c1e01b1200c0001d60f8000e03e0109003134040d5564801c4404e45c030802e000c0146407418140500c5100a12803040300110300c4250501e031000c0440081d441c7c0c0650f039805885090028441c280644090151041c805070041a140d540c600307965100d4840c0c1c10685007039004615090058641c6072905140b98001d4541c1c2e10355401410389603458070050100100124118001c501c00000050030450251240c54800c807105041c901d00306000a240c0b641940e61000300e0002280303451074a854010980b041c042d0403e00580ea5080036061155852943c003070011180c10b0001000100410000c445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 310779010 1250 310777760 310777769
    0x303020415051b160501080a0b0406030813060201090b19060e091605040501030804170a020d0f060b030601030312020d180b0f1005060406030f1407020d0e030105090c01030903090e090304 82
    0x141c00742c01c0450300c526980c4d4035099030314018405003083d061000307600883c0302c0e41e44000c1450010400c021140c010605844195004031100840420030f00e1441d0003900780c01020f0002440204815416174480c9681c04034007030700c003400c04011013060a41180311307600007030050031401d4078201403030412003c55070f41c908524016402c480182507000c64945071074002c4904884e007180c43d041c1441e0030200341d02218085658681498070410b1311207001601c400c4a10420503000c0e02c860444044503042c1042550b0b0301141007442508900b0051002a820840c0d489801e0340e030540043c4c8503884000100018272200c58010703c1c901540044a0800003640083ca10800310000c21941503110761511060110a5004040e4000130900050107000c1c8641e01c420401700d200c2d41c0208007007000010815000310196028001078021003e41468150031001c0204465429030081000389000031400b911011030104075410592100450814140316400e144003905900100e090070782404a10346680750701900c01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 310780260 1250 310779010 310779037
    0x906090705070c0308031f1202100c1e0204050a09031403070e03070905150a030c14041d0105040309060e0303041401142b0605220f14060906060c19030302041505 71
    0x4541c03580d504502c440c030b002c4512407801d0042c5142c827a800c10807800c030311a2510042141025003200840d503064824441c02080040303200103d8201c1c010702054440003001400d40c3d89c2404a0803002036480180c2d0011091144411500e80c1c982036030480f803410155080e2030f8140700780840030403414000d078800ca00480650090300240021030090246440e603510010b401022011010481f10301c841e11800c5980320b00401c0001d0068821b03061006041618040b600641e640740e00700010103401c040107c004cac1ca0b50b800c2c80e200000009000a42d41e200f50b0142c070040d020540207c0300182d002e015407507400f00341840386a80720f508410728940c481e201d240a180034030001d06511001d5007881c2c49010207032100a00a9060b580718003000104022040b00803511607a510f9001800142c400d20030300c001070710700d02102d54075070030184100b01400e1006880b80b4841e520403c2007202100d4001105a00d10303034454401000c244180c1800e4000340503980c07003d45820144041d99024680c01402060001800c24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 310781510 1250 310780260 310780291
    0x80d05031501080405070603110409090f0303050c030615071505160305060a0f0308030603070f090906110f1614030a1e110c010507060f0603081e03060906090705070c030803 76
    0x1101c41402c04d507009000303034200c114180a02d6201e40c00c004009040440002d292540e00c5418400300c07200c562041c2c0e140340e080c60624040551502640e40c02441001c1031a05605219000071051a0007854003482144001000f004004a42d0740040d0006d00030f810802c060710300300d0340c02214945400c0c1800006803600c00054040d103408940c0409848454070382902e05810f66031020b80ca6400500495807500c11101c1c005140c0180c140000040d0204650100d19076900c0d1900303405407510312041041400c002e005204510000c00140c035210340b2707440100c0b19a0700240c1822070f40c02e500d2110700d0b04640030015203240b2301c40d044805081c1d00e841c6d00032514920b0807562011540e0460304481101c1c1c5410000350076016600c02d102800401b0300480c0001f4000d201c070901c4104607560340d0700403111540040340307000301c180e000842c4101141c50141414514a80640042c0074285d005245a01c00c1360362002148200348500c00b545c012560202125070280c4e140c0c1004c5059820031101e10b050300d000701 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 310782760 1250 310781510 310781551
    0xb0306100804030e01030905150c0d1508030711010c1703060a0512100c090e0f06030705011d0108070905041a19120f2f0a0609060503041b080d0503 65
    0x1008080e02c42d0741c01d13035140c1512102040c01100600a00c481c00d03519071042d00c1c130702030b4a0034034545458000e60300e0210740b95507214941c103400250750600700c1c503404880002c00c00b000403440220864030503550100141c0142c0d07080b41b0050701c0c18141018003030039030b00c490600c6400e0650040c0080d400741c2d81c1262101e919590301e00800c0301883c03003406014000d80044400071800740c559040f0f44c402104504000010948641c2070182c490303c02c40d60446284200c0003489040d04090140318040c0c682882d021021040307440c00340c050300382506030312410480301c2d0001448451180745202d015041c001c1090107451010010304003418844000c4521500d120f00c040302c41c00300305519501c01c03030300102449025040107481d038082c1045440002e84424000b40c0d6507d024051200b182030031a80003800481c800e00c524800d000d5807500313541200382803065420090111540100a27a50b00541c07080c036240c0042e00034200740020b4040fa81c01030905214000340030300300903003100142d031298182e1400c40c460301500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 310784010 1250 310782760 310782767
    0x70f14040302180c09030a0501050a14040807140c10020a03030c0516030507080d150602160b0d0f0b0405090718110307110307170a02060a051b0702040e06010b030610 73
    0x2644802907100f840b2007249900c60302800b248950000400360070318184681000441e082807941d0b441103410780d54403020011440320511541c0c2c030818240990046030300c1c050395040594880c8036009000324131181200007981e4010042e50482a4000d04422484014210040d603544041401100441c0c00c02084143c0b041c800ca042da5540d8001c8000b0f03500700c0a580d101a503043e44640c40640d40c4000401955100c500d0781c0c003540400d100f403058140c1011380342480013400c1031460f51058414601683c802c010304074002d001e40714640c0d06400d0010b02c0700030100103800209005c074156900a410070f0f080144000d00403400b142260b0240c01240d40010080b00f80004035603480c00020120102800824180b40c400d084040c0d00d00e18000440c0c0c40c1c852551a8103020b44a04960420b08220020301070b414141d060202035000003000ea02031140e818000b504a020141b11000c00390030340c2c000704071b41c1c05650701c40d00072069540034203096843c5035071101c4126005500454059001d801c041c0c5000018512 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 310785260 1250 310784010 310784017
    0x3080a1104034b0f0c0b040314030720030c0d060e010b0621100806040c05011d0901060513031a100503060717060607150c03050a061a0a02070b03070f14 67
    0x110002c01848071051003c03002d241081d14030709850000780303424014000748880c08405c0c081c10300000e09a0300d451442c0b5040010010300141020303583c10038007003c400901120380340000141c0f280b030904505002c03140820728181103005220740c45183e8444820030f002d0b880c0c1c0005400001b42000703108191140f000c0c0600b620529000110721110003114060f01a21040d00d5070b08a1414414210010b80d242d150702d20b4150240c40a0700c0d5003418900c01c11071903801081120341c0c0e078100c2c980034803181c400703000040108405205d2642480340024001040d1021115020003441e40007911080717010040200741c6001804444291407a01c40040c04555843d002a000c4d1281c00c4d039940c2c4801c2c0c0b4000300380d5850601e002421445c0c120005109078800600c007035003203031542d69900c0000030344071800c43c0000b030a44001400c02401d5030701e8070800303002104403044d000703003801d20b82d130980c99035030051313200891820a040d400704a9103031001c014050140c1c0d00c042c00844400040c1e50704580e045181412218510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 310786510 1250 310785260 310785353
    0x11160c03050d2d05131e0e01030b04200d030908070e0f1f05060d051509010803090411190f26060d050106090213170c060703080a110403 60
    0x2c11141561141070642c101842c00c50f0a07450000d06003100380b10101515641c0b500854045405c092914055401641c0b480700207010040031b080d100d501d1030b200c1044116001c2e0001e0a01800306091100142280308030405031031000c0d00b001c0107041d040c100101b802055003d0055140101400003c180011154450041558440c000c040d5140c00f482c91000c109141c81c1c001b01445004400521659043d001d440c040301f080802081d10b24140350f41442561503030020318418100c000052021803c00401c0c1d42045078159030001e17540e60500131305102e500417132107130240107690340d1002c081c803d0f03200d0300a4440310120b0722144d031540e480c0011155007184c480310302040d13000080d000515520340103200d40200d90150000091080c0c0310b9020a090741e1240216110392004540d041003080146003001d5108000307100580740985140c40010214070805d0b102070101f140200116071070100c69030140d154403420080b400e6455a591500800e02d441300495150180040c03200659030880d032a408103c200c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 310787760 1250 310786510 310786547
    0x90207031b030e030102070305040905090a0506010b0702010e04020c0705090f0f040b040312060b03090f122a010603150c03150b0d021b07030209160c020411160c03050d 74
    0x20104129660800001c4035025010028020034100f01900c083c801000c07254000e6903030319510341c103241d801c80170750304050807540c0c00e54001e00040d004501c002c1125030554540c0c0c1c09440d0b996034503000403181220440e0400750300610005161000320360026440003103da056490280c2c0e40e940c0c2462140d030300e42c04c99282c150304c066140050b00050280c41901e90151003401d121030001cac484402401103c90300c0d0050f8841110001c1801003450040100b4141e03141d0360401402c403908229800c950714040e01e84080418000c494070710000081d1241e1400003514120020018147d81707040141404034070300045401d4600e80f03449201110301c24007d9891204581c90340300c0c3d28520b860b51004482d070194503030a42c01603087c07010302405c00b130f2144500d00100703514004001e02e609500400003210b5001d455240384e40c800300341e50080981c1100710303c4040381e0101e90008042528074080c04952103200400c480d2040b10400540811000144c15801d0b41d0082040b1150384007000402d803004110050f241400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 310789010 1250 310787760 310787777
    0xc0e0417180907031d0610051e0d0c03120201020301240816030e1e1203060d0f0804181b360e0f180a0c0608040c050603010f030203060109020703 64
    0x5051008190b03801000f82d1074005580440d0401709004414046a1401c0540141e8241b0002c40d08050b54900a4003080f1084011450071079051192005141d0025000d000b440d0802810f201d80d5211f038000568100d0415020885a0300c3d000b4000e41c42402003d4500b100c1154a455411408491400c8042117032122442d5484817a00c0c005403860010303400b402c00d9250035441d52100c200384011058107202d50960100240b100440c01d040282c00006280d10350024002c0003029528600c400c0e80c03082d00300702e0400101d03200d824a00c84030720813600410203a0340550034201c007102c8150b02c411600d01d44c4501c1180101c200d02000c40341c0d020b00007040d801031481e0807282c01c48010440346d02c2c41e48010401c00d06142c156502024079800c40103c0d000d1084000b13075010410b15422160381c0900103036002018000104503039031080050a098001d242c1046802c2c00060200445140f8040c05054010082ca4030b035030755244400451455070004a021740108800083c6100c228001d81e0011941600c440e100e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 310790260 1250 310789010 310789057
    0x1906080d080718180b0306090a020a031205040b04060801031109060102030d0b030307020a03050309010816080c031806150a09060f09020906070b040b04140a0b0c0f070c0e0417 77
    0xc041140f0b861140c03011042c00d000060160129a4007038a02c80200804a110000c01701050b0518400410390111a0020f00d60303940140d56181104041d40c1d48582901c000304a405e9045480c0d01407074000085401d000580820150b412800300b9040b81e205d400718039140c00040342440181c00003070b0b0750640903074014024a0b510104a0b040341c4860100501102d04100712500000d2880106074411f44098000080a50b00c650707000c9101640b003034080301c0f00804102c00f501d00800c1e0780801441d20006030004004600080b51003103001c048a000a0129421801d111181d042400e4828441910802c86194002611410742c0070308070481e8aa1018521007038907100c1c00401941c400e01d0400c0d80070000b00080710000b0700c0092028015070141030540840c0c80c052410f605003000a0321310114640c403003000e100000324815291036204030f0107071805480b1040174501c0750403030040743c0b002000b12005440110301d0076440380c40705104034040d10b01800e03900380744c0d0f4403000035100f1201000b04460203202c5046 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 310791366 1106 310790260 310790267
    0x604091704030c0e131203061205070501030e0d08150f030d110106090908030a09020a0503101b05130909050c040906020c3c030706051906080d0807 65
    0x4c035414220340309010380c14400030003444065071a03440c642d014404e80107000280a01c80c1b502413803c0c11860b0080d118035460117042d0001c1d240a19041c00d1400004600c0d02c9941c83d40ca07110020340710044200003810002e82419001810421611040e440801100c580b0711101d81d10100c0c180000c00ba41425205580e01c002005805c081132103005c9540301c411642c200262910001d2000340034404030704200c0f41907000c994980507115405c0d07594103194100064141d0140c1020b0001d4072114416079990080301f0349a003040da03000d80b0500c0601002d40c001c644141c040c0088a0040c401800082d0517251401021501c407a00030a003c00c404404008440000c2d41200f0703080b0b103084c131101094503280c44a510040440910380d040508020003402168915900007005010501d02000c0c2e0a20b1071100c550101d911a103011000100b2500102d085210b1040e15602c02806840d49c0704200e = true := by decide +kernel

theorem cover : BRFrame.Cov 310611510 310791366 := by
  have h0 := BRFrame.cov_init 310611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 310611510 ≤ n) (h2 : n < 310791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
