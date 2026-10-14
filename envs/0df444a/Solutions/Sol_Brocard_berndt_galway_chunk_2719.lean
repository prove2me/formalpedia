-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2719
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:32:35.811491+00:00
-- url     : https://prove2.me/submissions/1ebe8726-c84b-4e4b-834a-ea6e9a04b910

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 488848920 ≤ n < 489028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 488850170 1250 488848920 488848931
    0x1050f13050f0d0302190c03060c05030603060108071a0c12070c090605010206060616030e0a08100b0301020c03040303120b13020306040b09060303032205070f0608090d0c08070f050a0c0801 83
    0x60b00e07050f59020209a09a005800c0444210100806242c4501c0c0c2c1114290041e010100108800c0d10464542c0a01d03519403580e2410248109450003074164050b80d00380c0d0040c482800f00e10400302c0070040c0904640ea0003500c40485411007070070312030242000aa64a40071800d8401d102201200400311045200108095034591004a0b00c600d8104e0320250007510402c103c041983c0380540301c0700301e07a010380340c000654108180080c00d810000e90040f940380d480854411131903421403007054040e0000720021854016000902c030340700d0040748000390038450140881e00181c2102d81115014900c010020041550081d09803070083d00155090781c020ba01d07105442d40e8600700001624060750b4002c009509594400c00182d018801e150820b088022030307800c41c1d20014508215681c05440802c1000100c9414060700418541004001485c150b01002d8100e100d150000d0010706116080100640d454985040010482d88404002003061040c1070542c41441018800c02d015580003030001e010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 488851420 1250 488850170 488850199
    0x61302040f0303050904090b090c100207030c03081c06031a0a200d060b031801110f19031b020616090803030c18060a02150604090308130201050f1305 66
    0x4034015806200c40c1c50805041c01e00109010f80054840114010400b1581e04032503940c4500610042d1a1708134140c0c4240400d03003c51900c000c0d21104252144000d1402600d0340e22504240c0720315100241c5008030005110b003030074884503200c0100e00e0000e1014405a562444d2070301182064402d42406882d4010125240601c0383c054220542585c5086d00e2401d0400020b40b842c951122000084a42e550500012000c2d05813005d18803034419601c4504449801c448604d080d243c1025501e4640350080140107104030128050325110700070350540108500700d8940950003480301102c0300c164003a60341c05a41c41c0640c0001d14034802d6108102030204845503003c25240712603103000c1c80e1100d8005200042040f82d1202c090070080404450004e4100c00810100700594003040d00440141c1107001402c01b0800c02260b182e0300321800b0788003042040603e0b100145165005004643d0100c07000d240340055a01c540103403804400b04a4081c1d51310081c1c1039801038120550320481d0301030340c4400407001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 488852670 1250 488851420 488851459
    0x619080a0f051612230a0b01030b01050d0305030a090f0b01121203020405030a030e0312040b0a080105100801060c050c190e090c090606221401030e0703050d0c1a0f06 73
    0xf04484610941c1d240b9803c0a030341d8142203c0d8025214a500c1c2e02d120010175046004101140c00680200d0b01d010f065411402c3c5442c85400507080305004400780c1b010702000076404001c682c0e204545800020381070007145071030300c20f82844100140c80f6a03110fa0002c50070340701900914105a1045504c1171510100190503001d0b0300481c4941070b0300d03810001103a80801d0140070f1340024001e0003015071b1700075061203c04e00115082600310342002c1c00080b403210b0380d850304900f81d5800b5110403104065001c0ca51003005211030340500031141000110048603081102c00c01010300400d00040100707091000024401c9110742c181d04c02c00c46600c22110218408040c003250300c241540014025040c0c5a4602e81400125840000b030701ca9180010030103244e9510400c00400d010380002d80490041216050004003aaa000005110796401c960b104000050340081c90f400c40399480d0612641002c0541091901c03d20007a421b0300b010310242c8200b00d80c42e80220b0b0068481c01c81250b440c003060450b1110035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 488853920 1250 488852670 488852713
    0x3030e01080915060607110306010306150f0b0d0c020a060c260c0a031d0a060605091f0303120209040608070e0c04060e01080406020403080c010b011202120619080a0f05 74
    0x2810f40e101d80a02152843c10320000400b481e500031543c590880c01882e001c45c0c40c04000740d1054031b159960700c0d100c03000803601500c1003008003c90038100c02914105604c80340948520600640525551142544820b0090041ea003000d9040700e42040240c2c00e103403000d800f451241490f03602d80d421100c800030001040c0701340240200e5400d0242e88c107000384850300fa4000c01805009480001800c5012258200d003045045500c42c860440841c80f00c2c501000e1101005000c2d2a401102072408440103001004007402000c490b00340c500700011340c6c0b41200090091080d51500c03a040341c1002c03408a0940c0e40007408070f00b140c22455021240f5a1000d20342c00b600d0282d40510000915501002c10081d846103041c10b4020707020380001850a07a40b9540c0c1d007015845030f06064407594586843d03111542e000058494041d403484000d41c94210790025106032000700402d441e125100b001c0b030410003003c0d0f00800402601000b002c6442d0780d030341400c0800403140b102c501141c1034841c880308108050f0b098040c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 488855170 1250 488853920 488853943
    0xc0201030e1911010507050c190807090905010b010903081606020d1805060c0c06010303030b01140435070302010c112707031407050a02211b010b0307031b0f03030e010809 75
    0x80c4c1600c299410802c120729080d52740e048000c4a80b98400701e1550b005102903001442c100d600010170720945c0c0b50090030740d00751040c11414031079045c10400c0803855140403511500052240090b20704040c3c5404e100900035001d80c00c414601c0c10f25010645c0c03038000741d4440d605018004807107a694508a50002920640b0b1444020b030b00a02e0040000a000c0d4101c1b2203c2c01c41410020300001c4401000d42d042d4119510078400c1d2000760959000c0d90300c4503140d288410300100810300c400c40b071003217840307580f150039200090411003110032a0080c440a20f00700c980d04038005002c0c80c1181160b42c00c0c0c00b64000745801c0c5140120310f000114105e140a8401e0422076078425115201d0355880b00b0065600e9007003124403000350301808245003401044504000480080c103252184c0b120742e0b401181380b014081078149a1a030b89030610ba00c00c1070341c2c0024039000701d0354003079040e40380f451480c0b41309400c15009a010309040c1e0180303040801095040000c60808201c02c3c0c1e241ea8031551000f044a695054801c0c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 488856420 1250 488855170 488855173
    0x120204050d02120c030a0c051f020615030f0304120b0f13020d080c0d08011503020f090d0302030f04090203040201170402010c02011d0d0503090a1508070c0201030e191101050705 78
    0x22207001801e0104a008110340c0500603140031100d080042418007488907404c840000646006000b14a07250385c030414502d10310080f6070180502d011000e5543d440251503080100841000c40b41155800c00030003155007040000d40780c40d20b035510703080b042516040c00e003140d003200e6000005e00c00341290fa8115115410000b403128001c00a0740074000e000c007440500f5554132908002c4178240b0f5a0410681021000d08da985c0e110a43c54010b5000e1030b03e241c4a841c1d810180100980c0c3c6125030b00c00280c6504000440f042c803600c038094541685544101c030b05012038a240410000713070343c9026a01a51265000b0380314000002c60725401e04040302e400700c8009011501217002c081c05540300d20951030450a0004c0390407aa02200400240105000c3d0400c8425500000c0e0610480c10490340308001007904a0040d00040011007000c1c0441c1c1000300b160081201114003c002e6a221307030031100d404001c00b01a00c0701001500c4c074050b00401080c6c000d5035046031a103010003965108400f155800c030380040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 488857670 1250 488856420 488856439
    0x151303080f1b03270a090e061005030c03061f12050c031209010f0f11070e04050f011b0503070212040801091704080c1509100f0e01020d0813030908030f0a12020405 72
    0x6032150132090905002640000038080040f4000016100b000011500d120042001f49016500030034146000e070003550080d0401c40300880b0603140060004d4000701d005980c031801000030180f04084c95102e03482001c11b42c00ba181048188440411001001641a070a440d46204042890311180c072400c8640c6d40010056145508294406ca46003613601a01340303050074090900c0c2380040d140c4600c642040f031264607044188010040c2c10041c030110000703168000e010040700c00300ba00310814140505a02402000000581c0f41d5100340140701c3e00c03e10740e0100300e84603500c4e10442e90003003000c950100d4100202698002401440710f00342c8003119a807800400b0720065030780500006100d00054500000c80a00c24885a51b850384010f064889050f2780b241d004480340f1000404000510f0034203419500449850f442d929808049154080800c4040f407c9034001c1c1e217812031310b001c840d62040445d4080810f03081c4490200500074556404a50784626001c00d404041d030f0200c0c400da00c00c0c030f90703c44d200e01d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 488858920 1250 488857670 488857717
    0xc210c090b01020f010e0d090509040506070c0807050601030b160809030306130b04110a081503030301031101021006030311072319090f0f0c080402151303080f1b03 72
    0x3600301c410040c0301841a00e04c0400e5034840c42e800e4070014103000000c0c1d0071841083c20180e030300a550303c008007400c444400381810103444183c0c507240041c0001c0101300d0101c50303181c2072094560442c0d0019034004100d030610360352410300781d204c403100380d4150841c03141101c0b030141d680b8450007a60740548254400b171480d68865404210000c642d04081501e041d4807110030304a11b03070340c0c0e100707207400150700c0351000d641e41c811910300801071040181040810001c054040803d034a000007a24152035120501c00c2d5145024001030745000075101204003c0380c20000b0100c01c255000746450101d020890884a410f07031601204038010841c80e103035699a5400c4000540d4900c3d01b4a030015070b207011040411401921500c840c4240c03103087c8003500301951a00184106462a8854014494810700c3c040140b410558002584082c1c3d000884241d120086402e81c0e80030748141c1190b0042d03070b0210040e41e075041551104401504405464010304000072010003612101001301c075070042d1000c00c0b111502644 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 488860170 1250 488858920 488858939
    0x302060114010210020708040501030c020307081c09050303090c0906060c0a0f0c0e010e0402100f08040b0c0f0417010c0c030212070501180615080c0109031113090c210c 74
    0x7415026030440c8101e4480c0100b9661074070040c40b5042c00781c24059a01d6041c1740c0007400782d0300702c1031007441154420008040031444c080c09036004600320030741c030801124202c2c0c1000080c142029000d00f02d80000001d0000514002821000c1c694040d95030140d590748038410032010740030760180c4550700d400441811000840d09141e0030002881076040b180d050341c80d600f1001030301c00300760000802005170b4402e0005510b4108070300328084503a0704d085a007030a805c0c040113100100182005085c117003040081510300c007103002644c003442c030031030180760b2100e643c2d51840d03030100315038440e91f003040d440c040004190b507116441100540340c00d0340040210791991002020075070b006e584103440c65541e8081c0000100d040310303500c00013940910704c01f003500d00004409c032003103950640c0310603000c4c2d101403030750a581d03600455240c00702c98010703580385000d02c810800b281c111011403030809403140c50074010504000b802141c1c20203039100503000c0201820041c0030164091310b07008002d80068500340080220320103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 488861420 1250 488860170 488860199
    0x6090409080c0303010f170a12080a0f180c141c08160c2301140c0114010b0c0d02010504150203070c020307030b190203010b041205070b042403050403020601 69
    0x3007030046a2402c0c110602d0141144c1080e000b8035145e002e035031003c100003102c42115660307481040c005424074500e81d030703544140c4810403041042408851000100b84000e154007901803a07650300c60038452100040b001e1440205100c03070807601c1480083c2c021030142142c0f140304500c1a4054401128005859810920b88142c0e00044410420401c882403629007402000b645103485041c05500d100d0401400581036203400c482d8004282c00ca84020348141e80c010291007601d00346102d12540c6c1d1070003501e0703140504030701110841501d00020000034030002582c020b210020780d480c10f8405100c0c003880202d09a4030256000b6100009000182c7c2e2408160b0b4000c5420020030300f4030300c030340d80c1c11680440d003045884d40c8103540400709842000004030107441e1b05482020740c04000c525542c1080050036035400766008100151049520400401104111100142c44202100354640382d5500201d03541d1f9000c03094209042098a9030043c40d54013070701410b0b004030340c180c02400c2d90b6030034804031016458 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 488862670 1250 488861420 488861423
    0x302030c0c011b030e01021201030206130b0f030405011103100e0c0c06130b0612100f1e0c02010b011b0b07031b110f060403020d030203061908030705061506090409 72
    0x1002007004000314602481154044460380388000ca444884160241c2114443d5091100907401005407203c0c012101d294541580d5040b078400f40c642404101d101c11100320354020348100140003825440b26056030026500c110b214030000c0c0031644800800340c3c81400280c0da20669080d03280c60520664060320030041e4456034104105081c105182c2c01c1030324025003070f20301403000c011000d07640b000d026150a810f07901030419100e910b401030041d590180d071050351145111042d43c0d05c900c0440005a6a0441d00680085c0740807402a801903081c0f8400800202d00d640380550319000c200c3c40386e540681c0540c80703501e5403180850819031054841014a50f030041450041542e20b0700148182401c02042805111069441034404000004c405240616840783c01e0500da00c200304000000343d0000309030200681da4035025882c5c3c2c4030710707012802141d011080d40014210b199400325440d08004040c1001e20302a100300c49007500c5098a0f0b00030403214030342c5550044c0e8100485015400c00703400080206 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 488863920 1250 488862670 488862691
    0x3010b16021513090204120605040203070806100e10150c020d02060a20010203010b070807030c15091a06150901020a0206030a0605030d030e0a020d05030915031602030c0a03030203 79
    0x309a158001246044400001001400045030b0100210400d01003400070781840c110440c6004d0800b0071881103080c0c001d1000300380a03280c10001703003191000d01600000b00707848001c0f0744090034205a404504a42c42c05090300002c1e40e000041c4040000f804541c08541d08405000115245c0c2d10b021a11018086405da8009076205682e400503240e07039006002a5071180c0e60101c03180108100e01050400082110901d40e00500041c04100484411549910b62010145560f40c00ca483c1c10fa400e800000009403154060912040c6078131000e0f040001c205101e85450a002d056844080d0036809003a900e10744c100e004031820302e210004510040500d508140121203191500e50300060340d5a004940805020f9180e0303004120324141005050010300c01401c2c1130100030500d40303160703607100c5500310701078880c61400031a40140a42442100c18155018210102a2482e0304140010768030035102034003840f007a0703400300c02003904c0441500e260a030008060507112506803812030107500040c2204060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 488865170 1250 488863920 488863957
    0xf01151d0d330c090f090914060108011401170c0907170901020d15140405070512070206040309170718181202160311010309051006120b090a0803010b 66
    0x650074008440c15200e00b510081d00c40d4510020480d200f5502021110020300c0104003080c01207402218024040c0d60a10400046200640c185141c4c505802180f0070014007400740041019003064020800d583d84004c0c0600340f03a6a100383c046104081119031031915008240034868074905aa0740703582054103031410b48200300c480000270300403d1040d036455032160f42c00540180114214010403410852a50200d00c41074506032040c042e40092080042c8210341d10000101c7c04d5008805950200300c0c0b840c9941c291f4900040c01035944c1c042500c0070740c00702d00d042d4800260f0703a45000300040d141400002500550740b403c12895050003c600c41d40c5505032f102c00d52201410b001c1c0000e602120700814140030206030301c48000c0d04010701c00c50425840c50388c1560600c0810704000514810200a1800040f01a03042c02e0003410b2030b03070205d1001e1180b17040c06000150000c161403030310030090280b00346c91203070f48803009500e694150740d581c010070030202800100500b003c4030b40070302410280340c001c082e003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 488866420 1250 488865170 488865203
    0x2040b0a1d15030d08010e0708060306071110022a210306030a17041e030c030209040203150c091e01170c040308040e09010e07080709110c060f01151d0d 67
    0x40c00100c0d8020000981750400402c6048aa130201d40e400c400a810305510740d08180e00440c4d1104001000d15051142c4204d0100d02241c0420415042400b044c00071902c1310880031000030310440f030074903400c0c0104850461440e2030340003103245000d00f0211440c08100c0b02500102d04103581009008075450702036032403140b0214800101103000002a194440d81c0c441c1400b00140c00326001c0d02c4200307403442014006000145101550342c003520380440d00100e081e621440080e10b0401841300250a01e0900f006010049494001420810078115080550484644511007244050080c0a40025100c43c0e80f640c503062414006c41d04208845a298501034480e1988030041d44039501070811484e1610410086c0710003032084508a40b41c10014140140c0380c0042699507840074050006c43c1c95072040307030118545030042250500800203040d5003091902c8101100035900903c02e02c0c0f00c40740d210f40d00b008500e2158440d55006041e0031420342c4403c03008024400c1c610000b14045900e044aa044c040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 488867670 1250 488866420 488866423
    0x6080c240301140901090c050f0f1c0c03061d01052709030403170c100c020c1c3302070809090406050103110d03021e0106031a0402040b0a1d1503 64
    0x103000e4410004058400310040092000b90328051b44100c10403443c0001d42480103a104d0116000f02ca0014a210b45600c2084c0c8010032034032031100500e04c0c035803c0d8608240e003540e0940000d080c062840d1400c0215607502c80400e02c0230804915111b0b074a100c403070010300c5145030041802c0700506000c1c031826805000e0300c0b032040340b0040545220f019544049002c01c10444502c01040900a81d40b80fa18141307002c107440d199881482465075400c8a07200c58044503820f100308048401c403440140581201c503600c070300144c50044020400d0303500c0c0035203000314491080c4482c050003a54210b088000c0504494114010007900160812240359a0030083c40d0b24603918861414020f030301034540081d40394910710b4808051800301e0200d5024200078600030000c030b0b8012405d0b89140440c02c40300c0e284080c00841f101e00500603600020001b030200b281c038005241c0100c0c02035114501c00e44040061070803507404c0000707101661150040c4240205000386017404440d890305d821403611400100103c12080010703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 488868920 1250 488867670 488867677
    0x3030103060605030c010905092e0b130f150302030c04050d060e0607030e0d081e180f03090f0f011823090f0f07050c0d05030105010e0406080c24 64
    0x303440003610b4007400e1000d80380510548820000900b01074401c00d00d4940419403002006100d400360f4502a000c03680070f401104840300080d110a00860300040d2038014880494024580c040007030300c00c60401050f9010f0444203c0c05036402c900108810103001e69044029520003004410b802106200002e21911000f0400d0010ba2044801041030a094040d0501e041c100030300b135804240c24050120300790640070400201813003107460124250760b2401c050703460000c00f0040d035014454512080100f040d070000c2c60003000546d96800d448a038991020440d80e00d014004103994081181c40c2d21004ca45000d04082510190604120745403050000803410239100c1c0b0381c40302c000f1003401c0082e9558041c1d041012415040c1c1201c0e1540e96042c219426460b4040040c16500342d24401e601150020340242e043e50036a100c1501162544a8010780092094200b1b1192501007060310110301d4613842d041c00789806803403500000b08541d400c843d0030030158500e400500c5400d080a09461010043c1040c0203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 488870170 1250 488868920 488868923
    0x18050d051c090e15040e010c120b010e03030c030301170a0201020d050901022103010501021603151d0a0606050f03031e090f0405040506040201111204180212070f080a020f1e040803030103 82
    0x4e0071a41012403003404240c80300000000c403da45010041c2d040c907500807908156405c01401d0014078100c85000503104425036000c8594944004600402c0c031941c0040154142d8041c1c982400d118010301007074036521080c040d002405a00207001d4041c245119030041c0001610510440e142c14014252144095420711044026440300000512103940c04010000502c000f515825400314616101c480c40000001c03404c0c1103040d25019021316250804603400c03020711040060300c50042d100d00e48480203000511480340941e102c40e030b4144803450080191000751851403075024a40c0b01c0500a0380e055031069020710350051070a0300e0025a51610301c103892080740310704000c200328203040c000502882031a41c20820598482c41c1a02d45036010070040d07800322045002c040384d07000041c8400c03002900440420503096003030070040200c2c40c1da02219054503034040d6150a215621742d4901da00c2a48514407048402c01c404000250340d0b640d12060810a184131b0400881c1820740b15000f42e0b04680c400e030710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 488871420 1250 488870170 488870191
    0x2030d0218090f0906010f03030c0b040302030f04080102070204050105060f07060c020f0114090115032004090609030c060b09100509130602030705070c0e061008090f0d18050d051c090e 81
    0x40010850003080014050b00c8582147ea6030780d403550b9002003941145050081a0906100204080500030800d0303c403101280c200c207a4407192a203540600070b41101a05034421401c0000024040c180f80044036400c4144d40701540c501801521044041c1944010751400c40c45080d5050b0394082c000e101d503003480c1105059440349810001d00c0070782582c1446412101e88501d0400410014400c10a00302d2940015190200e01c3c18a100018005050b000741c054485802d28030300004156120100300145441818200081407051091151042040350005005611036006002c10f1501070034050344001512036000e040300c19642c8003002ea82003502c440010440105038802042003021103d0040d0118401c5070940b031030040000b44444040050302ca062016207008070764081410700c402c18480300d217942109c0366040700380001002d0000340d0b02c4d02d100c0158200c60228051428002c440461608880186214805491790320a2526090042c10a0007400d190005189000d5504544104c54260 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 488872670 1250 488871420 488871451
    0x418021203070c14101101020403080a09030317090607140d020a020109051c021f0b09090304170102210709030c06020a3e0402070b0f0402190602030d021809 69
    0x64552509881074204010484031441324541c1900e54203102e982440c09171410307031104101d15101d1070092140c0d400c0648000400151041002d401455400c00c90707100703a07140d10044030f8882d402c0004079025640c09035181c0088006ca00d80c0785c8541d040c0b0540d400d80341099454221010149000c984c464103051015275100c04992061102c24454036280c240340c1c5103c10303555070740124029220344016120009038103070002100e0030910389a1241441d02e030007078400400d50806103003080d9a034103e0f2241e00200751100c00e000150304418002c2c0d45141c81003148003e041d5482d0030381c2c00303150b0b00010140300801420010000203c1c201414040080c0500d801803e51840349082101c000c001c4050020103041c045880390320264583d10b03034611116030403601d401c2500036940008001e44a01d61014140c007000000703000102c50404081405140300310f0700c0045001ea41c2c0c17000043e29619100e12005a04140030380364440a4540061444009003072582d40382c49080030004e000b50b441903c0021201c4880c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 488873920 1250 488872670 488872673
    0x91204140906030d0207150504050607030e1003090203030d0c140d0204030201080c0a0c11030f0d02072102150d020415050306040c03051003020613080105181b0906041802120307 78
    0xd01250700010281c0241c501c065481c14080d40c1c45100b0720412008a40440d0001c0101c0d2044003032740c0141000400850791001542002400e03030075109250b070301c100c0b803600700c0c0c9500602911581d41c00301e034050b010354180113400c1000c0c00201421050081400b01004050821031441801454000400b0314010307200c5066000040c0b0f0541c00404c19024240100610061960402481d1424580c00101080c107809540d0102e4103041390003a840031a840381c500c00340390041e00032610b42c060f01e20300103160114040140f22400c9600415401039040480d0801c060324045040c001000d09000450f03015107040e94030b0500c4e10340d03000400600c07030000d0380c04420300c00f1a16281c058402a403120386414130581c200038911781941022440001c0c41680005840c41040700c02429100090101400030429483d042c07400300e0980300702009140781e50140550610b007001510700d002640420141101d00c859880341d062000401c105868034803240704104900005179500d06001c0c0e07400f912075014540b1034159 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 488875170 1250 488873920 488873929
    0x4090f0c03120905130c0e040629120c0705030c03070b0f10030213020a17070908100204060203070f03110628142e0602030415020309011709120414 65
    0x102d800320320070049030740e034101300f60380e00e0880d00800c60702c1e6990005141000d5074002e41e00d2072505100d00380c005062400c00500c8083c41c00307a101079540c2101e0311102c1d02c028030088000030320614400d07401c041c4810002c01c441c409480080c2080d24441d0f02224603000301c80741050b03c4c2d9040300b2004c0340d4001800f82040b6480849480e01c64000a028901443c158115800a902040e40b140e010f03840c2980820f00030016442080d50800d103004c2085400e0a40c142440020642060341c082d40c8190f2180342051070014500c1d00c22074045858640c0698102880341da140700c242d0310015400d030100006000c10b6043c04200b408220301844d2036001c0000300000381e28405005950482021800c2d519003552085036500e100320075603100750030248005007030240604041c50740400c4030401001c0c1e8000c80002c1010b9400000a0054403a0154040203110344918126624801d420070640000c003c946001c400b2401c844410750418680825218038217a4a242d40c002c50304161f020405070b890007140d1084d42c0c1070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 488876420 1250 488875170 488875193
    0x304110d0c15110f0604060b19120302060c04150e012601032009040f0c0b0304030513090e0319020705031b0a09060605030c07174e0604090f0c03 64
    0x1804090701c581c5404c9110309442e039130b0041c40a400a9200c5070502c417aa5104010b9118222006104134102500d4400314000020500c108401511480c0e01240b11859040207850413540300d080720705000d030000382046071580b00030601d860520a1681108002030f42810058101325441d161220056145084c044403240c1610151800d0308214402c001945d240c00e25160fa005421102d44003c5001c00d1030865034104095000300310f070f502c1c08000c0c001056404001090302030070000300103007159200c035102011140b00020003030765030b401041010360b0a15038040d40c1e5404070013401a41d40d159034034000700341403010200107426010001c1d00c1080c803d2a0443c9400068043c04d1403c000c89405c012000c0d21511020b40b01014041010842004200702c6180200c00076104403501510303a07a0421050070001040a030300a0880041d50044603102c10030a43d00759800c4806060f284070303805103046143d0000d40074243d20b0300142c035210000c000c500711000112103140300d01040c0c80014034604020403a00c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 488877670 1250 488876420 488876447
    0x11100801060f03050402150316030e03030c18010320070203010e010c0504031b080d03020c06070807020d20120705120703050901030b01050d0f0b1003020f0304110d0c15 74
    0x164140050200d00e90081d020050381c0594140004e0f03035205c500010741c0710710b5031805401c490a800020460041c03c03140310650300441d640c80500003a0300305207019440780030171034031514681d40c18850600c25609152a141c0c032801d06040001d4080c00c02d00d40084007200240901108040001e26541142000d109129807100d540b0003c00000d052001c00500da8855440064000480340c0c4604c101d00050608200c01441c1c650708031210403030980c0c4003401a4121500d150014090303c4002803105015404061180d0300c40d5002c0d01001021010944404248040038880d03100148851419541e0070403241050b0900013011304d480e005286001454014010741c0846008400d110100c0000e8100081d521150341c24240401c00c64480d0740100c030540150702000341c0440c00e10022107024111130b88032440b12441030710900884c00108100354140c1c4900301c280c41094504000090106010042010032103500a0030100041c8440c1c403040d0150120f6017100400854031f001c016007160300810000c0581 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 488878920 1250 488877670 488877677
    0xc140f15060f0d022b03030c0c030206010e09070b0c061015051207121b0305010f26070317030708100308120a021e120a02030f070e1c1110 61
    0x207140480100300445660b0a400b4010301c0302e9910301d821540c520003144450a28050401c186000142c1c080d400f40b030060341c042e40864500035802c0031052080b0304812206030907400600c0c00c4c0e440d1046001d11403038000e00d03a000030301600f07401042041c00c1034014505100003100504960500705c056000380c4001b540402d000715440d20400041e680c1250a5170200da020350764003482551030140c10740b810172281c0c3c510700d180340c0f80912061051a0050441c00c4200c1959001c100507a228200102d03291110f00410180300910000c4c2c0c11401c650b86a91603020f901c07142520034040d0f4903551000c424080c4d05540070f40540c00300400c00f199a1242001d64489903000704c0301a018910380391035a00340310701d070a0800c000041c600000c5c0c0e4008a45c048883e00c40154244130114282400440140d0b00301d1000d002a10b203601020503000440f40c029240940014030342e0202a40720b1110a54801001c0903030789410602c1501c48001078240aa44020b180b4016522820341c13961400030898500249242d14050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 488880170 1250 488878920 488878963
    0x30e2b0606170106080a0b04050a1a0712020406090512070e01060804140c0f010807090305030a0f0e0f032509110301050f1002060105010c03051e04050306010b090f0609010c140f 78
    0x1c036080003500718102a0007087d503089176212420220305140551202030900c80301d03d4208a984940524102d104001350354640c030100d0f44c0308187c0002d81c8250b20a0748000389580300103000c80d10f00000c2d0320104400c0756045602455941400f100c40c400242c1c84900071442d00070800040c070444400c4003c2c07500c80724028040450050f8000755040019084c468100501000011201d074011400000699080360841c2d40360b00c45502c0040c03a600c02000f0000000354000c1c0e90030140d00704032480b8109072500401511074050003005149402540b03201400c21242c6140001503004402e2080c0e1101c0f04802d60754565940c1084d042c40006a02090300b00e01560111015442281d40401c000d81504d40c00d2804040c03e22103030030210fa8900801604102904051840e82c801d8410f000c000c00440b542602a25100e07a0303034220790303102c600500f03c00982001903140404400e00c5d0540042582100504000d03400d0a001d4485041c1411405100d08107540b011802d08074440c0100581040040c00400c0c2144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 488881420 1250 488880170 488880179
    0xa0803070506010308210c0a0e1207030305220801141e0105040b040b041d0f070b19030f14150f1302090303091f0905060304030e2b0606170106 63
    0x107a0b5941403001420105005c200100c03040f400c0041c4070003c038036000714500309062407204082d45e91310500c1c13407602003070b032249c021142e03400d022600c41c2c049651030000e0446030340346071419a119402110701090100381c400346255000301d4940440c010f09045c10002442d0320044080411902c005045444140c0b41e00312601c4c0800401c00c1c101341034a90590b008a5400440c8000c10301500001610300da009040c100b5051600c408058007111038140c2000704e5110302c1d9000c3e1503a40720005409180022002088040c0280352810351503081c121880c607001801c0002640c2c0311044942d00181202d10700035103410b00c0b044802110b11001140c4c812601c0ca81411040d44c0011078103000308100d0000a500030840780310301d80c0d0034011f807056800081c1c10b5141e100000ca00b802400c001c81440c880100c0e0031300c08040750f5400c1c05400e40e445a13506842d1001c100091801304040940f41c220309804241403111001d441052001c40c05504a10840d40810313000d081c00300e1100300201d03031000d204103070303142000401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 488882670 1250 488881420 488881423
    0x30606010c03020f0d1e030b0616020f12030c1b0f15040b03010e0a0f0c0503242701050f150703090504020a08070e0414071107230a08030705 62
    0x1a000042401c100581006500e002d0b810800703411031012183c01407610185141d50000b03c00d001002100d102c1c01820580c080c801e03011141a020601d4021809011306d84120041720007165035540000c08018142c0140d40c00642c440c0102515a500c40e0404690800500010002100303c1e2128540b2040480030071400700350704140e0010070070321900c2c404c8420061034949904580260080341506a030380c0d83c44c5c0000d0303e110705055803418a054903084007142c1a066510882d41101c0060b0b42e9a403451701d8a102061820024611911516032002d88011450f03861929003011004401c20214901701099425000c0c2131050303000ba4003480700e075070320320010766603012a00d0321682c40d139030160741c640400e41822540304e510354000580043c4000f50b42c0d801142c00101c101d00c908160742e50403030080140303800c0c002525295a016038804010001140b0103502480310b45194141e2801194005a0382d00e005140b282c228000e28520340805c41c070b001149050800c0044081c0c42c0000c011454003c655440c03a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 488883920 1250 488882670 488882683
    0x100f1d0603070c1b0803041802070c0b03090f1509010c0c0b0406020313060204090506040c051603080924100f14090c04030209090c04050604090b01030b07020c210d0e03 74
    0x380b0401220302c0d019020050f00c541c009100c000c0356802e040450340c0303401c0c18913030b26400341c01100d10460740700d420b070300d42c40b200360085070a416031080680400c10f241c44509151a00080c041d40401d0140c0e8052180c405010401c21b0004240c0300703404491400c1c034080b03060031940c1c502803040402440034034400219407414503061700154001c40c016540e95980b14108443c489c80031000303201c079000150000d80340046412450041c1c02c112410008440042030541c0c980c801d000002e0705808a0000410209020761400d5a00c003000c0029504580e01c2981c0510074602003600b0517030828980301c180540000303407520003005083c0701d0800c80446400c0049000c0300c0060500202c2c4620000700005502c003e0703503020780c2c00456000d4a0b1051070705108083d1a2100c0006030031a01451170800000ea040c43d25018084003d500244402043c0e425521800d00345100103106c40294071905e881c1d0040c0f0b44680340c0c000031421005a1955020000c071065a0800580305080c40c1000b119040d44141a60003044a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 488885170 1250 488883920 488883931
    0xa050411060a020a020d140a050708011401080d030509100e0f060c09031c0c02090a1a060906090108060d0209041202060906041208040204140112050c0307030b0601080411100f1d0603 80
    0x8042146d60540f07020f103044410304500600314041c98544100b0040e00040c0001640c2d4007100038031110003100d41c039024001c0c09110b040c096030300074003c5040442c02684200d0300440c0704015a0494041c22881800f030b184880c4c00d400c4554041d000034034a004003132040b681c002c0300c8481d4181c60891001c0001e90365450a4908030745040510800000003030042c02c40821140d40a81a0220743c94600b19620042a042c4d5a00580c0401d640d403980d0700340b40210440302c192074003c0000381807162040c011144200c0042101d80c200507440c24607009661000e658a2140344074280c4000140c43d00200281804800703005000d15a0104041c800002c1000c0c0010780c007200a07150280d02a038403400050050091313007040304090b030110720001c242000208201c1c04824015030488468003481400e0554030b80080c03002038642c112010207d001c6610036074a0703c0d0001d00411100c012000354100081e0100d185082010100d10046100710340640c10052a0000e01c040b81c0c000c0f08407400003400300c2d8113448010074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 488886420 1250 488885170 488885179
    0x110307050f0a030f0c030b041a0603070f12060803030402010f0305090a0b1909140f060f06060a090e0c070c090209130b0d0c0e0615032214060a050411060a020a02 71
    0x1415802d06103c0d0b800342c0000f006462040c800d510001d032010740209040428540141d00300014411180300e00340480c44421305c081c001c2859640ca4540c11512810000d200c401041400c20701d220b003040150180b80d020b004018069542c9091074400508103036007982010081c54100401c124884034045040f10803c0c0e0440b2214072070340d46450519603400c0007a06604401d61030709440c2c40c03e21210400c2000e4000b000d030121000031758604511070340d940b02202ca252a07940500c00142c1c0c58103100020302841c54407030403c4208276880e845028009102211109044c2e80d000c18020f06201c078030f4107094000d000621007140342a080101085403407a490a02e000040d40718600f42406071603c4000150580d00080b08504168444240f10410b0300305840c251711540891204c5055003508104490088000b494805005010284400c2d240940e1310307016101a0180610368071031207410b1228922850000304001082d15240ca00b04d4148210540a0f81c090308003070000c5a007450300099840c02c41d0f501140c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 488887670 1250 488886420 488886427
    0x1e07090203060424050307210f030905210127120e0307030305030105040b0402030105010c030813150509010c1806270e040b1506040306020c1203011206110307050f 72
    0xa0201d005071001811441c982c0d240051410031416540c005001501c404405503103036a582c58400b13241e1040c00b00d86008c0c03120520500750000501d80000244102d10908007200010b81c2c0d200020f0441a0955800002c40082e4900c015103410a2195131410803881c0ca08400400c184125203520700300140d4000c04100c0703100e00c228481400f5401014882c00c0007000c41e9046030312407600500d950403c1c4a0140076600300044d40106160038001d8170705075141a96245405406920121090780d00038101c0e11000c100c002c030b07081c0418008a400140c00c1440d910109041c1070100c0150700b1a81c440c0b1031344c0d08101c807031000d00c00c5c4804190449400c6910078030f089071241082e5010313034031a00441041948500101140050710882c44894070b03115078010b2090395a1660b4007000805c440b5018045160300100c2000203000103251680030703124043c0741c40c00312401c400d03c07801518139580c02070304510301a07031044410000700141802014450240a041181942816600507189006800301c21000b0712010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 488888920 1250 488887670 488887681
    0x1b0f090b03071a040305061b0313031209061a041509110d0606030c120e070b0d02090307170f01020903030307030905160f0f0806090a0311070519081e07090203 70
    0x40040c2c0002d0550010301c624115000f80780801e1079441403000302c456003d810300180c41e43d1000c00703401d039a0240c01c2c02c2d0b0f1032941e6985008640f658080441c12014824210000388061103103102d201d8005104040010b1104040440b212020000c070000c18890380c00c0081d0710a0901840c2c00d410100d030230f04080401c00d442c4c588405051400f0b598840c15403e46041c40000e84203034550050140c8809903181c0307100e2820000380710300c00c1e162803c0c104840340d4080071041003550341c1200104205a02a0001400d180312100042d080c281550b108040480d200c01c030003020001c00307100043d0030b014900007c502c2e05203400c0220b5281c2c00f00401407001d05a650b01d002090080034020420558031f010004500985c0b5041320072080c10590140c20b510820014020421440008100d4040c03d00c110040803000d2240d503084500a008500d20501c0380914100002d0580f00c0c01003503541c071480065982402814050a145042e41d13803004500c0700720b100328401d099054040340742d50a9400040003d0b07640d9070b80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 488890170 1250 488888920 488888923
    0x3040c050d031e0c060e1b0109031707060608031305010f020102090d02060a110706180e090a110a120303020c0c18070c1b0303020a0209060f0f04020717161b0f090b03 73
    0x30101922890034a0394000d0203100210b08206000c0c0e9142c40804000140c1f00111040156800020702445000402d142d810f150880904402440b4510200b000d50300e5601007411034002c4804440031a180340000e211668000c2403920b40f030500c610085081c406658005201400b82d00c601a0248030001809980a071003441c42a10400f1460111203410755641b40041c4034600303002c4808000c1c04801d074003040e094844131145004854003030003801000b45503180c0b80405030101800913446282d04000155001b440b60108110381d01a0724010388a4000d03501c86420444102001803144000c0307a00091150a07d030358094120380c4600c1c052400400c02c1c0740136911040e400d1845000414012000001c050340040c018100c24404c1c1d84507130041e00c6040034004280091540258003941d0010154440d0406a01800115018800a07410302802c00789284159029440d040c00001100350501d051100c200c40c0c81403807020950368080e41030b240c141e50141e01c00841c080d0b844007640f11311084441ea0360 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 488891420 1250 488890170 488890187
    0x90309090906010329071214070302070b010503030405010c0305030c220306140f010504020703120f020309060f0411330301140307080307062309010203040c050d031e 73
    0x2500c900d405080110300607980700380900c0201c940c151807103130151282d0391343c01c0020051400300585103015200c90b0010341c1c0b41c16050b140d4003855a036030004041c0400d0300341c1c4040e0103160651070059540003d418a40040403058001768082d0340104010001070741d10440b1001c0301601440d0090300e0342c40e8402c10315010301c20610303055284030800d08990502d0080c62000c4040781d210304030400c2940c3c0b60307034000785003501d00302c481c200e1110424004012504107500144401c6110307207007007a0032512010142040707402860480c5503240d07003c81000a480010060f00e030b003002e8007000d0000c851606607900c584480320709443d540241c5140c420030001243c100764090200e4030f100040c00603d20400f203111b00da60024464904c010002c80d111080c036080110f8110151003000024500e05030560701c481010308030f0900c14151410404401c00350612043d00a940100d03400d800159980c2024144000e41c0070302078028504c50045101070000083d0000c201e00480c074050b00440c8094414024252804139 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 488892670 1250 488891420 488891437
    0x903170714150f0609060a03081605100c090509090d14040810091b031a150a09090308070e0d060c0306081603140c0310020c01020706020412020a0603051501080903 72
    0x8960405007070128400b80c07a452040711218031408050780e4410820002c0f003001d81d50b05030000d5159906001107000390004280010f201e800044610103184d0b1500d160440715902c03c0240c550300c04165070803c2c1d100c901c0c0380041004481c0e2070141d0800300101074a40701d4171a080c200f40716450381080d500c08035142c1039a00600c0107500f034a92200d00084490060500204100e8004801d548a4116a05615224030a482e004140d82a048011700482d0a0911004d07015811510805030032008c0340da62800308034064020803038041001c0485160280c2821805010102031140c84803110074161103c00641d0104c03030300941d01013005103d6480981c020441904144068003403100488d0010001042200440c0d1196940213a6854142c04140d1202c0104944552580101000600042d02500074009400c413810005241586a50303400c0206d80c01980a101035850016680c015490003810348002820301e03050510151510811842031035281c00e848034103104840380402d20001c0304100fa50100d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 488893920 1250 488892670 488892673
    0xe060114131406010e030d0f08040f120c05160b07260406031d01020403050a0201050c010605030d030519110409110706050108160b0f0307110a050703120f0903170714 73
    0x2e4602055107446442d0490b01a40425104100003040342800252100d04401d0781d903d00754812550b00e0110391140010700140c0c1c1710340c1c5003420000824800441640958010380b02c1800303240007803a0103410000c1ca075040d605070031400b1710200400329101c01222030a66200b8107000a0301118070164240282440d40c001d01494082804a03081d90542d01c1231000e0040c0c51401c00d40e4121400c03003103080c3e02c124003006109811070500d54006500400203455025442030020502d40d131a100464076145c1c60203022030001c2e840c0d10500c11103616103c803a90030030388810414441020800140e05d4244114071031841c500e580c48030310f41005007140d81034ad0a0141d011205020030750707440000341c1d82c404c81c2420320920001000000914240308100b19a80700404821503030a503583e681068841100e005001ca0190145c00c0c20b02c4000345090002501a511071825441004828080180402c3c002c1005000344204c131001840840d9028002021103251041025580c82962405400d01d109914514205 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 488895170 1250 488893920 488893931
    0x90c130e060a082406130c02010902010e0907021e0f03030a091103160302040902060706090606030302120a0504091503120206040201080a050f15060f04060e030708010e06011413 78
    0x4944200c54028066841250303001c061603107940050ba2100d80c1d101d08458500c00900020125880d03010149500040042c551075440814200c41400e403400182c920005075514003c9104541e0082c11100560a050702c00c5480e620304500080e56903484440350b80d61200820950404551040041c80884500041544d80ba0b040010140c2c4c064181d29508488180c03412140000038140054080482a0108408082c0a180d502800010141030400380d13041781040142001045103401080d01151151100041151031810020308102c0c02251000315088204080081586e00c003003030310280c4007003c0b8002130440d55454028202c2c0160791008120501c842c0782020019004101d8a03c118001c0e03c032004155100d280d100205e50f411140c070240030b40c0842c04650703c2c047c1ca03511042c0150001d0816441c14050000d44150358001e41e21820000b4051003552f40e050805221030b400900280c0005e124001c19401c155840366414020300c28000381c900b03580703003107a41c0310300ca0300001303030100101040b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 488896420 1250 488895170 488895179
    0x41d070e0105120309010f2102031e060102060705090f4b130903090b0c011e0912110a0c14011d0102031c09021e18090c090c13 56
    0xc0d21800348100ca1081c089049040320915000c81100c0440c1016074980101e4865510207403902d0081c0302c0740301c0b0380003820001e00d60781518510041d400b400c4490600c00700c040056003041c000100007084c607030464200e8424400e4154218041d0385103802c0440e810720404035040040390030b59580b00e0040014007002c03d0000250b00c03841032501040c000f0400541c0202c06004441d070b04000e43d10038030a4105044410200c0b070842a0303400140043e03c6440e145035501e03aa0096000650003820451900d070359a4014004200d042c0c145000c000b546008041c0002207450303d80e4040c81c00400744a1042c80b001c405c2074201c3c1c0409010203000039a00000500c061911200940300b40780229132254041205c00041c5420300d40094074000346000147d00940c0b52204824460042070701d880001003503a91201c80e40d00050741c42c401c282c514000d2180b941d103008845101040800b03085a00b02e0040b010001040c007141110201d030401051400b5a04100c8035143d0403201d2a0350f10402c0540303054002e54810114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 488897670 1250 488896420 488896439
    0x17030109090308070c0c0611030d090809010e0d111207091a090c1314010309020301021b19081611040504230706230c10091a04030806041d07 62
    0x300759038029660640c055841d0001914400591840030b01002003610040020501c281c0c228243e8000074016241405440c11160707040c0c03034805204a070115004210303c06596031202880302d24003021180200b5078038064444071441c2c1e611400c0c0e18002d514030448400166002c110000052451020401c45c0080c0000080f541104031070b0031307030f2281c0c1d04640400c95035611803042d628100340608110016614000c4205130081808030300b5418181c5810b4480d0160b5001e20160000403150311170005134242003c4180d0a000e10560650414039201010b60082403001c0c0075554060700745114400c9441c2d0500304440c4203040040390a901c0f6090004102c01c00089081891600d0700501210003043c2e12021a25115002d50103902d000468540c0c04001c0b0070800a180300c074116181e0300d400d2410b60940e485906010105e007072100c00a4943c3e405200300700300d22150140380040903d40711600d0138569001428168090310103486151030b000c003000799050b0742842820a00d42c1604840d003103a512038041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 488898920 1250 488897670 488897681
    0x928080601060801090f1b0c050705131b020607140d02041701020a030c05190e0f030d23070f0320030a0c0204050a05070818030403120801150c15020717030109 70
    0x2418141d0810303100741401e14280c054140301c01d02104070304c0700001f14030714105c0d160080e0880a545a20603503000103541d856120403c0b0f0b0083d4404c1011482055081d5480e050b000c51011800c11940031004014842d40c3c44034103816503030500c1144581d6140010100c0002e8001c54004250031075505132600e80132201507000308010156518180001d080f000700c01c1e031303943c0104108650303280345208035184c3d214480c03c0d80c0301054000030a02e50060000700042441c006450b00030b1004590781040782c2c040303134542000f101c0401811a40c00b51400280e5510074554049000c001010300414040d19180c80140350103404500c0c0004040304d86034600024000c00e00e0901c0ea000342e0180d0f180202190b8081c4050044034415180d0342c90b010242c0d240d01c0904102c00039554100c4095000a20012000903070071a140348000c0b15a54030f08107030354100168032520b501d5035000c42003404500c804500029600c204030a100d8070751b501005840e8442c9041201c000c0042003d1a440e42500000124119000d54000b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 488900170 1250 488898920 488898929
    0x30b0a0f050c0903010b330705010903050a14040b1207030b0d1b090e0c0f0312030906100503011e0e0703020402030a050406060f030b060904023607050928080601060801 74
    0x240b10551404003403208044030168100351411540340032010958051418100031f400441d0b0551410440751a12400c4854070b41040b80003605c002018440564041140c0c000041600c0700c1c18585031510306c1800b49842101140ba04059080c40000c1210340241e01105008001525008921711207151040c0070600400824282c1040079401040e850b91034402c01003030490b01001885964031010030804d20f03500281502e5418400d82c403810390400d03151009103000c1d003101030041c030190516480700001c0400f20380002c1c0c0241c1c50041514201803030030301d01c0b008070070400d0b00c001040310b0000c85050502a1076040a50080d0000051000014166011034441d50043c0420045180ca6598080982c8024403018003040d03103010200d00301d440d1500030b244d042403004000b03a0705030201ca003000c0003112032502c8107600c3e141c1007484440c5200d09034402c0c1e5806007480c80d1151070502d19400060381e001584c0e5600c4000200c11414804044140301d851014015041c200c41007583e44800060805009028 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 488901420 1250 488900170 488900173
    0xf0915030906071d030607080f13032705060c0102090a060c05100b13020a02150106180e130c03080d050c1e0f0705010501170106080c06041404090c060c020109081204030b0a0f050c0903 81
    0x4c00b8ac0380b21109080920b9410350b80c4400fa4400e0302c800360720a068400c1d503800340e00c4106000150703c0c0c0c5d41e030005085000b2100005603c030303001c040c1044800481a03200c1c1c03080c010480c01440005001141910186e803240b0030000d000454240480d0020340a140a03150040c0700156002c120b80e00000c032454509443d1000f00d0013aa200c00080341c4040b05402e20b4074100d04846000c0c402001604942c030b03030003014041348070a001c4240d20380c2d607601030b0950f005680a03800041c00c0750120000d0f005e00307544002481411458007074201c001480500e800c0c80c05440585001c500309010840031002c4a4800c0d130040020b018a5845010705500c10702c100c080b0001075031030a01c0c0040d1841c0081070601c1030810060010f4101481c12140810801c480c0e00d03210303442a42e48800e60002444142000c01038142e035624031141c02180c0c80090400003070358200c0d41040e480390401840b403412080855040c2c0c0ea11000a0100b0707143c00310380030081c0140800038080c00d800c1008010f90300c10a000980281d807030880 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 488902670 1250 488901420 488901451
    0x130501060b0a0807050a0509190303020c041a130b0d03090501020d090f0e180703110a0806040b040602091c03020607080c0a0903020114040503030f0915030906071d03060708 76
    0x3a29a40344a160240c2c8080307101c0d480040c0c4124000c1015004c0755030641400d52401100400089686030502c0401d0b815400e40041403043c140d0402105201d070400f41c40c02c03c03000d1004456219a4032441c0c1c00107106010020078040e61503445d070071040039031501a00d400100403286c038002d0a0408140165030051003043d00811803030348a1541a000c40704240c054605442c10010206000000103040310705035000080da892114100708072610007540a6028110074807242010015001515484900c0d0344d402401400040386640039102d4015501490060307031248010046601c0c4450807101d40d4001d00b90300c10304014160040340e02d0b0300c188219a502c002a40e41c01ca0f0380c103414041c6124a00004400c0320b010300040d400780a4600446441c4008181042e0380c540020f03141d40d01500004023566000b1071412040d0520410f2048801e8810b10b085003146440c0f190140c1e6044000d10789020444c8141120049040c2c000810011403c0603040d01c6807841c0c20580a0070350fa105841d0500c3e91003059 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 488903920 1250 488902670 488902679
    0x30b031906090c15030e0123130609020907080105011b0f0f03050d0f1505011b0f080f160c0f06020a17040909050d0210110318070302040513050106 65
    0x42801004500400380c80c84500031151560001000d21020072140980040d4011414040031020089480f9040c4d03404680c240b88600c80300c0c03e4802020701030005102220018007000034140440342d000300c3c40319000c960100c00c0e0600e20090001400081c3d04001d2420a200110741c1c4642c0181c10385000b80c803409040e2600c4022560019800c4502070b050711041c105043c00513208040031601c090003403405034109100785940f40d007140c100b0480454820790340c2017580e18900ea41c0f48031000501090038481c00010301d4278241ea03d4072941c0b170002800200c281c00174604201d100b5050f1008038101c908482d4883c000c60720003000c100038018040c3c2c1d8200b0307071100020700300356540411415507445601810b4102c0a654400f04041002104200c20b01c609100119a0f58030511541e40e819004000400d030b038803503001e800303800c04103008070011006040c80c1c1400503865005c070449070084a10040700c8450301054050509017591508000d50240c200408e01078940320002d03c19000e0b5000c0c400801950f6541d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 488905170 1250 488903920 488903923
    0x20090a0326071223070b060f0907030c141801050f1204060506190602031c02041505120a0b06030c07020402070215030108102304020a080601150f0807091502010b0a090c030b03 77
    0x180f141d901448134100100700009000b01c8035503400403070103488042c00e203901d0780021380e406100f1181203002035600c51201d54582e50041204075200c01c4070054600d0221860a90310700b02c5110519541400400a400e5001c2c0d40080c080341c0c010503036000030a00e14205450011301805040d528a0b04c02d00b02d100b00d0089101007504503408aa00f290000e514020340c00803213951041c01c91010310b018550030700001461502200c42c40a5140c002d50301c40d507441054651180c505007010b01211083d43c640241807800362101403c03642c00c0700d68904000c0d140c10403440010040e11401400030740096845002003040d1805102540c16201144c05440c078580030b880034001100c106101d58010061000050081c2481010350203800c0b60012f8240301c240754940d41081d141131400e9100001c20707950883d0b034619090340a003007026132003881c1c07500c0f6800b0b04009400406484860007500c420501544450781550b000b503100c1c4a901c20042c1c08075035020b070b542218070010f2200d145c0c102c02180c01c001510f440c6140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 488906420 1250 488905170 488905217
    0x501090606050f12150612030c150c030906010b0306060c0319030b040908090409110307030b0a0b012d0207180b1c020a03080705030d090620090a03260712 68
    0x1031840080501228103170100b0361010018107070070f40040004445046802c802c0c001000203224060040000040c4406200040500108804441b007024018007070120004035400341100c1200c8a266286c0c0c90310740024620340300780944040d982c03100007101b962441c01840c903900aa2425202084040e1544d402e00040c1c1d00149802044c07070004100c03607401b80c600750b400103007100d010b2400c81c3d01d0701c003913200480d00d0b0152680045e030b2110010000c1000a030f00b51300542744060400c3ca800a03040c003001003000c02424060362010035960058004a00e0700d882040080c000700410080ba1000401001c03c0c140202090010a405400064900d01e9020001c030388584500ea800303041c0111040c59505c031005603400c10902150540420000c50008282d01d014004d00d60340503010015010388000010184c40c90401e51801034030006200701032542d540c102001d0101d80c1c0100b118101c001c10110214026441e040707810500300360100d1010140b00c021480d0281c00d45840c3c039030f0025200118203100404c40c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 488907670 1250 488906420 488906449
    0x6020d020709050c0f2a10290405040f06050c130e160c050a0501050106050c0f0109021e012d1404080c010c020d02040501081605010c02100c0f0501090606050f 70
    0x104c208510460107030420006d2040d0100e0200c0700d8078010b544820380c0382d03030885c054840c402030780f20b600d952414511610a0440800c076100c1e440010881d021003412031002101c80d56403240381d0312800a030612124200030044558442410032480c40c0610500d4007a40040a66a04200440c0e80c007007290780500da407103405104c10800410030314407440030407a456a0310020882e4140100801c100020b8800d01031203010341200c0c0c0382c0c103032103c240d206894903001205181c0ea9485e810407940c10050780311102125580c10103c900076140015000c0180c1c1d6000c2441400702d400c030114003401c01e8072040c04180700c0b468001d0380c0e1040d03c2c0c0903800d80c0300c040301c1c0141e009040181e04420088145980902d092403800c0d44007038803820364000950001412298242d101e0341c21500440f9902c0f1041c4103461180000d08001d0038016880e26041d000726510403080d110000900c00100c041900740500e021210380e03451f03801002070100030001c5c80c2990203410f80d032140034000d4190801c4542c1c0c601d001c07000304002c0c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 488908920 1250 488907670 488907691
    0x110307020f0f010203070c090204052e0305060307120506041406010b04050d0c12050705010e03150109021b10230408030f0c0c01020d05060a051503010b0a05090a06020d02070905 78
    0x11407100204486420036420300c0d0306610040103482c0014200b51b031206e006000f0aa00161500d281c90184000040c0f8031210080f00b6100031096031501c0070460318401400c507245030005050f940d40340070a00d8444030303402022042c00200300e0882001f9001403014841d41c40303100c1d0700360000080c501c650ba0701d00c800e0060402d0003005000a0241e070400d035400c0e50036a030161500c42105541c80310780e195100844174003528030b504802401e00c1956046510321005c0d450680050007911110406d4102442042c0604d2204503000981034001c107511664507400f40da00c0030f0507a9190200740070044010500107000440c84400700400c28886503030300710101d00c115084016a40340d0380c0c0f060101c0c11040001091401c2c403800c18070841c050b0800900c054a00e507000000300190508042c0100151688540d009503c9090b06500c4040803a03007180913207044810781c4140e80c0d00d41244003802d40c1c850090310807650b00b084120400050300f560005001c0054041c81d02901c1d0342074bca400400c01590812280c40700d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 488910170 1250 488908920 488908939
    0x11103150429010201091403030406110903031e0403050102040f2c070f1e090e0112020a060c0524151e210304060503010f0b0915031e0106030c11030702 67
    0xa20075240400c042c00306052000159440403503984040b00300600240d039030765920100401041000c281300c0c500c1e03030380c0203558005d081130000b00000380c2e40d11440d94002680c1c8140c6500d101c10ba1803601c140c401440d030040095440d15110000c4505850007845050600b1f000030030611800114090603003101151410b0200980d0340d08a8243c0703841c03203520062400c1051600d40351900d822602c100001c0d020b255075a483d065440d10181c8104900107800150710b0741041034011006a5030a400401140d003a801d1001c0313500f000c3d0801b01d00f4601011070404030a2000c901d0350191415681440d4802d600c01c1d03441481c07449007c41485141151050120800d14815010840301d10b0000007400d012980795091007007e40e490000340c1d055801690020002c940c01100600004106442610180404048103801c048040f400583c03c00d8040b03203440a52600000440d0710040f2006900a80e070b811040701120659440341e000b4000d00341c0000c0303400028200245003030f0810740801102d01c8a80c00400c00e904 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 488911420 1250 488910170 488910221
    0x2030d08061306180f060b070210090801020f270f0f0f18041403070506010e07140a09031211100f09050708010506102f0f0111031504 59
    0x142040060580c40d40841c0c9a502c01114045502809002c0d01925410822a0069000352003d40e41c0f1600412030321800c0040500c11410084141e0f036155404803a0a80c1c20b0b0a0900c2c2078503030380141c0d0041e8100d5400000e2488803880b4000003003460020388850980340070f00d0f403141030603200c030201c0c14903a100e05078544405041ca0400c180d20740d035038002098500300b80466000550142a0030030b51524241200d0100300c180242c1c0d01c0d00d0100141694061850400300750740b081e4465505019180b01c01154501140000b4400c580034002d82c0b0b61302c80810740e03441e25840d0162002c203e86c8408c0b41d494004604d84e00c009881244440c82d01e0407290000d081500580a86401030407a0590010010395201190b0300890b40c2000440001c104034400044c1505080e0144000d041c900b0005c0400d00c10100130a0b8828804554600400481008003665500d15802290300b0200030345410300c119807c200e908041c000940008501aa10314202a070207411000c09100644132080140e90529034005600c99 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 488912670 1250 488911420 488911427
    0x70b09091006021908190810050307050108040f030c140105090c01020f0c040203090c0d0f031205040201090311150307020c120111030106050f070c0e0609060a1512020c0717070f0302030d 82
    0x70310003442825000c1c00c09039599001880801c6d1a101d06000503c440c2c140700075402440100301c040c0900b40c0150038003a00704000a4640f45024100900c03d45040c0440d07010b051042d20003a4099a1124800c070204140c100f00e00d0184c2400e403002c04444c0a10b100d11441903000103421031039a40810098440c400c550745c00c00009400040904601c0c0c090700228500c941d50300601a0b00803442640e0150f8244070b2401c00038034007a20000700c040344528000510015070f0700016124101e80d8000085c8800b55815400701301c2402d64140030120800c0701005210b0025004144160503a03406d0310081d90400d121001c2e00d007070394140d1035000345002e0100010308c000c038800e4000b00780348804800518170b4890713590b943e02c0c11105143e00c140000f1040d081802803d03d01003503e10340041c411680c030130070b03581401418042110181c07649020300c001744407401200100c0e601501c1c1d869034254160745105c0c1d614154010210304000d0140007a0180f1b02011803003000070b140001c1030320340140003010010708601c001d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 488913920 1250 488912670 488912713
    0x9100201151e08070902040f080105011d0901090b0406270f06022505071409240f09010f1521020d0b10170c0703021f0b03070b0909100602 61
    0x14680812030b00002c20000401c100100081042020040c1d46078900156200e1406094100d5891641407400400025046000d001e00400303e580d84088039881da501124010419000010408514101000180034056100c0b00444c800d0700c140c00e5103601e6100b000080624000c0c0010200501844a00c01050796540a4060b4402e050382c0c0010300c40001d400b04150b85103d410465031548441010b000403000c0e910325044441080c0d90320390346400c00b180889040504450520754803000203481c0560ac0e034541d0904e045820015000c2801561a000030203031030700e9507006a98501710b00d00d0300a01c0480c070404081c541c0c82c40030840042c2154180d139420004e58860901c40c00c44035210803103030341c855403400c1d46074a8a0510b602e5034039032803040311603a8150038801407140107503070808c1c03080c00b0101c0d401154030407403800f0490322008625410341c2288001c22a68a4842c1c047c03142c44408190440303588010300d00420101d48111150391640d507030846081440c0100740068011005000c5911100b1400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 488915170 1250 488913920 488913959
    0x6180109020303030c0309010b06070201020d120f0f0f0e03090603071d1305100f0605071104020705010924060f05060c0f01150302011205010308220902040b0910020115 74
    0x480d1058050700064916082030341c008090071000801d0000f0300c0d100f403082c00ba4008042c3d03242820308000780c0000c0c1d250314242485005010318481d405030005495401001880d0f030a01081104e146c242c40755400903c69050303010318840c03506800c00c0d02c02100006039072100f180249214a15030301c8500846000c411449010102542c03040d0301c05513955500c01d1022604481800000d0a01d4072540c02c1c0c08000701c5503c030090080d0001000d00c00140e0000450740850703000380d0145d096643c03c5001c03e0082c410410301030800d505e01514503040080a008079404204250721484480541000d408100c0360340d48100c20480c00f040c035082105041c220094420480400300f030b9005a842d4020582c00d4407081100c00e0a051007820040c4215a0012980c84070740340302c99070410280d070542d902c010741c910480810070341071660a0720019021410080320006480c80c540c00f5520f07a40d5400c0c0031103041d0801c13141035100e40220040106440e10512444121072003420941c01c0300d5251441c81003025080803c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 488916420 1250 488915170 488915173
    0xc0a050a03141f020a0e010807090603021b0708030702190e060906030309030a0b100e09190c150807080c09030d1809110a0206010f0e04030e0105120f011809050618 72
    0x669042d071000b0b00da109222102d0303200780541c2d03034080813400811400311b403241503050110100034040715660181e90340003551414240140e55405601a184030a00102070b080910710130921301190207030002c000b50500b00d10030707291b0f581ea803074800e516014017944a001e008000c00d01c440010380036151282215800c040c0140a9902d412014000700b810109450b805a5582018205000d940c10b82000c90341700414100324034070b200b404d00c0010b460300c0d80045605011451415400001488411003d01e0f00500940005003902d1900e560043d00031340003202c4190105a141c800940706100d07c2c81164848100107004c0c0085420115050310841c001514801d11003185100116461105200350714009080c043c074181c42c2d5159610084c03800c841608410034492801e0b1041000700982990300f034000b41c2c14102407100080c42c0c0d004039414050070440c40c407451104800c0c480200030b50100a0b040c0c8020040703680e101518206a14180e58101400070000d603c0000010307071100e0700452221403080060b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 488917670 1250 488916420 488916433
    0x7050c0409170d0504020108010b07050601120c051f1b02060a0f0e100c2a140d061a0102010c0906090b0f070c1e050414010e0406140c0c0c0a050a0314 66
    0x1410b1038a40e8104034207010481d5a1041130109540c1c01003901401408858591441d1805955031180c45800602c5030f440b1582f0301f80b60303180800c07011140720000340501074011a51124112400c4004a25481c50000400c00104100f0107140460008008464001d070845140c00b106d40d02c21900d4104400b007001c1080a6031b0030b0101e503035503207448101e0004261394500440d00090b0a250680c914030240c104050442102d40c5000028904407401c105c07a00f814003410309d0029440071408507804594010101458050100c0070b401d9401d801c0c1200010070781c001c000c52064042c007601c0c4840c9c140102c0000c154409800c02c110789071100204031070488503d100d81042c20b26629003440442c039400a0310940a600c0d5400741c100d120085500007008100c8084c0204410000c2d00d030308119040c02004825039603c000034060150700c2d0404180000081d417845030718680518420030750341140036100114014807082010601c1d08030004c4c420760303d00a04012903585190784e010807003a5000f850480500030305 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 488918920 1250 488917670 488917703
    0x1b0102031e0c01060819031b0b010e04140102040603061d04230102070506091e01051005060d2913020408060606090a030813030c060503072001090c150306060507050c0409 75
    0x2d125085c000e01b0b0f001a111030003103039803402909074083e440703020116011106506000c40c4070350001030304603080000980c40b16121420010700480300c10f0b2641d100c56000280009010744d01d68019000c80e26800462031400e0200c51070b03e64608420744020300a510810032000385a10300700b0358103a40d98290f0000600d00300c040d641e05410100c04403041c1d40075030041018150100804031003402503600c0b60f80204402c2c0346c9132102d6079100040340910350140b0b034080b5200c44280703480c0d80000b070544c224004000102100000600d140d40b92184080c1c0a110342c07281501d00c225083c000d413015240c18001a000d00c0d5180014014560001c00445078801c250304070000106186034001c154013110100c080b40151f0450034044904c0f0900c2e0301c0001042020420018402d911070121034692030210080300d50700c003800c009a0b025000c02d000142c03215000e180001140312b110f5141c0c50b60b441c1561414801e655451134161164020f01c80043c240b5082803100620501d810350003079800510801d914036a81598 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 488920170 1250 488918920 488918923
    0x515040f03081914120408091207061803030e130912020109380903090a060e040b010215040303020a09170109021f0e060306030312091b0102031e0c010608 68
    0x590300c25905000009840d4508140c50a1090003031059401e1035080488418420b40d02c603c031707134208075450748600c5c0c01240801801400b1640318000040c09100c5142480742155103524036403190901182003080d0b801c04080c000c103103200c220381c1c040d100c0c04410400d80e0144000c04600c941001700c0070381d60b04d201d600080c1e20540c0d0b000c645a030503030000a2441140ca0603007019201c1e00e0022410034248881115100da24a10602c4051750600090119031501d007280d902c0d41c000e04044561000036088049495a80203990100000c004c940c02c2c000d10110350016a20740559046042c01d036480c000c006004680641c008041c09041c5141a02c007969480c0380c1140b01400da4826075110740d448001c1c81c0254681030341c100c4410404581100703109400e0400282800c003400382c1c80307030040d8400320004009a4082c020395060700d1200c0101c07030461800c14952600e814400d603400c0c22340d4412640e92a259440041640c40002d039001145250140c003c40c402d600760000c600d140640d64881601003142c000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 488921420 1250 488920170 488920199
    0x20727060b18091b0f0c16140a03080a030906060e0901021815091e1504091b021903020a0204051312030e03310303021b150a1b08220e10051504 63
    0x487e80018100d0b24241340985110250540e15140f0401c1100d0040c008512503104a4110002c5810000b4074020b0b2032800c035018108980c0503411412006040005a02045d002071240c110440b606c2c0c0d0b0b2490420b410080000424014a80d100f6800c0c061140341d41816031006190600414144514500d51070014070300c485d032000c00e0214080041001c0208010b540615842010340e0301000c06000103206009540300a0410200100103040945038289402441851306080e0007800502c02850441c01200f11042c440c0c2048481003048900204614440d114421840a120015500d0010740c62085034070341c45e0038560a891164228000044010910024001180700c0d0f005001d0354902201f80e0306502e42c50000d540e0140d00c403210310031510a141c40803070300d000b0b26908000c00c03001010526080c2810351244000e0070341c0c4000864130100c02140c001e040800400720741d60343c001c0f0f031525501c2070007010950701401d028a410300e00b40120b15014050048c244004030242d82040c0e43e400030f8200555 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 488922670 1250 488921420 488921443
    0x40f0c08011a031b240c030a0207061d060304060b06030406050a1514040e01180c082103060d02040b04110c0f0d020727060b18091b0f0c 60
    0xa64403049044260b4007000508192601140582280e850010010000020042c1c505210f0b035004001440610b56002c042d50595050100150b100c0060b0140d944d6280e00240a11002d446494000036402d880741202054248280b10340c00032481e88501485803a03000030300119212619480030844503111031001d10322440c002d03003001c40c1c0c50a020300b00c58219400080940c400c1c0480300010302c90680112038048002005550001c1c04001b4507524600400c42c00070004c514050b89903005003407000c80b110340e0082d29201d07000d075100c40030342415000303006040c01048682c0c2c4c40b003030000424074507003a00414040b900142000c1410035540780014100c46001807505c05048002c80c0c0703c0d81c2036104003c3c103003013407803814014840c1000004001e07654018920a08284044041384141e220178200d042808892460000344500380d140c95820040c0d0f045681040c02d500c031200c02511035850035445071401010383c83d1414207281c1c010038000142e0b03408a510380382c10440400c030954013001c0401c072104004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 488923920 1250 488922670 488922673
    0x403020d0809010b0a0e1003120c0605070813030c020f0a0605070b13050c09090109080d021b162904090e0f0d090e22050f010e070b030a0203040f0c08 66
    0x1242414406070080d040902800c46982c0750240c0701200d41c4800c40000169120004502180c1d42e0700030072030a685003642c2005000d9804401c0c5081d1880e0051a030540d034070f214107414000d50b51100c1c3c1c200e0f000603007111040c8030610300d0038503d404240500100300c081800a07240180714019000032503080145d5600c000c002440c0050708205010321030850079084810030580d08041c032166162144d5440ca2001945d1145c038512001c10f0003082d095000b5042d01e0303400f010b0251503080f0350610500941080440c00340007a000c44a560b6822408078026262080202d81ca20300c40e400c12040e0119024905601c140d400940d00c840034800d00c401c4045c100405400c41c000c91141c0c0385019850504d00c0600740001207500c1100c9036800e80703400440303a909075141a1014022907481030701441b20009205456504100002a01401e21a01280003025580104001d10598030b002c4030707007a076074000d900c55041c8400f003d00c040b5807650300a8000f10381140c040e0709644008071035601c3d0411440540c2d8010040c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 488925170 1250 488923920 488923933
    0x61504020c0f0c010e1806041d0105011806080a0510050a0f05090d030b102c1017010605040e0406050603030f0c0f070b0906030402010309060e1006170303010b0a26040302 75
    0x803985d000400c00c1c40b00c80155002001c44a103405001c842d010b02800c0a807180f601d0300b008417080c0c0741404401850400760002030001d0359465144281004001c500d0aa1007410048082920b800024602c000c2d030398027500a1501a0781034440708000d01001e405a14025200c03200640b280e9068010130740a004114054004c4664240b0064202d40c08210080e00901e080300c0340490303041d0407023502245240a223410f00c290aa98409038416022507a251640c800203c143c80e0351401e034801c481140703550b809948042a6602d4101c1600c483c001c0d84501103000440340300150000e00c0d10b4028a80001000d002c50381402803120f225a080d03000594600341950003040710481c503210030800d0600400400d5a600d180440140c0420300c903100040c0080e042c141ca401440040000540c054902480e0500a03240d0100d1070b49010070141c0624420390001746150541c0c568820030110849048540c40c00c0003903e0710320000e41c00c0ea10460f01254016904400042e45041d01c801c00f1001485548642d010700038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 488926420 1250 488925170 488925193
    0x180105030d090509010314010b0907030222050f011b0f03080f0106030c1d0d060608030c12090f1e0301020403060b0405250e0a0506041401020f030a02061504020c0f 72
    0x5001080c000900c20451880c1040203503440c4c1803929410f494006106c4008640c0c0c1003a10340c0585034840c401a0815402d0040104096041e800360500b03251080210740180a501e07141900fa08042c01800d81c0304400800c51310156024080c02c82e11075100380421380e20003d4130f844842140440300c0c0c040c1c021900220402888001c1c8204640c0074080078201040481e4000c0e0300181000100a042e100f071003840b104c2400c0503130b9010240f07103045911050500c82103444650075500ca0300207071403101651280400c2649118000310a85488500c094010f01074000c4400c1042000003144030024800c09641c1c0500307115407028002040a54090003000c00c81051490a000c202d88009015021340301d0945520f22603800100b40803c5000341c1450108440c0c04154001900c508151b0311041c0d0040c0700090000e031882c4268940010100240c0994071100c1070070412a459214204407030300180c02450004049041079818400c9610014200605004851075660b1400080c1d09035030800d0380c091404141c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 488927670 1250 488926420 488926423
    0xe1c050a120e0618010b220b0103050c0304020d08070803040f0b01080f0a030e040b040608011505010c210c02030d030515060a1b02370b070f0b100518010503 69
    0x42006408070001c0102004625030161990f0000c1c1c00740d501d0b44100e1020503400c520035008620314500c010700c840c030020700f0601d4465040c0142c440124180c0c0c1060040c01350307580a841260710078105010054a9a959039080100a07154503100b101c101c0307424007840b804908040c0240d071040703100d488815422a01c2e400c040c1d0760703910305922040c00d540c40a1034232081040b001c170701c07803001e10742c1424108461250f0b07100107000340000750340103a002850100c0000c2d0410054105a40b0b022280c034007815041d0303d40b40111108220076070302414108414007980084c8000304110007030102ca43c94114120000b50780000d040c070303240304140d5000a840300d06111302c1c0c40050b15080b1883c0000c44181c0d1510142d1500074040d030321007081140300304050703081013030035921080300151020001c9525483d2040d1260000d511141c4286242c0c1078144c0c140f0320104640d00c40000303c42e01150407240011040d800703903541d4010040d00800c80002800c0c40840014151942603815401c1c1407410070070402c560510040c103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 488928920 1250 488927670 488927687
    0xd0509060d06083003090a0609020a1a1902010c0504060c03030902040e0606040b040c1205100b0c0d0e0a050f061308010c020109030e06041412030708030a0903110a02060d0e1c050a 79
    0x505018805c1043c44091500002c619458507800342e000b01e1040307003a000080503a02c8a07403000b28080c070062814207030701c202500281159000150f40140450200204074203c030348541070980410030403c000e001e842c0c000c01e104ca2040d8821b14010444208036800f04095034003600040300594032681c28044103107860300640f03101e00800e0714204450b06000000030b044050320041e58104942c0c51000c40c041105550071600544484800700d80d4400081008a03035030f076000c40c0c04000180c040b020f18a890b242111400003158001003100d05020907203070421105601c2005203000c503507101080028080301c02c1c047d000342c0308416000000c02c20211305001c0c04000c518036049101c1c0408000074045903800c0b0048402642e41642d0005844d0000452140303544510f25010b800e901d404020032501d002c04d50481c1c00203e00c2079946008840030030742d81c00d983c3c507030810001b0f40c03000c0284042c0c46081e0003503011386082c40c0d0311740c00c80ba0741004183d254290004042011070000e100040d10208036500070140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 488930170 1250 488928920 488929003
    0x1103010513031d0319030e120a020a0b03150a080d0315030b07051e0d05040309050102010c020d0315120b100e16030c0504240306080d0509060d0608 65
    0x1414807207401e55002403601803c03801040003401c83c10500307181601c040000450340f90500f150581c4100d01c5c0e08001d0000c4601d0303c00f080c4110342c00c501a2840c2c40b004143c0802240c0d010f05030b900c00380d00307002ba2000e00350030050446449400c08410003099640315000c58000f41078400c080d0099000104c001020340c1c09452034101d1002981c6401c00004c1d51804135a41d029041e40b4100c1e03114007020341c0c508041e446503041240b034070754085172003005410700340d0000c0e0095220343c0b501e9003d20703981c1005a003038900c22001d400142e0000b02910300006e010b5000325003202000c000084a4a0b161081001c450072480c000f0741e401d4040c03100300011825060740d10b0300603018182c0a80518070301050707800c11820300c01c0d03401d10400d51115002c00020303004005407000707007010140d070100c84181c802e1501c0c4580d00c0000c0d5500000c1c00e0100002d002c02010841d8400c81c0203981d030f034034a000303884010300c0030316403041c00c18142c9199183c00c0001c01c82401c0c40071702d69240a940a075403000700d260100405002050f501d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 488931420 1250 488930170 488930191
    0xf0a0b0307081e01090209010902040906090c02030304032708010f0506030a12180509040308070311160305070221030a02160e010909060b5d0c060711030105 69
    0x4042c0081100060311410300042942d88800010341035403414003400c01c410009401c9850000041100d098a801a0081e075030445001c00c1120fa880d000242038648203202c66000d60810008107000c82e11030250300b0b0001d5003207021080c0c4403e03c043c03050024403096004c61000d035554001c02d141a50036029054200394210000c0c108803e06440324144203e10012400034030402c860271440c204003031074100d0010300d001451203615203070505028041c04001c40c1d60b9000280b50840010f40380c200c000036110502e00c81c09000301400200e544c1690241e20403501039a0146c18005040e1a0594a1100c1744580551002031910340038010b80103880c0178103c07962501518015641407010140c602ca80c24111881020007003081540790810000030301d00d0b031151640182242d8051144194860484000c09030802444429a680324040e500809100d0b24101507140300442c2013507900300c0c208201c121405602c010b1718082640d450000d882503008240c210b410a003045600c400701e00d02807281c281d0203040c262 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 488932670 1250 488931420 488931433
    0x10905190308031f0f030c060503090a050114041e170a030219030b01090603060605090607080c010c09180504380f060907020c0906011b0c170c06070515040204090503030f0a0b03 78
    0x90b10701f07002c503c480c014201080000300008000402c200440c004541c1c12100800103a8120241c55130086412070701650703010752480300f5004090420941e21109604462040643d05000a40c8000c9034418445082019000d002400c0310010000103418800c8032910300080c00d0041400140c03243c02981e0100301410710301841000300035081422100d5007501260320a54407101854201e44600800000840035880c1c009400c03003142c0c004100200b030742c01001041008180310f0342d15400303444044400402803942d0b464941c1d000703d05c0403010240b00c05095203071020b00b62511503c61418200300c400100d800380b41e8051025904085d80b0f05c6402071a148041d2100e001224080340c0140000390000341000303149007110305104240700d5082c083d26800b41039620f4041c1d80e0400400120726104000c501402121411141840d203007041742c0201c1d03406400b03402c81080082149012100080c01030780c2040e1500f144a00013039050004501c00c403910070035480e071400e01c114a1401c07a5245028035001c2e40c0202c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 488933920 1250 488932670 488932673
    0x21060a050907050910120c0f030608030a02070b071e0317161704051213081207030903240204080a0b010806060315150604030309090f050105010905190308031f0f03 72
    0x100c01c4644400c1c0607606000321344100300049074641140003604040c1032621f01c800c41032550103100c410011a80fa902440a1521070b207040b61280719101078100540d0150604220014070301001d00302c3d49000d1000000702d041003014141083c0e001a40403000504580d07840c2840c43c603100d96043d000080c1c5036401104003070ba004040d000094204032041d101c2500340c0001c0070400100310812602080350245030701e91446004048056203c2e01030b145807130007090300e284044220f4206031003405415581d0100d041e850764403450400e003000c040100d40301c00a1a107403902c1545900040c401003041100a000c3d4102c5810400071100c4103030071007e8150400310601030307240c0e400105502ca240404a01408503201d6000e40c0541c0a41300052681107071000c54000241508221003501300d511300502400411454020002141c601b40070341e40c00714081110510107800c00041042d401c0b411141d951401c1c944a81765030a107500112480b0304041201e04440398072205a94004009098a050f104a01802d6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 488935170 1250 488933920 488933927
    0xa260c0301050d0609060e011a03030c07050907020304150c1505190213080a0507060f0e06030c0c0a0203150a0c031a0909070b0316031407020705010e030321060a050907 74
    0x1031164610441500c50703594144a803a45c010800f2541c0329508205d070801c500c2045010341070040390804400f0510980181c80c3c20040212a101013031030019007022400d040c10040780c107602030301040c1103100c280400b02d0100c00c8140080307603070311642e141c98100819a1804240040c0200d10070107103141010305200119281124589041403006e0b40035803100004044c00001e04d810380d120b40581c1c801c41d085442030110100da0300c0d00340e400c0ba07540c6040303107441c00c03c058a4091403607a101d0b810060420000b0700441664001d0546030048005858000740640c00080c035044c943d01490159202080a001048059110f00100000d403400e040c1f11914000d1941d0609411201040d40508500c0002800c122070901c45c0102400a41c500d0759140e00f030055240c2e0040600900050110749404c0c0c5c6d40840c040d0400c145842018554000c00505007480011220840414030307564040c030061159500c44c050b04540815803480310b090f05500743c84c00f06c0800500d0416903000e01e0003026100c042c030414550 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 488936420 1250 488935170 488935177
    0x10030b01080105150c0a0b180a030c0312111803010b1c06091103030301061e0305150d260c0c040902060d0b0a090e03030411030c011d150a260c 63
    0x841c0c02c2c00145031000981400340c891000b145c18640142c010650400241261981c0a181d5108400d07843d103400444065454003040400b4011540b0b011030310002170300c54014141280c05403000072940c401302c0c40c0b0480702c07508800782030151140410f20600460409114010840b08100c525007014164030b400d140303505505c000c0c094000d82e282d030003039018000582007100143c030014040341d41e2580c1d41c2c03800426800c068200808584440f43e440c00b0131078481e005250052041026a2141600c21070400031400d42d40001140d2000e0141d4103004c1500040201540c0464042c0401d640d84050800d05030070100b041d140544141c1c40e280718003015032202026140d42124284000441140c2600058034180041d030200c40c20f2810211007111201012001d11b00a034841e1b403000c1c1c07016014400301610f0368410b8180500080340b5003440d034140070200d040200c0300d0b000504a101e0420440590314420f81c80084c0c05c10200da801c04001314260460790040c4034103604044001020f04046200031038a10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 488937670 1250 488936420 488936429
    0xb090f0d0e132d1404030f080402010c050106060c0c0f0f120c050a06050414010e01050f07020a0f03030302030714070210050c1f05160c0203030a0f1b080910030b010801 74
    0x4202c0c2c800d800401c026401440820b42052500403e004840201c071410001100500c8000707080603145095410b008420300d0290768162148010315089031411038080000400580c100881c3c0c00d08407012a4080c031881001c0c01e000e07600c280e0194103a0170309030050820703a40160741e2039454000801c0341900110124065443e45088900b00070202d04100102000c550482940410212000101c2941040c010000c484d0451130016881609100540700441c80081d2381e80800c0080080f01c2041ea2460020140c2500c0201006100c47d25001400701c0c8240503007044001c01d600005001c0220742001c1807100312a503c4074424a8419554041360b4034860343c45000f2300b4040c012445000340d09003030150044907807207404219031020900c5481c6014141c29a078045050681604040c48148641501e04644e500500110700d01081e00208030344200c0b02d824000100a4082c10042005012102c10900540504200d9440b1486001001818a104440300c030615107040400d010a0741c00a0400b411107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 488938920 1250 488937670 488937679
    0x2030a0e0f0d110a06020a020a17071505060612090307060e06010b04090203040606050904060902040c032702010c02060a02151602060f0603070b2d0715020304080f04030b090f0d0e 79
    0x4881c451000f0b240c085400d13030090680b800820090092580043d1940c0c02038014240d1031403850032035007181403030b208040000e0105141184840c1100038141c20013504042c001d040d203807421140044015021200340c8400324503410002e0601c082c84010f0099034500d00b144005801e01d5494000e01d507065100714494045105e40200001c1d043c0405644800300426000d08184441d00d058a4440020040140100e110302d14003408000c40c14464410884603601f1004003410000d005245031541340700c420350407410010a800c00368010f0719803502508600c01d060300280310144040002c169030a1004004002100603120207449182d8005400c0d50418928140300410b9200d0101003410213019420081e040e0318005034800031180b403013030b181c140000c00c08400c1020207010b07540c0c07061500c150710f805001c4d07050b121f800b06c1000311513500954100c0e100b90381a901c1c0189174801c1115680041d8001c0e80c3c0140312404210030082c0500c40c03112289400b0015200301e00e01400094180c500c2c101009028 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 488940170 1250 488938920 488938937
    0x40e0a1e05060406091a09010b1804180206040f0905091507110109140f10200a0c170c0c040c05030714120108060601020d110a020108151302030a0e0f0d 67
    0x1c80d180d40e131218014106802d414032005851043c40404044d2240e0707518000c14610000094259200d01a194415580050402c0c0c0060f26000c10000d00038108030b05441d0886260420016070302c1000420050200d0060b0450292070b100c040011601c009007000700540080d006000035003409a0b02c180d0059160800082c1100d101c105540108003407800189405803807519003102040000d81ea402e9450b14034101ca002c3d4092526180c150b50300b64581c41d0440032600e0701c100f511752046014015507411460030ba01509102c4e1108244000031107101e11842d20300107001010200c040c0b000b032407045005d072170500c840400124000c1061100501d401304100e06604440c0070002900225156840445400c80141d61100b01094071030b80d0a039485400f521483c0790040c41140104410b0f07114001e006c02500d02404941c0065038046402001400115480030403c030032a51040c43c04240075080c03180044c0c407440c150074290112403043c0c8942046a1001c1e44010321403c000600540c140c45a20b0007129 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 488941420 1250 488940170 488940181
    0x12060b0f0f09090403111b0f040c021207060207060605030c010903080a050d14010503061807090213092a140301050f030a201306030b0f0603030d020708040e0a1e05 72
    0x81e070300660035a5680036500605010074180d0200d003c0e40c615134904141c407000707252054400a02050815101d40112032481c01d0701017840c01c0ea111140300c1126005403442d8100760204240140d008540881e200d540c04a0303000c06204140c40741c40c02400c800e4004244007158200064150000317440000e00306070000480841e0680724a00b541c07000840c410043c08100b00126a40100c1d030001d0144034080d1083c040080c070320714201a40604610390003070140107254181190000139500400c1c100d48070a031001000603d541c010701c1203400901c3c2d107651540d5140d00071081c000c20000052403000810000c011801c84140d4214201c4e411288203d0b078035110428078101281c24001030810103016144032550310000c401c400342038618800b00031110580c070014000c900e04201c503018080580140c5a000026001291100720390340c004800504490801c0e1a00d15090140e03031107000219170503400450200070f141051a0702130341100496100f44000740314400404a90f10403004103640b5580c44502180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 488942670 1250 488941420 488941447
    0x1409040b01020f011515090605030406020a020a0218070f0305060105221a0418090f0210020a06020301080c031014130c05060d05090d0f0807120608010c08010612060b0f 74
    0x120f500d003140703000f40038041da11501103000740c02621400029030100340d00100744501c221400d20a41d52142c442c103045031583d44465000f500400304100540c86415040b4016a0751924a1820007400612560b494603040c50018600080d44404100349030410040c422103a801006840c0040705a94940c00d2b807070a01100711045d044241d0124044c855108200c001360b0075404001c20a4030320054a42004a901140e243c04440306000c000c1c00d80c2280240c0e480061800350300d42d400b4140140f0441d0b940780a1525000106c0c1e000b03034008481a440840050748904040c01007000d1006526802c001d0300b24117400710350720300030020040480500030600b946c0400411350300c104060f14010704855102d003004100d040080c20709560602e0503100f040c00100080348115101100d01c1c860741d039100c2c0070b510340c4401600c0d1304280d104606000b9032204008220b10100344502c1d05035040340e60705c0400035450001c019111100b45140000b02500703007d414002d45405504907080f00011001d420343d512003402c40382 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 488943920 1250 488942670 488942683
    0x12060b0a0f0501121107032a170327030c120f0a0305250f030f0b100806030127020108090a081801050d0f0504110d150509070302090708161409040b0102 67
    0x54442e040046005000d0648c401d419034810364080d80d010f4491810f520b1004140400600c00400d603062881403170700410b405601458024103581d400003102071717210008800e2031074403c000c217000da480410003a418070f0b400c0282005240c109115035140000b881060049031160035080400d040c3c485020450300c10070440b00d6a1a84620003e49d1440007040000802c648410165480041c1c14010114203050300c5208035103041c58014074055249823011030a40c1c01001c001c150940c1035580c2d80c001400b4105003114864007507070103000c09892208a1001405074000a000740440c0e81c001905040055401000c0710b00c0d0040c01690009581c80180048480d48901000c032541d150810f02c428003003451030707001903014500c42c1101d840094426001d11202e186180006041070b041c80d4001141c0102e194021034000c2035207000d45540b40c3d120b801240d1140d07803e480381e400045030b1000300283e04841400c148100442450501d40d13200d648039001141c0e008101209100d03940e2048000e05982c02000b40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 488945170 1250 488943920 488943941
    0xb0420100504090609050601020a0f060209041503050d0c0308040308060d02120d080a0218060f1e0a030e16061110060906050112020a090605130f12060b0a0f050112 72
    0x540d00c00d48240680100707107802c903108810f40d0605007440401c00e01c030140100c80c4110f03810703401030400080c20340710083c4903141a803003514101c0c0d0130485a040c6440300c0c06003100c242101082070340031030314500d4810725010202d0724a508209008c03c2243c0081d034885809508150545801c40c02521104005043c1d036442d05002917100865814200ca1440301103210010300d001519911b511340c2d200500b25081e4402c5580c0c95040171401440e42400d881d000d4050a00c40426181841c10702d4640044a02d164981c4652851140300101d6203040f0203505000e210f42c0e0644040c0900a245c1207007095541228090052006201020040189119040046405884001c01c0030b0010759030b2083d0b854010540c0d4064680080c420864803054022a4004c81d0450341143d600c002c8828a001405c0328aa00088c50240c014001c0400008050b0800080f48002c2c1c003206404903413450385403600e40110f46040032246d005082d4501c041098080c4107005004882081c2050920b014407002a6030040c4110000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 488946420 1250 488945170 488945179
    0x1d0a021c0c1509091a062506090b01050a091e09080d060e07020c0909070e0705070f03051c1811010c020409080a03060611060411062b05130b0420 64
    0x994030055400b008800444085600400c1490651440c54110700c40351700342580c0054040103041c107172200391b030703800186000824407030060700b4140d681d45c10a84500d0042030310b9140a500050200d40307040a0010300801c6034040800c00c40300384807548641851140c19121540f55101e181c181801598011543d6a4040340700410070340d0b4652164010445d000e0b15540012b200d00c0b40113800c50f0900c01e07170160045040100801e4914070380460003003041002001d6104000d0f05100380b500041c9400181001240710343c80c2c0c207444000c8840703900640d2600b420442c6042d1708100e803510803210a01080e141e00358210b14420701e6081d00030010386503801072000c0250041e26000c40c8038280309030700024040074441641c050107119a2540d0440383c500740c140c2d900da120f8100709c02203000104000001005c21380b0180c03009080c001200720390910f40302c4c40214064038021013048442002502d225042e03202e03840303000f542001c01003900c45010311400280000e000302d50350100d03508a42102212460800401003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 488947670 1250 488946420 488946449
    0x20405040f0816050d020a08070215070512091912020f04150305010603050c06030108120d09151b1b08160816030f08060f060d0b030d031d0a021c0c 65
    0x5400615260b0000190780500070300c5c0002c810ba0b4404503240b00d200d40c202d240103003803100e01e030208044c190450824010114041002a001031814000020000c1d11030074040d17280c039440410f00c82d03240041100ca0f100d00741c2e4071f80c0511680071910010712115406a0b01b645203a54400041402002c9410003d0032405c00c0321000810024150002001c5e04d02caa002c0d01c42c980a46014882140428040c01c4900d410500e0807205007504540505002c0c05060f10100314003149490f0031402d07800510148010b140c450400840c0943c00c54044480300840349095a505644800e6805c40110000d9000382141c100045c14641e00039140c071241025504070b0b202c5a60b4100c412000007400801280450101d0b036410070450289000340c4e00300307104400c082e041042000c840b41c100401c076413140100190301035582215905d0b80d10100b10100e040f0507180c40004541c240c4085e81c0d00b00c9641411154134540c48001480010b0312031201c101d9040000354074204a08d80741c0d02d424816240290840c820582d5401c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 488948920 1250 488947670 488947687
    0x30436020a11030c010618050411010c11061207021e0d050d060509090604031701031a0601020307140f070915060c0c12080702040608060f040b06180c1210080a020405040f08 76
    0x641c013610840d03002803a00f800302107c0c0691030b42a104121805451408103843c4400c1c1540210214107400d40f0410440385a41d4a9000191007500100b482100e070340f491104012680d0780411100c0005805082200b02c1c001010070b1080d601c0c042000d2101c04c00c44086a17102d00303601c00c0e4105001401d00104104a1464080c010658605044905070006440c0c2e0700c100c0703001c1d81d000c803926050303c0c1c20040c3c4140c5100b42d400c070a5000803000d4416411032004000340d00102d0b09540b601040f04802d8809041e020002c0d00b98540307030402d02d410910825150054070034640c140d0320340d92000c07503089046c4992070900d281085a41c0030b00a601015103561910303074646c1000440401044200d01c00c480400a03d03032a441c40c203a4606017151901c9031114100c01007008290704140d0581d00c10303002060605c01044280082e032103600280c1da03140401d00003040300c10300480a601030b2070344100c503801e02142c207134a840101940d5007092207010f80201d640c1c00205060110078034a840c481500103049503900ca520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 488950170 1250 488948920 488948923
    0xa03060e0102090a0b0406050a0c3201151d04020303041e0504181101120209030106060c060b0411040e10050405070c0c080723120f030436020a11030c 66
    0x40d080b4980b24800b26500441c40005c05000e40d4280d503210343e1198202020090141c2d030324001c2d084103403000e9038031214034000501444200c510200306003140d0b40e1010340b200c1a55081d280060340f2030301d00e101e08543c01e01023074a04103a000d03012044810a075202d81c0351800803900714812600142d441c0312500700d0074240507509880c5002256000d460070004c2d501c03921080e880c1c0d410760386401040303094188403030f0049611070407403840e68912a400043c542008000028211096640302e0400308803120b401c80d042c01003911514035480d101741c4040c04580c9402c1c9442000d44224010602c80501c030b900810180701480595101420001e4000c20644c01c21f42c0c005440b07000541812146001400000301c0c0040020071003c04844a150108484016440509101750345c480f80d041d41284d920080d0000180003045808580e0108034051641d43d41480c040100003c4181760102d80120800f0200c51114501d00082c810507001c6a401030311040307003079021a4501c042031040742181c0701c0480c00d811070290 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 488951420 1250 488950170 488950177
    0x230d0507170c0306070e040f06170a03080a020a0c1202070305070314160f09020c03090303130e070302040602030a031d0607030c02010c090f060509030a0606090b0f041a0f0a03060e0102 81
    0x1000c0c04840b54402e03107808240c1c0c2c80404807038440c00a20540702c01c1c00d150070700d174010844950705e141d00414100c1c0c07214070096050421b195210b405502c07088203a4181908009400d40110060301e00b0342c541714050001130104081040300601224607003070702c0f45900780300b481058003440c1d000b816580b0746540c07410060b009401005140074680900d594218031041501200d80c00c54403201c0c0903034840c42c900001e41c402500320884c002d0700c0380020014880342d03650500041c0040303010a19203c200070306001d601440490010551020301d88104014003050b5000401d60344814400e24000c9803100b030004224804520500d050f0300a071084009010521303405410000700c40c64268001c0005204060741110f074034031030384030707075101d14136100c00c14481c0a118074001c100c10740c1c0140840d2450390484d50380c1811203202d54429501c560b0b43d042001040d00d026242038180c1a011942071041e029401c4441820740350303191501e4400d40c442030720b0041a8444145603402176030400400c005030070b00360b03241c0c41c040c2d407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 488952670 1250 488951420 488951459
    0x101b0c03020f030c010f0e3d051c0b0402070501020d0c110a0f06021803120406140307170714310f15031803050d0510230d0507 56
    0x1503002c101403400d00140092440d50140e50b1071040c085440740c19507000c0d000d02c0344190440003445560740c01160520121034052040081c81000980d401c00ca4500348071a440d036182080003c10400c941415824210500302c0064880003c025904400041c0244075486004203554000308103580e840d8240d5001220344800c42e20380700ba049401400300b6803503a0700c03242c009000050315070406c4003142c41e80e409050214551601401c6c1d0f01401c000180c138010501240d0649000300060511409511043e007004600c0b26401050450818100141c01d10742e00840107a48070710444005515a40f0400307200044000c115080355480307040390021801c0f043e007400386101c080c1544220400058648407150211481845c0880d0641d052111094804010440040030103445001c006a603080101080c0380084c0b01e41c8406a865805010000584034010704101102c2e4600c2820000c82c14558822249003006c03183c5c0c80c40800ba01000039440503ea014058640d110748400440c0d8040d02c6802d030401e12 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 488953920 1250 488952670 488952679
    0xd060e04081305040c392a060e120709051e0c0406080c0703020f0601120b1f060c0c090608070602120c030702010806010c0501090b0105120c03060105101b0c0302 71
    0x50f0307111010320050b030341c0c0f0300e81100006010511030b007841c1429071038108210106140341c1e02210400714542c40c3c03075140c951040d02e821060090004e404c00000c0c03170040f1445809842c6000c8589094000b401050440800c0b034001c80c20080001052801844104041d15464100704054204000c40200302a105031103248407000c50070203d0507070140003060314100c41c202e0341d81422aa6844c806003074160001d40d01101544502c049003813000506101003030181840000e030100071503013801d054002d0000504203894421100c0051007540d8454200942903642d00d0a008485c5865407501c4509014241d000403452031078640041511000072503008110303103141e42151003005400000a5692090f1400042207a000308075030401940569031381a88500141003811f0740b2420344e00d6060a640503003108499200c5007000601c0380b8905980c1950260044800408484e604000401d561f95410702541e03100309080f841d803c0089200e035100c4450061860303080c4803400c205182c00c03200b4688a0200702d109 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 488955170 1250 488953920 488953957
    0x3060504150b0715091113051302060309030f07061b0512061504030b070c031112031f0b07060b030705060c0a03030504150e0f0d03021207050d060e0408 67
    0x514160081d05420700c8071030340111075107203841d0801d4040e600891044030b0312502141c691103200080d114407030b4118015001c950744041240f040000e480c21514860f0740d030304e20707120500081441c10320f04040301a07419540c0d1682d9884484545255015010528540c1980082c80c1410403100c1c1c0c12010f29000106000c4402c01c4409005440300e00546c00071520418507200040c020345800c500290b400c18081c05010b1a240c0c03a5120101003100c110f80c1c1030007240018849108041d030103007000030741e518000080c14503800104520616803202600c020031041d00100054020040c502d1004000c01580c46c0c801d64480ca2442c02101500381618040c0c401d00034a60001490704100d001c42da400381041c40a0820b24409035001d40081c50040d009617061005d0091820110f0001e105507204044590010b01d080498030744140c0c40d0801d1001880c00301401404180d441010464090790030038058140360b51144440400752008010310b900c10001080588180005e0019883c001d21101c80c042c40791400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 488956420 1250 488955170 488955179
    0xa0e0f03010926090603040f030c020a140a05060c0a0f051c020f060105031902010c0303090b2a090d0b0c0c100218030f06070f0c14010501081605090f0402130c030c0306 74
    0xb481c043e1502203500b05c0d50030400100043d4000350186841c071710034189044e280300c164010a90780b6030560406098103a8402c245071040c84c10358034040050108035152842d0640751b5240b26103c018014008105044103c00c031410004180542107541d25141201e02041011100c001e5543c80d0f1000701811a0050030004520340c2800f0440d60f121030b05811a041082c0411743c01121080c0da041c80070b4080580d030752800c00004a001c00b25600030300d0a1740c001020705c40149a8104203510000b401c440d00541004150000e444800901d81d0f82c2c0d030840d05040d42a951f448040000c1d2148036601441c902a001d40d4400005055000d01740b50710500c64003100300e1410303809059403003031841203000b00c9621913000500003038859000341441405034a805000003049035203260900d03200c00c5541640d0794484005102050b420025918107424410310204280e00d0103002c0f07908584081c004080e003c0ea02030015041d51a5041c07a8082945800c4040143e03c282c1107004004000c501d2402000a007406030014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 488957670 1250 488956420 488956493
    0x207081b06070c14100606120c020109021f1713061407080129070b0106020607080412051e130609080a21170a05040312110a0e0f030109 60
    0x5209000c140c5864000400b02c3d200c0754400126016041c0302e07441744c070740008480c48940c004c19004202c3d54850b03800124415400000b03070f60080305040c0c21a80340038102c401503a0b48c0160142900d04200201d0044071071928221200c1c80140c070f0f02480a00301105100c00202030015000c4603601818040001d0031020707141c81c2242030140d452030005908400148a401588016620003d103403201509010810462120380ca8010700d00559610140301c004111898041c00300301e074411041e245c03e00c0d00780340c0f40d615001c0030100d00700c100c410440042030640d100d4a003080306403101c5c00e01c020716030340721403120385c030038050000c10300330900000d6610500268100c00062907181083c1d0144079601b0806041125590084010854100b00f10703a0800e00e0007804490b003251401241d0626000ca454981810040c2140a2400240840f1752404075411040b1a101050350992005480c0695003c4c040b0300008105c40c400c2d02d03405615520b0003407010300300001d0f10741c0c0c1e400da11402070744914215071501002c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 488958920 1250 488957670 488957683
    0x60a050306040515011215050307030b190c090303140913020c0d050f04140612041b1e0302061c020a0c0218090c0d0302070306050f04330209130207081b 67
    0x68041102030020031b051622540025803401c0340e80d41c001454650f00d03030020346000c3c0c1d0ba1740b05555041040c400c1c0449c4800562100c45c030b80791950700038011f807048554005d100c0802840083d04111010704020154202d13001159130031348c0000c014011072001c21421100035444001c204200f4850707021412609400f9005071381d4001820032900341020b20309800b1071a4a203002650a81c01001048031880c0f41d1300304442c5a02480c02002c10044c0500c400b0004900145950458030138003140010180c4174444002d500d0091381e0b8159110f68a82c0c420309205800c1d8060007656454490000c40c0b620b00301c591022070f041505000b200c09000316281142301f003a1051090380d44603141d80046169194904182c01c02e14482442403044901c19666521803504440b010340b0300900d03070800c000501082c171080c08024407050100286955003008032041500d0700300c0c4120800740c6400d40104a52070b41c0d94030492074125000d09120b0565a0381c3e880d02e4407984c550320a5001030694050f0003c00c3e0000480062a0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 488960170 1250 488958920 488958961
    0x231b070612150b03070e010216121205091201150504051b0f0c0303100303120213091d0102030a0501170f210409090515070f230702060a0503060405 65
    0x241800c550030403801c8005841c0b68004540c0c980705002c000299200c2480082d48100300a644515a19407008002070803c6014200c0c0c402c64100d40f8810b000c801d0f41d101d10360f01d0841e03000b4411201c7c42942c1c101580d06000d03054005a0220f0b000340703050521101900310482c40f90280c1d1011480c1c175252020030007290419101007000c641c0001e10902a110310000a00100c0040d441c0e5504003058045902d01d564000c40d0311040a480c904e0080003090307046244185003081525040d4200361000401540c2c0c6403540c42203008003612600d14201c0c08420f01c90700780d9840c1c00c0d080255600e281444014003c0c00d0207100d40050509003040340c6402460200f140c00300d54864002400c103143c011a642030b800c035480b0050b9180302c03004120004801c1c490707110300042d4512a0000d820844400d43c1202c3c600f102c003e004405000315007a40039281c640c00103606a0b032010102e01408101c1807843c06543c94040e0100c020b410450006010103260b030840081d501c9a40110303001d010507a90320741140446403d1110707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 488961420 1250 488960170 488960177
    0x604060e0c01261509011517061e0f03010603060510170a06020708040b07050d0f052104050708060112050111040303140c0c090a0c08010509010f0302010f231b0706 72
    0x1e034001c20807030f070050b42d40c03c000c4000201c0d4802d0122000a02801820b90000780f0b0b4040740c9260040b00c58000c00920305041d84100035549514002000c02e45803244041e00142055040c480c0003640d590780d41d4455100d0794050020006039480e4a0108000c1c001901c0c80d812a20030503500207007001c07a00c055001c5a903070200141001c0701e00d65071204040d41203040c003220040c40600010a0301d01c1c03004060440c09000784001e152960103054080c001603003017000c40d81000810064100034441c100c444408241003005100301c0c0c2e5480b420072904002c196041300c8800c1c05264000240300414a895004c803600400003040120028071085440e80b145200003408106042500c4a0581c182000b07040741d8074044059440c900c1c030107800a01160b80c111100c80035903903034042119000d5844002e99014001c20f031806042541003045541c84007483c0d11009040254066684400c6403242d8000c0c7d601428240b02400140c00e0000d950b1856003001e540482160f111504844d41e60500040f0f03902214039989 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 488962670 1250 488961420 488961467
    0x1110c1503090f100203041e020a060f122f12070302070317240a0806040f0c0f0602030d0c0f08161b1109060102061905070309050604060e0c01 63
    0xd40180080d0001802d06215002e014002151101c0a220061594095100c01640c030310f07003460b200082c440c0040000031340452110206c001611108045c0c01075031101c2c10540031b0020111000c950709a20780d0b14502c006824545e01484405100e01001034854284404c00080c0408400c0c0c41007601981c0c3c55004500d4550300810281e50003a0f0041050740d010385000c009100c0c4070056080f4506c0103644504400000005240e8440150403070f948030361404407951001c203172400c1c50301ca540d030300043e101070560101d4031030900801120f810110001c040b1210741e00641ca9855402a40383c0c0c11989808910600b00a42010801d210f00105189512951103c2c0c185d5210041300c280c000165403840801d11401e9082910300219030008580214810000c103040700070060144a0035a201422003815980706405200001b1880030201d00c02c484013580010309580d031100c00714050509040d0207811405064284010b01c01c3d19000301c03001c40d2900c421500c015220900465528018035401e8103c2e0075480c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 488963920 1250 488962670 488962699
    0x5010e011b020d110909100b030102070206031603060509040b01090b040b031f020c07080a020f032802040207080c0c03060f280f230703020301050a0302061c050703060501110c 77
    0x8800300351985005440c0c01c1510f44e443e2003c50044501580c000e20560b1000c9174918040070f40c0e008001e05484298002d5051850315070104d9174034080640b00c2000f0755500c2c0d90b0001c1ca18441d5104000a160041c199141e50a041c18091010030080c000c151425040801000003070070140195420910041c1c000d1650040600301c4990200c03050080c444042d800700100b008515040180c2e40c0030b4004140a004245100d01c104503002100c0e4488a000c0e82107525503c40c0e040541310180b102ea01c01141c054219a0703940f0008000f80b0031844000d0100002280301945d85000245801120005070200d8540b81ca51485622200744101d628805500703415140300d0082070b130304d84054102e440340317000428034484010040c01551019041c900320503001a603c0e210404500400b250481c1840c10304611b90750422011031001001804044d02504000415038424041c80010401e050303c0c0307420402071420039410042c007a100794443c10b800101c0000e12480c002e50702142c01c80034110000c0c001039481c80d40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 488965170 1250 488963920 488963929
    0xf04020702120d02011e0e06010510090803030a0c080907050603060613050a0b030f070914040b0d020301090303050a06050105031909050f070807261b0a17030405010e011b02 76
    0x20000807a008034420071002e14860080002180d54510307a000442c881070a1070170001e00c100001e4950010714100000000601d17004100981581d41c1924440560140003a05841c0c029003a44030414611000041006400040c0e0024540300e03065620b0b10020b441d103080c1d05039903185c0b03801440c2e4400c504101150262a12000034407581e1400200b81d41c41941c1d4800050344006540c0c0f008100310400010405070a00c15400252300c00c401d410100300d40d904207104411003603040382d0b12a0086942e4944070010313945400083c0a10360b0f008009225010251500801802d42520007555684c2803400c00704041d0b0288c0142e80c072850141c922201517034140341c2e03050050310019600359031074024145010755521040c001a009011503c000f0308649203410300d180c9036592903151460300d203039030403001407100c0c240030a04044a1000b0b0002190300c508100016000301151790060301c1210007800300e0040210040058400c4500903264150081841001943d402081c490080c555a81807a5683c0c01440d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 488966420 1250 488965170 488965177
    0x5061809070e090f0117060912031801050a0b01120b0d06050406060f060c02030c04050c0d0504080d06061d04020405010c0609080d0c0503040203010614031b1c0c0617060f0402 77
    0x9502e0521811080b15021641500090f502c0c000510301210040c0450600006049180300303042d40200400c2c07070851300880e00c801c00b0310025201d0303407000408200c1c442c05403078070288850070600017000705007400101d00000b8141d18240c0c60102d0b0041c0740041000c3c1c0d60f40b01e10840004050310741803241c1856a1380c54001d0400034021284195a14004076461485440f40b4029154036100d06500400038010145050303151100c2621841c281005c021079400380c841a00e415000302d4102056a407603d180181c614010f000070b180c062480c0000024080e0f9000d603a005841c0114645c0c52560b1003c08144001d82c4250300816001c40d40c48980700c000a0740550000c26130714002c505039814a1001c204807401c2d07503120000311001400210074003003540360a20074440104001d1001c090803884403004241caa030b2460100b251013000701c451900142c0c40c0e40080e440d42450212100305525070914022543c2c1c03801d030040030001380315256a4020034801035140c034000c1500038102c070101e41c0720900f000080d62 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 488967670 1250 488966420 488966431
    0xe09011502030901050c011518050c0403020f0d0f140a03120606022509051503060f01030b1501030b06030703020c0d050405060403080904180506010501020f060c0304020108041e120905061809 84
    0x10340e2004900d0348812014a0440a0300300002001404280d0884270b00540320090400c0f902e14004100400c010b95031070804094280003911159403c6040341810413820149003005440a500b41e00c4030070714001c1c003242c0d182240d4840e4413021403180c9100d038480101c070001d0094070050f030300186440481003540210548174010282c0303e09422a201c461800965038103907280c4004441c502520841d80ca030a00c5840e90100704800304070410f614640b00c01c41d6250020380a0700d01e035070b00500c010704a40d11036000a41540c0c1c0c09444c240d0f4070f0802a02c01402540019500380d40c07805a200c01e8003a140c452000c032800c0381c00040c041d03410142191512542035014000303040c0d01960b1001c07031640a0b20b1024810005a024201a1040350b24000003e0f007407003103205007000550040810404c4029400040c0c2c1c2e0403035020b181c2040c240d80d90b407400c5061081000c40c40141c12986180700b200308503400022218401080c2d403a41031481e40d071003d0100300d00664951801d42c0701c15801b00c68040c00d04580840c0c0c000b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 488968920 1250 488967670 488967673
    0x90606040906080606011d010903110d0606080604020405073029040c0513030803330a1d1b041509030618080a03200a0e09011502030901050c 62
    0xd5403840003408503402c40d0300a1219402040800441b0360f00240d107100c0c0c1d01e08440c08440100b800c3d2000070000345481c0402820700c0001e011107a10b5403250b80c0d407081d069500074400c006490300c03601a190b03034850031034040b4850350511002498031407142071a000a06034210f1560340c5900c8200e0800941e00c425581500016503c1d1011380c00004001d2021140000040ea030f06c14451903081480140c0c1c00341910f01050180420bc0c0b0402c00384680700c500200c030380050340c991f01c0b44c96513440039155078a8500401380c025a620550701c03500c10101c801e010b541d40115504083c6076524001c0211122002082d0220300121a000484230030720400d0442d0504990007242d031500740c4984280f040d9101e17003000e99000403100541402040024458095480c3c0305c002d044018500350364904665219140c0359108250f2114503005040340c0780c11081c1c400d0320302c82040750303110f11581c03100901b802c541c1062148034485550000070196682c040742070b040d2840c0c1d809180b0f4101c000b001540c082c1d005000e50550f6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 488970170 1250 488968920 488968927
    0x12062d0c091f05031015020a0305090414040804080705010c110402030a0e0718051312050d110712081305030301120804030b0109060501080c090a032d05030c010f02070b06090606 78
    0x1014060500300302d46600d688030b01307072203003002c03a00c0d44400d00054010583c00c8800c2e103a07107441c464001401500302d070703031628010307545091800101e00a884612525108418203806000410807600301034030666000c8021513040580d5240115110282e80b1009130018011030000a802d0425400450b80805030080c041201255810307064a022030b6a48040760030f500d17014100c5121585400ba8503000040c45044003e2500242c030b401c5948900408070100b403102c0000e0048001083d500000e000280350425030744c8980007418014011000c1c1241c0c50002460900000c08006003040d0920441da0801d0007103082d40c0c2041c50842044003034440503101c01e6802d21000000a101c120464081c00903400c0100d022458640003508101e00617140b9603140b0010b001d042307040d03255480105c00b22500889840304411041034802d070302003000007001080c1c52141e03000c00148a00040101100c2c0c1014000308441400710409100f24020324030300a00c40c0c1c5e00c40001c244c440c03801c00ca9041e0020b030014a010b16 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 488971420 1250 488970170 488970199
    0x603011809050d051908060612070927051e1603091b090c020307050d030b04060308071a060a0b0d020306010203090a170c10020607031a12062d0c09 65
    0x207880124645400000c07000616013040c08001c00c0b05da80340d031129080180e0f942c200300c0005820390050140075904112001c0000300a24401c42c4c0700030060282141d4101e41102141d54000a00301000308031b482c441c241000b00b41915180e000414a00040f02c8244000d40c81c2c0d86425280c50144c12042410591230390007020104e1a400100d00f204d43c590600140702c1440d05c80700009440204c5074060954000344034400102c3d402003807510340c0102c646030008164040900150007810260000303405148007140c0710040002d003042956400543c003c541800760f030303020100700102481c1d008402c1c050805001c07201510203d0b07005950410300500603242400d1030003001c079480d41040d9000103050341c80c0c00880110401709010050b00c03d1426100b01e1180c44c0c3d440c0c0c010307580700000341035441010350340c3c2c480c0b50b000b1141c070a040382049001041c140044501041e45941d03404143c43c80b1600c0d25181ea54001c40340c804241c1a004140400360041c0b01c1da6503410032400c1340d0400840c0f40c0d00030807d18401e18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 488972670 1250 488971420 488971423
    0x12050105071e11010f1a030d0c0b0a0507020a0b01060f0207050418030e03011d0a1e020d020f0d022205010f030203060726040f03080a0504031e05070b0a0b01110c060301180905 77
    0x15501d4841e107036855000c01151b41018904841240c000c420300c02146010300c0441e503041c20320340c0c0c002c1041c0340c046051703110344008038640858440003402d0000c80e40004681c81d40d0024462000030701980c01c503007141c2c1d212002c0000300c0d12103412009885a21028040000b8000c20040f42c0c11a0020000503c08040d00d512880401014612107402c0d00410205420440214048071b07003841c00f82240f80f0440440d41c0420034039070389100d001c1d02c01d03200c0008240066640c2990000744070b0303029101861f02030402c840442d02c03c43d9286d240075600c2c01c0c0400410109c12030b01c0484116030f0018014a001d441b6400c090b03c140c40309890794100c11007121002c205400074090b145d4001d600c200d8113034207908000d08000f08500005065030556a00301001d000119504c19400c2d01007129100d0101281c0ca40c0c82c6d030558080c4a2048001c0948641d03604000c403100c020360100002000c2a00d0343c814868903017407060303101c948980c0d00d907034480014001030145410b0100d08421300100c0c10000a0004820307110a03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 488973920 1250 488972670 488972681
    0x1909051305010506100f1214070c0c0e130b04060e12040504060618060509010504080d0806150903120912010f062405031906081621050a02100507020a12050105071e11010f 75
    0x31404034105000c1002085000d0bc40b000082540122144850800700f050740c0e501d01034110040c040320b5451000c02c2c14040c60b40e20130f00c0340e0301200c0c04a0f03950300c43c8410f52080540142c4100c910070361802e40c00068840c00385c403c5450040c0b000c480340071898180701060310a9044401903e04018045c0800f040c00c0000308600d240d15401d6442e0002c152400070304201050741e800c0342c1006129400c1c0220785450310700003503800344007424102c4540c0f2003400b20702050902190300080c2601d5801c200196125050b2a0f2021003030b502112540c00c0886408001100400d11114400380058401c2000900c94002110403000c2040741c0200850b03010351741c0c0410391030541400140e801192001d5010403043d91900041d249105ea102b510081c54066900c8103901d582450384040d00503104000c071018143d00c103104603502c180c0c2c010070030440540c4070803007e0211084200112143c1d0329280c045080f281c042c0d01890400a49440404e80b2070340e501c081181c2c503540c0d95900d03401964032038080300710300d41d0a401030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 488975170 1250 488973920 488973931
    0x1d071a1e1303060606050421060f1d06090105040206071226070f0306050a06030207170f071407030b0402010f140c0f011413021909051305010506100f1214 68
    0x1c4004490450a00000703c8200780e000e4020702404000030001600224251098040668101010420641012000380c5450130308042105d190038400c99150804000c3d40d03100754084022254a56038161100d0300700c4e002135401035448401400540001086038400003402101c40c545100710481031003061900140040003820f200244108008075958400b080f031828128074903040c4a90340c41c01e03001c5000007209010b51070170560000745030000e200d140640007002a0110b48031640c0c4d8150100d0a1a590b0030085044542e29103030501072203151400614903050303c7c0c02030742d100003d44681c0c0c01074403840803540b044801c0c050307801900841395900f54050141945860050700402080d0461542118000060031005004400030311205c03540360f0014005031603054603c4140d100000255032254000c61788031411490805c01040804442e04101011240c0700700024004d40c6c41c4c850800c480c11711840706d00030006108010300504940b00300c82c2c04018005440c0d001030302242141a124190100312072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 488976420 1250 488975170 488975197
    0xc0409030f02010b01090e071d0a08030c060a0b10050912010c02070f060810052b06020702090606092b0203060c04050901080f0316020a0b0d1d071a1e 66
    0x14049070706030280101d4010343c400740b8080081c01c3c1080c1a600000801030a45020804034500708291101d00a00802142c071004141780d64803544d500060b070340c036808404e02c207080c0d00a600100b0040640390050b5040460000c1c0400010500c2c41c40440e542d4000c1c0300703010780c401c09002480c0c0200100b07100e21034018001c0d5014000d0340d41800703410580f10009500840402ca40e400030462124175484151095500407908030300301c19603940c1842904a80c502c1d00c0c4000b513818101c000c0800282d80d004100d503503c00d8500050503902d10003002424010840003e0304610701248500014600d8511819a8076850301c41646d16149034000c00d25295044692100b0000005818001454907d04960051106400a2a04200043c92142c50780030350419001c82c1a800f030b02c00011541c400f202c0c1c83c0501509656a600c9101c868225805403100002c201d111140c020b5140244800100f9400280c45e1041860652041c8101c4c606100340e01907a041a901100c0305c46c071b00807052038140181000c008510 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 488977670 1250 488976420 488976437
    0x313142e020403151b181a0408070e01090b0f03030d05190914010f0501061e052715030601020705090c0c0105090a15091208040c05120106030501060b120105120c040903 74
    0x70440324210340d0043c858000d0000c09004007408644001424051f01c40c104e00e102210403d001c141d610a003e00d0b003090259026481001c541c1c007180946050480d103003017000340142e9800d2414000f08240c81014582c240c4c0041002281d0607841d5080035420480211000c1d04004030101103500300e513086030f03045030441040b000098002900b40101072505e011a041007009525042d00074214145000440c0b0506801c104ac4032000e901034404e54100052111606580c2030f0a03804c0201d241203101e0b59544500704181010542c1e901c8002038038452107040e0010304c070b103901346000c1080010000302940c02c0d8440030000f814100d0360138080c0034000d0080a0041103103140a1401d0714004200c0c0c1c0c511a0218681240e02c804030300500004082110241810743c6030b9200d40c1026500701a864000b103411a40301901c0e80000d000541c000c0d021030b805503000300a503035200c03000d052152154451407201343d10201e0050029150070841d16803445014001c4800d002100781c04102550800901a1302103134215 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 488978920 1250 488977670 488977691
    0x20d09050c09010503030421060212090f0f0705011b080a0206040311061e070201020d09050c12070f051c12030203041a06030604060b030a080313142e02040315 70
    0xc0219414089040b07a030340d00998108404030303507640268840d44044154a0b401c107502c0c0f0509001110129801000a65880d1107540100c140c00505a90780382441c461204048800c1c6008a0040c02c03131030080e80680314a910b0034004480c4041460000107404c11400c214000040d10a401031070741d80156005000e41c0d24117810042c04a085556801e001d98002c01d0400c4031120660310002c0900140003454101510741000483c02405a40040c004807440c102901b010b22000207a00d0003014030448104d8418240c80100c01c0e2903100d613110f115800e8010100522803071070014038040c14068052402024403107241c8583c6000c0c00c40c032a50741c021039030020500c001d000788481011031024030484440c0c00f40c103118010075078a10300100007800e06a075a42c0925115601031014841080e00208020f489040c01c4034070200d0f24101080458000c814000d205a681002107a281000300101403c8600202c0c0d00a1504c0e0700100e000a0620495003084048005000071594036175482002d200040c800c00d15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 488980170 1250 488978920 488978923
    0x21b1f05092b11030f04060c0f05011e0b010201020901020a020904020324010303180308120c0f07050f0c09010b0427020d0213061b080d0f1e0c05030c0703081801020d0905 75
    0x3010312600f070360b0070802680d060044201c0850f0102d072054a00000c5904550a0061080100150003440c0707500b00740d03a20b0700e100c007422050b9910300c0e0307002d604000d02031040005a08034414903404501580002c2c401801514201c41e0712640300e40060150b99a40c0580000c20361562135102d07040071551241c030018818182d200040303c00030710943c0c828202d018219122208140200c0aa07803030b02141c070300002a483c801d03502c250352070301c103007251429102d00741c510b0300a440c0d040e4996559594842e02e0303282071552420348400f130f04881403885000e04d03040c03c20002d85502c45002c0d9131402e1503004400751000e150325610051800701a1100016101c08041e001c01c144a001c96010302c0412120002403000041c05800100075541d00c13039991a5a601c0420a0704094408540045c3c6a28540001c0c45404621602d200e949010405810420a019000240e805005c140e4550f02e50443c00c0c02030030000380c000e90300560070001030020700028031075182215080e45e102c0803027070641640390310300c038010444d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 488981420 1250 488980170 488980187
    0x6040c060f0305010b030c031009020d0b01031a0603040f050102041e03021305060306060d0c0f0906030c06050307021002031503060406022a1005060121021b1f05092b 73
    0x1903902e0107011651514000f141103010140515a00700400800f144034036401c0c00b450001091420800e644840402e40110010140408041d01007410180190040020303a1640c2001a600820460550b03c60303446e100702000c0c1e2103008a44540d8200000300d015903c5003881800541c0405840320700d1400c610610a09280309201c4c1100503003400c0030b20100707a50200e80759500207000e031094681e195650800300c01c1301d80707503901084841981d9000841c0d40092a0046425a8050b6000c2080181d480c42c085506200c2120300800507003041203016420f5045400858000005000d200303400741c0d060700081d040079401e40d0200c403017a030700040c02010030080b42c505400d1414441c018081d031000c1c07203002c551926185c4103800c2402c0c2e07039000088c14036809260301404070a21040d800445400e1b805602d40203602142001c1c0c000b0302c500d00c0101588400107101d04011721707810f0700244540b0074002d81c1409820040d0448040c1c2c000c0100c00c140074050100e41070003a91307107a0000c05100c5501c0d91701400c444d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 488982670 1250 488981420 488981447
    0x180801020408060601030f150b2d0a0e060304051f0207020405250e0105030105122503030206060f0d060e10090f060b0f030604140102090402040e09010b06040f030f080c06040c06 78
    0x181007405d12024804404035250841b04414240c96588ae40044220705030108a41d900b507410110046442606000c10080e02400b103a0340c5807000740714825400c008450104441c01445c941c8910001618826030405071105006800c0e805800c1044503400501079a03c120344981c0010003008190031040d0030504440e01d405c2c880c0c00c1c8425200d1500000800740c5c407050203104d001c3c1a0f003840c06818218100410007034882e10181e040640304007201c503201c1807202c070310081d0700501c0303014003282440c600312402940c1510001c0148140000d00d60707130000a841701220090890260043e00c11031502c0902a00038138034416400220711048510b0039008692031341d40c0c020300540c144043c8001c01c2d200011300c10f400542000901090041101d00ca50191055080340b80d0010700220740061030045d0441d849020703130000c0e402071040c4c00c811024070110340680d06c1000b400c2908142c0400200c1d48800d13062a849000c1c0510f0b5181c01800791602d8605402540e04861001503110300300320b038640c800142c403240c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 488983920 1250 488982670 488982701
    0x70c0204060e07120504140f06010306050703020a0e01030911090a0618110f0d0605060d0606030b03010b130c090e2d070c0201080c071a060415031218080102040806060103 75
    0x14100340350003c00450709641c0740722104c1d541d0320109050240601041400903051821180c02c10029001140c49210071b1000b155a01c2c103048c0410061070184c000d0750f080e0902a6513040134100d494004402521850390140c50982d083c03c42000152202d0541a210300003081e00447e1003450700c10018911290058681d410500e0301d442038010590540858209069400b00c0a4a8480059003c2c0060020b03500c0302e9484503000440e80300f42c00168002000b212038a4404002d6016140300341b50a945a8003201030307020306a1031004c2c52482c0551301000c2510400d20f001140313541c4460301a084100c013a2406040600403d10480c5c0a002d40004010f6241540524190700d003042c0001510240c400c40c0003c5c1402022000030b82c400021009440e2102c4d006030404131405070254207440c081c101510820300990a00010350380343c964107240582101e901c4a503100180000810898503840050b00011a03603c1080c0001811031003400680003512241d0301401031414803000240882e45100f031a100b44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 488985170 1250 488983920 488983949
    0x1050a15080c030a23030c0d030501060c0506011a1303060e01151a0307030221010509010b090312160512030f31050f0304030b0f07091511030d0203070c020406 70
    0x16071000300da1801c41c6644017110b403110101d140d03541c1840b41c907041c10506003840042243c800382e0070000b841c454681644d072070800c943c0c0d817200e4046544014854001d030955000500400c00c0303280e0400359040c0b0350014103e0030701b030001e6074416480c07000343c0da4025103145031140025400003c2c2803107860740801da2104480e0b52946051414540d03440301080d2900e00200100008003c2d03806501100e00c504071000c400f80d80a02d081d9100015200280503103405988600c002042c4070b140358084800d40103000700180500380954581d52002da0240c4c0c0079140da14444100800007404c00c212074290078a003008519141d24189031400c032402c2c0020b21319040d154030b012840c00350490b0b4a0000034000071920031445580042d080c420314108100035800800c6c0700000e0f0000c05c0c001c18001040c024017448100030200d44401c0c60859409180303004084a1580c0f03040b0950060b8080ca91018507200c00c401500d0500c920b019404040780c008807506c501040042e281c042c00c61500f441030001800c0101c84280c407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 488986420 1250 488985170 488985193
    0x705012a05070819120f02041d1302030a0302030d0506010306030317040c17160503030a0e09100f0f24080c0a030213291204111201050a1508 62
    0x1689500c024880140040025144240100d4904441080e410705205540d15440c0c0c04008103075072500e802c26142c0724507040c04e400741445140219800ca502162003054004a172564030629260b001c0d01022101015142040061320b0502000c01851300035000785480315a004400010f031980100081d04149c588032081c00040d0308018490300c05400d19903802d2031903490b880d10354801d4015412400c04802c100c40c0e40d00c04084005400340d11600c861458004440e41e500034956280078031807621003c9640300010413000d0800c81001d80c0c3c88040465950340d80b507501c24882c8090f601c81d810400b02c80d0040e910171303c0300d000105212021030140315089144800d03406801041051b016003950103510001443c1d6544502c83d0301540e001640420201210982e14100d251080304040c0c040704161050030b101802c4640e440741a985041c194520121055503907a403280c4034480c1203054541d00440c900080f01d0011400d00c10b451045c2070710140012500307046103540c0300c5211039902c1000c003a44602b210b2070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 488987670 1250 488986420 488986481
    0x90108190f08090910060207050f061206031e0303060405070f120e0c13050105090606030907050f0d0f0506060f03010c02250b03040501240b0304110123070501 70
    0x200c290040440e050942052502d49000d1003210f1a040d80071034060240a0810b000703059800484819800f1240040e90310428400d500c2c20800410341e103e0000d10010101c6010304408075482f03540207041e10030002841124440c0740c1e072900584091a4000f10070000141000d01c0b800d034000b099414101110600385c807000344241034091007091883d4448100d99400e030001c21801d07003001d10080003007442000c802503100042c40d0074070407544107000144c00b2a04074103001d4100c9001d0700043c40504002d6040c00c0c180309403a01a03400d080e422030b40422166000c9120301031807022041c81400035051606001c03042000c0b81c0105a6101d2003645052070480110b90001004540111090700400f079124002100c02c082801e00da002d03000300c2c00b0000802013000010352104203001038000692a411415900c460100c0c2072074040d901c009030007000450003090b801c404898a89005240c0441c1c3c036000182c046040002050b113600b900c4001094850400c0b60030b000d54840428444c100d0701e4031480611010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 488988920 1250 488987670 488987713
    0x7080c12030114010c0818240309010c08040c09091514040606061d120c220609110304030813140f190c2903100611010b01050a110c03060411090108 65
    0x448807c40c50f01d050b040152104d410007079040020303129240340e42c0502010086c15600403200102c040d443c0420b036101844c000c0788440c0c007030b0341c000200860050605030003800400c240328065a40380b000071558400e40809003e88842241d242001408605091030408191071044c1c01640c117000d044082c102d8901c0425113100712540c81281c00000c0308007081141810042c0851005801c5410f403030061106010192030322464912450003007146944d02c01c0754404a80c044403500c02071090800c08100440d1048070540d0700202c980f01c2100d010f56141c0e0303840040d11943d4841220700c2d0440c4c85c005002070028070021101d550040760401c0300745020b540d20b0f420741c00c01d80114420112400703e00b110305511090144944034014000350380e05d042c80c000380c2c61018081e20802c40080d03c0174030214400380e010b000f044102101038440310f0400485030740a5890b04001c1001142c548038054442401d0b503001c1112a014500468681d40e80003d0b06d01031018191050300030038442c0d0310222040b880d00300894883c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 488990170 1250 488988920 488988937
    0x40b0403020f0315160c060903030203060907090501080414160f0504060b0f030c03040f12030b0906040207030905060d0b03061003020109081f020304080c1b19180207080c12030114010c08 82
    0x100d51805e200c4202030701d03154001d500142880349459101020160180c1c01140030f440f00f1a1a040e4550b603480040700c1d10000c50080c140080d01000c00304002510340f1528a00303e200450a170b880b03003209201c0c03803030f040301da158081860140e0594040180b810144580703006000c0e0118042d01d406080c108014181c80f000c1c04074802200c0000c0000c00f4880702c100d4015243d0703802801701171104100c11009001c0d00981222501c580c103100041210780c6402e100f04ca2000398191519214a0318080403c40a45c205410220100391615181d0390b29035824060a40304181403404422203134118000140700010742e400005280d172042c905100d0200c41d0592484c2c501e20388440c0581e40395100d00d095201401200062103091090a800000d08262881034138030080d4203451040020682d1a4070100b0381c00c0ca4482e81490410051110545c800c0640080807298020f20400c0c2ca03006032108500d1a001c01c0c1803803424544000310052050203141d080151115009203000c1e50a8210360721032008a225a240e07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 488991420 1250 488990170 488990191
    0x40308070b07030204240f210b220e070f03031d04021e030a051f030b180601060c060c03020a05030f100b0406032406021c0201060b040b0403020f0315 66
    0x10318001d100c1c4d0101c601034103080349003901c03d64000303900a2646541c0918180462030140d40c031114503200b00d211b03c01072170a1700c7c85038000304911034100000340003044001e40c003c580074401d020300081c50f014040320003882000020311000001142c13800c00145801c803006482d8401c008102180d4455030b102c00075040c2c044131940d005d05100c00100244240464800034134044042c01c0080d50284010b1445a44104024401c6540b081203001481c1001240c004012a6104061010410070361a0a5101c244040c610f1000007060f5426072604000340e015000140c4403400078010811039005030f00040c4d08500f019424070300c030544080c2036800001c01d515150f07a02c500001300c58024500203d0002d02505540640d926240c80005001d4241d00241d03002007100450328280c50345030a0308460031916250702a14002c6208580009904089080d8000319903ea90340070500d032800100500040c03942e0340b1b89507a00c07860b51052210a00700c08451510076004086a810043c41d800c1e08594000322480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 488992670 1250 488991420 488991443
    0x60702031e070f0f06051b03070c0201030209090a151203051602061204060606091409010506030c13061e031b0f031820120a06020307110a0c14030304030807 69
    0x540c29201d41c05103050251800014444007801d00c8410b54039090300900640c0244503554403a54686202d0380c00740c2180c10300b40313020000240c06911641d104d8114a01c140350140c503104402001403906038050751105082c0e03039140b55901c401103804100200400030100707901c0c0311000d00d803006050f600400d180304900807000303081d00003103688400880d0003400e0030940e103000c2d900705410880010b19803030042d4400b059441b10007140c517940b1100c2d20360700c130140240502d01b2a8207160501c034039504040c02146007014140001c105c5104054080409002c2643d50040500300241c44260a280e082c0785807000d15182c45040e4485000165091014855908010f460f00500540032401808004034801ca0f450000488904009540038203d41c01c1001821140c15800c44c42c0c10001d040300780044c0c0107566842a2041030000b18a40c010359030050050078070391442c4080c1102a03080030a0405c0885da0000511018400380b602140c12180c080300540c01142001d04640c1e55038001d102e0b070a8050503e5000300d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 488993920 1250 488992670 488992717
    0xd030807030510090509060f0603010b031903050403050a0302060919020f0d05030d060b0c0706020606420a08010905011a1e0a050a09050301050606042c0c0705010e06070203 76
    0x1a102c00002c008001382084603240c2104500e407544400d913171380086001040e0104000e45014002c082102800401030140040070000c003810f14000c45404070280034003404000049041800f03225a0240130b50090022481c003148000c0c00c20901056400160151304203050141c2c8440e140101010000c1e0381e9803400ca210703030801601d103018000e50381110074244a00800c00b000020003030700102114008452407107444000903a2038500803604207800502440c40400004600b0030000b128200203c120150381900ea9100002c0d03808142c11201c0400000a101d40340300d47c482c0d1135500405040408110302c0d41010101800c0442021b18484150000b00e14000303003da07019521180f00f00030746c2c02141c0d90685504090403607089442c0403404140b0740c0c580000e80d800c0c1030040ca881031000400540c5024100600c0001c00c2504898100641940c049074100c0c804011303403100c1c003503002e188400c0e0f118440c500d0094250340030342a807401c190f0401030610201e10307000070507100b003e080c0d03545c1008020500c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 488995170 1250 488993920 488993941
    0x8040b0403080406140a060f09020408190c0510081806100603020d0e0f060103150b0d20030114390c0f120721021b0a0b190207050d0308070305 63
    0x4245410001643c20a000e1640d0847e0300000440d00148081d00e4000c0c5d6800d00c0c801240114495019941c0064003048a56001c45a02100b41c0d4402c9804c440069112000304021000b20324a85000c43c40d011709211112583c8000c403101c03c48940f0042c00316242c445860b10080141e44100c2c000d0580204803041010207a8000764414003e079021128040c41024405a03612802c0c40151240109144000006507003801a10611200500b1480c44001a07942d80b82d4030079809801d0f410461000c0c003c6811a581c01e0203824405c070300760702180d11035042042903001000d207001401082400311a40038440422a451000c80882c4080c510360b0703e03000b905821908112b60003860800398025080100140f403440380140c4070040c00b5606501c213400d425948091141d2103160008007591004003031001840d1400c501e011803d030003500d100c200c160b485011045940141124402142e0080380c0e650640c1d6040019500414088619000d1040c07240c5003d0805140170b014101050307220400108070640 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 488996420 1250 488995170 488995181
    0x1c050c0907032306010807021504020613081603031209110f04060e090f06070e0d0f03020f01020c0a0b070905061b0316060e0114090d360e0708040b0403080406 70
    0x604080720b0b440306241440703140400c204135141404034281002040103207100044501100003480b10143d1300ea1141d80070003900390403803040c1c101c0341c0c0105a404120030509110211651002c22029074820307003103140c0540803500880506001c0c51602c010400451592a00945520030560705402c0c41c0302c0030b00200703000d0700864100c010f4400000091080303c200014505400300d005900f03542107600c5612040307a46403207000031998007804101014000c9010602078100f414400d00444d48880c0d000319a042c00c0e604201004c6495800c840a0704003807004445140743c1c0000680f51000720542410005a054000c05102d0140d811010107020b161800c10422689480c140f01d0311190486800c0c80c0000141040782d03080e0030a5401c005240c0000c40005078200d01918030700b0080d2507605881e03901180d800d12184040d00c0d59065604061010a1251840b0104031101c40303403900c5403a040460b098030404002d080f00341000b501c1c408000c00b1541c40104203402603031624244003552100d06020313001e0b0a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 488997670 1250 488996420 488996441
    0x20010207020406080601060801050a050a0b0a0201060305010c0e0102070e01060503010308160519021905010503060625050114010b18090a0f060b1902121207090803030c03061c050c090703 82
    0x1c3c40c0c900301080302e07800010418100d0785e44e55030390f0300540c0e2104240107100e40144262500b0820103134042c8080c5409402502c42407a20f03100004849030b40341c07201801d4440d0703842c0840c0800d5110142e1082c80d40d0600400c1d0140102c07000407a0329501d44000100184414030005d40400e8022a81d04500104078844004058000084035000c20000c0109480440d03414001c030b203d00b112200c0d00b8002040c410580b0102d40050310380c10b0441d03403004d003030081a511100c41032485107099485484a10041d400c0190074a0140c03000054080281910030243c28040c0c1203800003d01c01d20062040380c3c610703141c4691107241603d8440464441480c060301402a01c42107884c01420184c01048070301c0f060014040440002d011404890700132441a40c503056020707100040c1100030020f82c00d0b04414a070441d9001541072400098080c0ea8620700c40c11500242c4250b00881000418845949004030304008205203000801d8002c1c482650340e160b56500c0340386031901954103507000403070720740c020f500c800c0968 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 488998920 1250 488997670 488997679
    0x305060a050a1a0f0103020d0f053111190509071e05130e0601020f06040606230108040b10051005070203150906040609020607140a021201020a2001020702 68
    0x14100980ca5902404044a80640d50751810341c140e0b449000403251000f4046010700400110346510004501950069206000940d01e405042d490380209101c0d8034460081e1004040c2c800303901145001030040001c030500f000558500300800070603480b01441084100440740140310503010120403451424550000c1d0b800303401c030010030080c25040314810441444915803a0790700e0110060a588501a500e40030301d03200d4150300c05001c041400f6803426084401401200d0b0407200c1210320904d81541107408681c016181d8204101a480314041c011a10644441c00c0a2582d94080001d00c00a001131014140e0f03210031001c03940e101050b0f80ca504c054800034040d62002103c00c40082c1ca01c2d40182e10880c0641f141c840030440e006039011001c3d000b15074507806000e00761500d403505405800c0405082e64032413410020440000c1000603900d002c160a0720160600603000d004200c21100d00110101c500d900401c40c0801240d8080c0a0100442d10118980c5400120a10150080c010030b50000e400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 489000170 1250 488998920 488998933
    0x1b0f0d1407080702070b0a020c060f0706021b120403080d1a03062403070b04030201050c01110d0501080613020901050111070801020309010e0609070b160602160804050f0103020c06010308070c0305 86
    0x5642c0c0c007a25452264280781c0813224221381c0c0364000d190038800d200201e00107800c010300084403498a21300500406540c0c1f0802400c013090340d00d900080740c0c00400d05148010021560250400040c0518200d14407200304d014107080c03450300c424201d44180d018185600355655092803200c0d003c801e80210122010b422034005140104a14000d00300c095482041c164040326480d00c98500000c01c042510540b614444c101851603005456517040207012078407030754890000c2e04120024034041c1c076407000c01d05804105035140c00c1c203040c280040509440c1000c0c03071465000000d40c880300c3c01d150454034207280c060042200c1c00d071040d05043c1260400c5825500020600017065015000440b0307200380345043d10b5550300e548a40c00d50b00c4586108000c030400707062190f0007000403803200e146c0042e8023030303c0003524110100d0a42121004071160407154040041004c0c00b40382040015001c8404c0301f82021072510f40d401c01001d65806051000801860740014400200b11940080b4001558007804403501c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 489001420 1250 489000170 489000181
    0x120f06040305030604200417070b1908010b090916110a0804030212150c0f0903011508010f1e0b2e0f0903030e01081512151b0f0d14 58
    0x1003030b403095130b00c03e00c039604140c0c107510030281d00c1e8900b20482d089017801610742841c08a100f000121510414950741c01441400240c0c0580c0300010302901c1800b640400c003402800f40d02418403681a00190007150307082c0070380300c1e00b07072152141640c000b60a00a004e408440c43d1401b122012030407001040d41e800781a00d01d2003088101c401500542e4030032100142d11200603461a50f03a40433803030755030750f121b2000804aa001181c5600a004141078a10340d00d2030403030311502007801e6071225488400803412140381045811000e10800c0c00641200406026021104000d82a54080601160342080e070360b0705d60580310340d6090702c608209540c011001a1360020038900c02d1603c0c0c41040c1500c0412030f410310707410120f40705043d03800039030750305032559102401903400440701134100800d40700c0980c0107800d1000403655201d459800b400981b0000b80481071880542c0000034001402e045080d0800709401c03220508200191404101c15070b0324561148400074201000d403001d003581c0240306140e40244007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 489002670 1250 489001420 489001427
    0x5010b0c1f1e1a040b0108161b0b0703051605040504051003020a030f03170c0d15180e1b0906060703050717030402010206060d0c05102105060102071e05120f060403 72
    0x81d850010740501c0c10f200c0303402d0041c082030300d404001c2140028900030000f10039818203089145050801e161603850101880c85a010351160a2429a51807400e002000b003901d500d0700805901112072070058100620341e075000340040c0141d0103400d22568542c00052300d6119000c448034025078004018110f480d07079a0900712102841c100301940050a1038106007255001c00b80c41c2e40c01a030f681c5880900d002844101c11005042030349005440c00401440040c208444400e10500501101000a0322000882d0114a04182070030050f80e01107040852660a960721910b455111405a4800e56221641c0c901215a4400c24900403c400c0c003040303d40c841d080c070220146120300e00c00e8080301d07042e0b15400200040f01d20900402011120840000e104a0900a50584603045d447c101200d03161760310b400303c0040011580041000d20740c0c03441044815030b810061500201200030000c408417410009034aa0540c2c14024107000c3c4031204810f1001d80c40804c4880400d502540584940e0f041a00d0001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 489003920 1250 489002670 489002681
    0xe01120f0504081c092d020306091c09030503030106050f071b0927080a05090a09050f0601080106021b010c060c030507030e070803043b06030105010b0c1f1e 69
    0x7460030b1900f0740d810f4049015500c22035004540203048a4084103a4150081b59410382400440104000e100c540c401a10100090b5000d14a00000383c05900058020b90440030b10402c446001c018803071400304042103020007280d0540c4d03000d01d810b03680c1c0c3c42003000401c9907100d0403000800459000403a04c0c00460484024000e94194140a00013140080341d04003100e503103d11a80b960303005d81e0300d0fa9000103542c0d1000340b00e418260709155081828002c00600d40c3d1340c1541c01401c4a640b60b204001c82e5940c1c041109074000c1c42406e00003025410001700958901200d000d2200801400c1d1748030345268040c0d52040160344d4052018400e44115100c02030250a080d146600828289144d008006c200400c404041c0c407200c0f802075042502c5d108030102c00038841501c11030402c010010a02140130f00c2c1d2020030075000e0407182344086061020606084440507401101124801d01125403407100118021042822403100e0955840031010410024103214a40030900d403280d02170b82d403500d040c54021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 489005170 1250 489003920 489003937
    0x181e03030506100e0d1506030f120f0507030e06070b010801020903010f0e0a0602030c07061523101101140a090c0905041106180a1d1302010e01120f050408 68
    0x180710603200d202c140815480e28905141c04903a8920b01c03002c071420004429003a60b402584480010b0340301c101c010080b01e4142c0c2042e01c0703400c0c01515100c1440f0712081000341c00ca400303151a110348550b14000900c28041c41500400b000b110070580134060ba0b44009990350142c110610703200ba560b4415906000350b110000840c00380d4240b10140c00c1d95181441924041c2c07031440c0c0644001e5440d955180025071005102c90b020b50024860b02000c1240c61040302292a410010400c8403401c1c13141503043c0b02040e001e0008640740680c0c03c02e01da601d958145030381c06042802c001401d0034643c58428013601c2680103011120b0054020041c0b0b0101c23940122420500694011410f60f4843d2040380907203400b100e0141c8501020a903440700e0381410340090400c281602d2400d14001c101c0340004443d120640c1c010304002c1c61307a05214003000246002c59030801c0ca040e40d0351501c1c2d455580060881080c001201d818000c07258a042880703080d41e000120a411540c1d41005a4034040c80c100c0c0f030581006a2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 489006420 1250 489005170 489005177
    0x304020d0606051503070f0c081b070f092c1c0e09040507140114090f0a090203010b030708010902161502090406080304081c0816051606270b0a181e03 66
    0x100c0e2187d030080e01520300345a007003020340b440c2c05c500405c1d500050282c0e031424011485500c0c0005940d281c1c44400d0030250038982000324990304401081080000c0006000c5442285031100f50000307500010720742031000d08095090f480c1054010b00743e07203059034250025004141141007100b042004904d410503960303070899001c2282c40f06001101d6116003441059890801005140c10600c0c02d000c1303800421100404001c40d107915000321000b42c3e0002c2e4880782c0c01100c04005c2c8006a60050300c02800f41001d9281141400700f140003041501e005108068000c02004003110b4030510507804444d01d9840140090202035500c903040e566036400742c0300e602c200d402080c00f180554858000c1400701131034165500c410b15104c0541d8010403128a51100091190800c410501407200f600c0c2c0d0015a0302070b040010b01c001428800b440708882c12500d015131007840c1c0c07a561000800311280113801c460315000c00640c041d01c04c00d00c58204d4404086c0a03010081040302407000300d02034044034402034800d43e17 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 489007670 1250 489006420 489006437
    0x10309020d1a24030721050f01020306100c080d1508030f030108010e0c09071202210403030b01080912091203040e19051314010615110c0f060304020d060605150307 72
    0x8a05000010000110f203605400042040001c000071201c03003144081c24a0a809091005030b440c2860041454a0742e9016500070040000910f481110000007545605201c6144000e56850014074401c07092980d4031a0741d20001c2e10070380c08103540a40040d00440b4200c80d9103803101e003410740c0f0940003403203212120360911038641519a004625040c0114025000c03202a444101d0180c944a50701d12071591300640c24490b41407501c0e0080b40503080d80014511210b81410a4200101036640e9020803a05101c030f24424003406403400a01d03103806404240403d030f00c84070140e000030144081d41c560482103100119000c5403015100882a02400c540c0c40200c0c0100b8510611809030340003200c210220b0290001c150000c0748543c01003080c18184040001202600c1d411345a51061210b601000000e00340d01160728404401c02c44103c3e5680d048901c11b0a400c4100f002940c1d030f101c0180020300401e584001c0301c08000342904003401411000b4040d0405221403410210960001c41c0c51100207822032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 489008920 1250 489007670 489007711
    0x1021804110f0703122702090711120c030d0f0203071b0203150603100c050915130b090111101a090621070314010212180705010309020d1a 61
    0xd801c4855020308002c000e41818415203040c0c6a4004c0c9100c120060354507200140c081015030003448059461500400b5000000d84c0140708114000070904418041900c1ca00c0c1030540d80001e80103000b03080079466a96030313910b41c00103509600916141180342814103450b4030100501d500918841c00741651043c40b0400042c43d1602c41d1554418065015005400744500c0c02004c0304071183d1000c4060f080351481d44401036040e04071154010741c00005940030400364100d28040f00c030307120b0005400c0b440504100c011003c0c1e80c442481c51140e08070421000888c0d00e050303405411030b82544462101914022a894018080900100c01c50440794400c010007103221441c105c00114055140641281140c00d0361612020004002e03050707400180c4658040000064040565100081d078848009a01e507505140356195000005d404200d1008845440c1d002000c00050b018080b90403d2034003050032501ca00100b0404820208007500b503003612805a030391000d820a0700c81c00b0b03540010b18600c3e07602a1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 489010170 1250 489008920 489008951
    0x1b030717100b0315070318020603071d0d1e170a1101110406051606061205160e0708070f030b130b090708060a0b030402030c090f0708090307021003020a030e01021804 73
    0x29180c0000c4c07088200c001044d506403180e4002d00c410794940c02c140581e061107800040c03098008503a0080014080051425006054000c03042e6a141c242c5001346030900b03650b1480840031030403070310000e11103d09662405020850780c41010104510484581d1900740318401044072505217a40e015075820b021300000301c1141c01c0200d43c200c403802c1e620310303040100106d80c600d40f900e4184819280182c4581c2c000c5511000d00c80000036282c420401000a21181b030754000141d401940f1001101145008025582e07800191481e84001d03c0e10780510003925001013a4024a100d407221500071048640000003a1625445a10610002c540940450f52848000c41d8030382012196a900040c103100108204240c240286410602c01025508410341e541d02060300d2403070480c2e80c801f2400c643c1051142c0b071500243c1864104094030041c43c40c081050300881c00c03102110911108055001071004849840b0740c6c032007800e420040c0001d660316842d00301385420429102ea4064822450082c030782400421 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 489011420 1250 489010170 489010183
    0x30c05150306100c120e0405010e0105090f0403170f0a0e12160c09020d0b0a09050103170307111e0f01020319110d02030a0204060906020a0201021b030717100b03 71
    0x80d60094510b584000500100c00d80c848620820f03c50010b802200081c0101100d0325442c082d0303660403211307150034010881614010b03030001d540076210f280180801e44482c8156640300c1c00323241810352561610320f81125101c40200901c0303030b2007070314a0134800b844c0c1c05502494007503110540180a04d00b00142801c0d12030340c40101540300f805003002800b20b81030303400c0c4046c03100500a00c0d913001016034400c0030005907031104400c05003c3d0f41d101400c03a010324000c0d0040000e0034100004000315819a41d41c00380025000c0048405144040000743e4094402c3e41c00c000500340d813005542d8440f02c0040c00d103440042c0103000c02c5590056982c0741c1100801482902c1c4076000d007009410200184400401c01450880c002c0c0388000c504004000c0d46048078002035004611000c40165210b240c030340003c1400c1c070075400200454000b10b4458000d41c0e400034030310259030b000b00001911442d0b01400030f454028541d00403031a824095104c444961004151001c82500388101800f2101001d4101034440d48c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 489012670 1250 489011420 489011449
    0x70c091d07170f0f0a0501150b120a0e0d02010902040f0903050d0e15280209091902041a04210803040b070c0c080a02240f0d020f040f030c05 62
    0xd00c842001c010003a02c00c140024035090100035100640c54403000241008841d10741c0003410750120b00f5000c1000024031070120390540c5005043e44441c1010315829003886640c090014040d0b002011030390703100107076000d4520401d00c6800c03030300040c1c0c9060000e8003a04403d0400d03440b43d840c010080d220707140a0b02843c201b03107a050351100d14040141364101b0040c103480341e22500600c500d28106010000d01001180900c0382c2908240340c90030341d886070140206900303c2e07000510740107100500e41a00c800174040c1c1c100c80c00201c168204819050481c000b801039501100d8560341c0d0324030700e400030b01c1504010016a0482101000403c0c2191300c07142c0022006440200a001c0810008000c20100c594960f0441d0700d6140007841910f1076241d500741d0889903041412541c0000c02c00b171086180104400b61300840800c108050302075544141c00e001c0c00f42141c09841c0d09c00000e60b5011b14011581120522451040110340f40e58842444201c820213600080300e080041e2000850310b4074200e052290001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 489013920 1250 489012670 489012673
    0x2b0504110117010b1b2508010c02010b010818010b031204050a050301051b030406060e04080a02010c080105280b0403050703020909010e0a060b130501030308070207050d021302030615070c091d 84
    0x4001c41604100605a03e40c5000e010700460700c034a08401b9000041044c048000c0c10307a0f41080e42132450706800c40d001480c1c50801d6a1400c0d58882c60b90f60070501c156030082051040504000d00071100d0390150451600701c03076050003080405041c15180402074410707200309540c510702d040c2d1902d090600300c0300161070001503c2c2034080b11401040c0c04000031940140304240104100e5546e1243c50030b194410340d41241c440c80c0c04103011410355070911582015040c580340600c0b0b15450302c0003203915100c5140c003600ca114a0b282c8140038a801c600c0800c0010444018007640c0c907552411702c40e07260703601804120311400e95003001ca000180140602c070080200d50001d4480400a642d801000f81340c0d1200303013900001a8444a02401414071031076000714040e0311065010701e41010020301341079442d00110f10900d070710500306026030ac482907500c0c8030340d80d400c034016a03a0b250340c40054940480020000f90541001a2072810404950703035200803241e003201d042c03000b00d164500800704205030190f5201607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 489015170 1250 489013920 489013927
    0xc0c12060c072612060d1101050f0405091e070906050f030a060e1303030b030d09210512130b09222712080108032b0504110117010b 58
    0xaa0400404840d44103042c114146101102e010290325401d45030716071440070100342c1c9080100b080051325440320041300e0b1410600c840c0e40d9807040440c200e0b080a41006400f26070644010a40d004071006417400030b084e1005460100161104a0450313054031181c0440d07030010504140c0a9081e640640c1c09507100c40342032880003c2c003800c49400040c001061a070f2203980c0003898245c0494064000e803190b2507000483c4904c0c0c20060250341d0820901030180c1d02c952403030040d40e40e100f0203030b4003070b9100b140c0c03480d10038410f59841c00049480c40c40d01500502814040414241c0b43c100204040031120005121261381c030302101645000c3c0e84c00c402d82040010031440d41c40301c100e4120500c00010f0100024401d4501d40c3c10013482c3c0d07902413007a0840400341944c00180400300c0d1100e8011001c6d071620a08a41c1403040b910380380e000d40c903031401c54282d20700c10400c3c62400406803030038140c0300c00b82c08000700d1030507003880701600040d20b88060128000f0451400e4120350002014161901c0c00c0c000b41c136 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 489016420 1250 489015170 489015181
    0x307170d03060812070813060c050606010203031302010c06110a080114100504211b14030d09031e0b0403050a180302030d1202120423030408060408031f0602030c0c1206 74
    0x140d200030030441300c06e503040001000381c00014413010041d04455039070314481d81c0c05280040c640780e009010039055500500c1040400001927001c448030300c2d030a1804031186d008514065019001c0b0024018016402194440c00f950788070444034100d61500e6501699400a00180440c0400710111940040c0041005003c03c0e4821510017000074580d0b44881144816a11928050160b03418060b00031a098403041244035500c203102c00b40d08034102c0103028a6489c842002d0700c0c5c4100c13444010880e04112440d507103041c00c51510243d04a07041503005240d4502071500074202d42c044d100b41c1003c1006101038042100780044503605682c0d000d8014174071003070b590b17034252504010300c586803030526003c004100c04101d6001c0381d1030140c2d20035607501c1c6014800400241d560103802003200c1559000b400304110344240010080e4200750040c10f05503883d15540d207c4406401c0300d201c8100d144944c0c00000900f03541c0040148260310410003580c10714201c0804210030035035080c500582c203601c0200031a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 489017670 1250 489016420 489016453
    0x8041d130f08030c0c01110d0b0f0d0210020a05010c0315240809100e01050405060606031b0d020d0510030b010602031c110c0d18140303030f04030e0307170d030608 72
    0x103820003008013031030382002c980b50000b070700707481d86404a00140e000c0498004541701c403a0141140c40d403c1180c20844410b4504049104040340b072402031300c0f40514145034840c0c18000c0c40f54000e025000402448a8408244c4c090040c0071034504483c5082c00b20a000101450007034101785c0f06484001d60703e003440d910240d0889940b00090040340b00c9000780702140c0c05021245c0308003290400c40d90004929031616090040c184240140302500600d41082040108924140d60042c11648462441e407100e10000c1d5a10080c041c8626802a0b6494070301800201c440c0044d02e10102c9208821449942ea00c5020480c2c490180140c11819040b80800001c20603956401007162202c08400c0700b801e0161501c0403a15050fa8224044042283c03000010340700d00c0b00010f030802510440d036103114001c21040c00f00c2c0d0b5920004142c0e08020101402042c1090b216815200c0130010003400c0300e00303071615220b001007442c0d1002c450449520410040c06d01c41c90080c0030300800c880c10103020b040710310507003050314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 489018920 1250 489017670 489017677
    0x1802181e010f200601080706090807030b0c040302060d050f070f02070303081b0a0513060f050304020f040608030f0d0b030f0703120320030103050d031a15040308041d130f08 76
    0x31010311001c00e00c200c60000190000c0e030704283d80030004000130352400130281e0038078140da001032040087d201806d1011520004da1901120b51200800100d40d8a0422040f098007843d04000c0d881000019110041d8140781c00a0740188031070080342003039858035007040e9007022040700c0075400750700010703006c002007409092030a9000c40407640c0c02c0501c8900d40010307000707036000900c4400800c00c08905608200640e10f03400c0d020b440c40703007822917200c1d025000181aa001c000c01c000d00c00e0481d00002038043d11030742c00020003000d09400304ea44500358180c1c400510f400842801090500e4645100341a240020b28801b104111401034400d4500759154080d411540d06100000d05441d5001d080b2481032428002d41c1d0b014450348500d031254150701d0014100b510701c030b81480c209402c010440b050752084118030384c040013049801c44200d5000864070343d5140070703662000d8100840410002581410f52200c2d00529100d00420089a03598082c0c0081c1000000000b414107500c081100d030028001400a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 489020170 1250 489018920 489018947
    0x2151b070c0332030a050711040e1209030115180c053f04150e12300f07080601110d0f031d0a1106041802181e01 50
    0x60503140c0303031a0f0b2a2800081c1d0030f1200441000030280b01002c4610520b0307810414107003803201461400b02004002090b5024001019203840e0004002c809995a15032100f0140c04054055410880c0f070f03412515042c1d0020318455021b94240089498005080301c501c4c4251015186460048108060b01038010a52900c00c0b0050010405c1102c00341300d040e010103102e00070601c10000000d1030020700d1170122848900c0c40b1003480c0131402030100040809861505210407150b0010300ca00030340302d0356441e044121010240b585000105c00302120034200101040799200c800c00f1a00c0e00e030060141c2031000040310242c2c000c3d040e10010601d4248504c2c0a07542080301458522150940d00404a00b42410011b011012071000f01d070801c0500e8150007408441e14030501c25a07180c0b0590b006851f103e490102c402001c40566602090307030340d51004107a80c003400820101d180211040c2021b40001c5d40100c1e0a0403280c2c614242d562210b160120071285d000740e8501030705514800c81c1c00150b400403034070340d070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 489021420 1250 489020170 489020183
    0x70e0a060f0f06140702030604061e0608060a0b060a0516030e12010903030e0d020a0b1b0c061008010207150e0a061e150b120c04080703030e0102151b07 67
    0x640c01680500e03038026003120302c00740b05414075016001d000c6116060b0102031240d02070003c0005640c02003000d40c3d110340c001c04089040c26a0800d5009415504108850724070302c2c241004c900e241f00011b03d1032041d0303400d040800c000c00d035000400500f8015100c0c4400060010088851203150022001c003e0b80d110342410128021454001444d401d4100c0a400e041c0c2c1d507600c03c110905034140501c8041d80e440b003010380400b42c4004802500d41c12030900250034030034003d010451501c110300c1c1c0a2040002083d68a407074000982d90192501015508042170f44480d51000c121401d040c401c5a9000da8410650b0441461600014014080080310002c40d4014480c500c40031804034003032208583c03209907549200040700382e81401187e40700001042d081401a40500182910101b2200209403029142e125940c071101504003522940c1c1082d10700e401101070001c20160000c54400d8581d00c240c007503070140600c4d50054541d090040b01c12603900201d181d00034044d042101c00030042c0134042d25 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 489022670 1250 489021420 489021431
    0x2150d0b040f0f0507032c1e06090d0819090f0209041104140f0a091e081201060e0a05190815060a06020a0305190c140f0c010908070e0a 60
    0x240024112441082040020350701d4510344649072880b071041d1303588246542420040c0d40c0e404581d0b0b1140c1c0d60b41c10110000e0042ca40501c00454504021140003d0300c82e58220b00b88800b103824283d20340c24140d032204641d1040854040c041030003054028812441b4004114195828190400180c9000300040d540c2c0610102d5001c0540c5614022521a0340585016882e05407042c00b4401140c903840401190004900140140c03034a0001a40f9000300c0c580f400440e03c0002801e041511507083c01e4074003203070301200c8101410003800f0005001e10380341000c2c015403540c0c2d031003005458607100ca551203580100020703024092442c12100d6003211412060310030612039242c1503610301e4280c2e64007000081c007501c50200400d130f19041c0280b00203132642c0d10181210080310794010302a806400c4010440c102540002f0b400b6078414044000c0e8a50400105030300d12a070310b105d25840b2004510780301124003c1c00c140380085d5010324041012a40407500928070340e031411030350003450407028020b5002251180b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 489023920 1250 489022670 489022691
    0x60712111c2f010c0f0311180103020f030a09060c0306060c032f06061005040503070b07050c0411030601031a011202070c09020406021501080109030503060d1110090504050c0702150d 80
    0x121080b000c140d000c07400000c0c464070f0014001e400c0d03401148081c1d0402d0304116542d0394a82c40401a1000109a00005ca042d0b0071a0801603000e4081c91b505d00b84d8007000801009045080380c3c00c049070a03401420101f08080385104100d041e1840c0703004920100302030380c034541c1c00207210701c540170f41f4a1404084155840c507498215009040404040c0d0300a902c48802d000451030240701d150071101050804520785480e00010a0f240c000520a42d0325440003c00d48034140f1100b0f20120f00b0020000304204900d004000c82190590425244a40020301d41a146607407040400c0d030385000c01c44140c4a81004e03880c100003040180d4000ca6048405890035080069403228500180000d441c0d1034028001c68502000c1040306044142c0c40000660304201444002c2038100084030b4221805889020000510742086002e00d10490440c640011038100e8542c145a03214600200380d480c00c0302c0500c540e881380880341005004d249400b0b5848001901800a14400d5100078a00070440c4080840c1301a0385 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 489025170 1250 489023920 489023987
    0xb1b070602071a04030b010612150f14040506090c0d0b030111191403040204020c150a0e100902090a091e0303020711030313090506040b060712111c 65
    0x126841240940d1040e9001d102c00c0303c9010081020b54508121581458a10b8035050030081042c81f0305414040300c0c000400744032825030400d03007950620200343c16100750740c4c20380060b07400b040740b00721407a003c0800313007203046840d1a0041c140511001080000142c07503040f80001c450b80888040003200781c1d034001c0c03206152401e0280304114070916400350b8039800303d00784140030405000c02c2c803001c002044000721032902d05035040d241c01c1501502c0041e1141e1034074140c030f4138003508161400c20038058101000400c3c40c0c0f039000308080000e0300040c2d40c43c07590003034072205c03d41d880b980c1e0003503101070082c0001e069010142d000046141c080c08490071005c1c0000500110b40c4100c00b02500020f80018122043c80f4548010790304011094006624002c0d04640c241288c0d0043d007d03000c1c449480e0000300303031996540c6e049146040c0e001032a15a460000780740110304006c0709801440410400c0e180c3c45010300000c6130441702e01c41c28915100c105900004100d0780804100149203400d2010b520202c043c00a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 489026420 1250 489025170 489025183
    0x209070504030f05010e0c01050301080d050d020409050a05010305120c0a02240307030207020319030206070c061d1b01050f030109022508090108100602120309010b03251d010b1b 78
    0xa50001900546c003d00060400117400c2c80745d41401420001002880e60000e010f800c24402850140d0700c41c0440c0380c42c60041d101e554000b041440c2403e0034001081074540c0100e04070ba1145003100c11704d1082c1110a802c600840320840e1054000b00c3ea01005400c000c040c4144081c0c1e8a942d0700d0795055114594981c1f80c0040c0d802e2800a9400f14415007142002c1005009007032200d2910f800000b0280d41c001c3d40d07517000074200c0d41080407104c000c01c200501da81011200c0281400b0a0341200200e051080d83da0364120b8020b000f020880079800307a103500803000c40f0185d0034546e421f549140c1c00e1880c000d01941c400d40300201c011044c0c0c804210008807288000826a12402d1165510301000c400184203280252203980c1001c0c098004000c4035800080c105810025150f00d40d03241e50f01e10308400d006200c00c0c2c3c2125054090360740608004403403143c40420000c291070180c1d03501502c3d41001070064010380c2c50366041e03c400301c1c0140b0a801c840e50213024850b041c201492114170b1210452814400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 489027670 1250 489026420 489026423
    0x5060d020d051f0203060a03140106150c06050c0c120f0c10020405120d0f120b0a060c0b09030a0c11060706060f0504061a04050f03100c080a0f09050a0209070504030f 73
    0x10841410250001543c803000c05410340301032001d508504099000031217107072243c80001e00782000715450800e01d034030070b41004c1e0051090420169100f00d10030b0001e031805090040442c2c0c100d28050019038070312080d606599910396505c1c01040740b18000300007110307640e0000550340c08100090168600880003001a01d00544d004940035894030b180109104500c0741d9440fa41405e6000000308451041d84800450001070842c6045001d550941c60048003c046407581c03690808220310f004501c040d0000c3d1520482071042100d1050f59071008031441e124000d0140d03160015402c40001f001080144209500c1400c00a084528018440d6140c804490b580d80c49626074401200b070400c824170b0300e84038550051082041d8510700c034442d0035a40005e072082c3c0c051039201c0c501020030f81c003003600d080003a280d138501c00030301c1003103001c00f9200c0180190000310741c0518074505040804015610a01030004626406001001c03400d000d42d003000b0303062030024140f404002e0b050100101240044c0340701d10255 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 489028776 1106 489027670 489027673
    0x120c081b070c1202191d040309090504051006050307030206031b1b160b0405090a0c03200408060f01050a06030e19060b10021f05060d020d05 62
    0x3401299409045403800001c0072070320f82220301491840c1c40c000c03111903442c09189804e910340100b01d4041c01040b4010759646110540c0f40c120859007041c4071b0b00f0034052107625030060b001200c404442c1551568800c5c4182a42801948520f2010300020b402030701c929419500800d220784000f8100c00c1580151284020410034008240c41395480c2481d001c0c1c6c0c00015041100750b940601c507004421013030070440c0020341d8022140482d01164405130115803190755038107030180140180d021840915496011031081c0c141d468500d240c062140214a503208c50500707556614104000740205500720440c801408035684509520b0100c440500e4042800003143d0501403e1140c40079442c103c200b401080f82c402c01c13049801c1021070a80680f0054001c2c20800412030b0344525080300c20f000c090506240c160002d000350030050340010040d003014451900b960124142c4405158240c415 = true := by decide +kernel

theorem cover : BRFrame.Cov 488848920 489028776 := by
  have h0 := BRFrame.cov_init 488848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 488848920 ≤ n) (h2 : n < 489028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
