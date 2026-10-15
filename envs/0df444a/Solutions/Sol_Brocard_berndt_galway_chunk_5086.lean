-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5086
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:41:55.660806+00:00
-- url     : https://prove2.me/submissions/12d8f1c3-e7b7-4148-b791-b3a33177e9ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 914568345 ≤ n < 914748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 914569595 1250 914568345 914568349
    0x1803030405060d0204061d030c012712140a05031c0b040614010909050705040918050d050307110601230a030c1d0f0105030a080a091d070f020d1b03020309 68
    0x145480b0620210143e02c481c80c006018191030801c11f2048030400ca030351460225510006881491003200346402104002c02e204e07200c2d955005548084441c150351080407681e0280d950320f0100d6503210b109440e16540c07440080f103840740e40f5000c00401c150000c20402000316009907408004d1480e0303801c000b49200c000c0000a0071200e940c0e101c4402440c042107016103560300146400d00030b05403010240072501c1d111030001d00f80d1095005016a40e5038440214040d190201c412a41c00c43e4000203d44440d0790010000e02290421a0300380700141d803032000d1202c2060003040e642e041b621b881016480204020a85100c074007030b40c04001d9000481a40b000000c124842458001801081c2d01c810440940d1025204002e80052680680c4c110700401042151000a100d12000341c026034990b07100d0031410001ca800c0099540101c031000d84040400c50500c0165560a010b840e1540350440d0403e0202e1050340c803440700321420b2000c2040d00842c04811034a00d0520600c841c0700b48152858501c1d6540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 914570845 1250 914569595 914569597
    0x5120c0405040c060210060303082a040311150a080103141501090b040c0302030c0901050708120c09040507020d0c03200115030b0106230702060c0a0506060f060906180303040506 78
    0x40e0554111a0000f020084150148451002400c0740301040c031403641135403005800a480680003140039010a03080703407580903100521071207161030250482c1d941c0380d4a05098008803455501d40d403140c07602c00058120f50f50068112100141551540b4051f41e2854958910b51020030702c40c0c0005000e40440c0e0075240c0542d849060103003090b81000940010032900f8070040741c040300c0300c41060610400501034152505001e44000d07102c00d00c1c103a41d6072540c03441c00036418010381da020030318001c800e41449422142d40e070181000b480300781c1e400c00180d0360382c0404036500c216800340780001c5080c01340d121002c40d2040f05204d19030704118170360101440e86545400e0843e0001c00540c000242030480c03d000300211b20640da0300404280ca0600245002d80d1600f0061003aa6455440c0c001c8000901408549901d4103591140e4006420349004242e14140181c0f2140101c034010b208100c1c4000768012840c180003500c03c40c04014100d2800d0088002c405080d0800003d02d0359854401440700080564a01c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 914572095 1250 914570845 914570851
    0x50a02130b190608090d050301150903121d0f090a0b031614030d0302040806010b07020a0b07030c060b01051c0209030a0503190f0806130f110c0d110d0905120c0405 72
    0x85141982240380850040c5104000350000e640c2d03420040a1800040d4454288c1c1d0640700030918011103110800025105a0b4131540300070001d611030480302000540000c3d0071061800300c03580d8040091a20300800c0a40e00c00d43c041141d01c100f542c40803448240075a0300c07003803c01c0c1f405000c641d65200039000300381400000b5070154880007a10304007041141400d21044d01002468181035003810308080702d6503120f074414000c8643d84100401c030b10056642d0607006074014860214150b54a07038241c00d00420448a89605907451420000e902c1c0082d4441c9044840600c0003d107030784401c4841d50952030183d400100110340c10720401c1122070100d10140010100c92407010740030740c1584032a101c060705c0f0504444950301806003d40c04c10110342c5132500311820aa0041500150810f0005412802403da228468541100101c0c0a0f100310390005001e40a528007526002d001c50924281941d80d0500300c00000002503140c00c0401050824140301140340c008001507030507424454000c04d044803011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 914573345 1250 914572095 914572129
    0x20090a06031502040510080703020d0615260c070f17030709080c15030a020c011a0a08120f030c04030b041101110a031d04060f0905100b07050a02130b 66
    0x614030030820042007560468003071004080540c10545824009601a4041110340052000710b40c001400607200c3c1d41103850048403010700304011603c5041c2c0500c0300b80d86030700e0383e80802ea514803142d0307610080341d07080364030740c0c02920042400e039640d00001c0a0365049003000311090140518100005450b80802e01e040006242509483c2d180000e001000894a6405061302d60824900c90a00780c55081481e04040700680d1456078984450105c0d000902c580515801554a01804008480f14602902040250441d042c504582d00d03041d8503500c401e002500b9051602c010004088680b040001841c1d0180d40d1a51641c24190b032a01e0301280c003603044904039850449103100800540c0c0141040d246801848014900c4078420703503001d0715080c00300350394600e400217030b5100364415604d0b500540040e1101c000070710306c0d003591880c230000038200985501d82d10460850010414030700f00c0060701d04042c0c00000030507461000e5000c1c040d4a81010300c1003000243c943d502c5050030388802c10510901045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 914574595 1250 914573345 914573351
    0x210e04090821090604020609121504021f08040f030e0d030309060c0c030c0201032d09171903050a150b0703140f0a260c0a020c0f010c20090a 62
    0x3001e41c0088410b1861107440e251500d155080c0310640d1000520380d40e006074140c400c075540e480311000040d5681504541c0c0e410308e205000788403c20b2850b0b181118040d81c070a0311400007008059440c180c002511500d80c40004482d0000600030860114060311114000d0500000d801011004180d840c07038180c0c0240d0101e61918489401c11540344142c50a6802d07502c5d00500000c603a80d002001403914140c068101510344030360031034003000e01000c40450410030340d0740c000c101e1500c5890f10107000d12000c2603484e22600c08150204c6400d442c216030002c0302c00701c1242e600d1f1080700000d030002c26002d418403040c103995440c403600741c040d00000140a132040c450900d45410700e5280040001e40c4c1117001d01c0342058240840d884030112070041c0c0d2240d481c0703410807074000c110042400d00058801c140c3c0c082115045410b201141c8030a400500e6441096425100806c43c101d081c00144122481c002780000d4441803200003050703280c403503031032060682e804440c800034004000407860142900c0750208a56 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 914575845 1250 914574595 914574607
    0x70503010b121c03021303050d110309300f070f05090103080706020d060503010203090f011d0307020907020705031603021c0b060d03110109030e0109060905180c0c1b0f01030504020a030b040503120a051909210e040908 95
    0x434401d03002c0000300750498180800d503046640e202000d008145005041035001b040103030f4012840d81000020304000340c0215124a455804295074124143e490341c40b035441c01d01c07035180040341e00f00c01d0060448901c00543c6405241e03402c1c040380e06401444542180180031f000b040300c1c0c1d02845201c10f540c02042040344403600314010010071044030046c2d10581e240c01c800304400203400290f2294440000c8540848030041400e05503800031003594410220b51805c0e40c01d804060700031454503113020080c1d0301c800c80c440d00c17038905803070641d641c2c01031951103200905031004920040703ca6a0340503041c100b60301d040941d50742040d4a070018100300786050f080c260b0b0001045007015200d1580307a0100f481c0a005c5400d15401050100340c1500001d441c941d018000202402030410440f820358002c083d00b5540c6d40740c080030400003448107540d540c84140c45460680d48100301c5024501549800014981007948403c113031500c0c602041055200340800d02c1e0700402150b480b4800c42501c50b008500791f0f65202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 914577095 1250 914575845 914575859
    0xb03060108070201051306020a0908060a06031115030406180b0a0501181814160b0c0d1d100e06040305070503010b121c03021303050d110309300f07 65
    0x20307802842001103a24180810581c43c00c00c80041d42c0c019000000181d580014010449080303005802a41d80340c400c2006010b20081241c1c0724400700c0e0300a1080d0f14145103242d04215020581070303044041514280041000708515900150b00c0c451304400740c400000807503403036001e42c0c0e81c00c880c203c0000e561800100720040c1608411000c5c00c0b0911020401c140c001840103030842034203a406005000402681045a0740c10003a03d4904040360720080c4a06903129002c40466001c0e00c0c25403054042d840010620318000ea0120740000d4101e4204090308030000305116004600c1c0102d00c080140607110241503468090091010303500a40103005c002d800c18080c942074901e50b0a8083c080c03000c91511144683e0045400c1c60314041144080c03110400c02c503022000381c0039080e40d4004400c41c2403400810850000303000c80b2140307460f4490062050705010140d440b8004c0c0032449400200503c44805003550041010410100c801b9203da00d14080b006483d04c0c011024808032116807000805100e1f0b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 914578345 1250 914577095 914577107
    0x150b0306030f4201080a033e0a020402030a090c120c152303040515040804060302300711010504080d050c2205040605180105010f0215010b030601 64
    0x2210400e005010001c4000f40d80304140d20041c2c03169608614040c481c01c020320210f4800d024003584100d510700300b9619209881e440d542c0600c0120003040d51100c100c0c0c040c4580e203848080103000000e14007101c000012105511b6111516524041d0003001c0f01c0c20f00586d6036101841c00340e805603000048100e660f1a110702d15041c5030700480c50320051211a00001140b0003515030a9441e80801241c0d4101d50740c00aa60b001e02400c9486200440400d100751860005030241d489a80103a08960622075845e055101e805400d6034041d046800c104420300050f03010f03400030080d030369040c20b800e40652a0050f640c84129003043c00e12410340280d6080c040314907484510310a44401140007008039003050b40e12000240715000c0010700b030a48400019102e00300880546004040070b02818840440350300f80c203000100d041c02220f101d985030240100d03190418400000707914010f2405190f55074240801500c08038214035280d000c41c410360942c0c890729891144035500901c1c07082c0320341c0d4130780c02c08000242103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 914579595 1250 914578345 914578363
    0x908090306190c05190e0102070e09030a0e0904020307060f12060b03040302121204110f03011505030601081f051810020418020c15060105040b0c0601033e0301150b030603 75
    0x1300001442400d130f507005501d222114521103804c0c21a141900c0c4001070382084010f03030200e02d4081c06101017000041c07010000305800840c03590381c075010341c4c0010104007550906850281d0998803890003408154011194407414180c03904000107112202c2848000340c44031900b020340f008a010060008040c0c04101080b0201c5000d0041804c1c03042400001c04484801400640040120921041030791208408010541000b4000707100703180b10001d600e0101da2162251a00034810b0b00c00010b03120b0b00c08105055107100350060040c02e084041d40b100e02504001e403407521105d4460440301012881045564641c0309008005611686081d1003070702c481c1070130001c0c002c1041c010824081c003480003081402503c0641c3d00e91a0450321a203004885502864100804407500040c9111801d4000200d190489100d403030607040c03001e00c680c0e90750b5110043d1903540c2c40c6094900350003060000394102c0f40d0041d40c000360001400e0340c46041c0c0224005219448545090000828840706040078080707054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 914580845 1250 914579595 914579597
    0x408090d1b0b04091518020901031e09111f08060a090608070e1e07050a11030309070e1003050706351e0403091401050702040501060207060f0806010906030908090306190c 75
    0x4c4041d11b424408510180b05802d8a03071100d07400200c2180689c001d6010a001e100074003001900c1d1360b036401301c140003000d020205441da100c070081c100e10389180940d218010030442c0030840ba85080e6034501503440300006060a5805448020085040d4116114980c01050307810010003070b03103203060b040340e132071950140c40500c022059030a8800041e120b071800980200d65458050350350f51040800726100351003604c104880380000810303c505500005918025101c0200042040c1c2d280d42c5a494416180381c030004205800c210420003c0500035440d0031401001c2c4120584508840d41013024030000d445900c428040c2c13081e0a001100c01d9090100107000c0b0540b0070304209081684020b01503c00503c41c6000902484c4208003059100368140c4411641c0903200303109030358403541e0280d04c0700d035240110030000f00600c802000740d51041d101d60b4040ca00684600390501d05007079085001e012614825181801c0411001c0459207040103070510400410030612002080c03000800c050740e5285016070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 914582095 1250 914580845 914580881
    0x1061103030717060f19140f0f0d05161e080d0c02040c0c050304080703031b3f02011a0102010908030a090f14060402090f0408090d1b0b0409 62
    0x85816001610001d0300f241e1050411495030710100014081c809480d03503a5000201024056004090f5030060310644e9a146c00d800c01d000130b98024803031040385c0a00c859a20085a40404203d410908605007010b0b01900580d40c0d890103004c0e89802e8020b69912032401408884102c0340014100d014203000341c400d0001800e1402c031004002804501310700c04c044d1050341e80d84411007059004150020a103071340030003503e03252a510001a600c81030948070650104d0440d2612090f92140035612280040c1c2c40a511280c041c50194a0001c2c4110300001500790010594800e02004040e0a19021039140d40d001090702100f0810003502c100000e600c03e410740e81842c00309000203c005040d260f0050382088005028030305424800826600d4080181120000e90303511050540003242541c0f0442c0261b900e214603885407081e00e040114101c0d0042c2031000c05028103d40c40c600902c0c440c40c2c443c0220702500d5408081009003100890382d034010321041c003000504006800540c000c1490800d40400c40d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 914583345 1250 914582095 914582101
    0x50709150c0203011d06180f01060305030403050d0801030f060c0315140a0510020c0d0204112205032814010c0203130b0306060a21020d021b0f032205060705060106110303 75
    0x1061b568240609507014414540007210780c0e541d070400007404200d503100c00070b00c502680c90034042d031654081d000940c1e20380512151008058015440070341240d5011050f0050035400f5200c0303034001c0c106c00c8040000c0503250b40c0d0554007440c8943c1d82170050260102e83e0a0b103031500301c04209031b00000360302541c003030314500340c22501440d00840c2c0030100501c01e0b030300614034682c4c500c005002880c2500134141ca008000c50000030b42400d040d0f07400d980b4840c1c18103103200242c88800301a55903000590304100b0000303a05440c0084c07108a203900650602ca622840c9186c02c0c01d04406087d43d070f820035100016803010a5074000096143c103500010301c0011001482d500300000802c00b00d1003100c200c1020302c1031080d07a14a6114800710388000000c0c40c5502151500c0b414000d8170041e6200d00d00c40400010074400e09034440d00085032226445544d0030056141440e400340d400e000750380781c611403c840e1a400e640000ca64a9010043c079111748a50050101581000005400c000d100420304030b103a0b00034010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 914584595 1250 914583345 914583401
    0x12010c020d0e13020f0a0908070807060f030e01050405030910180506030c04150309060b040c020d030f0f090b1e010308030601210c0c02030106090b0d06050709150c020301 75
    0x1600740d29a106140100b030304000c65003c50154402041083d10703207840000c406401072240c1c40a40320000840e0780c0e181c0000d50342d58030250398003c1402503121981014004000b030501560942003c011141800b2031280d001040d081c0c00c444c0304442c00e0b9500d800001b40d0210920300141485140b55040c03c0c000246d0040c80c074428071512003800303820f010318400004070751601703094029075000b080c00300e810305159126940c006000c2e29010008035801403e10000c180ca5281c40e0141c41c2c4804966030081101d540619030071005040442e41160000740e480780741222f080300f640a480d01c0c0b18017629440c0f1036070808040940220051001c0a48040554001440040e801e403040741c2e0001e40919100d061406d0942c000b80852009030b00001800d07140c8018a2040d0303410821062006000710000c000f1151380f001c1510565500d04001a846008500d1040005415500c43c40c3c002c207051500c0031556481e0b00310007104005100204001c210304207100c4003186030074042c8000c0c484800c40c44203030301114060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 914585845 1250 914584595 914584603
    0x27021309051812090d050604060e060604020a1d010e13020301050a080a0c0911090d0f031403011203120f0c170606092d1504080106090203010f050d0c0504060e010512010c02 76
    0x107801101c2d10300003c4d00580760707444030f0201841540240a032011030030a841c2c0301d00104505c4005510030700443c0b000a419250030710035a48142d80388d07100c1014004601820f16402421810507905102c4500409000c68440300142007122620000042c2d480d4108400c21803a185035500500030342d0301414607540040d1090a0000c212603d804001c10051407085119449004141c6596000031088039160140711b44000b0242c2c80600039140c0712a5802c9000c2550743ea84002d0007000607049040c6c20b480300080c402c2a80d43e518100c02030000403680000d544080650300e221010000003402c1001050700310140b0420703035410000403200645080242c1c00401c40110140d484d04c0326070820070500c6031001000c040030a60f010701c018100c2a0701685a800b291035a000b0b4000c500042d0710f0800c001c94000064400c4905072a28200300d0310a9600e864100710b9038840b034244c21a541811600c0020b4035499034000d480141419840040b10344d811702050110780782c00d16400300002e0f03040c00400d00007141c01003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 914587095 1250 914585845 914585863
    0x6060319120e030a120f0c020f190905010b030711030408120708090a090f0e0f0a020d14010606020a06180c0e06060708072303040e01270213090518 65
    0x1030044100c0c0e5402da60a41400002c0381e054001c040c201c808101425180310700d20350182d11004401d0186460480e11160021030007500143c2e43c0304204404c2c949041c034000e0140d0341e0132072400d207580c803070fa1001c4c2078a03400c2c0d0052561580110621000d0394001e8030b5110326014140045003011728190103a030b130303031040d1801800c03c09800090800034000ca03c400c840c01c070710000c0e00400406607100c803004002c00440692161803403420740314001104000c542c1350701d256429070081440b41c03032603007c021500c3c660110481e41100031f4136003004103100a0040b2401042036070050708040d81c0b01d003004025660750703a1640040c3d021300049100041c040209503000e6030f0744070000300c025680380ca0205603030b4030510101070800a404103403178041241190240c506507880d641030307402c00718084038034596034026801561068a054001402700c81e0312606c1100d0030b030380c440540d0b011142c0c51598800482c0c0c02420b45500c0b0880260b0103101078a010300980c1d0304900f94851050b40710300310f8038016845612071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 914588345 1250 914587095 914587103
    0xa050702010c060507230c10050a060f121b06020d030c180308180102060c0322080301091515020c01050304060b18011827170a050c06060319 62
    0x42450415a4403410784511143c0c0d00107401c01c5682403000c03001d408004030311400b01e0580d4000d81d000c078a104000b01900c03044c000d40001030050115010172100607001c001e100030301c441e40d03445000079074511039a40d04008000b034400200d0303020601c2c00c045c03c9200ca0a141c081000d41510303010003030154002218800c5100c507142c0015519542c040445040c040c010404501b220b83e10707808824498500d0050070040b800c0040d0242064090005a80769130085485403810002407000480c0c02007901b01e001e40c005070710303110700c44120059902c0f003103580c00a0300308164040d95074915541e84840010381002404180d6204094400062070096030fa0000c0c1e00098100072010001c20704010803a0010003400038024407188409202d00c2554528500902c10401950500e41807000c00c00314070306c110056120300548071a0800010031418801100d00d2000702c9100049281110444080c40040c2585d40000e5a1b1666140c4a21170401d00c0e051000d40b00358401d420004580303401040140940006645c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 914589595 1250 914588345 914588347
    0xb09010b070f0c0801020c16060c03080a0b1c0b060d02060406120b030a031e0c0804050411120f071103030906010306050c0c010213030b240906060f16021507080a05 72
    0x2451030b0240d940030700400000c00514031800045112030040d0003420f5019818001c4030000c9803007410140188141d031081d8004160003003c9180403e100b151780036800060030303038041030000021000c0b03045401c140c2403884200c81c00360401003c200355122142d40000045680ca0582e56554001581610a9100f01000e1003a80311004d440e0858a811015620030700405603441e410b913030b060180c41e8094215800d40360ba40c040e07440c0580c84d8060080d0b489010f40100c042c605142c209004d000003485101610064803a0510001070b89101203a8082d10490700b46115801c1070078668000f50035901c0014201035260400d0040100e0303c0400121241105c4e08482d012541e40c0f1001140055807051080c50000b55000050701e90000100d500b944044074403422507460280d8424207941c9107403100c141f4450918401a24501807454400c41c1c0542000c0014285842c100c01811107a01c1039100d22444901e10080b505aa000d5191519544400242c15a00d081c600381d100e80d21500c052007090b03c4002400740c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 914590845 1250 914589595 914589607
    0x1d15010506090a1d0417030c030c130b13030203160308031f0f0b0a120e0a0b04150603050c090112034d10020f0a030504020f040c0c05010e010b09010b 66
    0x107a603c6843c001070403113000d144150800030041c108909011103003924826100541840c00712030071030880303105100380e04065003180c90312a070340022648000d03220702c83c000102002160034884400240243c1c0c8031040d244060600d10300c180344c00c2081703010b550014400d1045c810008035215500b181d900280005102c070442004000b2070b582c20401e0342000702074010a0001081240700c0d00014020541542c440c84c030940b001e082402d060340c00d0015140c0d415085031544100158403450121382103032140311503501c0251850510340403212250b0041c0c400d54001e450262190030035014290140600f1610400d41c0782060720702800c00307020302c2e145690b0840c020b011018041d1584c143c0c0d00480d88101d91268028240c80b101c1d60010072544601c640600400312066a07244062003264055407030a2409400e10010b84000e9000700310040043c0d030852018000403a40d40d495118840090165403150303024a60942806c908441d05150301c5510341c1e141c00070340c601c25514611b11904660141c050301c0e03036442c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 914592095 1250 914590845 914590849
    0x3010b0406030509030d061d13030c020402210a06030303322a0c0c0f150a0909020a0503190b06040b0c16081b090c0f07050a1202011d1501050609 64
    0x8410806c0c0b41070001e25190010a40e580c064048202e10342c100c070135082140d00d50a462a0120342c0c0110001d021513110145500141000c1d00503240307140d42c90290700f259410030000c5d0b8030108012160801c1540c0e840c401881055054442c90100d88001045203000c20041c20094900410301e24640248040c00000103c02824003400403424048454400001c4d56007031001c080030f0b80024001c44582d00408640b51424182202c4070811504010008045080302d40c0c54030032242d0000302c03420100710580c0008186840c90340020700503e0b0490341d0b504d60300e02d000c082019610071743c600352101540c101420980310303036540c1003034805132595056a0fa941d8190207008600c1c040b1784801245013011b0044000820f01c9011070701c44004807031002491101c1d1103443c10051070284c110340364008c0c1c94090002c1030090032228094211948201c084030a08041e603200e40c000036009803c1240141e44171191403004449002074041c0c101e90300e80091240c119420303036487c0380640502500340260008500c2c014a5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 914593345 1250 914592095 914592097
    0x160b09031e031c0204140102010209090609060d05160f0e0702070605180919050601020102160f0c0b120a0605040903050703030c1806030603020424060e031c200303010b040603050903 80
    0x200748408400411240300f0110800b0350894803030282ca00c2d1603208110240e50060084600351030b00202110365a036071f01000c100c1c45503c0900f0060301f00844090713803000a603003004a00d034403001074440c4e000c40354509118020a102e03150001d0400c114090103025040380c00080032070503501c00c4d0410300d8a590030084050344d1202c2c84003a0580c010105005e1000700d08007803000e12000f1a2032071084c002951100d005900381c0c072408990024055401034001c000c600c01c188680c44240c426421244da141e034540c4c0281c05078200040e50300100c111076040c001c01d010644600d071f00a01013036405101e101c20340d8070007030103a003d4142c4c06414151240740380b07c601c13446040d0b0049440055803100000a4607104000c0c0180f4640c04103d000d149070584a04103541d0751800b00510408140100c2080c034140081142c0c01c2c441c01c030358542c06104007114201d2035200e4000c028000030030fa59607180c0d4410b4100f006000c441c2c0d0944482c101d90401c00042c04010154000c55080d602d550501141e10348904056030707d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 914594595 1250 914593345 914593357
    0x60203040603051b04090b01121a0d020307050d031107050f090c0310050307080c03101a010507060b0603040b04050c04090521040e010308120c040b0a0f030914160b09031e03 76
    0xa51396000601151940c2a6401107403807070000c1c0e8032204030742c284074400402c541d05070102404000000c50b000b4401d04e41a485204001d2018041d00c100c5035851010590b150030204040b00414030412080040c403608018050041504851100e844a900c801050b9401409007080301c4e03000c0004002500011035072404001031401808490071243c2d58000340d5103600b09030151912034040e1079004104071449004005420744841400b41c156072141c00192203581c0308401c111400d64440c0768a01140c2c0d2000c010f944a01d003d50851a0340e0325062801390304140c209496280310f02c1c50b25100002103180050304860f110940c0001502d91242400007580c903002d0740e80309403502c100c214000310401c40100c01074196045844400794a6803244c00f603002450255028404a0200902442e40a03510038170301e26190501c03030b080008a5121075264901048140910a08076900440e0281e0602600001c483c1c01011852142420041c8035800243c40b000700b035a14180e410100d0341c400e802c2c0fa41c00d00403140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 914595845 1250 914594595 914594641
    0x3071b030807030b030703021e010c06060e0613020a0c03030e0c030a150b1203090405060612041410151503110a0216061d0d050304080102041701050105010906020304060305 76
    0x541460319008105031000c07160790002034103000d100d40803824000780030810350b54000d05428100d2000c881c0081c0da42c1d41d5860050420009030403500100b690b9204070340c0900240c0c0841c0250346400000d0048906038041001c850a2041100140060f805121800f2650b850f01d004124043c106241500c5c040103c4c04070703a81030003804401c2040000c1030354070080031040800c0600181c41400c003081412000c9514200d0ba5410400007003005140c182d1000e50700400040c22113041100c040c0d44589102421513040ba8804a40c115045818000300b00c246081301200e00700b40b02c0107040d00300f0382c0e241a170b281c80341220414410103c4038a0501030780000a4031409420403d407251461100290345410301c0e6103c4101d26458400822000c1c850314000c4103450384c180c0715428442103d410300082441c215001d9926000c20711010036428000c4c0020f0009010b40d400c507074640a6400c1100d030031248113901c024148408000304001d803a0f0003100b0f031000c4460904000545540740b407005110075402c50007200b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 914597095 1250 914595845 914595887
    0x4090201050f1c063501060312030506093106090605100e06300a0206180a0e2e1208120711070b090402160b041b060f050307 55
    0x2690000007840d110010a1265091102c11340d225041403c0394042c441d24841e005e040900c101003540e20501900c1c182c030000d800081d0040d540d490f4003003d01d1401824800003500c80060006d18a000c109450b00b00b17413480d0940f4050902d40450031504035a001842d4a61080549080288601980080c0b03000380c01c60003d0106142c1100d20008125190080017006101d420200ea01820480c0c03000c81c0c2c4c80444a0124850b1034207694095181ca4000000f180301c1c07061101200050320307588080d141c100c1250721200700c10340140e42001000c800580018044041400130052180c0d880045102c10014080348101810075802041c1c0300c800c0907411042c01c8404141d0b641c803c20600034010420303011310003180981c1d900d542c0800c40305082c0c40001c40d4000c0d1b0100300c0030f00025810307500078021038800030030051400c91023020068920040d2031060398801102c1080000303101d9001c10690988542e185420710081c10101d01600f03c4800c0342422041200200c00201000e01800e40c0c0980c0385003d640350 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 914598345 1250 914597095 914597107
    0x201030f020f131508040605061306060806011d030303060f01110a0f060f0903080c090607170c0f06040c06180801330303051b01021b03040f05060403030c0204090201050f 75
    0xb60741c180d01c640031181c000030344040300243d000440b081308100c841e92039880d10703942c1d2210744036000034102c00780156500041c0005007401500c0d40c2e108040080500392690449494844000342900c0005042e08500301c524168100711540c010084942c803440485000042e400c074a00100c032140c100c0c01e0301825503c64030746c600080c0440620903140d06c600c00c110a005900118164000ba9122408000e0102c2e100c00042880c02c1c490002074046c03001e0140485040c0581e644680d00800090b40c4e05006020780000d001c1c03030504040c0240c1da6a610004020021030038166176000b0008014850301e020002800000c07010110301d0b810100060400c0030090004080707030314121880420742c0e60b1204562850301d4501070031b030000c8031050044030b405031902d5041241c00c0081241750158100a140301c0d541c00c201005010304032507600d508111100b0015030301c45052601165000c04590841d51142e4000e000c2080004d52103903581c078030182d06a0300030810f00032603c01a1950300514003200f0345c803c1c0c08190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 914599595 1250 914598345 914598367
    0x1080d0c080d0c02010b06070b0114010509090f220303091b0312050702041508060604061703040b0309240a2a270902130f0b071e0b0f1e01050303160201030f02 70
    0x700d54103035841070382d40c0b004103094000150341c0c2d3b10070018200e0b003000e10000001c0d000850036160950014080044038075101c1100d80d80b0034010400d5100300d0100383c0e031704400310500c100b03011145001c0020000481c0c1090a50701e0b18030049445001d00e400b0004005006800c546580d080404039500c00d1103040381d00ea450321669034480e901242c20f2402189000c0c5c0000700c404841c0421100b01017410040d61809007048180d50080d40010304540b12072041039074000c0510928440a89421151303903070400b01e0308080200380140eaa10340c4403a0612110150941444120b030103001500c501a41461820300040031407042440c200e40300c0301400030410301703000144000c0b40d800a00c0e400303503641c120780c0800ba1211400004c0bd1a00e001e4404a031009000c04000143c2c440903038007880100081c106181c0c0c0d010b55400c1d00440701220543c0d001c502402c00d11651b0781c00e00d20401c0300ca04500c2c28003000ca45c1002d01081c1d490040c54203440c008092a00c9510941e40680e1040910400e03880302596a10301d061300e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 914600845 1250 914599595 914599613
    0x5030306190807033905041107020612071b031b0203011d06060312030411150d02030702030d06050f10050a090b07061a1005091905030a030801080d0c080d0c02010b0607 74
    0x482e08a01d242214078040c200c1da14445540c1103c0f4030f610303502c0d0170600b0320050200814042c01e400512410400050000d680d8490152803424403406000c805890454801024100820300450561600440c06000070fa00020a15003200210407140254017160000a024114004211480025840d00000600c1e80801d00c6845200b054003100d13684030500c40d510f02c1621003210098020b41c881075036070045203001c101c0c00016031004c44c100c42c18042100b25080481c2c0c41070340c8180c00741c0c0c400120408000c0c09800307850700400341202d40100d00c00841c40801c0c150064049083d040203c00201d1121081c0500e8400c006403e00c03080498a070340d0949020401001300005901004810340680030745454039042041c080c03942581c0d52030400038000248682d49441040c58019105080c00c01300d01c64404005410032a0b010b603441141551400c0e070618141003020025074100504048140301141d040c400712900c100c0442d80010f001a4201003c0b030040c0500504698020380000b4100c040c004404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 914602095 1250 914600845 914600873
    0x20310051002120906030601050702090a050114060403021e01110d020c0301060801270f0b0a1e110f03130804030507060201060905100608041b080a0314070503030619080703 76
    0x40e810401e00c0e241000140c0c1e07500d45400150106060030440100b8074149a00551b42202c010305049081c205680d00160099104a81090a00795250010400301858a403105582c480680d0843d191178159004a80504800310f240e0881031903410300e02401e40d104803007000c0841c1c48002075441035031a01230000e4031010301c696028400e6003880b0303000c15018018441c1c01e82800d10ba400ca60f84044d1003c0e036481c40710912007026070340c0c601200c2a1501145c00341903118418424003900203100446407000c0b00d1145c0f50b00c03001818261506002141c080d407403508840b2840b00b000d452603140c8c0d4a80d01d80c40d4180f00d03420f000620903c0c010078000100302002841d4020365545400a0085649403450101183c400b00c5060b02c45841ca03403001c00401d070180801a42040c028008d15041601003556040d0340c03402a48800b40315441030800c0340501d680040800c003100d408645e0380d480d003001a25019501c0c00041d1580d4801d0151443d04107030000c0740c45482d0018050441551026696030030600c188204c3d079 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 914603345 1250 914602095 914602099
    0x415140d0b1e150307120305040b0f0702010201140105030705060d02070210030e15040308010302010c06200414010203040e0406020c0307050f0723090c09040f02040e1501050c030414060d02031005 86
    0x1181c04100c0c0626200e402003c1000c2c054002c000d0649000f145080c0f549040c07000340e060100400003c54409030030302c002c10038445041075841e522101031000900b1100c00303400c0000b9115004c1700500071658041a5181112401c07107441b9180c0c10001494002445a080020752104401c00074400d125055000304001d4440202669410f642c0c4c0740d0880c2200e141114002c00184206005200660007001010786a80c09014000ba80180c040009000c41d40c001c52405a0f00c040420100886aa000220791000400384061801e00e03140000b40204030002600c02040150041540a5541d204105540600b40c020301111070081c8075543c3e41d52603106500a01c5006000505d8480c581800100c48144c6c042d00602040316030740c2d55200d03221698010350b03031665105481c2d2a2040c0d80342c08500180c000b403d006040140c0f0382c01c041003101c80c07030692248014140401070005045036080032094404803040d0304003806502807098001034180c4249095103400910110a11520b404e1450341d085c117844007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 914604595 1250 914603345 914603401
    0xb0c0a090b0c0c1f0c0b0703061d250c020f01053606030103080a031d101a0405010f1208091512010509060a03060b1207230415140d0b 59
    0x107080e5940380e20301132402c407080840c012805060001b074440f407500364054a2031400040c82501c0307112499074072207100c404240c244a08002e01103080b4003005945141035042154100078060a80054805103050002070712030120544004110390007070b0200d440300d50b080d000c2c06507441e46101031040031410400003030320110004000803a440c105042160f042e2900141c3c1c06040c0704118401302c01610942c220040c03455a419600e81c40c100e42040000b0550188450200744420b0f004200303d241100510040e209504090040003441d04940c9104144d680e03102501d001e0340100d0401600511400190b99003080481520b54914040a40034120f000506030091500d40d076694104455100b003a20b603550b0001200300100005511030344088100800509011069010a40e0b10f60030b241c07043d0301c82009000001d4880d0021110300d00756502c0b10004075010080d07a60101c4a2240003941e50080302a520444500c1d4401381d80c400c00244900c5602c1003400d01c1342d00c1c040e00300c0d41a200789409403940c5800c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 914605845 1250 914604595 914604619
    0x708010608120f0c010f06080312090c0108011a040f060e0907080c04091a041a0306010815011719050318090103020321070c0807140402070b0c0a090b0c0c 68
    0xa001ca01d0b00000c15110880d14202114400c1071800c1d5800940094059981c680448010340c400d40600d80c010f00760710010316206d4210140296458800030006003554009043c050600da030007918a9054900c2d01051a000890001c401c09079441640c00800c1c00c009070100c0018002c1d4042c0001c0c400078016510100c035034460100c00da41140c1c05584660b800141408207104002030b503404000740d0f14011407e44030092003900440c2c103c441c00c2003580300d00600442061003500341001000e0042c8502030040c041c0600c8440b050041036018007072814040e12102800340c4429081005c0f111581c5100300f06a4500075600c2d001d0f5413548100c2904100c0c080c480034041030f618019505e54100c2c3d40240150040210741101c0c1a00d445102003203d03071800c000e019003c00300314000c07035041c06401d044005240850521fa00104505000ca1116100301e0041040f900000d040c00d81a0b90070011800281780ca0704100c0300c058401c04040c0d080640401c2020440341e00c0a04001400b8281e040c05642611000c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 914607095 1250 914605845 914605859
    0x70f020f0a111305060120031c0b040b010f020c0402031b0d0e010c111b012606151c1a2701061412070c020a24050a0c02060319050907080106 62
    0x2071080f43c0039404510041c40380d014105000d044002d07c40b0420064070b182c1156903140d011900c0c55200714040a942e2007407203482c1403e00d4424403107010024203003104c60075100ca0000b582e441c06c80340041d00403500840800d903072247c24490740882c4d054507121540c46058008645006080c0740c100e1414a43c20500303000390550140042e050384001c07100180110310007845029400342c148a1540c3d04000c49000200340c421030002c3c171405817a200900d00f0606042500c10000841d4a000303031409100380411540000003034144a038681d580202d840071500c01d903200180070481354910070b0306401a00b20220800110b550140b6103401001d492444443d6076280c1c2002c549194196590500c211810400711402e00703900648a64001ca0901d050600c0181c0c83d404981249071660102d1014031000a028603404504010341003200c0c59881c0c5a410400c41150013000503021040103400b554000000c03c40c0c1d44603003901c00e8030201c1802c00500890030043c0416541c1d820300e00c034050840d481d2140118000e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 914608345 1250 914607095 914607101
    0x51005061e06160807410c150408060f01050612090705040f0606031401050108370615170712180b061009080c060c39040e06070f020f0a1113 62
    0x29460758691120700f504032100108a03824441e08003401d0b1040359190801c95031036005561700308c01035500e240d41396840e14401a1401c0d4020f8109800d2000700c4c00107100301e4840340b0680c3c40401c0d04024030000c035100c8207045428140c4d9604155081070070800a110078084640103e002c45e54590380801c090045a2095012140c0a0244500041da61008101c05042064807842c11807511101c1102e000501c500c85441416090074618803c0d0329028200200340380b024025031045030a00b08103031071205024180000ea080186a04140f180420704040328038241e42c49884100c40c0da00402e5204540380c1041c12541804803001c520940d0070400f154240c0348202111021100140014131240300b40c2c40812000750000d4004c48071901c50301401011401d4146248480d00301d0820021104201c0d4a1140400e802c0d840f0049014a003442c1c102c150300d1300300242040d84610285401154142c03507030b070708a091200840b900c12403441044c02d45420305c504030420380440e01c4c00702d603201c1d5884090340051060f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 914609595 1250 914608345 914608403
    0x200d2304031a0912070c1406090a05090a02070b0a0204150f0504060807140a0810051824060c03030601080a061d090106170307051005061e06160807 65
    0xa500d8441d401d00100b074000316500e60b003101c400c00507078001040030780c220303102a000224141d480c200c40b644104191040d15800d03490942c000c0c0d9115140402c80d41c0443d0340000140b045a014501c141d000038800d44440d8151440c40781d100032160014207000400c04040d401a0003201440180a0744916280d0b001e086c106110300660789130103042501c1d0420036200300000800500a202058401007001d4540c20b006080461a54032800028140100c0c0f03100d40103015003285004240445100c1c964524a40045605c60242c105c400c50030107005540b490b80c0c1c80910041c9801c00c0e4042040400c5440200285108100c282d950034016900c0751100004d90384244140444031400d1625005101c80401c544d5038050100e00000c02c60315600e1281804019140c2e80e000c4590708040f40e40410400207110200580d900da20041c4030604201c0002003080980303202c42c582e0210000e00c1c094043d01d0b10400d9800c0e010310396450010710b010f0340c201820720f58410301080321503682108618030b404040002c0011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 914610845 1250 914609595 914609603
    0x5130b12060901050109031104110313030f02160905061903031706040203040c060309050f0f010c200d0c061404030905040f110d0216020409050a03081b0a200d230403 73
    0x151300340c91900c07000122300c80f82444e10f07001034460401b01d03404502d400003123014040c541d00254180070941030041844c400820380404540040c4060030313165050643c2c010940d1360440001540e6141d1100240031103e0a00b004102c008903e8400003d050300194161615017980720040c1c1300340d55484c104400c0784000c423001002c101c50038006204191080d800154040e202c2c0045803030038120508100c0c50170407805200856a1344442c3e1aa00c02603120788020a559480c1c1d4441103840c0901031407a441d446400045c108210039a072071a024440150041540b906462800c2c103c14205410000e0007940319004550042d414400c0c04840c0c0790203440340461480d0159126801d007484290705601130340c41003403420b2036809880048000340e0f5880c4201d4540500c20380c01081178002d52301d409061400c00805a00c13103101206214070801040390100e8240c01c000345050050b507644003107050140e60740049415814490743c107540d030fa01c0790000d01c0c5422005081c1604c0c1c02c52084140c503002c0920841c00014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 914612095 1250 914610845 914610857
    0x1507150b0102211201180f0915110f0a0f08070e0f09150310240608040f030c05062a04080c0d0503041211010305060a0e1605130b120609010501 63
    0x1c0040484102c043c100c1180c1d07600c51030208003100c001d00150013038100301c1b2100740301c12180855900364400c0004c0c5102c1103205025074030380ca071204910b08209a0b2a0f450098440201c0041101480d0844001c002e41d03000b076680b00d0440e80d90080010202400e1031000c00c1780038000c252842d014404014612200038142d804c1c00050500b442100c0001910170380c0644820254513460b0b64060105051691000100195403c00d1580c0b600f20100508610500500c0e402400d12030300364000803070380c1d0054105a040300351101720b01e002c0310051840c0b10041d1185c0164800d12050591441d4002c050003910070003042440c2d820140e2500c0d51265100c2c510043c1d11018422a044c1000b885005d4240d02540070350b42066500c86403071407601840074044560503c0c42c02101829038042c4920340d013050341074030b0f080191818801114034001010f0801403641c6140d074071040743c00b84039400300c07210b8050a05042510b2a0781c1d0200304400c1d04414280f14203c842800056034a00341051a2030403500142c0d540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 914613345 1250 914612095 914612113
    0x90d060e0d090e0a0b030c030f01020915040305070e19020d0504030f03061404110f04030c06080a05160e0406030512070204061410111c0905180408091e1507150b0102 73
    0x10070001c000c170020310340e00340c01014030811541d078040c0403c0c2002234201c03001513900d103015010421201c24620080b602d4010a200c02c2c800b02e0000a50441510500b64001082e071325410440820a5408480e6a00f414000a0a40e9200f00c0c69001b650003940b098903804007011040000b0780580d442c034058124605070a160020f01458150813626688404014003440d182c001e0000c0c0143c0d40c0031b50003c0e1102c03001080c007008055409020726520500c1c81d0760820040c140940c0404071801c0542540e0108982c02a01c030203950b0b9035520000080d6401802c441e44e2401014141d20ac0b5004550141c0c1b00b90720b00000000c1a0300c40c5102d03401680d100615107000a43d00010031b984211f91061007480ca0f00c41c900390703010692142070810500e9000b43e120003884501e00005c00880c030f60340440340000304c07440d0301c144400500002c0954941d04011521001c03504002d40031440c04200030140e140c2d00c2580c50715010128103018004002c40780c042c10405000320310000d110001e482e122501c59006a200301c00d070b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 914614595 1250 914613345 914613361
    0x3080a050c191107060215090102040f06030f021b0619050411010f180f031e050a11031002030a0b0a080f0723130c02160302010c020d050102090d060e0d090e 69
    0x51a90b4202c141c200000c1100c0814a540d2405240360005c0025074400311860400300440961550700007a603000075440c0906128051591400d58400e602c240741c0c0320400311b1446c030810380540d0b071001422110741001040d804640c542e00c5500303a400040c107103c1c1d03406040c00e80c2201d0148612940d0000750040d4010b0750035004480448204420740d0810a40014040c1c1c003052440d055001462000c0c1d400c004103045040c801e251090075070424071200044103103540061404120008800d802c4118031000c0e50300c900120f428125444049a0800d00c00810421005d45070703406401d504605842c07215100d501da500c40d43d9603109424051449601405040100031240d000c40c0c5c1c4981d500780310500b4034494074000729041c0404000e4043c9003944035196407030840e50400201c0c6205101007a440d0b010b501c0c6400180c8448040b0300c0c048d01441c2d820701580103000e400d4040f2303115005c0c06812844202c9550a100000700300c00140704c00c0360302a402d04104143c0c81030340c20030103031480c5840c2d21030303140c0f90b01507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 914615845 1250 914614595 914614627
    0x30f0209180a0e0307060e1903271a18042304060b04090b0910020301050105070215071a0103060b010201050c0f0c0c060c03040f05042a03020906030c0703080a050c 72
    0x10039800c1503102c24420b4808801400074041c203602c00e14000c180c00900f010901c3c00c0c1200039611034070011803039032440d021982c0440c076501c540c020142030464ac08086080309030130032003503007084019504c410101c140340350b80f100003010440320031010010359a00f000100002e40f2030940000802036584060b10225201515450350014801c880c002110707050040410142e480c8044151500001d11007001200301092007446030b00101c00c48110300d10340c14071001030058025174402900030564684240300d100c00d500129000d103078209106942c0b00019140e230913140c200900084036081d05002809032154014000d45005056011a16041c10500300f07030b21100b90070803499044548540c0240802c6910340c203004210800c4007002a55559003483c04448a0200d590301050040c1e1a08a59042918151001901d0759054210702c07040d0054001085010340103240307550390b000500100748010620128001c2c00340380e200b5211080b50340c0d100000d2508481003103498402280f020006494414505c1e5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 914617095 1250 914615845 914615851
    0x90213330f06080a1b09090509210a0c051005180a020901030b0a02130602030d0c110303071427010909050f16031e061e121e050a060b01030f020918 65
    0xa02d0000e015541404c0d05d0b0480c1e01c880703e041c404102c40c1c81c42440592140e00800d684010340e030004101c10a07240c101c150081c1544840b6402a50700071901207480b0380b054a0000c2c1098000c0100d51141c0819412040180801d9a81c20b035441645581c518030f01e44080b402185607500200030310b800e40e28503216071109050040030035003055400c0000d074215054005080d8080c064a40c02542c60380c503450592804c49540301c03880c0050102e91603036185003060020031a640000c9614000381c18101d014040340e05400f0340c0c0300349100c0f00c0001e140a0101c1030045003e5212502c266940a20300e540c8200d6981260b4065070022040004240050a40c80380100301800f076245a18000030408150260340d441c82141c4030996003925100e020400800ea0190075070206500c540c460100010720740b00350b040401040030070040003182d80303a030107012161240b140e900c865074000e4103035080c00ca001d1910000412051b6440c6022034503140c50310203d03030a54420341e421407101920199001070a0075961030400402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 914618345 1250 914617095 914617111
    0x90e040c120201140c16080c0f0f240a02010f05010503060a110c07030b0402040606020c100e0f18040b010609050d030809030d020f0304030206150a050103090213330f0608 75
    0x40c18080049100d400c1c02404840e170b5802c080c0c0900c8000d6060100e06a520b41d0010304030f0350040c04141182c0c0d0b00c20126413900e10086502c0d514003a448400b09110302840800401c2c000241c1c01c040e490324801c80028100022107a0081147c141101c2c0703030004880081c02910741550160002500841035030744030710f6091307074100310386402c041880070003c2c07400c0c0e0b10350001c072244001c510a01c811420036000300300241009001030301c1d28000340d9010980a1201402510400c0b1150b03183c12030b25140d40c4d4040d02003d0300503100020440c002c0c0f1015030101d40c280c80c100d03060604a0000103649204440000a680c002403610040010030345044498042c050b1030b201c032a004c10000040c001c0b045200401070907000022641d21303072500342001380c14144024100c03070301a00020750412070f554035803d60a080d96004d0070700244900103800400c008910340c1c4144801ca81c908140c000e46600e00c50100d1404032010328a0141c00032104800c601c1100d0b40e417107a00c0c040790881d02d05202d1580206c840301c0c0d105d216 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 914619595 1250 914618345 914618357
    0x130e0403120c030b04140c09010516080325031e0f06080307032706140706090203010e0f07080a0213020a12022205010c050a0809032506090e040c120201 67
    0x14000300800b102e1021069034040703076540700d588a030790074a401344400c0c40092041c404a20303d40310203140c0c868807807410110304200e00040c464040324950b514035803005401c81c0480361285401d1440d060058204001c002e0084203c05000200c540709001e00c0c4880e0608014204041c00122506005009903020601055854402c0400c038140100050490b1a0081d6914074208446c12481034007240ac4026280f00951a10002d002d015000040004017400e0314008130b41c1c0300c007039090031401420040d42c0298954240340713061110210004a915041d504503050f03030102980c43c070403a270b901c18801c0c4009410014110a145011046901900030203070542003200647c4100030107034080707038441031042e515a2a03040c4120208000502440044c3c1001e0030304040c820141d0301da05503a403100c01c100503d003960010384800940c4003408540d00e4a4907a03002c400c07215210307003c1c0b5291117070341e80114000100103000025281454440c1d060256400c00498000301c0c1c182200c4032549814440c050f414014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 914620845 1250 914619595 914619617
    0xc0304021f051b0606090108120307051810082710020307020a02090c030a14010617040c05060d022503120c05070b09011a0109150c060e0a03091a130e0403 68
    0x40d080b00503c0c0c8100c9444050045890034208101d500038040e00a00601c0d0311004501c0001c14100c41181e03000078060030082d481d4540c0030b08014104541c41c00f040c2d04046501d00410180e50030000c10b81c000d070350700300078880007103111784642111440c800c080f0091070380054080c800300c55841d0f005682241107071050b1001c482c0c2d56004140903c600344c81500c10400000200f00003c10310744242807917103146240364107465151060082500185401750128004407001050030800711b049544014440a0440d64480420428002c000c0d04440780e05240c01080301000d1010a0640b1004075013142d05464001e0401c0c00070a00304000e160481c0d0b40414404104496404104485ea5480c40f4260910020a10040001030710920a18100714079050004280301407051003a10710340503c0d83c05140c540705121142604001d4043c01c1e0f000b50105090040704030b00030030305502210b04010f07502d5220340d10014807400c41c204e007594411000b0101607505046414040c00740f894150982050003441d01b072140300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 914622095 1250 914620845 914620867
    0x6040f080f01060602010603030801050415080f0a06053d080109060c0f0212040b0d022502030d14040608191d2a090603120408060f0c0304021f05 64
    0x180950041110341e4000e04000103280024007601019040e40d03c004e11140f451607a001d444050180140d500c66922444135551032020300f0240e4004102210407074002030407100340e840e11216104402c0d1b5010f810240010191641411034042403a10380781030010356440c285142040d00c007120040c00b09081182400134080c2400d00410348900d002da400080c07401074003000501000c5c50528000195040014841c0444188109440c100d80443e00401e60b940c5800d4420002889105e09843c103169074500d8108004480c400b148074058801d90482d24401403070402607410202c1d540100042110030082480400e02c900540c9030000d0f8400d01104018914038504415150742c03114400741155502182c0701102c3c420000c09914001c1218502c00d0706058140e000d44181c03180c1d05840c050004507010035480e4404105030280c0c2080b50351402d403a50385441c040c0303444040c182d80a005108404010680719050202242d0081c4ea000f080000c21910802601c42c03400b08000c152070500000340210031880e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 914623345 1250 914622095 914622119
    0x1501021e0d2109060b1008060f0f01020f0f0303100806010f030807020409150509010b06132d0303181a0d050411030f0f01051323030d1a010e040e03070807020604 71
    0xf984280000b02d030501c03840c4180611002c045214108001c012018410b09850382d0002d582c13507071810703a08203410700752950050380381030074640c0c0102403445081c040989004000c0041c42c083d01002c03041c60070301030f601e41d5200c0d0340340307000e01840072084e112440400000c1e240400902141c0c0c80940b0101d0000b030b17183c8480c640218015409451aa281c104201101c1028400c071111420110b0300d140c10f100c01410217a81c4a0b41c40c0c02030030312060b8241c03100354114201c2218036020300510032202e18484d40b01d01d40280b407810800304030a01c3d1261b032200400c2a01030700a000111660001d4458200420f58242c000a002c014006450760f410b8800240100d840c24065900b041c032000001307190841d9a20342040c01c4400041551349030002100c012800106002200c80402440000100b80d041d1850350490540c41000c2d8142803903072610912400008003503008000b5003a098032100d2505000200340401ea0b070401c0d51420054100700000c8000504613409040e035540042c10040c1001c0c2c55070565015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 914624595 1250 914623345 914623361
    0x608100509090a02030c011b1104110313141203040b070c05030408030705060604200a0509040c2a080a18180212091b010f0c06051501021e0d21 63
    0x481d410a81c100815410104013018806d031080c40c00040080e11103a42d8100201c40040052038201c0204541d1120b903615008001041c0d03604401e95681c0c2000514070b4078188452004640c3c1c500000e2030302c0f164034000301d845821140701b801e102d441c50307485a03100c0c110b105c0f0041900083c001c1c010344500102c0e80420140c00a030041000840e44c40d02903090445c540312000b00326920503801c00031342e1081c007011503d141c81d560100201090321060102001c0d03940340590740c205608a8076104602030500c1d0320100328004148980b000070122100c10390840d100004181c00607000c80400c101d6a50607622401c02e80799008200c683c440c00f80340d140c0261240440c2c034440c601c003009801290101d92414803840355500070840702c00912070403001d0805d41407219031483c180c0e810301441400c0346540030302030307000c41300216401241002140b8203003448141680000f5145401032082150f9451400d401e0a004091841d0750f900400e40d1280001040390304c8803450042960881d469021843c49155500480c42 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 914625845 1250 914624595 914624611
    0x3090402160c03050717010902060a030905030418050f06010e010e011b0b040c140a0f0605030a06090219030506100206010e0a020c060901050106030b040c2003271206040c0608100509 80
    0xb1710300d1520b50300f030144101c009008100c40c1d16080d035090050355524201d51420a0034100030403a0043d6003810350650040b039105020a06046101441755082d0303510040c070440c0150119031840e02d4080044601c4002c030107c0030701050400c0481d460541c09900800e140205004084209280c0f035130310b00301c44090944089805441d0b6103404c0c000d1035071034038040c103482d01d060300c403030091914001c504502210144241810b1050001c00700d13a01802d281c00c1600941f06801c8255502d551142030340742540c060805440000e8502400305803649040d10400022203126030081140f1703400d2802e03010b00004042c081c0c040d516800c00104007179440511103503100e02040800010039600d4050098282d50b403a904940c4610721b04031050440d9908100d1443c982e444105550700d95880f1510b82e031b8554422040243c2d18014a4048108070011124811a020400342c540f00300c0c0740d903040c4031242c0d02c600c1550020159041c5000c01c2c05018440c0c560154400a030b00710301c0d0f00203582c2d400894640541a10b40d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 914627095 1250 914625845 914625853
    0x50705090127122d050303161407030e03061012140a05060414250e060d020901090c030b030a0201080610050909191d07051507060501060c150e03090402160c0305 71
    0x15a5a481d0f9113200850780c111584d00e02c13207903007003952006c0d10382c8001402008410540c0c0c0008007520321542c80e07284603101c28000039a4486090a02a10203214040074910910030302e400608903414803140301003250800d004800900025a8810109030141c400c0c00c044c500c2018030807004950f0410405004501520311040e806070094121410448850804c14400817401151401c400790200d09808607000e10800c600f254842400260424000c6840658080402000402c42d0440ba51211410301000c2e2130810622211900381500c90300c3d04600a404500c00600048182c1070204e14030030f00750300c10320700140703000c020000213946208107441641803c803200d1660320724640c41d40b03d0200300d4400c200800f000402c0245a0316918001c6004243c05400d4444010080b080c111055401103540b0440510070342da1078003001803117001c5070041511981c2004030720b041e100095101d294040501300b0081c510b0f00407082c06000195114841108a40000b1218a80401d081102200c05113114201070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 914628345 1250 914627095 914627123
    0xb040612020909010e070312050d060602011517070e1f08060105010e04090209150102030715240303080411120105090a030e040c020601030b15060307030f05070509012712 75
    0xb00c10801e1005116404580c9000649000868001011001ca0b03501c0500d02d4049890740354211010700400040341d10150400c3c80220b04941c0641062110910491006501c0c0355640814092241600403403081d80d00320708010b00046000c00c0005600000ca100f4400c2e50701500d0036003218080f00c0764080700480d08010700512056078484183c07240f201d03040328280250042c1d5000a4411480504000c280303104d03404010070f85900034403d480d83c480c1c02401c2c000d03803540fa1a142e0005460f00581680044200c40030141102440e40002070949406580d17603115039807a0b07520b01c00c2e4582e40c0d03860503510400800c2c14040c00c403c2401042d00c6014170b4005410074071203a14001e030066000001c1d1030b100341d0900600d52000f543c0001c45504484d040b215035255070315038101d52481403076803684280e0007500c00400c0018654060301300d26801e0100a5040101d56030340e02003190103018030b41c205030005069064284500c1046208012003c09140742910203541d50840381c040e0300c0c0040d0303003203c0b000452001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 914629595 1250 914628345 914628349
    0x3180503220b0d0504060e0f06040c050105030c16080d06062003090d020d0f1205192f07080304170105010801050f070804031806030905010c0c030f0f030b04061202 72
    0x45881840d003401c1c846010315003000742c1c10401d401104441203c05030740e0700000302402a01c1d0401d014401488003524040c64048461079110481110140d40c1810700120029543d445542101d20840788031000a0401000388482d948450a41e01c09640b6480c050081007080c01c854880e54000b0140343d10f840c864544c10b454000c0030030803c90840e42d0305801c14400804039031a043d44404a00e43d04650140080c01607185c83e5444001018001e001c140c0140d001e0164541c00400600043d000111082c19510713003403030122504281044008102000d1540c0741c4154035010b14821001c04814058850264445500c02c3c0355030420f510880948200b0044102c0c05a000e00c14035000d004c8600080c421450302c1403071718140c110040c05080070025580001424180309041c0c4074908110708100550603903844000501a00d440300c0b095030994a0960002c42c81801258440190740e490380340c1d01c842c45226401918240c0042c91000245500c54449522070b80d52481b850700230304aa80e010360305480140c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 914630845 1250 914629595 914629627
    0x2060d020c1006141c061109090a05103506010f09020405031e0709020d0b0a090902090f1005060309210301060806101b0507080c01020706170703180503 67
    0x1040c81e07514640801407184629072450711580e400192001044041c2817600760240c80009800a059245840041881440d011008204100003240c0e0b9012030384900d445030044039010344007500382000e441d10800580351041c0c0e8425200b1703c1104d40800c044203e100c2c0104418045140184a401c808018001c926510b0025000b8210300e580450134030f401c000200eaa50707225950103d03007000d1094142d4240f808c0c02c206c200040c10420780155290b081c82c030540f034058098420703517a100b980c0d0341c0d40226584107548540100301d50000d0003105c0a449012201042364000b608480040304003400201d525100d1000850207031007000c0061268410000c3c044c1c4a25502070304840020700100010000154002d41c4280c0141d01124076402e24041c0410540f503102106c02c1c154814440030710060144107000c90f0100c12200010701303030740d54004290012a26401c1c103001f000d01058010910003e4800e40c001c84607400100c40c01c2c0011242d07295005004a15524502112264000504d07040c0d0a41d00714 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 914632095 1250 914630845 914630863
    0x40f050d05130b091c0b0103170306010e0409050f010c02150115212007060e01061208070c0302060705030403030201110a0f050304020102100e030901020105060f061e040302060d020c 80
    0x8030380700e4103082141c00c040c2c5105885115401050034013246040f8240d0360561015141c1c100c1c4035808030700d0760540c60a149040070134030041c0d071030318012070101d8000345441d42101e119883c140d440300991101c0d101004010302460005039143d00c20342601916441d0240310b403042604050300209081c500c2c00052100c1c481d8160041035200101c440b4fe891440d41007800000704942c0840600c010040b0702c04214028a117400c60342786200c00800c140c5400300084001040d032540145410702c50900c80b06483c900382e41c2180b10302c122201303d15513074802141d11a8050001180710f142d1664250350340303400040d8290041c841c16101900f00190030010103130244500c800b1404100d207020308006104401400340001c046051052000010000302168424400c80303022800808003002042186841d143c0d0b242c1111150a016610701004150145440c0b801142c2e2040c006100c0e0340762001d0501c481600c48251340300480459003c1c0400302c0180c0d10f20780038143d9804400c0340140c0740e40b504000e1601d402040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 914633345 1250 914632095 914632097
    0x9020a0e0f0303041a1c02040f03060e01060b0318010b030f011401060804050601060c03110d0f020c0d0b041e0b07030c091706180705040603080409050606122a03040f050d 75
    0x104020400c0c24640302e400c0002c1d40907445c8042e01e0310304900842101c0107030b82024202d4144009800310354910100d20403000e480c0500e40401003181c60045103402c0715224010060502c40c1440042c1c5440e0b40001c01d9601000c00000101e00300d2050303404249012200522480d49075111400500c0c0a00950f88403401069241381072030560900e82c40303283d12844180100410001d030f0307190a80900d4051040f20008940c14000c807001030030b0700d03c0020003600102041030018060900c440303540d860140f0f081840107401410301626500c0316564112000f01c4582d50703030340640c005030b1150041111011080c0c421403440d200801d24403803800000300141a9034000c44079100036410715034a2540001003256002001c0b1010404080c002c001c0c031807034003d083e489581e00c2800c03e40f01200b0000c041014108482062000744410307100e200800542d80a40d190000314040080c0010311005180c00daa0301c0c0c4484503040c1703042000f0420001d0809580200c8081e14003101043d46801042400c00201d21107a040d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 914634595 1250 914633345 914633347
    0xc081807081c141e2a0a02040e0102040501020601050f03071a0721050702041a03030d140f04080a03020702010302131d012309150d14010b030a0309180609020a0e0f0303 74
    0x802407140d5044080d008a42820744c007084603581d0000500d104200082c0401d0050080002d0000c01a43e407000309000b02e01640c00c020301e40908260500a40302651016000b81140d6800c101c01e001180d051156280e52612492900003000c03070200100c1c1d001c49203ca2056a91413005080c1001141d5204d01041061514400040421a1b0082c16104220ba040f54007041c41030480c2031801080e0248000c0c1d550501000030301e501941d1030b590046054011850101c079281d0344a44281c0502c40d021940a00228000c20104289511070350040460318030504006040000c410259035100e074280d04041403851a0038a1100401000f11003079005090b03003450303050402c0c80c0c42a550202800c01102074012003034807000c2501c0c1c002d20040751000741006401490100e5160a00e101c0c1192001501c401c19407820002c2c2d035850030f01044106110340c0584561141034504001c91101e00e1194440a8039150b40304070206050703c40e40000c00c03840c10190b40c1c81400c10075007000c0064402e0344030003061107a80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 914635845 1250 914634595 914634607
    0x7020f03242509380705010e03030a0c110c010c03080702030f030a09051011090d030318050312010e1e180a03260f0a02030705070827040c081807081c14 67
    0x62070261044c0c0390382000c011203444a415107031460160100c07602c085c009000100420031f0310241644101d0001100d0341c0c502030800380c0c030780e9125200d103100b50030540041c0c901c050004c0424042e485150700950701e44101d078a0309103980c1a440e0240c00c1610640c22080c2c40d40074200034400c04000c1085900b002020400c0012013492450945115014499028401d4400f180c0700703050203a400301a15100201c04007103495000d1a10544aa1100040502140e45040042156101d5040782441040c2c20440d00342d281d04a1118105141002071050100c4042d024005030a01002d2100080f0f0621907194540c401e14420080c00506012000040074004190b08000c10171001c402c809801101c51000141d07a034449aa0483c4c56104000c0c015000120018140300448000240b150035503070405501c4402810315010401079078081d102c1c2500142c50b00300465418042131030701136405540341c400c440100d981d480c1e90605209041d1117041110040301d0000e4100c42e040340c0d260f01c2d480b5079012020b24100b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 914637095 1250 914635845 914635919
    0x4060b1201030213090605040b1b070506062e0206040c05011112160c0b28120c050d0e06011502010216030c0204180807020f03242509 59
    0x500305210180c4a0044600da610b204c4605070300402c02950000b00074441440d09003408118414240c400980f9400d030b40031160780594840d402c0da00781940c061b021b00f016458400070016909142e884c1e2032000f00010a440180517800d0100240c0b0401e290040c1002c1e10701800c03d2181070074580e0156040c080c02c020400002000495600500e6004030319154882e08240d0030810000342440e00144a811180c0004c20b042170402d028142041c00c0412010060300700900040c00e2802c1c00c040b520202c0c0034182d22141400c0c0c2a0061080641c06181050404100e4132201c400c0e10340e000d10348145070700840011f10400b1071000344045442841d00082d8904404003030514070882c129400902006003540c1807408541e01d58000c5400c41034683d0a1000f0b000c00b5003040c0a881d8803900d401c9114454400e05003c203420081008444510661102600101c00d2444c920606000038a1a0307040300070207040d0a9244c01035852000050b0280e500c1041d61410072890104214483d8040780b00c8801851518545c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 914638345 1250 914637095 914637127
    0x30403020607050f0a0f050f01020a08060d020d080f250206070b07050d150810061a07230105040b0a090b0a020c0a0203070b090a0e0412052107020c04060b 68
    0x40394140c03003055840c0c2d40d500384079042c1074103803a0301c104a010307842c00d00052040c051503200c0c5043c098810394074000d6a60050500700d01c1848002c401140c50b80d00015042c0c6080d801032002c8030b0000c2d1003850303a220141e035000341f241d2040300103450b550004250100c0105000541903078051008914031100c0314140c00284040c00307840380051030084044002032406110302c00f43e41003007aa0080034091860ba44405080d020468014074445100381100c4811481550143c002164007114402001e00c1030006002c25941c090700054600104d4200d01074000f07007a0004a005881503240001007d003801c9c07511485041d00905441c3c0418286100000441d10320b0f100707103030810080b510042c5d8070031110a401d4104010303060042d50501881d1000545120740c400200b2202c9011541278510380c1e10740720034060a84044e500038000e5000000b03a0307030b80640031700c008020800e80b40c500040010200286c85014103c22298080180c0050b030800040c1e003480d010750700191415803655428240d031040620b9007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 914639595 1250 914638345 914638349
    0x4081207050322080a0507090b01020303060a0314011d060406050601050c15070c05030a2001020703122a111b1f030e01020f09150a05120411130911030f0304 69
    0x30254002c001d01c3e41111014010400411103442a643d8101090400c10303128421441849400b0f0b081050f5050340d584040100c034030441d001818a41200d081d601d4620701080210301e0f07c0841d42da60728025800010035074880c0c588688134801040d00b80740c24507256007036510141640d4140401400849420000815280c0317090940e4040700c0d03007a81d240075086500000c0104083c2650000050141a003544040d10843e11b101d00400b80070b1443d2840d01c00c82c01c0344100c8070041d000900da130803401c1c108945500f00c07005001080061030714a10240240e8204071112a0040c0d000c1900c9518001c44014240080b040101007203803501070b8100c6520204140c51221048145100c86414040c0f4440307000750310030803841d0840c5000319207803a11000c10381c0740b56016140c81071041c20080250172801c06203000700c40c802d502903991141030981c0018088295036005e401181c2c507451400c140c2c46075403503455400e050b0b403910401c0030524018030300348000c1101a6440325400394000303150017103100340d0020443e03003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 914640845 1250 914639595 914639617
    0x160c052803080c0705060307020a05070b0405060708030a020903010624030b0609010c051e0f0709020301081903030b1801030b060f030d0e03240115030209030c100c02030a0602040812070503 83
    0x5038410100307010f1820140682c02141e40004044184800142d00203100040907216404a605440e08c50629202600072449400d0340040104101000504910003440e0041d40009026041405481c0001d0035a03c0c076400819801d19040c56240d01500484240c8000c610141410030403680441c01041261103440211070620078007002c95420820100000c8201c0c0511550254a851101e060161580c3c1c5c138440f540340f240305111000c50194064404c4904841141000b4415102000e146038024140c1002c25000d140d591885800703039445101c2e5007010350700f200c1704a40c015030561a044601d40b6001d00b07100d0142e170b80c3d40c0601d2000d442c0000e600380c01c10460700300142d450a25400007480c2c5000d000040710020070500c2c01e04110030502c40004e041e56100b01d5003508200c00d03450114200d0085900311549070380015134403d1207081040c081e02c5500014038104d0100e04031500400e00d41040c4c0d4108032056039002800b00510702e8103000ea0078070385d06d500e40480e2402d0429201c00b40d4074090200200303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 914642095 1250 914640845 914640847
    0x1a1302040c0e0d05030c0f16030303090311010f02120702150c0d180807140312070503101509080f010603050a060b0f09010b18120d0c0305160c05280308 67
    0x4603074090742c80e0b900d20160041420203002d0780e03441c0c466180e4210601400d00e92240e1a103100c01e4900219469007890b0000d205441a42d1860300e044018001049040c2c0621428102d4122000c41c2801010400114007801517500c810396001e06e0491138004082c41c0440d0000d2008144882c560b03d1401d40208200c29501c0e215070302044100002d18242c0c100350b2503910046c03001c0c0c0403c1010b1014148445c00f031600ba21001e052050255101d128140c440b0a511502c1ca0020700001d0150300603581000f851840c0c040c0468584401068800c07407003444502040c900242040f03901400c20220764075040c100001e10595146994181c1c1c0c1b44500400207101a4840501401036158010304000e0500020001d44031565208030180381035004407604114800b40324200c0c1100d0401c0100700d180141804011701000303400ca40c1c11950070070144000c400300070007000100900c00b801240008045e02425a01c040c60380303420100170480c0d24a030008001c000501d42100e076181c40c0000302200b01c0c3c0d0400c02c1a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 914643345 1250 914642095 914642111
    0xe010306051e091b031305120315030708031e0d0b0303070312140f0103081c15090f05010803070311030d050f01210b070c02040b090708041a130204 65
    0x1a00a800d4640015401403012504001c8010100c641c0d1841e601c0281d540c414103031551060035a40341506050700e070050f1420804950070f03001081030500b586010300d0958035511003889a07222a580141c0700111035003180d042540140c94280030302d030010300f6400000d40c82c10304021a461421940002c01a090010100f07001e02c09038119040a20000c030010309480d5960190315019151003440310b48068240e19000c9102021510340004c5401003030350350081d10480e07103160386508080c0c0c070410359001d4145a0001e000691041d41c0a40f0050441d0311640d40c2825050a290404407100b0340c0207250003d003410010026248044206c494054240c50144402000120301500e18850182c102ca00945410100007184c3d101c002198140c0d1840d81d1442c07140034482250070040d0030f10240281401040c0000701300a01d01440b040025030b4030240002c146950102c000134802e580480c2e965020803442800c020400820700901800b20501102202203400c1c00c140010484000303620090040c0d0b520440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 914644595 1250 914643345 914643347
    0x6040903050403020301020307110601090903050f030618010305060702010b0a14060310080601080106031e1a190615030b0a0b12040614100303080c04181a03030c030711100f0e01 78
    0x480c2c1c0a0354000e80290f580b401c01d104010b08031119600360780d44c180034000012680c03110320f005a10704603400d540c0306400c01884480f020310b01c1e800680420350255602c0e0800000c208100c0c00d080c002d5008130041d0030310385851078002c0c0c25070f031003091107520450301c0384410700207811040d000035500c90b810344009480355200200750f50071030b5141e000000c0c0f501c502400043c0003001500028162032040c1154007000031003641564240003031300d00060610340c0d041518041020301d00d09145d400f00300000701d40c3c03042d28564010021102160442c21a001c0c01880380bc4565030940203c404410040d100704141d00d152071425021405640509601e00010001080038841940c000c100207007110200c6003683d081c11181e42c1c502070f54601c01200401c90800010b85c5450b0040c00340c1d01114941c10166600086403640d64008040319079030030940a42c01460500e0325201007000d4034001c5032000040da524a014100010f00202c02222648912200d000700c2500030b511021401140070917050110092050b840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 914645845 1250 914644595 914644597
    0x381201170f030304110a0f06050d0b01121a090108071a0a0c12050715181b03060501032d020f010e0102010912030c0e15070210300507080f0604090305 66
    0x1801c003007984000302c2480140b090b0402c26400c0030b4411641210311594405080c2c410012902c180d0000c24401c1c0005404030481d500f0040c4c00c0c4105140200c581086644403c007100c0b50551b44111041c1001d01c0082181044400c09014051a00080180a01d00000170709010440ea402c0c4104903400f00300c141140340076065002503a07501c0b840c4800041e0743c4410040c62600080e03803e8a04241560400d01111000c2c8102510b00e0b000b05034012034584c698075003403102ca46164100c20800316030360002010a01520036503001e50b11400700c1413955115400b0b9140030a00c09030b250744080300c0055000c00160b80d85903600208800030b0806c6c1c1c00e140100390041c1d004009840340076044503001881e81100c0c076410341c0301e101c41d1440d40d2100c40038030600d0014082c441c622081e580010328400c01c003400140c9020301b001380c155145031510104134114990301d4410082c4100c0070010211000e0107044411589008d41c0c0c0d4415400d281c0f040442c032b001340c0501c0d00c0c4080501900c0c051956200c0240a00d44228 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 914647095 1250 914645845 914645863
    0x10c140f19030e1203150118120c0308120612150a18060c0e01110f070608100807081515090a020f040b19020c0909210438120117 57
    0x3d040d20081481c0748400070103a4000ca41d0724442d175420741d10381c100310340c020368551030031f1010a00c5100d059402c0107401680720704026010f03200c12040e030f180040029440c070010052409002040741041c10960700740003d9001d40c00c1061090340080e0240404500014041684035070495004202c030502d0034009402d0349800d03c07000d0301c1117080045062205070081c4441840000c05c1e44e0307601c81c09030302c404400d03226100141e4040d8a60000101000001c2c4a060f140341c0094580f0161a84941c0d1407003041d14049160348400c0300360f0042a00c150890030340300b05440c4d0200c101500c0d08034401240b0000f81140790000c0c0720502c2650b002c2150f2a034060803a00b520040c0c500c40950b0b954a255a481c07801d11502009032020040c8140e0404100c10300340701c14414000e6100c0801080d01f0044092128190b5250024030346110005200c0040c1030007026604890145901c041e41c00c200040884009411122058096096004228540c400d40c00904c2540c11905840014005070000880d5141404404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 914648345 1250 914647095 914647121
    0x1c050d050901140a0c020901050a06080f0603160608010e0109053d1d0a0c2c10230f1c022107030609180210021e010c140f1903 56
    0x804c13001046604504038440d024000c407500c01e0301daa80d0750100400440ca500a400000fa00c3c40b01203540400100062a00000c00400b501c2000701441080c0780440d625521890003e00000e0040041e5402c403a005409448008030502591610403a4240d4011401c1c500420750b0151034802e8880380070b60f030f034080d109100d41076682041c40d540d41414124040c82641007110428101c1c04500107907468450404a13140548a5123141c00080e480707105c070303480a82e8154448548000d1440c11503130300d441d039080064a07280c562805160074590950800c403034100b01071000e08401c00548008048107001e462602c0381c02101919440c43c240075540103030003031541c4000003c40c29001d09400d960850101845082d455400300171030f81c0c0e91103200301690f0200c880c10060385c510710001405400c1c29080d804025415004071040620031f800d0011740c000c00c0c242c581009954804040013134603400200d100100c11404092818040000e0780c03100c1e24829900c03941505040c030011018228080d03040040e0030420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 914649595 1250 914648345 914648347
    0x310050114030f161a0702030d0309140c0604090e0106050a0b0a0807020109111c12091a04080618070f0303030f0621080d020705010f0b1c050d05090114 67
    0x764081004600c14035a50841c401e010305141010714840c0020000542c42c84114544003071890501d600e60710410000e07000300042001c00c0300c500562401c101a84d0003903c41ea0700000c00e070380c0c0350500e90022441300c410f04034103410042d482012039555000f03440c15121114000100b8100c0684101d0041440e40e105d2604010b5919000039201d0002e0003600c0195043c1c0c0710519940c0d1850301c100d080ba4802e40c2d0007844032541f2907040c1d403241410803400304004c40c0d44040c1c00066455844017a180c4541890340b000150310303160180083d4807100e0400c1825904c00980c141014100812140c88000080807083e14010100d851824070381c080051307900504018101d1400301d5143d08008018000d0003680209050425000145014550b2160000c4035000807000078804016620441e03181d00c0640c950340119000d1240f2008120b00380300301034002d40300040000303600c02d084003440038185803640e1304151103076000001c1c40890320110b07044807009082d2903d80d0744c130f14044c001030780c54003501c04c000300790048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 914650845 1250 914649595 914649599
    0xe0106030f051509150c09010e030105190c0207030302100b0a180203462705060603061e1017010c230d02030604110f2203020f0f03100501 61
    0x8104101929400c1032040e0307240d0307520018156a00101280c000d110302c0405d00280310b10391480040c114142c0145010151007400f000000d00b034800540380c9220008880300450713201c4250f03100f59201c20174280040e026040c45d6480180d05d074803401401045164645d00c0307815880c0e85030030790b0b03102420804e440c1d0302c2907004424480000f0740089a140700640096400440910350b4640030b030107260441d0340c850884c00e900e0700c4a0542d5103020050a4081030301c40c4440c5403440b03081c040d05101c0008245d15074540b0130981c2000c902e800c001a001034040d801070070034400c024440c03004103a40a1511811440c2071340718080d4140306102642c2c422003068040750505485080e041d08499864129550b035141e2100c00707400012400480129410855402000b2562030100d45402441d4005401440026005c100803955a025032040b0107610b010741001070301d502d82101004414444940120a103207516085a0108000f10300c1e1220a0303200b203202d02c129403801ea40401155030090310303040c2c003800156 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 914652095 1250 914650845 914650853
    0x5030c0f07060801050a050103020a120e0f0118210512040614070207050109060e1c050102031f05060d0513061a0f06070809010c08070c0b130801020a080a0e0106030f 73
    0x180e000a512503039000e01e040026582d0711810050781603a00042c291000a490f20f00190300070340c00130749013500f84840300e1402c007090025071183c10340101d1184050909600da24800c01c0c21a4811102080000c226201000120b401c0c507400410ba1307100d07040881000031512406039080d0040700305d14100c40540000700001c000094120400340405040c0c100a2500c41703003400c2c1d8440406004090000e0310840c0100a0184980c01e9802d16202c040c050300e0070a1506d162040120640d90001c0d2000c4e9000424020240707a000c007554640020641214512030510000460300d02c03441c2c0c08030b0740c0b40fa1188007050900115240000c109644090200b215006400318407070404030f50b1504910520041003402000d0420b001201e0301c0951050b0f0321442d0407001070040d184002c1308202914108004c2c407000001a1703050094001500240c440d042d15240d10000d007030a5000144c11440440e401403040031011034000e003c0c04e13080040d010022680307103214111a030040c91260b001405e105520b40c400b030280 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 914653345 1250 914652095 914652103
    0x2070c0801092001081311040b03100e160602070905070302210105130b0904021507150b03010f090503090d1407090506030607030b01020604030e060f0301090c120e070e090a05030c 79
    0x43e41d09000c07907800c1000c0055604160442c0c211403100070841e0071200041c1c01a4400c5981035008000203400401040400e2828203502c014015041d5103041c8000a040100f0203400c210007040068a0b08a061902c020f40302c0c1c1603442101d10440c1c40724041075410780240c054801c40601481c0b414020360901005258051080c031600e80960302c405000c01c5810340502841021202c09421625107031100c1d400d00075686841a0361014042c4d05205000c0001d4041d035000700c1c000410000880d1f000481410075085419124881d0000d030b141582400c00640044140c510310700040302e0340040c480d07082c18021500b80c907010048009001d216004201010030364000ca025210550407103485584503e0250100d91419444a0240c3c3c0090005400281305102c400240c62020b003506060821800768041d40303030000e0300712802194a404480c0c01e116804540c003006074171201b90034000310f0b50700c6102c03640b50440c2e8000d07100401503081c00a450a00c0801c94504401c0c0e20608499945c41c8041d030090300c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 914654595 1250 914653345 914653373
    0x7090203130b161b1e0803010e0906060a1401030b03030408071a03060f0d030e130e061e010b0a02071809150c0503010b090d2406060215070302070c080109 68
    0x800821200403c65215000d00038120b030882c40d072255040001032485a121584d180341080390011106208000c840150000c0100346920880c010b58072541414101012000001c104141543c031010810955a560030000c004540c0d07881c850041038400200120003910b181c1d6801c0e5018400050b0018060a0020b2400121850002d00b09044800800303111040d2000756030a9900840040d182d246d1841c04001e920003042c420304003400e03120140c80120f48660780b43c0b140308000c1031303650f034000c00a00410702640d81e002c1e800d0245038401600d4801411450380040c0114510100d002c2035003d6458002c009210103054441290f010710426005c40d20040c208004003100c11503802880d000d0440003034090742c1000450341e01d50a0030b503820540601c00c0394002103001070740000065010008210748130054005816004a248156001c10b070341351054074440d50002c021540b01c0c603040150b0384003408403e0303046069450301580e034502c0c500780a540d06c0c0d10743c0c10020b1254a0040401c04000c0d44400d0f0710b030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 914655845 1250 914654595 914654603
    0x5071118040c06030e1f0506185b0b040b18120a081e0309010509061807050d140618010c0503040b04230a05160f051305090709020313 59
    0x1008405180050742c65401b04000800c3c4416036031100c040d001c0140d0041544414041c007260004400740c0c0d4158880e100c190385555440400e038440c0ca03000c2202c0c04402d41810f011181604009405684e42c04001803030806052440480da000103098056001a8200401618103000e41303460712100012020352200400180c41e000306510105541020000920354400c0d41014040c0c011042c0c490518a5008103090301c41c0300f80b440c0c03001c80400100c50113503014184010000034a0301d40441c0051034280c001c0d211000b81f0280d490805001c0000041c6042643e000351401a81080d4500e40070316843c2c8400d9004c401e50048400304003c5102c00b00e0070120400c8404024000803c1035803080e01c0602c0195005000c0080310000203001c14003180c0d1440f01800030136002007080440404541c03d1042d80d00c02224550810f1142c840d00c030345010b07141e1000d0016221071407009460711000031034184282d00a1001c1c540c503403000031004841844468024880c440041d0b569140c021705001c610561408119 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 914657095 1250 914655845 914655851
    0xf0a0e0304050d06140106110a0303050a0908040b180406140103091b1203080c12060f120f0d03140601051204030504050a0303050424020309010507050a050d05040503100c05071118040c0603 83
    0xa502d0312510411003041c02320b001134120041103807000ca01400000780350b50b0b5a26100c54401c0009420480200f0007402c280d48941d0b1a110519655a503a005041400d40310350304050050040208140448840e52403d0a000800e1143c40c0390100300e40341003281c0400240d840c0c1000041c810740c80403410f0447c0b4403e41e10310105540d040004400c2d4040c041000402c0010107000420908040d008a039070340f00001c1c0103442c10010000c8862400039450f0200350342d90851031060105c0c9030940115886090311810405491a080c80003c00034080d403c968a82e01251201003070038540160b045802038503000c1c1c80f441c02280c503030a024205500c144100441c0c000c100309862264814110344400082003076002d9803901b5100401100c8c25040000161058015000c040000034010440c400941e0801e4454644aa21b04000c2508201025103001416414064100840c3d50b2050444031029401544244030401260100718401c0e42c5070000700b0003000720000c0c4011f0090449911003141d07050356041c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 914658345 1250 914657095 914657099
    0x30615080f1905030903121e1806130806040804180207020102060c090102391e09040c0509070c05190b040f030e030d0c05150f0a0e0304050d061401 65
    0x249641d01e9031416940d9554208a4003089103405512034418180d000794212030504900d000046e06181c00c21070352010ba0100040d4147d84003014410218165071000007450501840358035816500411781c0310240705d05400500c6000424a60310900d01420950341190b1a61031700340b400070480c0d44140161090325814003a482150303069402201c1509606901402954a55481041c06504030b510407606502403010340f10898040314410b91008860301070008243d02580f0020403c1da00040c420382d02440c01d002400d001c404031400c0340240c0585c155018107a984e100d05002c000410a90415540644c14409018405510001c0160518002c1080e164668070740301c038070b03c6081c80700301d401003482c0340781000613011402a07007607001824001d042803801140c2a10009040c50700002078000071a12462000c030501400308217070714104000f90840c3c04070341400d64100400340307030003810f40c0d00300b54484c4e201091051080c02075400404d0702504041400ca0070385441c00c00b07000f26801c1c809000c0180381c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 914659595 1250 914658345 914658359
    0x1509060b0603010b1605010b1e0a051203040b0a02011d031305040e120304020414010e040c09050112110d171b03090d080c0c0a1d090106050102250906030615 69
    0x11a8100c80345003109524001c1245c0c460b0900810f0640d0075541135590f06400343c2d55880302c48403a00c508081000c001d00c07203582078041000f401e1454101034044c800403881d4989240e8008119000d9503022444039071900c1603c50300b24050801c10124220100c0406a60820343c00000090071994200c141d0065116403100d040c0011644a881010250b9204c84100300c1800b080308001d6400900241c0040f5030128500c0418040d032000ba407007a030380540103204200510880e501c5440c050a55128140565403501818500c07140000310003030804c0350710000c007c2c07055540345101b4910580c025410f0414111031800e20b01c3c43c0e08550051154074282d01c070100c1c0000701c04404c8501c03d04000b0040c100a0002d40c64020fa56004602414028450b50325852640d54647d91218000e042030002c01c90b0042420090a91050024080c41c080c0da040204c10702107aa000714104050036036400303800b101600052600050130020790700003071340c45283c51004400d22030144c1003080c900340b4543d940c00303e00e0340c2c50b94 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 914660845 1250 914659595 914659597
    0x40f0204020a201f111303111507021509030a06061e080712240e0616020a1a0705090405010b04030c081f020a12020c010c14040f0317071509060b06 65
    0x11300304d49003084040d84890b03511344d168481ca0b1064004181c850624034004076456500016810984041d040c04181c15058905400c04003400601e0407506401c00c0b506501090495218802c4065501b4003c03076000440d4804100c00c40c050764000c0014040305564a80011700070380c0c005c441c4441c01410b808041544000051000219001390340214400401a114100b6151280006001d0000c42024080c105052070140403202d8001c0006000136050072245600708001100364801076400c82e500d0b450100b0070396014000c07551528417110032555110002101d1501c150304003660f02500e0f210011461070002030141066030b102e2030315600700304c2d2264121580c407840d400c80000f55800d41042500b501c50290040e0211400d03a00f0121034a4955503103030001d80e0402e1a1640c00c2c0d039501c07002c1e400001d6022050352040203090310310130300c5c107401c0402c50341d802c5c500c03800090308140d4929511070748140524203d440840c0c1040c0c1010010342120016400360900440c261007141c01d00ca00740700540b034408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 914662095 1250 914660845 914660863
    0xf071115060603060607020d12120903080f0c130e16020309150a0201021303060b0a090203070c0f02180c0307080a0501051c02031e0c03010609050618040f0204020a20 73
    0x1000d00e0910769148070800800d640010442d90b0410420302590005880f646282070307941d4810308400d000c0c510380f540005c00c074944518902c921181004000c030b000c41d400000154003c102e01201c1941540c40c01c1c2c86101d28450201051324880e02c80700c0008010680d004824022030607028108098101000226a24010303540110b900a20585c88040c031403402c60300400007101d8500000d81808500f40c0464007500d01540180c0d0500c1c0c0700e80096000d03291004000010b0b00703808600314114105184001c044014803203008181381e0240b1981c1c01556240d00e100100c1c0e60001c0159411403901100781b400c40e400544611000c01c4056001c1685ca1040340201416600040d21228010802841c0c03040b0780f0207046070582e01405141c6010316280701c41d8903815240c000010041140d480ca0400b030608560803540321426092400c414818507959041021503020000090340c400f0740c0f0399040800416800c01c100035030252001030030805d801e4010b1502070500010a1309106030a45160096803500703026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 914663345 1250 914662095 914662123
    0x2010e0a2105070810020307031506020c040b30060907030b04171c0209030f060402150a09210204060b0309120a09030609060b04111303110f090f0711 66
    0x5441052103032540c1c154103918500840454035669541d103003680c00c21442402c4140f6840e00001006600b5805018201354001d000c46401802d6180c844006d40f10591680e03180d04c1151111071114050b0345c9c11184418080d040c804a500301c00462582d100c10240e11113441c50180500c90000709191804100c0c00b04403504080c0010007580d440d901c41040170b01150300700c2101181884040d051203415142c203020441c54550050750340900d48109450911200c1e4501c00d141e100804000060319207203050320f0078000103c1029150ba91141d0251021940c68002043d0648a101824107004282040304803003070003074604000c229101e160000280c0700458040c05507500125030240038105000080031a106c2626010079840c1d22940c038074055a00003d019a0515241e40c000340d41841c0c203100f88007444241d9200c061410b2500e104910300000207101c007030a08000301c0c0c0b2811140c6c940305803108115030020521103442c644030440c0c00100340166088400070360000300a88105100284045801c546 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 914664595 1250 914663345 914663369
    0x32811340f05040510150c060f06210206070206120a0f0203090a33050a060b03060a1404140a1406010203340605070207080c15090603130203120702010e0a 68
    0xb040280720141502405c01302d880c20a603180050060303207144011860074400d41e1000070710381c0c050500d601a2100c0b80100c80c0410319002c001c2201035681d102c0d00d40c112100000354041c0c80420300020b2450302640e0710280d007041d0700061049415011600fa036120b2403212a04008181005046600b03d0008030303a0043c25900021003076010800c00403040c502028100e4241004168031400354004201d2840c075005043c0d00c401c10311030400380a00541024041c21000310b0b003180707484400983d1640320341c41104400402e050107035025464a0704040d07074540d00904201c01904024840d8801483c1c0d818003000078102041c0420402e41c1301008a0380054420440d5403450344100341140100980a0724003040d0120a003821400502e543c003685220752a250050482a481c18100c03074109149105002c1c8a4880500e4041101010300f080c0d0703a00d001d0a4800c15102e030740d1142c1088440100d1840650f151003043d01d1a03d400803800000c200007807003a82e40300d1504003804d00703106440000c2d002e0302c40307070000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 914665845 1250 914664595 914664599
    0x18030f14010509280309260f030903010b180c180a03030e040b010903022407020d030503010509010611030703050d020c0106090204050f041a0d0302160f0e0108032811340f 75
    0x140b103500090b006080103410001f01921300000e28005402e03054050642004c181901d02d46802c0c400c1210700700090712480b00141c400708402c1c564a0000301070024000740403a042c002100c518040071030a038005010429040e03242d04001d8014000c0031030503441142814010102544078071281021254054009a0a07054000024185041810781c42d09800d206001c80b0026a458888620485000b521f45540d02d5050005205420005810040c10302c14003007e08450a03000004aa0318941c051922948130350210158901038070861032900304030740c2841c0c40070550700e00310b41c020811288110703003d0240202e003c041c80300340c8940c0740101e00d1080070b001c9840214101020310f0900e691181c4151120304409244100c0e8007101600b080600c5840c03204144034400d055020280500394460045003810704000303031252031003030010355642401c0340780141c07010041c011455061401030101c00d0780c00034210002207180c0707503018000c140410344500000040310803e8030011070650701002480c501c0b01d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 914667095 1250 914665845 914665859
    0x100905010902090f01052d0705070608010b0d020306120a0b01060206102601060f090b0f040b0907230a08061f140f1308060604050718030f14010509280309 68
    0x10300f101a003ca2040b80782e21f410300c1c024a003000001c50000707051b0f4090713840d144241003461071b028143e00140c0c20300402c0300c014422401d0301c03816030382030709039480000da56981c3e400041341e50098426070090702446030034517100c200454210799070f0503288260f007220610344c3c901c660074003046018450100452100c10001d010040514134500407040c0d24800403e03407035640e0b00c2c000001c0650358010b01009030f41d52840b140520304030b10040b0034000208c4050000444490001d01c011002a040100b40300c0341040040400c07180d085004400d400310f18410b9225014160003400004084401d14890391181c2c010f68070250100603800300c156800c0d035484080500c01602e0b29956030103100141d840480510410041c0855003d005c4043d003011f2020300b0090510f502404180c58002d4824410702640181521041d6200710782c002c222600302a4584801149042407212130340d9034840241d2035401d0004000e56000d000850000000b104107412810344103800300803a080c10844d0700100002d0000714100500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 914668345 1250 914667095 914667097
    0x6050f0112201504030c0f0b0f030402030a080a03091416030b1506130303020d030e031c0e06010e010305191101030c0e030d080117061905130605100905010902090f0105 74
    0x10755900c2d41d8041101c030300140020b01c40c07506603140600c4064005800d1040183c400001401032214030108810281480c8a5031542e00890507004076000002c400a0155074041050801036901700d4113855480940131002400b910105000792101c000c078110240030010005a55030794200c0d01c6940000e81802c5640b0440440005428000c6041a0340e803804000d644510007440f8216400c03131b0784101c040c0745240c041e003000da040300c0000134585031150b5090301c000041300b201e0400b41501003501d0020018189000105500d4a03a40f00910540001080000441c164107043e03c5c0940c040b02c0f580504816004c1c400f0401c4c130740040020300d9184140e101d5501071303002820700c52071038141f8035460052000802c1ca803184c200740200c00034414200410540d8404101081c02b20840b4000d0001031070074260481c0c6070f104a250107080c1680c1d45000410141ca603851801600c0da000805003c541005094011800402d00568038241d150000004084105100301c0e10304c84800b41c54048164541d800550396 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 914669595 1250 914668345 914668373
    0x50f0603041b09270f0201081f030503090a15091215020d0c030608010e030415170f0103020411040e0f27011a0105130b070c0f1206050f0112 62
    0x300204080d2182034019002d2841018120203400041e22003081c110548828001058aa2402c5958041e05020031102c5151041003602800d05c500540c03282d103006445842d0b040c5107040d524440007008803c0140200044c10814400c68240c1005030f1507040702c16a2074000040a000708844520420112404000400c002d6000311040017003003481c1e03000e2005a0784402540100b1958480c014421180c1500c2840081c019242c001c003c044244c112a07a5039110f14010000b21044104410032454401c00c884a4400c10003400c4190301d061103004030b61810800c0c00200d00c07a50800c070581400449030002e40782150805010300c0101e440b081000f001911005d020150042101d001d00c26203004400200b20840b0701200c000189200902c07484013100c02040002810010304114030b90314070944407602000d50310482c030302940d118028a40300302c0040aa43c8480540c103020100004c410b100d1201c0885500d02030760302803040f55500004490449824003442c10600180501940400c602c644500300c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 914670845 1250 914669595 914669603
    0x605010510210b150310080c0d030315081905010b0d080403110d0c0807140603010b1b1507031d150a021b01091b0603051b090414010924050f060304 65
    0x2509031a02c90100c0d0340020360b140f9080e13044200005020414a64503030000040c03d12401510341450030a00040d0f5200c0b1011001d0300300340c0c4a51208100c848080e0b546402440d44508488500c0c0b081d21012644501a0005075103a5180260030a0a405c041403c046074540c40b480d110b10785400e40c0d840a281024499249810500190100300000c1350580311030060004840207103045d0385008526a1601e420202490242006100401c4500f81940c195010400071084400b620390b60403064034a860003141e01c0d01d01d1481e1003001e20142d181c040d0720418082c00d41d4441a403070b40c006040615541d2741e1941c561030200f0680c1c0c0000701560701d26800b81c014500c9445a03e0345454081c1030311400c3d2180780340182c6003214124bc4201e0112840055503004020600b01400f07a450602d40b0f141c10106800c01c10b940203140003408800580d1154800c0c107001e20140000285941c6500d110710003400f960760000541d1003881203241e11078080b0b861710030490380020800c0e01c1c1c25009200317100868101810031a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 914672095 1250 914670845 914670851
    0x1050f09090f10060c0f02010e0628030f09050d08060103060302040509030c25120f150609060501140d090203070302060f0307030606090311091f060507060501051021 73
    0x403140e0301e40c8503082c021124640b03420081d04041c0304150400140c1e03440360041c0800d454440d40001e4445900358a00d607024209480300141d003030b0102c1c5031351051140803243c4000088171400c2604403980c21142403460360742c0820545032a10840c50840d40d4050b4007030300070b038040d000c241040fa1103686582c0d40800f041c540070610340c0c2c0e83d50105003682d01c00d58650b03000303400c08588003c44a204004c04a150782c100f01556040300d403050540c43d81e0141c41e00850007642158400c1d14107001c0c0c440f030f290800641c40300150102c048081580d500030702c098068042c640742400c4000070198412800b20100d0000400458078045c0c141d411341d00240200c11080b40c140c05504400805039a414018000711007080c49182c0d90727894041e500904940302c039005441403100c0843c0902c00b01e60b5000114825080a59040da950788949402006c0c0356065080e045180360040004074002e40d0003270103000003601c6000f003880b860740ca60040003005840d00c0003820008070719000c0c20040c0007240c1c10000740c01100d02000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 914673345 1250 914672095 914672107
    0x4d010b040e031e0f1206031c020d08100620010906050708040b06040c0503060913050f0c0114040b031909050d11060603010606050f130b1303030915020c01050f 70
    0x440c059035169200600907800215403031400700c04440e03405840310210000d1501d850700303440d4207010341c0c0243c2c4440e48001d803480b80000c242e41c5042114600d0b038012507086403907a035100c0e00000d50302c0120b0510303a00000c000d0404500343c0305030603200400391122038548140d440c03540c1002c018402013941200041d51348030b4403190081080c9204d52405103241da074428081d0f14050400c982c00c0980030300311034003892803c402e14010f25800b07820780c0d4100004655002003500d035955000031031442c81c0c034040c1c828040e5602d003c500703900c0040e8516100c1c2d02030320fa100369013260306064031682c000e41c85002d043e50780410010302c40c1c4101503c1580d5285600c1d00024902480c3d07103555107441c00280410001c12031000c00440980020001d16034032a008600a0001070304100c0c00030142c6c02004901030340f1504c007040050080c80c00d490340710094019000b22a8503214084c0d6031810920781440190003250703078140c1c045070607101a50b00b400844d07602c0d00205019590f0b040112940d6211890040102c4d0082c010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 914674595 1250 914673345 914673349
    0x30c0207120201120c0906140702011d1809060a14100b2a0a060b04090c06030510080f0307061b0918060e04060b041815020c030c06074d010b 62
    0x5c2d90f18211810f95640750124200303180540380200034050300d4541d28082c008040140c1c0d104807101c80303903201d500c00113401c20000c4020400000502640c3c030f0040d0b0420741000064080022f600c0d2141c8503e1b0414490310030000a05010108143c0e040700c01540303503a030701b400110007550049c5400000e60b03140101002480078030300d140100e865007521160300322021420038405180520700410404448c200304100040c0c3c0d0390400d595142c81600306140c0c0320300005110314030341000b51000b804404e013518525070500403040d499a0203904221000f902d030038004000304d99072010181702540b89881e41c00c070407424044c0d40101030045501d1b090503d03844000220780104d100003d28026849007030b021a400700c00b501040140d803c403ca03620421664103c1500201e480c0c4112100d110306d80381d41c0140c4da03400010b00103056100c2e60310941d100f0300c641c005202416600484081311a188a110300b46100c42201c102d0103d802c0030300c82000d9a910542000c4121090504c129194114101c0001a48440400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 914675845 1250 914674595 914674601
    0x200603010e040b0c1206041a040212010e0f24040204030f14070b0c0a02210d110705010f05070308130b010f081b0312030702030d0213050f01030c020712020112 70
    0x7804080508240000c00c0041c60350b0756044038101c40007500306001404c024071207410007040d042c811a11200070380b25141a4807482140c50401038819580c42da21040c1070300c03c803802841041e104001c15070010b404c9400050b4442c1c001c00110a00d21140c18030f5107440100d003804c210340c456000d0740c00c100010010324103500542c042482a0510b20b0b0306568080c5082c1480c100740d0202d2f5066000304030400103084040380baa403410b0783c101c40c0f8030b43c10300c80b0303c1001c0144007030110700000c58441d1010b01308051b90001076856484040c04201c0307203865200d400458801041a2240011071428018200000c0c040c4034503551091021182c03490130140c43d20360f0b8488541c01c5e03002c4011a1040310060080810600048121128511591582c8238028010955035003c068080514041c040b0100312003d1090085803010a03141400359203d44540700d400001440c1c40c0706842c0714101401d47d0701d24a5001c0e0244494038100c0f034000c1c2011500d4607102c0c004038580c13482c0403410040e0350101c8025000e03045c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 914677095 1250 914675845 914675849
    0x141903020907080c2a0c0a0303020715020313060503040c06030b090c07080909070e331315031508012d020904020d020307030605010504080d140c0f0f10090f20060301 73
    0x1403000c5d40150240c511a81c20a06d1510900703010302c400c11014000309400103500011075082d140e00307165142804a00302c3c254044c0f40c00c00c0100e1081101c002800c2903005002c3d40c011800381440d040d1071603440000390100d46420f001076810001001c0000c54a000c0403010340705082c0920703480ea00c3c202036a4005070030664121003000c041582020500d5050501c22903403072003d400640c20a442012a4080c901d416803440c041d0400860005000d211a1440488080003051555030903034601c0702403030000d805043c070b0040105000901100005d4007101c14011100d45003800780310f80c65000d41c800001001c01d101d4219251665408111504103622584020511480400d00058507070500311001800d450490740440d04110302404180f01000300410a50b405041c1070a0082c04083d40000c6240315003d03000c2065400e02540020712100c04002c200125015905c100741c8a100d400300e600d290440341c04480240c00044444e102030001460718401e00d10100c45080041841001540025030a074000d0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 914678345 1250 914677095 914677147
    0x319140f030a0501030c120203100c1107151409090703320a050c07170702150f030f0718050904080405042901021b0f150301141903020907080c 63
    0x3c0c00040040c000c3c01c0880d00c001d40003040585a244c0b20700d0300000d40c0c4c1c20183e05040c0d01a5510505640f889025502c1001e01c003c3d06804e07201c3d4160f43d03a0710303d0340790720340180c1c0000440d107000b01210716100050704407a200b030001000c0c0760554031048011402851526030740c0c3c0c0d08030804100e0308801c00220700d4245a50a840d044032145142c501e10311003c4d5800903241c44407000040c0060b80004482c04010000c1020301904981c498a550001580b0103101d981860703038020000510010300c4090a0041d44600c0751800d08850a441343c100c126110206a445074200c0220080305008a1510100072030b00300307000c1c0c00d8141c01d180e250800501140c4403104071081d507121048080d800c041200d0702c48a11090240054031201c2d43c1800240400c00841020900c02c1481a032038000c50750b40c140442d86e20b8441d00c00c0c80383d144e68403141507520034001d00022600c90076140c030170080c0c0034003080020020740342d000c1c00c00102d60f00c60740f0060b508440094140a0508014400240600808034420002c07180b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 914679595 1250 914678345 914678351
    0x9130302071a22080d0c050a0f0f060b010e2d03030a020d08070c0305120a1b08010504060f08150921040e0f060d0b06181806090319140f030a 62
    0x2d054030b40068005600f01c1e81c070b0360f038810705007007000c0000469400c040c0d02650420b030f00d010f81c01e0f14155041c2240103030010030034038607182c890051119000e9240880b40c410f410800c4025140b40054440e0105a26410f03841700d040102e2902c1c06a40440e402c0203494032030151402e00b504d4200090850300450410300040c3d01c040c030403440c0c0c2c03030380f03d0000d83d0030014904068404130352a46000f041e9128841d1603c441003076520104191004a52000c480300041702e054020951155400a18051080c4501c0340300c1d40c1003120201d640700b102c202400441c2e00d03c400824041020790b0403860035400040a0030014001c00304004201c0500110039184100000d03080e5949070b0900205a40d030060103040090f609030a102004210b8807062040c03280f0f40c0e008402c6d008266a400b0016030352584c80043c0c08045a0003200340007401d230103001643e0200c450b2005850303050ba0f40d010343c56a40c2c0140c1140700341005644007000f483c0380c01003503a090803a43d040d440915080100080309403d5009848211113203039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 914680845 1250 914679595 914679607
    0x70c0b030a050c0f0403020103020a11060f0402100e0303250b012c040f030309050309060d05180624030c060c100b03010b031b06040e010611150609130302071a 70
    0x1240388160b640c0311032076515403428040110481d05260050f0701009040c568009218510301e4000d03d0761546090303000c4202c58481c5403200140041580541d422409540b03464142503045019039528216180041c00035420b24070058121041c40c0740ca0400d049a110034400541d000c50010124240a800c03124840000784000d03d490002d4030500e4440600c04500c00c10600c00000d40303056068410035010b25010602200d107080050842c0b00c2c003503505512800001c0d01040c00881360300142d101d00300c440d0440e0704800f0a030350103030f8031060112482c403452a240200c828560130601d00c0410611000341c211400340d0150320101d01c0640c0318406868079a030100b21040c829500900030050b02136026802170050150520219581c6d14041800c03900c186040c2100301d0f45600e070401900d0082040302408104c6507583c10010303041c0701827604010424010750038250842c101101c14107014481c050602d007040e98481280344905040007808408502a842000592400c2c41d02c11482c031487d8403915641d548 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 914682095 1250 914680845 914680861
    0x503250e010e100801050402060403031d060307090e090303010b040b07060e1516210e10140f0c0f07020f06070606060e010207090501080c090c070605070f110613060b06070c0b03 78
    0x1150f0158074180e046c801004016141c40080c1c4040f60340c14101006092413440480402c82c001e0310310f698100e6004000c11104643c40990303242101c211114040c600e4584000300c0341c5a00c0300740150b0710000d00c1040704002d00341c0400c1c0102021809040b0008009509081490428402c3c1003400309024002d4280041c495401c9601500e103201828103080f51140e01d200341ca151030099807101080703503807050340c00c1001c58240003400d0070801d144c01c10004584001c11484c4007200c01c0d0340b500030052410001607100020a0111050607980d54040d5003048001e9082280354418940c81903080351007848030000041060003036901400d41625442c219103c400002881c007500f96100d4401c1600b040d00400a01d840446c03c0c11605805840900702680c844415140c948a038038002480c0d04e10340030030008455400510241c801000b51b4407070b900301c0c03d0103602d96a0303400107488008480110703003000c4000502c5944004000d800203091581029155201c0c280d5032544c65114861408000003041080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 914683345 1250 914682095 914682121
    0xc032d0f182707020c030a080d050708070c0204050402010c061407030c0e0105030610110d0305090106090219031a040f0b030105060409120e1f050a17010503250e010e 73
    0x25100b5601d1465012070051070aa8801c4000000c084040315100824441c510a104a5a034500081d080750000d1019152031403140e17018030032480f0072524000100320818841d02901d400780b80f240d03035030440140140d020480141400703070040303040c4258281c81c1c0c00007590500440600c0075400e80284400c0c03034140b03c06000d941540f001c600400036100d90720f482980e003040c2a070b03411042c180d9001b00c038a540c003941542c0a00f10901c25108510800708100c105982c1134010703901c0390a545009100250f5900d200209034003a401e07a0400907049090600c8076544aa403100c01900b0748040603400e00140400130070201d07604a0180710000c4d032075801c0c649103800e003405942e0300b016003550708100c0c0441903160145411120078500c2c00b00407514415114903610500e240d80000c1c00f401900c0310550805e00040e02c40d80c0165002004541c11060804040701011002c60480b540540900346219051280b0041e043c07090071200c0c22600380e0200070401010041d02c441c06411156846200c5040001ca140c3d04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 914684595 1250 914683345 914683387
    0x5091005130b0708071a180c0907050a0915030212010f0e0c0f0702100e13110d0b01112d030301050303070809030109060c180602030c032d0f 62
    0x3032020401884005200030341a40302101c0180c6902a1030b040c1e02d01d000350842c443e0b0f04000e40b140946081070380942101110b0705001380c00c0040c110306801d06020240d0745074203150310300300c1c0e010a8001c001500a4010802000c0e0a0003d140c03404446885244050724074580c4299100080d9006c9404606606465596805024002e02c084030301c03450401c091034040402041c01103021004a1a031810898103010342d1038081d0b008050500c181814040100458074030f4103103910403100240302c1d411500c01c0c2e104038824400e40345400c80c6440703914503942c4040c04581403028100400404071041004003484002d804030122810004200502c81c0382030f0602481c2c090b280d01542040004100c00d940000480d4074542c0d002d841070340c440c901d95000a004044098000c0c15079170a200980f20b1241e4400312031401c0c01c0b00010070519142d158081280d40f4081c1101d00802540100803441040c080d802d1102078082c04140c1e05091390030340102c0d00560b6001010f2540e510180407c0b414414020320b485440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 914685845 1250 914684595 914684597
    0xf010f0c2a24050c03040f0801050f0610020606012601031505010f0b04030f082104030f0e030604080c031b070302040b4204030b041401140f071b03050910 68
    0x10b00100401101c090350381c8140c0405040c054000f500f07541410052082d10001c00510300c0543c03105130303201009400703440219100031241a0000c0054440e1a05500008150f1940c0e40101115614a401982d1140160301c2404143c40c0000454010303044509049021354030901d00c00c0001005030480c9400d852041c0c1000e4009602408240480150f002c00d40341245e0700710315500c030746141c217040602c030f00d00c202001070941c191501030410b5421501041d40707006602c266201048a407241c20100e0f4140a44100307a907041e04184082070218000c040988480030100e010b40c0d24040034504881400d0544455807011504024000c00642ca014401d100020f901519845100d2121083d0207000c901008900107044024203060112680c2c9041c0307034103003010b4007c92151703107540300e09051101c4901101e04891410075501420034504044c041c5043c8085140540c04564941d03251401082400401100c10404055280c900350344914500034103150181e2521130b45e512180080c41000040400150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 914687095 1250 914685845 914685869
    0x280b040302190627081c020d02070f2f090c0903010c080f1003150f0b03030f09130903050301030818150301090509070509060f06090904030314010e060f010f0c2a 71
    0x70012400c01e8085030492500e1b05004810200305802d00d00003402000311200c400c510109850007000741d03680c055109240150027015a84031003031130b1121007100604009148800642c54405181407148031030f038000c0c0d404072034a41092100e6010a0031208241080c0c80001c0d11401400b0700d0300c0c109892150403002c50503a80c08440c0c155140c0c110803824282440c144903542d24100141d024485d8402001e903200141903a83da0491041c281036070350444030b0b4141c89290300c1558200005010302c030b050025079158032080d09580c0307562114a001c0d002440411202446d208052025039031781c091003843d10b991490382d5034682d410046200111080200424035541c0b00c400c09010550b928052a079005004a5071941030400e0b200c04036506008101c4000d800144610501c401c064142d001440c803606401c6203403219a07600c594001d075806050714450303007282101442405a501c40c0c51004810403280c03c2220b000d210541d1035000e088244450441c4541c4881c400c514100791141410000307102c925948 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 914688345 1250 914687095 914687171
    0x10f0f061502010e0d0e060d05010612230c0f0706020c0715110a08030a0f020d1b0c080a05031503061f1202011b03030b06070c08280b0403021906 64
    0x90b07a40d541840c44c60040c00100d040d620101c1d03a80c80c00700c0d5920308c01c0010134485541c1d01c540c090145400f004291304413a0420341141c09100030b0540703041e60300781c51240003003940d1506101d240702d69001d24008001a80c0400160000c40e00c94001402142140c1c0014450a8542410b00900c280312030b0201e020460100c0c801030600c000011005811a0840c420564a403100c2c410a001481c1c488400800c1c80d001141211010409078409130b800c4440e103009903c40c42c044003017101c00c070340b130000c0c001c0a621050094040440c032074009103070f02850128003143c0c0300c1e0b005e000092404034121131280300080200a031000c02086134420034000d203242c0b482c49001002c00d500280984a040781c1c4082d243c191241c3c0d000c28584640c00c4180311081c05025903a80b405076080111002b5498060b07070803103201e03000c44440301b03211a60103240410a00e034100c58407203403165680041c002d0054808d40841c4515815021201d450340b50380901c044c85504000382e4051142210b0607044010001030709203407200480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 914689595 1250 914688345 914688371
    0x4081504060533010519030e0c180f13080423060310140607060c2003040f0603091a150a080a020d0305070614012c1012020102010f0f06150201 63
    0x1520b400501d20700740302143c0101040040f50300d4010601e214400c4400c98100340045501075000c046d020a0030310075a48407540c440140f0441c46d00f981e85130303801c800031900002d0008001d4000c07075420410040301800014540c1c0c441610503040380d0007441901c0001c014022044c140c6602c08034440e10140c44003400d514008080c0c80c0422428450338101a1400407a0203580c0d03185800c88a229502c20000c00c200b0060050081040d90042d510f911000c00440e5044100c24001065500300c90501da44000100c0c00c28104070b011340b50b50041110050f80980842e0084640c080f4818450342c405094108036000c942c042005080c420360005185800201c083c0740940c5504244003152901400c1060342c0780921310300740c0300400102c141d5031020003130800082000d030610704616a02c035801c2c0e080c0c03448507518851031241700341c001d0b05c0c14450080d00503010420800d034a003a1922081c0140000117502807100c6050041d1000301018000e901d0313941605111910044c0c05a0381d050103140b00070000000340b4a1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 914690845 1250 914689595 914689651
    0xf100b0f12130b0619080703060506091f15120f0c090603060b040e09100504050d0e0306070206071d04020f0403060e06220c03060f0903020708030f1b03040815040605 73
    0x1001c2401a0b0ba802000d2032402c4450202c58000c110701811150400e42c0c82c09d01100420098503010b1090310031344c000c20400c2d21134091800b25401000c0c80281094982860891a2283c500f07031141800b01040c20449074070058480c05005003007400c004903558007609802030002080d41c01c14410b01d490902c052107208419400c0c3c0d01034912207103510066444840300103203050008c4e089682d6550800c41088100800881c1c808900c200b291546815100386034200354481ca0102c58590050b40002c0c0018002c0f4450710b11004000c3d480340c500c41400d40808041403c1c4c2c0d103c030b00180901c04002804004110035071042a940030405c0010380b03042c0c201100036041140030350748040b50f041d18400540040c8a403007442c03a001141e100c0400c0186c2210414030b400640f11418056001d402200d900003aa0200481120010014410510b15011081d0981002d820031040610541d10040c4408a907000c1c0400224401c081e4000d2790403103e18040c80c03d801130754801000c2040c1483c0301804d0b009d503450321030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 914692095 1250 914690845 914690851
    0x3030a08010e0709050a080304051804030f03110c190b07051629071107050f010e13060305060403020f0d21020d1e06080105060f01080f100b0f12130b 66
    0x10280142e00e4981c000c0480301d082482d00a50384c4255842000103a82d04000020f0040780c0341902e42280000341203003090b0011000f04c802401003508217990840582c07099000048443c60404500e00f014189503100e8030342000d0a11b01090114090b91000900209000160340808203240c150319007a82110300c0360f5001410070005107238804000c1c09070025100030b407680c0c24803000d4040030022480e00c031600410000714204072030983d008038030010441c0d00b03110262049420041c0c40f41e400b00252401884a420804207911a50a58900c40840010360078401540038a01030390090960340c0320151920708001c5a404400284030943c0003610060150044101445044107001600d402038001d940010b0401047c1045102a0700440310003086a07540c0903400345e544003002000f01740e40302400e214036841403010141c042103240d00054a2400c4050503141d2182c224004d14011a60b02e80b0b540300b1b95000114410540600400e40c00d17030110359201402d9000e8440d20aa0b501c0c09010744403105008005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 914693345 1250 914692095 914692109
    0x180b040c1b14030310060f020708070b0c0f011d070e0907032a0807091a13050c1c090614041a1017010c0912110103050a09140601080c03030a0801 64
    0x40407240107020400c4440c00b036048488090300d03581d03d8040141c0340d00c0041d50041d0300210303900c500320a02c0144001182d105a0700094010b0032620300344518814150000303000440140f08000740d6650700301003802140740c4884500b5960b90310807812207900d07040901c241c02c06507122405100b00070020900144c140d080f6a00691240702c450650120040c03041c0c1ca074240d20710394900c1c1c00c0300002c0c0c9500000354041115903400e070030450207030780c180140e03503c5040c4281c00d5030000001c82c221250070b0280d48196002242c0302c4500386491010b95050180d582d81142c2c590b1515a100c0d40041070280e24052440b4800288202c004546402d544200725490f9004030060b0801d003090005014403400e5031504040c16030301c2c2c05e80724100d102d4000d80d03001c9c013025070007503000034030084001800618040c8101100d542c84001c0549140340080110002d000040c404012152507001103000304016082205000720f00310f0250515604103840245440e9200c1c0c2e1140c0240d10070020810240da00034800e50542d400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 914694595 1250 914693345 914693387
    0xf01050d2a060f0f0804140708150402030616050712201c0203031006120b061603030e030309031e040801020c03031801020702131e0501180b040c 64
    0x1640c01c15400c0001400820504803007981840c0c980c501c6000002012110b42c1d41d140109000300040403034114031004640c4011811820120340001c0c18000400b60500101044070041d41d9a000c0251605903070f6040f62540d00310310010301055007424080d0541c800d40b0060000d01042c80c030030008180f4401e90101a06045504d00c0540085204560040007484000c0200e40c00749101c2c0340e035588541250301019030400500c0b51070308106001005582c402d0049005001503a440c00e10155060080d00c403410601ea9500d0101c042e65554603000350641c020982044403500f8440d00c3c025003103640000030289243d0088c8100007013541c0001c110341e06a02001d40303195014510202d511381c24000c54001280550020401c4103610300008060744c8150140240008918600b0401c00c1c200e1117603031400394210300c024100203140c041c2a00f001c0b0140014914030b5003801d104d000c140040720341c00e07000a2903940d40391180070510680b07401001c1021804542c2006080c40303821004e8988010b01c02181c000c1d880c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 914695845 1250 914694595 914694619
    0x6100503090a0b0106121401060906050309070906060903060510030b0105041e0c0320030606181f030c0e0f090417190c1509051b0a08010e060604050f0f0105 69
    0x205100c0e070402d442d407025080419585440c00600300d02490321074800318900e0001c03030761203403a69400b005040b01d01c42d0321a85081c0341049021100740d84014400340303040c410328800140f41c02403440f0f984000e00a03542c1c0d40a1007803c500d0504192000640148021130b000102400407907007000c0e0407411550308480000d4690000c0416110741e02100300e40080051030000802e4846415400c4000030b620502102114007426022000c1700340800d0321030640103c41803150a2441c608224991b403401002050301042e02010741050b95007810540c141000261618140c610007508003080000c1c1e584111000052910288085001e203440200b029007810b0401500001c20154881100c1804030b85101c015004040d07442c000d8050f20a20000f10f0300035541c08401c01450380c0920443c9001903001014241483c40d10807501200f0303600007281948080c11003000aa0301409125000c6111782600103001c061503c2c00402041b114000c0200400040d100200714258200603185415184202c4500450035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 914697095 1250 914695845 914695861
    0x1a01140f1207050301050c071208070806010813080307021f0216082115010801060509030a0308181501050306090c101407020a03080c06060111121b0706111506100503 73
    0x100d510307030191360154601010700c40c0c60b840c1e9000820300c5070300a4040e580481e405007002c442d0070f03500300c80700d81c00280280c0101e540756101e14816030300801c40c0b1080c120380d1481c641b502032283c0d0068034414090f030310064001605a8031882c05182d1801c42060450420701016242c40b803540d1150401081c1000019554003220744201006000e000414132195440c5003080c84048515042000e044c049515034000155003840f600443e500040098068800700e00a0390302540d05040141c940c0e140b86649140d9006080401c01ca11203042584000030b0409516000505003884c00280961026803c0140c4881054807213105120329401203103000d11401a0700c1c5511074149c05081d400030350110304c041d000402d110003103000d031004110050075100c60b0b071105001910010800010f415a9030894062007003006003200c040d10000402d0803800380c20341101e00086040801c150030110105184500f541090042003144003210a2a803645d582ca23420584005612110740d04d062408222001000070100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 914698345 1250 914697095 914697103
    0xf120609050f0a0503130b07080f07240609111e0a0c050a03030207150905060105040c030e070e22050709050703021e031801020301030f03050918041a01140f12 70
    0xb100d0303450550340c680038145045a04c0754407084200181500795000410030b06141000c46200c40d40c4507058502d020521a900e4005401c00001a84c0a4201ca4441181040c1001111007181d031222000a0300c541440080f00446400c07060802004d8002c0c0210b2284c40c0c48222104299405014915182c01c8950011148e072040b041c07004203030780235103009002019010340181a0790b521444080c40141810600c480480d1781a01c00074109a0102c1c004100c0c1c0c0c01c01e0b6004c8001c15499207008102944895009454214260b000844201c03040c0204a103040c5000e003141c0100e91043c0c0305807d0441192035550b0b40c0d1415015540c3d4003a50380c40803408040c060f504a0f894180b00c0f10411202341c5624072110340c540c00440f00d04d90050158111001108410303c2100c0c1a258001031980e151480c644080ba4107400c1040140e0300202034200c86065200300320440b40c451032203604520111440c10b00b24103030003031040e80401d0360b0290350500c241c4560f5440c41c40d4229120700b5a420b41d0044800307080c061030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 914699595 1250 914698345 914698363
    0x7020f040b150d02040e0c03091002090f06030408030702071d0f10030f060f0f0c050f0304020607140705010f0903021e03070b040b031503151b04030b0106030c090f12060905 76
    0x12107800103443c000e051081e402500440b00c034556a0f1180e640c41d5503a00d4030310b102c21144d5074010341188003402c105c400f8070380c080d141c00040074140105030503070303c3c0101d16594800d9a0680740c110001c4100860741d0f1341007015902038240b0401e10565a01420010041600007600016984000a001620340c2003510368180095420040c0c854408405081440080c4444107842d407451b0f04100011344621241c0c01040504a0710755a80c0e0726160a0120000d06508042c0c4200e0744001e00300141400b1a49209140464480700806010241d03d001c0c005408a00051244428032604d03d00c10009a51010f0305a080680d9030703030f41103444144213030020f03040580f83e411440c0c8016004c200401c490010401843c40342003c6620750803029a014101a61401d104c0f0004860320310000002d8098125070070b00c601c0007090f0a00042c2803c0e120380d03030b1000f910b13000d8220900080e5101220080c0030f9200070f4081c010105042240c20540c1004145410718400c240003070421600c039400d00040000800c2a505 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 914700845 1250 914699595 914699629
    0xf1d1b07060507080903041818080a0518150405040c020a080a03090201170f0705070804030b070c0b063c0d140d030b030d031802030106060e130207020f040b 69
    0xd03440a040c03a00303000502080d222500010b110000040583d0b200004071400d46e28000c060115220031100080040e2000d91181c0c0c001c0034450341d0b110005003000000c0e0810382e410f6110a91a86c1c2c10325840d0001103c403142241c41581b010547c02e01d0b24214804030303000d4070029100421740780d04030750003079280c0307004408018251000020610007042e85584110340d01c0e4800d9031900d2241c4d244200d507620f103402c140c54a4401d4a200c601140259000308000c20311035128040013070410395261078207007041a040302c0c6440400e0307800c00c01104000714a40d520368442800c031042840aa020000d080040b003c0086c0318540c8455444440e907031100c80d800f40310620340018020345500c001403412042e9159003115004142c07240340d03165100d49000c1d009124810b0400750007820b0380e14a04c0e8040740030b0003160400c0c1d0f41449a560384400540c60a0103000050807094444207146900c0105010803002e051075120b017801e1052010200580d5031000031000c50200f294003040000034200090881b105240e135400f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 914702095 1250 914700845 914700847
    0x1c0c03121404050615090c09010f1e09050901090c020714010c020909032206020c0d0609061d0d0306290c06040501090309091b120e0106030c0509010f1d1b 68
    0x201c108000004c200b403103261305142542c403c084e180144104079601b0303200c0300301d0300380c0c00d2012110380d510484481140c0140791406d00003695400107800709800f1240304850001e121548140114101130007a1401050112410402c1500c0000025251011800b807814600000010460781f40e104401c0f5810705900242005000d040c03c000013996a030145120250790b0004856207440d106d900c5401200311039080e0040c140c20141002004805510300740c08480180d500c151080c0456183d01c00c016010030100780d5880700c41d415407865490440b101d25000c00301800d001d01070094414540030030300c40e0400c01c01c4074031318142c000000740e03501d0242c4414089988a440100818880e0541100c41d000707019442c3d00f440035842e42851000d03500c6a0302c461000781d0100440c0b141c1030b48942c420205080c2050b0700040d000300052607507402e4410756401581c043c00d1490003404145044c000b00ea00403c05015500c0010303140c032404203500d5a1007115000558290400500303c00c5202c409000b800d40d1311402c030707 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 914703345 1250 914702095 914702101
    0x507061e110c010b04020c0d03050a1d1b2b061103072303060a03020603090703170a02060a0c0906110c0310320c0c07050604030804081c0c031214 64
    0x80c0d141d60b0401c02c80c4280541c00d01c107921034107060510032155028441c10181410031000e00080d00540000f8100c2002d40390350300e1090801d0540b00441542407120307076000e800790b0400095402882524004aa4841c010342c0c54a4a00c52007400c03030758646001c40305c820b0402c4822608000c0e00410103c01c0c112000c40300002003100095001006101480d00008045100c0d080c0030b0000400780400c54885070403255202090001d403410030302a5901045100407203000e1520390f030300c44100141654030114480004100301c2c000315014000781c0d0340f01201800422018030f0710f80c002411004580b1440f400c0c0140d00d00000161507003801403819609015048428a403540d05241009111002ca075203140407034250307260307030410740c90500c02e9805a5409806030746407200c141c80a44c44d07000b01011081c40c407403024001029205c480282000310700800049132114542400c0d103003458141000148480700090481c0092a0841c10103104540c051401801001d0035001d0321000300b9107003100b207083c6402c035820 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 914704595 1250 914703345 914703371
    0x1430030c0604030905150403050a0206070f020a0b0d0c111903140a021608031321020d15050601020a1502030a14151905090c07030903140604030815010507061e 70
    0x1480b021220b080d03800c00e45100c2d4044082e4003e00423400010419000303010f4841c05032415030003410046005444039013600c403886e07000954684051784050840c1c0d0002ca404041c0e6545d07481400140340c074509110765042c80d4542815241d1120703404682d50903442c170030301d0b0082c14070902c4801e00c04442d1450789541c840c080752000c0c3d502c1c003145403103080d030151100c80030070201004400d0310084059107140040c0f0f5070034904044802c0651050b0507148103d80da1481001d680d405002e594903038000d0304988180c903142807441c000d84d40c0c01018181554070004075440002d040115410403810301b41801a280e840362103c00c0060234240c1d5004e40c943c80220144502c000044040d101c6280c02111803c000004c4071148150315182449000e5026082c40e0003e820501041d004060140c443d15103070740c0700350300ca51340c5045103925800703107071503d40c400c40c1000f00301500450300680010f040301061008402000c0000c1c51407103400c9008002030784640c0d40221810320311356280001022140c00f481001c0d20722030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 914705845 1250 914704595 914704607
    0x91206391e1b19151d0a082a15100302040606210c050403080c0f12190314040206160b0703020d1401050d020d08090405040c1430030c060403 62
    0x44240c018000c84034200020011225444070703d0754421603100c0b03519840861040280050b4080071400c007604081e040160f40e061082d1020103216070b036520748440704040b050755441086400b0f600354416108200c0b02440700044c03030700620103000140180e130740d580e0220094510301943c4000d4006050500200740c00b274101c10034a6a000007007991065150f00100780000f82c0c0c109480c6040030807400c04c014004219043c0c0242036501034030086480d2880c54140320b5107400e00b4200f464000c09004a03d8801d0341c008828801c612a9072807405004032900380f11841584080508001d1155800050b9680d405480d5080c6080c0c15410000c03800a0f440c0910001c2c0103075101d061241e403814640040ca02c0200581e107a12410f958015280e035003080344d260f0a00440c4608040d00b41d80c100c1003440019a41d94941c01a54443c51003005041e20346450010140c4054013141c2c1103d03c115500700306e210070000300942c480c096012a06a52000d020104c9040d03085101d494261001400b4070390401041c150084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 914707095 1250 914705845 914705887
    0x122502100e0f0d0308190e060f060a08070605182403091e0c04021b0a030905011412162001050601090806040f080f091206391e 56
    0x280722072102402c400d0400ca030700c0d0786245000700030079400d0003c2410340c00814503901c180901c880d4000341d20643c0001503481c0880860705900d4101000040090a040c14003207c001007840000901d5207a0802c203000d8040d0080380a241394040c104100e9070015691400160701d1040c04420780d90219072401e452081a0f4030484520f5014402d1202145c400708004409283c103c010f580a0050000c04800b040081d41c0106c240304c140d4001d0b0070040f08442c0c81800842d0100e4441e031a01c0400c14035120014105248a0a00800440701031000200c050440011250b02500f00c2c040741251030415642138591031f02c2488494241d40b8030070441181c1802c1540141c3c041e020988481c0c441540d16080c4903650007003100e0040c03480c41000b20401c0001c241c4806820140c1310130fa06103007050900c0000c504000e1045070303001110fa0101060ac40c03520f1044507480c00f003102d8032121030100c0e0b01000c0440d14211401c0301c00407004c48009102c2d03915600300001009802c4242c0f400f15643c20722101c2240128100b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 914708345 1250 914707095 914707099
    0x4060603060c2a0206030c03270c0102060c030106231c0207150603050a060f060b030a0c120203070c02010c02031e07032d0308040327060908122502100e 67
    0x6148542454250f40440c1c0b41c050390082c03031989107540344a00f0f03400301e40003d49029a0540b804200020107000b1411140295624030000d00c1c28940c4040024600000076100541d030360070800050000e551300036649040c185202d00b04074445a02c480b05040301744220010182100404100c04003005c001d90004d1a045024901d80c456001c0c8101210003140e800384030003411948030010300d4000441640100d030880c040c2c4080000c01569807070400b45613503c102d0365100d81542c0e4500d001c06e45500300e40c45191701c4005c00411030844c81e2121019149007035100c0b004c0d043c0091030410104640d0108201600c0d00780c0c3c14140140706856540301980ca110781c0c0000c0f503041c4880c0250086210310401040c212900c0070203407070359405035a20152402c182c06401601000302d1120100610003405c03103001c0a00c0888950415845c1c54240c00504a000c1c40d0800c058640200c0c0c4403000200790308059900206402c1900c0703140e0312800d000080b0b500d40021000b5004014000d000001d6a0899007213101c02d802 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 914709595 1250 914708345 914708387
    0x31b150c110102090102032b0903050306131b11070b040b0a08010e1005040905010212070504050f01090e0a050910112a0a080d1413050c0603010b0306040504060603060c 74
    0x80c1e0000c1c1d4242d00403050341d140141c0c4140408200890054400440c7d00507030812101904240e80c84038003600e41003035003a008508000140862810a403450003c0034607002010082d035286d02c2c400414011a41d902801040481014107868136402e0001100400030210510f0765141d40b0b43d0000d02c42e030001d00d00c540200b0b90001c0000b030003110b0403c1052003030300c510809125190400b0304100090030000c41c2503d0941d401d02a4500e01d02c2907588550055074251125038507289003004201c410310f24003091904110500008003d20f404989a09030031403180d0801007410303540c0c580e02c60714110010b0700f40c00c03105041c401c03030616070540503004000382c0700d00c08007000c9400d22442d04284060074184042c840c81c0d1246a05d800814201c501400075507641c010089210464600741458003241900c2e8400e130740402203c50410420308001c9803141c10019151541190f1601c0c0c1c0500042c080203081c140246d0319000050100000750340300c5005036a000508002001c46002e0051881e100022519403401e1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 914710845 1250 914709595 914709617
    0x170a0303060609061b0606080a06050a0605010e090c180d0303140604060302130504110406030c080c030d08011406120f060a0803090f0f0604150210050c0313031b150c 73
    0x44100603e03800e49140b922130001810700b1800c000114441448140e8241d5512032000c2402003003441030844d07050041d8004a03090802118090072141154015814404444140552921075050f00c691100e07850030380395101c0e80c09503412000b40c580691100e40c405986c00c412000c254142d40092040300465000c1c04681c1d07140c1c414001158050300019600881406040f40c401d42c00d0303005141e0141c441d00d8a900701500f6030021800791647c0c1d820841c0c51903514401488134032030410082011590880003480f000c0e6115001030482c10b4180620a4001402030340000340d42c50300011922214000032500354a03207088900f4004200050f6075191142040d9180017465110003c261401c1e03060003000440e5024003d01000342246444021039081b0401f4000011003803914040c403945c144054001c2c0884903940a000000c80f20004c1107420010014805c3c0841404000d0410200c158542130800c1200807114500b0040d075400007000b41502c2800d0b07004001854180c020140c4109a6251040c80305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 914712095 1250 914710845 914710847
    0x15140403030b0a0311090a1509090203012912010e1608010c140a031508032808010806010506161b060f02061510110313051806150f04170a03030606 65
    0xf540e0300c40075160030212880a1694542101895040602c066000a050342c400c65a851208074aa101c01d2013950b45204100660800f03003c2c1c691007102502013280300c1d240404125802003864a41940100e4819000c4210040c007584011001071440c4201d41101c018503904000f000e00c5800340392001d500308514422124000e02c4581c21880003441c1c5141441e103c00d10031401400c40d00c5c80e1180700c41140c0000128144140b0042c120045910014403107858030400c00a0303994202c02041c0700700315a01004001140001c600941542c00440f032441e0341c1c1071400c4001140b030b05500c0000e040800807580e0702c0740c40300010026a04490b41622420b004656820041e1f071030b030b00d0441d5480321400201029100d1403a120884110403001c030b040136580c4180c461081071a5401194003200d0f6030703440c0c1c0b000340410b10f44820031080f503103140c0107038140d580b40500100b04c20110a40341c1d403001ca107021804a040605c034005550251200100d041c0c1908660300d09507540c4d120307800382540030a1520701c01181c10703 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 914713345 1250 914712095 914712109
    0x7031214061206130b071701080304030506060a0807030f020628091205100c11060906250f030903110d09140604080d050d110307030b0a080c030c0d15140403030b 71
    0x1a85400d0302c8108440064440f08045c1d04014130050030019601c42106280303109205560281035901c00a40d01c45095160031481d2071806002544110322841080009240003d00e0341d007940c0e4002ca00d02030292413440428024082c408514600620b10080d000c042490008000c2c00402195500c14455554509510a13404881c00c080c06c160400c07074851010240603044207109062600e0442c021801e0146090b0801b407041c0c0c0c03802042c0d00020207000c02a140c01c511001c600b051100c1d540c0740855030003800f424100b50420303190145a2a1012541454007511000d2030340c4940000b81c6d42c0a01010f00010007255250190ba00c084007815401c0349c640c01d18030260380c02d86089400900d010101e00700240c46c15040340d04a18007440d210603a42d05a0004003000d54007800c080e4070040341c600030b410100700360314071030b80c210301d210764450412084c95036400124013862020036941c0320740781d0b42d050410b01031004101c07034510141b508100c403844481ca8002d00c1148114040d6a00b001400c0e0718101300307d18 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 914714595 1250 914713345 914713351
    0xb0c160609210206040b0a2016150e030d0c030201050f090604020d0512041706070c240b190e0c07050a080903150903040623030c07031214061206 64
    0x109216445001c506206402401c02c07005000600c141d081964a0b01d01c900303660700404880000860720303c08100442100c040081d00c0304c800c80c001c0d25030004402e04100b0025558461002959806c4032001c0290780640404502403a019007620301450b2111006400b40e01240d2003100150b00e0140000d800c110801c08a5000340b146d80701424594440707030204101036050032030680c1c0900500424940c4011208010030041c100c58081d0100d900030450381c2e40c1009001018201400590120714000490b101d05010203040d0001d079a103030305600d0300012401003100d6581142c10070392072404100c0201340c1040725002c85038200c50904180d911110380076406d010b000e4000303103a50300103840c0d0400038200d100a8040400c010701110303c007220940a80b035152a0684062f038541d00300280034071001d50301050075940340c1e156500c85610000042c0503201c0f64032004000c1c4102c0302c000304250f000c141c4609481d000c10004c000040c400c4a201c009440f903851015a80d07688689818085841044404514544 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 914715845 1250 914714595 914714609
    0x103182a0b09101403040b071704031713020303070b1501110607051b032a010c0e0f0a170303010501120b06030a0b0411041e090e0a060e01060b0c160609 67
    0x1050035074041c1844500703c2d2801c0c0d24810302c01408180342d00e50800102840c4507501a243c54441070910790f00262115041000700b1081015010030003000c40c0d0030000003240041110905102603944102d643c0380388002c080020751601000505000313101145600b940101e2007510b042051008501c019520086981d600349481d4201e000055446405074014002007446100d1074407a60652000403800c5901c806805001040d808410b07c25409090450961100d404c2000b00f1401e210350b0005001d00c01e16200441c0b2a00218642d0030160f100c0d0458600180350704642a100411000030681c0c90b03410034082c080c0010700f038064002c0d400100c0d0041d402d00140203020a455519588181e030003508118507030790b4005865404001001442e07500420080048460303400c60909000001c1c0c0e01020141d000c00111420003a050301c031907a01044070341c140d90384000d0003d60050350940550150685601600310be64000c580b41d1003440c0089210100c1c003c0d113402209400344ca40d0020303104270200c0e002c0e9074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 914717095 1250 914715845 914715847
    0x12040303090b0f0f040b1c060f12050a0c151106160813120e011b050705060307111509150c0a051602040c03021c060e150103182a0b 58
    0x403800e12214001c20b8080408140c21349403500300e10341c0c0c40c038070741c8240c0c040d035405240015801d003101c507810442c4011829101302406083d252040d002d4950310240503070b0502080800b04c1d0020020104000c44040d83c1c04103000c034100d503441b50403101e511006a800b60108128001c080135200c00803869521a001c00c100f0310010b076035aa2001c403000c441c000d140c200044d40002190010502112080881e44540e50340c081e0910410781c0010f14002c0c0c4511043d9801c80c4407000c0790001200410001d0544200703a610540340d5440410844180c01d40c410504064000d0000440c0c82e00d28040d5440d21414001003182d040540842004c0e07080c04044600428960003400741c0440075100b080103004840300302111159160306600054105c500f1803105c480032944c00140c1d081c103903062200c5900c2141c1c41e00390030008603181c007120700c400e444000c0c18541d0f90304107ca14410b4a80c000d90110084614081d120721209000d450800101c3c00c112107503501030101e00e10101c1450102280840644410054007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 914718345 1250 914717095 914717099
    0xc0e040b010608130611160507050102010b040204030f02040908120403030b0f1c082a07050a06050a0206010302060f0c030706090201020610180e0f0a110f010e010c0f020f130204081204030309 84
    0x7110050034503110480c48400204103258640780050684900b07d030003100603085103880d19001a0848801042a40c00b0f140103010400115450401c101043ca4050b20040b480440f1860268020300c610424842940010002e0201341a415031000030742480c1a03500a02c0090320320100701d0101c1012a28415980d6400c06100019048001a048004002d000303201880d4404040020b00c0c0d401c000801510b5000c10380410440c9800003c40000f000c3c80d0411ba850114040c1c0001e4903a101404064001c09002590080c85903050b0201c41c50f0480c4142139035100c04642c60190301070015a0b0040e401441740a01145d1110104030b01001114204028444402100d000c42070203031641c6a12480c05009a81007003400800520098070264171403451405291890b4040007044c2921140050400c01020781d0041ea698002c0f215946c0e07a900030f50030f200c80800e030384001000d901e9001e040640180c008500440f003403d03290050000d403004101a528000200d95000701d99010b00d04c805400540a0141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 914719595 1250 914718345 914718353
    0x1020a0f030e0f0f0f21012406170f040312050406021b06062b02040528020a080c1b1e071403060c0a030b030307150c0206091b030106030c0e040b01060813 68
    0x60070000c6c3d4840c00101c0da050518698142100c2d200380c440c0c001e101d07001101c16070f940f100c1f003c3d00d40a055103044c010303200f02010840301c0c100c01c1d005100080f01d000b00e80102e410726028401ca42c2c01d0150342d500c00c2c800c0b03203417628004020390030a884ca46143c015030700c0040072059002c41d03d0f5109180181c02607100c0c00744032800c1c12602c8540d080900182c07030341848507005a100c0c1c2c001e983c414039201c141c2c80802014200041d9041c01c0000070806030a2040c80b0040846034010803080d0043c240b24074a50315803000c1b84600f4401e0b03090781450101c0c1e00c20851803400d883c0c102a1141480c2400209070703a0351655401c01c00d0a42001c0c0c07008150b16400100000b07402c1301c1032001401f000300041c40c0c00949180d4190209207554030002d01136032803480b2108984c040c00c101d4003800d05c0003002c601c0948242e0400440803555100d81303804004031300c400e0741c00c254420b803000d40c85200119048104845419610040d0000c4048161400e8a04502c100c0002c06e00d507000f185118011941501d1000f4070f25140c0d29 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 914720845 1250 914719595 914719609
    0x120a0209101e0c06020910020c011101020a1b06021912060f0f050909070806010b19020a030e270a02120903120610120c1106090a150b01020a0f030e0f0f0f 68
    0x459940d91700b40040442600c4104a403910f100c10f03a00184a035410030070000d029440b50200740f5095030700400c083d034a46648401580326007102801100031818461500308064020b184068800b00c28081070044842d502410450821810340d03400c000c0140c88403090805407031507000c0c1a1a200c0360100070041810b10030162170f4003103012003d5925980d1a0908142050004e0340148407469010038144078002c180d0882908081e00c41c0010311034035400c2d581c0503010081060840f031280003081e10420080101721088800e4452442c20f0580300e150101004c0c00a402180c048607081400c8800544892000403c5a0641d19038001c1000d071559480104070410040d44266010060403280c0360410b062180a007941100640d2580806060b9040c8040e2130108000c02540082c0d110840c4480400c03503141c080c92016203601da01159100c81100180e00d03100420000074224a00070500c0400d0652140080705e80490440d000311103545030f40100000c0340c08034651f0780d5105820422034810303490902 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 914722095 1250 914720845 914720867
    0x70311060a090806010b0315040b010e010c210203040810061214030d0914101e0b041428090c060e0301111603020601050402030403090614120a0209101e 67
    0x225241003a0b9455840d03d44c109032081e444040f00316004000c0c444111400740c0d910500403000d813801c010702d03200d100009200c659001031341810b01c10520380e0001800340403000074090008222041001810305d000c0250b03603500c24841d500903401030f4100d0f84c20030480b5005170000c448182e170140ca011289600c4843c04181c141540c58405c0c8020840741c83d4282150042c03042140c010305068038442c2103420004d042410071007162070018640f405034000d004000388110002c0e030000000150840070280401c00400700d10f950504840a0700c0200b00041d010030071082d2500c410080305402080780034030508181c03915080020a03001e42c1000905c445849102c1c85d0307503014030040001c02c1680341402e01402ca540442e01c3d0395801040d0f4580390b001d040c0c04100c100e00520003035030700318514900703610001c0622083d40190020405408820000d665208051b04c8589881c011015080d00b0711007030001c025400410b4450087c0c40c0d010300702c5441805a90303402c40c01c0c9040f051166003080e030148222555a208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 914723345 1250 914722095 914722097
    0xb1b150c1b0105010f05031e0d030b031905010c120501030809060d15081b0901120206030613110405011e0210021e041202092a070213050907060809070311060a 70
    0x290022001c1c90009006083c02402d400620340841c500344001d06081c043c803c070046408510004980601a81c005582c84c9000254900006c1d000f000500007030520081584407203543c0ca440194109104066101a80085840d1140c918500300650141d085c0ca00034800030b03240000600102c141c2d420f1150007004c41101018001418040c4824154184012500054141d45c000c0b004480410400701003680e1310002210104500e40c0741684240091b6031030280240120008408529185c9450486181d0170b051180284404109031005003441d800502ca81d0340014205801c040b500302d90b80b80c1001d550300b00c603800b03800308214068085010b075110700106100c9454075001410764200000190001d04940c84840130481200d004020703030060003501d289091507001d01c092006903255141034809038042207180b920f4100ba07000241040e401d0300f000c6c0d10ac02d4204020000a140049022421b42d0080e44900c0d119803200e81c0042c3c0e5501150000810f03035060503001945038944200035002034192 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 914724595 1250 914723345 914723377
    0x1d0103050c152a0105090309090103020d14031809100308090907140d0509120a0207140112050a050a05070e010905041e021b010f140a0f090c0b1b150c 66
    0x4019020358070001040c4483d02403040104440701d6a03042800784540001142c401582400420b0000403000c0f04103100080c4203c5012110804010901c00140c0444544c0420b403511030718048100303154004e0350f041700392080da0410001264072070300000c401d0030380b0b401c41401400e0449030010301c00c0c10b410150400d000d000c0c20301d402c0e000c0c8080310002440c41180c1c81c0001b081c2400e2443e9084e2034140180b0300c1c50344d60001800b208440960001e5110110b079000180100720444180040c0c0302e04580380d0416802038107140410444403000e8200701d02414141108020641e0791040071102006246c0da200d0010340d00a0b0100568500740d00140780b0038181d40d510000050300c11907145e04a038005201200d114140c403c00001c0d9807c20305c41c4040c100340d104814070a80d0b4060440e691681310041c200540c5c5030795091511240d810b0fa510001c2e442e94080f4640c4940e5880c1c03941e03000d0315040594803010b80642003400350044a00403c0ba841143d10a00d04600c8984822a20719000d4100030b1821201d0380e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 914725845 1250 914724595 914724607
    0x3110a081302040b0a080c1906140d150b07030f090609090b1c031106090a0804090f0b0a08032205030d030e030c0d0315080105042f04020409061d0103050c15 69
    0xd21440d06200070501c80d030003480354040c044107001d0648d03028090000c038000c4880d0300308641038022844140c8007460444070741d45c2c0d0f801484094001c1c05c0b03650758001c0181035118046a0610001c00604c1414040d4840110081074108111a1403917a8000c03200000d04c00001081080c0d00c5401c90741c80144001e081e0b200c9070200c003800281c0307524560410b40010700203040c80c180e25982408941d8000d0403803000360090080741e8a408420344202c0c49808000ea9407030903051001c515940c41124210002442d50b00080e43e00e4600640c0d80c0c00a9150302c00f8010319180c2a004030480c01584c0c001ca40000e400340800e07101c810710540c010500d02d5564091401304005410780c9a030148100030725825a81c43c0040c4420401001410510700303908100d0150380340406010100b200100349160210084600740c510344a8030783d147c1030802122100c603400c140040f81c04102403200e5000101980c1490003045001014135580d5220060300303101c041c001e0f4000302190701e20b0341062220b0f48060722800081500e012 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 914727095 1250 914725845 914725849
    0x13080d1d0a080a060b0901170a031206080f070f050f010c0609050a02060c0102040603061d06090702100603031d010c0b040f0c0b0304060905160f180f050705070303110a081302040b 79
    0x11009841111501c1d41d03400c1c5c040d580d1510045480c01361540c403000705003070882c055045a84e9880c4940140c01d008050380c3d000c0361500940c01a4000e404250b0640d10204060705850350344444034020301ca0154142e94012500d41040720b4080102d8030705030b64240507541c09032281002410306e404186c0c1c01d405030401540240e100c107801410b41c080e0381000180c0e21481d22000a045400c5a0050428841c840c0d031040c800c00529140b03150800380403526000b9913115148140d151207011a120071845003441000000e05401070009161590000da200785034034092401111204254400144204ca1100200b4003258268040180d114401c2c0319600c039242e2904014801030704110b030219034194079a402a000c20005008540b281c400c240500c07040d80b41030844461070040a4023130f00e1450300c6ca900340710421422541222201c0003402d1001c0000d07040c50000140381d5440104203030007180c146400d00707540030200c004491540c0c040750b42e2580c003512222044441031240c00030a03a0700545030120800302e5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 914728345 1250 914727095 914727103
    0x80c3303160801050901061205091513050729030c0d060906030516050a1503090609050c09070206010803030703110d0c05031b030903041208190513080d1d0a08 70
    0x10016010010300c807500000004200c040140c0045029074428070041280c19000301d6113000b42c4094900c04074065541a85443c80d00c2e4900c0c00b400c101e04500014084240800590b4000f07c3c2d001700199807141d521207802032898080c507148031804440c0807140c940c58070035000c0078680207942071086524000d0301017004401d55103260460849207036121006c0007046002c0020842d124000806c61032428644000a4850407442c4a941c0d0742d84079030301d501080c6070f1180e40100c0c0031a610140800100038507007071941d603c41c81404400d009141c09008112054000034629048440f420004d62035a503036008110040c000020340e034040a04103104001c205203650190301c0d400b861950350541c60740742000c15106180f0b001c55011000da202002480716a16011040300c0541c3ca044a60044c284090300e0554003030321804601c1405910990a142182c3d070f402001003c85120580400783c1c0d00e0307180c5000c261618802000e1401040c1c1e01c0c451100720500745402041c0d503c030010805440b60395900380746410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 914729595 1250 914728345 914728351
    0x17070f0b01030b070905042901020c09010801051b0f09010c0f024216080403021905090c21190c0519020d0207090207050106030218070306080c3303 65
    0x14420204120350303501141d017500800d000c0780e00313101189101e080c10009803111640030403100101000d041c11a4000c00441f200030788045c082a0309580d458051b28001e141c01e0310500720380d80074208491982d100580a81790030b502480c01d042c1c034100c076034401503070a110320070070032540a281c203011007001d82d8500000003810382c0041c0034019120030341090f228105540380d40700700408054807080a01001e6950540b1007441aa55181c0948030341c0c0d082090a50150740c2c8001e50141d00f0100041800720341c2001c00c800c8a100340d4110181c1d44407500074400b640180803c40781940d002d00c018010007115078030001d0b044070b5090307010241c00714485100d1055485a41c100b40205800080010031881600124280c2c0c0c4050310240c4400682034500035160a0703d0b210b628841070f000324021041c07080030f50241000303590007090b88006402c040e0000d11921011035072500424500500000d0210700802c1c17a66040030010a540d6240c3c0c020412940b8a45141d00944000c046008080900b00300c0c401c01140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 914730845 1250 914729595 914729603
    0x30a06032009092103060a240801210b130204052e0305070b0c15010e1906060e010521280b090c0a051c0203010503010e0a17070f0b0103 60
    0x81c03544a6102400000c85024244205551007000c00d0310810089030440c49800c5141e140702c5603240c94110005500314600d4204900900b1060140b08000da481c0390b05c1d0a00810645501600360f0707071a828034082201861a00200000c1350707802e10002511602d03601d520950300c00800417960069000300301181d404450260141d1100100320b18201e031481104040c15101030303007024a10b4156620240c44614070b224026002101060b21004580e06020000d1045124000c1089640c0d454041d00c1100509507010b083d1114004070301200203c0a0080905541054841c0d00c2c4900f035800046a203980f24900300105184071030021107400100e00100390042c4030864001d0369201c0c2151040c00c280b12030540000100c0d1510205881c6511440c60856210a002030030607113510680c44240c60300e12400140c0c030058040a40360406041042c1e0140d4140d51094000b03700f0102c3c5820740958032030303007010043c0041212880980181c0d90440040c1100e620a030074144540312160b842501030182030300115 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 914732095 1250 914730845 914730893
    0x203070c140d030f0e0a12020f0109081201150c0809040609060e010302010e060c1c0c05030c060108190b040803090106051005180901140d0c080d02100b01030b1302030a0603 76
    0xc0040c0d458003812100c1c0744c2d400301c1042a41e800303446040da52040c11800428070803080039220f0325036001348001c07821030200c01d00912140d4440d14001085034440303151400c400241d0000030031030380414151103420450a80b00c0b4800302c040c81c0c403006555040755a0480d8001d4564602040303c00650003a04002d210680b48440c582d415440051310081c00d002da214044c1006000c198001840054003908649020380407800e1045015011131308035484c501c015045100010304c4070903010300050302d117040350b01032000c1c2c884120b03150000034540c0c901141c000d04030046080102c0e000c209000021500b04004030000184076aa41c004540c20705d09460883c80421404035540090f8940f194250f0350b900c4048072405041d42c1440340c60680d40d00031701540d6026040c081e1841c820406816508805094600101d510440d468003000f035480100d4804c02c42c030a400c0c8800a01103500a0190004080300281201504101252105c00a40004040d500703126165480000481c801303138501d00078912440041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 914733345 1250 914732095 914732113
    0x30f060613090902131e050406022a07060302030c0d020318070b0403030e03070b041202040e300408062202060f07060b030c060d0c020a140304030b0109110a030203070c14 75
    0xd884a5442104203007505040c203844000020106c2c44901c2c1e034003090001140e4642d400d085000340165203c106250b58a412060b203881030001e0507120501c010740445103101c0d06c6030021001da01040e5108440c4200522080c0360456494003d540d101c110a51344400116601c000180341c450240e0009020003000942402450b6001a44204801d000d4000301507080c580100d01c14203100740c0c41094501d45195809804543d00c0d40c1181a900c50044101c0b41c07440f21a190344400008052705003240031b401548048088000c40c07040d00c080b0341c4013a0280100750b4a10b10303580300c0442c2101a116164031102521001a541d0401404034206442d2001b61103842d2483c05404032200051a540300754004d01c20035015030f950000f01e030150044c4000c04640601c406905038503020510100030007030014003090700c0c00c4501c0080070f8402c69008060390b13907869980e950303070000702c480068003200b60070810850800c0c464029002960000c000c5d140904200039203840e524041e0920203d6080c0d03035000a403030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 914734595 1250 914733345 914733349
    0x12030702030d170c090f01030207020d020d060203150a03021503070903051504110f030a0201050c10110c1504030f1812060b0a0602070605120a0b0916030c0c08030f060613090902 78
    0x5450b88009031139043c0340341100c4440014000751000c1c4103e03040540000d480821900d41c1c5e050083c0860707000d0081c0d0b07980e01c03841c54240c01a41045500d05014059210081020700d0310004000842e40c0180401014004800b02100c036540000e0140d010b05c144407200200242c1c00b00401001c241c00395540500905003450200e241c003003403000092081e008031044450300c0c0d50108142c0031855090801c60b0380c0703c4a0941a50405082040c2d006950380f51900081d001509940100032055428003035030220705403092840c403040310640b0050001101c45210407074250107004d100c02060310340425000466a607034803001076502ea20004a0f035094a0703a03441c805a08181c0c00d4240507182d14009000d1a03828080b0082441c00307249014004a45800c010440052940d40040743d00080a0080170b2103240609040c0c500035603807017030200000c1c03130a0807400031035200b50401084668020002407960303d80349844001200e014003501e40c401c204000d08101104900c040e04010240c104d404152178081d401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 914735845 1250 914734595 914734637
    0x601060c020a060906051903060819060f0509060a0203130c0303120c081b09120d05041d060f060a1e0c1109130f05160b0706050a0e06010512030702030d 67
    0x202100034042d213814188006034108060310310300d030111404c0c002c0c0d002e803040301100a850940e0000e94a40140e0141c807544140b95102d035140c2c02e0050200703001140040400d8000c0b184e04441e9203460760400d10201d0074590098008540060540e441d0840d8441941ca480c4162103050384100e0119006140341c05110046001d0081103014508240720301d03180001d82c0c109075911000d100070031400e0000b9606456a581f81e82c0c090124080000c070364600710401c00140041d403283c003032a0002140510090721180c9250300751480340c0702c0a400e0004c89501c110034042c040d042945160140568007516501c2c0380c03d42904114147c3d210340c1c402e201428141003a14810030b800300040d000b000d81d6410050021983c8850110a81c0d2020080d5148485030030024204451050510010009480000f401d1005240a0aa8140602c1007000716807103801d080c400711800064a82280c0e004074004001742c0c42e01d020355140420645081e2442c1413000d500203070411051800e110041806020000300046d0000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 914737095 1250 914735845 914735849
    0x615080402010f031b1e0f0e2814030f0c03150411040c051b010908030711120d020409230a0f020d110c190b04060c030902040e01090510060e0103080315030601060c020a 74
    0x3c00c0c2180c4880c0c7d00100104113254100a06004040050700b100c0360072240d0070f80d15115445500e01031500750b1550700b0180e000d0200300425100344540c41d60986e0300c10780850010001d84004009082e8218840d1403036440c3c0740000c10a44070440c0d40c45d00c130005e980300d5001d00002d00d43c01c1e507215542e80c2c1800d55050240c164841d80f10086a16103041040081d52074021203400c0081400c1c800415450381000500d0450844504040034001080e111203501c2c041d00903000340e4401d9078060203103041100c0a51002048940304030091130090f00071850b51b0780e15600c4a1140601030700054030b4062a21120025294140e911000228001858941608081c441080c80410320949010101b030541c030b8201c201240548083d103266611010645010702a0f0311024126a020303106014032480b500040d4001c09488009885900802880030744010701c6120b014161819400e40c3c0415900315164802a82c00003004d030380c01c0b041c0310261030000f0750302001840e0081c03a01c2e80d00c042d442c00d52441030140346034040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 914738345 1250 914737095 914737097
    0x60a030b1507030c08030c09150d1b08130213060f0305061e07270b1207020c060d1a040207050304140d020604170a0b090c040615080402010f031b1e 65
    0x80c00601e001039444102e404c045500030021170307100e84070b09500580d0361007403008151340901da1480c0c075a041c03218200540001e1031480d90811200b400d10b800620b40004411450000a80b80700004804010401c07080000300d0000c2c00d001d03080a00c0324035103011122580c102d00486800b841080080040811030382e40d00c00030030001c04c4082000380002600c020809032a42c41480882082400c10f4240c0d03200754426500d2180b95802c5465aa0200b880168001001404808001c40000b80721600010321202041009000c9a2078050110300c001d006014201d43c190060801e038442400340c0d51203002500d5054051400740d9601e40c5400c000e81108e00760400c030079000fa0301031504071026903201c405840441d0090201e075120600c1d03281e81c6508114040340000c00440d130020610042c0c00c0001402d421500e4142c4080010a88994010607030590740e06070040003d40001c00074005510440b60405481e5041c10080b4070b0000c03510b41e02c440e039450110307a44002040d18040408600e00d0b10300f8003a41c0102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 914739595 1250 914738345 914738347
    0x60317090a0303080c0d020a030c231605070f090b0a08120403020f011b08270a1403030412050a110f0337060501050a05031606080c09060a030b15 64
    0xd440082019007805100c05804d010500c0d000070641204402150120304102c0000c41d9288170600014005010013208100000c40d0f00b0043c01804404580441150280100f054144680302c030302100b58500140048034940190785000403e415128100c2e809402c0410700441c06101c4141031003810a000d500c28800750b4407011806000a40750012101540c0e0180d4200d04803405050058901c010300d0581d001820401d46058401d02005030083c060100c140e505202c6940c4601d84000d8500004000091b846902442c041040d0130480300e4106180c080a002d0700c1c1807a550749140280092503080546141c1c110030030050401c60040d181d07031074282e0215a62b030004040360020a0b9114004180c031261400c01c0b0100c0f1011200360f9030804900307141020040383e40f001d07520340100904028450a4004c44004c1c102103814540440c001450080068201d05143d18124085403800409030600c5041841044195140d4413041c2c000d00301d14003e0344003c1004440c6000b40107451021460180280c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 914740845 1250 914739595 914739607
    0x6010c02150405191d0114241204060b0f0f04090606030b0f0907060306080c010309050c0a120c120f0f17070803100b0c03070818030102040e01152f0709020d060317 72
    0x140102944441c00c400b0b403004490110314040508d811101c2c2045043c0242011900d9040311a045c00c0c6140304a108900070321424501c170080c0000c0b10389190f007045d0711a1003860340000354203096000304603882c01500040344131550380c0c035101c00c0d10009540e4068000c4090301004403640082051000400c9a8a400c0040301d2a1014107502c80e41c40e400c05178105916840b00000b03101c420031180b200110700030407800e141d80d07030b400c0606005800300b0000c450b040e9007054001205025000c0386d55032260420030420030462aa96840b03108401d110084030b503104c65211032001c1c6003505002e485418800d40341c00b0741c0c80c1408039801140c1c1515a2104187d01410032880a04a02c0407050712641daa00214403615402026511112280f0b4210843e030107610200b00000e06205403031049040781d0780328000341088023090348d044452101300440310841a4810800e014050b500c900c40c228001703282c0003642e485580340c0c4c3d46002660b102c9d200380d01d6116101c0c030080c81400f040e240c40c20001000724041c0c070b2401d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 914742095 1250 914740845 914740859
    0x608060402090a0c0207051003060608061005120c0c1005040515010510030b0f0d05070510091d0a091a090d0201230c1303240506010c02150405191d01 66
    0x48002002400720340d49403504003040900030030020380641002004094230203c103000050051030b041c030442c2d00040079000487d8282c01c2c015400c000300b10301707580c80078078100e90100000e4071080c0190a5001c2034038104003000740c0c800140481c0c81080f00c0c1407404a81c509160608510344211200380030415080c80c001000f144d9260582d01410030907074100814040b0030310001410224110300c20540024141461804000780801c540e020758400721004103d050303079020200c440c0080382c00ba00d09214003688a501d00340d1900385170f180e40310340c00c090049032030141c0799030382d01da0f4a0903240c880e4510900032051200000003801071031804a110310003004007a110700b0100700d0182e48008400d400e11440800700714920803442c2200c5400045032010303200e0503a40d00d818205024034030030104a81240e088084440c2c42d09003d00d80c051072050355000b01d0980e1540800458000b00c1000000b6404104400501070700c803118228a1504424001c7c45d03450300d442c12403581c1a050140700d027602e4514100510000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 914743345 1250 914742095 914742109
    0xc19023d021c030c170a0204091d0d0e0f04021b06151806010504120c0503010b150702130b100918050108190203011116050d051303060203060d140a05010608060402 72
    0x8502e45004904008120001c1c1d503401c0c4035200480450400381d0401456200300e4004104a83c0250400c2040d032540b406010302d500d4004580450a4121095100d1820b20943c00d90301c18280007060300091601850005007264484e02e0303000440d2072000c407940c99000c01400b2f078640c04501c85503c070409182180003c0c042d941c4500c00345241003407043c00b0854591007481a100508418036018141010760f0407c5043c40c500c81c8212446982081032021803410325401c01c010040050925a0074900d8a0782006040421142030310402940c80c40303000480da503420850030b4003c04546922060505000c02010341440303030620500d2071410b01c401004a40000505406000001c03c0c0707090101c520b5200082c090060301c04c4501c021400400c59540c494004450050864030840131103a00c800d0098064455008858420440e0b1101207030400c0411201c1c3c00859024400800051000220b036036072186031908004410300725070094803070b0420001c007440b40c080a42000001060145002e0b8000307818 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 914744595 1250 914743345 914743393
    0xa030f111309150503030307091e0e070f021612050613020d120507230c010f091e08070308130f03050a17130311150c19023d02 56
    0x31681e41d0007030041c8843c10004810f024001c02000d4076640c1c24040001000716806002e1055040c008814000007200c4036504c0c2411651f9581c035044940d130f2651000d540b00c1c40c5c2101d24200398040c00c403c0b180c0903403401030f1301e034050001d088404000c00f00504015151040080071230010b4800394280c90003581d901c0c0c000581e0f9039484180c50081c3c0c2a500e5007120341c5d000e84040101300380059034459181c6c01503581c94a0280c900031040b244464114801100c03480702c903840340e0001c200c00e00070038040300e41200710502da07560000300d52038511960307080018a0104640c0c41503420301408140407402c91031171103095000300721241242c0403440c1152a46a1281c24403040100705e9884001c11a201c0e680320000d0311549096a44110346a50392418201040703005200039610400b2040d14041c00109900c00340c1c0c1c110756521004000d0315490410245190302c900c641a80c0c0a005500d040725001c4005020000d20a9000900c1c071410b0242c0702c000904007060303980740c800d640080c03002030308950010010f40c61b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 914745845 1250 914744595 914744609
    0x3040f080f070606120b09010213030303110906072d0b01060305061c0f021003020a141e0f0406020d0f17061f030209030d090302030a060e0c04020a030f1113 69
    0x40d4800301c45030520401e1048240061115092400c00110008071403124040c42e8080d80701100305030b90b81040e45080f8402c00500d880c0c400f66400341840030a100e50310000400d81c07091401032074050400001849608943e00072103a0800ca9400040c0c50051602e13003406c401b0180003110070705480c607940c401c0181c1050003003404240c0d656001a0940ea41c101140003450030541c009883c0052a0070b00b03001e041c0c008041079014038800124240140e11910032201820001d5a44c0b51491010715a4440284c0c02125041621403240c401052141103d10041080c103011a40b10340d5650b01d0081e0190400403180b00c070400340040043e0151200d80c0013041c50803030785401e00f480840d540d00e030000111484011004864400d8500c0204050250180e000384004030003102190b050004500c4100c038043c095000094164001348803820024415802c14018a54400107450802c082c00d00070030100c0c0c01ca2664800000e860342400629544c00d48600c0c500054140c0c2d03504e14100c00781c00002c80d01c0c9204c0c441c2c42c0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 914747095 1250 914745845 914745847
    0x304030302090d02040f05040309050a08071715090607080703050f060d0c0801060602011a040606020a030f0203070b15210613111903200120160b04060e0603040f08 72
    0x200c643d907a00060b00310042c0e4010003c00000040000101c000c103000c9900b200818500320001c81d092070a480c8220031a00e840303006000050601d00d40104400301141c51114034800d0074070883c4814036a24040b44904158002042c4c18540440010003c01d030291464003454035107030500101015039020b566214070281e95603150b500c43c628080d42c0c4640e003507000304007551904001103600c83d412f404c4089101d000103460034510001c80b00f00000c0714414460440076a10022200300000e000c2c04404145a4250060340d050113815203c803000c0601c100e41103c8a0051b10718445101d00d000358102c00400e0000d40ca0b4411100c03880c0142c1c0d62140050301780161038101000e988100704e040c8103002a00c00000d401c1e24500200300181c0c50080303140780421100d9800801c08401d8a000e5a41c2039080910142d440c11807224102900070344a189841510880c1d000d86403100c40003500708492200109a00000180d641e072400c0310041c6441c90f41986a4800c5808000b1301020032041180b400049400c02115 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 914748201 1106 914747095 914747107
    0x110324030a0f08071506051008040b0f09100e010b031c020703021c020306090c01030f0c120c0201060e040525050112050406110711040c050f0304030302 67
    0x280d050350003260308002103400d00700001c2c07045004010591504203251145245141e12841040c01c0c1a11000200818101441074169005051078602d9180c2016074a02c000050043d000720301850859011801c5100d082c0684c5000c1a8001000c102c0080b498000b280a8030380f0340285807190094048a04842c083d0750340010002070564064080c25045600300080c0c0c84a0403d160b0b418242420795400507201041400c2c01803030407400030003640764030400040c02e55030b041c0f00c00c1c40c2e040c1c1004990041c0725002590001c142402c032502007840001640101d00410181d40050384111003401800140500480d910b408541d41c10303021100c6c070300860000e11b054529071159900003410460856000180d5500c22900940704030700c0400c50300040e098040864000c20001d85040607100c0040c801e40c500381c42580503050490501ca800c0040032074015956010007003000d02407580001384 = true := by decide +kernel

theorem cover : BRFrame.Cov 914568345 914748201 := by
  have h0 := BRFrame.cov_init 914568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 914568345 ≤ n) (h2 : n < 914748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
