-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2721
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:32:38.403818+00:00
-- url     : https://prove2.me/submissions/765fcd12-532f-4945-971b-c2c7014d8fb7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 489208633 ≤ n < 489388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 489209883 1250 489208633 489208639
    0xe030d17100803040e0702031c020a030e011103070c020a0e070f080705070c0e04080c012a03150302090712020d0213240305090c0d0b04110a1d0403050405220605 71
    0x40907103000d110310b60300d20991007036140124041d400321b28114800d0044404a0300c0c4848258100c06403043c2c0c0c00c00942c802d46408001c686002c0110800303200601500c0c83c0d00407112203042c00e6035224841500c0d10f10090108a900220f92240400c4110b08801c0e514041d40b1255100082d24418840181400001800c00c4052041c103026032000107a8010bc0102556112543c240181d02e851600c04014000d0101d4501c495081c403c1110410780003e22030314032510303041c11039405078148d1b4034180c048030401e2464160440c400c44c02030015040560b65a070b040030b9203160601e0039104900c0f1b41d008a81280035002811900000c031008003022504ca001c0250415400300d4114203001c00300380c41d4511540a00105041d11240050040202805050264900a003520900321414545004540320840d03084410030420448650b0741c0c10101d816605440910700050501302e40350702d1011920100400c1141080420800402c80e5210600150054424400c400c00101004030380103007912019000140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 489211133 1250 489209883 489209911
    0x6040602190809063709020a0b090a140d050304140109170d0c060b12031b01090b070507080403020a080a0606090e0309060904111b0105150f100e030d17 67
    0x25051400b00740b41d07400c1203003404404229020180301a04040012500c007a803050100c40e90a2061406c2e040740c0b503143e200b2a82c0d060216142d48841c40107009218070315170000e0100c0000c2c406044075154003c04944000c0c0307045a581100c1d603845145901c10341080005840401e110390381135070060103500260200c4441107008010744000e00b0713a40d02a0782c4a43c2c041243c0904a0b2050000c154003101d507005010b1702c1d90803020030031401196a9031004a89004079083c802c00c60752034407418480e10882a0f444075142d035058a80480840f00340d0080390040d514003008000000041c0da40644581c02011403c02030700c415842da0409000702c40c00c41c0e008541d11800c1040b030b81c02c0d503107011044540000080381d403203807680d01c0c88000c0f50061aa5641c000c249000005802e043c941210060006440c0000e00a0100c0d03945c0d02c0945151035403140d0741c560424110043c034401450507041076181040c0394602201403051080c0043c1c9481700c48281c500c0800e03009130212141d610340501c80c6902c10301003003100b4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 489212383 1250 489211133 489211141
    0x70e0c0307031a0301061d011502030f0a0924030b010c0506010b0706020d06064109120114180a05030703110f07030305040e060d02010c021201020903060406021908 72
    0x222488010030305010165100a80c0008040a1542d81c21614010740200016a260201d2001880e50f440c0c3c1c1461080c4c0103c00010b100c0310b40408844a151070390f001c0c41c1401201903140c10345420040d031f01d03010701610200205540031076a43e0304130182803001c41c80c11542c0e40f443d0701a040703804840c5110b040207000706507000401d00010309241166120f440155a440c1c1c3c81c28004024010070304803207170396405c00e1000100c840d48020b0a0002c10b050442c0e00021800c2564600300e60341d85030422100105036002d00440e45161507014101c0300d280a004603448040c81c940c3c40742101d0317100341c0c030280842a540901910f1155040349034180c4401800802410186450b0241c2e41e000d80704000302081203007141900d001e0000d10907844202c400c101154649902c0340f501074000d400034055080a00007000003d10245418410748105580603150083e100302c075902070103280042070403020b60380c0d074081020801030b45042120304d20850241c400161542c1000002619160285200c00c0400494000380 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 489213633 1250 489212383 489212401
    0x3101e06140f010f030902040203041a06010c1122020705070303030e0706080408070827090f061c0206040b040303050414030a023609100e0304060e0103110d05011502070e 75
    0x8031942002401c2c115481c0624010171000b408402c1c40007034101c0c0c008402e103c10000003691030b08040d4203030704c1081001d030b1f1040b00440369900c030104040e1041090501042e024209890180707054403003140c042600c0805000788000b680e20280e82100c09074071281003001495814481c4000207031104000c0c205143c50303c500100303140c01c06000500350000010b500380401029404558042c4002c01014490210161071100c200c0801d0700c580c0d02500d50503002401c0440310780d070b2241c49102c00500c011a0210120903501e10700100c46c2c0700f240c00883c1008007207880314060300940000c61203541d4499072a0b00342001d010740c0340380102c0543c0c02580425a840b00581c1c07110030811042800d48800395180300c082e651100003c85c021211515626400240540304002280d064030340780308214103008081c08207540c0c1390b0300c0c4079910442e80003841501490501e584640c001000d00e105104030306092101c14001c03481141e80a9010210a13021444554241c6806101800050400303219003aa540f400200b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 489214883 1250 489213633 489213649
    0x135030f03130209010f181b050c07030b0c090a05030d050304080d1e0203041a0c0901030c020304091d15040308060d240c03142403101e0614 62
    0x3188000020000800035a112012010ba142e0000c0444081e565109020020300c125030003031001c40d03510395500740f50a541b1030240000300c0c0400031120342d012500323080890f66a000250221500d00074800000007113035015044900400c0040a41e544da401e1000c10080040f0f01580041c1c001e42206546c0541681c10a00b0b481d4055040040696100700b036a1015005015190000c803006421501d0380961170201c0d80070354400c070310807070115401100388030610710031f00c008a40070030354042d042140320341951082e0011401101280104e038100340d101c16a89042d2407084109450b001002c040104403a00c00b040140307038034001600380341e071070b400e094400800e8068010302890240c07451034590340c2003003819040b034110311142007072414082c0158008880034100e6403c06100003400e00d080e0808030901250903e02556185207004100e82c0b120340c1c03444504c02c7c08040e050b4107001700041c000d12800e040c001c051070354080021852108841c490a9001c49501d90090480c20842c0c00004a05480b5049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 489216133 1250 489214883 489214897
    0x210601050114070503030a02090f040b0a15030b03120a140a090902071505070914030118060504050a080d020d0c0309080d0b03011d0c09011d180312013503 68
    0x1900c16200103032002c078802c1d680305040004240d80f200204014500900741c2c040d2100d84000c0380c043c1030165001007040156489050b8565005800850401c032180b00000d0540500e80360f414007082c03400582c400a4140201520b02003054000000c807a003120741d12240c164084007803080e41c181080700b103202c020040b0400d401200b69181d4001945010b10098009100e176480c448441440340d0310b081d150060828a691250380b03048886407034401c02e02d141c180601074030010b458410740090800c1c0d403203103c0502000380c404d403400d01920700c0702c80121b05060002e0085c51403030300000d0303590a04c0d5881a401c869800541c442010701e004080d40005032100110b4404000102c2c0c08145080803100003401012101c1d800c194803040c1c00c90750010024045801070910758201c60401071aa69002c2d0308211f04004011000b40621441c0041c50100301031a102050361401401c40703007858405181660205001e0b0003214411540d848400250400c801d84030070887d0081142c10170550303034000c465030750b401002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 489217383 1250 489216133 489216137
    0xf0d0314070501090606081e010225020604090e2a1315080d09080105060603060604030b1503100b040b0f011d0427050d05070809010c03030f05152106010501 69
    0x149403092240135001062115000003080005a0382c0b40f62055032130031361401503403c036162041c1c01c118511041c82510000342d403100039520b10802c000000d6201200710381c0100c2c0d100506110200300c6203d944030744403074a86050024105600341620313043c80d8070354400001030100c6120104103115243c0e9911300040f65120f20f0302050901c4c45903420302c10140e2907000742c205842407102d00e02c3c036190301110100840340b40400810043d10340c01e09009551108840290304444100000c10019a00301c00840c1c2c862110700d185409a513030480042c0c1001e9042d15401d600b203403121441846d91805200d000c04582084a18201c225030302d00020f05580c12100c0070528004124400c0025503c031900320a00c101030075600c100d070340a0840c5032800a50384c094400d03202d070722a114002055600420480b90090341080e4402e082801c21001101c3c04401924100c04141d11044030750170355000c0740280e6001d401009080c8190040c0c0d0000e202014042c8201901107048d99140e07450b41110104020f41590800c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 489218633 1250 489217383 489217387
    0xb040e09010b0d14031605071a0c0307021002070306090c0f0806090a08090406030807060507080903030702070905060103060b030906151008010e0c0403050708160603110a080406290f0d0314 83
    0x5490340b01d003180104184040905103030030146c001c1010201304001500d03001003450003d0303034031210309142d20b00801d84000d665074401c00600340507140c8840c85483c00c800e88d1044914091302c0360703100019200031034801c84c0e08403a480e809000401b0b052003040b01510383c130b134010076280c500300d504541d4840c1c80314800b40c142600040c07c000c0a4550340c20400c0515003241d132103640c1d503a491614bc4020903080b110000000c1d181000f15071030f124040112401490346034010310740603041110795001098040d02c501c1c141907440c0400650707000b044c00654440e40702e01010344140e02d001d203108108110300d0310060f07210701c180c0050544801e810410750b50654002c012034000590f51682480038610898102810a02c10b861002646002c001034044082800750b00441c040713552814154252032003d412600031510501201e00d46501c140703003942c1c3c414016000030824194101070142c4250581d0b0b00600b5580350041528180d081881c28490009010740349040d10b00c110f500c00a000b00011503580c1c5080c940 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 489219883 1250 489218633 489218663
    0xf040b1803010609020a440f070c03090b1c0c02011a06040506040e060a081608010e0d122a0c020108060a0f0302090903070206040e0609250e010909060b040e09010b0d 73
    0x24007008085241f030b4104641005000c09580b04030303080c1c401c603284100900e840000808051040c0c0d40d20040e964152142c04450f41130220001d07040e080102590358203c110700003803d51120a000b0f00c64450f00720f8000040300407080000b404000124030407035004440c1048200090340b25002214102c0e8a0380310855007540351540018484200360340424118480c0318108040c100e81c1c0100901110b98035002003021007074441b0342580f10300c80900c0150101d60112400324408050740c104646801c4668618803921001e0080004484521000c0400050140814904658119039441d8105008440c140c003110f10b018824500e8448038000240600b41c1c0740045100d203c030800584000da0340c010009500c2d00d0b140d0783e05000482c0c5c00c40b02c2c02e214113180360104034141c82454504c8070200f41c9405070100300c442c03008281c0c0e58401c90001d03030b4100650610002a00e03036092203490050008100c1c201d9a851070001d1202500d80007510f051100e924290000c48559150910b07044241c1d4002d801c0400807203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 489221133 1250 489219883 489219947
    0x30b2b0512030f0906070c02010c0204092a051f030e19050307110d0c03110a050301060b120c0c030a0f0302040b0307020a0b070c0c0b0f040b1803010609020a 69
    0x4421a0014114072618558501d05110100034610903e1640850803a1366500c090306550b034181540c0b0800811140200440503500c00c0c40c1e8101124005000410030070640e40d40e140d03405000d030001d600334a85405007040306101c03482c04840200800c444041403c2419034004405c0800041410203141c0c1c0c40502602c13110003440603c0320101540c906400c2c940e0380c1d0070301689980c48100121451418007118644918100340c4114005400501880005d03080d540e0341011203070121140d239030000a00c00001810b6030b0900884003d8107104000c59140d1031a08400041c0742000303061030309c000d01b050100020411001059840891075071410a01036280903c05600034461a0000741601c1c000104000d200ca400140445a251184481c400307503170744c0e10307030304940358000b0100041090580d004104046a05a0090a80d0140714407100c1d00d041c2d514004034006600203a980c3d40c18017180d04460380685800c3c82440c0003030414403001c0d460f00d66480402402800000d030401510440310411003400c0d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 489222383 1250 489221133 489221209
    0x2030301150201180807020a050409080904050c040b0c011406120d030c1806030507020d11030f0306030c0315042105090904140105102303030f03070216060e10030b 72
    0x103010b034448060138944c1e508203110903502c0350030181e0060300f1840300007415003428401c80341e0840e04822b12030300308590101040058040a80781405090b020f003c0403030b45900040c0200300c500d0521000044220602c0224140c140004200318491094034038a00545040840e10407040f051f40e1400080c20202e03550182e510110084405074800b05114010404175003660089009070b00c10b03022034402e5006c00d0012200011035600503c0315802c1440040c002e24400c102541d0071180040944003100b90000210b858100e5625014200650000038001030100004602640c0c80300d800211052640e5940c026200d440f07825001801a0b440d80b0000c4c0a0103400326007014100c5500c402800603062581c142d2000c0f100600a164603888005004101d0000890711036500001c040e0165081841c00d21900083c0c1c1c00080c560310950190000603c424170024003500054009a100d0702a1002000c00380325070001d614003c4001d15161044055481c0d4900c1d0f07400310903001210301e402c02c2d4108030607448803803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 489223633 1250 489222383 489222401
    0x20105032d0412110a02101103161a010e040506060904020d02040609052409040803040f0f0303060918050a0b0705040305060a020711010c11060f04150c14010c02030301150201 77
    0x4407050020b1208000715101d4594141c0c41d03a40d0f60384020710301015002e480d4106914000c2d88600c1005204507003c1c010b422842100c1c0c1420f058909249400d0784149442c81027600440b440c0e9406a5060601070084140d42c5c05841c0c0101011103c2ca03060741d034940e07900001703040d4a1040c540c000010b421545c500c4c00346681e160303001c0c0060106a0b500c10240c000f40c039041d11803c203c98840089042c0310003000305070310030f840d200030200c11494039180c4504515a01c0680107488002c10886131402141c9403514941200d0310942d80060b40c1442c1443e51800c580f10320110040382d03040c1c0d1086102203000010750440f032680144800d202038841040c25645c86c0b003030743e00082c0b00b405410704000c0340f4000c3d0303400382440324014040b22004201c00d070011a05000d00000080070080304408030480c44c1005000307400d80c0c9a0740400e591900703803901d94151503c42034101c0540000d2607840c91034104543d0401907a00680010001c2c88101d00080019440340414011000b94588a4a40441c4031f0b200350000240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 489224883 1250 489223633 489223711
    0x3210e01021201150e030604140c1c030e1f030f0209030f061006022404030c0f060207032d03020f1201120c24050c0721050f0a02010503 60
    0x9920b140e2081401c002d00c00b48100c0d03050026480048100701c1c0150069200d8600c0200944455540c0d0795a540104102c90140c04051044140c0c40445445100b20310741b42d0403e0000a207102803807460003e01d10000c480b240ca0244082000720640400842c1900c20743c0002420080358401034010b01c0002030040c1c1b0800d941c0b5109049200d10141e0002c10294001d00c0e002d030b045901c00741c68400c180e86d2070001840d0499145020038140c40003c037a5952290014031034034260303a001455869218400c45510801d0f101250b0001c0d01c501050303003000014007803c0c0c10003201210882c0c01c401c1ea041c4c103c0c2c2c20b054003040c950001481074241c40b0300c0741168520310a848140465503150344451000010b400011a42c03c1100e950204101d4005965226030454461144804411078401103405804c04d25003516280300300301c000304400180306005802c0150815448546c0c0b941400c102d0f05d00b5121404c5940142c00c13041236080541da2200c2103035400040d00807280c0220392030184550721803501104002c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 489226133 1250 489224883 489224887
    0x7020f0f1315091b0207031704030602070b070206100302010801140d020315011e052b0506070e0a1205060f0603070e09060f01090e0a02090c040b0c0d0f050703210e0102 74
    0xd400c60441c840b800c00d03240350350303810805140803100901241d04142d00c40005a4404801000081c0a0781010300c1244072107495142031070b41c3c0b6500e4909a03005207a00b2a02001c048081021084c1e04000956002c60003041c0314040b036140d500040c1c1300c1179040c003075100f0440300c18038816450344130407048480d401d84c05811500c0303003904089403c0c0400020300500343d0030544201c054080301d8038241c1510640d140203003048a00f0b02194400b100b03d00302840f1f03d00e400e101040d0340c14040360050150600c0f0720f50a468941800354801d04102c0c62000a400156000745142607210200c0d20020710103501040c1c00004141c0da0311038400013071030922a5482103044c1e038070440400541007000301e11140160010250203005989901800094580100b141006c5510095902015280400e820350b00035865160302445c0136100e1701d0001d0300c0d43c02003011010540c0421050901c040d848800c070200b40855150040c01d2020782c0d07400408a60140c59070a190106100c10a1603084080e1301c00b60000c174003800215 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 489227383 1250 489226133 489226151
    0x1003170c0313050a06050f04060804060e0102030f011701020a021e0f060112020a21030c060e0d05132702180402270303030c250f080706050a0207020f0f13 68
    0x4450103420b0040f01d001e20040f10000440380d000700c055804a1044090203801e06041c100d08840f04100140107440c01925100045120142031000354068555429051919810710340021071843c103104050384141c3c41005007101a40d404aa0400c0100f0380f90410004503409131840751078900382d661201c1a60251000000303c46254005003040f0300d02c00e0703410300c84207951505a2401c240c24919900f4446204079130f1000064400c80d1501201c0344074040006402c03810f600c49030b1900c1883e001000210300009541c03240f803650507040380010301d60450500485000c02c02c0d44665032022400000704260086a800a0609030492075007000b08080c0c811500e845403249900c10b8403020300d030220490368007000e0081103414048101ca20450320305004c1480c000b220606401246010210040c80740d0503200e41e40e00140c40480b10ac44500e01400e81e4603114901030500381c0442e1070107420740e04142d2040001c040161181c9a010f90804021075800080c200050081000e0901c06909000380910b001482 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 489228633 1250 489227383 489227407
    0x160f080a0f02070843080c040f1b050706090602030a050402011106070806120309040f020a021009150e0c100513080106030c030b0403110303131403031003170c03 71
    0x2031100d07095035a08451010f551101090b840304a401e1920002c107418420081905800b92141a40b100b43c1081310114400c00c18403000c42542c094000010541181810084614007802000c5103460032013010401410f03a0403880306e004c0c4038032110105002c80400d944080c015240c0c40080b2054100406641d40d140512580005040450b0204d020864248514410342400100300f80703d8007054843c5c07d0207481c1c8404100740308070401003058041c44100100c10301d603207940c0030320464404030080150b03c81da00034001908204090f0341c0710b1285860f2094403008035101001c18034914030718643c0061201400440725003001501c81540360001d107250365003100154460001c280c0748c089103c20311403460311050254240e5100f071001401241040d0018004503807103041580e041886810322140d003025640e00b030b0703066400491304100300c0540d14225805008080c040c1c6915481e00c20061883d5141031426009040d4a6000180240b25100c20854101843c08115407252581c102200d4032010480f01c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 489229883 1250 489228633 489228647
    0x30415110706021e03120c0d02160606050406080d0c020402090d050d020706080a06121e0c141801030506041101020c0613150306300206070f02010f0212160f080a 71
    0x94403020111454102190044250740c8003030350380a0380c0c0d101a00c0c2c4207a48261f07500710b00d8611502e15801c102c080032110b00959540c00300c43c410400030826a29100401c422606507501011554204420b60410f0988c4805900500c587c110b1700162a0182680880c805810f0320300000c000e44140903031600308903000120701c001c44846035601c0c0a5541c421442030700342c40740c900c2070f151501c2d40104040c00040b208446c1440c07906c4d100703040c0d0310040002d4a0301c0085142550004800780e508503014070a9041012011240248110004086500d16550165a404003c1000d084518609200c5840768800d00c440400d40c04000c0000e0f4490050500c0064030f10703124801d03100007103009408840c84500030b000307000403162107954910316203d180e5100e8610803002015480001c1d051800e11006a4820016007500d6020312031404600b0a00d10002d0019042c80c00315400359031040000d00c600e28a480102d58080c41c002c0b8000b50100c1003440d2120040c40c1c1204000d281020229a80300c1d602d600c106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 489231133 1250 489229883 489229903
    0x30c03030207061815021603080c071a01080f0303130303051504230a050106021509011509060302010318170a0309080c0105060910050a090b010507050d0815040e03041511070602 78
    0x3000821703403c030200c3e0022441010000f1010114404950303011a0081440c4c561003c081203a052411101e03a96181c44000712000d0790000701d8640c030040c025203600304904807a61081c1001076141d802e00a03c102d04002e2401d40040400d500e54000411080d0300c0d2040c1002000c000d4824002c0e00b804680251030001e012032080380c50741072400007a8045800b40240e9040790101c1d0047c1a1144103502c41440a900003089803809640310481040c103030001030826001050403400004401d8114400142525910720b031076080da4403a0300b000b0000c5607000401203e88078a0030f1000769540e0000c02c040d8041c0802e0000038180300008260840340c0401034100038800e00c0c04581c400c20640c0c3c0c0d83d494095071b030124041c2a0b000034110005100c010051780c07042003007020504149003004016665680b4000240d0b98a41c0049c020303505000071000409114410303490101d07018000f400e0318620030740d901c0c0214440e0421414511510300161030103240f0322162042c00070141d821498031080081e555148440d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 489232383 1250 489231133 489231143
    0xf030e03090f211912021c030f230405010c0504080303070f0905130f0c02210f3016020c040504050708010903090e07021504030c030302070618 63
    0x484018628000841200c40c0034400800d180480c210100600c41c00c03441c00c40c074181582c4200000e24030402030400104185500aa4078030018030000c0c50410380c0ca001c411a100d0956005030340b4004185000c40701400024080d29000804002c0c9240081c054403502c1c0702500b801880320300f5038a40941c025407044c4141e00600092009082c5d09400301d68520442c400d4140a40003880400e02440c854036846a51030182c1ca03140390341607100c1d00020160501138150900e10f9075201c0460645d82504d001e0341011043da4000382071a4400050605100740d241c41d6611943c500c001180851008903c06071500461110101182042404200290f00c4800c160885c1440c031010b0002d07400041d40e4411043c000c0c1203a0280001d5070481060102402e80500116094003504c000443c601d0030911404031140d0107951001580307890900c1d00103095a01810090440d04003441802d9840c02180b025a085a814907007603408520700c1c00c00300c0080c02664002060281003030049802101403110102c1c0040c084e03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 489233633 1250 489232383 489232391
    0x40b0a050c0d11031b1f020904050a050108030a112104031b0f030b0901060b0a0203090109140102150a0e0d080619030b1308160c08060108060403080c280f03 69
    0x72080c1a251070f41409400c02559100b0810341803000014007100b2450200002100c001d11460b50442990700d0703201d004414240e0317000c41c0110151400380502c0f40c0103100c0c00000c016550401c1c2810340c99110f5a425401802441c03508003080d070f00108040300032072000b0b0300c00c09400d020549000b4926885481306441680e0301e407401c2041d80c89400e41c1e0808031650f55a00180291039036584020b02140104000381d0341d5690f600000f180ca4071710b401084074040f10390245503100e1811300050050466500b2040e5404005006000039980000394401d00d140208200401a45c3c2c0d061080c0140000c901c84800c3c5001722004004800d1b00074400714040c0ca03044802c024204100ca03900c0020b501e0714031010700000c1c51031020600f09100410300075107450088101d00d142400040c61030180c803503007403000c07202a1701c90241000025024003c042c00343c107045010b480c4906058400a15082c0041e2540c4003818002500e041c408900244090501801c82d26580006070b56a00140000260180d0000400d081c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 489234883 1250 489233633 489233653
    0x5030115050c030304060b04020705060a060f06030e0a0f020a12150501080a050d050a020102040f030803010302030d0f1d210c030c120a06020a050906030a060815040f0b060303040b0a050c 82
    0x118195402e6110a1000b1811540c4070b8840f10050301103000c200c3c0c0c01960801241000c0f5000b032080502c00c14071140040b4100e890b05a0004114400d98801020549040203c42d24440042500b01c0340c10781040d0b243c040107103a4000143c90782da041c1c0c440b00c06000d45415000400c5204499190034034044801000385070307640c400d0180c980d25003a5000f4525080040e00c850300c1c5000704054907079841a4400141010340b100d4944880101fa81c2055a41da08003100400031450204401054544a4074050440c07605000e8047d040b18000911080307650022030700300740c0546450300c450440756414480500070380304054110f51140e003e003111601a0107041e50660440c18181801e41b090f07a1060002c150800040d10340e18001d412080550b000c004080268103a1561400003450044501c041c0014880349401444c40c80d010b040c041d0250311201c454100400b180210782d02114440e0050300150160760b542000074290700c1182c212018044010905988042c1d1007400303441c007001c18404482603044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 489236133 1250 489234883 489234887
    0x50a0e0a0c091d090f07090902040b03011419090b0705070512030705041e15020304060806010806090a0209211b06040e2d0106080f0a090503030112050a1205030115 72
    0xc0d10b0242014034800f9a024a20440400906a9222403900c1c00e0b00e00071440e1100035414180035901081c96561145c403c02c040d407400380314810101c44102c008001101c0e040d54888503281d8020041004030f8082030100d10001e40700d4100300e080a42c8215000528075042e400a002908812419a0303144200b46d202a0401d103482c0459005130b0090702c8550409240c9820856000c055a184400060005100044a1860402d041c1496903103030091502c41c6d007000c00050842d14000c03d0320381041180d4007401764540365000a0364001c070300d40c180561340c0c0c041070b0085403d5402564401410884000c1e8100036100040b455045101800c1c0b2560818041c5104020044c0150302621107091440c0b0089246a20320988443d270100001c41e1140c191030140e510400820b109901034008500712f0005c0151440001007610360200013454100500034032500c85036502e0005005030640c540c1c20010313210600604102c1c0028455100c00ca03c00f140d80c01c282c00502e190000c0c441e100c14400c90143d107600041c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 489237383 1250 489236133 489236147
    0x15010918031e09030c27110f0f070c090204180e10150e160e060c060f310201020f0703171b0d08160c0804120606050a0e0a0c 55
    0x2030701561545590000951200c102191075500c0780b061100004001000507203042e030100081001c414400c80d090110160504200e450306610204c541c50503007003044450840c41a140101240055143c542c581080e04074884c4c270610300c0150007208269000035008861fa0014015208103084005076000094090010307203e551141c0c0e9804d8100000c203112020007948103020041c041040001040c5c3d42d2810303210341040640700e00c52612506880b98641c81d412850354030f03000c0c0095500b6450142e003203031200e1311600060728098150800002003800380c0313038602d2030003001e03040c02072000459444803d24141c0c600340301100700c2c090302855015400c10100407a11100301d80e04180c46070b407034034581c0b002c800040c3d001003a4032101c00c45952103074026031410420326203800d00c00e86520700c0c0d90401d01600c0028045400c104020400890707400b000161046054030100d9400107907a1001c0c644a160110103452103400154114214440004080041e0341106001e1943d0304000c11884003580001c07174002c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 489238633 1250 489237383 489237431
    0x10080f0a1a0603010902060c010203010608063f01020c01020c10060821130e0609061509011101020403060c0c031704020109060e0102010f0e07051806032d150109 71
    0x140c000c0e01c0440780d0261080081d282d020200800006095040b94009003a580188240c11820381d07010005115a42e0050329440d00204229000200e4054082801048400c440c000b40e0510711103549050460120a07401c1c5c0100c0403040c000d64070740f9103020b4154002d40240e4a10b044611400002c100c00b162988034410070703260006c01801d202404085030490082c800a00909000c0c02009101c002580300c41d060000340c085107641441078244007040014242c80600450710503541a411150b00d4900b182c00c07a01d01c0c0c2c0003070071b00404180109000b81c0c0240515070015107a1030414840d860190340c0a158240c13298481e4440d44103410301415880c80781202120700a011035010078050190600440c1090150041403002007038000c43c5141d080159203809901303101c90b6100e501e0030b0045240206040d00030316011a0000254903104000035903500000342c0804901d00504a40c00744158450300b403102050002d0104d6002c2400708103007a610100034441c14040c10300d412200515420440c041600c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 489239883 1250 489238633 489238643
    0x601080f12041401050a0c0218190b0a210f11010807030e21070203011b020c2e11010c0504050406050102060405120d020915130e10121a10080f0a 64
    0x14002603040195180da01c00d204880034400800c0b0b01f58016540c5d4004a041d005c55144101d0450508840d0916001115130215260342e061a003988656258903e4840468503145040d400110720021302074640c1080380c0000c0e240c6603515a40324107108044100c030b4a40007080e80c1d4071140b547c4a1400f00c0844140c0907031001140c22010a400c80b51010242c10020441540c102c0340c40c003c00b642c002402c6980c0c02e400181c40541c2400b080798101e40511140c0c4210805482445c0031074000c0d0103a4640903002c0c10140103200b10b1640c445922031003400e0700c26000008000030400030100c10030203800f58010b072040301d210f00e042c030401190651021403014012540b107802404c0340550328079041d80540001c0e462001c040d6080c00001030300d079500707240c21b450000380300c2c4140d54800c0c010101282034500b0344c200c642450000014082c0d18107800c964041291100c0c0321000c5441198030b894070318812a158401d090341745040901c0031039030016483c6c0045583d070748119861100c5d62540151241002c02c3e02600b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 489241133 1250 489239883 489239909
    0x30c0607051e0a0318140c06040323010b180f06062109100c0c06050a02040b030a0e0c041407030c030b010c060b0402120c19030911040e010605030601080f1204 70
    0x81c204050802802643d5842c0c240890350300c0380098050f40c084a90041620000d00e5840c100315440014007070070142800646050780703854103503111540f10000030904070030000280340d002c85941034290300400d0b8940008282d80e04810010310314449155023600d03116950006000854400d141101c1120940c0082d6401c40380b1581401034040c02664006018014901074090807034900219403142070540b8401c0d0701c83c0100e144040c2401812100c00621050010388104002c2c03009444c40030036203520024107500480c002d4240d010306402c00c0070700141183c0042c10b2240c212035008800340c1240c81f41c61a0344c1c0070099000c0d101e004506480c4084003150100f041c1b101001c000c240395800c020350f07081c3e016202528041070800308507501e9100321140601841d02207015003000003458841e407800781c01845c051000512a03266840900560043c8510840d134904105010305820340220380207080040644440350b9680ea00c05440d00c032000c80e02e40a80c05030107540b60b4281c8040042c1c03002e5070040d40e1091 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 489242383 1250 489241133 489241177
    0x11e050f030c0a06021b0d050705130207120c020f01180b091206070207030c14181e010602100605030115030602031801020a0905040b061c0b01140c030c060705 70
    0x2240c403000029205400d0700842140340307080d4aa022a4800410142d0f0080156601d61003100075800030f03142d0880c0c403901141c6401d80220740c001440f001034074001c61324480e02c50880f400440c000e10440f440204035288030704800078219000710311018440d00907251040c031030750400011541045101303000407404405c3e603028010f00e2401c00245c13141ca40040c1809a28a90070960310f4038114040702d4160059020003410310822000282c2e4a0080540d071108000b030750001c0e4001459135581398160100040c17102c002403500307007040100386100800c108036422196158440292a06400110a41c100703090480000381800d0521500c0c000c0c8200800070401c01d411070f40c40380080e41c0013a010540e10b84610654885244084c801080304550301e485840d481c500d89010712007960b13031241c119441420140803005045d041c080c5030305003440e003130b0740005039091503140160f85100d00c9a148480b84200800c01b005031620000062482d00c03081412510217a8400a003200e0038454003000c4011034207284e40607 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 489243633 1250 489242383 489242389
    0x40b07081509010e040c0f060e040b0612040c05012a020d060b0a08030901090608070206060d03030608070b2a034e1803070b1005120a030305011e05 65
    0x2903008061140c50306244003003070300054102003080e0040c0d80c0f04010790041c007040140e204103c60083c16080300c04002646040f401030005006201d600e4003541e115180300d100360390344c40202c600141d9041c8200311242018204000c040c005130280300c0c0403c80841d107a40a80d03180300105039114542d80c00070248005144d0034003e40c041c51940c01c80d403481d106c194a22466651001000142010f540210380750100d45000401186080e40402c0a10030080107001030f91b507005c2402075000000341c0d0400410342c064a021802803c031a170100c80240201e02e40811128080401881c3c00c80481d500e0644417122400480c0101303620740c00c2e800e1240d004010030010706400f03000c00c4800502407900086482081e00c5644031000713020042203051000d4099003803060114000d0950403d114048403c080300010003902c1ea01e11a01d140544500315110004002c41041c40341d400180c18044c01d162600114440500d550f0034003c50220040b03805e1500100e0141c641c1443c8408554440c40886444e0341b9090074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 489244883 1250 489243633 489243647
    0x1b0f060403030f0f051c020d06080a0803041e023303010f0f08120702010c0507080102070605071e0e0d1b06050a17150409330e122b090503070c0e040b07 67
    0x2420790360301c9e181c0100043c0c0c0f25041c046c41c88214090800e5035620f207058582005034088111540c041030640100d6400540c440480c5421010610034030b00001c1003411740756000303245440d07807410070841000001048480c4108480000c94041a40b10b42086444052141d1900300110015114a00038004500035610407a605c200090080c41542e00560310350080c03509903030181d0000e480040c1c45105100c02c05a20040d81034264080c203150b4030101200c400004c00e026000c3c0c100600c2082d41241c00313001e11582c4080d01c0c41d44200304035810100d03603a4480280c1280c000080507000b10f500c142131404100c1da081c4900d841606c5400f40020a49403002c00c000003018905410b4a15a208000d5a4003440c440c5144054511085920001d02c4c6140c4004106903030080050304042d8000016042641e01c1a5040c1d0348044a89078030f4801380001c02500e2140d1075001c000440655040500d01c0c030900c00f02000902d6000d0041108000450302c0740c83d120121981543e000b0210410100003492091040e50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 489246133 1250 489244883 489244897
    0x40c02280503191202130302090a02120106110304080105010f0f06080c07022106040606091d0606040203060114070c03060c05040b0a030902010212042c091b0f060403030f0f051c02 79
    0x1e002c5445081d624091017242c002c0a60280b10790030604c8141b06614103007103104c0e80408174500540c6400e0700e004090805900c18030401d0b060087d50b201e00d00e50520706200342c9024059100c020401c0390707035500c58400154580d105102550b54a600c010540611902d40984221004401c0a1500783c1c01e50912540d03495406e068070301200d02c2811900d54131014068140641e000d100c021500b1802c06031040100c0d41d5446111181520380f0420062060307020079141e07407240c001ca500503101e50f12a801030f1011900720400c1040010700054540402104494950590f030144070104044084060141c6961060340150034419905004e1408410312a810540c0440c0c4184140c41400399600790040d4160840d41100344084051210074290545c0d40484014044124100500c10308042e0300c45501d030303814400f90340c80401219125240c4c07074441100a102044015103580c2c0d42e240d61f4100240b21f40e00481340c3c500010442160352400602c00c100343d80c40f4440b403079480540141d428907060300943c0300e50b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 489247383 1250 489246133 489246137
    0x190e0403050d060306020d02090a0608130b09010e030a020a060c030504030909090c08030d0605010212030c0f07030306051e01080624160c0303030b150c0c060c0309040c0228050319 79
    0x10f00c003000203603071400648401c08441101586032102e9900300102c0c0026508400c0811845904101c00c80301c250180c400707601d4104128160640340d1048190140c103107421961118030001407459211a070001c0d1460001e40189010403803080310302c4048007919400d88000e80041d9100405200c060103d40c00b24242910500050404a135a88916400c1d5007000208202c803d59400080155503010300c210b044150008030404d00e10300c0c0c101501d1f000350049603103a416502e8089011000c1600981c000c40103400b0003030500503039040700100719030207101030080d59001400d0100401c03894101040460340c4101c0004d00c0d10100e10508209075007a0b00490304600c0700030b48031308001c0f02080c0305002d883d02650007a980403d45440000500401c001e42c13a51034944000d08100303e41c003010000c640d0b119412001c8036000c1c1d4a10200400c00c1ca1401030910080e84545000d4008203203680024050760003040c0c8101820148900641e070380a85465064064401d8004210144100d60503150740d4540e00d200d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 489248633 1250 489247383 489247391
    0x90a09020a090c120c0f1103040b0a050f0f04090603020a06050a0e1c170a02070806070c02060702210a11030f060604050606040e070201050a1b0c03182102190e0403050d 74
    0x4c0a10005440b940c074513000c0400c00001d410b25003198043c01c0100c40c1d08244d0300940c0f0f024580081c4204600c200340c03d82040100104a2080c0a400c05080f20205681d01d00307195261512154080d0040c080c0d440120311403507540e1400988603008009891000c0718030344403354015104001e124071130203500e85003401e020b16120fa120004d0124103209542c402c40703486c02d0340c0700e40361000e0181c0740c201c1d16002021540c0c09a0100000f8960140301c014205a05031182526045540b02045422800b15030340346803d0740d901c3c00d032408601f00082500444d8000c3c08a040080080e4052646510750f4001010254001e00b0000b5138504058201d65001040549100c0c58903a07580f84009490500355a04c50060b5150f50130311020b030304039000e4400c0c00192502007074200406190050700e030181c0042d0080c02c1c0b10b4405031041c41d0040f1000315000920201020115070b41c0d881c50052006007403080101c0c812100480301d6102c0098000d0361006580d04080c1020040d10b46803020784a6401c440070300729080c0c8d16 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 489249883 1250 489248633 489248657
    0x1030f0204080312090705010e090c0c100f020a0e01140417120a0906091a04030b09280302120f1c0b130c0e03010c081308091e090a09020a090c 63
    0x8100510301d084d000c180086540c1003140c14103060400c039620050410051030900c2e20103070740b4009885c3e046090610701d65920342d040301c4901d003803080d05624100c605145c2441e03e01540340079001842d40c60840d07921151007080e04401500c121107601c0070040e04035002d1009100c03040d69070002449502c514012240005812454182e46038042c100c120300081416404008164104600e04050700300b6111629840c080351020300800d008a22001d88142210400705071038132014072401c101e260240c1c001c5500140a18820943d54100290450040c4141c403000141e0b04280b106944d042540320400c80d141145880c450345824440640c40ca4103a41d07108400c0f031103661000015120918201c40101f01d51901c000003411207012001c41c5406641458810708540e41c1c002041030348599003e00410260b00f0b5410214847e00508912a070004a007002007204500e12840d10110210103c503200e40b580d81b0303800c074441500c80c00a0029040460b2042c01e00100807260482e071142c050500d011115408 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 489251133 1250 489249883 489249899
    0xb03030f04030c1a041a030a0e06091605030106030203070e09070b0409050105090604140a0e031b07090510030f0209041e1505060103090203150711070e250e01030f0204 74
    0x80260b1080f151441060800c2041d400c1254414500c1020741d030380f450419140c45100101021000c3d8004115400000080e0f0320b1440c5138000319030800101c0c119035032480e05c610307602c0c2e907403035a085084000d588401001616180500800d01626800b0340a810b20502d004d9424100d041d02804515071402442c2001c910701c03005001030402049000c50100e00740d4545414498001800380016000310b0030401d1905269401e03180d4940c12440002d0006440050300801e20b0950113500d11040000b155001c0542d1a0356000441780d003541d5210a0400c0f103900e4402c900c140c09041880000d2810300c20103405409807074070080095220740141360001405107803021280190750081d03001c07140ca080d20700030340c45d42d01d1031442095400300c0c1c03e0808120003512a00082c0c0e079500120401c010320b03000d80c0000390341d8600c10360540340d04880c04400c807107215031215030294849408031138042140100300d400c004940844c0b80251800111074440440008881004401800c1940215024541c0130400003420729 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 489252383 1250 489251133 489251137
    0x31e01111c051e04020f0a080d0c0b0702030a0c060b0105090d080307030b190e06030f0a0b090f01061a03040f051009140604030203090118032907021506040b03030f 72
    0x201140a0244000301e111205070116030b0b0192400038001480280c0c0400781c603894021a4000e07804842d6030040c0c81c200c1d8001002c802c0d003504176500340c4c002c00a113412800e070891400ca203098418601034034140c1e81c040040303039240a0060301400041c41018018045580741e40030410302c0c076040c501689840b40100208801220b01241103603999000030811080d50b5140c410b450309460b0072503e420001c400400b8010403880a800782021010300702c00841c03407a580c1009400a03944000c030a83e454500d10741000207600b0000c5039440468058060080b11905045c851001660340d0702002c0c0302010001d00054255400c01070040b91400c1d9280b2480d0086041040500b407440346544010402060514044140d0b01d00d1049050340f9600030030601c000a60003000342c0751000001c0c0b904006180903000c4c0031954206690018108905000c400b0b0004444117414818080c0500440030a81c2c5600100b2681c4806170001e44580c5186c00012910f42d14054101d501d140400a08407800c0c0344c0705030050034480d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 489253633 1250 489252383 489252397
    0xb030417160b1006020c090610030c020a0f050d09120201080a0c260a0c020a0b0406020702060f0406120b0d0209150310051305010606110304060311040b0307020d0e03010b031e0111 79
    0x42c3c1d110104000303165040028480381202035401148900f03041d4007280b1165000301c1800e05040c2c54840039036100b482045095101600301c1d8040003880c903541404ca45400f0b641080c400002c11101010886607a48010a1003403a8180c0d034100880d030701d07201000d00420072643d40c4400c110a81d04501ca0f205100e80704401036000742042031085003001c10107442110000c030244801c0d500501c9462010500a00040754055007144016949000520009200344140b00c507a55440401203404104a540240c14403951001c40b50b08000e504944400c00c2490140c00354001c0d803001b5030b030001804000740e0111082411501070201c86c2c2c0c0c40032500205d02640d608440340312041020b55201d03000d104003406160010849414401c803040c2004105a4907445103000f928207050b01d841d070401b07850345070100319801803401a26440d1281041c610094980402120200004140310885881441c1c107100d002104003004004080038011181c02071240000d009005580795a119201c8115050b840c000b4065 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 489254883 1250 489253633 489253651
    0xc06021308150702190206030c1806040b03060102010605120604060f022116030e0303130c0504020d050a0b09070c150b0a030c080f010501060f180312030e06010b030417160b 76
    0x80b074540f80c038009141075000c1241c5100000d80251200c0980c8500c0c04a90b049100040c21b55564190005440441e4000c0380300130b0b40140002400052101e030350000f0b980166000d900a04c0700a5617107082003c405084411030003240c210402080000e500e984c0703c0e450010b0051009401d114080490030300030781c0e1040010504003000d00421103641907082c10740ea00c581c1c081c07d041140d801c85c1200700d60360f400010000006102d084112030188054821b00c48020070f0002d005542d1100c001c0440c0014282c141c3d2034401007401c0c94003074001442c20415440c8a1400c41d61100303004240c1c4e40381d041c0185000c03a14411441c1c2d540e003040140751600304406c400b95028814002c0500e143c9800390389003206c4c2c0070b0318210320f914080050144591000441140500034074007078124440c209030f000742c005181e074802090b50b01100040c16909405420804480700d240c4180e480d90b0380c0c0c5980003600b1744401c031001480b107642d007036100d030303c8040300c1c00640001c00180740c50780c0c040d4003681c5c0e90304282c41c800e44240034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 489256133 1250 489254883 489254923
    0x108010606020f120a230d0c080702011e0b0103060e070302070b090a1a04032606120604111c050609010f1802130c020c0301110414030d0c06021308 65
    0x12142c041012078407182c0820010042000318402030200c60140000640421030b40346080c4128101c0101d5000c403450646840c43c2e81c070412002407400a014002c0c02c80301040d441ea0010340301c503006110b500604580041383c82c5d04030603400c140310018070303114110605051782c50601065030036040d840140b045405031801a43c1c0c0685080c101a2140d00802412042d8412442840051001d00c01907014001080e410360035920b651609442c295081189054030007008401e40303985641c1071104500409013940c07052009200e0101c0181c071104200c4000d03001c03440100c14028582064034899002102c81d8860310389a984555480e4188007003070b00c0c1d00c40c03180e4498020042002042c4a070048525284c0d43d801c00700c020756400b103001070b10506840e0700705039510849450064024020125000d00041c001c20000450040c0b00c46960403074040d00b0301ca0b0003480305003000c5080000d08130031550880d8507142840005070740e4a00c069408200903031820101e07410300051071001044070360004c0300d034030380805 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 489257383 1250 489256133 489256139
    0x3080d0f15030c0b0304020d1407170f0c24040803120c040303020c0d06021e1201210f0203030403021809010b0901060c0f170a0f0f23090f0901080106 66
    0x31098a607807100311200541050000c00005818034102c408540808040726129507860001131107a1010700d01c007a0422440c994400078028010402006542e900d00102c02640c1000e441030f41e907081d06c2e03850303420141d10000e4015803c0c6000c480c0900710013020031030343d22503224421540310340350003903803142000ba4004100b29074030107070000601b917200794107222007401d0607d1500c0c000e540e98a60220030340640b5a0003044001d026091f0101c2d040000003588602003000100b81032102540f054510026000c99000080f031050303030b6881e10102150790314a0946500388141c4480140701281c480480c0d0500c1f0401c40003005841c7c01500e805a0246284581c03042d00d007066643d400d5554901d200ea2045402a0042c044550040d4040d0416174000ca001c2a0029451614070410380804118410000020440d4a1400e07400f8105d4030b00c0290680c1d4401030342e518078034241c400600c07410083c46150141d22100c280c0b6500c0002801d14030100600310140b5a007010046444a6000c0e00001d41c180d44450040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 489258633 1250 489257383 489257411
    0x210915041d090606041a0103020a090e070509040b030a0b071101020421110f01050d020f0c01050114100e0306010312030f05040507080111030606030402040203061f0e040c020309030a0b0601030603080d 88
    0x10f584c403c4080c2d40c14021070079440c0d20b24840c0103040b031006041c16400b00e503849503184115a0070001c1c002d248480010b03410000707006010b541060010611a604114120234241000300d40500c410760700c00c4141c81c4e00d8440c0c43c0b080d2030b031415482c6118030303030740d800c0c4800645288052100d00c1421000c8013180c04442032410300001c1070800640d41d501500088014407002d0b44d000003102d41c9100c00300001a2100816001c005c2503105070346843c0059804d010012800c0c80c801d6480348200c0b00c0440e01d803d00003040c12006e4406c0b8025060042c4d060704400010008203144918492410b02c4d03d00d00051803d0700c0425200448e2000d80b030985984d800403d05110f8113500740f01e038105408402d03120a04514101c00018040d2000800084c040c070307004808901151100d8512525294181489420910807010b0041c0141d1508905038459801d203801051007a00200403503015420290180c100203c031030711100c9000030003814180c10546c0d15400000400c21610203000c0c80c40e0024400300703000d881040c0d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 489259883 1250 489258633 489258643
    0x5060f060f04140606180909011406031204060c0f0506090c0120030f0c070506030411101d0907111f0b120a030f0c020904080c210915041d09 62
    0x507260146143c01e00f28210003400e180710541c8803038100c0b40d5503074408140c031900d503a8031445c2c00d49540203604141031011008042d0000030320210107003005104e994461040640e540249240100310600410061080d14402c001c2c0c0d0600a000b51100c80b0308501c141d440c1450b0400c202c80b042c003a900403a030101040c4da8060320640d003985a81e40740707280c000e1803e118262244240203c1c1920000001100c442e0341d64140119001420024801e039140d140c40d040800360303500d0240005200300c031800c64809a0701d000340c91320940c1001000340340f20009001003c3c80942100134000c0c0741807180c0c020440c0c4003c0f9040184c51011707004010446052909044140e007650f410400c45441404a0b040d131810344280056a61495900352502e42c40314030740344800396840e84104101a40180c0da00041205000ca2880140781400b6001d04640c030451180c3c107402504000c9003000c0300c0240e4100550405454000d920b007092500120034649400e913286e0681c00310f252100c3c24079a16959610030070050981c1800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 489261133 1250 489259883 489259909
    0x1c02190303050901110106060e06030a0609020406080a06060512040f0f0b0a1d06060616080c0d112109040c020111030906070915020703080a11010f1509110405011b05060f06 76
    0x380010742c01c0c140c8c003401085660b14a24000c130b070080300044051000d0b03000b41d402044440801c42d03845403503071001411041d00301c2e460303858982003150000c5c20324481c10848590700d0f442c040e601d116840d90b682d0740c0b120300c1d150401030f901e414074241100003041e41142203501560000100290a403202410305442480309250907610750451010000035840b00c404480716055400b002c042a0442c80c40c01580e24050038880403103502c03c5021200707050b904014203448915400045604219003040001c00039280c0c003189400c0c070032007401803290a06140d0818032020b00c150001043c6980d07090390304204e40d0000c944c01480b80c2c0c84041400903161b08001c2485c05420791070700f1651601d076049000380d5100003a101c010311040001854040103846100300d0115800f00750001e0058803c0c0155240103801d411400b40004400c403040001d42100a02c181c0305104041d07200c135410a8945001525102c05120343c0040c01007907424082c000440500ac450310403c2c886d0110445810010180b09840301d070780b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 489262383 1250 489261133 489261167
    0xe0601090f02041a07020a030c0308040f080313050f033f0408191e0605040318050a030611070c0b19210506010207090f0b040f0204051c02190303050901 67
    0x41c0500c0c803000f402a401c5007480e00c400c0380d17a08218804980100102c1d48082c5c0149041440402000040e1009000312580c150991030240d07183c07907516403240305840580008051111041142e420f00c0058052558001420b0b900e4541060040f8824581d181c0113883c00b1000034405a48001c2248041070181300512826504150400130016555445c03240c86800180d0800c882e003003040390842104028199180c0703800195092447e00e0f0740682001d075412000314003504040411a0302480c0e045046541c01010000400d1960b294100101411010031550440c10000c40740401c41c5000350750028000c06841550302d1030b443d042d11610514030320700382c010080c2c0d079042c400c100c3e50122440c44143c40d400304001440d440d0080141d04d00015075100d40150342c1029904540244d29500a01c620442902d040c002e040340174850300d00300e1040d40206a07120400301402d40040d94644a900c18662020f00508880e20708d44070700d24807030715440d4030880c002100020085800d5a10044404841c01c81d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 489263633 1250 489262383 489262387
    0x21e010912080118050c0d0908030601111b04020711030a050a060506010203031320031c093303020f0d0c120b031c12060e010f0806040b060603190e0601090f02 70
    0x150406a07032444c070144440c030b403610307800403400382c00c80b2200715642405041c008101c6d07007055240c204040e4108a03245800700b0030385d42c0d80110300840407640c0b9030402c081c4d0446008140d00300080200a400c1f00e00250340c000d0808001800ca52410845000210f001b03400a0003081644d03e040c40c141c0d107004012fa411500140180603000240c1003104045943c0940d01401c52003442c41d001209141004c2c1050741841015200c200032201d200d06418a090305680e065003507030f29080e600d141d407179803043d4107071b0100b40841030b5001451140900900384d11245c98050b2402c410414201c100d60080c4c484c01e68402e98403550130342c40c1c0307800008004078440000014040e0900e000c00081e100e14001c103c0c1d020600b2820981070301c0610071540075002d552803660400900e911805031042d10f0f002406100e690080c0d440001c2400764000039101d1182d58171110250ba140d81e0300c0284040d036000640440c0c140740c0c1400e1440e00c490300c0350080541080313000c001064150714100503030081d40c12280c00c00c0704c4070b441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 489264883 1250 489263633 489263639
    0x1503140402040c17150a090b060f031b0705010c09080d0c080f0405060c07050a1a0910050702060a1e050c03180a030b01080109060b040606020d0e01021e0109120801 72
    0x5211594819011980000d082408001c00d44954028958160b00705039154100800c0c1080c40750444007203241516602c1c0040c4e250720000c0d040768007030842c5a0748081d09006180c549525403004641c4a10b2a0f000900d2441040e035590300c00350400c000440c0d45075110180b500714143d2101c0c4010050900c5c500500f8000039000018140c40c103480c50103410a500043e002c1c00b6810300404a41c020900901815035608201030160f0301c032123103801020f100350321450380001c9428030301c00004400186030000c00e00d4100b01d0b00801c03406520900d00c25041c040180040c2025a031848040d00e031070b220940710074036401001d407404011034a101c140402449418002142000c6001066a8000d030102e1f0141030b01480c940d0008070120301941c002804138100c000007060485040d001486400d105060600821a00100300700988055000d0302c00149e0204000120003440740c01c43c08085c41060043c0c038603d00d5181c4581c4032040191842803002c0e07440b243d00800304591510494034866441c5441d0001e541 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 489266133 1250 489264883 489264911
    0x203011b0f080a0e0a050a02090c03041e0201091205060a1b0c080f07050d0207060f140a0503041104020a090807050619050307050c01151809020906060d06120305041503 74
    0x204007128441084408000116200e86640c44004030f609804122801200c40f0b243c1103640300001d0504074025914413010410503d911025240100d5109411208003110450748c6e03e01c1c0701c1014400d03410802c4020b40010280031a82c5024021030040025100b00e01d403908101050b12544000c42e495000804021044d0544c044000c5109a510890242d40d80c1080c1c1e0b110351040c00b80040c0506540070710082c040e019a00000c0300c40403199583c8410225603941003090340d44c0b04030301c5804425010200045a0f245110360006e581c00351140f0090f02c21003490f00c0100d0100d82000702280081900e242c400d01440344104280002001c08580c0c4614000b0b581111050001d50030062906118011006c00c000c5030046054400755018440200510035850107c00f030101c07224071507610354404040d0915103c0ea5580034a412043e005800780d03606403100c1d8184401c40d44407107906c41310150744079000706400718a905403000c054001d0703850340d0310350741000c00c075000100c495851501490b1030f1105a5031150f0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 489267383 1250 489266133 489266147
    0x100c0213021b030c010c090b0307020316020418080d0e03030c040302010827010b0109061701032006042c161202070b0f150a080304170c060c01090203011b 68
    0x81a00005070725034a60500c0c0060a040a0400d003582e030002107500d0081d100150f1003808805220b51341d01c0ba04c00ea4458110030a8841a1140801a0803c0141050000e030f05452204d01d10701c05080000c02100f901d8618048000c1014101d5881800081d082e500c003d460003403115060710344024510314281034521520381c0c8501d100c000c1c14072071918001190072040e100b14040848d00c0e52441821031410707403072450017040c20b000580e01040b08410042501c1d849039034000d810701c41c1c0781710121090b4290f4071400022102d42c0000c0c140c1e602c102c02000748544520000d400207003599604070711801c88203104288503e00c3d40c020030f02d000303450302c040011424a500c10120018014240707400303410300c0d0a0140c00688510240034241e04104010310105010100000e4410288100d4542180329240c08020390042c052003149031650090109001c00700740034000010001050003120024200710010a441e50040c600320340350341e507403030b0044004d5007800c0c05544941e4404080303d9006c00901030028201d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 489268633 1250 489267383 489267409
    0x209010602340302090705070512030c0304110f0a06030e010f2009040912080f07020f030f18040612140102120f190e0a02030f2d0102090d060506100c02 67
    0x40b0040380e40c2080d90084a4102d805141c002c0c0080700d9616220102403c2c1340d01400f01100d441c424044030b4405545284252800703074440002c114603580312501c03000c0d0128100321100303501200b8950b121405503034040c4040c008010343e45000c642000301c40d0a41c0c0c210340035458504141c1c1c3c140003588008010005007034206c3c00200815545925100020500511421900500301c0382400000f4060320340183d00705102c0d100c02d034005c040c40d50b29030300100d8032101002280841c42c4d000744107414004001c0c0024010021110b06031101580e003100c0003409903202a0b225921a24400054005102509a00c4541406030360025071411000c0a104240e504d00249400f84420000c40841c500c030700807a400282128008200b0701109840491181c0c490b01703802c01c200c5c0302e88582000502c04140110783c1e401c040e0700002021030b00d061440300000c10780000440c1c241182d503081000c1481d40ea51a440c40c4000d5003d4032000483c0e01d05071041c84110400c3c0c0030030406022805a01c040180c2c2c943c042c1641c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 489269883 1250 489268633 489268693
    0xc040501050708090a180b19120809030a08091905010801120f12020105220c050108060a031202070312080f0c130506040e0a0b190b130905070c0209010602 68
    0x10341c2c2481c1c00c2c0182c66016030161540d00180f000301c00625010385000403601a60028400c100c03110f800d0082041054000c1e044011046610900f0030040f00b076824481611801503e02e149050710300000a4149903500788201d03424000030840e101142480c4a0000ca10420020311103c504c0c141000030300002d805200398440b25a40211000030818405007285c070070b80e440700200040404144001e03020f0300040f03440f50070001c0150082200e0f510595031190f082900315a007103035054103100044030b03407100c02810b90307420203104800000014500016a10081902d40c003500d1a68110326103840c40b01d4090800b00208207485050000441c000445160480710804080da59500c070f00c071841b1451182ca512403a4401070200b8000b03429602c030902c881c420518101c00700155860041008544040401e4100c142c0716651014041e2000d840e0041040d00c607480b44d25607140e6510fa4181040d19411103030b14000035035a041340740450922008081c003400701400904901e48040e100f219076880c0001d06540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 489271133 1250 489269883 489269887
    0x20010207031a0a09020d05070e100f0302040f0b060a0306030302060a020715090201140c0618010e030a031e0c0c1202030f0703051305101d0f0f040c17160210050c04050105 75
    0x8018451a88040004c0344c4c060071035034a40d8030905005450303101d10300c5003480e000001400520b078040d44401100a40d144144980206400c40d02400001c141041c520340381c10b5a01c0300240d0184c0e4900c805011035000e96030b0f0116406045260007410254040c1c02c91200ca030040c401600028210f100c4031841483c08000019220303400d000407a108010015031901703c00001680340c0c0745e598040f03140c521490501b90315020001d000032a15080798259074107040f0640050280c810b003984039800154006200206c034619038040c603410032044408049202000c641102d56510070091681060034421203240095414441044407100a61142d41c400808100340000c000b2803c14a041105001d071001078410002080390420140c86200780c0461100c40c0303220814441d42030319140392040501c403005444005040710800500c0007804501914800b401003c40030388119031658035000d8841c25648080251140c02c040e0080d00b0300002440ca00120340c100303400c100801400b18200ea04450f02840d1a40e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 489272383 1250 489271133 489271141
    0x20f15040f05041b27060e0f030a08070f080c070603060302031c0f05070606030c0e01180608120705010e060c0d06050312070b071b0c050a090b010905042720010207031a 74
    0x1520b280c031240c400c4c40c010320f0f903800e001c01c1407a030011f81526018400d0b00c1424416000c001090f580c0c00b80510014001c5e5004c002d440001040940c28139582ca129015003030030300b000a1181401c000981c2c0180b00006d544140810643c941006004002c5045060106115043c0d2800410b55a841c4c00800240040024400100a01e07940b01400840d000b000450169840d80403645160300203110720450314507400c206a4000c1014441c0c6030803144020020071804540d064501c9564000000548295503104074881c90a1003e00005108240c8107485659a50b002c0d9070036002c9641541041d0b000740c0c00103c01c0b2840100c3d0008403444e15401828405c1d5503070b04c00008990084d842c0c100c200703903107081014000c10805402d460b1019200101c40303004d402601c40403c070341103402008100d400203a07000801c00050815520a00d4401c10102d10310f411035402001e00c3c04490518601161204110025201d110f9019010141004400d01c0940740d1a813540d01c0707102031080390001200c44021800c004c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 489273633 1250 489272383 489272417
    0x5061303020907050c1603021503010b12060a0b160201081302090c0705190b07090b0a0c150b04021c1401030b0708060f090f090606040509031204020f15040f05041b 72
    0x9079046101c3d010071941b541c0c00b8010410700841b45444100d02415920003146020101001600d0580c0d9501d180141007410758a0000c4111002400e071a805c42070840300170607245104230041c400b142e07800703054810a1180e8400106104030040051594806118039800180c0c0d0b0902c070650081d80400000c3d44481140c02e1071030402d803042c24601460407107885040100610403807954401e4800b44c0b01e480c1c80ba982c6400b600d25500c0384030803080005401038040c0d400100c0fa03241e9011541101240003401c24807070008103089900c1065000c402541c2124220840f5245005600f600e9100c40b410211951550fa0b43c5184224040c14100c144881400001c8903074586854005100d00018500801303070a01c41030b440b0707003040155201d003058003c5200290080c18117000340350096040b00c00851411841030440310542001a0003280d000c03148003454621642d504d00c0a5958803141d8182c259690f2405040e03500c2c107411503008900850601704d0b10110740d150348030082c000b84442d04017680c5100001c400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 489274883 1250 489273633 489273637
    0x130f02040e0f07030b033403050102040b090a12170d020708041805090a0309051905030322060206010b180402070210110d08090307030f02160914010506130302090705 73
    0x2000d5100d03100102001020740c2082007690080c94551004c2041341c007624141600c07400303000200b00450511002000c019400718009107402a003080b038247d5003d40365034489084e68407592040005050100d840103043c41c0492203034005040305150b00800720383c1942d0f24000100c10040780d4410700400300d0401e4091310301d81c0403104000d5000074a90b42d02e5803601e0700111428010904a14480c3c03414002624410000428aa5181e01a2500c40f040b925102c00c104000340507000170300700c00e00c1000001070307640c078100050808111040045814000c02c81c06803ca0700030300d90300000440d070009004010400c5000c0440e0345040061041e0380c442c076802008900a44168440290880313180b400444c4040e0b44120076281c600f20030070503190032109401d01116024015252400700313030810000c03440024003c4850005842c0741c2e0040e107a03400802d4029080e200e0041e48049545c545440d20700781c40c0401da02000c4c0c05481c0442d00b103401c0401802110b001d440b0a800024000c2000c0c1c2c010840450250301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 489276133 1250 489274883 489274889
    0x40b06010215041104022503020d030e2e0204030501050f07110715050a051c050f01060e0f040c020a05030304030503011a0313031211040b0706050f062b171305040b130f0204 76
    0x208800b9090b1f041c41c00035070703e0034066110000a45058000801c509004c20701140c11400c2800d8400702020b20b682c3d0804020a006c05103c0d1306500f00700c0040000c83c00e02036980b0410601038119528600650060b001881941d00d0740a075411408050206048000b00d4110f00707844c40c49d0079520751385032850942e941c6c4a550300e01c0311414200344102da100311494000901c0b4404140304d4603040e981e100020b1380d0401c01d08010650114007000600c5080c00c290344242d0714907040e84120780241100d901d8090542d8019201074001440010050101140c0040c01d401a140500030092440c600b1a8a400c099512100003c0c00c11101c1c00103010484400d4203c410ba1404880886035100e6448001030100c1c3d1101744121803803800c0900144e00d910420905502c21080985003c3ca01c1000301050401c80e020403c0824080f00c0219415012440c039410008a030034400d00030503a0780d50322076404d014820349640a00d2145007440000c40300b9488220b50b8054079024201c02080740c001c0c840c0d0300d402038042c3d60 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 489277383 1250 489276133 489276187
    0x1e0e07060815220b031e03180402070606030f03110a02130c0e121501050f0f0603070507052d120f09030703061406190b19020c0405040b0601021504110402 68
    0x7800f182c00c3d241042d071155240c048101c2c103d990714103031800308040003002c402d00f1484641003481000804030b0803401c8408801c20041c80140760007a10380c1e50340b04480706074000b501d10700c2c40d2151900c2050b40140300c2c1718803c680e00005155030b100c4d07640010b00901c00d4400c50700b42e00351940740034840c4134020301200407000e1000340852501404402c0c0c55549a8001c0141d0000d0351000c000003034141042d0007101c0c0040800741c001020b140c00842400360591010f0948e50404c0b400704001c2000c240309020240303503151400d5810348014481807410f003031442c003000903410781e8000f18244c15040c02054221920740140e0715013251504081c000084c2403d80710b03480500000d0800408a8000c80c41c800c00c544a0002280c03003841d101000640201540c1d250b004014201d0b40420100c40105080b00c00d0a034005c6261040721003075146000480d040d00c4040d80e00b01c0c1c90350400004d02015680500c45e017402050040c010100620703040d26603184988422404a008942c0025400f15170304100390b265440840310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 489278633 1250 489277383 489277429
    0x112170c06070e01030f0b030c060705151f05092502071a0301030c0602071401180b0c100b040c05030a180807120206100b070201080604020d1e0e07060815 68
    0x350054010205800f415000a00d00003600d01c954640380300d000d808a4002d40144507180403841442050390010701c5c2500c0318070030380ca888071049001c620030354850b903d21a031001c2c003181e251402a01400075500003034032400c246010403240310020380d80380c160404142c0c00e030131000c207200341c007a401c2410a070840604885405607042d072900043d4000c50403244551a001865940c1e940c0490710f6201701d00403200301c2011481d00420329032140390980303036441c40c1034142c4048640d1560503c3c0290f120707074000003c80c1c0020001d6030000103148500660b101040d14107000355034148a000f00144002007411822a0b81e80d0b034550081c010b140d030350b07440041c2d121044c1540d43c42d503810290407a101039100040184030b03040005549401013488131701203800100300c036810004598010364000c10028040c9400960034007400e410254a4020407202c07021000c1010818040491100b09440c181994030000e5882503008010003640b001106a0251041c8003410080b21188001000301c01080c140100c48502c2e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 489279883 1250 489278633 489278641
    0x905010218010c0c2304060314060907050604090e011103040503070507060f0f200d0306030b01122f0a0e0f0f10120c08060a230112170c06 61
    0x154000c10004101403020012107410800444401c0d0100800800c0c443c14004200030301c11a41140959041c0321200840c02c0e4040500458100c0f0003030351080c0d41e04a28404c660249240038040b058101400304042c05030726050001040903480b440c810030018540c1d8404030400305101794482440c00d1054401950340b802d0034107207545c3c1ca40198909680394001e00c40008ac6140c0108603600318108561121035400303203a4031099a00821440e800d0500e8100e035200070110b0542401101d00840154500241081c1941001460900141c02c9000d0f0000d101c148440411003c00070700c5104030000c1007000031030760100d030718040500701c80700c0c481e80150700e0721001701d604031810708114070401c40507425080641d00c08015840080c0242d41100c5000701c0b00b541480925103401500d8281c6010b24125201103589a04241c42c01a0444100604998840d003c44003c1a1a00c10350700c00703900045000120b50400400810408590400070840901440c100344a090f8060a81c1d402c001c0c41030a682c001d00e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 489281133 1250 489279883 489279893
    0x80c12030408061005100e010c121116080c270702070b0f041d13030e2701140303070302060a0c030b0904050705040b1e0609040908040b0405040f050c12061309 70
    0x89406021b01c00c40041074818481840348400b0600c0d150165a032803a4004940c50b900c04035103440001b0803c02030805c4140b01590030030030419101c0b403a072504000341545000c80300340c208800140040c1c0703e2150a40b40c825000c81c01c114500450301e0007450b2900580314040306034078113161075000003c01080801c01094044504010704101c1e06005032284c3c006070060039200c40b50314211001101e0106002541001c82d1050020a04041000d002001c800b020f000040911240128159204000a1005020580c01c0b0402c0854024003500111704040c0381d69000ba4031100000c143c0003c00b0341c1c1c2d050200800d446078011002e0454043c02042081c205400e06607140c0f07145002c0d00e8011820608048901e003400c6c2000412501002d0040005500d001c04000c100d034881440325501c21b444071586408114000c004000a10481002c80d030391314940030a0005907801110541e404624200400c600c02d00c3c0c0c10200d0303110f2150300d0304034211569021300044c039668105202004e82d9280140c0101044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 489282383 1250 489281133 489281161
    0x221110020705090a1a0103141303050c0f03030a0b01050306010504090213170a03030c0801050f060c0c090f0411030601060915021c0309031409030309010c0c0e070509090709080c1203040806 83
    0x1070328980c0f0094031740368001c00540545410312802003019050800003003000b00d40264140e9102e00c2443c0480c41d03c001400c00078035000c0803c20401d40da0304000180200f0700f0785440341a001c0d00b000c0c00c0032801c500c5e2031000a8458082c0340315105903141c000511814004400740d00801604441e220701d0400b083c0b111201e55604407000341100824508140104094007502c68641251402040c18850b10420030a002c15500802c0381d10600d445014980036180d5118001c491180d801c420076042285454204201050843c00842e8002c0e0046001401415480340521041e940b1503031600d900030390440341c1245400d0031126000e0340c00c440c54403c0b56960764150000b070764190203980d5408ee0010302a425160511800d0162a8141e000300700151855000f2070510724054014100350784010350310030b0b5842c8003440445130003001441c0000c1012851070701d0103ea9400905c1072500003000303410310300034a5540ca941070b2080d10bd56201407800c09141c00400407100601514000c0c1d400904250351910004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 489283633 1250 489282383 489282401
    0x1090f08071103011b050a120e060f07050703051602220b0f06040506030103030f120501300201020a08030c040315200708030708060a03021008221110020705090a 71
    0x2c500c0c507442c81910b2505014030380c0c110f210345480d1155401035010a0382d0a92240c068001030041e4034600c48403480b1184240700e424090080030744042c2c074000410f084100da005000d5801d0280a028001c007182d4003200780e40801214058400080400b0b000248141c60301d0342c2142c01601d55402030400041554001d44540401500e0400c0f51142840c10080e081c0603d0142540218092004101280c40ba030560744000249040596108083d0000d8a0680d1000d0304806243c034402d1603110403000b071051103c0340b040710449100c0d40b00740107a80003d4503150582d002900011011012172110700f0000103c40045038040c1d11082015440340612014010700c1c01c0c4070080c525040c003101511991001160800342d031100c4120300e5640c480c041031b031304c1803806081d040e0400324803040400142c66622035480c141d80591150081803902c0c0380c0c05100040442040c1d013181103000c1d1950300260610010004049086400403130b4610304c1d00041780350800941c002c99004d402041403140600099105081d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 489284883 1250 489283633 489283643
    0xf0d08071a010611060a0b010309080a17010b0412110f0a03050a02030601090203040503041a120a0504150c020d080a14011e08191e020301061e080a170c01090f0807 72
    0x745a80e5800c2c150380b00001000c2c0d2803103940150b000070f8545015a07011011244050400140110480e00d4400094214031041004130f030602c400d4503800580c48604034010044004180d140034188021100b1641c240d110080c510019011f40d121aa50780c510000c1910801403c0c4d0414903a40c1d0074004d540b9070602000340d001c0d016041c00450300b0380150085a1041d07030400e00540c501860040e081d41d01c0c0008807031203d87e040c8240003040380e411491101d280078140402e008500da04213414285034100c08000011340c450b02e031100c42c02810390086100c5080d19041e003020b00050392880450b00140100e008200c0c010300e1203100110b18810aa0b11508030840d1409000100a40301e0701c4455030f076119001403003600038141c20a140082c040c07000729803500c1665000e01c2011a5594042802d544060b04141d009031110004000740c102401842001800036000038852442140ca0b03505a155040c508040c09450002d40e000030328109400202080b035028040222403400780c20038805030b40200307408542c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 489286133 1250 489284883 489284933
    0x102090405090606032505034201120201031409030406021603260c060108030415080c1803210703120b010905101116091103070c020f0d0807 62
    0x14a80400203403d0b10600000e0004c00321417102d0000c0b50802030f00081c0240b065034003030701301040d603407000d2114003000c01408650080304070300789603201c2c4c0902c0340800740d00c201c0c104541c025031280d40300d0201a0460b0745207005042581c0d041d000407006050707000c0c1c1c20000445a20244120300300000010700840329a5404d80b41540c920341d041910050f0184030103025160307242c240400807940343c0f030f08070640c5000c000307840d2801c549440e0150503c2026071044039142c01c0840e0812500003481d52270003a4241074078101c0d01ca480c0442c841080b5000e4142d401c00c151025004488003030710204070050b410741c0e20800282210302007a5945205612164080700001d42500c59001460400d02504205810507101c4000040c1460184002241c0e01c000d50010000d807454000f503c1b15080c420f0202e28138102c000c0b003c002d41001440c0080e10140c000740c40c00580100100010541e00c6855542c071941c0c100c903404064001500001c403071840c40403001c0c100f92400182d2800300403032211710006c10b400460b0300003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 489287383 1250 489286133 489286141
    0x114210601290a1419170108011e0c0c0f060605041103090a0f0602091207030203160f0b09030a12030e0705030105010506070602130b0c0a05390a0905090102090405 72
    0x5118940920400321800c00c0a00601500c41e01480742c0c00e8015159800c4c9034201881e541003510300c0041444e45002040308200012207150a4900b924054100c12000307000c0880758020800700e0704403a036105034029980d202c1982d6040d03c518000c19600b40c100f1003c4001c6c10150400788010b0085105a510903886c7c1040d04003c500020203a038411202500901603001858075840d801c01c070320351000c48032603500300309220042c5c1d00c481000e900300c07143c0d00040c48041d05510605244c00040320201150701c400c1501008030089045c2814107440d500705801d5100d240e80d0002c01c0c5050b03010000240700740828000e615000c0c0e07042e8030403650100c0729000ca690301c5a0300c406142c01c0315028081c15030010010002100414443e0b00100065042c246504480964a82c003240881e049580700700159001511200103110007044134030410540801803104100003801450900f007610703ea00074000035802c00310020755407118038980c010406101c0034002c43c6090100c00b8001e500801503280310398a00381c041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 489288633 1250 489287383 489287429
    0x120c0201090c0603150b0d0207051218061b070909030e09061302090a03020a0303020a0b070e0105040504091e06020c0d020a020f06070507150e0405010b0306090114210601 75
    0x1506040c0c002000b07120103400d240080300039000349404000c110000e171000040c804885002005420004c2c5001600c1791143d1034408d080401d44220303503940c1441400840d240c42906250f0310200fa80840e452581c40303c402c0c10701c0000f00703000302c102c14035401016000945484690007418040e803103030f079440022800e0710782004000343c0f00740c401ea5040040a00c0c04034443c1c200742e00426561000900000d00686c1e41d60010709a58090340040b00142c0107104224100301d0324107400307900103c0a040c01a507280c40600028402d0145116032403149454207081c00a100302200385400305015115007000301015410000040e50001c0c00c05a40ca2144034070301d49401c1d1010806c004000ea000b003c40c92010784030010042c141d04101002d0320b1702c2c0926540000d00502c4020100d00f00000d944a848040100404010403142d0507846072407285801c00030041140e83c0d1064850640d400c0d9840c00d2842040c102c0480c07008898540c4d0701049041e0403034100c04074680020301e18101c0ea05000405c030740301134000300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 489289883 1250 489288633 489288641
    0x13081201140121050c0d09062a1e0e0301092102030a050319140f061003060308030f1f030305070b090a20030102070f060b040c0f021b03070b0406120c0201 68
    0x5075841c40d203c4020341030802c003a0b41c0009400c01c1e09240700f14140005130710f07000c0840315025802c44460ba44c5180b03400264000130341028011510000c1d0100003c0b4a42c0050540e41c81c15045445d912160034045030818000c1c165049111405002000b50751a689030100d5503842002c190322022460410f0080520b20000844002c181031f039403085d007544c0300c90403800350041d4843c9814400300d03140c0081e400800480b2011a10a00880642001500701340c4240a1540516400030301003609105007030010075658001c0325000100f0030310400c2c8640d81d421800008031005602c54031894a260700010a259215010b000e2040c098441d40c94161a0000081d41c2d42c60800802410420442c501c6d414656106140c5000280043e0015203804a203130394200e0300002c2014201c84036a41c45034010203a0a281c4241c030300242d100d0801c440d038401130b0b001c041d507101041038125803d1011268895940d880a0090800803c000d504c1903807266241d200141044002c641304021562402000906003841401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 489291133 1250 489289883 489289907
    0x610080703030e1203130311060703050304020d11060c0309030f062214060c04031407230301060302040507020f12040e0f07031e0203060f040603050d08130812011401 73
    0x1031101a241d40da0650b00c004031000c10b00da001428504064003a4001d10090030f40b10010b22001c04014190b2402d0340240d82405003c901815051100c240005e41103000c44e90800c2e0100c0da41210040e40740b0300014982500300c4515002500426030350b1049400101421011004600707441c4e0001443c07001607621182183c030350400007008424000c02c0302c01d202100026601400c115401034030718920f440c3c076104003a158014000ca0000d0304006001e42803c1d9030003441c141001400816140060846140c0201c5140f05070b804909005000c0a54003540308000555010b44140500e107808131002e51a8502c3c115041080c2c040d1314100d82903000301c501114240e41c95012118500e8031658442018610010071000034550360b00410203216040c100c080380360782c40000c2c0259407850010f0a100380d20201120490140b0b040c10300620020700089800207001d041460215401c1d51008079100b180358414002500620300010b4100c2407420307810070746040e14009540d82a100d14401c0044442c0302d280e507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 489292383 1250 489291133 489291149
    0x5040f0219030c050c06010e041a07020c01030b0d0b1e010b0403080a080406090b181002091302030a02091f030c0507080d0c1e080603160605070b060a0e0103030c050610 74
    0x1c0e29080010700a0303001e80c0c003541403441e002e403e220b00c0e58000c0d8649002a0030529060b80312000300010802c84200b580c00f0502040c80507030540c10400400380d07440b1100100360341030588450b00b111090300e0344204611640d40281586900c1c0c10101600d40ba40e0951000052044182304000306010301014100c508490744410070a10b130007030042c0115600780018000701c0ea81510754286102255080b01c20500902c0c400c51040711135560071001710b1601240c2c40380111024018420441310395190402c1030b00107000a00c015070307a5030702c4180500080c4079901196a010059600c0a0810100d0011481d51501141c804206180100c5c1b010b603524000d01100400001e41040150403001080d00700c04506c020ba03080ca0200d0303c16503040500344802030207540e00000c5d502010000326140c02c000d60b038071011015050003400c3e401c1c00b90043c01031069010241000c40b60300c020034a16201d804045004154503042c014455840e4035000700103003030210094030584220b00c0840e403101c1e080c01c1d00108984400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 489293633 1250 489292383 489292417
    0x206040e100306020c032101050609010c0611030907080d080c0f07230f1603020d0b19060608071706090703090f06150303110327030316060605040f02 66
    0x80004405904030080103030203400700440300000012210300117826800b2042000d151070b410024408044038020480b40c11011052400401698035482c086a20b41c0c907081c030f01000081d06a040080140004003269444210004204500e2110215010045d6420401941e800d03c1e11103008449149040d1030b4248114420024400031640c00ea00401d0010310587d0245100c0c0000040c083c000340d0130b4440e401054100101d5202c200b001404019503804051b035031910301d10300b59004a9290401080b00514400f2114042003040454514081c45541281300a010142d20340d000144608400d58080c3c0c0801e114002010f805980744118910540c80034105010355034030024220041e0a51080641e0050a010341d40c0780460700c98080c0c006040c0240080141d16459464000e0000c0c910001f03001d5150000e101044490b20707221900030150381402c09042e0640311000000e0300718460b1a5442040d070300744000400410a46811103011a0002c5608004070f4482c4803007e0180d203e201e0020044901d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 489294883 1250 489293633 489293639
    0x5040612151508011a0d0c02150a1b020304120b04020102210a0e030d0c1104091a040209010b0c0604020f0111010c080117070602030f0d060506040305060105130b090631021b0a020604 80
    0x1591f8040b802c0d165003441150b290f5649510380030a0104142e800070b040c0340d11043c2041e01454011018179100c440c5100a52030f0514103a40a4078216440600900407145003000c0b8003560701c01c0102c02c180e440e100c2c0407101c500305903001c2039801d43e020010280110390100a6a0b00d540f801260984c1e50b80f49a489010fa42a000c1e0395100d40c1d0102d000c4042e51107030380d6070000c2e008030b00648600003003154039200c04481418a4010020365120503404203a003034104120b0080d0312080483d84030380242e41a207983e03880d00d42d500016151884158154485580b070a1001000d03103038041c510904850550b6400c040e500c0d8180007680e1141d0300d0f4051000582c0c400c01c00707903480c0c9a401d070041c604030510b000000380c01503d9800050150340b060f07000344c0c5d40d07030310250040c05075107406803881c0c0c1c21801801c1c041021a0441000c0b030030301c0c3d00c014040c0d4030503003035001584403900c8815070403606940d6101e80400d054448844c3c01000390003c1148070b950102c000302200d0311040010313540c055984c0040059040c68a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 489296133 1250 489294883 489294907
    0x307030504060f0609021b070605040314070504020c0303160e01051b030903150901060e0f0c090f061605120f0f07050304030203070f090e0d05040612151508011a 71
    0x81c1c002c4625035600c2000014400c000c3c4140c5000d811a00c40c096607600f0340c03c26003030004c5100c04582d503458020080030810740360000701b03d80c01c070faa11181c19411820911400c5061450580c081c80c1c00130300003c1c7e100060741c1c0110080d846540c5169810202e101c5180c011240c030341e02c8603400d5011480800400e18920700004103840c40c2c02002088070f240a00c4000031900300300c0c0ca0034a2000c0f019401040c08190b640078080da1011b04079030103041426251600c141d000055000d861074040300320004d0701028684644180040484016003040e03501d1400414501c00d01c14900b005452600424070a0361200300200308492240d800c00001e94241484483c88000b42e920420084440f440700700310002c01030300d041c0a01d0006115592524034110b2401642800340c4480c5504215244c000804000031603400030b041e2001d0301c460b86012052544011804d03002000400e245100380b80c5c0c40f12000412503800384407030303050000903074800a00340d82c0c9040c042c1d8a41a032001d81501c1c13400071300205070302c0d031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 489297383 1250 489296133 489296141
    0x50d020c030d1107170a0b010e10030210030f2904090b0604150315060e091908030a09060f0f0c0c050601030807020a0e15150a0e060708190509030120030703 69
    0x45180404d0321501e80da540088106200744c011840076035040700843c0000d02c02d01c005400c1c01010440665002e0740b400c02e50544e01c00702c0d5804007e101701c00300300c00f008001d4072a0303120281d060b030781201c1000018411605030f194198003034200d141040b05c00c81c645400b401d0034001d4102c0198041c11a80d02601d400b030400019001407113010001c0004c00780c000000c10301d64607021545510300000021040d00f031000320400300200a240c140e01d507124030401184004002201d814054100c1101500c9450700d01c01c05001e01483d0320040d20850a00205503501003035640034810a181c0040104500234403048159000e8044960190907900b00d81c0041021420000c020444948000c1c51042840d40311921400a01402c0c1c5054454561121101c0324501303003291511030710203885440905000e02c1d00c0c80144001d02003403109000d401d0100c0c0010400800d0000c1d1054824180416000d0080000004003950401c0030020303c603600342454802000c081ca060400c40001e4183c02da0320303680da8040103070064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 489298633 1250 489297383 489297407
    0x11401030818101106060f030d081f0e0a0b09040c1401050d020403110a05032d033c0403080a0305090f010e0709050c0f0403031404150804050d020c030d 67
    0x20b84400c2c0e0101400360303034108490040500030b8039000c003015450300c0c2c00c2d840c0010061006006091014501d00c45a50015100000c101549046421992060741081c0200070140317402d10342c0400d920001c1000c102d00c1d010342e44030b0f02c03001e482000110800020014040c9085c1d402030404141d000c3c0c103001c09250a00164030717050381810720b0740c58010403841d440100d0b405580103454007006100d10b65036618014806000a1100300c0040204101034100c2e035015031041880c406021103520020444010280184c81444010b002120100b9074841c00d00084404550110116086180f401c48014280351003070390306807074020045c1410b008e81c58a00360001c00001d0074200c8148a00e0f45603181d4007909005140d203000740311019080d42d03032400b001e020a03954003401303040ca000010b200b220341803140c002c05c0c2c50440f60940f030701c0301c0740309449034101c0e166125680010010300d04c4406e2a0745095040031266000302e224104492861021400c100d03125182c0740c4196601d50841400c0000c8244603507641034007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 489299883 1250 489298633 489298657
    0xf2003090102070f110907031103180a020a03060507090911031b1306021c03020702030606011b080d090201120b090601030e0c030a0f030e011b0303020a0908031314030114010308 78
    0x9014000c0e100c2030004c1d10030f480d045a030000c15000d45482d03818410030781500b00c0b1081c00c05115001c608582c0c140035000060038031901903a1020307159110b9204003d880c644a8024262102223a201e04040d0094101140d258002c92613031200000c1e000301130b1151014600130000d2a40c11902c8500e0101c030b04580e0701d41e070040480c03010310031050032032141d03d07060008101035002042103010685a1400685401005a00303041c818401c040150314042020f0764480800d01e0280c1d034800e01c42d4a40e5802c401c0b408400380005c0000f003155600b00801d580b2031032605000341c81d40c21385406403a80b0141500c4d6022a40d980084115010507a654080c1d0802e84100c0615001e445441140a011034600803000700107540466aa582e03131424181c100c14081e210b1007003843c2500a550b0340c1645c554103070320a104020209a80080c0c041b00030342c40b07003040c0400303003000506582e40c2d00041262500c01030028022100441042c0240c0300b12468140301300312812103e20043c2100e45c0c603549411400303821503005418 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 489301133 1250 489299883 489299887
    0x51804150b0604091d0606010c020f0f03011b03050609060405010311010305040c05040f140c070305072a03030522050a03031d0a0e0f061c0f11090106050d0f2003090102 74
    0x3a403944d0500815002902e4030100482c0201c511141030b14082c0042c01c0ba6041c0501410301c00096114030341d410030301600a950411a1050303060200b801404207129010b01e60100d24444814664103401460007000704540001281d1034007002c00088410038800241800c5510070791801550198000a5029014558860f44d07150781c2e0f801304080e950b0300d9041c0440255262102d0441c40c1d50f59a07000e4001e007503076100600b402810b680280ca18030a5840107000c1d210704d0340c000b8660110b550407560210b9941000801c02d80d0340c074a00a441a04003094003441c40081403948200780306000002c1040b203030009c04080d0b1041c0b854400344c07806850800d20441c140c01a0088a00300e8444126400081c100d10402c13000c58903000c4c1c90700c0300c040340103807900e80f092201034000000c1d0072040c8a101c1030703150009004c1600d401e2070314020001c60000c010050300003400740000142660407201401c201d40f8810000d0140c040901308030011140c0364000040070003d440121b80800b55000080d6034010110302c0014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 489302383 1250 489301133 489301139
    0x409230a05330603011503050108010c05040b160210030615020f0c2103030f010521071710050103050d17040b070503040816062021071710051804150b0604 68
    0x19109a000746c101ea039202901c0c40e5800c501e03540c140300301801400d03001e000300b141031a0940000c165104502c101e07000028041100603101d5440300c40750032003070f5008109079859603002784040c01402c014801e100c401c2c04000383d446003460002ca81c2d81e03024903450000e0f10203440c07202d0421450108007030514010001c400c2c2c80d44000041040214000c101000c01141c0702e40c509020401010701250108900340c002e00d500c2e00c2c000708009020410f60300440c01c0760b50f031000702d20700b075510b00300c0c12140390911182044000414440302291028131620940c1d201d507444419074841c012004400d0b00c000384101562030008080510401c00756400501c10f5981c2d524004000700810341030ba20310141a6419940c611610b4032901002c80074080c885070100e40d00d42440c2c450b4005141c80f0103954494812044481d00250760380d44102c000155843e020b620102c46420189407030304441d501070040c0d0340184030b10240008900400d40744284a0759000c2c0862100194004080000d840301c06010b50308820180008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 489303633 1250 489302383 489302389
    0x5100e0406121101050414100e0301050f060a0b04080613020303041e0e0f0c03060d2a030606050102010204080a0609051207051c0305010f0512030409230a0533 70
    0x4219189510402c000142015100d40314420541414850108010080302d411220104120801203441840d4800b441d0b000340c1c0e00c00d01074a0307929855460b200401800d034440380c01e042d01034602503038502c54150700e82406a68912a6004001007544a03200180c07212000414400d546440a010b8a00b440c0d5254000010181d091071a80a081d110f2001807055015551985034001800d1070000301c07509008100d1092031101804443c0a42c00405c801b00c20311501410400000496000582408241e124070104c804c3c400d01040741e0250810310009803544c414001d69090b9550308001d0b08554116540e440010090b00c0c0d030071103140c011a401200d47d00411000f03040124001c0b4003520310459103d03480c00005141d00c0c1c0c0c8034241883c10005000c0d41c500b4119240a4403c151a030444400b00c40841502e1800307140d001900150402812100c480c0810f4401079002d2080c13003803c40982c41c0c00225005440d4100c9031284c800d20141540380c0c501c6801700c503e07480d070600410019440c00b92074000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 489304883 1250 489303633 489303641
    0x7050d08160803010602060a05041a100e0a020406021b090711100518061f060c03030e010504030c020306010b1206040f09060908130b0f0a0809190b071202090a05100e04 74
    0x30603205090040010445e01c0e406000340ca83c040d040c100d041140c0d28140e0b483d1180f10700001c24241d0f102041100041100c0008001c01010300040c03501051a440e008900c2c1001e58464014100180078034038010b440780105400c01107003400001c140c11420750701c0b040203c03a0b20401001c01d8420b8410304402d091402c00611841c1c3c01a2034038401100e080b01c1d03001590745090006006803000a03001c806034110070003070a4040d01a640b041c0381000d00003580e0b0804502800c01d40d10701e000356500c1c000034441059000441150b00030f200b234042c0d41c01aa40c507410b1740d18501407020801700071141d610002c1d800c2c2c642981300508050750101c3c0014201a10b865400803128208011261068000341d03110360144421003c80c0200311800b11179140c2041781d503004595001e0b0140304020f10400b1004200c0a00080c0001060038500303200e040c250752a1410300105050702a81ca48011075120342c4000070840c0f0500031507014641c007410b04c00360fa51508007807240125a180041040007401c00070041c40e80d9403802 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 489306133 1250 489304883 489304927
    0x403060608010f14190b030c190608070f0c110d0506071701080307030509040b040608030a0c0309060806420306040b18010303080907120b0a0c050c07050d08 69
    0x7009141c18081034112980b402c140c4d032030104a1020086000d11410b1440c12030860080702041d640022070110b0b141484680303e046e407100103211200c0c00440f10300c0c00e00040340d10759a510111622103003010340704004107071158400180e04070000d20115000d00320203074844070003500e828007444042d19002c1c10028282d680c5000240318a584280d511122040180908080c002640c07a10300140d4011303000c2c0c0310b08203900f40519281e080090030380d541c0768132140003016160301740c0340d4440081c100204039030040b14040300801c40d81c0034003041144c0b1440d10341f0300c0f6800c0038011041c0c8500030a50311071031450300c1703107110401030019403030106150030b2680015a141240c0049501d90800e68104400d6415881c6094064103c28090140011001c0d0415044942504240104c0c3e03e074950000e0800342c0079003040c140b070181003a610b03040104d4000d81c144280206001048803040000e4200d4180c880d40c00b500e00254072615040c4020310700034007440742c0c0e184100030782403404c3c901c107030050364016140c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 489307383 1250 489306133 489306149
    0x12020307050304110306010b16020a05040501060c030f0201230411150a030e06060d02150c0a111903050304091104090e01060303021005010b030406050402030c120c03250b03060604030606 82
    0x100c00e001c100310740342c0e01e404c503020000c801514041d8144001301e005070150300c1c000c001506191103404150746505030170401804010700140519a11050090a80c2802090880000d02801d80990031184184110790040307048a200c0400040d0400c1c0d021412900a0f200b44c0360070030000b0b220f5038a5562502240460b0341088486608d4054010700641128509809082c4a80021080080603501d00f6108500079034100c840240078500c0040b144010702030000c40401512407801c600040c81300414800d000c07108100e8105001402e01036800c400e10310180310080c2190302c240002e12580c407190300442a01c4a1080019041c17640d101804010340f0114002d10640340d540b84800e105141d4184940d10b0111032280092010703501d4604c0890080c80006c10240044c1da1fa0300104045503010301c0220603800c1c0051100c1034072400031219503203926030305101500c00c2c400d02c0d6205104030301840c1d40c800c43d0021180002691868100c01d01020b034801040141d001804202c04030006280b0b11030100505111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 489308633 1250 489307383 489307387
    0x5060703180f050310051306020a0c0606060c060f0b031e011401090501090605030d02070b0a0912060e0f190b040302070329010b0702060315010e270c091507031202030705 75
    0x1106041c2403000600380c44c0c90186c100743c10030403059403440d81d840c00315920640c0180d031804021001c40741c0d0101080700070081c9040003c005415584401030396a0035015500c2000501e04102e0094101c1e818140e040350542c015064a41d820949440852103201465002041c182e8410f003c040d00d1103800d030032080380c1d95550401400f84403074610821016060580c0240340b403048a4801940d20710192203401c50b10304c00061149040d6219588117030040a0504a040403425035140c17250260015000c090b03070500c19a000950319080010710388002d0480f045011005d580c1039119a410318a0041040d0194030819200200003802c040c118800c581800764901060180c0c0e4580c4112820184e02044e00150305100707038005680c520f400c03650864540842101d08641131001aa940880c00850544c007007414041b80c0c00c8000340040514032041c002080e082c55540d508404000c42c059040c4894004400d00781d10050760641100a180f0b280c02818802000c1c2e00b051420f00c203992040356000000703400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 489309883 1250 489308633 489308639
    0xb070f0501050a18080c010605130903083111090f070207150827010c09050312130b0a1206170d02060405060a09110607230c01080105060703180f 64
    0x78860b460308404030807014854411541c0d11404d80800410010380340000001700b990311900250b120400801d0098035444142c024010000018080d84900340c0100d8105000143c030511020005000103070003518212801c41c410028400c21044440b04840f0b01140b070903209100d0f510310304a28403512102034038000520b00640020309280d1945d000c0c19966180d00c1c040c240441e040103003240d000440030560308040b02c01c080ba2603c000144c08801a5551814a100446031340c05031180e0241d540540445510340590390349a0b07030600c80c1024803071004484400901481c01e0036002030903103680600d07081180880c19844582103880c2a401011584004121080403580c10f00c4a440c11203042e00243c086c80c5000d417141d6803a844004d100d40c0d070003542e4139203103004c01560340300b51111602c010340702c540c0b80c440745d240100c40c81c154580c207880410700100304200c00c1400040c10300101310060b0345103001640303010103205035504400302c104c060240301c0c100a100b0754090401032008003a100c42042400345 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 489311133 1250 489309883 489309893
    0xa0c0503100903050702010c0501090f03051908040f1b031a06040f0e151009020c0313051e0907090504090605010501080a181511040f150518011101060b070f 69
    0x1c01c020740495a41e0070310501c000401c1e000b9065400554080c2000c44c0c0c601e0440c64204c1c01400708120003030a66000203031a006260740030024100fa4004040191541d050b522820303981810b0031a8000c0000d00351740d00034000520119000e00b1401c500c2e05000113415103d61350b460064400c00442400304120130104500e51a00340200c00c024070303458408004035101011103544404080700d000540588003804200002c85c1c01c2c04400082203003080c110b464001c00101755442e0340c088030400c420802005030200d540c1c948540c0071161140100c3d03030700c4000c2e40c0000a1103a0710100904100c1481400140000c250300c480c010401039a104034000185581410005400d50300040d042125041c0f41040e11242a0702c0d11140344401c6802c24590070011aa00010704080c02e0b4480300306400901c041400103811440c010740c40281e4070040c0b0000003204241400311103a0103009000f0f01000c00075035100b032455010300c01800399001c07018000b04965031100e00c58a01070344042e10490300090700c0140c0c001400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 489312383 1250 489311133 489311143
    0xc0d120210020403211b05072402030d0b1c0f17091003091e1a0c07120509040603060c171b040302060c030405030115080d0905100507020d050a0c0503 66
    0x5481c009046080c18116200c1d21302103c061850241c10003a500120100a40030f188988090705c034440e0f29204411081c501207840380300364803030094411440c16030b8500f0702c0b0403240c400d0313004001a4019410a115184500003801c1290742c8039400803900e9041002000f540d181e0080d460380034800703c810307101c0186800100941c80118101403040c0c10301080c0040c0d690282444c200c44124900424202101e08106140980a0710910030484041078494108508440c05080402e900050980785030b5895182c100c00303102c3c81c003001782095000440c2009450041020f00342003803015200040d0a034a07a0390300001c071040c28410030042003025407038070a0040300074032081d800240c002d03506d818511151000e007000d0040d0300000b4800d11003c03800040e1501c003002540c0c010315008000b44019921520301ca81741c03156900420003a4002e43c2c0701e4000c8136020703c003980d04860b8082c0000d51200c000d04401c13181900122001c0fa4004108110f00d800718404010301e05896005518043c1c0c1d007890300042504e81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 489313633 1250 489312383 489312403
    0xa051c060b1008040b090601081c120e010903022e1802090c091908030304032604150e0105060108150d0c09020903010b10090302041104080109030c051605090103080a020c0d1202 78
    0x25611120050100d8503022920302b0454900980600b11035551150a4440c0720107620b560589500c2d0a8000c2c46044054001c1504507000703400352110114074280e08907090108201001890400c02c40b80c0d4001000c0c0ea00543c00c1e05580b8141c04104119580041d10301c00c003c1e079481c18407090104075041c07a49884080d0482c44030b202090b900c00e0614145945813a40402030000c1c0900600152545d5090342040ca000c00745480304401c4441854070b40341502181b000745115000c0300345004250000088144511800703454140c40704071490ba1070403160310006804200d013a420804101c074007800543c0d1135241c2d0380907005004d00075032524444d00c2410708403100148540e20803094103c110300340540100c01c050540c1e4055401244141d40e01800610034440c50780020785541c83c1c8001c1c07409240c0d01902041c02d1350301c07a00940b0003040c013603040030700030b08107900a4503032280c0914010070008208400400c501030150043c1d42c0c9101101c2c0005000081d407901c03d5802d03c480c211500c03c150f07030600c001010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 489314883 1250 489313633 489313651
    0x2309091312050c07090203090a02031006060801120503190e03010204120b0603060f1f0b03010e07030e0d140309010b030d020f0f0102030c071506030209190b0a051c060b1008040b 78
    0x1e006004420303e903120480e00c90034090a1b400408a1984c0c041446070b86001c0e078000d01110b600800898451000342054811000080e1008001143e008003048004c1203540c0c1010065080500302d19440d90101100c107095400c1c00080324070904180c800703001500c01007800003049030790810a42081c03004400c00902c99032107600041c0800030030034000c8100e20f0b0808228005582c0c902040c4252070403030710b2241c014104008002c0000902d142c0040070b102c0c072400d4503580c240000440120901d0361121140d5004004c2051810000230b5440c000c400b86a100490000215091800c9004642020380460701080142c11240e0403210700c41080125540c032400c140000c500e949441c3d280c0c030103140240403004044620400b2a0007002009401c008087c5030020000910307070400c2c0c1c03e021f010105200304501e84904080d803a001510f0038030400d9003114006022081c0c030b04445003081800d00f058143c200c66465175001c0c046d81d1622441140180030401d43ca6000329170030035003480038502100501000c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 489316133 1250 489314883 489314887
    0x50d020c010f151a07030207062001060e010602160f0909030e180106180e06060306030f0f0319050f03011a070803010b070b06040903020a02010311040803030c1810230909131205 78
    0x400a54000780c81c90840310327940f46c80c5112021403c40c01c10303041c0c035400b501441c56003007041c003240416a01140a0480341c01340c00301c1d001c14601d080b0000350700103030344254004569142820800d40340d841d0060108140f107894010b0300401600b00260007030310000c5d91001803d04800040c030056406c03900220344ca030a5201c141c00d495151034019a1b01032002041d55000e19400320100d032498404000c4030001101d44416100a10800d002a50b42c0b900b044030204102140d001351102c000b8018806c5420407401e01043c14075680c00c0220a014440403e501b4400e00c84017040280c021038003400185000c1c00d110304000b55100c000f4102070b500d030600900700e030f4400e40c9007844081c002034000800881880d030a08020550000f0107a190110380115800f41c45180170000030406101016002070a90705110048075110701192024030103180721503a2840d011071a004800100701070055004070a0700c05142d440c07460240102c010507042c400a8808896402d03120b08844d04111542481003a100803500c0c00341c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 489317383 1250 489316133 489316147
    0x30605060313060c11012a0302070c1217130603050f090309040f181103010e03090d06090204021c050405070e060105180a050a0f17030a050d020c010f151a 68
    0x2c0325009111801000300303641d000000201070046544626a06000008000c100b891102820107068482201c005a0240c50002590b035802403080c0c50510b504007440180d0142424a0050815043c040030b440140403881400b880d0510700740104442e0f0a20049402d070302e80f8001c0090241c941c094020000041c4000401c03403068000030598917034440840d004a50a24402c07a09030003031500c0e41603a540302c800c203442d00003448413a0941148045094000700000644a402c903601c038040d603c1c090b82d002c02c2c601c0181300444c0c0c040d008116041d0009100510340b610580f26041c1c003500000c08018130301d494008200c00c2c00828030440300180072078002c00c4101d240c0003000034400d102d070712644496a1405220598180c69411400d000f0307207006010034131050340f00c040e00340700c00b441132142c46410031b01500303000f41410010055420030b003441e4498a0804c404024050040d401001c224146503582e0a00450070019501400003680c1306101c1c0240254100411007046011a43c03140c0c041070300030880c2c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 489318633 1250 489317383 489317401
    0x50109051f140c070806060d110910180507031506020717150702060f010603060302010c020915130c031104030b0105040221041a07020a0203100e010b120c010306050603 74
    0xc041c01d000d1401c540708415036080155400c01c161030808401240c0403d00320f40041000403080269400340c1e00312a45541d8000c200583d0358032111009143d85004400d080581c24086c6c0079540243c0c0d0f0880e82c4070105c0e00d0344040400d003800015280030068654040c048090f8040c410018800156850340e4a141e09011010b96104000e2040018030040da10b01c01a42c03030f1060001c070b5501d040a100595042c28401d030006c0d0f03588010785060074981000000025694028440e034030442c0d0741a15210080f91aa800304004064003c0190b440c40c0d0189151144503030f1908150010145403200000d0320b041108001401c48100e501c0040e40d607482000300741302040751a00740c503045510407940582c0d80d4211103042c0c0003140703d5858085500c003103c8240010403009113824001c0450700281190309503103480c1308030313699074517020040d415400c0b00540105c00040c6410124480e0000c0d070020480004e000081120030089003007036070303a0790000280514650b0781070080800502c0e081f20201e003141025049 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 489319883 1250 489318633 489318649
    0x70f03170403090e070203090402030103060501030b0618270f1020030414030405060d09051c08041b17030c0105060a0b0d09021309080717181903050a1b05010905 71
    0x50305880001391000100380d544200216840b440300a8000e45d120350f901d10b0010003401081c00b00300c40b5410000006056403c1900200008884410007216a03840b0740c824039844219141e15222440c448060251007000204040c0c2e1420301120000e1150040083c0079608550084100d5402d21451507542d0107080c0d68001034035046a0030010032060f544006181e140303907109030382c8800d4001c0c102080c01c0e51b01d00603650002c9075490140302928070084807003103030b0680545201c400101046076007002ca00814008076994001d914805800d000705600e408500b800381030400c85990981d8000100314036251001e0092982016090302d503080f0841c241201101c240c0214200c0b07200395955403800106640c0c8411144c42c820115240410054886040101c001c2d8400708c4162014107059140c1100142180101e0b000d4010383c0003c01d600c10252020000d40a41780302e113502e2200a20000400802e000382b0241d402c0600c1101c41c40d69050551400084920580e40b056040c0041f0780405c0007252a5821 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 489321133 1250 489319883 489319889
    0x9111c020108102303030705160f06030216060914103204120302040e070e030f060420120f0c030609070806150121060f12050d0302030714070f0317040309 68
    0x5130030f5072200001000c03d2960142e00000340c00c0340304a007500310001c1458444002507505541901514941361281903050b80301c2c4030403844c0c00c010010384141c08200030b82e001c0c0e08201d01c83c42d102403040c0c404907100c03450040c0400000201540c5c45118110944145e106e1060306401000c0006100810140070500c42000420251081d80216542c42c0350910981c115000740c0703584e40d081e108504143c07400130b20b41c00c0031011460080c4a00c8020310406280051414469540710000444140b0600c0310030031032030f10b6403042903048001c0d54180c2c40070260038051006241c601400a00d00070036404105450148040d020240342c2e044001d040c403055501081041c0d002c504592011004409400101c545800368411003009595141595840c4049500700d030044400c1440d121074203030f07140d800042851041d100c00404039071059005120303070350103078015551003103840c2042e00e640e0b22901d00900007540028003c4801c0c240c0940791004054200d07801c41e40c1a00c03840c00448543ca002d075006012000240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 489322383 1250 489321133 489321179
    0xc0d080a02070f030b010509070815010509300610061e0e060c0f010c050a020715030b0a08010c021c2c060d02031911030a09111c02010810 61
    0x182400241d00030002d4200a0404200341041030383e503401c001d000f428003801003038855a104008291214845d90f0f8180c002c0005001c0d05250340081c000548042d40012090342c0c1020300d0f00000c41014050745001d960b8403086640c1c1c4101e0702d2241841600301071300100075000b0190900c0c000d01040e1343c01190340e82040f800c00d035203484001240d107003540c00ca00c04043c0301e60711883c0000c90141120b00072403280d50400c013540007442000d000f000184d40c0c50203444120030041e8801001000720228003152030004055500b000100440110f01240e0b003888a0303002881541e441c0d040d02c0740701c15410408600c280e428820300d103074048014140204a80e40e5041004210480c0784050100c84105640842c0c2902005001e80e03918004d0555000180d00304403035030074a5115854810461005500400242c4010b0200c041d1031680c1780c145000040444040640d0b015003010b00340103d907265a5440703200d4940800c40341c1d4425a113440014402c2d000200304410708010002c04001004801c58500941440c01c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 489323633 1250 489322383 489322387
    0xd170c0702040603210e1e010305100b0301030807030e060301050f0402030411030f010f0605090606030f180304032d15021b07062601030503030106080402041b030c110c0d08 76
    0x190001501800c15504003910b000c84101c0d0030f00504007817090888402000e40c58003c0b50b00140410031102c0356100c0341090005604d0354000e2060740c030941c023180d800441c4d51101a1090748444900005800036003040350560400110070b0145a00070011403801e020854900d8915130520000c1898a040707440750a000e00c0d0044080350401a1612691040c19005800c580c2ea91420550644c06440003920460120307141c03e2011810b410040ca0352485001e01501c1640b07103456421440000000050007500001840c4000700c000d04400c1c07004000560050901c4580d04182d01504000a07012106116880c640503031000005502c003c0d0b5030203c81d013607800c01030319602030b802c2460444072034106083e41d5004a00300071401c0390304a80061000700e002900800490803401003218030207070038007000c0c3c881e42c070a0004110284c452403165620170f10107400420001e0004040034070b002044070701e03000401e0f1117852481125030b00c2000d03072010b413440500070b110314008840804c4815021450180ca82200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 489324883 1250 489323633 489323647
    0x51c03050d0903050306130e0613021210020a080c130312090308030c0a020601050306090a022b0507150c0c05091005061602030114220303060816080d170c 68
    0x155007521000e14001409000048861030000d04036070084038807510584c220081c1d0300d0b150b4100d10131104c0d0207850301d005100c203482d494010b50085c0000700b4200c0c0d100c070442030200401c02040c40500500c40e5010809a10303050300314405040281e0042c600b101d1004c0034001128800800440c420880360003140c0c80456100010080755103040b5a00090030030a0000180700c101150301d002411544250760985040743d0302c4a0805488103000d4424410b80d0b440720400b0b2000d850301b140e880300b91901e04031008011089010800d100303140245010341c0c0d1604200003c1040c5503d43d6001e180304071035840c0821a4002c6582c83c04100c0c0c0c1180203450059022000103800009401242005040024091520b95500a80b80c4820042144040b80294200011101c3c200c80a0a01602036084900c00c024042c078085c03034500121250110543c00c15844200018400f0418401d40b40e880c903580480d014111f04000000c2d192004041d51102044004044021103901950b0b006400164641ca200d544e040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 489326133 1250 489324883 489324887
    0xd030f08090316050c030c01050a0c0b09010219080601171b1c060803030907050d020a0302010302090f10030b120d350a0b040f060305120912010504080301050a0b04051c03 75
    0x184562075143d040c0c01d2015031041c0040003520700d0740c1c01e50480441e04000603040c011246402400d0780000420f044807401c0c00000c1c1d40500041d0b000020348001414114184040c000940e04060800041041071042c080342c1c0d680305003001e5103082c8992a00700c407405c007600c3c0269042c0030301d941c0b800140000300b6070032030080b0303030b40503401360b019481d0024081d1399101d060081e10b9900c1510040c0b000e01c10303d0000111824286d615400d41a0003c003007866213455900154060b5011017041c0394000e40c00c3ca80c0d041c02ea03407540c40741051098941d60016003044072009010176180c00341c58030040c41c0e02a423241000d903540114071658151000260041c1245108002c0d41e003d10b001d0b400c43d44800340c52042201422082c2c0c802a03280c2d20880300ac2c486201c01c582c4840480c1c09601000d481ca4101005203442c06001d28002c0903040006088218495242c0b43d007070f03013120030a40d4121034103407000004000034600301ca002e4004d800820040c07031800d40b4200008192101d007061150100d1840924142414 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 489327383 1250 489326133 489326137
    0x140705130e0106032304020a03030c08070b010927020a0302101815081e010902031305030318010b0303040f12020604090c02010c092306071e05100b0d030f080903 71
    0xc001210200c2455840711800b07005000226900207461780440584c101c16101c0e5083c00c1c6c011030b00a0902520241075032011601c1d602e0252007507414030420060140017a214030f1042d030080c15411400240e0080d1400a0001d03d101d6566030054200008580300160352020700d00c008507079044540c50480004407000f52036141c00100c4400016403202800a6440303c2024403034042e0306240d84084450ba54500407610311300981c0300c03034400c0c595110010702c0406030b15401103420848625244100300c0680e5200c9246920032184095000030442c02c00010700b0302401105162076045014605040c14402d504615441600c03601114041e00ba01410554036640115805041d00348002e0014002021340030b4041c007890100c4200084c4d6000380000d00b03001c8400d80f0000b4507940d080c8074070012000d401700419074210080a540345912804c00030000041200002c461510400180101045500b020b4089510400c5081d000344c9034460b0303840009038001030515103094981800200c980b250802ca510354 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 489328633 1250 489327383 489327389
    0x1030b0315100608010b030f090309150702090a0902060f0919091b03024602060a0e0718050702010609050c0405150910050a0c0609150f14070513 64
    0x940141003041d50034040851281c1e11460301421400c04a994491085550403400d05c60444103040034000309001c484031049940d0401d50b001c00b100d040260000024104c1c0e030000d2200215503030001005030450900301d0200341e0110503001e00304035944158000c11818801e40c40d10f0494000c0c002843c00c1c1d159540100985281004168020b10700c0d101c0020100420f000b900d028400d4203080c440100c080d11a0003101c01142c00050003150788085003050f9100030034a0800c000030302c1000d0200c520030307146054002000c0d0310b59500030000c03030620181800c100c5100c9100c1100b03035008080280008100064015080e02c800b010020300c9a075051030490061a8036001070114074200302c203204564408030043c00980b2422642403c14113104100e0003d903100701c26920f0b400040c0b11140c000342c00e00840181c0365403030181c18101c2001c01d0326a41c400c200c0d802c2c9403045a181110f6507421051075000e201daa01508a01d801c02c100315242e04210f0300744a5030003441c0b501044400610102006801c8800c4402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 489329883 1250 489328633 489328639
    0x91005040e0f04021206060625080d0606080709060f050d0f090b010617010828050d02100b0409020f2106011401020d080c0306060703090b0a021c02010209180601030b 73
    0x514102082501c0841c1c4064405030b2007500d001d0085c0d00e440c0d0001c20858058100108518a04800055a080f0328401408680030220000042a011840c5c24000f0200704003400f034002940f80c2031103005000f00794040c03c954100818000280090ba401004006802e076560030f0094642210403400c2e400751000c62140282e03a820032003041c00300705158940740c0c140c62498562200d00c49807500044030200c0c091056400c65401800c90a2002400740344c441148810325102500118030703512034518000c919a481c5c40140c0c000004911200c825200e82c0d00d025408940900142d00541c00058680703070801c528a2080c0394900c1c0304c40041401c060b907002ca224000055030031645c1d40d104640c028a44c04044240940030707420645601c1881070420501c90300200b180c860a68594030140300c1640c100d54021800c0c41840c0002141000c0007102034803c0703001581c010301c4408550b04c00c04902041c60307801482076a005005448803a900e40391011480d041c0b507442d45007240e5401e00100c000d0089000d203203030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 489331133 1250 489329883 489329909
    0xf090301091b0b090918030c03040303020a020a06050c0c041a130209120105040c0b030429041406060d02010c050a0f2306070807050904060b040f090e03040b09100504 73
    0x1042101401a84002050303001c2c1c00540540c0d0340d900c00000b440781d03500417a07006940500151070380184066006012990408990a00309400c3c0c6140c1f03140d12a40069000da801428070408624140c0c03103983c0030b4034240c41c0c11400c3c0324940e08041c0d07607030842c0900f036442140c0719054412404429034aa41c10050300a01801d50b04030390812640003540404482030003a04c1070061001021014001c10b070140c2d910000d09104503280211084c3c0a400140c0f046519030600b003c0402c12414441c44480d50100c0800303041c016003030928015155403020000da50194104208004c01c598400540c00710198082c01c1004801e4042c1c0b50050806503211001004143e005003e1000d210509030300000804100302c040842c108180c04a6507203482c210f0b0b082000440c820006220140304501912108001410104d082d40d210401309000e0741080d00308800d60311021030100701c01c43c46405010507045000c1c0145150034100180103c052041c4074810b07028004103c600c141d59481841120300400d10251040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 489332383 1250 489331133 489331151
    0xa200123131406070210030b040203040b01061710050d150c0503010515030c030604090609051f061212031508010507050a030501060e09180102091206010303090f0b0f0f090301 77
    0x180c001c1c1c0000192006440540c4070202e648030100901802100c801001c441c1403100580c01c00041110300d03003405040580b140240d84068585002860286110b054007100542c1444001480c1481c0c1e54008807181000c2801e0014a00d0084107807800e40340141c0b0641607204450601ca15203101200700146510b00c3c00d400d203000c46601902550682e802140d10140b01c0c0c4115080d003078580400d507000c90301320500300003042c2149440c0d88401d8a1a21606000c1282141621a40d0505e030f0a0b824078841e06020a003040e01c01440b61150300090f040c03400110406c42115201c3d240d0b40d0151510040500d0340c1c0308065104c242030f00c0c8900005003641c000901c41403900300702c014202d4200442c1040400d00304400450440e00981000384400c00141001000d80c0c1c8096001c9800c8402421511440d5401c029000781a200c0c0316403c084620350500400b915450b614001b4280c8580303520060300300c0c40d03001040c48040042821507074913007010407005844950a00c0008801c1c03240100c01541986828541 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 489333633 1250 489332383 489332447
    0x13080a031814150708010506030612010f0b01120204230d1b030203010f022d04080d09050a0f1a2506051015170910020301260a2001 58
    0x20710050702d1628140d5071043d03004110440602c800fa40c0540201d80d54800600c080d00344a0044d5907c104020802000c00c0901d5518a0841e00c1c13114421080300d485146a0a4558001050b040102d104080c00c600c0c151802d100e03607403809a141d8401d08440904208070350b07152b944004800482d600141c1043c0240645403100c1d01d0740005200407400387d400c0c074400018041c85c51003031f20249613a0f1903111104085005840020002c144403030343d08003500384800302c0c2c031903010010411641c945440b0f241400342094104180c01c034440e8484920921042030510800c1942d030784040f01010150110354075034150013040119144001c076042034400701e88400c0400c1c000e0940215014600c2c3c507094150b01601e90400d001c03401c00c0d0340b0041000c0380f5448542003082d458240025842a014010340308924005c90745a002eaa00a9100710b0903446890340100c01d4900b01c82801109103021f000404074041c059458840050400107040c0a28803065007100350b0307900400c94042800d0109481c80e182401e21022 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 489334883 1250 489333633 489333653
    0xa06050406231609030f0b09010603050d02010221060a06080907030503030f060108070e01020c1e040203041212020a0e0f010509040e070f12050a2303040f1d13080a0318 74
    0x521880b80e0700860441403e43e0044c13031640d00f680d40020b4108424a0a03841e0301c0d1180c02c02410034540c5659a107000030100d002400321010701d40199001507990038480206582d80c2c1000c00c0c02c8030280661100f4061a0341ea400d501e5000c44180f82010002c035500c14003042c0c100800d6134009840c03030200208002d800d1104c03000b04c912408090300d51810940b1a604115071507414910010b006d41e020002d4040585410101c0419500340002003aa08540c104007040c1a41c1042e02d08407032100c91200452115504007000c000701c9014294218203040c01c01500800700b0381e421a9030341c010400c0d80b08000035a4450422030365442001f90041c0201256810000c1d600e11061242c10160b44d403124000c07823403545000a0044442d00b001c0104152000c82d00e07024418528000a140b050b0303507419550a40383c00070f001410050030101c0000d8480d516207000031110b1280781c060903038900403510801003110b60000c103d00080c0c0c4c01901250310388403888001d8008101c180c04900c0b170000350700c451400304040408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 489336133 1250 489334883 489334891
    0x19030b122509020c15060a0906030f0302010e03030c0d0f091a0402100201020403050c09070c02030703030804120e010c030309020f0604030f1103030306030d031a0909010f0501060e030a0605040623 86
    0x30140c0c1401e981d03803141100324000c2151460064012017421064940002c1019070408030042200c4c4030143d07a901900300b01c40a56004072843c0c8041c101141c01d058080c403621743e104080700c003d1481d51404e100000003a200c2c21058208050361004028041117660f800440341540c0078880e40d803920b000c20b01e00100060100c038101d20590071110b580c50154410300956046030340c440000d2120004403000c0100020000702440e04015142004c030016a4007080100000e40c000e0b2a003003803c1c1002d0130010111140d646041040c404840503044503668081840842c00ba00341c07400059450940c070014600010081c80c81d0f0b0300034000701d00131040c811011480e6107454400d0107150800c600d088149500e03400f04030303a05c40d495001540d550007001e0003508050400507035040001c0d5500d07403010000301c20500542c0d422036169507e00c2c00d0240c40e0004e1003441e0140c0403074144482c1101500d0006503503284d005000900454461000c5030801c1410381154170170340c800c3c0003700c01400b4000c850448400b4112 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 489337383 1250 489336133 489336193
    0xd1401061d0307050a03020d0f05030a0f0806100504120c0f150e0301050106050717041d01051c0512090105040801180201090603050108071a0c06091b040219030b12 72
    0x407082101074500003806608441029080940c07491941d002c02c480c0a5081c0c3d02547d1a8625905460010340180010040c1044c0350f240c4100105111034010701d40400100313503e02030300040d0001800c540d00f0a00355001c0710182030703403407586004c00d1901c2d80c100c3c04180e22524081465400110f080c52030407201c07a030740e110503603141700328404840109400e0380c40a10030ba0022a000f0000000401c1c40f41f00d0316043c64107038801c2c0f81d01c3c0c1542c0d64000c8980403c0107290052000401c2d0040c80949495240344003840700c426140c00c1e5820383c0e03486081d202d0461040f0042400d40014584130349034020b6090310010440e25000b00018091507000c00c002d5904124100d00041d02e020f0003103001d5000c2d00c00c1905a0700780600070194035080c81440050801000d80c10241c0750428401c3e610444001c00189200b25410000340894034034103400305100c502610341c07140c4150b0046c400080d24100311554403502c00014500451005c0209002c00d1084c028000c06520314050341c01316102900703001030807241c81940d003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 489338633 1250 489337383 489337427
    0x2040806013b07122c031c06050f041e051302090406060e010e0108071203030603020613090c033e030f06030607031a0d02060d0c080f060105070c0303050d140106 71
    0x440040301701e8602d803402c1c0d0341040c400d040e56507880c40d005401c00c0c882004a41100e1400d608048106811b240b0100350a012a88402060046007042c0842c502c03124010b42c2c090007440b0310340e107201c01c0c00880100b40a584641e602c00050017201c0c20303407071030000540107013440f101800c1505010016018500400e441c2c21042c600001b5141003400d1454102d48030b56024140303040c101030490b40d0b6001d80d45002d5040584401c4080007580c0d881e0300802d602c00803c0030040d10940b41140c0001034490202440003450318220814940520951025a1485030548547d031390520641a00600b00c15064414400345000300c208a20207000b140312030302076842102110f2a581d0f40c07c40450942d012800a8440c884145030030b84d6517410504031542c4503d20040c40c1e24200038a40d000c02e4200c03840a501100002c6a42c010b00401658500e50103400c04070030320346240b6040d195192200f6903925840000c00704100003c10108244050f4850448400d200b0586a13207035958100c0102502020b0040044601034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 489339883 1250 489338633 489338657
    0x204030b0f1605030a11040b04090b0321040e0603010e0f06040b0903090637091d01030206030c0c010207020405010311011e0f0c0204090602070b040c0902040806013b07 74
    0xa1102d010000031290399101d03d1607039015008001340800022022002d4400e01c00440c290143c070010b04090400701500040802c49941010b03d030a24020042007000e011500d90141c1041d841c04aa043c0d0345440002c415948450000c0f034010194080d45081e103020b000b08680e0582800b0030124004c40c0070f051601000e8071042d03100390300c9106514500364406020440001c070140c810303030b00700003440240c4c603849210000c0d000244010307286843c013100025101c2030240800301100350104014000c0342c0102000d5030440d17011424500c000b504007009070001241c22041a5000d4045403201a40500180000d595910b481e04a03111803507112030201e40c000300c5081100803034800700e007210259035542d81d00540020304103039543e0300d40724030a98029858120941c0441c100f800140083c43c4244000303c1c043c9002c3c1022060307030000c2c1d08207054560040200b0002c000c00001c0460560301d00e0f00d200042c01d00740c05c074608140c0d05098907618545039000311044d84851240b00551280c0001e45840241001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 489341133 1250 489339883 489339901
    0x200a140d0f021009060e061006110a020f12031b03041401020a11101107181d1218090f0711031201150917030a0e040e0d030902040f0204030b0f 63
    0x306100e09500183e00180100d001410795402698440340030700c1001584e400074028460404004a40d60100c01058038010007209a00450152014a601001d031034018841d80c00503543c0b41c20300070168803800310b8099050588105004840489441036400d0000f200d04800c1d4a07281d4019100742100c09840c003800c80204e50000c90344602442d400300c08026950301040030404048070121082c4104041c0c141c0d1403003030813020050040074100c9414286c5c0c0c410381d5041c03100240c41b5071003a8a04078113400d01910402140024003007151440561501b1707102d05083e04042c188034076285400e58410038a0080c081051498003009008100b0352362101c00030004221220b03501d100b06515006403003501001008240008030382e40c140805d891801c014010342c1c1c0c0d07500904207000d90000a0391a00001480c08419030041c00608004100b07441c1400b00308190613605850341380081883c070030315444800d0403045645d47e40c0300100107200c6500c11500c80343c880c00d1040b8014400c441c0744540e605040003107034a80f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 489342383 1250 489341133 489341147
    0x3160606060e0f15040902120a0605010906090e09012310050402030603030703050f070f1a0618070305132a0509040b06010c06021e280906200a140d 65
    0x401070910803c904808091102e00000440c481201072014080440e581c203683c0010645417152041e9042c25003041003440085a03000d0744428180148224100221500a500401190500710560460b9611000924094025242a05808041c81a82c07690f90715034020224028264014088411500c3e4000d0208901c0152a4154142c0c428070030503001130f100300004c1400000e020811410815142d940c060380300d081c1d08040310301c0c650751050071044040b40709900341d01460841c0c0c850561049881e0081515030f01400c40310800d91140005940c2149001405c0195070780041c01c500d00d01c28060401a40c000403480e003007018a03082030001414500451014010382c0c200d00c80000e40d032503030030040d00c1c2903040e44822a1001d07001e001d00120410303145114a100c003c8030090782d945544014140c00f1410040a0504a038640d20061021b00c680c00034080064900c0f6043c48071500d000303159035945410517107440c0402841802040340c00c110b00b60b8100c801c85000d041c200c88001c05c000740151408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 489343633 1250 489342383 489342407
    0xf140a0c0909050d0c020f0f0d0b01080a0210030b0f0d080c0d0503061504080727110d051f03021012050c04140618010302031305030304120e040605060712110316060606 74
    0x821221842122300e40000025a4500000e1900390085502d80d182100c010303099002526681001400b58107500b007868400c65025101d240400c810144440000c03104c100740e03040c082c016856242c0003010440007000f02c50341047d180044450040980307400600c60380c001c50700180200c6d40c0c00824410f88242006031402e0f6464070028040b0300b410a02003e0780c0d4080c0240000c141c07040140b40c01d00340c0500d84100c013051048450135a070b5880c00b240c000030542e20b024000004481250002d0b40744489803001308004d50b43d0480d8914101d4421400490700140008101c02c0d02e030340f900081c06500c40401d0700400c1220440314560645041032010044203004404c0140e05001c025071501440351310070340c01564450141407428070300c040c050f140d00380395820407601150b22a1400e01c03006402900146059203050084509004150404010402901407844020002403040c0b99603c40540100c07400103854100c0021640c41d070a140d8006401022044070a6885501c0c08502050a9106d28600d42c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 489344883 1250 489343633 489343639
    0x7080708120a140409060f0e010302091501030e0102180a0f0b0a03020c1002070f0c050a060c0206091f050304350d0f02040621090f140a0c0909050d0c02 67
    0xd90381100c40c41d0200d03648000c1070764080000c030300480303800700c4a03142c00340010305681030300019050308140110800c046c0c1c07600040f0155a1a400400041c0e407a04061030380200745901c1e6440c2c1c120b5600051b0051b14040851900310b50001c903241c1e4440306215510914141d0450340703e0380240c1d8030609003a4107011805030181c540c1c0300304820f54903075000760000c0412440000c1124064103048a01c00101d800441e4121100b8684480140034071a58004480182030308076a520002c03840d01030050150654164000d008010100301d56006035101d20071090700b08501402c0b20906900b80e94002c00e82c1d40111402c03110150007403488e10702c02965a0b07454018000c41241c005a80c860b692072004a40c0000d845040e9803a101d01f1118080b12403800503100401d6541c51300ca0424894041704071000261690a1910515154040313002c2503104a02181507500310101c42c4040812700307021410940e10300009015a4031120300002d030500a035010301d10b410f0083e8183d50204510410444481c44695000b0f58 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 489346133 1250 489344883 489344893
    0x100c1709040f091e0f020d0b06040509070f05010f0504030506070903150c0c0b0c0c0f0105090d020604050607110307060e0d0306050f01120509011d0a030306151407030c06021b07080708 81
    0x11440c0700c10b0703022001a4080c0d920780e04c80241785d0740000d45154410380c0807100c86c502e22040c404c00d400e0a0080c41d0300540306201400c0200e042260f140075800c5140710f81810890f148460b13a9481b40204100d5024580000c1503801524100030090202d086500c0215599901c1c0043c14200500c0d621911583c0982a903582000d20117648440500c1740c805815442249070030010461200400c0214908924140c0000311307082ca031584d1080d0801c018800c5503800c2d0340200d42008001200400d90a503c02d00c00d05000c112100321130002c0b461805500c60083c6554607007003241c105d0b00f50004003c142ca20a0355002c0c80b4080d1a0300c02c0c0f10a40c00340da043c142c04130303030684001c02008d400d07500180c0e0b100081900001d140d180310010109405154444800c0da07800c1880c1c40c40c18140c1c1809203070003402607009100c40240704810010019a540c81c8094040a0041184000c040c840c0141401c015000340c01903490714140503003c0d8030b04c400507054958910810100051410020812808440d00100540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 489347383 1250 489346133 489346163
    0x30602072a0b030c16050f0f0a03120e0c030d0201021c0b0d02150d09210509011e090e04060b032806021e030c070c050a14100c1709040f09 61
    0x16080e82020b4a0304c00c104805200c44100700e0813400d414801035010b08020301600a4449031641400003081190010740c004a04c504040398100310000e401c501600400505540604040c40c2091042c950040c1c2c580142180d00b80d4080e130540240c001c0d8070301688020307441d444055415044900d804171140d08044c549a0503000340c605001107000b034640004045103848040510039044500c03c200403102d40c0c80c0713805204003c210117101b80c01c0001c80e50030014508510b120000c0d00c00c40901e0f00414000d41c030008860805c6120701100c20081a0030440501d4604007440d00801a201c03802940c3c0c041c0c803881e010b41c00254081c000c5d20789442440f0407104229609511610083c1d40f01c80705403c200d6501c2070310a1010619a00290320800312442c256880d591503142c40b660100c1c040e848284150690001070020342241c1c0902c005d01403040b80c0d244811621319006483c14240d0420103000141d2101070011083c090300024100c601c4101e90420000c042c007031544003200c04440000e482d20409130684 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 489348633 1250 489347383 489347399
    0x10309031209020a18090b090a020a0b0c030d0f020703020c0904030e040207050111030106080702060a0902060301060522031212050f0402040e1e1c0e031f15030602072a 74
    0x41031080c0054078080245417207a115101c0096181581c485860b9100065018000c41e14000c41e044041500030b8580b803003031a0000740343e4074103c0c0100900204000741d8400041f2040080b01c2003013218280500910244034000402508407200a60250284468400307007880c1c4100e20310700c17a40d81522040022524403090000a40003a1001c031000c4d0346e950f80c00c81401500c0b0000c0e6008099030b64503800d040c90010740080c1400d038040d2034110710070b0504040c940160303526010b8034150390b140e190007601c46005441e205807440d404031596881c10301954000c42405410b6019045010785601c0c1d44030740e0440e10341558210341040365003110011042002c5401490303c0d0300041c0700d04882d1070032600805405958400003580305200c15507240e00070b400c003a100d9198160303079459045041c01d05c100d040c0c4040e80445e44401030608401c090001003021120a40c025501035107000340f056040c03a612503101c0c500b04000703501130b840940c0c1401e030345000c80000c419003036200300309200d030b5004000c4424035241724 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 489349883 1250 489348633 489348641
    0x304120f0504172b0f0f0c06141006020c0303091203090a061d0a0b070221100609060512070b1309020c1507111e070b1201090b0103090312 61
    0x860040020401c0009003c03802c1c3e0185102590409010341140a20103552025a0f600c4d52140c01109104a0403094215082400c07000c2151542c2042c03c0c200c2520041104c4e00301c2800d000034002403070300445541842c581c00965100326141c02400d0b4100341c598074140d81d80d402d0b200200b035143e0700800540c0c41504100b038075030049a440904881c1003c0c0c42800250503507925030410400941e00321400311007410715840c459858041078a418040c0307820303c0c134810400d1041c0c110180c018022030036840a0074a00d42c4910889101800c181e480098264000d5005052240f0444c02035508101011810389480e406011001040d1001030400030b18020390488160454800000311450805001030000c4450004103506d95260000e4400320500041100610030040c4c2408100b20340c4840542d10104001009444a11b01070108078421004040c2c0520700400d903001032250b480085250f410020080502c03505079030522805220b448000001141141c0340c01b000500041c40d03a940b0200d001d10340f03600c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 489351133 1250 489349883 489349907
    0x1151404050a06120f290604030c03060519051e0603060c030103200904060605100311030c09060d020c150108150f190c020c0102012316050c0f061b030412 68
    0x213000b00b0013203812100305045a03510b400e6200000c5803007041030410500800c0e00824910102c5100d801e050668888429809140c040109011380d146c011031101d1365422040c00c1d01040580e410f014900c1d041031440c2c0ea00440040040010204001151140c58003181444c07284001d2008541103a00c2c47c3c40303a080f09900110b00001194800042c0b100c292600e0f070f5201e115900411011800629103424000003400c038401e01c00030540341c074215425240362760045907040503804116a440d40f980c0e00002c0c5091042440b50708075544001942e900280011400c1f0695010390441d030640340c0c0c2d880002680301c80303404070303640041c0c03c40a001520100e01c0640044c0c10405040780c00400303a02c0961404100c880281c048009a8856600c000266909004160b401d2018442042c14148a0780c001c000e1484040c001c40007100c0c0e144502d43c5624868010354074000442d13000c0310604681084c4440d1035100a484048031032824161051401c50000308607030003554480a00106030300821f5007181c1d1040c83d07039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 489352383 1250 489351133 489351167
    0x30504080f06010e01080d0804060b031014041a16032c0a060c09120204020706022a0709090305030f04031206140307060f0906030203040c050901151404050a06 70
    0x2020105191904110355100c1450440041010354100040002402c070168008a10366100c4007810250940c4020030070703001030341f0040200e00383c0340710400a42481c5d060b0a007401d141c0d01d0031400c0c8544400340816940950300481c1c0c81c4c000c26100c40304410b4801c804451503030110076000007110345d451082c2e01401c00c1325071206c2c0e401110307018142040380060b04d5401240c0c595105501d41424400c2500c560110780c02c19082580d40b4900e410f1441e40d00c001c4003d0042c0c4a143d020a440060200d1034040fa00d101d800240e1806002403016404041d14100f915000c3d8148114040403d2900051266410464054885908583c1c50b1001c4200d90ba20060045081000c80d03d0080c05a410380d015510140400c00914440900d2a034213040c1b03400003a600c0202004440c1041080d00c80d007000c1100181d40c0c0614016030303a07645604105140d44404c5c2e1120b038100040314000114008a01c1e0b41da0a40c814550b00c1d942d41650031b13a00301006001e1801020750002c900c0000b000000e005d41c2040e04522039070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 489353633 1250 489352383 489352387
    0x5040209011e090207050607030b1f050d0b10110705030c0d1b08060a06030605060d0f030f02030f0a0f12060f050409050f1e0601080f07060e010201020c0d0504060908030906030f040305 81
    0xf8090b0901681c000c604101c40640c0208184545d09425020f44400c106069800044000c044000480c0c180c020000c1d4030148140010704900045494000d100b03140d4014046031890780c140e9000074003000c2004172001a500445801040900e40402d00c1040daa00042440c0e0100c04a41c460a0301d00e4166241c0c410103582c00c100000c7c2d0b00006000645c8513080740c8100056036851410000140c0b0001044140709140c4030301036100140c02d0401c1003002c29054035069002d0258030206a15522610032a650b50101c0480c030b6054155010681c450090110f6603054a0000c049051030b044d0b4400c1e00800c0440c80740510240100d0425620102c000c40c011000c54000014015500d41440e03980741c0781618480031145c51642440c42045102d0060010000500102402c140850303210003490013141d040007030306d10198000d40e00c00d40655141c02c00d18170503100d4102c5940000340c0544d015204030b0b4049610054005000c0c42c01109a0302c02c00340242c150f51071580c80d096088525400144110148001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 489354883 1250 489353633 489353639
    0xb0a021606111303030917070506071b0e0a050117011506030e0307060609050402010801050111061609031203050f0105060a0e06090109030b0109051b070515060406080316120305040209011e 83
    0x180c910710001117020751180454507003171864801c40d29480c1e4181c03920a90140070104840e48a100c00c03103000c5a00100700301030340f644001c0c0320604000b042d44400d98855a01c01800030119155028604031041182d2542c61801500ca082d82640e60344d5070f8110302c03014611003c002c603600a4221103207404880c0140c80c588002a941d035012035a20f0780224034400c1d901c0b002c100455030003861150260100b42444141128020003c65442c90010700f400328480e8043c8080a125001320b40c0c0308051640800c000b0783c0c00034610001002807a0860360441380e2664007000003414104102206e03090b840307031b40e00c1c80140580781003400207581c060008241000f4111500102040880c0c6840740a450740e810007054034142008043c2c0001080c85038864102c000304149800a5000a4401e82e020f1690340c01120540e135100014004100550021905000c0040c01d043c00b441c030481d1003c0120b11902c1725100343d02440350110211002201d00039000b0072500c0061040344055641c4494011850001c1029151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 489356133 1250 489354883 489354907
    0x90f0d0809040c050408030705150a0506060d0903090e040303291503060d08190201051b0405040b121905060903130b0c030f07080304020f0f090105060c010902040903020a0b0a02160611 81
    0x407000c00207460541065001d040b5a8442c004a1504202f580101b40700c982001c070006403151183c440311080c0b142c1d031081c080c41014040e4a8140013010741201d0f0450524103414040c0142c60310140304003000070160600c2610102d00c000c1c1402c0010090010202c80003200208209980044d00306503020a00d000d80700c0014010b130004001c0c5186c4c20710300c181c0c8015080000380c20756001500204a914101c2c02c2508594070340c2c0103580403100c045901040043e124008901105510f42142e400c6002300b43e10030b41c03041075105045e180b0511850440e10195140c5848a4a070f00505902020105203400e0400512504102411030900450262480d0100d06081c5480746c0c0d000034001c540c610b40c0801000250b00c1c28003050b070304d56141a14851107030010710700010701030103050103042d00c5100e010540c422045025807101303d4540e0b0140003000100118200a0354407011451f04030f8031041c04e14006200403d050094648880807141d000070a4840c0e03907500800380203002c410150700c05062096802c00d503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 489357383 1250 489356133 489356137
    0x503070303110d02030c030f0304150e0705011b0519140d0206060a1d0408031008030c07052e0509041b03060807050105070c0e10030b070302090f0d0809040c05040803 73
    0x620940b201c1002e58085180d080c1441c0c0490b0950056420500c40212480c9000c011100c4014140071299500e44c2c4514010640002c071080d1551118604005503801100004038001522026240c050414045a101003480700865200030302c141c001504403c590340c3c5031200b405800344a54424500b00c3c2c0c6030080f0f10b2400080211210042e40001b09010341401d1200b40c60300500300500040414120030704645420020180004005a10000004034150030503101400134202400640e540d400200da0742e40c0d69010300c0c0c00f41511403072847c11182410300c0b01490340b10351002d00f5044210100580042628142c2280c090543c00a455210003222450728045c103101c43d41d115100010010300b07114541c1c4c80c1c0300d40c40e040796041c84002c02010010038000310f4408122000340041440310784d00d1a00c101064006a400104001d60310002e1200c4950990003509030307000c040d00d5042d82c05840c0070410420845c107510103401101c08010000302d608003500460003910301c905055183c00d55501d40d041c619 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 489358633 1250 489357383 489357389
    0x130605030a1217090307240c030207050114010503060f0402030c0616050c150f031f081b0d030f03020a09050a080705040f02040501021c0e0301020706020424051c06050307 75
    0x18107003000103611082d40100c00c507a45040c4403e002c1d2201e20704800001d83d03a04c10820f010f4100c0c4900c03c0c01c010b8000da4510110040001a60240002102140041c0103500075000840751942054858800e1084200c43c03179040b02e000400610380e81d04c1d0303060114407040c809041681c25003d0300313541110b26154000200342180d212450320380340362650309040e42440404980a88244281c0c4016045a1201d0b400da41d402171442811079580c0c0c80d2215140c002c1565124280c14680481200048100c1d002c14400c424403681c00340540b0f107100341d03c1041040b0300303006401400725410440d50a982c512036230141004c03483c5818403100c4030b0f4540000440c00441c50340051440c0e44000703018042030a00b80a1384200d00d40300c00080d8105030030480042e4445019000d981c100d01e4411510705205c07803080724018031001c3d019000310355445c0e01e810060080d5220340181c3c8806025030700480043c0d41181c1808010760300aa503658104200403e004000da00701c50060780c00c541d02c80b80045a0390398140840401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 489359883 1250 489358633 489358643
    0x304050c010c060b210d08060a05010e130f02190f0807080a020912061902030f180a15050115080403020a0b0c04091a10020a0b1303172e05060702130605030a 69
    0x101840301c00b03045160012248001041050b12010706c008c685901d2030250540d01c1c2420072a9080401001007801d800c0005c00210040e030034400000d007074510a500038480d800d07a00306c0400303225a00c48410b40f03141ca5501c100b5000140703100002034841d4401d0301040e03000106004054034090001e400950400e07101b0310104130303a4100000f4016440d5162506d03404100c10700c60150300303500d00741c2c20710600d4600040980d030300d44014080703c00300701c1000d01c89040c1140d40000105d1000b074114a0540003005c09004040003c1d000a4480881c680a1108c044c880d03030f8198010006502d49907620840c0c1c02000d00207104070001444007150114003805420305044440312120206081e410400088041d44880301d800c1d0340001008102180c002011300340d00001d5503116092280e81d924007213808004008042005010700401d0090901807081102315402032400308008840100344180381d0100c02c2d1080f1580624100007807001801c000c0348400070007010301e4001803803a0395400800d081104030710044130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 489361133 1250 489359883 489359929
    0xd06060f0306030203070e090a0803090c01020c01140d1113090519060312270b070201021c021009050a0209130b0f0f150f150418020304050c010c060b 66
    0x2154080005144602946000c1c07010a1440d00402c6d200d0380280520f01100c1c02c01d40001e00e140800304580740e800c41d4031161107652454080c1e0110745900104040500600404561f0901503103d010705042c040d00c9010301d2071030702511802c0e4400502d00069000c00c0c095044c4172100e05043c019070707804c0040c403038240045014070b06103194049119120a0401420740b0b040010300204800f04030040708400e450904440821040c00c4030303900c4600c0030b9148442c4100502c4049903100549024007441c0d4070030703000c071183d0240100a90411825264080006074002004a10481c40c0c6412030b101c45c500645c15614510340c0ca402145246500304c0ea050300e08562510281c04210110b543c650380042111b0407480141000d00c400c02c03c00001810340e0721618400c0b801c01c041d07680c9000244545c4240104540380d200718280101000350414072039150b0f0020305641100142200e4000c4900c203640c010094901c1c510004c0055603034405809003500c8460791410352148030340b50520044154a10308003040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 489362383 1250 489361133 489361139
    0x30f0e18071205100e09011b080705090607060605011704030e01050f120126030403020d14191101120b030304050909030d0204030614090c0a0b030c0c01110309010b1f030f0b060d06 79
    0x17480002c014201401c4d030703850040e40410002c0750134441c00141040e840c1100700ca032030f4520b08880e24021080b045a02900026110080010b258400130450b40b01ba02c0d40d0100c1500045400c08031030040340c018005c10f000b122800d1142d84100c0080c031803200103500310390602007c61301c0303410001c40c26080040d504441030074101100804410032011444160004c1d0f2034641141e0214028101e22800105900015600f442c1210703003d20a03075096550000c000c00d08003d01c0e041c04441511500c0c540307804500c861158140c00c403481e008884907604054011850103181c0390074403000040081240500d800280411680c1145500060000f10b0184101007080c070721040c140020350101810520440d44428880c0c1555110401c29100b02d5408400c1151a43c0d103020507840c0f188920a010562035180c5030316400f02c070340c0240c05140101c401600821401c0c44a10074400c003081e02c070120505880016a50854241c03182c0c01642c0544072114001c1043d008800100719260480b41ea40e0030a1034070303071500b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 489363633 1250 489362383 489362399
    0x602041502070f030309061d04050405010506040605040902240417030c1203090d0c06021303032d0203030f071b030305150a050a05010305041b0e04030f0e1807120510 73
    0x1410161840c0c43c07807009058699540030309141094801d12041c0015042c0c88100000c01e042d20a40e001c0020f807041c0100d1070f003854118000c0004803006071080c0c0c98400082a00e042078400c0b07084031a4098500030f00a40d009050400c0f079080c601000384040c1c0104400b144d03ca20b0303050810486c1000f071005589500c100b0b14024109580400f000c40490420320030820310020006d00200c0c0c00640d4249050f8201290820030081d1260004450390246620701c000101a4000c0e084620003442030500919000707602d0303902105040d585081001a4024000b20701c0051010380300580005140c282420100c1c0c01ea20445548025103400740c020a50702c030100681140c5460700c201c9020340864031304034400d080c080010902e1201d03008090402d0b40c4c8000003420032002d99905003440100280c101c0ca4144d40b80e8413144400c40031642203000515079000c12050501480c1c0400c13007048010148900d401100900d02c0c04100d00034413020404c0202501c001b0348020900c41e4038040e20301e405100c8625820000c071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 489364883 1250 489363633 489363643
    0x6080718050a0212130c0f18060902120103141f0212070e131a060c16080a0b06060c0c040e10060b0705030a05370f030e06060402160602041502 63
    0x110099004100b2180c207180207101d0300e40d0001c560114485c0100c030310304081400144503003290303450010303001d0301081041556003610142c030303c2c802007841120345515400c02a40141100c04101d60b0500c80180005a2400441640350485604549102c985c1c1c10b0001b80c00304c1c89081000030a640001c80080240c0c00d44040c031340c801132a0500348080f01030740300403800b840d1285240807841c030743d00c0504008180040c0006c000c02e510052900b6120025a0307803468403201c1b1255500743c801500f07207001a0900c00803034030095070307a040b051400e403580e51032091041550102141c01250701032080f20306260380d95445018000c1c650100181203250420b2949421185c1d19001041c044c24140480c03070004000008132a1002d00928145031121944c21448021010302d102c1d1a103459a003850006c65656a07000d04044c00e9801d90b10354518880800042d0111a07440b19258400c1c0c10850000b105410190000c0c0300c01d04000b030800b02d1203910340e00c80c0400c07a005a00680c0803070803014281c900480c0c2c1045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 489366133 1250 489364883 489364891
    0x905030303090a020108090a060603140114010b0d020a0306081509010b030a2f0d0602071b0510141b01050103050715080a15150f022a010509040608071805 68
    0x2009514604014992982e5003102003030090411582000194025600f0310103c0101503101c84180300013604d901c1c1c148440510217440114a601e45001c1c2c0207804000181c40c1e0407248000c071100d03e808900d007881c5001c1e520601e50101855194074000500c0d00c002c00121003d64160a42584641440e000361800d40344485440d03407190f80510b90880c007149000010401824400400580c103120007040600001c01a204c41584828203103020001e0054039001000c0745403203001244800c0b0904c030130200d140100c4d4042ca98000c5c40380c2805031005030048842c200c060f80c0031f100d6141044c0206050a100c035031104000c410a0f51210010420840d080042c0000303132022101c1040e039400e403004001d12503039005214061b056151750740c11324800ca50304810070103410f48011200d07100d40b840340050800244000d5504c014412410418540e184154a00080080f00d544480003005590011551a0000c030841644a030ba42c90000031143c204004000c0108010640d0301246003410b1413030b40407103034010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 489367383 1250 489366133 489366139
    0x201270e0f180c060d15031707050c0102061006030e010f150303090518040f060902030a0609030e090106020607050c030c251a0a08190f0501050f010c260d090f02010905 74
    0x403c030582d0350303415059601e08003000000081000d61548a90600203113540003a01d10303800007064801c0162014018450760740504100c3e9010140d0000490307441400b200d040c4075038103c5040c01e01405109810820030800b410740081150306500c0300174000c54000c60041c00b08081d60f8203040003016000911b0100a04080b01c41500e454805000e9020103103008000428059894104000704000707a44425841d54001e011200034903da490a03000420407101d040c1c0109280450034101440e02c0106a4141d07034441e40a0202c1d51a58641982c5a411a1140b035285000034826611402420031040408030002940d00d68200c082d0500d203a4103000395044850030340e40c03040090b400d07a1040320444441820b0342c0b611b4201961000c03c420a040451041940d001d41050005012107099030007041c107130380d8120345445e107004004005590301c9035000720040c0700f45881034030741400c458070400e8110314061101c4841c1c50586450006400c80d042400d00711072030f49403014a0019940e014501d20003810f070907 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 489368633 1250 489367383 489367393
    0xe0118050609062806080415051306020c0c060f0a030e0f2a04050a09050c030a020a0e2806061d06190527090601030204030201270e0f18 60
    0x10300208081d01c60051840d8000c1e810240c280484d82544511568808404807940b2041625601c004194000945007583c202c80c000c0242180d103da05d101c0c1a002e880704803100030084209030354000c0a074121040d01849070080ca03130601000e40358200103003118080c0c1c000d00da80e95122541d02400320340c0d480303200c1c5003280e0100403c400103c0c40011800000032241070326a00c107044590803a502d808082070b02c01d40003030401e420301080702078582014280134440e03000d407525061034009050b500c0c2c1e84040701940c0659007020401405242005064000c420b40b1884840054020643c00d01c0309a060882000302c1d98403101003004545c00301115900005040454151041b607800044190288041c1240105c14003008081c13441d00a004440c41c50440c1900c14401e01204c1c6480e8520355401c0148a0141d0307030040001c1c040d980702c2d1080310b05496058580317540d802800c0500004100c00458181200c0003032140c0030038910004044184102402c02c20b600662402d28007010b0401200c20361640244d000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 489369883 1250 489368633 489368641
    0xc0503180a02030a0303050901020f0d0c030e030a201005130c080312150d2013050c1219090b01080d0804050607030e0a0f0b061509060922060e011805 66
    0x2004c00d000c9182c0d0342601c0c0200c6c1c15204c07440c1c201e009120341d0701034040c0c26100141c0d01c00d082002c0c4d00010450116501c08211000c01c200e0040d44034443d00380200c000440410300c05a09101c40c6410fa105e06007040e00300d604410401c1510740881c3c0c0103427107100949180303d51003170810111894002c080c00306103000d1418522903600f1002540d801511600054824400300140c6417102e84850041c55046a0078040d060042c100d40d0280300724440d041405103500c41716001d03032800c050144c1800f5000c1d09548514090405082d0003038108041c1800c000141e06100351494280b0a0050305161402900d80c2c1009525000c0a04d29107500c000300c000c00d2000781c0c4100300109101003401580134a42c0e080100e00c102d50804614200360100d82c004000f0800b0002d81d1050108840d07019124a0f01030324840940d14410941c0212030103129080b075400842004183c480d030810365015501401c1c1c035000780c2101100740100c0405d0700c4036030700410040106000104040120021910390880c9406020070031410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 489371133 1250 489369883 489369889
    0x318030a08060d050a17040612110a0c02031f061d040c05041503051212010b0705060412030b03030a020a02031e060c0f19030902040b09070c14010b040c0503180a02 72
    0xc01880e451140c00d80442d0042408010b1003820050740e4851b00c00000c601d0109860aa250414050040040e0300700c48107110804940c4920000c42c146180c0c07050070510003001c21141390800c02030403030f094025894802c07454151031420010301352030320401240103814607841d1101c1c0300f40888140000c5c07800e0010b01001c0f641c2811047d050310026280880ea8071038032040704001a50580c401426071144803407030345507480c00c20f01520030300c1500071100f8010b99840920181074003e440c405000c6401c028041400548407190611102c0901e0030085014401400002d0858002180c0440507800c00c0520008501d010b0183d0f4946030224144120b0209810104036603610b0010f0000071401400160100ea40070500c040c0e0f1000040404040742c0f280002c01c0003405400c00460490055081c408428823500d40305899a01c50102992150030240881e1a4440501c01110403c11155030340c900000007910740d070044c05005400e0380c03034240d0740e07040c40d031400070044004011301c0c4140e420061108005035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 489372383 1250 489371133 489371147
    0x10060905040e031e071217041101091502010203040c050307052107150806150f04030f0f0506071110050f070f120f020a18141504053006010609060309050c150318030a 73
    0x275001010038800021040040e03940c40d0980d04901c02c0c0941c154880c1c01615415001140300390305c604102d480850f03a0310b040c99034030303807150040f1a4404880710708000103020794100c11512158840c1250100340da2902c4814081701450000e01c00506508104240750910740a140c0c0e5940c503004001d8a023110503052200720f4065408010160015090359034103000c65003c1007090260080b00351841804c050b034001c1c0400c2c1c06c11000c0041d50261040181c2409881e00c12640305401381d41818460356100709044541d200d00107030030024000305012074400024540314a9441da4980280185d403015510400781400b00880544c5148036000101845a003007041d9050507551800c3c1c0700940d81d0003140b08940d400380560741002d50000210065401d41184242145040c503180c0c0790602c07014a41c015a072603c4940900171a40442c1c4282c7c410000544660301006519000e1004d0302c240064400005000711800c1d0140b056014001c01804883c180302e194281d07030207454100031898250409401b44c010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 489373633 1250 489372383 489372391
    0x6030d1b020402041e080d020d120b06120115110c03120702180f0403121814120f040302010306050a0303020a060228030c0810060905040e031e071217 66
    0x24520034541800c54850341c054401800d01000c00750148850201c0003048408244200d01e804d1007003481210000303001091024480c1c0d510b0755000e008115130807001d405030103081206074101c1c10030004040344146907410540a0701550440c4125000d030310400402d030000c1c801110201303400c041d020b64022740d80041c010f002c41d005000c2440e1100240d000081261401803c005c85e1003c0348010010902e10284606200d43d1081e00e600c0301e40740c10200c9042c103d03503803c0070082c031441005041d100407494003031082d00990008070485240f0009036484107010b8000d00c0c08001c2c9180c000c1802e004540e01400382c1c1e4054a02541d80380a103d185440c000c4d130318844042c0180420b6800141a0044107140c00454400c0500b5a80b00c07c1d220f030302c0e0800400501209040f0030014030120042100d0704803459841b000c61300d641ea104134080c0d0414003088010440541e000c46188003c10400d20240e40340c200524800200d9450342d42c5401346420482c00f2400c1020380303d0200a0240140d4030001154a941900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 489374883 1250 489373633 489373667
    0xa020715032304060f05060d020d06230411010305190f06030c0b030a0b090115080c120403080a0621030f17010b0d060e0105101116031a06030d 63
    0x1450402600141900d80e0342c0700308101c0440c0c0c40300180c240c0344000c0d07010354851001000101405c101c0e140c03c503030003620041e0740144c1400c1000c3c090b203803150b03480c01130600072900020104203c0124004024481d2442140200c0c0c100400092209032031442401c01403e0034103100d2890302035840c1410b650383c003041e01d041d940d485030520405400d82d07000e1800f956221110101e1561036050380c980070342017142d1980d10b050070071150000600f41007141074126640620000520110301e901aa56048020130070600c4507c280140340c601406007103158080c1d40261240f0304181030450410060b40e006d5001964441c40c0700c0c0780d0b5000100d03010810b03410a0742500d0b0641441c0d00040d030841e051095070314080380a58400c0004143c00280340014000e601442c0b4040100c1940c0e0700c0388000d0464240301d86a48100c24070401c0e18054010400c241041c0032a01c1a10f48d521500704030740340b1402031504150381c1e8885c46160700385100170869035590402021002080b8150302c02c0001449511500031001d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 489376133 1250 489374883 489374909
    0xf0e09010e0712240209090603010b060a030f09060606030e0f06041113020d050907080723010c0807050106260604020a290c0f06010605070b0402040b061b0a060c02030a0207 76
    0x18030900b02c1010705404d042c104405035181e00701c402c55020750044001240314410880c00310b046851305101d2400e5650380541480d040c0b080250050b001010072600040350300303889030211000903031640301e1880a04500d4900081d0007a40300d0300c1c136192000e101e440705c105a0189041c0000706443c000340000b102d401b152042120442d80c0300d240040d000d03c0f40c0190000d4203007020300040c500c01003003480c1501c1c902000c49144558a00c421039038820003404221780080d071079101c0c101e154496041e09448900a034401442d080c1d0596405d401c513490350380412442c0740140c1c1ca040406c0c030022640e5448007110b600a19240c1410340001d6440c1a241c810b5003a805d91011681000240702a28552050348074081c04d600d5110108000d03458280c1d0361180c1880740564800810a00d0103007050700d6185411400d4802c5ca80d0300c03642800010a80044140e80c484030074000311484c021810780c10350341440342e50080c200c10002c40c130b000c10a951116002c001075420500004803d0b070360025611049411500c0d40300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 489377383 1250 489376133 489376169
    0x3040f02010c0206070b0429061215100f0905061806030f0706080603070f060207170102070206070809090109020405010e092508010312050717031e010f0e09010e07 72
    0x282e054107541e5002500001c000c500a030a0102214030b1500c1039008401441d05240d00094007201c02c4000c0e1100300d48050500041a000d0070010244003003d9146011074540101c007001e25912410100c902c58058002e503417042c4402841d25420f00300030b0124001c00c0c0054204000040c25440d12480f034142c2c1000d40b60009559a40c040040030011203c10069841c1c81e5104e64000b001c482013214070501030302c520380300024010f881e6105a011248540c0c0034041e0142083c00365907143d50303043ca00d4000e6640a1049001598940005081c000d02c00c101032580d51b80d1a40a100303050744140c0c88100150310511080101780d810207800c540044044480d403095503101504003101d00c40c0c00d210300c003001d0180314000074820f80243c81a8141c80c007848400c60742a046d1403040b5000d228025004066107480b82000310f2204624003e981c205401d407000f48840b540910039a100d2040036071200106e561401400c009528102c18420b0300301c08054024402c0c10b25543c0c0e0f580e41c540341c5211310480840c1244035a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 489378633 1250 489377383 489377387
    0x50118210b0a09031b11060a022103010602010b10140f0d020f03040201092301260901060f0602060c12101805060915090f070315030804060e011403040f0201 69
    0x1040440350300c24003120042c102120030b40001e00541c1c1049020800b25442092018070414080d4680c99116200b40d040410304020701002e600a03403c280305501c6061301d00f080845180e0750304030703012030001f2001d92a1f40c54264000d00350783c40f0f080705a0240d071092941032002c030b81c00010405d640c203094036282d564401d048000074030340c8150021402d1041c030100707020710302000500082d80251f000b684c0d41030219803101016021824000795000c18441884580c90b80c035402000070743c02841c2610407140050000c0d00f002d08403907404651081c156596401d003440303640c00700900b580290010307100401c450701c2c00c611071040031f1064000030f2501d01c81c0000015000c0240c40c9101020304244400012003401c0b50840390007514094035118815840d650008401d4161107500c4406460300400c2c40c0c006845205482d81c2030a805800403003055156540d0036a0380400b240b081000b181300d0800c0f55582e501e03100c0000c11602500d48154104500400d25000114464050740c2e00550000b1034452515524801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 489379883 1250 489378633 489378689
    0x110d0302090609030a082107020304140d140a03111f0b06130902190815010f0e03070305071805010501090608060301090b16080c09030a030e0d0803010816050118 71
    0x4440c0e00d0710034040c1e094200010000a4601c81f00c0c26200407860b00a606084400f13110211b49050040c0e0090100f0042e0030f2002c030019240c2c04025001110614058485800441030b60500a1080d40840000c008141e4804514183c41c80d89d54081e14101c140d402d04400070001041c41c03046020784560000d80d80740d684208840407264800c00149850f95911608006500700100c2076005980550080c0c550314020100240700e03c1807800c11121150400006548400c081140d01c4100814000440720340d840800c90800079602440007001014680700c5441d0b444a0900d020384002c9051400400c41660802c3d070000984000e42000e145603520304010900508078064040c1c505014901400344650102028988807080c0d9998983c00b81c0c1c501010701c1144c890225940c1d0580e003e001c500c0d01107031040c9401d00101000404d030541e0884d082d1180d01c0140c10a802c903812315040038602043d40c0c0501c48031a0b005281c00c0c03c003544035500c02031292284171458850b80c046085e0410000c81300b01d1451b50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 489381133 1250 489379883 489379897
    0x1b010203280e030318010606030b010c0b1003051f0b0d050601030f080913020910032d060503120415080f0408090609030f06060312070f0f1704081c110d03020906 71
    0x703d0b916442d2200349a05802c3c40300e01014065403030400e001c162181300c1c1c0980c800722201038640c1c8100740c6280d40c0d0303540c00d0440103147c0c0e58454491000800010018010003a85449820a0b00300c00c03000400c034003003110301ca031010502c5200400c544a000400100d821411203030020801442220715051890b564814400b2856200d044210138900d501e00e90340c00380420351420789001c07042001d280010b4045400c12203a40e02c11026140317202c4000812513045070311104410b18086902595940401d151400200c044d0381c0c0000d0100b018885c4a03d508004000905280713000541e9050245500440c1140904050f000801c0045d410f00750340c41d0481240d2003108054200c0e511030103a40c03299520f503802625243d203e40980c0998101591440c826203c0391034000c00725001b01c2d41d4a42d580030040e0072000040300c0c400080e030012894240c29030081d100070003000000e880c03012032818255000b6141040130200344800c150200d1450540007079003a5080c10581001699000041c0019440e409152 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 489382383 1250 489381133 489381161
    0x302031903091a0304061b1d06120c0301030203120f03060126100905060f0609040203060103090f1a0f0408030604150510020708010513020303030a0507090513021b01020328 76
    0x10f500c00e00a002c850700441c4641c0c0509010086010802d0044602d0020406000005001500c946001c0a02c6010a900014005002d1450b01020400da02d421900444840300c23403207070120040040d41418401d074007c80c6c01d010301007460302c01014481002808042c05450411121490044840d02e0314509000a6000400c07014010301d03000300344101080e07090150a2500741030002081090810400c41028418003c101078103220503a001d02009410041c880c0341007645582c40c960100380100c0300103032040d01813429409284000d200d00c040034207002e003603844d12403400010400483c10b80000d49812120841340400d4084074041800d8150740e8a0300200d1f441004c1d00c14003006640c000a050049894400080c80b4a0341c4030042d80b01070001109010750150010030004046101e01e5111a034011b00604140c030300d554072900428814a990b48121403007070350002c3c0211070399124014000040400b10025480c40c644451445e00f00007004840d0710340c0b03003005148111400c106801404030b1605078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 489383633 1250 489382383 489382409
    0x50706020d06091d070501020106080706031a040c020a140d1704020406170a05061803032a04090b03060f060a0513020c011a10080f0105010f180f0f0807030203190309 73
    0xf1201800d400c0313004001095603c40c0503000125540180507680172203103403101928205180c0f2000b81c0191403040e40581c1440140d100d011600d41d543d1180e5131580da0f655008000d110b001c0d00d48509a50140380f01a41c155004180048606600a5043c00d0359840c002c0e40c61005e482d140302003405403a10b50001000c52000445e8207550780800036001e640540580111445074a03100107880400d4180030745003440307410070000270b5080c4550300408020b4401c0442070040141c00107201d003102e6001034001c144102c0c0c6a140d500c50f0ba160400c02d0380d0f0002c011400381c0540303060100014030840c4aa1003900c4c01002c0780284070407480e0150741510b50704140b85009114020707101c80081d141c030302d190011521404680c049218018401c46110307101e0011408045400d074200701c0150341c005407401040c0100241a00461401007284062400400c00c0ca98401c554604009005a68210745d40000341300d80d005c804100090f0350005084e51003440d02c0550340c0d198419608044070b8068003038000001e5400c003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 489384883 1250 489383633 489383651
    0x312020423030f15091902090f0402121006060905090601120b041503060b0405090d090303030b0a0b27190b0f120103080a081305151801060b0c0f060403050706020d0609 74
    0x20105541c0d100f90f4120342910505c6c40310641821243c0c1d42e20340040d40004200000030703000e01c0c880d0005500180000d141c44003d50241700f255140410a01d10f043c18291540d8007001000d4000c1804c0d400307810212000d050034505100005d140ba8003048101d5a100d0300d070520101e00d512241d0003076000d01054044211300d15100e081c2031003e003141d9582e07c0d001d10314040009e0312485c00440c240c00008580e82c0c4103610285141c40c114041d0003c0040e596202181001c00540311002c80300030100c0c0c3c000194108442d100111282015188031810300f03008005a1848200003c4e0188550007a241050b40041e2900441c04100100d4081c03081594400d0389203100101c1030100510240c04411455503601103140c1c1c4840512144021045006041c3c1d840440540761090307400040d5130303010840c0d90342c036480071244400c1d0b60f080d16250f03800404520030001d00c2019194041c0310204183c10ad0034020100c5040c1554010018440c4000141140383c0c0400c80c0710300208950000380082c14116006d101c40b02c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 489386133 1250 489384883 489384913
    0x2b0303020f0c011e020421050718090204050702060c07060f020403060c02100b0f0f100e030129030708030f030406060503030f04090f1b0509010c0215070312020423030f 74
    0x74808810110448814140d10804a910b00031035058130700c0001813070b2000c3d0703075080c0451150390007e00c2207607103008030040032038081e408800301d8091011104002ca180e01e0b16005000c115600913159004642100c0c0c10440d188001c40c00302c0d007000d0f0f0302c85800289a000d4881031002070103103420080416040080400000d507000a01c00e03c0728100c40700c20002e81c0c3c3c0030800c00080306a1101056049910804041c1862030b0280c0b002c6c0308410136003054984a14030400007401c6440700e41c0075074402e8917814200f0507251050005c103803181400354010401d00b418091415500d0040d18003110301d101000000500b00140782d0481002494040c4c2126110b06816400c80c60310740081c050080101c0c6004d0034408140d0300c41c05041041d0250410548209142c207038111682c0d03118995641c14484408001001030300c81c410100c01a103080441c40ea1906100d141c010401095081c403240c03042c0c0140800e10000c001c02a07503488901420bd000c0c0032203140c04010a0402d1035141100c034680c0a4020071641c054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 489387383 1250 489386133 489386141
    0x60c0702030f0f030a080c0301060e0105090d1b080d080f1b0706091104050a02090d02010e210102040501080c040f050603130813050a1d06041808030112060b2b0303020f0c01 76
    0x8442c80d100c031a10b03540c607c2401c40a601003441544001408403540d986c055000f600109510746010780005040541c94507000c10740041d2480581d40265420300400108101b405080740905091410351220f05101c0b400a20040000c0d10000b003030b40301250b481840000d90022101d0700fa51040c002e2203180c1942c10140301c40b000901116010303504100002e40208400e2007166001c00c80181079510543d01070300115404965402529001a400000c0c6a1200e440c4040c0031000d028660025a48030704101c0010700c100f4014100b10303140601400107204403800e107070310503050b1081605d066490395640e0000344846001c0c2003028111013800035130a03000203400c5582c1816518152800d89a8a540e850088074400b20b00040b080011f070994007203011071429401c000c02c0444c00c411540380d0761040f1384500240d640203038400480300c1c04c81070030101040064002c20000074801c540c0009440a80c0603460818030015a00b00c1c040d9403d450607800300f5020b98169101d103010722038403d4461550000c014020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 489388489 1106 489387383 489387397
    0x1e0402040902071b060c0c1a071202010b030c0907020709240620060403090e0402010908010c050405010314010b09150c16090b03070503060c0702030f0f03 68
    0xd5181030000e0300d42c05004050009200041d14a03541c071300705455001c0d5062066070f400c0c000115140084500c00c035150035802c121150b46606400000d845800c0009000c6a180e0107112a00c0b0350542c0031030510b03075040d002c0b101240b6480c1c0411038902d400310b51800040e80051401e0243d294907410882400000b0b00e848122501565007902010000d0b0700220300148190310103060032000691940400b4a1610181c5554106924000c0200c8107500a0321048801c2c40e02040859100325400e900401810008000c020030003413000b01103912510905000a0411182d1540d42d40b0003400315040311320000703100703107804424001d02801c1400c20f4410031500ca000e2041d09075049003480042403020b0000c00e02c80c005420810300f001110042c0000324002e9004100a001c991000100320703410403200306480340c03130710300c1d03440020b1a0122039014407501c0c0c020501842007104000010307081d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 489208633 489388489 := by
  have h0 := BRFrame.cov_init 489208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 489208633 ≤ n) (h2 : n < 489388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
