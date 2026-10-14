-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1810
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:45:46.438115+00:00
-- url     : https://prove2.me/submissions/310f4c92-1067-45ff-97ee-99e72ad12d09

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 325359712 ≤ n < 325539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 325360962 1250 325359712 325359731
    0x60e12031b0306030f1005041a06030705010f0215040f0c05060c0d0f050405040e01050a0c020706080c0a140c07090f090b18120a050702030f21091c0501020d 69
    0x10112400392071910000d00003036030120300041e10750300014012030b8180585003008818410074442c1045146018000207654900b5142000c817075604600310440000148003000069200040c01030140c40003400d01d00c4140340c1c0814102c0c6005499006500204090001e0008101d03458404500c22442440170400046e100c1c42442030310301502030414125031190300d4108049000d985031403848203861809501c3d254641e03020174292141e03210f0540b4181e40d203c0c00c021f040b07241c1e4420b001c600070403031010301666032030480001c2070000c0c06402000b4907000000c101c1d030035034010340b1800d00085000808a0b155403140b041740744c442c0014411040c07621b0400c601048103682510403601800e5001c842404030783c8492002207001070700d9101119242c170900c446400c101d00c203800500009803041e5a440c8d59800280305241c20042c681190080903440b6440508248030040090800c0e0003c280910351542c81c082c0004904440c03241c5a4642c900010105405002040d0024a0036504441c01400340007030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 325362212 1250 325360962 325360993
    0x100804051c1107050d17030a090212030d1a0a0e09010f0903051309020f120405250302010e06070507060f1202120103030e0a2103090914061318080703020102120103060e 74
    0x55594020303d400000d10500e006c000580000d16044030380780f000090070310050b0380401d80c8074440742165806644085000c030039001d8140140720b49100c0440100e0310b075201b10404183c0e020014001c4040c40f002c8640087e0354000254000381000808100a210b00001824050007035401080c14035000f0a030000045004242402207618414044c110145088002440038480c1c060262003181c1d980a140030100c8012a02d080750300c40c0700442c0c901c240d0620715510024040701d494150707081c0549820f0080030301040003c180f1780121000d509022001c02020300007102e496980030415440c2038804107214000240503a0114140c910039220701c880164602c04000c0700040600c80c1440350702c500130b03902d9502d02a1000c214002d17031007401d1000030031b0303220092170007540c0c50002829800401841003003a10f00d420f85100d800750340a02d10800074483c07210020341d00f9005480025180c0c844c0002c101c030805200754100d4402240104214a06585a00d8980d001c0c107001802040f151240005101d4002c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 325363462 1250 325362212 325362229
    0x305070308070c0c0b0901051b0c0f040e06180304121209080307020d3804120f09061b06020c070801060501030b01050915041206020d0c080105100804051c110705 71
    0x141c201341d0155500d450080166429842550000d041181c1404100c09480d012a0409000d94400001cac120f1801e42d24180104140302c16012880b0b0743c10030380d12801508010030313020741203101c0001d107040384541910014514419540544440c04082c0249000d119036150212421b4406584512400380d440038240d40ea8050520069481000d213100c00c800580c00c00380346200c014521f44030200300c04c0c03003254401405406190800040c0d84001c2007004000c07900080520900c61404e03e000c0061000100800d03c1e54103002e00c0d0103111a204002c81c42600300800c0c8440c0f2031f4230000541d03540c0910191346455034800c0c413401d0425030800c980400c0c5076019020320509503d040c1d45090a084030172003001a4125010b21118104100700008508000c00b1b00001c2c104078002d140241e81c814086005504681005c039552042201e428010301c8a5580c00d052034078189000d00c0e142c0c906031030343c0c02c081e410000036014480e0b00102d5017107001c5030700d84c0100707120b01c120052106840349503030b94005014990 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 325364712 1250 325363462 325363487
    0x305060f031e01060909050106030506060a12060c020111160c0605180105091302130618050105090f0a0e19050c0a0804080f070c0b090405060f010e01050c0c030703030507030807 78
    0x42d0040c42030200c40b148400c0350403095600d084000f190b0301d80d540c04110122081d03418181d03a182d4445a052043c07000400c8140d800004c250340803d132852800c0c0c180c10401280900041065880761110105a8400d4002c041301d144101c0d22141e6441100c40c08294804c82500103c0c0c0000702c60900081e41b07070107941074422440c40426130b0503015201e200111076a03440007596030f0344040c052003290b04e03080c46d51024045044035a85080354480c100980030b00008642c09100d03903003000c10391041c003050743c1c4041130310146c2d541680d0344030500001d440021030121068002e4000602003004019995a610302c0c0a00030b05030f081d00400450b02c807148014814451204240c0100e0103c0c40071500050350b4400521044041c85103160522020743e80d10403610015a10408190b0401b040508280c6824442c050308011300701d422101c20703007a080001e003a12411300c403124144200803814113000d180c1404201904140201a0ba862a4480c80e0182994100c642e041c4c0000e03100b5030000d450349029a0060031003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 325365962 1250 325364712 325364719
    0x1e0a09031b02120609010b090924220303021b06061804030504030c06020606120d02060402040e010b090f040309050312031f052d0105090a031502070b13030305060f 72
    0x81041c5840840c2100c0c0e0748181c02c03a004a00070079010880300080c0a0607025082080011400d000310750104a0b0030880030f0035540c0300750844100e1001011076000d801000700c20301c20440141b580c07114104007c1c00410055421000c00c00311014007056070503801082044011040303010180007446003240d980804840c1c03c0e400201c014a804204218210915800b0b846441c0c0700385429102e695101001c0240d078052400350348201c080c0045803034540c00341929108100000c100c10400b07000025a9804041c3c0003a029694450300c10356128400c1d082242203800c00f034808070641c00c20144007000f803202110203070300040042030003280c24940420b828090300e100440e0b8078215128803011070000742c0c460780e0b01802c0c141e00460025083e1650344842c01d040005130081c07107440342e2442c0c1102114014411043c1041410411300b446942ca002c0a242600d4100700b03036204081140d0300c19030080c45100e40c003030305a078241001c1001001c0300b9110128140c1c4070360380a0100c0e46900c0140001407807100d007801d61 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 325367212 1250 325365962 325365977
    0x90906031509050115060806030706030e0c010806011101060605091e01020d080a09020406150f020309030d0e190e1509010e0a0203040218070215150d030c06090b1e0a0903 75
    0xc000707800e40c100c0300c0042d000d44000502071400111182d0841c9080d13100901207804042005400d00e018004803005003013500301448800128080f843d1148602c002c0301307040c0407505020804a902c030320784000c81001c004000700082c544645018003a40c100b00711461040503a00743c588030a8900d00c01452202c4010b8006042c540700d100c409444061004141e40b01c426960181c0a000d03958500980b002441290220700e0704200744080248000d82d00500380c1c00395441040b501c060764a000903100b8000c0c2c2146400710086543c440010412944582d01503100c01014801090305001040b14034010508520039481c1c4010780418011445030034400c010031b9050040000d0030028141e0001c42c0d1083c402090440000b180d140419407a11065810b000140d01c030700c0c4214500340c24400071036004092800c030800e1b24018000016456540702c0c038000c00308852001103a04100141d0840302109601040305201d47c50407060303070220034601c01d21200850f00e2400c04376400e0a120301c0b0b200d40341c0c1d4040e0750718071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 325368462 1250 325367212 325367243
    0x8010f180b04120509030d0c03030c08160c2a06120e07031515030b06040c020c0303030c07080f0a050d050703091110110a0b060a051903110d050312060109090603 71
    0x1081aa03074180f5405200d82000a021140d0f414401201c40107030700d8440209080a80c1001012200007140c08818000460f044c0100d5181c21621006054200c0ca00030303d0755416480e05041444a03000b030950740030b8031180c0141c40c40c60101d40c400b05941040da9003c20303601e18596440c003600c10484440c0101d4005c20014008651401c1d9030700c14007001400c1c0403c0109a81c508240c0301c0c0969401554850300e05030a01c01c2e03900d040d01442d110600c1b40c0c4010242c04079041c000076100d1002070b05031140004006002000c011101341a900e081c1c40300d13180c072525044d43d920003400c1940508c5c0024400d601d031400050005009101e0043c0140d0445401c122540b100340c1408000c0d0301c001781d042d051001003c0c0045042c1c2d009c00c94180842e11510151505040007824402d801c0c545410203481203090f01d54405100480e038681108498000c82005001928440404d5008407403a002910701d020000d4200701c0184a8000a4041c000aa17244e00c6601d6440355014216036981c04010490406511040d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 325369712 1250 325368462 325368473
    0x106030c0509071805210a050c090a020906040b091f0203120a05010b1c02040b04030813050907080f1015050c0c01030e0d0e0316031a060108191a0301020408010f180b04 74
    0x1b41491070b900c8890540910414924a280804041045a882d4481c0c11070580e54101404059001103c290003541042d182500017105400350780103c00ba000c10124640c0c01540e2070701c010050a101d0060030301100c2041c40c5009407290310010043c00005005004582c8055451054a049400d443c40725414100890202d201e02d543c0400302d0000c2c6a000d02000c18076468040081000310310500200342d641029065000c1c41d04081d038041480f42110800700030380c04c2e400104290388110781e0709d402c0f45550344960200c04c80072015000407111482c8000340700c40c0c59402000800805180c1d00c00c031022002c003d401103065854524174000c5a070000001506414018076506e4440480141a548690758856101c2c1350101c240d40140d030000b1120b0f50308000115100c51035034001c6002e01c0d0010551070301c080807101e10b10364a441404515910b0400040310310201d040200c00420050081d560385980b0000c090207001400b4084000c40d1800a8594030305500801000099900040800e41380d640c0e80c890 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 325370962 1250 325369712 325369729
    0x6011a071208190509030d15030b0613061d0f0a11090111030903010f09030809031813090b04050c1e09071116120b070e03060402090601020109050106030c0509071805 73
    0x820b0100c1c264011114a250f0340f50141900c2200c8140080d502e4429201e80001a00e4001c01c00030706400c90050700780003046040260984c08001540d1000e0810352441030350004000a500200300002494000d149010000ca441c500640c00e08903136030201e03110802003004540746410b01c0c400308042005035641c0c0d035010700c0e4081c5500d4040000d49040511003004070b800d4454070040d1007406566018603108040d00000391a4020b2480401103003807181301803520b040441c010b01d0180c07140410060103074100e101a0000d00f182039100d0803400050800340b030520354452004845600c104160031100150b010480c0c229000c490004003080400d495440c420744259105060400c0c09005900824101c01c0c00d8202042c0181444c0a004110603605e0401b03160790500501107100300104000e040c440c81d6400070b1410b4015030100c44c502842e844840040c0c0c0146004040100103500348040001030083e007100640c2250010344001c40245d40e00c80c000c032103100707404410b11284500703040144614100040c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 325372212 1250 325370962 325370971
    0xc0606091a120a11010e0405131a0f07390209060409080702060307030e0d0504301104021c1506050a0507060b0a05040f1509020c0705190b0a0206011a071208 69
    0x10b1106d07038918400040740a03110200c41a82100a9560350300c0100917160300030004945c070b0002a11482d003801c060600c413118014050008003d051000c10100a03110341042c410144d041102c80120380400c1410141d2010743d42040c2c2c0710380b54100004005040c02d000350240c1590101000d4580000c035420040650009400d00301003555400100220b410b007000300204d609043d850f5640c69500d80f003082e01c007166440c0c0c60604454040b61020070204a0f2620140c0030320fa00061a100100443c0045002801884085002d1450000c001c01c1c1c0071b46141d1140e00900c0d082ca10055003582c4400e420b07540d034480d1124480000f102040b0341e801061003a4459581150024001c4c040d0381e56071000070707050b00c18003450710b034115038bc9000484051120b90f00742c0c1d00501280350154140104400160b40702c400c1441000e01841c07820740090320f07801d04082008041c0048c82c007510740315085508003d503288002d0144080600724903541e003103110f0050013038602c0681e00c014a82c0c0300c0c03c400002101c0c600300152 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 325373462 1250 325372212 325372217
    0x191107290c010603171201091a060705012a1107030f0b040c1a0904050702070305030d0b011206030b04030f0816030905010f09051c0503010b030708070c0606091a120a1101 75
    0x18000b0001605c02080350034410b5100300c1391512140c41d100040800403041c1e016204051411440454503050355036044003548048614540380c00080c28113501601d03458031001441a15200c104221040701c0c1d60166880440e5a20181c40d04201c800b00313940c60703806000c050100d40c411001d0300e0004a544440d29801441481d4829010781e48400340c042144c18200300d03659220010650b103200d81054450541d00c4030312440180607461654807155102d2003207410100c05241c44114200280e40650380850903281008020400300d40e5034100180300f010705030340c00c60028007940803500f0b000740320303064140c09280c0c0e441c40c00d5030301c8a50003426402007960f6002252955202c1401400c013032001d104080300c0354051000b8005581c058210400c60741c020310310503400d1050510042c464486103106480c3d010750b1300d061a1400783c840007015540ca05d20541c0091030346050040c0070580801e19081a4150f0755040daa0140114001081002240020303102c008c03d40e204407020004510b9401d16540303895010b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 325374712 1250 325373462 325373471
    0x1b0602090a0803070b010317120f06010c0c080a03020114041109042406080c040c050301051504030c0b0a0e060901050703080a1107060504110301090f03080a02191107290c01 76
    0x8600b45030554100f034409075084029440104144a020a1100d446c804a985100d1074400b4001c09030102c1d000203000707803440704054000204641d000350b50740b5090f0764101d04004070640e40d0740c1d403155a079680200c1c110015424421003a80340803103015054001e5901c00490300480c10b002e4140008643d0013801900c0182c41e801c0400c8940c0103100e29008900c000c20750200b03c0300d040c4a4500d10b8170104980071401107140c801c08403800c0350302c5000c0c0ca054901c201c5940c6c1741010400c0795903103d03000ea5000600b4036a03c500d00000e6500c0a54001c0122401c00d440300d4902c540c048013080a94040d1803905070200700d04015420009102c1e08400758422070010000070014821407400409400061040310001d503103009101c10301c45007001600c1c142d1400c0f0b00900c10401503076600c548a07202c458005043c00000c1011403000b00703003a01a141005a01c03244180341020b014001802c101e016100700c4083e0064001c08122150700503620031154502c50400750a0301c00c682c00c00c00443e40015001040f0355a103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 325375962 1250 325374712 325374719
    0x150705031b0a021f090308070206070203010c050a030e0703030f0e010c05030d0606080112020303040b0c03090303130303180803042c09070e0f040b0606030a1401241b0602090a 77
    0x40c1951528410440741c0105100c082c14414000110000440c07042070108028075520515804050b00701075a42c000001d90707c8002920102d6510300400c1030081d459420840701d0040580e120300a0b00040c65940d4050060301f078412002500d900c0781e40800f0b000101c0c1c540c010030405005030f400303c0450300189011814600c06403100d6003503800c40000d801c0425240d0f001040707004e500030351680c0034081005007104044500d60009640b8880c5101d1704a04000110706101d000000384252a81000041c0960b40d4580c1100c007100143c030302c14001140400c81150304140340083c0c9440c0a82900d01910045107081c3c100103410180c20448100034028106011340d41d0100800048024000d0004d00004d0140908000040c810500028440002c503034524040002040e0702c00802d503000030b002c0d503105a0743e1711100900b1000e004400b904110681c2804000030786028000303450040c43d00c0d00c0b107000c4108955180100c0d45a20504031a1482c1d02c1c00c0580180892580c0e4018040301034010303c0002000d0b035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 325377212 1250 325375962 325375987
    0x803460e1c2105100302010f050d0908132117040512010621030504051c0602070f03110d020703320c0f040c08070809122b050615070503 60
    0x403290410760010b40d0301c0d00b44032030002c40c0b001c82d0401c076100880107210502d00007084035400d203070920000e8100412001040011030050044483d440d90390101401000841c1c00c12000642c82007650244108641500280300e0300b46100c85691400c043c1803120b40d00f9041d44075543c806800309628420705004100c0059255a030a0300215103986c49000071400514041030b21144174030351071400d00d04006005128000952100841e025140100d52002d1a044115180a1a049003000051a10f03100040013000d104100c515040910f01ca80d480d02e51389048401403a441c0e40e402d11008001d6882880c003840040c1c50360840040c40010884d0511100d01c02000f0f01090300b03004807041d04a6002500c503100b071410910b402c1d011101c820f8070240902580c1c024002c3c10088000d1203d0100400380010464400c814408610100d2051031a551100b580410202c072410180c00032012100007910080c80180701c60281c0762245000400b000f10522800d081c14201d94030583c4122410300040000d07010058 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 325378462 1250 325377212 325377253
    0x15120b01022406090106080402060415050912030c0d0e0f0126040f0b09060114091f080102040501030609201809010b031f080d0c020406030803460e 65
    0x1180b5050390940d050620a111500b50b06030001000c1002c071800f00005621444216030440c3d89405d1401c10200c49c3c103004981c140508010300394041480b80d01007007149400006030209502d403c00341c4000c45414502580c410b1210365041d80c002000c2c1c0c154140541c020324100303c20680b000301e0f0341e11900b1640c001c03460a0300c04035811283d011100030f606003402824050b8980c0a062000244520350410305c2d20341e0082c030003800d4030384929099400604101c6505803490424040c000313605e4010340c3c54102c3c1c1400303500700d80549400640781850000b04000d20b070191103203405420a1032070f8019492041c0701c40340c1d44900e5031070304003c50034484801c00362200191075000b841544000ca480b4103002d0010450014180146030340b164040c0418000f503500420301c00340c4001281080a40c1c03117554800f28010303010030340c0050312490011040000300c00c1640107c01d400000000187c102004407030310100b02c1c4442014066212030400c01d42410000543e11401000c003090701210015004d8040400825 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 325379712 1250 325378462 325378513
    0x30507270e0601081002071e050c0406090615140409020901051e0307120207020927030c0607020f0307080909060d020405160f0e011e17041a0115120b0102 68
    0x42d808400104004e020134450381c0078440a4035819407412400d5260b450f0034200f6000b0505d0380030b0b148070405040010801c820403029030080c00c14400d09940c0d603c8207004080c00d101b01140d4680c0048006025480f42e15042070480da01503031241014201850f100007900880c034418184907041091140c40f015442c0082c034104800b001c442e540c2c1c9071000d00200b455445000400d0b5142c010701c210001130303032080742c4203078840c140340d80c3c810103110a42c032040066801d05860172f525000004011149034408581c0f603102c5c00e9150200d900824130001c0c00d941c1c0b88110000545240402e0280070802d14020400d103410010081040b0995581900000d00315181564210119000c0740942401560020880f200c422010708014941e00d40201c000381c000c060b12000e99890851000408103e103018032120507448583c8810325542c1d14251404002c000c4440001e0b0020719000c100010310720032585030350600312076181c0e148064004801074074406400d151011030b043d4001d15030440d0207610085126002c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 325380962 1250 325379712 325379741
    0x70b0118150b0d0b040209030d0f1e0905030c030f07060810030209010b030a05010e090a0204020706090b18010f0203100302130608030d0207060b04020c0a02131b0908010e01050103050727 82
    0x11414107400000c21580c04071320290156006104000c099580440c84500848190400030310006070070030308aa0480201051880002e07034041ca210b000c540c040411001e55200341e0890358109084810580c0e11203040d0104c440c1980318880c14442a44241816504402e01007a016250703622a40080c0e8490f0090f000710042e00004000c00c0500c1030310380034082c01001c0b5195005420b003000380c40c0a40f100b401d2840a030259400048020030014141d00c0800003e400014800c0380e81454071107801014a003c500d032030150309101c241d41c3c02c402507100f1207000701d102c095540407140ca180d00744801c804455080400c141d075140000121001b09000810710480051130040c3e880c1e41d54a400c0301114020800140101e04c103000c0c080400000080f14144560115842c2d20715280c0300300300c803000e031a02c41021203d003c0e014405088494219042201f43d07a0048020b01000880c416010b080350b80920014103554000a4204558024810341d403d0007000c0d80c0207045643c424842c80310503031b00782d000440741c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 325382212 1250 325380962 325380967
    0x60316051201060806030c100207090b06040306050a020705120903070608183405101419020a03080a090b06060d1508070f05030a15050606040909111203070b0118150b 73
    0x24589000c0c8040104107c0c2120401920f00050f4002035407580c00c0d020362040203540c1d40311882c45a881c01c0980b001141e0148007030041d0301d484010f0a0107034005c4202100c4502c09d01c40c80481403500d00c001e0701c0b00c100c0003030002c00040f80b901000b1101c60401601d46406205414640c101d104402c2c0001a24107001581188103104000070072048105212220710491031544000d00c403e40d20007204d001006200c0c0350031141c032241400c0c0075219200b072003050000000403110b0034a0303ca03004602d111400d0f020780c5030022030761703182c840c55010398060345030003002c82001c1e10002d22145070030000347c81580300507a4009103261011300c80001003000f50b040719510b640205401c1050240d502c0384030380030b80401d0340602840a91a40c0b00044032400d01c2000300c05680700c40c001289074981e00103640c020812203c05000d461035500341902c0340b45500e80311034000e4804444040c500c40d40041200c52903680b0003185940e030b81ca84090070705410040b100c1554400d03214601050980030003030101010b030002e0100300343d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 325383462 1250 325382212 325382221
    0x60c0207060921060e1e120408060f15060a09180c0806121e0606121603080711040c1e0509012a02090f0901180809010305040c090518100203060603160512010608 71
    0x34541480d4122402140350100b005102052002c0354071608540c890981c8400f0340c640c4cc4549040c0007064503402c0c1c01260110720500000c2d4000107000c01c0701d80030144494918610000e1030f081c1d96460403841c0114031003030007186460800b2a88042d21a1100060781d1f503121450716030800103d510940124194400b50a00041d441c00c13120700701290359403100074a0509006010120780a106100117800f580c4007162280c24882103074118094444020001c000c11520900050003060840b81c1c18102c05481048e00c407802030082080383c10458050310b0741a0700c1e0300b00740000079207606004010041288980045801600c94005650258540025400192030503842e0a03085800a060519606403000b50070300108080340216550300c0420300e0003141e035903102d0801d8060020713194041500d05e454502000f0034540b421311005003540c444c03000d07100b00700741c4a00310710280d010903940d1592001003000810a1071281d4003120340180c18a0134130a007000b0740400c07440fa000000360b02100100307416a0420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 325384712 1250 325383462 325383523
    0x11805031608150103110d060906020f0304051b0603010b0c0a39050604030602030919061a0603010e0121081801090b0703080c091309060c0207060921060e 68
    0xb90780140020016a030703940c9940c031148920000f000c0b105001d070841c0041f200c01d0045642106040700e800a2096585640205140c0c00d1b03035104860541e2107028181801c080780f00740462200c000440105103030308590800160520607130004551003001c0c8220020300740064540207009280c3d20780d00311821180249010440d03031803008506911016009004180072035642c2e64141e0f026603422103c016100d90b0b03404855890310210101110810043c071a05100300b00042e00040302105501401344021100341080c003c0310b01083c002c0e01e8500301c440700144403490326000c4480078600003010403000a0140e07281c20340c140e8841c0341522060f8141c4600130340c07156048075425000304510700c05070b85403000c2524024032280c07001d00399140b40400001d001e11255101c0b00400f50522040c0c8080110f0b9a6518128000b000030001c2c19015000d080e10004802d401615040211003001c205244c4c114504841191a050102002c1384c0e007580e44d4401c00f010307070010001d08100c01c040c0040004c0328131703008410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 325385962 1250 325384712 325384723
    0x20405010e0303031306330314030f040b18060f030405010507050918150a0b04080105010e0915040302010207080c060f010b03070507030c020a1a0414010914011805031608 75
    0x1e80c06a4820018440f00d00d03402a140380c1c07516040000050340341d50b8030080e02108050f41c1d66126070f050b4041c860381e143c5407003014410101c8c0d20031442d0004201c00c0302c132281e81703d0007140c1a01408120521003045202501402010f01d181c114010002040308180000c0468000e00383d1407028000c040200001c0000c01d2140316040344a0f4244035080128a600003001102644e4880182801c48030200e1003d4242100400c41ea00008120010450300c4e1a0100740d2600988940d1805600348000003c050744440d4040c4c3c050b4900e0409000501d043c48490480b01901070411001c43d036003044100081504140a0420b0000140183c1380c0e6090960300e8000004040e0403100303e502040050140c0150003000f114085589410103900e5030300c1c24000244e001e412648075900020841014100e40c1e5000310003841540c226030b000002d500465401100c2c2121a8003514a2507002d201d1340e1904ca40c0505498859844a0494800c031107840b04040b03400c01030703e00012103030810441c60038426000300b0300c01d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 325387212 1250 325385962 325385987
    0x40f05030406021f05150607060b0a0b1c0b0a0519050d08070605090d1b02010504030b2e030209071202090a06020607030606140a110f06090d080a02071203050a0b0301090602040501 79
    0x2030501003828441d00ea05075424000406c580f15283c0020383d0002c2140359000003501c850004c089221072a0340d600422455401035002d5602c07004101c40b24071003604a445291450940031300516404c038204024004000341400c1c0e031941c2506008000200c550300e5000340705a940c0304010f40790b294140740c0b410000b51440940b00d64140d0304498800c0e031a6070740c0304100e01da207050f600c01d5507c400c015600058940d071203a5040901410803100400401d001001c0c1c00304007203d84420000d0510001040c0c2d20302100c1d803408025842003000c008100118802c40601c1110b0389800790062420816400041f184112030b4055005600018100052990544514030050086040c0305202961110031082c95220b41300348102803254905c14904040c3c0b0420181c51001480f90413100c481c00d010810550b10382d0f070151404001030540000400003110f500075034403101d502044045c800f000e800e00a80c00b4020003040c3d0b41d2710306e50311203e08001d0f076004d0260b1344055001d25070042c1d58500b08000100410803181 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 325388462 1250 325387212 325387273
    0x609060f140a180b180603090c06090427030311040518130c0f230f0d0201020309060406030e010c030903080a0506010c02061c0e06100e040f0503040602 67
    0x1000d2110890300125100e21400030361a009558601c20641501c0d00c424401040e524890683c0c40442c00c0c0c40814000e041600c0500e1181c00b50060304c1c0100003687c40f08560300746803604440c00005041c10150050503180200810204e8500700c4083c04041941401c4e0045070924074400ba004c051603054072803442290340a00100e440d007414900420550000203280400102d0024009000d01c80c0e126040312495900200140100e41d03101035222034081f00c3c1c068088216644003401c15000e24586075240517010140c05c2c900c41c40609000c11211244101069066000030400b848103540c0b40320040006d49a81c0d1000150301411845280c2100c10a9801800781032420341700001181c3c21841c005c0d4010309400b404203141c0e03101401215510f50484c03009420850205140740e03094400d903480708030f180406000b00440c1043c50840c907507810064900703030381c0c0c2c1180d00000c1c0403102282441c15481030140c8203610401d8010350b030f03091850340140e1044005070405418503100d5002040c1d0307008441a2b00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 325389712 1250 325388462 325388477
    0xc0f0a0b071b050d050307060605010503010e0c0901110f0d17040b1602030403120801210c05010c140703060504050f060106020c040209010e100e040b0d080702010c0f1407060906 78
    0x12001003588074640d00580000048440040080018550003000c1e11010b40b01ea40f0700f580c14504141d403a00058411074030541419030126455101d20103480c1203e040060826a1361a2b03000c0960580d44440800d50401c10001c45094584004005000040e00303907070003c5c0214001d2060041c00c031600044120134404240d800d00000c02d08800445410860410001c880b21503040000d03840c0d403003581d100902000030400050860b940000b18a0704941f00c2d4011045c00114004c00240702d940d000384014a03103031501005001d2540304103408141c4e607118403c48810700c414115024641841c50303208958503502c45080104000302030090b020307045c0f18603002340715550505802079120506410014003a95000c10300c0c85040c1e00c41c030100d611503c4080c2a9031024180c4c0e28004000386802c001c0b01d802141401d045455074189607192200c0f2a4100e01801d003040c20325801180c03134520071402655407000d24203094020440b4044401070322450140101b42d1145082c01c003602805041d403040c414450071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 325390962 1250 325389712 325389719
    0x10090c08011d0607200609031b0a03020a06020a0e0414070e03030a0504050108130b0405160b09060711010c14011e060e07180801020c031b2404050312090c0f0a 70
    0x80c2c290340050b89814940b10f150740c0410b640c516030a041c251385c100b82c403840040c04840040403006087e580380300b01b0b40d100c8045101075800e6807101c0ca4040200164000c980141c0424010b03070151100d016186440a04651140000b5090b034190300c3c5000d11442c1c8080910030840d820680301d0075442c8044e0b0203107040c20804040500705020b00c1c400c40d0b041c00110030000e603190307900340148805680c3c090004401070509081042d030b01c0c4503200345001040030008012503c50005000c1d500b0780c3c1001001c1c00d01e8100c0e6076440a0134030507a2960a41882204140c100c001459450310840403e00038000040c41346810510701c003130580d02280b20b2907680c54103d09101174101200125417200650524454158801d00c2c046100d05150307128010070b510109858620440c04001411a441e500c4800b1fa80c500c860b09805d0740301e14040700001907041c0b20241c10001e0480e81c8400740d503c1401001524101143c640800d11140c0e011100c010082d003000459403041c4c1303800b075a0548140000d0398541019800c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 325392212 1250 325390962 325391021
    0x120607050304060506010c06020d0f060506270d0c080615010302040b030a02031906080c013509030c06010f031e0803010b070507051008040507090b060a050c10090c0801 74
    0x8003500240c0703090780320380005d103107039005a201d46134440e40320004656a00500317040b400104034000d6811b030001e0602c3d200084914191090f2000d9402c1001210403a884600a050102105d0074009400080040340c0c8004502c2407450b110040552034007500840c41d1819107100300c080740050850525105120501c04101341c401566030025135a0001682ca444032180107112805030510700b80001e09101d07000c40c0c1c09402142d02845142c0a0302c4070355075416000307000070304e1a28244224110700201c15003a00d04680002c82c56030000100e03000e0703c1c0703420303810031882e801d10394247c210301080041c0711004c004200c5407410b500703840b140240c0360100100e5160f54000071480184600590381c02c1c04210705051010034003501004040050100140c07080c23024010344100000c80c0c00b614280034038840080d0800342c038080c0110101000f031500346000f00285090303aa40d081200c404800d44203695040c5043c949522420801d5070040b401c201166181c89140c1782510000c9014400560650b40f100c6c2d96101c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 325393462 1250 325392212 325392217
    0x406080109060f0e1e0c18011d040b1f020312160906050901030b0604080c030c0102060702070501050d0603060c0914060c1b040b0d030305100e0103020121200912060705 74
    0x71004040c14144d0340314503107480c41400310101c40191070040c41d010b000120f00480b00400c0c0c030301c03442124030100500810064680180001960b01100c3c1240b4034400980760542c419902e503600204041c3d01c0c44810300c0c001d00303803020a40080b00541d01c0007407842c041034a010b003a642d00c0031181e41d101c482c00e05c01001c01403010360284601c03c02d02001042e840c0c4268041d400240f00c405018102c10b48a903070314022941d0f00c252604415000b40288004c01c41154400b0551a02c14241c03a00102080c0f03142030700455140e400403c0303031300d4000da0340d80c00840065841e005601001c0358030703541c8402c7c0c20f080c80004c80302200c90840c9075120304070030041007a40d041c01240b040c039400c45212a9510500750000401d000d00500d0000d258011013071540d400406405030b00c407500036605940700c112142d0311600f210303848803401c1c0000b03404924421091a650340701c039840700081c0d0104020104808002241c480c0b40e0300c5040f810080d0161000c100030b80c46050101e160102c01080c1030040049050400c2c0c003500c10b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 325394712 1250 325393462 325393469
    0x10b07020121060b0c071503060308030c070f020a031109060a0f050409140f1b090f01050927030c060901020307210902030a110f090108030d1a03060a020406080109060f 74
    0x1d2018040d04582c0e60050b0300003001410a40e0405a5403e243c0d01c407142c403141a40a81c900c03080c081a510807200307210303202d0b89060f02c2d4001d141c2451911800c0b0421120b402c003100c220345e0391000c41301040060326000100d80c000c52040a103214416000400c00001c95002844240248112501008030808046403103007141d50903240015482e0705030914131910680807001d9022445901805501e6031400187c2da007440b501c1c0c0c80b5601d43c0300500d00800c090102c06584140c05100c99000600840c1b9205101395000311284110024240010385040b50b148085103a81082e50401304054005010a1007507680c00300d001002140713540351015001c1d01042001d0f040c0065180386031000400c80e00300c2d07840f403009140c00500710784480002c1c0c07800602082c1001c000c01c0c004d600da40d5003a440350810086a505031040140510708107801061148018102d109032142030034014030604a02e034500b44000341c01910740490241c0d0729414a04043e00103841030f4070094105143c0101008800c24105e0440c003035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 325395962 1250 325394712 325394747
    0x105130519050a0807050c030f0c090a0f020702131a040501030b01030b1003200f01020c030706080c04030606081513080406120e0118020906100c02040b01050705061e010b070201 78
    0x107a20785800c02901d40b001042d8000c0c5518800640d410030702c280058840065641101200c483c80c044440c0940c03561000080590007407001408500b5400d00c076000103001c04501580141801c1207030b00082d80c1c110103940c031400034507a41c11028084160300400e1958080d0290380c244078030b5156503a13004180d841440040d240e090220040f4600c0d26810b125074005682280b411003071500201e0010b403064485c004102c2c890803038480d0080081d400401d4054520b400140645103003071801c0c4081c0c40d0798000806007802148100404400203000e032041d64050304500000740186440c02d5007120341400c000d0030387c0785007000100140340054030980c200c40a54920380740144d0030021240d00c400190500c081034500355400c1030300100c0302d8004a0741c84c9413414001c480240d03031a01c41c1014441c0503001c10085030001200c0d00007080160409802c01c0c420b13000c06141044c031313041d100d89600c0d04020b415589002c0c43e1140c3d4801001c0308041d2402075003d8800356001c145080349030b0740080d200340b02040103030381c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 325397212 1250 325395962 325396003
    0x1b061b020d20060408010c020d08010e270a08040e0a05040c0b2a0c03010515030a060207050f061003050d08070e01030e0a0b010906060212040605160c091802010201051305 75
    0x358999000300680402c40c003a011540b503076114030366079000e84000a0404c00520039004101c1100f841401001d040301d1440001c580360b034460103d140d41c2202c81c1400d402c1c1941c8600c0d418800301304200030045400c2c0c000c0030039640b95800d150125040146c060900c004070780c2401d0a002c0030582d403903401001ca03120342903856540d81000d2460002071034441034074020300c110542c8460300a14040780300c02c5188001c82c001c00c42c596510000000d10702141c10015050703030018620b24000f8010354000c0c84243e0282c01120080341c10f0075081480d255040303994044a031107101040007044010420556040c1450424410b1454581802852070718018829410151601402e09892b9000d00154221a400060030905903031121803801c05020144107041c0144155844a12008410016070b420b803011940e13010f00d045444412240c0d1411606001c0c1e41d032200200c400a444249889000005c0ea0881c100d4905a58580006401c442c001080142183d0b514500c613000541d0109585030b40c849921074000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 325398462 1250 325397212 325397243
    0x3070308091c0506010e161e050c100c030204050a060201020306010c110d0b04030513050102060c1e0d020310031403121801060b0f03010305010507021903080a091b061b020d 76
    0xc103242c40d03410b409849406010004502c400380f1400c0644122610b20741800f0104c0203090455a00c036032042400414200f00c0103001c05c107407195004180c04040701c0201d90400c0d41c3c1e00c003490100d0344039049800100350300007020826800c0c050102401040345000860131850030030000391071a002e80300010300a11096000361416a00d021000c40341580000214456140a240140482c0d003d030f80c0084414482c000c0000e43c941c40060203520412944805c0c9040400d5180b0540c03074064440d00309010300c04140001020082144007862240c0e904603074601502d851800c002c20381d04e03d6807804406d260403c1010000c0d140d01803094940107540549034802846200d8400380c0100f002c2d4200c0c0300308001c0000c00d000c07000c1400010b5410717240508000c0217251180c038016665080810140c03a0700d41d140c240d804000c030380920507041d402070003138801081c0d5580f280e0340c410a907000032010800030400070b00e040c440168071034076603ea00440c0e0100544504099000106c82c40e2420500070140111181002c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 325399712 1250 325398462 325398499
    0x60819020f0c03070b060f0f012001020c0a0309050a090507300908030103050106091415011701060305090f0607020709050a0f06080f01051617061522050307030809 72
    0x19a40b42404030180c2c0d40710b901030314003503030215400da404502c80c00f105030034450711746080d20904254040c143c4032030ba0004a0065010071403101c0c0365001100d95400e020342e1070326844c00e000860b40c4070b03c640d48806849041c002004400d01403500246962864201040200307900000c3e07581c00601a00130002e00fa070380c2280e81d08090b00c010410200081e0400701ca0008212103d030242d811307288110000d000c01500c840c1d03030380111901004450b115020070004501450210901003030840d030189040580c8010f400700c03800401c0420381c4100c00090741c913410855001428400e800004204201500180c2408400250b84545600501540d65910008180c3c06d0850b070b844000129415001400310540c1c54500d070362590540d19000036194204070018121112041d820400380c407494903044408090b960403a00c0c6620300900c540c0d000009078151900c08a690300140c8a0392141d540002070702e0745100c14882c15480d00b507111500960003500c080c400500030301e05944006500365100340c0c0800010354003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 325400962 1250 325399712 325399717
    0x7081801090804140a080d021f0209030715081315110919030b0c04050915030a2102070b04080304150212070609120e130c180e04020901060819020f 65
    0x902d41400060b0020303403c403000d000142242c1046035840035140d50b031080036071200c00480d0400010381080103e55510b41d00000d42007001000004014181000039010901d80281134000c0080100c04445486010358468441da910540310401100c403a0841d50b1105445104400741c401d106484880d0041020034140c141e070b401c0080140303c086545201032100003041035500090b503240750900c00007000721580b00121002c890028102882a0343c480402c00400101c1e202c2c0f407a0705008402e0b1001c00310b12464a1001d105510124101d600d620071400685002d40302d42c04005002010700c4100101440481a02d0486101c1201c400c5450160a0202e0030301c8948200000080b02c04074189003840043c1d030140715a1841020034802c0c544031310301c003659018200070906500503050f07440c41e004048242c00080415016041c8030004030006001040c0001040e0050641c800400040106501d071400d8140d0041c201400c00124600f06031340c4004501ca20b0b42601100103400061032450f42c03118608 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 325402212 1250 325400962 325400981
    0x12031c11070605040f050f07080a06020d060b0a09051309050a02040504030c1205030703060927111e03011a0319030c0b0f060406050a05060a080c04030804030309170607081801 77
    0x204200604d0585042081c0c6001e07410152910310910130498013408000072520180c40d00c00c1c008002c41c80c080c2e43c600c0b003e50b201424141e41d031619a040061a004500c019244010ba40d0f1594640b450a0a050109401152060f0441d050820002e00003007180824120710701c6030151004a002c1e665401d05807500e00e0340b803000070300040e058a2a4019654013001460060b4100d540610000790b03110116815241c03019201110050248191101c3d034900f100c20b10811441070070343d1141c1c40b00d6074000075a441d05a1b441182e000c01412260501483d0a21500d40702d040551040b00710a007400c2c01080e5141c0c0f03001d075040142526184424145402511030185099015001004620705244041d14100c4292545402242025800324851a081c00c040c4142c8102a1507a4240346c04030404681814000d4080399100710104030200103e1084c0004001a5001c2d480e030800322450807100710400700c8481c0000002e50010b0050025559008030390395000b042d00c4900008808070442094010450b068 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 325403462 1250 325402212 325402223
    0x402180a060804030906020703030f18150e04110406141b01020a05070b06032e06090218031504080a1d0901081c031509020309100501060e12031c1107 66
    0x8100052182d0b0000c03001e44a948030b541c600c040d0a503944030a90f640c250501005011607099100000100d102e141400211207d0800d0b80c0c070050b030345010380745450354191070b90800107603101c44200f0f0508250161129949211540030714091805100401e11a041211081e0000c0300140c1050348140c00003024102c6032401c8000c40d42ca12680601410799480120100e4005030074400280d560f240210308140019114890b44440114009030206020361000000044c0382c0d03140000710340780b002407016005010190641a00300c1c4000c44c1011b00d01125a202411407004041c01c010000d0501d0003a205610303050f09040e8a4109581013505038000c07445061504191a40700000e4203000c0005c0c0000b0b0340c0c407945040701c003a5507001000c80c196506907005620799540c4c3c240800c44c80c2c0556000319031010b101c2040c0c82d2400c0a000508042d5407003a07001000051904010201629000c10b00140c22468000114640b49001c1103503030114010b554560300b0180c1c1c2d650680340b002d9065084864030343e0b002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 325404712 1250 325403462 325403479
    0x9310e030706060e010e0919021002120309010203010e160c02041104091517010c05070b0601020705030a06020306090106051204021011030412170901020703080304050106230f09100302040218 84
    0x704c443c2c128100003441500102107282021402071a404105042d009032505d44620b0342120f00c0e001d11415401d058049000c51041c4580446001843d0001e140110107481c005030f50ba5250480e03aa00b020b401030003142d2945c103050140ca61441e0000541403015a040d240812011070404103880c13680120703803220380c0c0305040481c2c0e0400d402c01707810311400391a505580d142e4a1038040644c40e08803001c030148180807800804c94200454294004650300c040140b04503012240c40d20701083c01e101426508544458020060010a02c1c00090050240c072403450460b003090290003001c0340c0c00e2400740004c2d0007210000d20050459100344103140f80c000c0daa0088079a9142d60b000c9402c0e070b00800c417800307540c80350404490302991507080301141d1041c44c0c160300400d803d504540b03412100d0303400500704403050f66030750000086034440c8184607500c2000c180b600d241019415028054041401c4a07154440c0d000722040160084100a520096030340640b801615140c0182070880800450800e00d948141e01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 325405962 1250 325404712 325404719
    0x90903031b0327060b090a0c020601091e1d0d0203031501020606091f030c060905030610030210081e01060f02060f04050d18031e0218040506150402090a0b09310e03070606 75
    0x8c0c0c2144011030394a900310303000750380c0c0c0758803032400c9650711107000b8810b29065020142d40748180d006405d40c0143c075004401001a1012860701d05200d0244001c0540c00110400c007000100d060030807800803081c0041c024a14114000840b1380400400c09035070200302560400664a4100ba50300c003031039004105902c400d440d03100141400b00d01e4401c1e148203114504c005a08a0f154003807100489502a00c80c2d07410300004601618040c400802c0440f108424815103950141082c02003802080251218106161824070007424850000d02ca46e032010302039418800090300004801c610880540b03400d00c2c903051a4501040346600961014201ca564480384200014201110f008180d201704e550001d041000039594050706411140038000b90080000600c0303000041d103400c006000010001840c0c411780800240e602540c64021001c0118003041ca900d0500740030034004039030b492a0348941030b80f034108160464031501a00d0040b01c000d44600b0f50601e00c1384100296000e071070380050248042030300c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 325407212 1250 325405962 325405981
    0xf08120a0815130f0e1903050901051c09060b0102030a0e090c0405030102031501110a0c050607030c020402071109060a0e1501050424030b04060627090903031b0327060b09 75
    0x3e5880c58944e145080e00c88224000c0000303d1185c121800c1e01000480c0f502a18162046d070411401c990600c802084a803110301034240710341d1380b41071045200291411103410100200c501d403001c06415544108043c1c0205900080544200f901c00c480c46100350703480703201008650140754030164166002005109501e244107459402c2140b0a0340e4142c1c40c10103c5a42954800f19001c0280409130317050414002030400000030f06806009041c50000d50840d54003003001c0ba44418800e079895030b0351881d500da0381e01e8074440041d00032000b128a0346081e03003003948424a03188098072081000c900c5840080307080c0d01410981c2e00415009411440e010307808580c2c400703000565a003410000740b03420407542491a040c41403009440703544d502c62030000c600c080b201c0d075070707034030761107007144541e140c04d10004070410b031401811032180c031030b550104020a000f0070f003540c0c2070b600003106030a050404400e030381072900c008101c46044540e460428580103803410200e0040900b056100d400960318800c2040fa482d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 325408462 1250 325407212 325407221
    0x41119020616090b030a020d0219080615030c1206150c1b0402190c03030905030c030a090f05010e10030e0a0b0108060906100b09031906060f08120a081513 68
    0x5491100c0c40c4a19a079008045801c3d104600680207020014404104c10312000d0707010b056881c0c655400149080d208500c001d4984100d6942c030000618400d00300001d0742080480800c4103c9400791070350643c288580300c03002c2401442001206882d0207400564903030f8a51a442204030f0070b00420555420710500030a45034203061000c5072821807140e0350005641030038421940061001c003225281c001520a00700c0f2003052022040c2d003015100c00302007011810500007002c2c010011001190b03200c900400c0548100615401103080c2410040100321690b040364400f120003030f08440c0713504c2c4900081815001021043c04c821441e2095624400c108020356030003605a40400007181c0055880d51461640c0d0141140d18403088080103604010302d500c02e01c064542c00700000c0c10303586402080d03808401e0380c6daa07024064030a03940391881004103400310710591000e000104050000711445080d03014891064040d200e04002c24180095889201c0040b5440c03503a00c014682ca503000c980f40380800140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 325409712 1250 325408462 325408471
    0xf14010f0909022404051809062e060207090e0115060302090a15020102040e060d03020a0210092102040c0503010e060d0f02091806090a020d121103210601050708090411190206 77
    0x1024101e0101c80440c40052105202e036171404000d000641e01c00d00701c0b204060b440048ac55180c0e00404d6800e2903540740b07600321405040c182d8014181c41d1700e00b0f508042076549a006030761035640b40005042150440d29104415103046080144c2d4410380710340400d2080b90340f43e10002d40d00800001002d0042d0b0b041d0020811207512006244407a151401000f074010700300003000700564065402c0c01e0041c00c0001e03018440514a08024940c5a581c0716810380a2120700c40219000903940302d11001c41c50281b04103403490f11103282c001c0c19036040c000c0c045841080981010310a462444a80003048142d030311201c00c031350b4050410045810450010300804080c00c221003d107000e04d8000070000000000c00b040641d4005120801c0038803203403903070a00c41010729154001c10400d14840741c402c14082000b8020050204112480b02c000c1d0080c9507005070010304804d04203c4104030b1403000c0b8400c0419134490340c204a40004404192411461a6201c0c4e0011240b42c41421900c0070a650b8000c92100d01c41d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 325410962 1250 325409712 325409719
    0x616121e09060f030b181b070501060315050c03070e041503151b0f030207060b090106020a030201151203120f060609080606042d090f060f14010f090902240405 70
    0x400d10f01c02800e0342540c02c400c1a40e40c012109038840c40901450750101a0030860240c0c800c1c001a0900300c01c0c280c0c88d4081142550160346400c010001c001401140c0d21484900c44420040d60620003202c000601c4058082c01c00c01020901c10784c05076586900c200031035055810b031f16030030790380d00e2070541c051140c1e0061250842d40341450b2001405241303c0291050001552042203162071500180c0003504040b00c242c0c0c40c69502c0810070000c1d1180707003501d0b01070300154008286941061400a0030364044000072070007400d10034010461f440c8200d524401555140c10308900c1880c00f05159801030000f0680000018242600002c0d0035030042408020399000c0f07003d4840e85c0da110801c2c070081d640b0f4a40d0010000100312a403075042180190745045d140a0b0310800724020480d41c40d10606030b4400074050724125528403000003601c0052141c0740c0344000c9404000510b6252268408400e411f611807107011989070000c100841d6100d000f4803038402520400c1205505030f4064a0f66a50010b004540c01b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 325412212 1250 325410962 325410977
    0xf01060e07032004052119021e0108011502030c060c0405040c0206040818060d020f03070f0305040210030f020c0102031603061208160f0203010903080f060616121e0906 74
    0x15040c0c11440c0300301907042000030245490b01e06002d00203da12120300456090306800e00208108109200702c1f807103a03411b0805c105221504e8010040a0b11400078002c4001103045000da041d40d802400e22411240b641c0e00c000241c400b0300b04141e05610846412140900a00c001c00c42ca4100302d201910a1b40d009a8080000031a0100b00f0b0782c2c3c946003034a020b00580410b200012001c80203001e509044800900200d090a03a8440090141d80252402c1076010b038020040ac49911352020028001080c24a4140028203190f004900d507050303814a404101511840d00300082e20311501141d409010300c3c1d0086560b4074020750803218000ca95203101d80000d003070010001d41040d0304200004015000700d41705290540300b402d0105206c4d01c40000f2105d1040401502c00035030740070f1044a802d5030183e2030301c100628040f030251074803100080c032403489010309210404070800c00046241c407240c0c0c4841140c1d540745d0021020f540c90b0710304469008448400644950a083c0c2c000498022510540c66054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 325413462 1250 325412212 325412231
    0x100201060314030f0d110913060e1303122f070c06030606021c1403010608061003290a0b040611010c050a1407170f040e1b12090f01060e0703 62
    0x644034861320b056032525032014411010742502c50707031050081c5072004001e80d240200ca03c0100c2c00700544602160540c03a5110804c000c41400c4400856100103a10001014140299070140c845110100b600d2800795980c1c0c2040841c3c1c048180c1d20b9440c2c10075082c5601c0d4068a40e071042a0b60340030003021208121a00c100050140c044e02400c0207561544c1c000d040c40340d55500c41c2184a00301e450502c400c0040002c04440244164001940a00016540c0181c40d00d054028001c810154061030750406141c054117030704047d02041800c185000074000c6026803c058000103e20301e0f5550042c0116000000700014915004000041080150ba00034040440c1c40c0d00151204d02038215420046024201c6540040031104000c0c06c1c62032103210010845085503081212a4101101316140303d0740028050241e02a14080d4541c0b100c8180c20106510604100e00d12042c0100401c254403e100c61001c00c4c0c1002e0b0521060030419604002002290ba580d00c014019880c242d4400020a10f01103240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 325414712 1250 325413462 325413503
    0x20f07021503131202010f05181b03030409090609020306011205100902130e030d06030309061b020a0308070203030408010203090304030606050d1a0a020903100b19030f0b0c091002010603 82
    0x201c0c07164060090300a2503044907254000c1500001c42068115513940c40c004a1f100d00d14841c00d4015183c400e2010707524001100070510f003807003c541d00c4201388013200b0200102d581c004100d5054514205000c160140340b8680345d000b926540c43d000798140114030000c1180d040d218542c11010340200c04031443e03812441540d004594480c94041d400424190b04d00c1340d00003031034001044185030030b02202d107014403042c152011211642c10072030000c0d06400c400c0000e15030040a15981c1c010b4000141c070f450903281e000940d0301d031a03888020580e00011940806640c0d040c004c0d90001c00e000301c025507480c40c10b2800d02c1c0e1660701a010448940b0310301600407485050600707078440210381c044503d100002408038040e45c0107100410865819808001420040d00c0c14040b0100c0041d0525000c11358078400c40810481c44804502103001c584855000c01c0400c454801681003590060a0142103071581a07145515200300489550080c0c80007011b03e40d011380c1540b201c001c07130740219402022010b044100c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 325415962 1250 325414712 325414717
    0x19230309150c0a02070501051b010c02060604061401020a02211e01060f050112050a060f120b090c0102030d051306060b090411032e1505190f1b020d0204020f070215 72
    0xf05006a000c64810b200300d5014078000c201ca03501640c480c01004019017085801e44d00c10300641c2005800410911485040c14002e20014020382541c000303000f4a1080000d40c3c901d2103400280c400c0e01d8400000c034605007003103480d80840141d00152144003803030b0f60209040710300500c40b1003010742c42d2200001e1500e54a4202000380c801c140d46881c090340d03107991802d001c0c0c6809019000c1495075460700050742071058a0140090401c0081162100c090b03040ca100c040000909180d0076400c0704d00480443e03a800b004590200491f01c50000d21500d40c00f900303108028079500d00819892401d1700118109200101030000e80004480620644000c0e54528801780410b8540c0c2c9920040d404159084070300c01d120001211180e07400310b038002561070801ca070011003000c2852000c208005450441d8040c115809202c10000e0309007440c1c100190366005040c6021030744c8015460808022079802c55a51042402903950010130035511060700403518001d6a2000204034401d0a00312094240411141c09 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 325417212 1250 325415962 325415977
    0x100906030201080a02030604060b0a021b1002030f0705030c0610090b04090827060d2702010203030a0c0c05010608030a09050f031e0a0f0303060f060519230309150c 72
    0x585644644413401004040d40015259540c813507110741f004501e054040002d8007244c0420b5000342030f4515110740f9458001e8945c0c4915004041c8441c00c04400e51b0000103c4094414048443c1e9584256080c140e0450055005003403803801450188000102d26041210a4400c031680c1080480f8480d0b04200031220703da10020300e16002480ba00a010890080594140d1105070419141c080c840707001909680c81400781c3d0460903511039000c5070342026112800c810b42c484000b1020709003050780003c0e541c2c1c080103000c2d160154440820980940c440c40b00c003520703140d00400a0100a0701c2d0b01e5450307203c4d0001460303000013540e80e010028451610381d503407003a952030240c00b03800c0d0041c0c40c2008080b6455001d1003841c103885050603690009000700c5c05400030900a58001900c41e08040306660a64680d9020108010080c4480109600649440c1480e01050b007090005074503030103500c02d20201d00031000c0200080100810102e500e02007103500507401c000e46181c0a07135030707030348034000041c0034020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 325418462 1250 325417212 325417217
    0xa0b0f180c010e150c01140411010c170304240e060604180b04020d08040f060906030903050a030b0f030307081902160b0a050f0a0e09070206160c0f0c0806100906030201 74
    0x20f4a00f240c100345240e8643c000070000318a1805480d0244242501e41c81d19042501102e01d90405c02482842c001901541e84240b138847c1c1d01608907212001110600740800c40803a4000001c50308204819140e01e2030380c2401e44141c000122007000d000000c1003041c5502c11039000b480001192480c040c4140b042d20010b0b2003c4503030001c0607450340000c0840080080b40c0242c00c03244c01c4004500706d00003500007001203640c0036030b00d6410120001e080d0400c644c4000c09050500d103c820000341c1000c155501400030b890b002604c248500005005200161200d54250100203840f60601442e8030080ca40c0c50030700b860100c2840c03403140c400c9035038540c000440703204c500600d5400e100e103c4205000b000040c00c1d500c1c04d503050842d20301203034030690f006000707009c00704801d104040d51074201900025480700e0140003800c200d1420b200350008298502c02c40508120100040070300b0091100c0c0340c04002508051660541c1d03881e2947e0303569800301070b100790700c000760b03100b0000034041441d00a1200752681030b03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 325419712 1250 325418462 325418477
    0x60506070803101716290a02340503060601080c030c0712030b1309020a060c0312020408060405070803031b030618040b100b07110f030a0b0f180c01 65
    0x19240e0918581010307241c10461141c01500041804105240400001d4000b015040783c022100d0203100800165101b110001c2c1442c2d220042114080708280340d10000d46640c40e943d0321074500032401d0513000c104840090f02a50ba0000340e80d03200d0300b41c5121405284a1440c0a55221800c00d956000f04499244c0052000340001d2807498025000d150081da6904101e803c1c28101d03036800102e524905100800650307544002c02700d5190045198001c405503c2c0304000e038201540115011142500540e000e100d1520316490806203c2c814411042480c5c54086442d41c1e242c0903410f4a070501600c05860611400002107403800b0040300300c0780501c0f140750910000c400710542d03507110b5070802400c55a120400741d101640d80a0950388091140b407041592521034030340075601e1404844950071401102c4020701c0030000003250420401075851003111403105054003a80001e203001040c08008001d40319020500207003a908010311409a01c040904410704c052408401d41d0741c6400348111070005104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 325420962 1250 325419712 325419727
    0x3111606180807080a02101e02150604050402130b0d061d010c11070e04020f120d080c0703050d020d020412060e010b0103140402010806210304140103090b0408090d0c03050f10060506 80
    0x4481000561a290910451202d00c0d4429230241400d011000703000b50300211003500194094081c0141d1000084400301710608254020504c0f001080c0164a0000e5039000030403020341d44c0b942013580751907012005101510a007510101201c3c6a800c088030558200400850b1190150200e032184026450042490501d40259502103242c0034200303903008102c2070141d011649548940c0503101c20510010107891343c1c440001051200001c1c004001d80005000b0040003039403081c111741c08603003202800341e181c00310014084020700c034907800000c00020031003c4500b041038036048207128403141402044844030301303001034095405034554407903140034507000240150b004d00310030350308400c01520b60108140b103090040039103821420b40b030344194004503007003060303107601c8409402110302803806200c92200c2c1c0d039601541e07101c0900010100c800128904180f9282c40042c60141c58004005100d466640d0800320748400201051410a000d00741149410394100c5c041c2c101110b10241100e0314003074a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 325422212 1250 325420962 325420969
    0x103031d060f0f0a170705040303120605030a03021c03051e1305031305130c051b120a030501261b04060e011d07020607050703111606180807080a02 65
    0x4001400396005000388000c41002032080e01418401c0f481c2240b05903207403644a0003812100c60f502605004980010403c440c0d50340c0700060700e003140d606080ca103a0ba000641200300180510780c22554151240e0700c804070516a0000e001c07240b450905004d0400d41000500490079204101c4015844200b40b00e501401e903100210416800748602108542c80102992a2400d51340054050308070b04c14154011710451418045203a0341044000c401c100380b4002c008098084d0041506403100381d00d00c070b100b03144903190a1100d00401c42c01c10300c1c041e9850501d400d010b00100700c20b02808900b100070003040d03011141000100760360003c5990050290115010503190100ca00c1080a90095203855000800c0d4015000e17040c041c01c00d00b55104507519400132800c030400c400801d400c0031948200140403096800100b1620602d4040c03030590b0303104884411051500c0c4448001d04041440398400040c990742c480076284884011a02d82c00d08a42c0e030b281e8080d075421241c001c8140c10780040140c0d500518 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 325423462 1250 325422212 325422257
    0x21b0d050a09090c020a0f0f150204081005090d08091c090f140a0b0a030f0509030d05060102061b16051005040309120203120c070e04080c1908030f090316061401090203010303 77
    0x40c4955011100008c2c41c1e691850b00c0c280c80c080c00411b41d0380201e014010340380b003404810540e55400004014903c1d103565865910f0031080382e400c05100c402408168212414031072080c003500c600d51024845d030307100d200007801c42c01203110b8050040001800405c0c000310302500303003030001001010341d941c3d1801c220080c101e43d4040702c079280505540304a0000e04003a02e003c0c0c0c0340318080c0207001d16215091507841c1ca00361400141014110b40003001003110103102e2401d58030840c1c0f4440c10194031151070641d540e60f90100868040c215104440f9140362281c6140c0040d440740e4070030754600016503a01d015410340c0da40c400100035415001089a50030000c1001e02801681d2007210480d0300c00c9a03246115568000c00741c60130703264160001070f0724003503800800100130004040150403074000400d8a03013244a00018129003d68001c0d000491200001002500c0900d00c0c9100ca0035011102803901c1e500030718590740c4a0a04503081400007070006018400d40341201c4c1c064440c1d0a80302800342e191054039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 325424712 1250 325423462 325423493
    0x9091012150f060e060f01050415080403170f041109241f050301060e1806060a090e0c0406081005030a030c0c1d01031b050112021b0d050a09090c020a 66
    0x41c1e65039040100304100c58080d503001030188952406150078100184402454445062030501c20200402c01c070720404000384400c0028245040d44950302c0300e1401300d0341c0d40756075603400090041d00790902c6640e001d03050805000e184102c0700020000c5841c004d128900104640e111100307004110400454135041c1d40d10580110010140c83d210200c41003542004440d500d100c10001c1d00c0400184403280e001240a6800035040f10402d1401603403a81e4080311440060085004190200f64803070500d000c0c0c0c40f00d201400c0c24621541c414a00200000040d41082c450540001d642d0000b0410b91000c4001600940b41d0140240c240c8240c1030b241610741c49131542c0c0468000f034000c140010401e0000343c1c042c400c02c83c01c1c1942c1545503d5410f1401030001c2c44107032082d210554001c04c001517a0800d40034070f100058520b01584078100b082e0032081d041d0180d01a801c45014034007400359a80c0d07005000784002c5401d80c83e1810314640b0396800900b01d4009a1000000d6400500301402040d000240301820 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 325425962 1250 325424712 325424753
    0xa03180206131502010204050a030201121d061603090b041209080f010903090608060907110304090609090c1703070f0804051c060506011412041406070509091012 71
    0x9004440d030200e000c551004080051101c01404180085010341da20221420801d01c029804c10f0306010000740503507094400207042c8418000646109001500306014127828450b0820150380c0c030134130280e100c82046450f0804111800c5a04003030a00031b2183e01e000c140c000c080111640c3d1540e88a0450000085402081c041001c0001600120402a0001422a283c0082803501d40e0386000750070b100a603000070b82032040c100200249a140c200c0300c1a0b208090f442c100c0c21100d0056040d03825441250410340380107080c40804184521180c001030140c034864607400e05c0303440d610390401100704a00608040150030411000c00070400402800d070800340100042c031718080d43c0f90300244110641d0081c1d03829040c0c804401c40c0c1800b0381c3d8401c0e0f0f948520700b801e00314418a805d840f88005403240041d1102c2d810b10760b1020800b40011521074040c940c0c01d4070200c0c1c0142c103001c0c5004d401c0381c2202d0201441001000001000c1100d801e506000b110406801036550030450360325203c1010a1200d42d820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 325427212 1250 325425962 325426001
    0xa0b06120f0702030c190c0e040b06040c0e032e0504050703060908091807021002030c16060e070e150f13050a0b09190e0102040b09010f030b190510140a03 68
    0x84100520079031510403c0c510001c491b0010750b150010200126502000f590510f190400002c07031000c0907005d40c0007208a400003039a541c980b5080d0754222001c0c8001d9090f01c00d0000350340c00c032130294004904039104042d020301001c2542c01c8001c1a41c0301103038014140c1c1c0110204100017040b81d00400c2d0780324810221142880c043c0004110000758828800f40ba071625002841801a01030021245a182c0c8540540c034520341420810f82d0b17449100210070a20010f156500300b441181e60182c880105a001034851243d580d4403000c1c1c03101e1065034400a404101114000c041c580030861031028900500f9603401c000001d0f46a800404004119146107511180b0020b02c585d94088041e100780b07554104400300c00d402d410040100c80811802c01c0c0260f20400080c800d00a103102600c080c10000d103401c580310611100c0072000f906c03000160a4015010700391140c8540041403180c0140c80c01a0380c880081c0780c036550b08a414200078000c40343e40d03440420240842d14402e81201180f40a0a0122074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 325428462 1250 325427212 325427227
    0x20c01180b031015020a0228080105010902071209080601090519140907090b0d06110d060b040e0603061302040e07050d0501020c010509240a1803080a0b06120f070203 73
    0x46910481d100511400008414060226504443c03130320110320b44000c0c51503041b55408030348003880310701003a407002e0200000d8402d042c0c480c403890000707071285400074811542d460b65800065004400220b6580740440000c110061080510740200d0f15404000c040517482c0618040007058040c05140048100303e100041c1c1c0e02040c0600103101036074202d18081032803c0c0f44241c0c1008240d40084004071f04180640703846940e05a60800c800b03801210015a14242142a550302d20564126490003400c0840000d40030660001400482c4c00d140c0d00082165940f5003015198081100c920300562032021800d03015081551000b1283c50400c41164036040e15000090981d60071071504a58a0703400046615105100703001d1940c000802400400200390308a16150500c405250044110441000001c0100225402000341500764090101070f88140b410000c3c031130f11048a20301c4010741049c11032581d60509000700ca8100801214500098880980c002d24000c0081c2c02842184010320245 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 325429712 1250 325428462 325428479
    0x20606150909040f030e040209010c021c05122101260f1f0605010c02030d080403140d020703020706092304020409020f0c01050c0f120907030803070f1e020c0118 71
    0xa8010390013540540c58544891a004060004c51b11480c0d0180d070050191180300d0360041700288800c1d130f0448020f844001c45080c8400f100d104c0c55000b40641c46410f29010f410b0b54064011301184800d8102c40041c002e1030344502110310400c0c4541380c1c0f46d02d811035114040c507001c100c140c52035025090544210009103040245061000c0715200100500170711110820f11191003018024442801d004e01d42501e0350b00001e03112050303019100d00380710385e910006081501c2280c0c00d06000c0c0041c0200390321010280c084200075005080100c0c05440788080104e5554055248ec2c001c40c0c0180b02d202c04034905404110400034026403000f60429000e20000c81c110100d03001400144100742001030b01e50f401c04900600751380c070180109002c2e0b40104140305580851004403551800c451096208584400450601d801541e0b400904a4a0080140f004580d0b0250940041110782c0d5641c0c0e42c050406100380b24150b0b06504101c0c09640038001081c101e502800700610740e0701c1200388001c5016500c0852 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 325430962 1250 325429712 325429729
    0xf070e0a0f0f0501030e12041a040e04030305040311060c04050d15020d09210e040b01170c031006090b07110307080f0604120e03060402060d0209030f0703050f06070206061509 77
    0x20100842c1003440c180059603040c07083d00a000400e0000f04041402000300c0415407003035003c1e64036070600e152007500341d80c0b242c0d00441d4020304800000e180f0601c0c0c10705006000700030a850032000501103100308400010000350b000d0003083c071a42d40750714043c03804042001072440160110341d214074500c42e04012018070301c00741200f044c4000c1d000c0360f0034000346460100c01d89540100c2c0b40c00301d5560b845032203071a8040c003032070403011080c0c500050004500c00141c8222414104001050340000100700240f01000040c0d4010740d001d2000e0002141c40d114151075072202c5028045410000344504000700300300010009200304007030700355203402d03465200250414240c1d488071a002c0d031112003400308010b00c441d10590702c200107140c4044042e5030900029201c0e0000f03070000c1d107d03280200d003001c0f0b4541c15070b0448084000007000c545420380214481900c0d25603920040e10140504403070281c5862000c910b482c0302c1c140d2a80a4503442e0707103080030418003135507003419002103017000d1280c0c102c180c548214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 325432212 1250 325430962 325430969
    0x10030e19110a0b12010603090311250902070203150406060e01030b0405330924010509150109060311070f060506040501050418060504020f030d0c0b0f0f070e0a0f 71
    0x32000c107a286030180b10308450103920100d40100c1c20000100243d5101c891581540c00525003c252074415080855601c0c000c40c0c180c542502441040b518002d10700f848005164200000c41c4129964440c482c00490180850180d01500000740080d84601120603c80d4004e11400001400544510213000080401d8100b151005510030500050042c00c01c40c0407881350001c0c003000280b545141d0304890003140315211494962014003c29480703207052060b00504030341c6c11355003001c40089841c0352060490038801e803400b070b42001c008580440101200a600888180c5441d00c9052501c0c500310010050b4120303c07602548140032050001d1400c421421813240100b101298906001f0100003c90b28103034046403040f8076000280d540b0b406100d44d000030158000034000b80503901c2c2d00200d503a40e010032040caa814010040300c0444aa0819061000540100c030303400040d681e8514904035030303107040d03c80c6401187d200000864071442252001c065840150041c0072882e035070380d030440042c0029007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 325433462 1250 325432212 325432223
    0x50303040c090912110f03030702160509040201170a270303050601080115052a07080d21110d1a01020f030f1603050408030403121d10030e19 62
    0x400e210500a01208a1018103008a81001a602181e0301c150306109007484a0080c01640c54030310044240500050381051205c0741600c0d40e0f4900000002e4032003021401c900d82c240c004401c003240e18142450958030903036040c0c4039080c070000c090801e2461040001c10b0120015100d03031030001c6e288410035840c05601c40717802c055030300d85407646405400d0320350091040307041140c020f0040241c0400150755200f810040d0070700c5035603041c00341c07a0b5600d050b811071400260a48542c65841e85520b0003d50301080f104054181d6074442e072200800c071194031041c0c81c41d10392407640203a903106510325030f40b02001c0c1c03589401c81c1500c0c000100c0300305400e0f188054001c0c1e8072040c3c29003030103600e0358040c891607186208030000340d86408007002603020780d401054034105001c00e6003480c02040602950880300902180c00849031600e80d81c2c82c0000c0c044242c10b40010029504040650301c034070040541c213480c268001c0c80034941e50800c600c110010300303420386032076014800e00c010303184144003181e003025515000e207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 325434712 1250 325433462 325433467
    0x3061503060e06040506041b030c0f030506010b0a0f05090d0b04050a050601080c0913050c09040c050a1203050a2304060201020c1b03280b0c0a09080304050f090a0204030f0503 77
    0x14101481101e07203882c5007848a800060030480060004580c055106511070881009140382c142c541d000c41c80309800c0240325040d2503101054030400d050402c4100d0303203c1c1003203400e40d03a294000101d041c040d0400040200d59241d4140d21950b0140001e0015041c0291070311402d14000e072204104140c0641d404e40c0c06810100c031f403000748581800407501500b0a00d0007040d00300c0070345002c00d4401e00010700c0c02945075101d4035200c0411906009007141c031030000b0b2200c4100d0409007080480d400140c4a62845080c89000c001a040307003110504001d1034241c1c0303446d4141402c140c070580308002c0042d071a001ca14170201c06802042c80181c041c1000d01003541c00162610410b8483ea441c1c040f60f00181e0020302d074083c00e8002181e0f070000b00182003031507200944d5828401c0800301d80f5551400c00c00184040403110410160b92002c00152942c20303d25030301c020100c2c0c1d44008264a03031180e405515045866051400214104104143e80203602142c0041c40c080c0e80e92120441030911039030441d410b8000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 325435962 1250 325434712 325434719
    0x6110304080703090b03010b0d0207061b0809010c08040222110a2102070f031d040513051903090b09030a1401060609080c2d0d030e03010c14030a15030615 68
    0x30420040291036145e54141c5103505020f0340030704a001d201c00300700f00c0c1a0001a41810440f854024260300d105042035001215140704001e014802d08646180007503181c00c091010841c41182c645001e203402404a4205618400102d141400c10610703402e100d0b6100c0441b17560748070703104008120440260766010b400100d20903c1c00700c07a5a12138240314100c0d0041c8028404901d40c0321102e0b0103141d00d82400340d1240c1d000c644989a1003410849180d005190804211805180f01c1403107170054460b41c2590303071040e109031180c000d0007000c44003d03000030f445ca6400c2c802507071a5001402c03c0300f4000c086905500c031550340c00401e1001c0b55000300c016511800b0030049a03800440e2000940789660103840410507202c0800c8941ca40710f4504008004010f03402e0440c1034014400d082d00841c05000d0240c60480c504015003c6151b01e18003900942c030305914510b1035807040001c84002c52580403c6480e54884141c100042c00e400c400c000311842c040040000024094030a410030f01044a03811811540f9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 325437212 1250 325435962 325435967
    0xb24030f030d06060305041a22060b100305040c0515040305070f1a040b0a0509060c24090705031b1f090f050a0302102a03080619050604030602030406110304080703 72
    0x84c1d0000b41814101424800022400703c120094a03002c84913040b0503681d5000e5607000240c809142001c0190070185c020b05010460700540e41d8040d080c1c54a0141850b5040228100d91007200d014000101000c400d00152501c98103107a07180b1075295030241016166200d4500700307d2203a0000084010341c01080024480d501d40c0329070003042d04040903043c149011850400d40c412680c6440c01c010000445400b103a8401050308c0340c0b00100700403500800f01b00d902c18001e09a40441c0c0684168180f030009100001c00140782068810290280904140c000302c050015215021956440404418445c00c402802c04070b00c50250300683d00c6074142884d2401f420040a0250401401107006072400c0c40580c076040741e03088901582d40381031104500b10488051200c10803408100030700002e49049024594410342d824080c000c205c4101400304c400f54035804000750356100c1d041d00088103000c1000803c400341c0c00345078407a0241c4000f00d80418201d9407500c240d80200c2302110640c401152020074181e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 325438462 1250 325437212 325437221
    0x18030705010903032709090501020304060b0405060d080c0a0204020a08100b040e06130f050c0909010e0603070302090901020d0501030312140910020a0201060806180f07030b24030f030d 81
    0x400b801c00d482440d00350384005105030003060b50080070410305414240b40e94041e80c800002003107031513020440036200385031a5002c0d6005a4050b900c00d030420320012424a481c1c480c07a401090002c00110200e02c00303507134614154018044420040c0105060940561a41d000610643c0e20356a00e503015442c0002c982d880340700141d00500701600c4140b0042c07200c040030204140d04040d044500140840700c0c001c4d00400ba24061070059103003801d020500c1a800921000746c000d403102102c122031240c1c0c81b10142c410a0604555099166001d0340041002d070400000b102d4115440000240c504200c242c1d1403001d9510030f82c003c4000905040100311404154070a0400c00750440c0403011440c240102507075598078918038203d181b150300090040402d4000d40c042001000e044064420300c1ca013030800c0390700b080442d40c10750300c66000740d00d809141c000012449809690b48a140d103049511a0907d41000e0095120004074208200e0103000c91607904100906201d15800015a604c00580700044103030b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 325439712 1250 325438462 325438469
    0x4031527060914070e0106050903061305030c0a03030608240a091a240d0b010611031c0204090e060405100f02090d060f06050f0108042901030f0501060b040b120615180307 75
    0x5001d10278004142c3d0082b40054121568586900c0b501c0700c1403d141c1e040d449400e00f071441c0c0d4410000510700309605904040104c5a014090300e070038070f80000c0c0c00311960024403841c0500c22011800a44085032a40c00a40184c2c0034101440380718021411030940504c040d02d0360050502e60884d07031054140c250703c03104507400003521040702c5685640d50300281a041801444144203481900003512141042134903c03c45000a0034070400d900000844000d50040c012800c5090408002541001c80054507602071a480001001400c0c03c0c513681000514000343d0f07041a4030340030400041c1da60740d0501c600203c0c038050301e40010102441002d95084032085e50003540a0030321082f01100c903a0b0014062540140c100040d0070210841140b2803040040b0b400c40c5032680c00c00d207800442172022120f10440b0f680d21690013040444c0e1211b4100c0114003603407162001504040011035090500e18803100d82001010b41f49440d13041c0700d024045a640c014502c0040303841c000e5909003c50740303010403030350006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 325440962 1250 325439712 325439717
    0xb18040612051f0b0607110f0102060907140109050901090b0f0901060909020c0a021203030a0e061308090f030106270203070503130c08030a0504031527060914070e0106 74
    0x70269520030707486103d541a0f52241a0380c0305645a95000300c2e8103c040c448400900c081d42e51358061600700e2852160f540410300031801d860401c4000d500000d0402d00907803a82d0300400c842c914080a41c01481600c0210358100721082038000b41ca0b0711080a1140a455103003804100f0501c0b81d020b101c0341003050055603102d2481180100116038000416209031801c1300740c09642e4060280d42c2c5890804001750080d04400c0288418441c2500400690300906d20f000d42400403030f082c400b03c240d48550603140000200d5140c0da5880000f540907004000750032003e001c5849501d842c10019084444550000e03807008100c8038550844698039103104002411404118218204070400800500009041c10003400b01d960505003404a8548208000c11584003101d503106100500188241c2003071108440211000c6010b16405195014080d9210704104101100c03000f4051840d60740c02c0807807000c4d03407caa55041c2034804181d40102003000034080307000800101d4a01500741080300e40503030040c0b04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 325442212 1250 325440962 325440989
    0x140a06030215090f03030c0304050108090d0906110a050f011a19030f0206070803070201020a0905040e0c04020f120c090907140414060906030a0e06130b0412090b180406 74
    0x60b964000030806081030000d0340368840b845070001c298912036184103140d26110220308035241d590f000000344142ca400380d90b0b200e081c0e02c403162100d540d800b8100d2001c0110b030141a050000300c0c400c03074203a841604400111080201980c0310742d8146010602c0705581651202625282021541d80000c2041300c191010b1013000c055802601c40e048031400300612000e10340c00b0a1040d9503901080d01c84403a04201080c2e600c0c00c00310000381c000d51000f8070020100d03010680000d040d14061140341940904640030f444071035030242c00c0000950201e41d080c801e49006011260007404501601c0703106140c0c401e9545d43d12410b1404021421400030208400c000e407619841440d0300b88401958219140c50272a0355840003040c00181c86400362400c482d40001010007004400105a000243c0e4001011306485054885008031002c6410214018040c03c1c6020041000100c501016042400c020300e8070300c09158560305100400c0d03020700c48501e200220315201c1c0141d03107424450400100b03c0c0001d00b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 325443462 1250 325442212 325442219
    0xc0f0606010f08160302070b0f011e03050d0825090801110301081b04020f07030c1a1b071109040c15081018060e01150e0d0b01050d05030913140a06 65
    0x4203c1400104210743e4000e1050303164005601a40507106125032118004a01e454240d60703011003c0742c00d00c141c0140c1002c50307041720443e5441c4142c11040d2074000300a00340342700b881c1400356143d80000d007800d0b08402484006110781a01144401e010340503030380c1c41d58511854101c541e82522020506004145006c000400240c07030002030f0301102c19594044488400003041c0050002e001d0417a008145090000302c20040682c0101d04620452040d0765040764071030390103000e80b0550002c440500d02c0c00890b0a00b40138007400b06d0050111548a04040030b030300c918103008103e0b042e5068400300d5030440507000034030400d100700d0f250b210400d0312803400358103501d051040d6041070800d078420501120000c03045010405001d400510240486070031500003035a40315804c00480305140341100001d01c80c40710103036551030424440300c2d440d908034200d0f0200341d00780b030104051007510fa030003100d032403000300481070b22a01ea03007a001e142d40341c400c140068052512403c0d618440d0004100c819154903201003807 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 325444712 1250 325443462 325443467
    0x120109230a0b0903070b01090b10140f1c0c030207050d11030702040f0b0a06120608034e01050906090405060a05180102040806041b03111c080c0f0606010f 68
    0x804681c2e00000b070078529865018801d0305500c0341600c068003000b0b00e60300205500400b40c111740d800a206490078242c3d8000101d080f1909100510310201c1c452040001744004c41d070030000b40000d540c1c03030005031000f20170280c2103004031890a07140c50086500844d9400070b10809111903c5550620f0420040b4030a0f000601070b1a8419180c00070b10455607030398402e44040c1c0950207031203035200280640360400d03150310001e08800b00e00c0840c447e510b4104100803c10840120a0707840d90845070900e108500c030516246106039140c0c0300c21041500880c1058010b16455450a22440b03040c00222500d40d410a002d00c85101002070045020b007245509000029000180031070340903d07807600000b290344602006a6103d41c0941039404c40798004140410306040c08103800707004510461012140482810011245144034480501101e801d000318407030780e050401c00d92003a01c89203a00007114224555500540340c009107401506a44143c0d10403103d5007040050742e4000d07009080440318440d254100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 325445962 1250 325444712 325444723
    0x20f0303250f0b1005120d081303020a0c03081306080903190e121e010603020a21080c01020703020c0411090f18041209050a061b1112010923 62
    0x2000c0705044507580081841070082a0b4004698002420075441c1040c400c07070303003c16040f40500f51048401802c04284443c00050505100c04185c9076100903030380702921056400aa0300064041d406461244d40001d0400442180514480c064043e1170b042c00c205840c3c0b01c540d40c7d0304200b0611480009000d00c0030720020075144000800030a00d04009044401100c0701c1138441e01280c0c005c0d800b007000d00601071010941182c8c00449100920480034480c1d82c4500342c444a20001e50000c0e2200030602c01901c0c0020700480c1401c84049080c509503483d40c428201c0d40c46030414183d580d5000c40c00358101070b414000e802100e0011075003840300b2001011113407021311421406034400d1840d4070340c449107a12201800400e10700c403816444020714103030400055142d101744445c1e0008020f190040f50b946000070340003080d0b0f0901c0d07807000c2c103440c000b041d50800c590014034241c801d15050a030049d500d5403103c0040300c41c000d2681c00464442c940340340c080142b0344450a08500080c500c04000c80e1100001034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 325447212 1250 325445962 325446007
    0x330f0712030606052b020f0703020c0406050d032d031d060c090f01090b0309010605151e0306010516050d031a0f040203220303050610030c0e1002010204090612020f0303 74
    0x2d103807208001c11400070440c4101c0c05c168840031390010a80c2a076021442d0f0150444e64000d80a076581904072030f0400007280c009000303450740a18040c0c60400482e204005010525064820810700b04c0b00c50503c0c60340c010020002d00740000d44907101c402c0040e10f40c3c1c1010070300705064001804282044a15038245016010b50b0602581820403060500c0c0c0c4503003001d900906603481c02c55036a041a4859a002e062540546030080009903486114001000202c804a00130164401c07210000041c10320a103a1019041380d04000c01401050403494007105150203640c0701e0b0f0b00030101208134081c06815140c1000420003880302c850134030b040e2902c0d01480d1980e0403e04590040e0360365201c400480e45545900c0b0b05d40c005040b00c2040c1c0d000c043d0158001c6002e07803000c4071030610842e41c00380c040303040c0c0b00364080010010342001703001800d03410b00c6044040a00c00600015003410380b140d40c00c404980d0150702241005141400c3c1c0e40079410041a40c07640014103401441ca481b41d9030b007407c202c0e6a00e000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 325448462 1250 325447212 325447237
    0x53708090601060e0409020d0803010e0105100503040f06140a0f0608030c0c0609011709012f070f03051b0c130c021510030c06020309150405330f071203060605 70
    0x6101500e90340d0f580306d02c00050380100036110034096070500d030744190003d01500110125060000c0344a260a2081410509481e03803070a24503035403a51140c52a080c1c0c0c1c002103a08589418040800c0001064000e20a8030010000a000f06001100f030042d42c4003030b8040d03105034004110091b900c0c800803a00c4a41d202c002d884483c1d1310208800101c0d10380000d910598426490101440803586042d08401e80c2c043c0c500e1110001d509070324401659501040b4003040304c0c41c6040241800080c16440002e054501a0500d582420703403d0701ca000d85075500ca000703072401c1d4009014007070140ca85024088000b41585000300240c030300000001c0e5562609480d1407860209540c005100e05401080c14406540d009003103a521654418001c1d40e26000131140c280f06484107203161591800c0307842520200e80c00205000910500b002540302803d80c1000310100000181d020307104080706e5a401442c1340140040d600ba599662414040d180c2d452a46c1c50f00101400c00508101c0207910030141c41ca00403020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 325449712 1250 325448462 325448477
    0x32c0103050c1201080a030801080c0f0907031b12110f0a05031b0d0605091e06121905070302090c180f130903050d110403120f05370809060106 63
    0x2c1c4038500c240c061200c000010200c04000030644600114044008074882d89800186036215038040e0344851f8810f601927013011010005030365900e0314882c500e81040351810000381045080c80d025581c2c1d010061403102007054105030441e000b01d1449515058165400c0503801e00020003200210387c171811200c64200300b804408a5060140805030b440c4049801030459500d82003039071410090031503403007490700c01d40410300003441c12414111403045807140d02c07000028955959040116490050800c46242c1c86401c0c405034403c141324031100111030142c402491058910700c1000070f040401401c084da000700078004422400c20844e0000c1002c003044070098400f4006002080c61001d00d5800c1c0c440050a190001d01415008801041c5032400c1c1007003441280c0b07040844403034620561000815280c52239150184040c401c84500b00ca10105181c054601440416000c0c50407003031518000121550f04004190402c410900705984a19420405224a03000c40819141c980510030308041c008030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 325450962 1250 325449712 325449721
    0x10501030b010f0503070819020109120b07090b0a12020d0207141606020319080c07020402270d021503040201030605130b0f04061217041e08100908030703020f04030c060309032c010305 81
    0x280e49422f024103041c00100404190a0401040021080c0e5049010071104180171450f6030340402210010205070f120343c3c0440040c6144440203612190080c40e0032035007408480c0001344424150851808854000c0c96000400007403500c480300300d544150255881040076091884000069120088140c2000700d110b80d03030343c00d10310030314450120000e510070720004040310440d03a84204400150750740850214400c050506112402e400018081d41c03240051001e000040d000c1030046512070b1041c034001c10255612030101340c0002003c0020802c0540b141e158103078905044900201419049406010142c94039210314909400c45001902c0b504c00e9111015400ba01e03402103400802103180c1e0f240411031802001402a10030307000d10314550045001e800780040d840d000d41040c964014540a2454070b50aa050700207500124100c510300d02d0911002010130386041040340100752031f44010641d8041c0f0f1500406560041a02d003004221054058001c11a00380c070204109900307081c005082e844 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 325452212 1250 325450962 325450967
    0x1403090304120605090f0708030403060e010b1002030d05060f0a0302060a2c09010b04031707060908180f03010608060604020901030212070c1a0630010501030b010f05030708190201 79
    0x2541e040000440042120ba000300505944040d01c5540c0d0f1400b0345144010031707450303507407902e03101d210312852a4801d200910109031154050080441c00c0d200004884080f440840c1220740801005c0c0c001da0408500341c11501e403c2d01503d940114111043c000716101c600c0000d41566007400080d0044401180c01e00c0c1807405182c01c031010b001902c21001c50002d581c40c1885e01c007601c1541c15809452054000036040c9244007e540c00d9a82c0310074865022080c103501103080381c002d0700003640d2031600c40c0f40500102c1d41c0071004001500c41c02660541804154042c4000030709420220350080e0314003601040b00050100320550850710480d00035030345001410049010f409880515004464260b0910400940080c6004d80c00343c8241c2d00703140307880c445005d54000d0040440d9156001300c01d6240c18828940110a1000645000000700d20000c0000004a0841d41d0981085070703400c0c00c600041c0104003d16002c4001003008600500701c0504216603192244100040740b04102801c581003011a030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 325453462 1250 325452212 325452217
    0x8070c0f06021e0c15060607060c051902030306011d01020c0f0121020301090509060708010302010806010c05151b1303141905150f090a03300212010803090114030903 73
    0x103458029184183c03401da20869006210040031441000d1004441394840910306100e000000d00d81030800c281a00c56401900318030515000b000350812001e000b915440e1410142c05009500445c0c0340e161041c005054108240340140e5121081c441190035a071340000c0350001c001040c0c400c0034038a40c03198016100e000a11542d1016a0540421550b48500a0b03000c0d504a4807814420300c00e13030b00c6003c0120b84680061b20007030300007601e041c011320141d40602100f507005001803510310514200f9495283c01c005600c5404242c4410702c01c140200448544140c0c0c4441002e00e81c02464030040340c09818548400307100082c0428441a94110700790300910505801c2c2850116140b0a500c0c20710b4041c1d102c41c4010401c0b503400100c1ca0104180003050000b144c820140080240341c0400952800d03203040d6449142c804a001c2001d0018440c000341040d03860702c00c40c10341c4016840740711a00040250902c140c00101e201e900a0000c039420383c0e4000c0d88c8080c80c403e000d1250b40d40341c644091407401e61 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 325454712 1250 325453462 325453477
    0x3020405030f03030405010f05041208060328020109080f07060c0602090a0e0403030e03031005040b0a0801230c03060d0f06061a0d0f0c2c030a1b0608070c0f0602 71
    0x41c041d11806800000b00803000794801c6100d08001c020103406076103030000b01c840655000c1c210340c81016070070120500490080c0d030488401012544200030f6081410280880c810a501c000c80d0b40600304402c55070800c000d04054940d80000e0100d45c00c14030718a503500c405c540314100c01c02c4101c0b01ca4000b4490298111041c0d802e01901000d07425440f901c3e548103100090710200d00091600c0c134210840711f00401503a0068405048070350f107132032503e0304010241041c1c04026030710030121580010340b04000d111b60700f0701b91904154003a108240e001188402100140680c40c5140d041080003215a00c506241a005074800341680c000046410520300a2040b90450008542601c040300f4010007288007601c0034422201c028000c6040ca0303e6607000799070a0180c1c0c000840e030400180b05c0008492002c0b110302c2c46590049040c26424440021701e0001c2c9060159452060f408d0240b41000c408924800600300d5810a1200ca0415040051204c945d108018108005291034a81000b159404550f6034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 325455962 1250 325454712 325454719
    0x43f15050a060e010b040605040504020d0f0e06090f070305060c0304051c0503010906120332031e0f0702030313030908010c02011406041401030f0c0509090106060e0d2103020405 78
    0x81d00e040c03407030303480202240d0041c0d900303c00c004000010a40007000441d025202681d031214205450041408080d41001304040303001512140b00c103107460140c1c440d52007102c007950014181130400006850401c415030070441c011b900002c0090012500c00a85503401100320080c5640d40d81c0c580c1001810940d01d540065414907860000d2070b280e40d8810061410f0b04c40e219401c10a55a0f030314245e1030000b03c000001030108094035000416a1107105104c1d0b00440c212848403002025940c5c28031081d442118096006c1c03850742c000c0c07400c0480c1c40d940c0d00c0c0e021542c00440ca0307090074410740c00382d42d81c00010140b90000c515890031008140c416080313140140b41941c028064984d4125000e400f0b01041d44184a1109050000561501c1e0038000c0c03407e01030148607050400d90950f01c40c2030500c040341c14103548a14070340f40009180d89a08480a1040408100000f442c904003140144000650310030345109040d100c00100c0400c40c20600301c492209181d02102da170f00700888090780039011790b9129a52 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 325457212 1250 325455962 325455971
    0xc240c090e162a051c080f060411040b040306050c16141c12140106090303031107050a0b0103050c030703030806010e0a05030d0306060e10050909070c1502043f15 71
    0x101a0355000020032194812000c2d50150388685e880d0400404061041d40005580c010104000d040c56a4156402200243c408105803030b0b400d0340c000640e4842d901050205034002001c0040c00102d02c01e1a030011014031540c1c3c5081e042d009061240703074410b100034020308003000341401c907072404000b40704031051303420600c294088420324042c003600310709200b03041c3c514203000c5c000e5405011224160b050380c0b101e860341c140b01821501c0440052900031586111100d0800c0071102107181006078401c0580303c1c4502510399811841c0480c209480c043c0907074000e038040b140c240b0010780c20603000b551000085c40e180c2d00c000050030000e0130207007044c2e0095415000722131403215000e0385034026405613a040c0e1544c40b41110301c00305100105940786100e600080060001e03406525280c802d941e00900346103000c114201c0c241d01c0b510303400380d03048000183c15a40003408000111300346591481100c00c01c400040c0c0124201e101001082030903041800c2c0070360314613843c000c01c5449544003d4541400c8010030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 325458462 1250 325457212 325457267
    0x2060702270c0a030e070807062106150f030207200d06060308250510110c0f03070b0a14040222110a0311071a070c240c090e16 56
    0x81c10351040e6020030009040c2174a114a01900252803000c58403800000c12800d440e02104554450901d181e42400001d1100e40e00d1700d1181e00c0c020f8a000c0c04910803a0f030840703110003c0242c400a00440641d0a26005001040100301d1a50f03d02d9904034040e4080081c006800b1b000948481301e07140014001480d068000c0305001a21002d84100100302c4402101008040c038076403902c0c0c8140200030200d500c89011504c0841c140d070020558a03000700f108030b003001c5019001e40c0c204020809414115400461400d0600c800303200520f411492032041041654800c83e25444500d600420280c040d0080a8220b880920100f024400030710040404014500211340803031483c1d0301c40d0884200082c10002c203503030100804411200b140364404290705042c02e80002545001c20014003500a03c060300c4c03508030111300d203034022401001a84004400e900c0000e0f2180007201c4038074484100304285004280b0003624043c10316508142c011030104200c0d041c1110448500704084a40ba0203001e0800070301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 325459712 1250 325458462 325458481
    0x806060d0513021c0b360607030c030c1d01180306050609010501030509060f0601090b0408031c0b13111e0a1b11010f0c050f0c01020f01090206070227 66
    0x30b2001c0f407003128150079201101c1c3c030015004904040c081c00005000300032559000f0b020030100540d5010144105c000003514800000724046124a980f403a0418020043c00b00e0303052040100302ca10b50300b010010400f0640d8002c0c82c114144145521000314905201b90780c1e8041c900300344246081201c80c0110300d03100c0c94410083c00c415582075004040c100300120f03240d03000e8095244505018070044c856035a41c42e504503400e14014103501e0520003110b40201c1e41201d1000144003810002000315034640c011560501c03608141c035200034050345420848195a036400f547c8030038800045201080042c5801601a190b110340c0c203515081a10240840d4100384040c00a010140c4603500c811407841c840c02010807070461500d5005084440c01d1001c00f18640c05400c0d00750700701e00189400500e084250b65110300c3c0021900c01d0f0101e0340d0001d5640c844c19a41002900b00c00340c50f10000f8070000181c0c1c0c1c08540346000f0100001d100350054240380201440240148041c1c1100c1c4c0c01440813810000e402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 325460962 1250 325459712 325459741
    0x17150607020312040b070302010e0d0f140702060d0b030d0309081b12070c031a0402060412080d0c110d2c0607121206141f0c060906050114010801030c060806060d05 72
    0x45026500740042b00c501c0c0040132840040caa41580c4601d268911103640441c0d0704101d401e0400c4616000f0b100c65000340e204d01c400743c079003c0d02c20a4005004000d1000305071a04050322400d408040c203100810000458031000e460a4000c07002032003c18462003284941400c41c1403110b061220000b0681c403007803180c0419200100da015000d65028484011710b07042d0620400c4034069005002040f08100d5101050881e0f0551070144003240e081c03800513034488080e140070150703a000243c1100501d0402d43e0b81804001005855801c055680841200491908554006a0a942c80940c1c0c40350103841c0c440741d0440d40d4084c1c0c00440112003010006014103050304100c000c605503840c046002c01e40032810b03918030382c00490051100d03a02c47d104101001e0701e0203026000d541001503280c5104001182070042204c150b22601300481c46605040e44000c0f1840000c0710305041101480040010481c0c0000090684a00d85405400395a590300403540920607102c04500c400c1c606810007484407a040e00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 325462212 1250 325460962 325460977
    0x405132307051e0a080613020d060b091503073609050307240b010c060e2a13270c0302090a020d060b040503071214011b17150607020312040b 62
    0x41c85001381d41c84903140341d5075000803190070060300c0040300c14401514000c00d010591a100751008120414a20049000d0340c070180d4074030607940048000c21600b03103028402c07100903200030f2551b0225601040c80c10a207680c8007090005240c88402c0002e0269900c941028980316003000407207175903501518101941940c0802c3d070803d641110fa61600a03411a8014100d00d000165914040341e2000d494800041002030b6840c0010701c030b16592112030030064144403011141f00c241c0c20302000303010418050058200302c114212140b902c1a502e61000b00c07480241c2d1800c0e031034800c2402001032454480310f0301002d0b400295120074201304001e441c0c0d896800800e49036a680000b4440a644c0320a09841d0b07002d140a52a8181c0008209218200c9103500c40002c46008401154082403010324180c2104c000751007805454004e209140c11107504140600c171168022044003049103000c00726030908034600740d012403041100040c8034047d0360b800c0006c1101c120400f030786030713907620381d07500b001107065107c01da = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 325463462 1250 325462212 325462219
    0x12070b1803160303050c0705031c030b04090b01030803191409010e07080d050a0207090603050303091b180c1207031e050c0306060a02030d090b060405132307051e 71
    0x806580d454100410b008080040641210640508543d0709941c0e13030300092841c54075441b880500059030360b400c00c035040d480608038500000b0107a0400c802401e42d412502a58092424203d114000075440804503044a411141583d107980702d15103c00700d0410324071250f01019090241a01080e0182c52505000b15880c40007082a5907115071400e4841200f03106000c695001750103001040d60240d40280510841c0d48181e5000c26115030000086030080e80095640fa4000300403c458224200080407200d01d00150380c80f030208540d8005840c03080c0c00001c00e4900102600410000a9020113844003040404802001850a554010010b00c0601c0303680300c0c0c0d441803050828801c109480b98501480040c20103a140d0791380c100a110305548242c0b034036011444104a294061070891082e1052588541c01400050502c0d0040005640024200ca0b0500c004900980009000321014880c0180c12540d940b04580706a80090300b400b80c1d5a22030381c0c104400c1d01d1142d91000040d803a40c2500e60342107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 325464712 1250 325463462 325463497
    0x61b050307150f0e0c090612030705070617010f0902090103020721030b01050c07050d050c22060501090b07020f0406150302210709060804050109061407030b040c12090212070b 77
    0x30303c0290941d0141c0091810300e0300302440d06081030800032005940100040c0c46190701c000b584007646d156510481003a40c440e040510140107140c1d200c4042c019050584c110f4481c10750410010300035014052040280d8143d0000300050309900a0301039a480750741003401a00c03e404492031400803910010bd1000000385000c65200761507024000b660b003895194402840c10f03074102428064070201181c41179409110390020300b612035a80d44200140d010b07010b002e108500c43c2921601c2d09862254110a061003801c0c1d41c140480400340081e242615012502c4120700c5003034502060051a280d00400380c02c65000900988203a0540c0090513010588030541300000304107030714680b0a140c00e4500380f000442600d420000c80d0700c23440006410a000700000204400d003540e41e4401c039401c99400c030603040c02800801401f250940b16280f0480b0054a0034002d182461300c00421115401009051555440d00c0c0642503403501200741405800300c0044807030951321103000d03108641051880c00001c80d00c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 325465962 1250 325464712 325464731
    0x6150f08010b0a1403091009050a030306050f06070605130611040303180b091509030a12020f15070f0c050609070e09010b0603070c0204020712081605040f061b05030715 74
    0xc00c040726020443e40d501c800c642140150030340c000b54005801c100315032080b0140324210f600c0b2481a213080342d1044008200d00704480c0b4024040c0c4803140e000314410000c41e06c0301c101c16200c40c41113544030380d0300800010342580c5030488140e445c100c5000c05480c4500d4410f106005261500040040d03d003e80c507640158a41082001c218003418040c6212103107052002c02c107581086031780e08200cc50100b4089040c51200d9011a140c01051402620700380034038428601c0c1603405121408071900700030040d00500031500203c200302c4d400039200004004407030041140b92441900d0302101c1507480b034295981402c0c0480d260782d54035080e01525080300f40000201d42c4c1d2840510a10821003005428142076039a00c440950b019040040e05981046e002c00115001813401d08840e407204440b0348400c0c0c001d04005000c0c0354500502404027092000c104024401d058040c0025800c45425240281d010850b90048042041c00004020010320002c07543c1d100f08100700003e1215a550300c0020440340c400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 325467212 1250 325465962 325465979
    0x70e06030115030209060f0715050f040c1a040503061504180b0a0522030909050a060f14060c0f0a12031b0305061f03020903060f1b0703020106150f0801 67
    0xa00c2400002c0400d9080c1d451501d0094004e400c1d10000207001074148052404002416401480c04032030041c50aa0b1080d480316180c403071940c012402c9402543d1902d8075039a180b0a0500c50b004034407000342c0d030045d00718004076454211006000041c05403403107414410a03110b500715005c5243c503c07460030894007500f8000070350f980010300b0350481c128040740d44807052506c00409000d004407a03005520049815090710b00140d041948d442a9241016507140109503070481d0f001600310107071780c1d040c541c007000413800c04280c02040c4c0303c1024400c0c008821101c00680c0c0c40c0b0800402221a0094203271081c03900310041140c00783c041c0520214410004040c03001c904444100e519130800780000e44d4107120040c8680e1180d980701c4800740c0410100700703c0506a50b6480c500d46d040b0030020b500000c401a00d801d06000c0311f9005000400500040d05145d20008090032002da03c01a5036800400d201c070901d03200350001e80041c02c022030910a0300303030b00f00d00c000c1a10070200007003008144a040005103894 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 325468462 1250 325467212 325467217
    0x90b090316300507170315060d0b0307120c0801020307050a0e0307210c17060f0403031401060c0b090d0219080906042c04150c0c0c030b070e06 63
    0x901403101c40e1101e10607550744844280071611000005070034844000a503034003450406500c070aaa4481e1901c0d42082d14104c2019201d50840c840c401c00d05009020001200c80e001c58a8400e00f11102520380c00d001d40c1c601c2c0104001c00c201941071080e0b100c0010070000c010b12041c081c500400c400b06196444200060a0f84019980130000440411002040d43e1168402d8a01014000c05407040c071641e030207034400441c81412000452401082141c4c007002684454030f0010700130184006100c121803074615840d0f2000900c41c000840c80c0d0000542010b20a42c003070f1542a0843c501c00d191542c507035400030201010000d0445002090101064009000103481d1901d62283d40c010a11048682800d42103256841022100e0440074006900345940e01005403024040700c40800c200400c0e0048a03017100c058460480003514410014400031030034211007003255030001a404203a505500100721001c81c0103003800707040b41c12014400300c20812808503060241d94143c0c0c400c089518904108007251 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 325469712 1250 325468462 325468477
    0xc031c1e14040609020d060e010b0118080c27090615030a0506040221010515010201141915090914010f11160602040513020913050601050d1a100201090b0903 69
    0x41c4107000070000b4240d600031145441c80901800820845a43c0740c600742e510400c0c1c00c240d581d440300d00020140d6804801c402d86840340382001106a841d100702c0701d4445244607503050003400749810301d000041c29000f400340380d4038404a481e0158a85549e400303860300302c2030302d800e0f0062549a81d80d0007a07203000910301070016000400360820340c81d16420081d04080450070005030800944c1d0070014103000380308a0b4420201c851401980d070f41c10000090860782039030707400001c0c4a00c040c148182e4545000c042c01032007801d0310000070b8142e841012001d0410160380518003680c05d04c06100200080120a03c0c0420700082c020301c082c102c006200700c260303107501400c140d440c0014000b0041c550748542c0348184040c0500d80040c03a1580f2000400c501e18400c513061325009400181450260900701d040001c4964101c00c2088503043c0000000d0481c494000480016901c40580504106c981c400e503822540d030081c0a021245148a0301074042d1123480780a842c190b460170000342107540084100c6503030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 325470962 1250 325469712 325469741
    0x506010509040b151201061d0c070c060e0103060b0d0b1219020402070206041205150c04050a120c090c0e0a050319030f090812030115030603030909020c031c1e 70
    0x71903035400400041140340399450740d840703005c1c8900d40500c034400703210301400790084041c0c0c0d10041c454407400302e081d0903000c0c106080721501084417802003585d1000281c29038401c3d00d0400d0210303e20f02c0048010b84555088601d000300001001c14181c510f55104020510003582c1c8540b042c15841511522035441040e1214580405941940140740c01c0d030040c40403c1c4000c05440c10641c80b4084401c00e41d001120445850b445000c07501c847e05410f0f07010aa10900800c0c0461505051201080c8000e140348181d60320003802c64449400c101c01d841c41c010103000020f508000208001c4002080780428410f640c1c0036001e00407021800c0c0c200071039401d0740b508044510704290680707a5030443d05d1240900501082186100e400301c0c24010a008404004c9001d130101c41e140e505140386101c18002802e00013060510780b82d030400000360000c030204100ca04801006032200801031702c03107003144501c8259030150303a600b203508130711603a0550040040c40b401400308041c40482c2c0243c48200c0722002c004504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 325472212 1250 325470962 325470983
    0x18034e0601110d21110307020f0c1c0620030105010e06040308040e0c072108010e07170901022802060708040f02040b0117040b0106030b0f0a15051b0703050601050904 73
    0x9040f800b604c0e8551264454003034030403a4142501468044400045040548580000501c07660036070421501481d050440060000310740c0341000103c10a1a42c21296280919003000d02d083c030003d40d1121407000c0e046141c0c9116a0071000b000c41e442d40c0240034881c00b00c2e00403200032155050000c2603500741ca41c00003149240504000092039100001030014120300403c010300700c00100c440071014079001e50315040b1042158481405030032031070305800c900425081c4204216801e903000f224082c036000707099481c0c059500c4048d1040d000e072150b80c0004141d000ca40e0302c3d210310065111402043c02083c1d500707030344094030b81070700480d881c0d203040c0c0780600380440012001004d890a54015607801005041442c0580000050700e40a50403c60381603c44c1210f41c4010041540c0500895821010854500e2011407030000096001000d03806900010904081040d00c1640518100ca1040c14071840e401058480c0790703030a035078415060108880300c0c040c101c0005018149180d5907805564007108040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 325473462 1250 325472212 325472233
    0x31d01110913020f071505011406090d03020106050301110c0f0606210a02040c08060f0a0605071e0203060910180c090509070306021c0518034e060111 66
    0xb81100d50500c811165a4200000c3c1800e00100c401028070901c981100c800c404400281034003262816444400094a1481110745640c4c038001103407610841100c00c10f1070005282002c900412158001c2c0380c140d843c19403002e60103824103010348400c0426004541103404c041c036205844007010f5944640200c07240e403040d104c810503810103841f00c41c40c407801c55042e0006900010180d80440768041d0208010500380050346c20b101916840105080d2090521640741060048c62881352190140215001c0012038825813040e01d45028115001412101c0c039040c1815207580380c4182011043d4440d01d02810580601780900010070044d4008001e084058542041c0f034000d454010810141c07400354035000301c0010700714401751080b84d120603000040900c01c03c0b038100403144041c003a080c2d050400c14000e00710f800000100e407901440b50403000d134100c50442414a22200b4107801841d01c04101d030f502100111016a01d5454450707040340f03819103884100040d00c6402195140e031030a03410181902 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 325474712 1250 325473462 325473469
    0x3100e0a0807140d03060914070f0507021c050609071e380a0e06070f0807050307150903141303030e0a03060906060602010c14070605061c03031d011109 67
    0x1040c0860090703c00d1640080441c07031082c2002030105500740883d50b12031052149a60314400e4940041c130300310480d00d99003442039014211000400b280802c021000034080c3c11901c55040c13500300c000d1042084500010300380382190300c1d010308803142001032150b0308001404082c02142031b100c148039100d00062841c18402c0ca082e804401402030200050000e54500c65000c6505000140980a405454661403a00401007000411002c4103102d0f6005108200c01325145501209a544d40b2400075581c40709281b80807811401400e030b01401c0c480d44045403100c07201d020b81104004900c260744035440703d9850000c0e40c6071400f98a1124110f42140d0009200181c040c017562100d01100505800c1c11a81e04c0d44c0c0c2105a803103c1c40122681c03519140b04000480d0240200c40007001e00b070801054150030a03500c01481c0c0220440902815142e4021503807a4a407003240f54018032242500800417005801d0117000b40c507100000c0a03040b450722500808140061142c86400b002003002240b500d4a2101003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 325475962 1250 325474712 325474717
    0x30507140a0e06100c051f1b021c030e12070b070306081e070519090b040204120303151a0901020f06071b02030c030a030f0305010902090a051306051e03100e0a08 71
    0x940c400e103c0803804001c0802c00c1042a01d42e41282a081c200c140000c3c0c1c10ba40d000c0e0b0b880404408123491a40e5050308004d0f4011642141920260031380307a401950174003003100540a09162407001c1d026030395151410f000350200425050340031392070b20115130321240b10890448802d40b0806a43c0e40110840d089003031190409401d0420140e821540b00b02e480704009610000f108640000003403500a040091140302c3c09801c3e040307442164214102458503402e90b407a910100700090425940386070f680c0215008c1c1e82140c015140c61038010703812622030b41d481f015661020b01101d0241c4039540540410b0140010800c2c42403044d40d5802441c04d800001c0d0b02034445d402c1030100e9240c01090494190b90700d00f0407115032aa4043c0e034413440081c0c17900c6000b800f1140c0c10380207842854010480554203894004800b0100c1e00190f07400f04203421103014100007040c2c2c542003a9801490801c0c6640d50800071080003024890031004c0d00c0001c00c00c0404101241c040740601c215a81001140314045030b0118007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 325477212 1250 325475962 325475989
    0x909090106030606060e010801120201051b071e0315051b090303040513020316020706090303110109140105070f0824120307030201061401050a0e101107030507140a0e06 74
    0x115000b9120368498040d038103a900304400141e0382c00911000c96a0007180c050050010540640c016403054000034801d200b10790050f42ca40d804602802e210030340c10031102004002140384000030000c3e26400c28203180c3c05c2d11043d44c42031040801d002008250b032040a001d8095640a1b01e0001c90751700c000280c1e504005002940f500040c880026583c49100c4103120040f4881e00041c0d603850300403507070340810704400b40440031980454000d10860b500441c0740c00550f6094108054880c0c108100d85024184428000346035038894250204c5042c01508102e000742c005885042075080d11401c03c03200300c4030840781000b0840c01c02e150700e004110103020340340b600b0001505042e9844100c401c640d02e158440c400c01c50050b95600d01c02c01075a000e10181940d50942440c0080c5045130b103d000a0020000c0e6009500c5042030b40cc841200d5800f07501084071440300f22007130300c00131ba540b810029108c1e096441440765400c03020100041a29201c20074602740e80b8040d503944a02e0b101c440030300c03011100c41403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 325478462 1250 325477212 325477231
    0xf0e010603050c19110c030a060209150711010507240507020d0e01140306030c120601080601090506090a2c01060e0105030d120c050d06120201030b030102030106020d0c17030f0405070501050f0909 86
    0x40900b19241c5041c002138502d14050b0001607a0b03a4402001d204d0086488805010000024848030001540608061168000910c1d00540f6120582046000c443c82c500d1401d2802100081c0304040b54420b0b00f1451280100e80c00b81c0d0540c1885602c01e49214100051460018952007191000d501a50020759004070018040340d050018003000b150141c501c08040c40420344c0410010403d0400410026015100c900030a10103410a5004907000413805000790303503d44e40300c1920401070000385018a144149a150780c840014031559403900800aa000d848070740301d031a01c0042600d083c000781c200318000042d600d102c0c580b407444003030500800500d424001040300400860580d071035075001c2c4001030180c14100c11240c0300b80b0304c005401c840c80801a180640d006100420000b41c01042400640d40641800004000d5030b10f440302200d04103055020402c0d6010041c40207a088440c0c000384903030300c200101c4003420b441d0001901d4500408490740b45900040140116130b04005c8106500442c841 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 325479712 1250 325478462 325478473
    0x5040e2509020a1e0309202d040501080309010207170709110409390e04090b06010917030f0a020115061809050f070e0a0f0e010603050c1911 62
    0x4250081c181c0e400104040d0000f224407040c11025285420308545a0301141000c2280b03100b607503900000d943c0210b5040e03d0b095010350f044000c2d6161a030704502803988141c00d5094400c1e168410002907440500428002d601c1c1000100d40008004112071440d101600100303089458034089410346141e140007481c0a006150b40011008054011204160301140c40c8548443c200100c800440e5030007448a91440c251601640081c1c000709281e0007184090500c42611003c4202c0c20342d981650318030416002480c1c1606a010f2100880d090350007040c0982c0e410100ea6640c40d08860300e00000048410f061b0801c008800521800d000140000500c50001240094021a28160303003861640b1280102e07500e051404031080e034040c44540a002044001c0280b4140035802c8644424000c001009100301441d0742d1545568083c0400000c0c0070604840e90182d0300c070003c40000c5070003841007a01107414003000c01e004a501d036040e0b6a58100c10080c03482d4644158400310b0340d0740d024040ca00800e000c0c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 325480962 1250 325479712 325479719
    0x405010e060423070c030e1e09060303070803040f02030715020d260405010b13020f091509060309010615090324060f12021203130e0a110304030c02040605040e25 71
    0x1003020740e1103484c00ba11028600951400d010f4518a10660807074030805542070000d103017401e500340c035904152082d541d51185644520121340b4502c40e540020313240c2c14021003044108614030344c2c00c410385c52082c0c0c00d80d022203907581e041140701e009200c64240940c000c01580503406100303004a2448201410360b0007011139505420081500040e201559203135151503508902c1e04081c43d11600302c1e1120300c0304615107508141101d40368050900307145d210318042c1a1856080703400d6019114200c0303008114682e45c1c10b080039641e00030040362084100d5401d01581512209000c1d0390407904907a08501000303d88220300030305401c002d0709141c01c2c040003540d890300403c200303266400c6074010704200e168040b549046401048078000c550348544441e64810000d59422a600390a002e084070141c00b007800c01c1d600c4102110020f4071440e851807848480220420080c550b201d1a4442201e00a031420412203440e60180019560820b40e0040c450707216400700101d501070702e00c5214210351804088298245c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 325482212 1250 325480962 325481021
    0x60d02070f1202150601180306050a0204080d05030f0105061305040207020310020c07030b0105030a230a0b0a0506040b030c010504120309080a050d09082a0303120a0203150405010e0604 81
    0x2001407810740160700100516169080c60b1040c4c43d0850801d003031504030446551030000c00807406000060849844001240302c484658060300c018090800940b203803051101c400400b00d40003100c00580071070f0030700300014039820068200e070a801038914204410304d0900050001a61000704220780511130110351307200c4032030a4030240c032109803258054800305146042c030005640040c0c0143c1e119402ca68044000039401044076419015442c03103040603503d0041e00a82450200040500f0b4144008100a024892503010030310821084404200b48005203050564070342581c840300e80410020001400400c408204020900344a40380400003d620344040c3c9040c401d140300c04441561202030311081d035603003160480f8040d04011000b011a05000d01c4000f14034010a00c8012030701c60042009500b80d1000e00843d1044000301403068003e041c81c00c01e8600035401142c3e1250010801401058140380a002e81d604a806220000d003c0d07499030003c2000038280380c48107518202805079003410728007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 325483462 1250 325482212 325482233
    0x1002070f020d0c05030f1501120c0e01061e0201090b0a1508100501052701060c02150313110409020904020f0604080a0317010e06060a0f030b0d0501090c06020705060d02070f 76
    0x3e201e500400e07085481c050605242c021603c19200342034000403000d842030703c3c0000a4a0440702c004031242201d40681c00d0884180769950403c541c00b0208a001044c4190000d0855030780000c0600f0400392100540c508030708031282c103140146202080404105c0021040e0001c1c82107030404040d401510360b6420340c1d03030326100c2505045101c4c035403541c004103c2413414403541c07a901300004110320120343e100c4019003540e64050241c0800e01210b000b800341507495441a00e07003401080c011640d0b50b414000c1588a070004983d008448601e42c282d8260f1082c1001c2c0203c01900d82d015146800c15103840e070820110240700009660081010b00001512080800020142c1c6000ba1104c001400c400701403000144e60580004045000c02e0085c400c25441d08d0701107880642c401e19100b4441911864104d014206040310f003076002c082c0d5003038036040c400d0640c8100c01305031091504c210a82c1d501d400c180d03150010f03482034035800b000502c034140d00011340350010402c16120b0203070209400300681e229000c94 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 325484712 1250 325483462 325483489
    0x200109060504051e15090102070209040b040203101505011412010b13050307051e030703060606180f08032d0307110607080c1c090803010b0c071401021002070f02 71
    0x6079190001c1c002806000d10241c0e40c60302c5210351000c10300c0b02888026070b807006030308510840c00c6a032000086080c40f085d03054034803040e801030506c1c0c0b060130705023002010100300341c3c1d080e0f1103801908038084600c3c00c184500308810b6240c1203901c411714500001940d2185501403541049030080080ba8007204000c0400c502800e4102a40360b00e44142e241c071042e01e07001235001107002e6403201106206981e180d10040d4104070040f21041003c00c1340f039021070f082020960000b0300d20350801002050380d9410161000d651101d88010411580d600c0998080305981d600c540c0c14190401c01c41c068415640c2c04141d4416403031135281410010f200a0b1401c0c0e41c2d4011240000002c41120b4100c803040c03018803081d41c20405902d4011094104007265072200d120722407185500145045000c4680305a80d00642e44036500709841c03645030360703445100c2003e540c40740020303000d00d00030841e021071010300360361011008034070603802007041114400720900298841e1900b0346105420032540c030010b071360f10071501005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 325485962 1250 325484712 325484723
    0x7060603050d02061f09020306062205030f010b0a0e0417030f0a061403070501110111070f12021f0203070e120d0e0406030f15091505070e06040312200109 68
    0x107007800c0710000741000805030108000d0882d1031200d04005d20320f0401c40c010350b01011070060341c90300d9002c00641c1034071850022440034030601e6030298941c451501e280e000c484082d000e4483c07091140400ca804c03110141d007141c0e4400c02884060000c88840940e9950261280030002401f100300402ca400c03540040b41e801c420801001d040101041c23130b40c001d102c0202429140d02c1101e0715800c0c006034640506003d028100b1071140c0150f03120200135005280c01800300e081440d51010b65050184010840c44803e441c0400414007480c0d0980c80090b052400b040129111094492a43c1c3e03a200a035102402840403c10f100000201d20f5451907000d600303401d8000c00a1002100c2401c01402031802c00240301d00c1203242800070404200350300d46201c14286c0c00b5082c10038511100300907000030152039a028203444d03141c0d4184c4148043c20740c04940666603a803964400780742000e0401c40984107a02000313009072100000d00020380e0140a40040d2400d0554001031860315044038682141c0200d5029500e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 325487212 1250 325485962 325485973
    0x1090b010f0c0305120403140a030207020a0506130b0a09170a0b0106051e2d0706050c03040f060903171006030501140a120804090906020910022803050706060305 71
    0x540e0000030280c00c48001d810200c2a00d405070b10040c006000b41c4c40c50f5070100710381d030000804041c814444982810019900d4a0701d44602c0c0400800a40000310124000d0031100000702c1d1a00d40002039410f04681e450b811030300c1030300f01070b213011454009036a82c5090080c0e08101040b40e18150314011042c284110080202c50341d60308200c00e1394001a4020400c1c003c0820182981400c10801d0780c40d00c4481200f1b0b82c0d0341d440c105400c118411401402c103230411202507848040340361100300614a80740200030500c1075442c0d0a40c1c3d101244001d91b0004c0c41100e42030090800290300e03801c00b80c0701c1d40c0681030601d032910303607050540b0b2104800c071044005030500f19424040e55401d0b1046078050440074085a5103492442c02107035020450b0b00400000c0a08001030000300b250a608035406409000000d1115001e83e240c2000a9040703002c2e11032107140307000320788052988002048001a9800c114007400510041c0c108541d4441d1651300b0740800004001e280c0201303145018840056129030020301c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 325488462 1250 325487212 325487231
    0x6030515040b060901030302060c090d12020106240e010c021306140a080c0f01031e09110a270c02012306151e130909050c0108100e04080901030b090109 67
    0xc0b840b01c0040085204440b64001440401c2d4002a2954003460700c981250380c1c4d0080c540000d0202150102c011700c0e0100d540c00b00c680c0c050741904084122603030003220761045241583c002d83c2e0002c000d2549400620a0b800b910800d40c0f0542d24024910b00141007003465049068204040e121a03030071071501001603641803101410110003040007428050090300c0050101c82c0001c1d02c941660760302a040503160413040f40541703120700689800c1d220300c40c02005170540038034000824640d40c0007440d00c510500700c0c0018043e400713800b4460105045002030101d656100602c0300c014070300c01c6c81c8201150358910f00500e00c40d4a0307024030031009040403550340091804004100c5581c000343d04a03032a20006004400c43ca04102e41d42488100700da80650380c580ca0a00c0c0205820b8170a980003101c82410304111405102c004955092660001c0c0d03580c010b01e95403400469002e0440d032003034802ea2030082000402140c00039002d090100d0052401060f0740c0c00031130014440c1c134804c2c1c100501c40e6a0301e00340c85 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 325489712 1250 325488462 325488473
    0x1090501091e05031b03190e010f0503010503100f020c0304030c03020306070509150a020a0b01150906030506060a0c0809060705031306020a0f02011b02040c05040801051f0b0d0603051504 82
    0x2404002441c2c040410382800302d6503515164020340c6070342c111050038400a110004130500989001c0440c0943c04082c020901c80010541140420414003080d4005105140c003842a0201c9069840c054004c00910030500c400030001c02000e0380052303280c1c0c1d007403014200201007400104000e50140c4032502100303066004140c18024050010710034800c081140000540b110b160b02d40103625043d4a02d510f4440c900420f07400c0c0300243c040141200314110011070305600d100d0314002845a141e0711000d00a807960803e03802c82c2c10036184141c1c81362042c05880c200c50300c9407012561041c800c20a660504601d000861a5508105000c540702d80000c01d02d0100701040b01692002000303144004c0c84915415181c048001c507892001030304000703500c9040b016a110172b40081d01075039400b41041240c40300c0184020311547000b03402220b2040d42440042640e0007503214100c28001c4264000c188420b01d0101162415844807250103071132034580e20008085881070051540c01e03050024210114501850070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 325490962 1250 325489712 325489733
    0x1106010b04051806010c020d17030a05090f0109020108130c05040903050c1002092d030f0f070b1c05060a0801090f0204060b03040f0602090105070b01080706020c0d030503061306080109050109 84
    0x600d603d59100c0300c208602030380c0c045c24110b04d0607010358010301600590705207119207903244607002d03d542c4c6000080c85500201540020701c19800d05044c0c40100e242428418282e898a650190014089902103089016510382080003e4800d003c00881144c0e101c0100c0d0507a80048001e4000c15008a055183c0417002d00540e00130415410342180341900790030004403a00d03202c0f07001020340b40080c0c3e19201215841d4028040d8104001c0c200c1e042d01c0002d41c1c016aa608241100548600a4600020707518003a4800d0b2400305241550070b24550b90480c0c602c20081134000c294a502141900700003030404001e1103054911b42c041c5254030a031005034010300056500b103078080214841c0030410040851610202c50a1a5a001902590b91091007004841600800402070005064a000011108400162031040390072517001c0c2d032458032049040084045590001501064081000600303a240440c05c251500c880180c0000b0ac042d10344d68190300311084654100e9813603559007821014013914898 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 325492212 1250 325490962 325490989
    0x503070c0f0b0301090b060d15050f01020d08040605130f0c06030b010c230709060b04170102090d060b1504140f03010b010c03050d0905121c050403090b09011106010b0405 75
    0x400c07914022140c0c005120501c43d049a6a0341d51a900c2100d43d01d940480b580740380310790002d00408454105440c030a40651103964401c3c6101e1180a08550001c1890040c1030320300d4a54205954407512004040c0100404442d0406d45880809001401e001d444500303083c0111000c1070100d080c4540602182c10fa02c5015051206090215000510410154441c8038021f011085805004c4007200e1a0031119003181d41e005081c2130004c9600f20550000e8012140c09031040c070048213441500314200c6c070070b00c942c140e00800200c52200c04581c80b43c000a0032140007515103540007880ca51000c405400c0340d007081c0003840030b05040c02c200d4030b090315500489100450081044031004000a02040c0210382e0040904c4408036034001800040d910454400740c01605407805684540503408240e031018a07a420910b140b401c05e21010310941c8605449154551030b91002d0506000412295800c9104200d040001d104036040d902d40c0c1c103022485c000d00185a41c5901c4a01301410040740344042c01c1e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 325493462 1250 325492212 325492229
    0x90501020f181c030c0c0b0d020d0510050d08071a070309020315090319030902061803060f151e0a0306051009020c030d0e030c01020a09260a080307020f06040503070c 73
    0xc80c0c90007606000b041c41491644d00d0f05140881c1145441d2003500701003603031700c00d000865000c0b45001503104283c0042c81010010b5004200d90756480c0800c130321844540c01210b030020800581c6000141c01c441c002e001d118014141200e5082810b120021924011030341203000903212400034086080c01c00231551b80e94000100c107142840c0003d0031560304e00801076158000d5543d510f50240c0c8600a5010380a40d980140c4529a602c0d01c04100010244a20803424041e00c203542c0010300345030b00304504500803000325561049420a0708200100348480503501d51041030345020100d501c3e52007983c1200114800c3d08041146c0c50302004803600e000d40d03a444829090300400481e04141e201004440300220112800600d440d0115900d518500500d02c0c1c0d103c0369032001994034a216081001c0e00c08135090b00210010000700b410304201c0406517266458050350050018600048008014580c0289644101e50038400c152071502c0c608002a0303415110b98100280e050207005400d18146e01130300038031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 325494712 1250 325493462 325493479
    0x12006041704230f040207030804061808130617040c030201211406030601080109030210090317010602030d060b0a0e0d06020f280807080403050d090606090b010f020105010609060c06090501020f18 86
    0x1520302600d00e27840200000d0165035601c0e4000c10000006810307605080c3c100c2c120035110038085004004406060007504003142c10b441041d0920901007030030f00c0c0319640c0010000081c030702d0b590042d108010454508031403a1032400c1c612203a820144038181c11480c207194408418203102040c14180300c1d041c1c000c0145641080d00c440c1c0400c0c0c001070030010114440ca000101754025041c1200d031030002c0c18184030038603004400000c020703078000090040c0040d14101089216910300305455030340b099101203000b0904050360a481c40c540344007075108160299001501e0004000d0b120750285c1d005001c9064410a4601d0380c205804800c1d0702c007205605142820155800c0a440141003c0e40040c002001c206002403078000b08910350b006014203035803048061141d04d40702c081c00009015110a01c9000541421807243c0940c8140030f401c0c12100700303446070a4454100f80084614001041c81501c005858140460000300244020110840042d541d1610340a0216804800128640d000d40c4a070410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 325495962 1250 325494712 325494727
    0x319052a090d141c110c0a030308040803090f030a05120a05090601030b0c0913050117150c0f090d2f01020304060807021504030e012006041704230f0402 67
    0x14101502041c0b600070340103a00a01e00300c0d1180d8030f8105100c000f144031403101132001c00410380100c000c117206a081e0f404d54092010a00611030551600d100c094000b4000c540402c011607003e400842d040a60700040d508a00307403941d010351075948014042000500009080c3d040c0050800b201a0019413008050009080c03036040350360341c1c002c180030141000c40311802047d5980e11b400f040b5440d249015000e01c103184950032a0701c0080c034003403141420b108403101588400c203001240100b4107100d407114081c600d0322112642411501f0080000031001410480800a070b50b69601e8003d007103109450740038212807550001d0346200c40d8132503c110070303044148054100781e8010003520141e43d13682c64140301d541d584c4d6400324907000b1581c00450303101800c0014481819441001d51030780d61380a881c1d44050100c801e0341541140003481c150692500480c01190011300c800f4026210304820140840c109520303407000340c0100d10354103e2010201d141d012540800d041081d0400c2045508a9045040148 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 325497212 1250 325495962 325495969
    0x3220305071403150a02040f0501080405250e090f07120b0601050901031e0f050610021c020a0c06020106031e02030d03050a06080a1b050a0602070b0319052a09 70
    0x2007030300500000c84000246001c2da62400c10000e81c100e0003000766500c0e5420403090110080d4018042c1c0c05d004001c115020038a540146032a81c0590b80c000d00074070400c0390105180110300b01d070844009612a03040400510304042840a90082079060060142c1c580300d82641c84c5000d07400d134041c03405541d414522401040c0300c0307402c85503c490203003082d0b0303551060100102c000700682015401d00950f21000e000c40445960b124442d04c844401c03081000b0740f02c1d50704210000170012050030060707001040103c0c0403c240f0030304d40c030910840c2c0100c40b014442551503c0d4030321090341017003005030356410080040c04401050803403406c0401d08018000c140540200c0c0e140d2000704418010705449102142040040745d000e400106066400d5510340d624a141c40c8040f0380e401290000305640004020482e440c080407008100c43c040c1d001884040d01d4161081019013008001e00b516424803502c800742c0d458540101d503c00c41940240c209030405000c10075406040184104001000c1441003a00340d84 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 325498462 1250 325497212 325497223
    0xf041707050d0b070203160b040b011410030b040207050f1507050a0801051011060c09090108070b160f1b08150c090d08090d03080f07030917030403021e03220305 71
    0x3a000000503900d507441c10740603480d40c4160040d20502c0c5030340c80c1c4224184234282d011140100d10a042500d200d903620244c090003802002115540318125003c0039408500950040e1021100070700058100301c01071f219035041c0788800340d004844c1d0b000040e180910f94411401c00350f03c06103e040a40c208034000c0d200900c070174814000c5031701441008003034600541c059a03441d10070501081c03c9503020314190f8503021003500980075890045200380008242c0c0074001c0390220503a0700200140e81090004500b103c032114003500c2c01c1d03815580c880c20240c003045c40d01e240401c01d5414000750403041854081030034a41194080e203100114444010702c41c120386002c1c03c4400c10f000449940b00c200d08242000145d0744156018513501120698081c03040580188030188640e462810012203607468010540c140c581c4494010f00e00f40804900710010401ca2000d980c0103030180c03044134170070401c03050100512410911400c1c019400810f050140c1400c6202c840c101c0c00300e0100a03001a0314550b1280c2d46c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 325499712 1250 325498462 325498489
    0x501030b16020312071205010b0408070f03021c0f080a02070e09010b0a030b0613021603020d050c0a061815091b0509180c0901090606090b1602040507050f0f04170705 73
    0x40413500041014948288694500f40514440c00c20065030769a052880355841446003081c00d000b090000180c0d01c084629074011240c0183c44203800c003040856600c901110100d045410503440d6049401084d090400b60115450076002850441d00307186103500303103d9000300000350907814168903a405843d81004001241d41c0503410744955181c010020780341503221002002007a10114440009859064200146a00940a80e00c0c1607035140000c4620344034461012440b607220500400015110354064006075030100100d42c404111562031407405510342c0207220040d030b111524001440007540612407008003000b203001069103890007090822400404140b41c018808000d00c8800c0c0e07042c081643c0200b802440200c0d00d40c0c4415034007004003000d001c0d0701c00141d001030001c20301421180880700c0174461034950120000c41542000043c2000a00034400c0100611901070f4058140e40500000c21140c400d56444900340451031840000714000c0480c80d41c4140410040c98880000c40b1481 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 325500962 1250 325499712 325499737
    0x1080a030c050316050606100201050c040b0a021005010603021e0a0e010315050d0308010e0c0f09060a0c05032a070b03131a0a0c1d100509041e0501030b160203 70
    0xa0310403400d1807415030050041c0d0401101300c260706401003140110703503d4428107046894000400016000328225a0120740082200d20208414864a0041e9001c2d088590240c4100e4405c038825400403010307904207a2020010a4000ca141d9801001c5c040d040c401c0816021121400c014011100030400350501e0081414503554440c20400c0c0c0400880000103030601a00c001d04034409864002c041103824866000c01d0b0b103d000c00f04240010300400c0740c541c2c88001c4003580c1002c01000c2000074540c409002042401030710030f9000300240307003070003c2d180038501e0b01900004214080d070304c1c15624008031841d00c82d9030409441071290031402c0c003c1d650411403141100c00301c0d01c00342c901134200c2040c0c1c0b83c0084d0600b20b801d04003c1c0c0441140c22500d0b040726240d5440f1103410395901c4e95201c504440034466804607070500f1008284d803003100a08590b681c01400440d00200c08503c0c001a81c41d904a41e001c1c181d11140140107008076030169a4109201c001703e004480c0110b10000d44030302521003c45103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 325502212 1250 325500962 325500977
    0x6071e0f0c06090f12020109020d0803190501080601050315010e040b09030706061e061d0108090c040e010218062b1e05041403090603190608030412020f0901080a03 72
    0x10141c8501e02580035264802c00821100c05181409074050b0a015011210300540111280c0340078410300a502443e03902901250110740207a60ba8882c9400086c003090b000c2c62a03c0e403442d0301c3c081c0c0740251802880600c1c00340010b035050000f8541020b000402042e84055440e0041000714542643c190b07000750801c1b6505030a03191160940d00310f20508101038038042c00e1080106010b01c0181c45840726025a030074038a05d141da0b0307001c29110700b16504150140140d02000c0c010784ca5000d1107000b07a00501d02d90555140004081c00130f030441d0403080101150760750100310103000c42d014030154035102000300c9401c3c1c1400c04828401001c0b4020b40e541c0c0404840d14034181c1d020f4001340e00152540304120381880d00b200da00002080040001310b0301904c80d491000d0140c0ca0815000c800c40790511405030106103585d580d0200700020030f40f003a0860b2119680c80f980040d460030140090310282200c00c0320303050071781d015004206024044d425014811807600004004412000909a0f4450341c507040c00745 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 325503462 1250 325502212 325502237
    0x18050405040c050a06080a0513050a020405070e0a0f0306060b09090a09050c0913021503010501050d021806040e0403030b03011802010c020d0204180302010e06040201020622080f09010206071e 84
    0x6155450b99000b60307048001c4480115000d5004401180300b150744070b00400032903071105511003c00314000c07800f4042d0382107010420b015080680056521241508109103545203c03804142c0c1d03907540d40d03c0029001c091030700500411202d402600e000700403456000d0b0910300302a001500401c0064820501d0550780e640c03000801800f40003000c49860b00030700c0742c10140b0b00341c18420b10144070402d080b442a01c2954882102c804c99000340c0b816135506a40311030a001c0070400c458001d6220844503070b40485c0b1280d0243d482d039230304030040c03018028042149141d41820b24001c5d058500c0e8000c860310076414801000014980c0003008202c650b0240391001200c2024000b0419030484503101030740041c204814003d00b46a09080300080520a030b000300716a000300711030140c0360700003510000d00581202001c180400c0c0c1e000d4903d01c40c0c020080810101c5100c5039030b202d005070721500c0040c4d00060082000011036805005d055408859800e01856070035210300c003100616441e00c03544052008104444 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 325504712 1250 325503462 325503473
    0xf1d0d0c06111b010b0307081e01021204061b020c0f061c050a06080c030a08300f0105040c1115131712060a0b070f0609121e1805040504 60
    0x80400751054014a0352100e400c1c0f9180c02c00b01946034070046940c205107001145040c0051311104440d00e5a0242101c1c0a9400145100c40006130310001c1541d002d00448901080410381c4a014074030515000501d80d001040c000c1c1c0c070035410103d500a540002c001c031103040e03c4844904000180403a01542c1d1203c148030b001d404501003060712481e8902d00010007076442c1c0240e0000d4141c60070502103481c0246070100305a51400980001405990144040504594000c0b803d500e0300701e91034042c2c00c00d00703681c3c14090300781801150307104080c4100302c2c01000ba505003442240e8400e202d43c0381007111000921060780c1e03138200038540604a0150040090741400503400c9001c3c00b180d0105500108020138484100550015110074a0300660200070030054074140a42008651980241030f04110300741e00c1c0c07901400e140d50b0083e1380c280c1e00c5000240004800c14011000c4000c03a803500d00007090035681100f60312a00710601170a04c11000c10200030704541030b4920003111400c9a01194a13034072031920 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 325505962 1250 325504712 325504721
    0x906050d02070f050a03080a020a0c021c080f1c050103020105120711150a061710050c0412060f0e01112d040617090a0b0c07240f1d0d0c06 61
    0x151200c55600f603144200100807604555040c02551034004507100c81d00c1040880c412a01103d000c504c40384001c10040c2040741000705810b03001e200c040541c24240c2c5401c4051740c410300080c0c1e111000040d1102c441d8490a04035090428040720400c199070440d400a071640c0b1945840e150441d40e03403400581001e2088004619071001c42e01a0b66024403a8040441070140c01c0d58041c15040c00d058010917000420f064944124800744001c141080101203600007d01003d0b1140d4100c0b0740801000c1000482c100b0100c041910030100060031030342100381c0c20101d40d00280102466410050b809238981c03259000d855420800382c005c120400c054001c402002e0307010f15523502d4100e4010a001070f00380e402c0350b02c04458150414402030290f41d940e030810b880c0c20a600d40107113411424008a661304441c0c41c09070404c00c1c030603141009000600040d8440000c00c10707255280b5103407901c5580e902d8030502d004840d008000440c60070703900c051804a8640340c592030f10090007000b805042a80600486402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 325507212 1250 325505962 325505977
    0x12080702120d0f020105010503011407081b040b0405031015050f03240403090605090310020904020c100e012009102a2901060e18270a030906050d02 65
    0x40b601d0303040d501680074201031518090340c0003551a2200000396820103028843c0c0c1040e11700c0c0b180c0307150b035203110080c0c0da011406040141c071040054008055111078200610203800515220342e1210701e01800c0510301204c8440c00300b1640d0070608544c1903011015909016258110f0303c52210103c2000030a2400b03075510543c200c4840e1048504915a00008503135024074000d98909035441e031102e0041d1814401c011010360198000c0001034080f8419902030702d40c60200502c05072a00d140481218900034a45105c41a0345541d510300300d10886003486041d400001801ca01c004000000b050120a4018000d8050003401ca0060116210b07205e9084445240c906064035289583c04007400c940e0360030724020443d1442542d482079106010000d11120400a1480f903001c0c0aa084c80c500b26041203200f10b07441d4101e09042c1d0b0f030962580c6045401846001c200c4080403081d00c0e050010010008414a01c4104e500700350014400f080d4030003145402d403031050a00760354854141c3c500d0002440f480d05c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 325508462 1250 325507212 325507249
    0x20705030412050114070e060a0c051c0908070b070b0903070c0e07030f140a0b010905041d070b130909030c0f030206040515060a17010204090e0d030e03030112080702 73
    0x190205400c048800c0021260703019030000c21000100401d01d000c8001e0550303010010030001f0000308200d00c3c00070010104680c1c1c0b4913240083d5081030b0380e0a13180401e45028030303402c516100440e01724181d116a0a90080200301e0003000e03450716080901460780301381c0130003400b0b244481c00001d19851003002100c19841d445002a8159a550740c929050700764252030450000381800c602d0480c031500e0380603040e07082c0032450301c40a0549415036480f000b171007186000e81c1400300748000082c4079680ca2258080c0110031403500381d00403403c040c12600300a410381008035122000c0c002035003040e55600002c800d0724080c8200080d18042800c00344d512006c0c0c000000e00000d10704061a04169010950500a80c171074004c4905500744480d0709489404200c0f65250080746082081040d109400000c1901540c1d981c00145001e0711030544038251181c07500740c0320907a803220b40c034040c109902d40b00e61043d000800300a541594140b6000c15442d8a000c0da000d0020328001c03511805550b00d00c550002c00300d4402c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 325509712 1250 325508462 325508467
    0x20108101e0608070f050405040b040b040c0201020414100801060513030c03032a080a0c020d020301060f030c17030a03020703020313090507030e0604082b090b040606080c010e0f0402070503 83
    0x12101d04840030060049100190b034000c0411102406404803c1403031045c1d8554600b4542007005001c010856070660303d41c410303245e407005103054803184100740503400b00380e0001d6500c5050142d00c441e004440d940312406400c946400b6801d50350300400707503030549655103485903803910340300444800c00006030070190010003041c06c00000c050f0480c9461103049280c007580ca01e8603402288080791140c08000c003800f414030400c5074055203481480590032491004140006021345500801c1c211842c98001e8941681c90320003e209100240500c040180011140f00c45545c58a1038a2a1a0301505490344103054000c41c20208041c000d02c10380b0100545080021b044558500c10080580b20030748856000c00c0c907264a5621032600415034522454100d41040d01c0c2c80c1c0902e080c0000c00300004040300c041140051060404250f9010340401e10b40904075000290030581440c02c21640d4036400002260f00855000d101644c00205214010404881c90441d41036414007190107031148000007409400300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 325510962 1250 325509712 325509749
    0xe031609021305060306030703141e01051005060a02030403020f01050f21090f0a0206030403210b01020d050742020c0f0c010512040c0f0e091005100302010810 70
    0x3990702405910100348040c180150740c42091001e10301c416901c07603030140c012580a2010804802c04244020004421144011070006001d0a0380b403e4141c2c4c000a079455800303200380350448900107800b4020860f00c2c07904d00a5040c0000c5e64912032440000d010f604044449402607010303c0070f59400c51400d8070429a6440d8400e818014400d15031401240a82d003600858242c14001420b002c3c40c20000c001405071202640821030141c1006004804000d54840c0400c0a80e9004515120011401901144050a420029007440b841140b07443c04c005092120102051043d100d071030341c0c0110601d41c100e000800c05a555a200c01610b00320390200d21460100301c034041550b0052200c80313100020380d00c180d400030090903210340702c0d2081c10340080d005020001490881c0040300b5040f40c861009043c01c1d07542d41e4020145040c00d64048071810394440308000c0048424025220b2807180c4c880c040003103142c90b04110240085034000a41000510800076a5126114183c040504600185c2041038102c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 325512212 1250 325510962 325510979
    0x1502010b1c0215030403030f0e070b070825030801030507050105120610200d080115080f0a090516060320031609080f07080d0e010207030201030e2a040b090f04030e0316 74
    0x4031182382d01b9400d45052106803402d40b0102c0c070300098600d2240514074280d41c0b5110305103190400134420180c00050007a240d205d00e4904000e1000a00c241c85412075985107080090030032003107501541c1804810132203807012001450b902a84200708580e584621030700e400c8100c0e01840003d14440070002000c000b40c0c0754150005800b020392103590340d001d80c030703a807a00660001d030b80c45040c107400460441804100b10b80075041c00d450740721840321400a140d070f40710340340c5516202d0412440801d950f0020024085160705d401140c103a0b900008079281d441c01892850411880020405006007941c400301c0744aa0b071141015000401c003080485560046c40e0650503200c1d03584d4419181648240c100c2c08030380b00d005207454170401c1d50580141841500d140c0056010340002010704400b801180a16090303031151510071842c800840d0309000c01002c02d2005d020841e007410700f803140f050294408000000c810445e11030343c415807500d4004609640c1d1400f0a251081d8907110302c000800000c0c0210301030b45d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 325513462 1250 325512212 325512221
    0x2011d13050a20031314060106030c0305090a150b0d0c14030d0c0302150717150a0614070206160b0a0516140702040c050d0c091502010b1c021503040303 67
    0x2908104000e1140e0300788026641c000b90303426a070700f410b6062000480c03a884100e010200b5a01541482d02e1060f2000742c410f090a409802031030119a4414614100680c94030406078010491402007030044242c0d116196040711011080c4241038456100003140d4950780014003059901040c0032004c0390700c5030340c040582070041e002c090003482424141d104031403140750550741694242d006041c000109403040740309010010013030801d01c91108040c0f04030712009600c2d14810181441c1c00081c8114280800c030ba40030050b03020741c0401007e002c44204034031b036800c215403400e41d044403c0d1365a034180074400791500341c0c150405082d9509800400100c00301c9604060b205194000300d00a4080706d40109452011023292a01a01034003402680014240755104034415110303414076178180b881c20700c1c0e0081076540d00440b41c0c0010704444001c12004001c0140c2902040e001e000921a900c6c00b680030410704030340c1200310004010150710120641d00c03000480030b180302003d40602d40d40e10703003414060043d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 325514712 1250 325513462 325513471
    0x6070b0105030c09060a03030e0402250312051605090f0d05160801090309140a081c0206101a0d0609020f1902060103050d0e15070303150e04080702011d1305 69
    0xa00502d5030f0f406107840c21180d001d2080340f008144800c000c4c01c540701221240c03010320025800c03c1d400c100081c40d07658403140504202507000304d1205030000c00d05d0300804030201c49a045917040d0811041c0114440b4203851030480e83c40034030b440307a11258108005600407500200f415041880150940203004000c59140e6111a02e242100310243d070f515040303800c80c0d440c10310103000110042802c1c00b212610990000c1d128200400d8000c0060701d8821235230519074144903401a100242c0311034007100b5018041c40d940410000c0382207c160b4074201030745048210080100295142c00145031350203102562040000d410011400c6403035480151b401d0990ba88030b940c032080c51703a04542d1151203240c400141681660361050140001c80381c040800c1c0ca040020b00c8015610060300503d2100716a1410050040d450090303030080346400c0c2145a01903041d14035044201514034190420000c21000700888180980c20702c1c3c0000e500d0307600d2111042000440041541c4182d44040101c0003507850380040303025 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 325515962 1250 325514712 325514719
    0x604051018030605012301050a0f12050708090d230a0c0b010b04030303060923090708120306040b240f041e03020405010909030917031b0a0303060e0402061e0906070b0105 75
    0x40307064840b100c0011406c84501d00c0d0024034100600b066692007900581d021051600300b003003521688001c80f0702035030b41c103ca020780040c0f12070041003651003003002034485201032418420300395152540003600300c0100916001d0070120000d41121803c0c4991030150130a50400c030410240d5840d5446944103600c02d200540000e4207282d0042070300081e5104120030007000c00ea40d4409a040ea07200380410322402801209103004050b4001810b0300c050169a001c0100740c60015601d10381603040200302c03442c494089014005c1c20341000f0610541515101c0084450203c1c152106030b81d006202d11403182c0d410100c201800d10710444030746210742080788160303403003210140204c0c2e0701e801401046030481d13813001d1b0000707140b81010002c01803590300a450400c3d41c9800d583c074001424000c8290640017200302002a0b00c4010000281075042c854840501800761504240e424290006002d40c002c1d44a0041c40f280c0c3d204600b90180b1007a400c49600d98005484036444442030f0600a008201c24820a0300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 325517212 1250 325515962 325515989
    0x10801060513020421060b100c1b0e040f050c0409110411130515070204050117010f06030206090f010c050d0c030806040605100c0c03080403080d1a060405101803060501 74
    0x1585615000b031300c065a88215284905a08100c3c000040488408081d02e00b1551001c000e207040e1642034070b21000c000e16440300c02c014002854000c000254090350b141c0020408401030000c0160b002c5801c0d000354015188001607c01c5080079400c241400b8040c6520030314000030001088504142844820710844082200e5501e0010010951048032001c60a070300d12107000b806145041c003450384c0510001c0c03440c0d505000660340800d00710762080c0c028160b0220741c4490605801c0090045905500c0d25210502c48a882d69012070418000ca10360030b07204120240c4410410392062181d241d109402408980500d00c0c82d241c003034409076200c80160002182603000401c182014020700c42110006407a0761030036404500d04a850301c040c40300440740d10858407000070104000710041c1002e103004821081c2c0e13400d80003d092080354540610340240b4141a880c440603562144c090342d040398015a9091840b45902c00304517250003c510703000080701c134081800300500c5115800380c0e050f58410302e900c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 325518462 1250 325517212 325517239
    0x106090f1503030f0f02011d031903020f1c0f050411191809081308070608092d19060b041805030d0b0103110d051006180909050a02090108010605 64
    0x1c081d0324440c04081c1c0403410100f80103c1180c480c0020301402c0c1454800011400380c844640c080342842c1c0300a00c0d09943c800f050380343e580f1031419842c014640c0c0d54101146007540380322a4010034060003200c60000b1185021854003c80250081a89000c07800700c10800342c43c2618000420800c95148507000c6c0e40e003480c50080e1b14914031104020307a06c1c030b0f11070144524026141800a40003285041782c0c52002030082203810344100c100354000d40078000150030760314203004004104040003804401564819202c0d00ba080000e030803590300092000c400c140304401d80b034480c10314018001c8039564072101060480d406205880e80072250782d840842d0184256400a00c001c18000c01c1064050031907041088090300034107440d84180d0312454107040c045058446029000482e800c4006070310340203a223070700030414403906580140003d03180358181354404d0f150f1389a6801c06032000e4083c59001355510b15004042c001e00300824000350760f009088244540c0c6415000b4060901c0384902d078041c030303038402d2101c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 325519712 1250 325518462 325518491
    0x40b01180603020a090c0504030b040c05130b0915010905062d030402031902040915020c07060239091003030212070b0610180803090a0801020a0c030f050c0106090f 72
    0x52040b00d40003800400c009041810b00030043c880000d000081c0881000004005444919024429070141801c21803480c9483c0038030a000b100300b443c2c0100b151a00518851307070380c4d85204030383d0001e00c40c24004501e00004001611100d0094008a40c094008103507000410500c01c2c8411660103072884c0a0f10010003401041c000e400140d83c000d42c0740e000a003c100d0800c0f484181c130200140010f1011174032200e079859040c81c4144202c1c06440c0a9000519004c20500130468000109070702cbc40103002031004d40900e1207600700c3d26000c0e4032282820a40302a0b0080b046409018481030042c02d0307070b40f182884100c10084010038402100540030b841c60315502d0512440994161941220b0f004025540325401c0010709403003030074103c1c28000070340c0802c0003408000c140340000d000120011a40c2c1c480c00c404100c0700040c03944c014403c5070300411110803181e9200c04451341556144c04c1c03d41c0340f6410100e044d200d40c00355441c4500c86618040b4000781403c00c0ba0808260100071038810000d40d008140b05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 325520962 1250 325519712 325519721
    0x403020a121214070605070c030237111c1205040f090c020a150501210503122502011505061204020f120312150a3002030303040b0118 59
    0x40c1480d10214403645015001e10b444101c03120800400f1480d14159036074007000c0302c10a0b1544000102450407560401d40c04201444c042d503080c032a640594000d2203081d5400c0350b0112412581003013a03104510030003d8100c14440c07280c8005100d964020410741c0e0660f03101204040035500c5506c0f80320030003149030245085800780d54604500d411a142462510310144c0a503002500c118410b4070f50200c0455558138130101200800d05002c00c09514242001c0c54042215003440c1c024419805600c000880000c01c4855218108840d84060350320030744900301e41100742d89070b05115412155009105541075004010034030048041a1440740c5600501406020b5104980758080c11640420b0140c607020007200c4174044001d0442c40081c04081303034103046801000c180d441c800449020301c208595500e070301d40d054010940c0e60303205451400c01c140782c0009008805013482050800e81c8500c1d07141044100c0030041c1c02034212687c034101440c04e50000748003403242c03500c0341c0c1441540f0050001140107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 325522212 1250 325520962 325520999
    0x41803030528110403050d1808072706150903050607090b070b040512040b04080601090b01090317070804230103020903120f041e14040b15031e010b0403020a 69
    0x480c070640450b2803105402014021050700640c901808008006070042012610310b2060766035905c204090741414448140e42c030b8000034035507004032101b8080300a075181481107200d4688400744161081d0008800140015004032801e598a5883d6003e4260808254402c4910490840c0c2e01e43d43d034400211030b000303c00c0c041c000300100104801c0d80451401f40d0410380050103102a500c801840407403442041e481680b2000c00c101000c5401c1003190814440580100143c00c020b0080e9292080000c0800700503000042c9290243c010302030208054200340e90410b0b500c5004c1903a0b40e0388412541c6460f290104425500b501c641050088a502c24026180440b90180085c03070013480c1c45d0f107140740b95001440c03040c8015000340400107001c00d50740100384148080320701c001c40e20360904440d1400e070132280c519180120700f0004100800d4a800e07001c55903444040c03981907103035110440e601100303280082c0300403542c04d1444004100042d0302801401180c0c400c0310b0070200e8513079034014400c1c007011100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 325523462 1250 325522212 325522261
    0x41b020a0302160e06060307020f010c0908060109090f0219030602030403030e01150302030303010605160501020a0f1403090309040b011106040b06030d1d0d1406040803060103060b09130b0f0418030305 88
    0x60101c0c1446c2080800345030804500d0055401860448840600311260392440348006441404200803415090209a015000550307052026000d2901e841001500b800c0000f40030341d06002d50300140900c0405420060f42d4000e4040d9500c0c10725040085c050080030000e15103c0d46064150400c0c2e2135032040c0401100d0f4054091410350b81703082025900760b004001140d0300001d044c0b24400008070f00388000c000009458403a47c84080b140d4600070a0701151859110303608008100340462110000261030b0729101c1190045201d025400048800981c14044e8400078072440f800d0004100320607180e68032a510640494400d000400c0040340e04000b1407414101e003003041003003098035003440b2451414103400703040d400343c1c07a0341d043c1041031074404219010b44a800e400710501440d0b43e45402200e00030305c4128500e43c00c20500000003800428892644413005544031502c4e46c0c662100491001000f1004004108065240441c2d08540000da07404400007803030440020907007040502900700310b41004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 325524712 1250 325523462 325523489
    0x3061b0215070e03070803030f060a06020c091909060e060a0c0507170c0d03141008030a0f0e030a0b09010f021603120f0e0c012a060b041b020a030216 66
    0x70340c24095000280084042005001ca45212034800f000010001c044090056589250549403a031418002904d014030031496144100325141d40090742c0e15040608031180c45064540510810303042207c248072549103810f1036498021701507260710101c0e0b440b00d41400d0303a40d240d461441000450380001c4191000c12014481000841d805120342101c0c09040024545882600d134021844c0031284140a00040c0d143c60940c0c3c5035080007208507800100c4c0d0709a42e0701c0789041458481c0c41c0e0103401c640200f00420130320a03801a40c4038401f40c1b22000c0300a01545c901001b03508210313206880803035240040e5030800b0000c000f00b801910850380e8540710606861081c0200303941c1100d80000070419820403c1c3c0768000f2a000400d40c1c03080c07451041c0e1803c000c1a81c15001d4001400b900048161032101003404260824540c0c51030301840069079108800250740c02400c80001c00034035150141c1668455417041007800c188d0005440303c059402902182c02c2840480f00c0701c01d0b03100b99030080020b501c101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 325525962 1250 325524712 325524733
    0x20f01052a03070515070e0a03020108010b0904110c0a0501150b0702090711010216030806010206271c05040e0f060303040e0a0b030f0c12121b0709050703050103061b02 74
    0x1c03086151000c1c1c000c040e01d18203038543e00e0341840d1511502d40700024104c500c0a01c50000d030070000c412010442525985a01e515640001e080090144070b41d404c007840000b044861507480743d0101c180150304038060b54455500000554ad00d10960034222219031034450300c1c1c506440042118021510854211882c09009909000f14080054880c809100344292070401307480080c006040c0d01c00d802e6801b9484030140d42401822140058840703419900207000740712004038200b1500008480c085c01480f06821041c0c1810b01d855000c4041000e00b84002c203112518076400001081124800702075403002d510380c07040111024200340c4240344c0c0b44d4000c02c4204903c10740412803a0f40000034410014082041001083c200a4000c0b5044e0568100040340400303440c290100384d0f84400050300528100b031101001c50010300c40c800c40700014461010780c1c0d520800741000b23010040c241203001840359080184001d13010303090038041219428244001100c04800c000660403490001e54001d0010108 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 325527212 1250 325525962 325526017
    0x3060409150c0912050706110703210807080702100b01140f0c010506120601091d0a050706030c0c0308151906030207050d112a0301060305030306040c0c1218050a03030507020f0105 79
    0x70ba0f4400510540110034000005c0bc544499030f0303844010780001c40701d100c1c20075840203002d028003c20305024000d100045c084800c0d80003684c412081d08182000034145501001601ea040c00c22070345082140d03001501140c45403032140541400d2150b00000d0000c1e03281c3c04108258000f1305a00702001e54020300040102c07000d03a401c903c41000010785242d41e00c0000651450030160480c0c0c007130790107500070041000700c15850321a1401e40b040c20700c1c0042e00601242e81c014520387c0090070340510021b2403d41c003941c503618188901620040d91030204046030387d03a84050082d40016a003501d041c003500d8250341009000784180d040400c0180081e080300c10301042c80d841c1e046110441d507958910407444038074468500344221006140a400219100c1c90041e00308000c0d1401c2e0a181400c100c14160034100041650403881d0190900b41801139206010715540410a05d8135403000307034480302c118000810706400000501c61030b80207070740c030a084c2c461020040d2103501caa110f00183d25556003d11090340030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 325528462 1250 325527212 325527227
    0x601050f03070c0f0b040203060606030c07080f0c070608090d210e0109060507020304090f1107020108191e0c030c0806010c021801030812090c010503060603060409150c0912050706 79
    0x29501c1c20002c0200c211a202d00140d0320003a842240c141172190244025031070700b0050540d010608403001c52851400314804174940c00b810b0b80040101c1400b1801c12500100d42c03080c0e40320040c4110031103503244c1c0d6600000701281d070b0503509803006014101d03540c8a0306100b940811155400800e002ca142440245c20400400c14008591a29540c9002c0180051a81d02840e0b000d005503500850311581803408543c111a01140c8581441d46460282c02a0301d40d45019140c0d410f40900740f807001d55480013940b0320102c0c052040f0310794043c03400900020302d2040f00051b0959100e46e4004000e40740101105a0417640c0b00780c20a070108400d1380010742c1c103611612031040808d1010341041880301c020311444440b03000a0300101c4425201003841d506e5400b4101040b40e020a4140080070708543c0340707001900c240320250400340160340010000360b0079100ca42080759031641c0070f107000351441c940030346800003881d00c03442c11000074903039007000103900c5140041d403890345400c0b9020f0007010f85001816030340c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 325529712 1250 325528462 325528471
    0x1d03280206011a1209100c0302180f060f030405211815040b031303030c021f151502060a060504090206030f1b0406120501050411031b0912010b040b06030601050f03 72
    0x4079013045250a101011445180039030040c0c001410a1040340000400350340009100000705881807008020001c07506020b2030b40540c003580c039080c0403140700c80422600d1042c00b5040d40c03d81e60010a10041001c005221400c0c055805c0e07035160245102e04901d1003612a21000b10301868040001ca1001d2821035600803034850101e450518040d540c04421206801c120b0313094903e282084806000d054050091070303030203000c510207422550400d0582c885901890100c03900d605035950301c00170f003051070315042d03031701410040e100100202440403000703540380000c4490000c05d600380400041c40e800c0c24007402404d181c1c0142401c0c119900d02805042c1c0381c0008008100c02032240e5004111524100020409002d09590794411950001b100e41e0668030182d104501451400c2c00b02090b14010b0020707281c1100000d4408000e01e5054450a16030380179001c1070035071002d08250012000d480541c0000c041d41c03010745080c0324070604581041500d010444a460205400300102078503c1031420080d68032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 325530962 1250 325529712 325529759
    0x1150e0d140c0d0309050f040926130806061809121606090309090507051201030201120e07091d0304060e09181c110105010302130b041d0328020601 65
    0xb410b0700300001480f2612036000c00c4d40415081c09007404142004598400da0342801d440501000042e40e40c0c03000c0d2118014003d0503150620342a940124801000b214410a040303100b009116440d400400e440e080140c81c01c0c3e1240340e060002d044000d400e01486446040d600c0c010b40320148105c14100320aa0080400240e6003500e07200150000e0090310417002414082e03a0388140d924149130011048601c080c025201313000090048042c0e9102e1812440e042da031f070a19060b0700700606488544050980c1c43c5c205030440c0205600403a2007a07256103c0045413402d5105124140d4880300740701e07201d200f81c0c0500800030f900b100d501c0f900c0342000c241080d000079400341caa14800c0b0507081d41900b070034041d10b24282c1e203428001c0c070348500c0d82d80305036171406c040700d0000200004c1d45140d00003003101040c0f40c600103801ea213403110368100380d660384e120350048101c0310313041d07000c0301c80d0600030544a9000c280030b01c1c8000194500c02002c0060f6208181e403020594004048507400e00d1002e0000b068020040101d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 325532212 1250 325530962 325530973
    0xa0c03110d031d03070c12080c0601061d041104030209090708010915050f10050103052a0406030e03031e0a0f1d010e0a15150f0e01150e0d14 62
    0x545820800881c0d1101400b940c00182004580c004507807003402e20b01c07180c0015402440100d002c282c81999900448010407869601d900740ba04d802c003c58010034950750080d01412000044240c1c00c08840c00042074074521400c560100300c0100811240310301c0c14592103400c02e00040c001410281032058115140c00100c500a5035982c11407400d43d11100c00c2124050030054880003171070f0a03801010b40150406801190505c4e01c808030b2103443c4140c0c42280d04150f1614082205e07850391101001c0101c4c0900704980d80d400e600040307484e00b5441807050f0340000b8a0690128410030001c01961301818490304864202000d044602403949006000c1c18200c0355251300d005400c2c003081c811090a000114112100c0140f904200380c211031250100da40941c02170200000080c040803c0c1025858041c0c4c030000f00c20101c4180d806041d00941c05c044c011a480c0c0c480414814440d46440d070407109034036642040a64001c1c0d04560b82083c080203640c00c000d0181c410301c0010020009038024038010000c891 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 325533462 1250 325532212 325532237
    0x8030a0503063c010905090108030d0c0519020303040b0117030703050903100f050a0506010e010c02120106030b09070e010f23040b0402030a0207060f090515070c150c030b150a0c03 79
    0x6414003450031100800f003400354101807555810400700c0d4010081211003290641c54500040c1d00c911400c0e03201d4002e503640302e140d02805801a429a401000c14541d81d03110307489100b501070760302d5200340c03001c0c0c8582c02c0d04000000c0d400d80c07072600c070750392402c80300007660504056540665039600f0581c3c4042e072502421a4401203284035129150ba07460700160003003002c1c20521302980c1103e00c00b1303100904218a0a0319001280d8012240880096051b03490310b00c440f21501403d8010301e000c0e00b00a00103410780041c094041e4002400c00705907600c0138203150f40390744d9810068810081c24030a5241404103080c2600010741280300d0080184000b070b20201c0c1c046034010008040f80d00441c1c43c00344186d400304a11090001307a00c1040f01112141e00100074101c61a180d03030f0741d110166504007004c02501000200301600c1041c024502640c4242d603400c0c50440080700e0000781c20350040c21340000f80361500711080ca00c0c111002543c4140b540020302c1c17911b0020b01080324450003040e02501404202403212 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 325534712 1250 325533462 325533529
    0x7030915030506100e0f01050f04121101021009260c060a06081b0f04051e070309061a0a030303051012060b0108180303070c02150a1808030a050306 65
    0x9545031038060341c00152600d441d008024080032801201d100304040390000c1925615400d02c60980d0003400d0800c1900c03202c0c8848000e9030351260703030014265000764021020811890b90f085025400c1e00343c00b502e0400b411450580c003180d020080240001c01080c042042d82d00040f0a210741d8082038400080c6001d07800205079181000541e040701e40d40d6640e005c01c00c201d050a22481e83d8004401003d0b224201100d400a40ca841b6402031f0f207031203280c0d544080780c42111130182681c04003807443d0800d215454029006002083c455100362101410102e210810030703400700107039040ca2002480c292640d4290b807000c0740200001091110583c0748082c011800720880c00494200600c10000410301000240004024800140541425495030b207a080340082011064a84c0400c4900e00341d0764070085400003c8042d50781c944078840c98580004c085464641c00901d140101920000703d0210075a41c48101380d85e0f110f10940c0034001142030010404500d02800305000401844100d0684100c421811 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 325535962 1250 325534712 325534739
    0x3060d050d0f0f030209090115030608060a0e0d30060f170d02070308040b0309070b0c030a020609032109030c010c09080f0d050a050a0c1202340b070309 67
    0x280390101d502d00208100069100701c0710000b10f149840e0075418688100003040311400103006440c00904d40314907040309144030b54032810003800380d86e0450b0700700d0426490000c010405900709516078000c02c50401000c500444400c0082807010ba40d0440748101c60010030740340140c2c0c0800b0045039440303010008124000c842600068803030407402c801c042c0081d03660180742040d280c0b41102507400c00c1c0001c0002c1242c0345c0a80c1c3c102e405088001d0303503948d9010031050510310160407480390b12401040581c800000000503003070600302038080340d40070f46510308820f550380140110004070b034492603044420140c26640ca25000f518a0044a050000c007000da5425112122100800505560301c1040704c0d02c0304118146e000044000034003603404000c04014858420072020720188140050081c0181d8419800f400e0a960001c0d800004c4104940c0025110030212444010340044c03001a45036003401c0034080250808032051450501d0310386034407035825820140d02581070000840c5d0000d00f41070001c44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 325537212 1250 325535962 325535983
    0x8040c05060a020c0f0a0f180204090f020c190b06060706020706051317190f0507050a0602040f06080118180605090d110319031e090606030605010b030405060106030203060d05 77
    0x9800044c901c07005114101d030400495510824089408200070001082c64505035403c1d121851a05011082000301a02c42c03036101c085001d1030198816110340c034590242111581080940d8580580080c0d1800d03610160000039040c0041c607404118280341490080801c603204a10241c1404036a4441b10206d402c100c91202001040c00030980821a0280d1041840300540089605101045001d90101e00c0025419000e00552111810b030441c00380c015107155a42c440308449046601d07141c14006500f003407041210490300c0d85404074810380241c02c118165120800640c0c54012480481070290106900d08090003031081d100703202040c024011a4481c80e0320100034640007416800c000c00744041c51071110701540050000b4808000c04041d2000910924500410701290400a4180c0304c420b2181c0021081c1c50704042c001006050b401c0079084900404040041c0d03a0b807441e4000881c0f100301e900800d180c01102c01800709501960140d500305501510407410403010340e9a203441c1c11003500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 325538462 1250 325537212 325537217
    0xd0e07140307080703030e04180b09100b0a03031209110904201e1909060806190b0303030a050a020405040903030f15080d0c0510060f150905010804020108040c05060a 73
    0x4441a28201004420010981c107801004c00c5851524010450035520400c14800d580342e01d49e10300c0d403030030b624005001c164002220b560582044581150b40b4407240c41462511400c161440c00070346030144d06e141c212600340d161450b003041d04480708801090301810840b103816621450104a45900319541d1066125082c6000c80c030860440724071882039180759540c0b1616060354940804070945010140e103860035a8080700340f60848030607005850742c90f04441045850050001640180014038038001c04a01c01900c210710044180001035810b10030b50075805500030004142d115045600c0903030f114641c008014202500c602c001025240c004509800094445030b000c0c02000c418070444103032030311002121b41a41e10f02180940c031345406049900c14400007041c00c07024001c06202220700b000384c80c80c040001c0e030346684484820305040c4c058030b00d900e04089032031001540201a0034007525416129143e01e917640c2d0340111a6003900034011038800034503941c002010307156070000d0102d009941c2c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 325539568 1106 325538462 325538489
    0x200418060504020a1512061a19020307022d010e091902070c031211030703090b030603100903080601031410030311030c060c070b150f01050d0e07 64
    0xa5124007804051018214217035a445410510620594141000596119408242e0354110784840341c88000c410130200c1003080c201c00c0d05801d103490a02c116490305680380c0c00b080440d21424a0708035450704070300303044004140b04131000c55800420700c0d0003040140c49000051614001829068030b600401d800501881403640445481d0341d00f060103100400d50380d180c900c40c91580d0400d0400026045040030303400703d90110444040340e8055850380340d01c0b801c000751044540d04c0904507543c03602c80d285015030023203c1800350904090294555054610b0490005400c1c0d03441d20050281903900e040070000c203100c0c18900e0703206607605407601c00c4a81c119400c20302c5ca507100310741d00700c95a4800c02c0204481404000000c064851007280030120540b1920900028916100c1d01d4552150550034070708043d5104001030250030103150000704142100d101c03d542031010b150400342e62411117 = true := by decide +kernel

theorem cover : BRFrame.Cov 325359712 325539568 := by
  have h0 := BRFrame.cov_init 325359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 325359712 ≤ n) (h2 : n < 325539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
