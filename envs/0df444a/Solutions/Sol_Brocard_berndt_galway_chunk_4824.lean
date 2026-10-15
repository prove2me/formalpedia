-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4824
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:51:35.428029+00:00
-- url     : https://prove2.me/submissions/d7b8de64-17e8-4cca-88eb-6346ebc733e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 867446043 ≤ n < 867625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 867447293 1250 867446043 867446101
    0x2040e03070537030c0b1503070f05010905090615071b06080106110d08130309050a0923010b040312020f0d08011d0903090f060412060b091e 62
    0x4080344007001000f815080b180950149000e00c91001c1014041e9071601840310201d0a003c2c1d400030380d21501c0d02c0d1380c003074008030030b0141038640c52644401d019000003d954144034a1001040315000100c0d03810403120240c03149840140d580090000c601c10449840d41c0c046404c0d090040707406ca01c400101a02d40c403410780404800304000014082e00c1c0c060300a00c0c005030441d0010312100b80c00442c05142c41001500030702018003505401010303203200a00448000104001d0760003014015426007000d444020418914191242e601d0700042c81c2c03100003440c0d41d100d03640143c41c1e401401c4071954142c6802c011003a00c0c15080d038540140b5075184d003000308110b10694060a1040d5001d0020207000101560390514a51600500e07071040b0100341341d842c0280c04080288036105c1030020480c1d501100580715031071415528070010705140956801241c0b000c000f0585001000300c640d0084104060445210003039840da83c0c0501c03c1c0504015560600c14480d2011651204070240844040349103003903822 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 867448543 1250 867447293 867447307
    0x6030d0c080f070b0f0601024b0c01200304150903140f0115060801142b150504082a10090c080c21011503030c0c08010b0d02040e03 58
    0x40c507503446603c05840c21040d403400e00c980d58900f00350b0390350030080c244010818401e1070034a9125032211070644000084d20303109011144c0ca81822413030075641140b098404082d80d00074020380c4032617520000c1400560140c1021a1403540c44400e84c0c0340700c1034000194105420040f50f840e161030144c1400c0b0900500340c070008002401100c01004100307140c00903010448809603100d0070340b01002c100c05041003600d90700b4040182c0c0300780c1030f47c119441d0a074121044e56448021540c1600c080a0314080d11b441503000c400f1503540c9074121103a10b441083c032211820810842002212015100240300c408100400504030020440c9070513a02500c284018a80402003c014079140480701c04104013600d6242c21420b00800040036401400e0b204094100740000c840001c2442106400c202800c0a416070760341d40d84882548200700f040805038444060076182d04003c1c0200c0c1b144417040703400d810710400100310118117015a040400740038002807904070b83c4e5800c01c07003e810581458110391000780291 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 867449793 1250 867448543 867448567
    0x60a0f0b060f07031d06090f1206070c0b0f07080f0603070e09150c0301060e060703020c1504090e01270f020d0b060a0608011a03040f0b09030307030f0506030d0c08 72
    0x1005030b0042c1c850699034a820b986409014032498003442c442c00c2c001d5803119802c41c0c44000803640405012261011003015440000303900260b00e24811616125000070001c01580181e08040f215014054010281d5240b109076040f00d44121520b20000d07510802090654000d8100c441e0060402419a84440d45035032550b6540941100c0841c219813217029030303c155200c610000c503001245a40c1c0d29145604200340a00074541c025409801a000000d018040c58401c0c860802c10740070080020280c0103442100d403540d0f40040c00761648a610b8140400754001d4148545520009503102600030800300304075a4210a120213415924100d8918600c030040ea60b840003c102e2600c21b940c0c540440c02d009050005122290700300c907041c4609440184803056221403905149222200700c240d9a6840e0700d4211501181244020b05c1380c1c00c0282071004034600400038500c43c07400741e80c003040240309508200c0c0a5410582d6082d8240e0003e49140541d0340c810b146003407210f40036481d03075841d040001c140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 867451043 1250 867449793 867449797
    0xf0807020309190f08030f030601050a1119020108161e030f02030f090708070e1b0c030318010e0109080706110906040305150a020715090201021c08090c010203030702060a0f0b06 78
    0x514030340188051030903c41c01e10343d134442d10302403d0000b0007181000036031018000706100c040d01c002c0c1480004505580440d00c115960426418a00305482e00810036625400c808504c1400481c00304101d400040c0c044100d00100c0040c0c1a919500c40d0342c204a0003440350341e810810b405c4401010340f540300d4840c41009a000450207100721450030111071800784107403030602410390003c003002d80110f03a04221000807407a101d50421107941000107240c0c00b038807001116115583e00c4106034007020003081240704440b0001898622000d0091001c800d0360b8503031501f211045203004040340410700021010035140c0d070041541e82d006c07881d40780c40c102c051070004801c1e8026034012141a404080d128401001c1981c0207a0001c1600c0f105606107202a540c003144882000785403502160744012000a580c400c1108881850b01c416682035141c8403028000d20303c4500300e80100c03051091390410302440d40b001003200d1296000380d0182001c0c0d02c1d00c0e10840c020704030041151040c151141d24102c926035500d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 867452293 1250 867451043 867451069
    0xb0603150621040c0801090803010611010917070606090b060a03020f07170304152903100f0e0f030309062d070507050d0804111302070c1d160f0807020309 68
    0x46681030b41c6414600020302d50400e400080140c0d0509420100081c900001d0340d0554115050601c0101c101400305030051455040c041c001440503082c13014004040382c010030545004107014011076440c6c80c400c40582d0036038a08581c100404000404090b03120380e02030079070582c44002040c60030070251200031a404c081a02e040c81d81400000b844100142d0010b0f908400b00702001c240100c40002000342c1105082056680303070101c0e00d80020505546c2848006044100104200110025030280c6402404400c4030f0324140e01c1040e600d22450343c400130690307214000c4500100704582e52442203200400d6140c003002130207074040400c000510900401d46d48110500c3c5c0e5129140c000324206980b804540014440c00d0050010602005c2040c42550304c0780403005461404141c5ca1740280c80c0028891454050f01c9010705a101003104900d1005101804948103400711b103e4440043c08410400c403605c002021500ea21900c00780a40103025040c0e20058a005030f0b4202810500481c41024085c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 867453543 1250 867452293 867452347
    0x7030e102c01090509072a031b0204020d0e160603090b060609150403060219030c02100e0304090f021e160b060a08060a0b031216140708070b070201030f0b06031506 72
    0x1040c3c0351f8810b40c60542644154a1a0580c14283e01035100070705000b0182c5600115090301c1d0b07198400307540b2160122061840c4d402c1e82000488407100040d43c03103500905030b642c9100582c0c100015083d2080c014425865000442d40442c0d45030700081024a9100503000744e013000665103400b00c10075203032001d0b000550040f00e025a0b299911029408031409000848060602c1c0986420419a000402045a4458840000721030720706a017024590301440c0c0c4554031560405207010600b120a030080d0521009041380381200001e0060008018000c3d14481d4880342405072402000c5500300c1c003c190800c001402c07541050303854040c81410040b080ba50b1404468461a00a05900b1304010781f1a002c10b044550324204919000555003e03a8640e030042d0640105140c4801446010b22441004010241c100c1c2d007002d41c6d4000302404c03a0009030040c0d010a2401c16420380d0f00d2654000c40003452002028a8515074030b6403c2270005040800d4540c3d0802d5060124000040c10006e400074881006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 867454793 1250 867453543 867453557
    0x9080c0304050a05100206150415181103070f0e0d06020d0e07060503010b0a180e01030b18030316050a0c0605010801060f05060f03060108090a02040207030e102c0109050907 76
    0x30100340f114444450b40818000d0404407480d0030410341c08250f8030340004a0340703c0f004107511a400010080c100b00748440340c070042a2940080c09900c46c50751014906528102800401a03417918040580001c454a20118008070850b20440748039a441d0503040000406681d42c0c9012500e40c0c508030381191030b42c0300c442981c1d0165210200d00c00c028110040103540703003040c55981014219003545c003d00c00c04070244842d44000300da81e040c4140e2a0405020071002d045850740e52800d0034aa104400d0f180400e980d641210360b00e000390000f104891051880750f401a0000d41001001c85190f8400414070382042800c0c07261000151490140c24003c200c2d290011596506100c4100a850503c1c7e2000e4803440c17080100d4580402c0c10b405980d8401000d0030400c2082d0395188d48141400000c0c080298420f100041800805800030a84282207a0680d040d641c3c2a404c0e0000340d0704c480840c14030308900e0340300f40c0a0b0000c01000c4411710000810600d090310203035651703c02081d904401514250041004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 867456043 1250 867454793 867454799
    0x80f070201092f040903050405190e0f040318053a03021b04021606050603031e040905070507030c32030703030c1e2a05011406040204080709020a0309080c0304 70
    0x6249000f08003480031602001010456a00504203108900c07406000300400c1c90119841081c1c1c036290002401a0b078101d501900c3c0040320a4031268088a04402080648181490014604e92014152000a80800d103c240100034450702200d204a00f1505d8510401c83e4401c9810704c0301218180c80c0c0700350020490708180c5e5908440a405282000d40110b00c184029200c0601e0f0001c21102c0303541025000600d501c80801003030039480703025080d040142915150003004040700c00104200c07510904100525121504200d855214141014001400c040110310100e900f50101c11440c0c00d15806200c5696405024042059040f80b80910260008180c0c4000e15800d402200c9100000345481110101e190aa102600d0081c0d00b0744420000e411406446a0400c0181485180d01c01c96a45150004901e040ca0207000c020861a481800ac0c9012a03042e05080c000c0c2c400341c51068015020b010704000c4004000d4006510010404da12940c00c0c01c007203034481004243e0940c0d8407010310f40e03542c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 867457293 1250 867456043 867456113
    0x504020427050105090d020618160e090c120a02012d050417010209130c0c080403061e05060a030f021903051005131a0601140a050405030f01020406080f07020109 71
    0x44014801c500030780098410802e86d40d80450400c3d481010280103180c07440f034072071405107000c5c410f4400d4182e41c1802500482c40d2490345800a10034110304c3c04490544140d0f20a0014483c14102034001f540d001d008074400543c01034183c0c0000250000c580c6504800100894806aa1200081010490000342445103040e211400004290084025850241c00401203100826140c5150300c1c410f5843c4c504c00f48040c0b0400c120003040c0d0700b00342c0440e102c03030700ea0500c60300501101084d0407a6401140d800b8444020502860784038203002015070605610759203845121550003031040342c2c0003070600c00410b407032125403c80401450140300100000d01c19210700d9021548060b0010850402007680c0c000029840541082c2d03000c0082d00381c24094035040300682d000c58545071004e141d1480480c8128201d036005c0d002d03004a034403c80445000075508180c8a08070711440c020701d00019244400140401c0c0c1002520b40c00c02c42c144000516540240c403003050440d50004641059004083c10544000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 867458543 1250 867457293 867457301
    0x61d2409010e0a1a13050627032a0a051305010e07110303070e06130b0a03060e22150501030b0411010203030907050405060d0215041a070b04020405040204270501 71
    0x50302540c650307810608214100405503914042e139001c0c0030000651a504600180003200107042c05025662a080b0042606041106500d09002040c109082501241c40c000512644101c05000402c00460300c003422440d0b40101245115081079101c3c100140b00e403105c0c00d9800c50b00d00e01c1c5000040c0c55050200503140144c0c051311040c20010a01d80d401032107900031080707907004900c81c2084a8442098000f040d510301170030503240b0404842071000501075007040000d005000c41035034100012500c1d0070740c0f80c6118000b40c1b40050003100201211030540c01c03140003440390034015841d40d07064030b014840c0401a01d02c26042250b10b0709490061204101c10302d000d0281c451000d002560541c07402201039503644002c0c2c4a030510a54840010810a40f5540700980c1055000351105585045508046100e544680f1540303640745031024451880f00c10f0581900c0c80b03d58401c4185103161119003c0201401018006903846503071880c0446d21048150189203c00c007032051403069205040c1000d07421a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 867459793 1250 867458543 867458567
    0xa05070b1b0a030e091b031e07020111040b07020a0f080c1309020906010c032606150a050f030a11031303030b0307080a021c0602040b0c16061d240901 66
    0x40d9015100b440002034001c50810540c90044c2c1d0314580507603d11510801d1580c401c01809408240003061280d07443d41c100c400813818498034210441515590022401c981c417401c0c1c8140d075a4801c2c4404c0c46503290080040058600080803800200d4548140c008448001c0c0d00040041d8415074602c81030b414904004584145002030400c81d62500343c02041c00000002c00c1141040344a5a8582c00c01d4060840c0e05110f0720000d182d003d544034030703082c8140c0c075900c140c072024440c2d0590a240c116148081044a03075040441c2d580b5400d15006221040b400e130005805842141d45610101e80300e5000d120243d1b1080440745840500c10300242006400c81d1001d40c0050700175080b07410300b031007440d000180c03140042c0d505490805480d5602c59080e518184003c2000b01441e00000b0001611150440a81004142c420079142e441c828a41c070344049206034414a00881d018030320050500382940311004031008080c1c5039000d80349104000f01490044103079105c42d94080460000c03290750b8408810349039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 867461043 1250 867459793 867459847
    0x1b1609020406120203180d05070515040c0e090a02130506011b02031902060d05151c030212030a021605011508060408070f08120f0406111e0c0a05070b 66
    0xd482e081800003010b408503590002c000c182c00001050b481d00d40c10004c4040821000e040c0c542d03103a20514000c02c541d0050713106944520884644400305009501c115008913800440c00c1c1d084d0b85007628100710480d0080c5442158010032100c0c80150711080f404c5080304001c0c1c2c1c3c0001d1513140840c009050507540b5510071480f500d11600c903e0068070000f5140e00045030303003c0176510402c1d4920004400f8441c16103400b1072035081030103105041070200c0501c00c03444411212202242c0d640d0a42429038002144c020b001607001c0c10100a102c1044001190051040d00c3e0141c40c1c480302001c0a00340c903c16400842e80340c0e54603090032040d01403048100c2c01030300c2000080c0240c0d0600c4e803100041402101c1c3c0107416021000440c204002d016811a10b0444011485005515190300454840c06089030f00342c0341141000c1d00706141402820840c0c00100d101041c00101500350b80c00c0c0550b070780061387e07403116502c01c0390b40041c0402c500300500c1e402480a050746540c0d44502013161000d41300407070820341d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 867462293 1250 867461043 867461047
    0x103140607020c1c081309051308030103020904030e0402221403060c03070c0f05060a0f2309120d020c100b01020a03120212010825050109030b04081b160902 69
    0x2071495010034042c11064013225030384a58030906041201104075014010400300300080d06400300d0851117500c00031240440d00030041699059074000490111101c0146494020001070006140001a03250018041d141085141c00400301041c1240d008510a600102d0512000c0c4401c3c0c5102c03080d64050044039248804119228011942d07a5501901c807556600c0c01000040000303100f5072445181c6508010203020076059030505c079449010544650048504103442500c980c1032a0060142c0822081520005000c1c510301803a500e400240140706c507405248240041410468040c0054a403544d40040c2d0340e00301080000d1030315500b00c2d50701580c00d00b445c08a140c207a8011641100454040c10142d4003018603800c400b000b1301c144824000424918400800c0e11031000608003012020400280c90300a0100c03001000d013040d0f4400d040c0060788507407042c80041c5c030030000560043d200e0131003503091070034121817040e02c108002c441c07034074550104e11060143c9013011030b000000c0a01d903a00718 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 867463543 1250 867462293 867462301
    0x1e050a0b070e03100203130c03080d0609020f030f091c170112110d14030a0e19030803060103150e0108030a080a060b090402090324060415081e1f0501031406 69
    0xa88400e200d1122244e10740c0e01000040301154030340f1000b003407a03502c078901c000680c0e101c0c64081e91540149815141e45481c0903808107040000d48200c07001c158180d01030078110383d20b4052096036803c0c0200440f1590086038040000c41000300001042e40c840d585641c160160b0007803101003c900140e1150142c0240f070120403020840c40154050503034020340351060040d900303003400764101142d26841c0301030f03200c00500c900039280d0141c02c00c202e00700115034204404061500041106000e0702015207c18010404a07002d0342c0240d00c581807604d00c202000b28030f1580c40700301090b400800d9001480d01e4000140d000e4002c1e5101980700d0340200d80400030003400341001c1d070320340c006e02840643c43e001c0d90380001e821131195810003c00103103418a082030071740d8010381c0d54104903412065650701c0c0503900302201001d05107808826201170f140305000901d605003003418050104001c004402c9101d0082810301e0205035034940554041c8502e194020605514500d42210140e01464080300d00e9000f400c244 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 867464793 1250 867463543 867463549
    0x20606010c02040b18044e17011d01150905010e040e07080102030105100f09060c0c15020c010201150602031806090d0f0c0501030c0206191b111c0801030f1e050a0b070e 74
    0x41c0c03081120400051014a07003608064444446602c1000302032806d900000034003907000e400e400c0c0045181e284c0040e0f103980e1000070724026080981330b80041051a43e0078811540b00b11201c10782480300500109042c64940703245400d191082c0c10902ca01e9400000520282c280001520500c90340e5290840740088041c000a10500c6180a103004202c100c040c82e8081c0080141510301624411010303101401450b03030007954585c04003a005000d5402c09940c0102c41e030851a12000701e84440c0c01841ca40300c3c60300060402c18941d002500e5004100b0700c60801d4613205d15191242c40c8ac4206c070f01c0411076800307080c11410000c542d40028100344c1401c41d00841590302142c110b4010709841c0100c981c002e180c2101a0180040d0504921840d010300014541c050b40301d000100791038a21405d0300c0d50b201000d400e16071889105901140400d455000400001d18014101d0800900030410b40c1000707194102908801b54420a040d81c1c0c035031003480190203111324a40300941003050b0317043c240d6010000c1004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 867466043 1250 867464793 867464903
    0x5100806011a07020a060c03020c060c100f090f050d0e06090d06020306010908060702160b03060603130503251509031b02030f030708030115020606010c02040b1804 72
    0x40220418000c0042050b14410304107480403180e0040c82c0d100c5541e2980d90003042112550005d40c0144030703010040070a41407100403900c07031008200240c01034050038044c280c003410000c0c4400c50156074400c4501c002c1030703d0b4180361a50a02c100040c0c19207601350300300141418070744541584554401c0100c130b0840d940d2040601e2240b030f403003c40961a6a5507000586449c486680700a8003401034504024000ba40884c00c14a00d0351134080d5080025240c5491600c0c40c0000c95003550001020030224940c049505140c1511034130a0080300d1030021b40f05101998861407048500e100b50100c41d40c80300304905025400340b0b603041d880c0100038154186e03c0040243c91102042c40141c02006013507c00e40d04c00f030000d013141c8607001c0e080f00e5451106181910143e4002d05c900c0d00140c40316507c502c1c1a902c0810300c5805020142d4600418404a408110007008c44c442032580c005c1400c0d801e4041072481051003441540a90b075105550220082e02c4500e000c4007410800c503c0d034070b6800105074200b0b0404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 867467293 1250 867466043 867466049
    0x608070e06040e042f2803030c08070c060f110a050a030503060301090212030309010e0a11040218190302011b0b0c1e030f1609051f05090d0b0105040510080601 70
    0x7401015a403139a04200d1519802c0442c03405446409108a0f80f01c0315a020079003c150405803a490594041d0f50b40d40501d62040112092600341a50020004207110305032940c1c4442c0101d88161504e80c05580700c0300c240b0010b40c045400302c1c040d010016115500030031007540c20316000f0f01904459a440e642c040d1100c40d1070100070b05006010000c16090b4400354848000075034068000c20000310101340303459903504111002c00c00366080000d501401f4801180120750f49a00094110aa203960010017000e0b4100341c04082c4c6000c605441c0450380e0f0740b0700c0c022a441e02e5084106000e100c0c1180001003a450218182c1c41083e00044030040c0003d01018566600c082c02c2e51509841d020507005074420400349003510419200c000c024040c41c107140b40c410310f014100c50034041c00490402d80c0d09840c81d558134800c0c2544030207502c0b068400b001103c10f00000710081442d005103041c2d040c00008400009410701921580002001400303141020300c2110b4015141480001000b071800c0c42e6246d0740c0360140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 867468543 1250 867467293 867467309
    0x2c0f031b150702031b0313030b0a0605030c0109060c03030b150a08090601050109051c0206040e0a0c09031101030b010e102106120311030d110a021b010203032706010803040608070e0604 81
    0x1444801005000c0c03080c3c41e085000307d084c407241540d883c1024a041c08080d80c3d4181f040307141c4000013079545000140d468907001c0607150624001e02e414000d0700c20110307240003501856280e8814a03201e40c0d45594160110002d0300b00f0317a0719130003000c0008194080043c8100019403140c401844960f0300140101c04961044440c01051500c0c42a052011a0f41c00e400035000103010402090211010103003510422070040100047c2d5040c90040302c01c40c0d207034030028242c0985500004415403082d000014603010604020f07800105940115040c4c1c0c134000080740010b245180741032138181c10716205003503c1540f01c00900c03901c0c1c01d11103038802645e2080001014840703118458080b0302000d0080d00c3c0703a170915035010094423040c0300703d206059004003000710040c040c822a001d000c1321040101c80f0004010317030045066503212210800101d007400140420040c0041401a41e04000c01056000c0c0c580b0b880a1a161490284090280c0e1005400360081c4020456122402d4903a042030320119a803e03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 867469793 1250 867468543 867468577
    0x6030a050c0f130e03031f0b0f0918072109050319021203040305040302010909050f22050111040e06010f020607080606160308010510032c0f031b15070203 68
    0xd100007600ea8035040203d142690801c400510742d80c0001c0051841500d0704041c10070710284035040d401a040c158000d09005c2c50051104160281409001c0c10007404007a20a001480e01f00090300007002080741c00000060302c0111101c900d021010154150390b034024018400e0701e00c6590780350744902034010382400d0708003252045032110388204002c03400d566201a409030f0324113140c00d006002d540680402e901080c19480d002800302c0d00d42c4100307442501103036042400c40d151000c11400f03407810a001900400070075518400802c0c401e10441450700c0062450580d81c0d444c0c80d0b441404818001d00701c1d0706200c03150f110b41131240c2d000704105070b00c030307105180c00e1005035102000a8010b01618060b0002a500501003038200741d0801030b0281a02d00403180c820000e102c0d0781c8102e09989040b00200d00300d4112400707010404074001d1044156a1b07005083c1c0d19500700031040c603803541d04400c0340b40000d11001c900c4580302070000d0140710601841440c65020500d0152780203907980c45500c1d000b107004111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 867471043 1250 867469793 867469819
    0x6040b030114010302280605041d13031202040801060902212223100e0105090304050f03010f050420090606040e06011101050703201201051c081c0506030a050c 70
    0x2003602d194201000d1b0458800c100c54850b10000d05c180c1084c0101d08040441c005003100804c40f0401040c851f442d0610324150b900e826035001c55862141a01f0705203059000e100106101d002070144a01820040000584400580b0b02c52011130907172005481c503006030300003170000801a00d010002c03100380c04450102010154038090714102540f210704c0c02400c944200c1341c1d000e158007090300750344006070703d10911004043d29160f6080f94400d80740c4100f25441007108001e41d0130032510780415a90b00400008240d4034500d1100151030b402c540403210080b400469400d1449100481c0c60100e4041d030309000c02d07180034804034203980721f1402403142c02141100000c00c6684a0800300e606804110001e119505180c1e4001d4041e0400360341e400400b120810700311410740008002d94150030400c1c01c0202080c0d1901c014483e0504050070280020181d1002d480040b44061000700007002020041046148944445d142102d202600261190701300c80005004983c0000b0802004a03080b10303010a2410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 867472293 1250 867471043 867471079
    0x1140910081b0d020a030c0306181109060f04030b13020a170102090d060203060a0b090901090c09031703060a170c0621250804081c020d021206040b030114010302 71
    0x4200d03119103160100090340000214035070045c000440241d1028002c40410380b509034192035007405094184060750307600485110f1190400c0d0400901e5550003840e0211a10120303205503c4942c640c41181d1000030100108440302c014942d00a0703004490b581d1399410790340001c404503032500c50620504082048030400080a40c102e4516070b8009000d08003020440c82c150019401c1220720300c0c071500e28a04000f035030051201c100c2e40c10100051030445142c0c01d0030358503802041c400e12181300b0002260408800102102d000c904217040ca1200551285040b4040204031466504017000600325481d003000c00040007d0066203146040b24080e40342d050007a071564062400e040d100303106400c1541131120507110405200011061a030340c000d2400842c010075600e0326401c0d50005c100e031008003e25003403414054088501f0700a0b82c0c0025242002d22002030050342c00c481c0c1c01d1000c2207210814040645010710820070608800d800a01040303075003440e01c1c4245803052201074001c4600d9101c0b06640b04d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 867473543 1250 867472293 867472321
    0x90c030e1605090a060303020c09040f0c081b01050f1c230109050f0402010804031d0d110108090c0a21060c02100b0301151403070807140114091008 65
    0x201034040780d000742140345162000300d0325403103854040d00304840401d00d401c1c841e000309016a500354005281000f60601804078410000f001521868510b0548000144808004400801d00180201411448824003801180d18030003158103104040040c00c1042c00d59406444d05010b0045404075150a42e10185004d80000a10125282222580c1c6004020703080c0401d8160340d0800c03002c015035680c40590500090051380c000c1c2c0030800384000500000d21552a0b501d1030f40540940c88484031040380858403011a5150840300c0090a030481503040d40d00005081d40940d00e40010009a901a40403900c8801d10b401582000c4200c500c0020703451003280c46400c1d40a13800142042070f0424a44000c0d100c4003510301d440310403400c0c101941030074035050040d2020300d500701540d030074564549400b01040700d401c40003080d0140101c030f00009030000d007800010b004100c0e0060320a103103c13102c800100015a4419040d50b0410144014445134885588852158005062042454a503d20106126 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 867474793 1250 867473543 867473561
    0x20402130f08030703110706050910090e0a050f06090708070e1c0c0e0a0921020c0904050f150c030708060a0b07030201090c0e3606100303110f0304090c03 68
    0x10840d28107000460240000052044a00030390321406030500104805071070750507601c12200050000e21103412146000d10b4510036182050a20307141255a07503421940c1e10500721390001059545000300950300c0b600824081d0710140440b984000ca01e041103003d402c114001c0c01c7c00c000c04c282c240752000c0c29201c01000180603608042410462807013417520701507054941c000c882c00d61040c50b010580810b41c601601d1b15081d8010513182e21503d41010342c468922440280300f00314071503003250b414551200701480c0e0050780590083c00c1350299001d00307140b410300c0c10f0070401d401e82c14903000c10540d0015913055940081ca60f2400c020b081d2504400603454140980040000b408005455420160154022905240315200e01a00e159458a444030702d00c104440e00700da49400401c0400603588081c40c0d81d1454a010101c0003028030101a101d4039002c030071603480ea02120709400a00c24035801c45442e04642542100610324208868041c5440340150f02c2413140e0242c84013405c42e40d90340290070017181 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 867476043 1250 867474793 867474809
    0x3020a17132310020a030b1c050615011209020117090303010e0709030308060424230d12120906110a120e0d0c050a0c03080c0c0f0a0302040213 63
    0x85800d190084600401c4422400c844020150002111a00340044a0b0072a40d122a0192400728011100f1001039800b02c40f007034041550b150a600416a52882d17860802000c050842e90716241916000740790410240ca44280c1c00c0d00c2c441070000e20381e0320044011f07141075400d4021405a200d0b20060f500c40d00845800d6070a030341403804020708514000003950499050711345020303181e11800015950402c00d400058006280f4800082c0c1508054100040814903964100c4800700682d6211011040580044460b4480581c860388902e840c800c50f0f0040c110300700c0703005941e6103141e51110288924419290103002401c00b24000200143d4080c1d401030790020000d000061080d10700d40e0103035100d0704189002c80e03487c224440c0049514468400c14805102c002c140d036200b240c10540b01c0e041031209c107d071a440f40200090004044556060046101e8001182c6880c02d2210142c244014201c000d8003c010350320600e40d040d43c80a01d11700c11070350140c2b0010382d108089604480030740041c2d003042c08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 867477293 1250 867476043 867476087
    0xf06280b0c030a0215270f011d0114220501090b012411030301060e1513030b0a0b010504030f060e0f07050102070e090c15040306150302040606081603020a 68
    0x21141c101000030500c4006a50a80e10340005400014503e00e200f0740f1a000340e84146d40000050f680403412a1210031001c030115021482403610940c00c1d0390004103a804044c0071702c240b19000030024012484a0034100074030782ca00e4945880c14940c036155110a4501100f954524034080c440c007903004850042e000004d0050b0756850320000100040391302103050040c028910f080705040c1c070444c01d002051124601842c036591900000b11550400100c0e4290b001d43c02c54082000801103000a004101d00d00b1001c070a580c1c5142019188040000d10028a00c1d080c0b00d14404180c2e40b14044800f505c1c0d12242c5a08800c5040c100031000b1700b010071105045200c4c0d107000603600640000c400d01100c100340e00701c9001c0c41d140d08030306903840d40550300103500ea400240214110316120150b039003125100581036091640d25160b01081d5560150f02c419103050426090083d81054010311014200500700700103641400c031004c02c8015400d4560300e04155001c501800d0341841082900d10b0030720348281c030007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 867478543 1250 867477293 867477307
    0x9012007031104051302011116091413170a110d11160e011205030c060a0509010b150702010806030c10030e010c020f030f070c050918060f06280b 64
    0x540d64806a0005860801001003541070629060003020312640501e4080700740494140c0c0155032048a084051080e400780c003070b42509403c814007804000703081c2c40002040076204000c8414094501038a0300341d49108050034440840e1a00c80031407041040001c00e12703510b9218040c201d4191480300d03650f1449000700a2069122940480c045100c1c00300741d010703150104102e106442001146204030a422403035003004202541d074000c0a401454060b000350780c6004441f4103107908004044411126455a503030511055920034401e00c3d0400341d040e1100d001c2d807104d01d22184118000d0800080c1001800c030000b59041d00c0520510704038a42c0640302030a403800e081000b402428040000204961800d0118220184005120001c2d0100c85028502d88240c500103c4416030100000781c1e0a8002c8550000b007a4a0b4444503900c120100e0300c0356409001c0740e603211410030401905c034103c42c8149400344a5656150030380000d102c50940c40c01d0b0380224400840400e6100b03154801500c0b490081144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 867479793 1250 867478543 867478607
    0x403060f020a0f081b03090c0316030b1f090b0406090c03060303111b1005190512090601060801060f030902031203090708010207080912011b03020d0609061a0901 71
    0x1a207101d00040c1c403406941803c40804490300101190920360031420a008540c0c403907032690080d40c01c402840140c8800c11440800310340382400c021175038a5190860076081060042100c031460b0450f50b00072070b90078040c40c14840c5180404c4e080c01228400c0741d50701ca00607a00e07a100d078401c000502c10048181b1069111a0340a07004098911007036003c1050703100b003900000404204401c00801c20640503901086001c140548845040d91410510504020880311010241d051001c0324946030f5403079070b41d040078900e00745101001a04210081e4004801400f0058112014a040d10325600d41680a5a00064110003510304900b0203500760213810450f890030740241000b50700c00d5010504443c00c3c9941c3d10000d5080740b08240003e0700004c0b06220184542c900001080c2e4807090b11000440c0b01003041407040c0b1200f90380070706080829030020381002c0a4408e030085000419032440100700542c544190910480340d5110302c1c40701d040000441c08000c0e806070300c040050f92240c04038491448140350207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 867481043 1250 867479793 867479797
    0x913050f2e03110a0501020a0213020304020d05030f1b24070210050f011d01030b060f04020408010f0911031b040c1413060201050112150902030102090d0503030103140304030c18020403060f02 84
    0x83c601450701d41c90085400d5000040e500c803070550242050721850007150811001350070141007242d100f1005520540404d01c00c0002c0c100c54050315103403035900c40d2009040b6842c050780c844030380404d070050001c1070119100d87e65281d5a1701109511100075540d03a401c101d040c40540141082c0c203a1400042c081d4507114207410606032409036001b8603203101d807600740c208000340c24400141080c4003000010020705084805068601e07001e8005410152503220322425541c420048400069503411100c0510005c0428141040c500b0382c080c4c510782420414004001c201000b016008a481da140c480102e07209200d8840805d00d10890691203510b220b201603286284e174400c6000540c2400c00200f0b220f10061041d15810b0f90119040e01d1400d80155803034054100810300703aa055600b4481d50a017500c2d404540703003141d403151000d1545d960440c0340c95000005001c00051480d44180400c2c8001800c001040b000d45000150030507140c070f1582d0f250780182c81140c000415241c01d00e5189802da01081e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 867482293 1250 867481043 867481073
    0xf15040f08121e09010519020d12050105010c0803040203070306090b04050706050f0406030c0903080a0c050f0106080606011b080d2903030a14070602040b0913050f2e03 74
    0x800d80e401e6030701140c0220824040d4401c003103c8205010040d080350744070031005007000c580c18104541810f000580c1c01000080986c0d050015803c080c441501d2154070443c8600b1000960404001c154101b0000070300d00071400c00010850140040405c0c29980d04118100041d03a00400a0110b00c2451030174490384130381501e04459910543e000170a03da402030382a05c15540c590080306042614001045015100c035520746030500001c400040301040103000148400300050f00c03404d1292110f45030580ca080c00503450507195914000d4140030315030340800d0064000d882480c0000c4c4100f101d000ca002c6480b1900001000c1100016604040700d0132038101c3e0a080c240ca040300003130f40c030798481690040102110003541c99013003046014032090068038044807019001140d03d041c10750b1581e840d4200d80c403a40222403603420210f40703007523903140024407110304507101c440078006c0c0d00309403d41082c10300c405000080100b49442c45125452100c10020700f0250300b02d282840c039155207046c8500c1c03074000c0c20 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 867483543 1250 867482293 867482309
    0x40f38190b0714060f0402030622060507110706051201030f1403070f020f01110d050f0f180406061b060902040b03060a06140d170906091003022508090f15040f 70
    0xc03140e18081000c54406d940180181609a5500000d01c1d141d44d8240c412000c4101c91180c0d0710003060f180c6c0718141c03146140d5141c8414560407200554036000300ca904c05000c100c0100000c0b000e40300c040f00c4140c11070744d10400100140c002031a10b03021202d030307030140f0710900d00c80420310380207000605460411031402954100340e480015401144c49203840f0005421036408040d010f80300a01c601e0003443c0c0c0102010f0820705040b41c03480f903030441d40d014910300d842c0d074504080d01c20054602849840b00901d080c0c2003100100c5860309032018800420003024041569804261055465603084494561030080070b61304245416410f140c010300f0a401070141c0d8070302c9801c200b44c5a0526000c2c1c13680040d0400e0b4a0035407030f4240503021019600003000c294201c08180640ca1140d260420580d01a150075140940c8a400d20860412010410315807661400248581200811030f21002c8503140c81c0159041107611241c100440c0e5643c01d40001d861f640000020001a0100740c2210001551200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 867484793 1250 867483543 867483553
    0xb09040809150702100e01020c03010c0806130606080412170403030f0c050c15041e0b0f09030304110402030405010914031201140109170c040f38190b0714 68
    0xb0004105990281520094100040e190310110260043d10480d0b61150148103e50345030440700086801e49920400032004030341620b00b440103c5c41d04640c003480c2600b04820410a892403c2c20040000501910140078041031580780c1c1005481940111f1561f2410350400c03099060614004000300400f10828031828903049042c4021340c8100300300c84072005c040004100300a06c10340b00510342107018008489100d4071030300b4450300040716031000806030f00480310040e0614203d01324524071500100500301540041003000001a0900054548000300b5940140c40e503949180503801004041c501411100c82e2400409000a00200611811520446095080c0d9a488002030300c21043d480b4280811980b800500510035032011041c0a5501c8208075410403036003c02190803204101141091030f0703114801320026081e580304403055001681d89610f4204501480c5411800c841c3d6900b82c4110754800e580800303029102e20900c05484400d1510f940c9045e9460841e80800401e0040301080c050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 867486043 1250 867484793 867484819
    0xc0d2d060e070e0301060801110c071a0d0c050c0106030804080c04150905131202160501170a020f040308160b18030301031101050d15081218040209040b09040809 71
    0xa1402440100c440000e1000029100c100042d00d00800c000200340c2c056603a8900015400c00c00d000f6100d205982c4510140d44500121205007810020307041400e6000b51418040b0304481c000f022100d0740c480c0484002020490001d080340c0074400c1001d991100d60070702c2800310602c14640020012201540103d0b8040c1400d4070600c01665480610085500e5603100200300006254004550080c1000d1040310031035160f664500e035450046407a1030050f80308035030a441440380b00c1076580c050402420002141e0404480c002d15190004280007501a00840c503401e07000c03103080544d405940d00a030344a8a50703882e88100480d00044006c04d40b0300454501c0032907404200001d041115841a80145241d80e003141c03102c2c4501c10004542c54100002044000c020083c0c0e481440003204040b101d81b540c4518000e140c9140000381c01d60081000030130171000011103228580500d40c040c00750b802580b030382c1e82100013400400c0d060b41e02d550803064400c104020403101030000c3c006928100c3e5081c420400b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 867487293 1250 867486043 867486131
    0x18120706030e0f0601050d03020c1504030209060103060506031303030e0a0f0606210602071a0112030905120a020d08090a0b040e0a090305070308042102150603030703090b030c0d 78
    0x2081c0024202130b40200c1e00600050400c020384015081c081c0c011190000518400b25201640c02001c0b00070b0b9070004203089c001c42c07403d1044241c100030309203814441c090403c0c002588ca884083c00040c0c0201c030301c2000800b00340c060b40054101d8407404080d104000302c1e5081c075008400706050101c1c4c0c4030780b900d030300030525510411502118151172628118001031a6460b81d00a50102c0000e0b9411150010040f10802058003014041c203a45402d1201400407803502405a0600e40c02180c07151030450403180801400084404d204c640444095541100500f0051543c1c81900041034000905110202d030032550800108200c882e11501e00509541c0c4403469011100f09003070090020390200810b5021a10450510340c0007401140740c000c2c4000011510500250340c0c0d07641d032016801100413902c42c0c44c400186580d00840960241d4508241554002c0c0702135410302400021000c04800f081c00c1c18004400e4685603898071104100c00011522140c0e11810204034031109203507201200c2d03208031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 867488543 1250 867487293 867487303
    0x115081b090f132c120a020c0306041a0708040803061009031e02180702070308090112060f091505060d23090a0c091a010503060103090c030c140307031718120706030e 73
    0x103030f4268060030b400c1c01c903900608502e1b0300102001c800c42c80b554000f601a59001c1c005240624172a641c0150b400c200d110034000003100040240c414070000740104804140001c3c11203912902c00c5401101d400b010340800d0f202880917400180c80118204c0e031511804100d5046410018005c580c030030904200041144240582103a1000043c0c100840c20800500d00c40e0191002c0d00b41410148072400e2040300000c00c4030004e03800b00d401c0d0200304c2d004203c0c03191588a81100036601c0d0081040711402c0002180d00ca03c94081400602da50750f00c0250030a02d80001c05211440d0441210b64003814064202c55a4000c5803000741c6541038061230004140c0e10034440c84810600c80074070441004c800500554080c1c0000300201c0c10315032a0082000000e04803c0480095449a0800c1411501b0700040d0f08484c507484e28058080d40c07220a041c00820780b0b40c903010a4034466004450350f00d16859004c907105010b100105a003001c0801401403c10300041084002c0c0c030030656041001400d9100002d54a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 867489793 1250 867488543 867488621
    0x81b07060c12110d030603140309060403020d020a260601170d0c0302070906030305030a05070504030201021216020a03060218011d01181d0115081b090f13 68
    0x214041914550009808030741c4022111040d0603d0300076140381c0343c802400c0290244800c00040d5541d8070500c10400c0b22610304500c50440802103042c0001d001c041500c900c00d900001e841a00741c55550380841d5075045541380a49128032094001802000040710401c0b00505501d02c04e014080000c680c3c550302d50b090f690342c0410b00005040041d5402ca0a58410040c10020342c11070180c03100c00b082450741c5005182c011803103a42c3c1c003596854401c4c041c20803540040d10600c10460f08102c10000361f0f90004806030003c0c0d00c80c422a0ba00c0c140042e06100041c200a402034000d1020344002060040351340c00391841e098840d0600780c240840400441742c110b040b12210202d01050400310400f54429034007281c240162401e500041611901c0d4100304d08808510b1416940100d030040c4070040003007035402c841040c1c505041b062414600c400c0341a2805a440040c14104040b41d01c0c2c03000d039599514607030f180300003401202c000d2800700c4180014000d14070100d9042c244800d43c080c11400954100502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 867491043 1250 867489793 867489797
    0x1e140402010c15060e090a050f060402030706081503100e150919020409020d1101172208120f1506090a03113f0c01270f03081b0706 58
    0x1240e80303d0f0384110366111819a0810b410341d980c0340114441c1851049240184a060001c14405000d8588189803000c100a85005600500c0600c401a140040c001050301c2d001d042542c0d81d9960015084000c1c020520080d905201e0000091113100d0203501078900803401d00d0540d200d600b582c0700800781302d0310181d90f040d00b181d0126142c2070784070410500c2c9401c0c09200901c08510f40185400140140c000041c0682e00c060340c0204001941d80c11855043d01c7c51307009104602180b0b00f0b5004030000d0010400f80c206450f138201580c004012076501110100b01c0b00700b41e5154a41000c90719120301c00b00c12500113455a484007040f107042d18205040d14103010004056880080c115501c3d110281000424140c001403101101003402500c43c0d01c0041482c20502502d500300400c040018010300c02105084180d04201180c0c070859034082c0b810000c00440140c1501c0180030101d2482c00e86155500140540b0300900000c010032400c103005148001c200300001c422040404c0c140d6480b44158496600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 867492293 1250 867491043 867491057
    0x1211150f071a042a090509030d050106110709150905090c0103060902040b1603180308070302010510121b08011a0312030906130c0329090c060a11010f1e14040201 71
    0x398444d0001000b1004d88921a00d2007449640c4000c88070903a03200b69141c000c20741003c141c0b9502243c080c803078140102000c0c5004005065481c0311940c40b41400c0c02011684c584800d800c405c240c908081c1a07009089a003810401440c2c81e8111030f844461840760b1500003400c2c071900080864040c0207aa0940c2c01c0c1c491068546028880d40014403072a420381101800001c092284201400d142100011401045201c2c0c2e201c000c1c0c5070090840340001c0814216030726203141400100c5071150383c215001c0d03024074413080c01021420700000d01c444560004d913066080a040c4000c007201c490300c020411005408841181e0301011190210b8042121131404945c4040d0008046200400910000b540185103a030200d588940322054159140b00d02407858090410065901c14100716035280d000c15090054451148154001050b0f80309101100c4100210034600c8040001c0c2036015424980502d40300300038004c0032941405c050b2800c08182c0520274079103540b941140c807051410500c10365052f0b507a15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 867493543 1250 867492293 867492323
    0x3040203011b14030a0b15030403080c120a050403020a0501020a090f0503060129041206051801050907050d0305090301050403170a06260c041104050a0503071211150f071a04 76
    0x81031900020010f150745c945400b07192100e5250580c2c103000806103003208a035245041d04019116400240850000c6142000160a4050096200e9811074200302000c209911a400c00324a4445204009491544000382080700340f501700d102d8008841500185001c55541e0300e04068603100e09214052180c0b503c3c811001d071180c012182101c10005e580b0200e41070603114080d504561956240482d91030366200c091041c030030320000941d802000071310000d001a2501c145516143c40c200e11505000f1000d01034402c00705401041a0b64001102900030030951400e400c1c018640c1742c0180100a000b4803000c04500040410b020f020103030781d51b64828607100c41c0a502081000c3c0844205410340340511b00d5002c4d140c2d0303603d000d4003420a001d01c40d07160300d8500b00780400800c1c00d000d5200c1440703030380301e4802041488401d83d6140c256a03045155407d10407031400105201804401011211101c0010401d00ca892007402401c08079001ea85c01e0003610000021903510000192005040424201115 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 867494793 1250 867493543 867493577
    0xb010215070c0203031b060f34140d0f0b0303181026100503070503070b0306060412120e0405060d060c0e0307170d020307150f0605100503040203011b 66
    0x807882d501d01c05001c403440c1c92045c03c0d90800a480750036034120b00b82c0001c0c0a00c400b141001c06c00c20b4000c1c2584181c84103240e41d582c80d40d400c0704050802038070050b002150024505014201d40c40703451785030502c625901d080c01d00d6180c00a0055600c0e400344a0b10305591750b4801c2c14000140c4d08c07484080503161755103a071000c04014641000101c0b2008002c02012945040c0c1400900c21111040c5200c1c01c041074100640b64a0142c0c84a410140c00780d4070414040105540c0020707408111145000400e680e81c035a20003194480c80707203402420842d07103892452000c0007001058503050011513558101d043e4040402c01c015640c06482c2c969012880e080200d000c507002c1c0e0301650400c2e030982028003035260010302103801c1181962211807005005040740b10118170034031100b40c0071092403011b1440c2c20120742d0390b4140240b0b80314040d00000c0d95542404104040f65003d94080c100c001d200c04105050410b000340258000c5904034000e5080c18030070240442e0f10541001056100c1e02c900d03100d603500e5604 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 867496043 1250 867494793 867494807
    0x90803040317070c030b0723040509100905040f211202090d0507080706021b10271202031605011e1419110703030516050313080607030b01021507 64
    0x20400300da00c0c1c01c0004000084c810b6500314010362003083c3e884440d2801034401740640000c00ea80e0100860081c0c0400c2c80e41080d5411038066500444420300d1035181d00c8034000c440300b003d0301b040f90590300d080180070912a0124443e17440303e220b0186007000e070f008410810941c0c0c00c82117a0f20040f03402004001d003052540d030041c144034400908a1102c0c01110f031a000c2c5003c04562009007071760419071041c40f54039810f101c0d502054808070f0440303212a1752000030555185c3d130518003108004419001020b591405d03010210243e5400705a210660344810300c1c2200c51410708c5040b071080c030481e0b107021503060300401c0c080d04440c0141c49500d15446007120004800c649400344000b04003525528041c41807803c400b4000000f03620b040c000910103040c0c005885540341a0401a9070340c00f0340c0e81000000e40c803000701c031541c2d100710000d07135180800c901c0c01a20b18042d03140c0400769066044000f054440000031101e20131181c5507000e01151841d2001039860350388000d0f04070107003049072000425880c0121a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 867497293 1250 867496043 867496073
    0x90b0a030f1406160311130308090604150e1e0102120309010905031210080a0b04080f09120c040b0d0803010504020711030a0b0a14060105070303110d1a100908030403 73
    0x12030b54412045800707106060110440311031051580a1084150850703061080d24114607020400e186005201d015659001560b48002002c40c4400100c481d22034507541e080e94002c0c088294240d03608440b10202800e08500c00324598002c50000c43c410b104259270304240d804401c4180c001e8074110f80c800301c201c400e9a000034000b001c01e6485074548400940100014120348150b02c25524050615070500181c60b001640300b091154000c0303590b0340108124102180d0040c0e40301c440e0542d10380c83e85110301d040703004101605503c641030400300e01030720a0208600c0c54000040b50100084040340003001540310003101c01a161000c140014441030034550300500c000360040d5441000c41005800180c030b4803000d50022152031111505100490a681c0102e2060035915a401056840c01c100001d00078092070030082c040584403594a80f2070400399080318900c080c0c000c01404040032002c040b003140010706c403d1500440301d03040daa1100303a115510000070350306212b001d540307428030315140c0c240342101403c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 867498543 1250 867497293 867497303
    0x15010c03140418060b120f040221030306090a0e03040b0c0304050901060c050f07030f030c020114030c0408160b040e1f0929091f0b03040506060a090b0a030f 69
    0x71211802000420300584001c003803910020640b400040c0c1000c066401c250300803130000380306204c0b0079900002040358580c80003407041c1c04201030b40e607400060030070f500044480465441c0c0368a003106112000c00118400e0340300355403030315543d240e8800c028112105e1110701c03d5035401c248028418203000b03030010805024035000b2242426103500000c0d0035800207902100201e4074205a0004000050041c5405256164094140d56155442d485010691920000c007003284611b150011a80621b1601001c4564590b0840d200d01d0210780b041519401406100011300c560444002d008108204500035a8240c05615040c1454a01240f600c44806000d1214800d04c40701185000400e003c00100100014400031420860840c1c40c02c00d030306007140c40c09102100c44907211400782c45151009402034040700300500074050400114000700d10540040d85e002e0800070034403082c0000007640502608c0d0072181010071566810750202210640d0317441c160400403400c000c0021a000300700070144e250040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 867499793 1250 867498543 867498557
    0x28020403110d050d180f140a0b0f09040e15161701030f0b09030c0d020a1e0308160e091504050f042418030305040510090b011a090a0e010302010e0915010c03 69
    0xc501350010718089401210f011440c17030400c45e0092805023030b400020b00c000c841461400e40403c1c00c2d03003024405d02031030074069070302d88480d100c80410402006402c0002c800300203a01e0b0902c0600d005508910003007050014404881e0351390b80066034000719040b26800550303040000c400d6600c032044007900800c448103500081c415051008018001c2c0031261104d940074124090b510305d044000442c80c3e004a89046014000f03800009402043c02900007a44003101101e291215104598a10b100d00300309405c9150b61041c020088005140380350010012101417011b40d5440c0d4094901c0710040307030080d00ea032110140809200e002181203205020007107a0200d1107181c9410030340c10381502c41c00110002503a0308104002e200e0140021041c1716441c0409014900130ba4071440a07043c0107015022070910b0240085185510030412500b904901400300c502103580c6807440c0c0811202440700780c1c0420040703207034480345140200030b0071700c01e01081204c809043c034100c00444400746a09806c9080c4451 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 867501043 1250 867499793 867499799
    0x7121d2205091c090501030f051303030e030f070606030c050303091c0c0b070311121306110c0909150105030313060c0f14030c011b0503060928020403110d050d18 71
    0xa14028928503c04603201c50307445914020004003200c00c00e01e8940b07049403034041400707201d003104696848015054500031800a080b03141584c11031003010707100090100c0000e0b200c1c08108040e0044030459000384200141ca0742d5174410b154681c4103421005900c005074801070400e8800340038000b204a07018865243e621610340028041c1a40140c0f0168049001520941d200c3c84040058075106842c03440c0160412100811a08017000036000711000d00040345883e920b41c00080000b01204a0010700b0001c1c541845078025403920001e810030214000310500104007428000100c410310003240d100e42d00c07443c3c41c0c0740007200c41d0050708604a60312501c02c804403003c43c41d0307000103543c17032425180515680c2c0c80b4000c0103400c4410401c5000107000307441c0881112250003a0559911110079250400705a0300d10f0b03c0e8600003148664a00350858403044103007100d14565002c0c0090340d00c140c09861055100c401040100414000010f01c1c0398001c20700309000c40d100300b0070180240c951448444005071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 867502293 1250 867501043 867501073
    0x90b01030b1e190c0e010e010f0201020d1d0f011103060603070c2a080c031011040306060b030114040e0a030e01030b030f1c11030901030b010507121d220509 69
    0x1400b61544a0b03a40300c400800161a1244e201e11010300409007002034004400e400080e103c540d040030100d05216915111082c580e0003074040724229107241c002081583c14101610200425856600030380e40301d4810045d030008014410034021a100030201d07400c59036001d040145a0f84001c1420003007080c1c80e8100d00000e244490144000b00250919508055802c020824110215801030009a004200c440308a4402180715101801d50b81004a00040404081003051081b98402000285041c0000400c0640359002c2c505031900c40c1c00a502c001c202900b04026555017442041880e00500c0015001a0040301d00b12003039101810089040210040000d003060b0411140c510703103802c0744640c02a2000e000000d00113207031050402c5000620440d070700c19607030300811610906150761060082510fa0142041d1200d15074802d10448810b12200300050101d106003502d070452400c8101d5140341e6103040070070200c3ca0705040c01880c003e003800d038484070098007007d0308440c201e02620100505401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 867503543 1250 867502293 867502351
    0x30105070305041b0303051b0a0b01090f0f0b1011102c0f060703050c0910020c0a14030d1202040317030f0901090b06090a110328090b01030b 62
    0x12207840002c1c603440c050070301180b181501c503920500340c0c4c4019401e00001e500f01060780c17240b0b45a050318001e0f8440b003941c0e031840c04440d4140944824546000002e0014039900480d07a04484030005002c021010a500e0f400d1f1410105a903500090429903003030150710400034142040044d40449e02800115284c010480d60303598006030407419450072255125184504c1c400102c41907500800c00020b0ba8110b081d110030000d0019810161250040307070954510b4425181d000c2c0c2c005092041ca8261440040d50750300c904001c00b801b45c1652440040d80e00140c0b04402e849000240c0580000c9401c0f946c00c86004642c481801901e6038280008801704500494000e07122841c0e000c5a6a40d0802840c40007942c6401016182e403a0b0601c2035200018150019071500001c080c1d401803080c1d218190320a000d4070b5140715034402c4442c00300810524401e968644c0c00c120011130381c440182412005030106480c0c1640c0003030075010b1640c004100045c40c030540c2c5503004a480d00b0500c0e10000c50781d0003804032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 867504793 1250 867503543 867503551
    0xc0504020d0204050405060a060507080703020f100501050108150112020901020111070f05100e1b1f0207061404080607050903100f06030209090c01090e09100e0607020d02070f091802030105 83
    0x110b40d0116040c0003034206442010b8000304d08a50032609146005e00040c081d00c1203030002000c603500440c00d442014001c102c94802119942c0940700ba9020440854008207424030580f4002804c000c003140c04002072100010342d203a01070391000c42140300d001d8148043d500004c4050f045658030b00031a00e581803164090311070716203d5071380c0841410750707411300c1481c103d11a081d002c4c45920704108030082003000a4448401c84801c03c0300610328802c6c0001414610304001407070701440028036009120740e07011070040142d5140d500d407004241d1500300b8614031382c0502d0140d815164012008540100d00420107050300c030100404443d0000010802c3c0340a036509081503803075560301c50405000310700c0c04c2400644c0c8007680e14000c00c4000240302c0001c0c0810018440c2d10510849080410b45403041840395840301c0c0224a02440307001c0590100999640c800c41d0050f00600403448090b460a20205600040320304480c0a00d00c120700380b600030002821001c0103114141c00d000300c0c03076006031401c0c010103104d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 867506043 1250 867504793 867504817
    0xb1003050a150e03034501051611250b27040b01020a120908010e06010315090309032a260601050d0b0604020409020c100f0501150503040c050402 64
    0x2800c402881c900003660144104070f003180c0c20a0081080d49018040b0010480b00d00f4800d18151000368825502c0c05103c050280400c100b9401416031104815000240038070281d203100903c0c12004601250042c00032080c0c00c8641e004101000c00c4001051010340d404580140301c020507541c0c50107000301560000d49145000c1440d603058400076104805a088200d90545007401451041d030b0000f91104000c2c80020420103024005282451198a43c0300c00b40c25004000c018040c101c8510654803d001d200c01c81b588911683d15512a61040c0035425240343e040e1510f05c50b0758119a10000001c5080e82c40c2c140102c070207141d003200000f107a9480d0000b822511514902c08000340360558001c2c400b00901c0c031f000e174400c0740100401c0e1104010070741c115807c21613462041e1a400001f801034410f96006460030350012944803402e00012a02408070b0424180030080d0000d0f81d4559415240244911075240b5846010482c405000303100030750f806881004104d882c0c903101c10014089800800d03103102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 867507293 1250 867506043 867506063
    0x30405032401050a1203110f19150209091b070c030b0f090a0b01050402090102070308120f130b06010e0423161d19080303070e2b0b1003050a 62
    0x3050680c0074146405048280c412038126424002c080740714404d0b0440080410000200300c202074034050204204005040066072950340c04126109807016500d142074980d020580d0300c640d1074000c07620883d04e0741a4090f100c0c1c1515968800030540407143d1060b001c0e00341d0030412800340081c07a28504000514800c114109042c02c0810802500800c000c00714000b03540180d007400003140489520780e044550450b00507075242038860040b4145006070f84014107070080400c000a009008906092140381e10110407600350392400d4600141d60154000130340403028060202d4900d510806849420f54409400070611041d81c00c82d00c2e8440a1040801402c076008006002c02a00c0d010103403110a103280c50090316071041c80400d00002d0020200c542d20030308a9885105003540540e42d031030000d203d4103041c1c0c1d0700d03803800c040c02034514414101442d20418104007031103000c0001008000c04114082d1410561950720364400308680c4020b4149106000c1e1a0f0000001030010022601d00f01c1c0303c0c02c4000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 867508543 1250 867507293 867507343
    0x1c1407050d090815181e0d080702030a14030c0c030c060f0a02181908070e0405070b0c031c1e09050f150f04080f0309030a020c270903040503 62
    0x18041802608032541c41d40003141a10311504d04441c0320340d04028050f503061407020002a90314a40004526040e01c11000219454420800481d481e104c824403a11100103a90343c010040fa01c0f0701c511241c035808642c191484603100c00344040074691003800c0505091516418500c0701d880c541000d2410b80f955407200c42000701c40030b1165400c85d04002080002c0d0b00b03207d580c501e04105041072001d490b005642e400e031a1418203802250490042c5647c3c0c050b40d50640d00c501c42c2c2c18105908507000e0750144268040040d00000043c110780020613903101440c14440e030700d40c2c0460a110301906460b5815202e020809800b2043c80d00c40745c681c3e4100000203806403481c9000ca042400301e0380c001f80340c1d812100c4070701c5081d01002000f590045c0000d0b410f50041d9254500300c841400380300c1d8038602e1000c4c0402045200c3d05c00000406407204582c084983c01003c80b4200458003041c2c4a441540301e0302c00311501120a80401c2d0341d07030062005000e40741426107400c0803a01e4001d0b1402c0301c6802c4507421140d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 867509793 1250 867508543 867508547
    0x172205030c15010503070b09042c070b13231002030a14030403020312071b0305093d270510030b0102060411010e15041401020606031c1407050d 63
    0x52400c2c016445120102580f410740000d864038500c4c032a80c011080300107030301400380c4d4641d400884150f480002001c0070310038940070402c0600f15107400070041d114110f004945000d4100a1304c6441e600007440c1010300e07092180d40d03411175401e001748030110410400502a6070b520542144a81796240c0d000790b499905c0100010040f6601c60090802654200148004698048121903849241c02a80c641e5a100c0075000c03106282c0b4406c0c20300956002030b0781708d41010f03030120040c00030381c0c8205c807400c0754440480c050324920004a44036011446002600c000d02a1089810b08581421030400c46200c560103030400242e0124000e18034600c04402505000514091200a4510300303c1d103001c000c18154000040d58035280500050404070f150300d03059440b82e00c54155203004610103031039001103e00c8680030016a030820700594a40f12080020b50803e9440003c2c801e214000081c002c084002110481c6030b0031018260320342040110501c031103061440418000c0001b90310030390040078500e88103240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 867511043 1250 867509793 867509803
    0xd1406010e0402160201030c1803060203010510020f06041b031b1d0c0901030902040236010f0503010323070f05030607090b120a0e190b07050901172205030c 69
    0xc8148100d206020b104c21900c04080012402075080c01d00081d110b101207019030f0a060b40101691558114410203c100200c54000e141241c0060f6105000c4064120f801d903100c105001e95403d55a018400080c041840c1d8000d0300000740e0940c3c001d000c1d203510707515000417030f00c1d50070090100040340c048100101c103241c0380810b035064807581d05c142450a0031195040c0c944070b200301041c10581c440341d03480c040d50307a035904448541c100c0360b103059000d202c0030907246440803101c0324108140440c9e0018602c47e50081074017440c190755907912285103a0944e503070b1841030f5082514082c4074449003208800f050008000c6100030303000b1b183c8200704061810701054503016000304403030200402005d08000072562403066074402440d036251104259205641900184201d81400c03890348a10309000e0350044000c0325080c00280951041405030741c88050544080c0302c0c4d5100280010050f4102d04000c100c0da041c055008a100d5103c8020701460188111a0490007081030320142c200240681c814801005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 867512293 1250 867511043 867511067
    0xa0c05040e03030a0b01092103141309020d0b030601030c090f0b150702030f06130203010501080606010804021002070807170d1416080d0608010c170f01050d02060d140601 75
    0x190911440688501c000d80700e00015042c04183c03a12034200400076806000e04801800504042c0266401d502440b01010f181c6107000340c012541c0440c64800f20040d02080b07845400c04005008080b0b443c00c000d22009500c154541d50300740b6510080451640e0b828010076000b14050032007e85150b041950304000c9403185030f40701204501e401d01170750700ca0700e80034440340e51600c1300314160fa1a090b0702c3c00440d0410071141c003103148a003d0314040006400c000208140d40c42c0c000c1e40200000c4ea01c44444642e0740c20143d44280c0400c085034006001450b107460882035010b41c91042d1500c0959890280703141044980001d161961800c455080d400020001c0345200841450b00e0255101d070740c20148211310464002c916888803016519080c80780c0e010442e43c08174203d207810040c0c50341e44c0318114000d200d17600039200010300902c00060010700036481580100300211100386280d1030181004040040c3e502c00301d800c80c0d010b00c0503a03a004a01d106401030f542c01182d003440c00780740420004110340307520a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 867513543 1250 867512293 867512299
    0xb13051305060a140d06050711011a3d02240403170c04260f06150d0317040c05010305220602090a18021c0203221103010e0a0c05 57
    0x801040516542c1104402c1113400e0080444059000e0901068191007468001b40a0303a081c08140480240d1080f032104580403408000c001a080410554207080d00d4241038035030100b008180102e00310000c0c650b81c1c61091041d280450350322803000219909240403201e100144c1c0200410207600c41612560350008103c095546002d46020390b4080c1c00082c08030194000001c5a0002850340110582141d010f02110703a44112403800d1111659000c01d90b9040c0e82c0c4d4640101944070383c401100062050080341c2030054008a80515014481040b45915082d810407002800d59502911360304070003801613010b5190120003504200014007583d4001e00040b8213890320303000044034001200c8101103940d50000001d69030748820300000703c82610b190450194000ba0409803003c095599000384095144608000c4150444440c0c2100720302003150303052040b4184200341e55804081c004403000c0d8602c00c0c01c10b120340c041540b011908403540108800201d90004507284103000d2840442e0000348411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 867514793 1250 867513543 867513551
    0x17030a03050c030103020d06050c13080705120d050f070f06020a030f05010602030c0c061b1203040515070c0201050c07180b0108061e2103030a14100b03070507020402040b130513 78
    0x7646c0401c00101c0c1040c0c01a02c960b680d0000f08a2000000003100c14181c070781300f1240a8540c403143d2054036600c00c0d21501e803003000c40312081d010140c070124448940780c100d43c41d01e44c1400c000d042100e0481c0d0103408116105030714124444d000819500c05890045a280d5001560b8007800304044212681038010701d0075584180040320076800c0c0011400040041035890540322180107084001c1c11650350030380040340c068040c10403ea0040b400145202d01c2c011011a015000d50301c1240300005c509985500029030303406010405940554028184a281141161030a55440014040d00700d203001e61600e02a841d2400d044996a00c10b28183d004002190050421a20005200103404042d60058021520415140107c00025404120030030b5100b099913036924103044503030020045054a0030114041101084110065404e020192050090810310710f0715082d60554168020110499001c0d80802c030110340684400c01030014814402c0c0d103c500d05003001c040094005101a034140d5861030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 867516043 1250 867514793 867514799
    0x9060302120105191109091f090e0c0114120414150105090f041a100501141908060a03050a0510180507050f0f040218010f030204270617030a03050c0301 67
    0x300c48015500700c4051680000c445c075a0011152184c0101704409601c108050100701c071991280d07800d8140840740e2240f00304216103890103c03040310082d072908100756000d0f203805c41155000e02c1301440c1d001c2c9101082c1e400e080c0308554155129004460450b10742200c41c041d100140e50403c014a2144210001d40c0c0d4650704000200e690300307400908195040e124480454140708010b4210851400340309002e01461030401001d0711001241d108040c00954640701200c103a2801a09560420311592030030607210020f0300c011605290044c0003907910008400c1d000002400c01c2208a4100740f0443c090440d00d106d141701c1c5412500d01800b0f006004a201541500207240403a00c901514400c031a034481e44180d58011a404c000745018450704a840042e4001000320ba0350b02d080d4000c0002d036940d0011184d0310100710241d015a100e406d1250800e91100c008140d00003519030303880b5040c0c4e140000e150b0ba030340c50700c08210140c1c40350b0285107400000e08030024a6150003988e034007507a050360061035545 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 867517293 1250 867516043 867516061
    0x306090515150d080a0306080604140d0921060b0d062a0c080304050114181c09290301060504081207080405010c060b10050a0329010c08070c09060302120105 69
    0xb45003c00a150020015006408034020ba0002c005005180201c40c035600d4680f505210f0084140c0f102d904502c9985920f880151048207410181c4120703504c20980001080c0c010250171240d00402c54056484009546042d1140503000300d241f4003071640818902561040a00340c412105200070000c501c009a5600141e001058411580d40c0903550a0b40c03640c650501c6030040ca115001c00d8821060342c000e0120310000070184d40446000300c0c00f504c090300c04140304600840c0b15404100f000c11005803041100c00480400c3c0c403030300030f0a241144241e401c419400069544241c04c42c001107400420300340000b1000f00024248030460341c080c1d03460310700107880da182180554420b03613041104440c07006003040382541104507040406414864001c000e000c014242d6002440440e00103403400784c06c010103e107616072101454140a8481c90b040d82a0340044170101c1088030700361500e40040115100003a09440780100401807101c0004140742503104000984001100e082e1a51381044140b00d4501 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 867518543 1250 867517293 867517309
    0x15052806180209090a060503151015090501020c1e0f01020a02040c020304170703031d1329061903050c0705070602150618010512070504020706060512070b0d0f06030609051515 77
    0x60410309c40c0709071541c3d03501c0605200c6455402c0b20302e9882d16100e8218a9a8004c1c01c00c00c2a035509800340eaa1011500007440b9401c0d0410700301d40007942090b4011034090405034031701429102d041c8150360049940d0b80228060b034081d00603040060340000b40c104142c0500c4a0000800c1270440c015101840c510b4800401ca9689000b01c01c21602c00502807038503640d01d0b0996001c001d00135450910546c121005960301103540660244070f82c00030401500d403545403840459524448210881130340e540c000c0300c1103004000061881161400400441d008900204002c400414141c1d0017050820014602c1103007088000d0040f900409101c8807201400650418641c10342d0004e43d0080c0020300058242450500740340d00c1950000c0c40026003c081c80103e800c140d0a03140c0541e021100c0d854000300c03003039840c0c0703181c820400303c244244450003658166030824090722024690102d041d0b601c81c0c40780c0046442007881104c240c5d01c6607084121a900e40084564881686001c07501d5260605020683c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 867519793 1250 867518543 867518563
    0x90a020a180b28020615040e0a06090b0705040b04150203120c0c0d03090b070e0307050607110907140d110d0c0e01080a021e031f1215052806180209090a060503 70
    0x361b5020030410403034666510640807031265101b21010030505090140c01482140c0099401c98076040c0080c1250707009000312012030b2050032826103401e14010341600e59940341000c0350210300082016110007011192100e02600b90094080d54805905070300601c0d00c0c04100e088400d050801d590003011401c11000107510141c03a0801400000c130080009080c103540c0d802040e401400819400d0a01800012040c03000a05035044200b9464000d0141c8868030300382904041b070502040700241015080d08507074250a06000805c1c2095040070545080c0c8003102c5600740000d100c08070070f800a41e845035109802010380c0c0000c52a20007400003c55250b50902d03c107000c5c2140010210309002d45c824000500b403041d280361038403d00d45683d4084401c03025910b0a4070601d600d4030104008181e03500ca40c90155021320003994423070117440c1c6051700d04090250340c100c1c400e985141c0055002c1200c0310300c0b040f0081851005a4030782002c001c025444402503c03010340c2c1440d0080c180007a4a00007214045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 867521043 1250 867519793 867519811
    0x1e0207050a0510030f0c02010606020601050a0e07140706020d050a0b010c020a0620060108061b122806080d0306080f03030a02030408040305120324090a020a180b280206 74
    0x188220680117028810030052400b0b10708642e0404641c3e040d1b1240341522540c1d400c0d91141c0c2d81c0d038400c01811503070b10300441c1c401c42c507a000800c1c44140241e014140719050b01420720300300030580c1c884074200c2c1c100300c8408046940703503810801a90240d2240f00c0300c14400b401d1940c2c4201054000c60702d03020150082c14184001e85134410280c01d40e1854000c850400f1004407141582c40f90140b03511080240c94041440b0004801c00c0f004104d90030540340d4100070a0f00b1101c440c2d0707480c00c0c0a003640e0400ca004180481c4480c0301804442c1150280f00080c16107600102503441040da8020b0803141e20b03503c01c407041e401c040110414000f0201c2226003055101401607106c4d150350a2029144c407590388000c000c0d02c28124400c689803803c001544c85607007581c40049038080b18280404003c0300c800a0180d2001b91000015004030040c2e0241288006601d04500d03100070000c10707020005019081140303101400f1510742044c590b00149240090f54848151007803800902d0040e68035000a095182 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 867522293 1250 867521043 867521059
    0x180a03020a0209061810051f050901030b0111061e0709060c0b04170409050702011b171b1317030f04060302090d06090f050d14040905190603031e0207050a05 69
    0x801e503845c0400321003106900301c420400d81c10903514214a60b600d0b4414180107c90209001c2c450034014548080d01e400b0584410707180c01c081d1401140186000e07101e880c14030140505211756014100f05980c4034070907614803080400300303103800050014401003510301081081310052100683c007040c058061640203042408030780340c51403e010300d81700c0802c88540010010a0015640200d42c00ca0750040c54a60020002600780c0807413440c4c0010b54144d21000720300f09240c11661801a0450a58813806580740d032103480a211400b0100c503880141c000c07010300c081c0082030090925501240b500202c2d424000c5d483c2c00c600884c180c2d4140114072620080c941d0105012105488408100c55520380c01403040204102600c0e202e40010301c81a41502c45101d0b43c14030205441c060030405011400c040d1002e030070f0a28180031480a002700500c401d40b03606030030113907600038030307003401102c02452003901d441d04030340700444044002004038141364085500c6035404000c99140c1c0114038050310402e4840304 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 867523543 1250 867522293 867522301
    0xb0903031e010f1a040308070b04030f0e0907050306041e14010902070b180c1302030109150803161a0411151206010c050c030607030f06090e0d03090f0b010e180a03020a0209 76
    0x30080d8045c0e54805800d540300020305404004110b42c10500c101e1080d00c3d2000f0881142804031542c40544240c0c0390002681004130300325602544c059030340600018404508810100300c50865200405205c0e01410f0b122030b40b040d000b45040c0c0c0b03140e015203c941421420310b00d454030b907000d80280141074007100200307089031105004030610081041450140c60000d0005503203403420000d510074800c0f000341d00e260004e0709041d4904868600308845d804801141040d50345060751075040741d40c1204540101440d8803ca2295805108040c0710b18000c8020318040301190707081c8118211507001c100d100c482e0070020f481d070180c01811103642000d800e2070724940500161420070325040d4201c05440d454400c2d5410000c80a5040e0406c0c0306d01c50079100144852956540d0a2081c1d0310740910392400d070303040910b401110502c80d03030203d59814052050680013105544851a009400ba00203680e000301c070750200701040d0a8078034050178100407040206061441b07078500941702d08100c1c60081c03040880401023 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 867524793 1250 867523543 867523589
    0x3070e030307231218010807020c0d06050601050403061407170f04080714060a0905011a0312030a09020604030302101503081b10020d1b050403020105160f0b0903031e010f 75
    0x2190b5102103c01c1325130700c5e08202c00788400300c1914550b40e40001c1105000032026440030941100703090307015200d948110420740e14013029100040201741000350901000002c1800307801348042607056640203401900301044000c080c0418074943c00049800f0105200a0030800031007950300c541c0125440f0f0315003c45d4070341075480c040d1840c01e1600742c1c4034583c14020044803a511000351244900c0080050808902d1580481c00304850780076450307000000505002d1542400465008903160030002e0040070702e40c00105117401c030b80c00070360040e40654a452148038080c0704a0522500700c01e42e04640528560b01c0b00c840c2d2061813441900301c078880c45001c2a90008000c5540c40080b1900150348680341c0b215418000c08030080081c13058101364100400342c034000d60448040e01c1d01a5600d034a8542c4000400d003605407691b0085803103e82c030764106004200110740890084c61110080d550341d08080c0250b507034031000c00981182805a10b0010852002e5440e110340c1121420140c0d002204250034135 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 867526043 1250 867524793 867524803
    0xb03060631110309061501020f100905070305060403050d14060a05061810020a30110f030307030b130605011d041b0c0b0f100b0327010203070e03030723 67
    0x30b00c6905401100b4003988031400310303c8500c10f1010302d020b041045245001243e54100906115010b6080040c40014808498208006850061044651641c0e9a41d02c00d454000100c405900040c00801c80004800403801054101c0c803042c242c01009040c100e0010f00707030701c001d0301c202481848001a8072807421582043e8251201004200c441c0c5c51140c400040d49406c000705045983c414408441542070940030740c0740f030310a12220b0350f00b0005a0304800c10307160581521714845003889124800745440350108029032242c04195408200701c1801414405840c114400f1300009600349602401f10382d0780012a0368035118010000350074803101801040062a1500011294030726840783c4d80c0386560400301d40d1070810301c01e062504040e5240c1c82c5281e80400140e4a06034401040b5500704100e40020780510340102e021a0000000100b15026901640307040105880594001c020403620a0304000e042111041c242c01640c98140180c0d103142038440b20a14105450f002205201481441004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 867527293 1250 867526043 867526061
    0x9090f060f1e1a011b0b151002060f0703020f09131409060c0409020f0f0a0c050d020a02012001020f0a080a05060105121503030c0106090b03060631 65
    0x60100012602115458054544005519450304128454842c19a500d2080104101039594500010040900115500c42912940b100041803284540740450700640c43d89010f003980c0b0103203203d901408014400e504c24041001019908441c0402006e00b00c07180c08940c2c000d6851500507034500c6604400d030342d1f50050700f42084c2c03c010091307400c8050303c4040e0b2010540c12a4070400200690b24038511507501c880c00c444082c00c51030180001c1210550320340150100e8091500d034a41814101c00303003052560031203441d42c00016208182942440424080783c107091000780301416002502d44c0000e44550405141880180b04100e0b41e20700c500400c0d8103031004440450b40266071201141d8004186540c10b0351002501c0d40b40c000814000c0d80188101c4009142020000c483c50380c0d40b246c9034809040006503150940400c00c074021049a080c8105400383c81800c1c0e0000304da00341e0105052601c000148901d0140420520304006000c6462007002c052403c11990012803811641407000341c50114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 867528543 1250 867527293 867527303
    0x10090201050d0e0703020f0a050d03210507021e031815120c1902150708130203061315020702010215040503130e070f0c020a210f0b0714040b0409090f 66
    0x2146070b10110f00d0100d9150b048a00031905000f55402c9101044400d0340b0a201d100c1d40240c0d603a60980004c0d000e01c02c0c0244c04170089403168042a01140000140c88040710b5100040c0c0040c0804906407603403e0704800728200c148001d6007800408a02c0d01c0c01c2f41102020136118041d04015480c0d06c01c03144044896031800d4034903042e450300f461506c41203e42c0205203280140300c4690141c0c1c403070910002e4802c2d10b61340d80c141195400e8a90392401c0da45418090060340003014480d070030703101680b410840c0034010910040404641041801c0032503c240d00522803105580c010003c010141c0c3e0f002464298108a00c13882c42c1c06602d480c43c1c154a10b10440c03a0420b00143c40e100d00080703403100006a541700d0107043d200c482c110400700c0c0d0708031208031102c82c1c025400258250306201e04521991004640d40d00844c4100c0301c4200c0b9142e83c104107440c04003c56842c800e660400c05401c0d80881d038240b02e018035001103401c087c1842102602c5028500070b56090b40c2d41e03142d609090081c1810820007240e001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 867529793 1250 867528543 867528551
    0x2303040f090204080f060708010306092f130e060105060a0207080610180b15030601050d021b281509120e090c1201050d051c09030213060810090201050d 67
    0xc0c100080650060303c0f8101c003a014030780486844105c00f0070154407401444e6900d20880e070a598a1100414007541d06642d80c4540440c0385100200c00c88136100b2a01d9001d0b81c024840e0801c40420120b441904011940c0904040942440e56400a01d083c19102d0407200192100c00c103c808900c0e01026510081031403142406104202801100000036a1101c90f4001c04003245a6254019108602e19079034002640c0904030044110031800786800c410140b401307a2401d40b13500884000d9811294000200585426164801c6001040b4610081d209040d41204200d68004030b030030710031070002001d03040c0f9091400000c15403a859000506140e13202d0300705075070806030900060100101c900c0c12402201020302050603418018141c03081881d60b050036865503820f01082c0b201c2084004c07012102c51181c1140080d01d03605841e109118128940c2d60b04413441d2035401007114100b2400346440040d464840c0078000d0401c00315403201da01c20602e1003c42c3c01404d0340300403a0540305011058002c84d03d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 867531043 1250 867529793 867529799
    0x90206090d1a25110a0204091e080309010605041e0f060312021015230a09060b0304031b0b0403180305070b0d0e0c1f1202031006030c0207032303040f 66
    0x441190a61042a9034500c14034580b50620103955062413000341498607400b510f0024010701d081e81241600038800c00c0401a2041489000550a00700a200f00c41e10000031082106400b402d12407035000f400216001e1000e00b04c02042c003140300010079402a07116869140310040c0c0060741c0c001d0310007142e108242d80203880c041c0c0e20003902c41004030041c40081e4200700010255588ad1100c05080e94580d0008502820f0f9000b1240401c41e200c2c4443c1d43c05c40a07040c80042c400500b489135000610074402c0d243e64a01e4a464000c1144030049220203500c0f012036620f1010410f8810321a9015503d414011450b0034000c082c4142d8014a50004000c0c1c4202c09010070005002c00190004c00a0a03030144140e80c803440f85240c99040b00420907422201145611013150301c0c0582c0c3d2903003500e090500c8904203d1220b403100599000f01d40707419007a01000010000c0ca0303414461306803400000d2002c0c040d42415552035161003040840c0b0070483c03518a0003041150a000d2080354010110748400040140d9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 867532293 1250 867531043 867531061
    0xb030a0b040f170a0f08072307150504050c01170f010b0304081b010218010905060d110c0d03050411090615090102150f01030b100303050a0503100b0a031e090206090d1a 74
    0x103005e4600068040001300d20854010500c89030030700c103070a5440d20200741501c41c00c07415400c19013064407c1d0017400b4891000101c14407480d0300075406000a00103080704080050507403074a10a00c80c003051b00100070081c800109100741c0e4150b51000481c0c50f5240c903113040141e510301602c1002490945410a010502c2e0f00544c000d2098500ca15090b080c60480b13100113440700d075136911030b00f5000002044074460711041607001e00542691445110b00f00030754010031030300e080c1046505a0110b591031341400280642044040d4051804507403501e50392a043c80421006918500c80ea90740030004100c4102da41c0c000c1c004c5c00b1110307170034036440c40d003d00d400c00e07294844202c2032001344c0340082807901144034110394589003003d80b905616550720b00004920111070550004004007083c00741c07d04081244045040100408625550301207961300c040e550120030440c03104a410240d40c03038000d0400068546000b81c0302580310865484500340780508003070281050001c03c00300807800780401c00201003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 867533543 1250 867532293 867532307
    0x11060706021305120c090402040f1107140111031612061d0a050105010203280c0f06020c0c060c120721050c011a181308041203030b030a0b040f170a 65
    0x507030100c4980d040c1c42403003c4010789a244008017290080d11810001303000d81050780041e0440590410001066540b00c40c03500e0142e00020800c55503c807100c680b03865102d10901400c00110191058285141400080d158840400c0c0c1101c005004007a40403a040040c954407000041c140d40c60301a22000b03844680108040701210703456101d514040000c80d16500c004203030b03500089450041300c201c0312070003454a24482e00018250130800304403200000194000c5046102500c100c40150711901c40803030450420380406400c50181105000000e03800a000400b14420030a55659a46d200d03101e040c00d0910010031401e0071000800103182e5100c4540c060001c08030856902e008100b02008143c0c10081e0986904100740d008445200e40300d0b04040c8a0b4481e50481203000f1000d252801c40e9a403604160455400702410b1504400b42e0707010b041d098001c80380d840c8021000b0389944e10080e0381d140e61008010b0000307071240043c0900b4504000c076082070442e24180d00d030030031601d034505008010560 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 867534793 1250 867533543 867533549
    0x405130e121e0f1615020d091a06130b0d081b12041d0a0e0706021b0d0818120a0f02040e010207020102060403030c030b220c050307050403110607060213 67
    0x81c101c0900100152403404040da5050a44070200710700c4e1550080c0d050496000500094681a00c00301468407004101e100500480212070b10114211190b420001440140d0f0284044160f401400300841075036142041c98a19440c0d180000d0f15001101c04900306007400308c00240304801c00501c01943c04620350400c1142d004102c1243c00b0725070b4239032444c080c900692241c04245034100d00988601140403c019a000b0000703200080c0707076001e5032442c5203014456401600507030400441400c2a080300e511480f0000019140040b0310841961841e080384541141e50510b031925941b2000680d8500c40034a180103445011120ba0b9034450a0643c2100031038030040348103d10f8060b40c009a0074043c000d440e1a03640503001741c02c050791151002d801420602d81d914082559034102d204081c1d07252849510035224800c0c0700d0610349900140e903800c0710030030340303108040c02028010010016030020480f000d40764860081c00e403026910b00403883c140620310b0010170340c80c0042141c590240c5808046422 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 867536043 1250 867534793 867534817
    0x151103011e0f060504050f041e0507020d0201021c09030c050714010f260a020409020c1c05041a0c0a080a051306031107060b0f040606052206050405130e12 68
    0x1e0315581d45818600c50110b02c5010f022070420301c002c102038608400c20709119400a0800300d01100c0a280503800008900021810590307139500b80809a076040110203150000390000310b283c2646024400c240011507581c03402480d80350305404007051300c111107a8203a944d0140840ea09203460358241c181c0451048209400a0074000e080d25140740300d00400c0c00410318050135940082300f0a813a8801401c0c2c02400090000c0d000c002c000b60601151006101905084000e802c81c684452a4100c41070304612002003002000e00050108040e885540d08d002246100f03840d60301c0720f555148a0030518401400303407041310301249220020340c004004046182401a145060341e0316013409030119180e030700304016124001d000c0c20000a103568410055408020400c54003c0303585400070741034075503c0d042900000c0c1c01103070030b0120f003d00c500d2507445180040c00700c0003040d00740304c0000c1c034501036803060911480300340541c2c484843c0306a001d240c0786d10040b419a015401c21054285090f4031918050342c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 867537293 1250 867536043 867536099
    0x1b01110a1205060609090708060102072402240c0705011e0b010206060103060f230a14011202120c070f050a08031b040b04031101050c0a1109010608040b0415110301 72
    0x10f49144c600100d80003039800500515441d110310000710f0307020100038245815849804408500f0080608e42c0186004d03004000c18840310300b401c03000741421803451901081194021071041048074072105140d001254642c1c0c0798440c410303400d0807400361052401c2c0c0c541d145090310240440000039085440940400c1e021102c031922840011011250281700f5080807405401c41489080019080307401c2c0710054440080b462204200003800c40d14495200d5811804c81e9004c0d05041c1d40c10155251812486000840c10200b16110715034140e03030b00401140200000090880030020102c09550406070402c0c2119440821072034445440c1d8026514100c000c880d5032210880d04410b481128140c60303504e103d8a003880c0c5035980e0101c4d175642100410f4117107c4c0074442c0ca064814200300340055907018100300c0403083d183d28207205450303070180c12090030032610a08210205012072070300e94100c0d5100455080550909912500800b0182c07680c07441c50000200000d03003241c0f60145001d1420480b00c0103a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 867538543 1250 867537293 867537301
    0x801061511060708070c08030c090102160617041502160506090d0212030709080607270b0915210a0605090702060c07031704050d1103030105061b01110a1205 69
    0x140300710803070040407140c5038072400005480c81c1c407800071241c0003109400d100c071100c12030360b07640c3e07090750070840c2c0881000c2004a08040b0031f6904001452013005d0161072a0405403c1ca0b030b004001000001c65140c100341d19602040c2003026000704032101c000d9914045480340031410340da50420300c0d00e40707081c0d800344129000724003090404109640c0142480c0c0050464a4032003850300d01e150002044901805507851001400c444c2c10f02c403651061000766203030b0004540101009041d110300082e0341410419081c0c06103e150040f81c00c07500c00b20011a00640c000c1d600b051189580e104080700a00000c02181141500302c1404401c030b401500c8090301408459152000d01030056001c4501100590112000c100f0740541e41d402442c1f220300a2400b8155914494000300c032001d0192400c66040e4000844484500e42c465811900d40307075800b01461843d454200050b4050084107203154003611070040c654902d600c00d41c01810100c00c0081b015440341030201002e000e00003003031511102035040c40009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 867539793 1250 867538543 867538547
    0x2010606051c050402040b090702061b0a09051309020301180201080610090e040809040507110d020606060a11030706111c090209042d060c1b0218061908010615 70
    0xb031a034450b403031811001001c0c00000c80d07001038403001c1c00680c1c100e03640301428201e0303484104880c0d228031110340041005080240711300900111000e4030340c80c0d4040c2030041c031406550014044c01250f0b0308492245481a16136111710042019241c000c0d8503601c1d200c0d21540d4908503500c0915014000d8840202a80c4d4450274004801c900c2041030340004c00400b01482801d4686030034580080c00b8143c2c00d8201904000420210740c815600308000c910624821441d0f004200304082e4a4011840034105505000d00810b4503402a1031014040c800c50405d01c43c40c1d02c50400685040d280c0011f4140505150300410f48610f0f444408454440c80c000c64101c000d040990240c42102039024190350455916500c5e408000b402c01c4942d01480c00d01c901902000080010840c0308450144100103001c011600010b4044600d203a0750656141003141402c0c00343c0c1e1034501010340c026181c4070100303203aa1071100050741c2e170740800c49000d4a0500d0180100e1122015403024082c0c1d204d00305001d084031031410741 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 867541043 1250 867539793 867539797
    0x1e01081b0604030b0c220b032509050f011101020f09040605180f040f02040c030c0201060503070803030412020102040f03120212160f030302040b07080c0105011202060403170f0408010b010201060605 87
    0xb502c1910380701d000c00c040348280b20040803c080b05a5041c1e40f0350040d0011541d02d04c100d80d120307103490b007c044207000b0360310312100341510454141413103100440103a0b0005080d0340818400c5902c102c03c55040d03000540d016000c100d241000c01c00085568022484544076660448011940200d26149e004980c50400d1501c800700c4151b103000001c0f0695814142e42e0240c240284110381064403400d05000503190390084a4691010307480100305542a40c200a0849120b40e010904c26441668100070405011088a0300650031040d0b41d010f411350113100364064072491740b10f5210154201400000e10003040d0501e070309060580e0a442c008543d00d03464840c0c0d07018000d4260603400c2041d0089000510102d0740046162081c10090b04140e603a200144490300f01450a03502c124000450070311482d028400c02d40900000700315600b80345900d13008280729010368080242040c803100c403450240f441400c280d4000002c40c01c520303a031f1540c950800c68060041c01c5d0b4014055070030044040f62090003442 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 867542293 1250 867541043 867541049
    0x1b1c03020f061e1501020c04060602010b090a0b010905040e0c03060405240609011e09020d020d05090f0307021306150c05010b031209040c120e0607020d05070305070b1e01081b0604 79
    0x8041140d41c4a04e41040c281444c18406a030551040b00c1d401101c644a500407100180440e07000020140b0029082c0800754500415500d4040d1612194004980c3c002c1c4c0540300313032201580d001616000d5004811b14120000b0710440c1c1c5880340b8030400080100000b1038091552000034411007680808500c1d00030854140d038480e5008080c80010302084840310400c12010040c0603240041982c1c0d00c0d00c45049074460080e48054540009140d4062402c0707004154005401d113005107012040d4040c996140c0c0070f0814000d103c0d40ca1074201031100c12503071b0480800f4050040ba44881000014405404002c031108100d805500b406861111480d012980300b00f49501465510703d03004101042000070034091080300d0038004902c90450454040744140d85c0510440070050417241008000a458404100c2591040010402c040c038002a4040181c4020740c0e403016150301c6603100c14610744c5288003040030064000b260040005229040060402c8810456000d40e18070020042c043c4079003485240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 867543543 1250 867542293 867542341
    0x90806130312051501050306040212010b041724060d080301060c020a0e1017100e03040603050903070c0911250b130503041806030c12050607111b1c03020f06 69
    0xc29013032165008034000c5a101c20010001440d101d0850314041800101780c01c41004014081400d22a4803e440450a0304030580340041a07102002c0384041040f80701542c4805403040d2a50200d000c548841e8209502c8640c8501150785030341e1030700b034001c20321034480405910a1140040c00680c3c005094540c0b030055041400100169050500c150031001921408095030702c20744103407800c9a805486054070102503c00511360b1517151a4004040e0350340a001c40c84141c204000110010b001c2e401c0e0102124260341001c220402d0780b0b07060120031f0040c481c840c40e50550b070f0785c00307080003c1034001ca0302c042c640700e22030309200da0b2103000c11565441c0b081000106503a00070070080c02180503280c83c0c0580001000008640a03499a03504030740e681da01d0b400300c3c146072140030107041000418810658000342c113140000f1449900c180c001d84d14107100303064000b2410701070501d000329100d0207074407101095041070701081c01d50729240096645507074641e188920f00410010030701d03010002040030144100e035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 867544793 1250 867543543 867543571
    0x5090a05120d0305060a0f1e08060c0d0911131d07060e2e0c060e011b05090d08040b0703021b010f0f020a0b180105061002030301060f09080613031205 66
    0x32402c2a0000c2c90050460344d800b8074403000c00120b503a000c04508000d80607401928044043d110075024440b4016001140d45810030410002a1302c8103034207945010400c180b0105520803a802e02118500381507014503007080140305400000c405903006541c50b4645159421050f1710089030b41034640036580960000200610010b08071031811009121020440450b003144a5020000d52074224586c6000403010a070740e031413102d00740f0800e485000c80402400c8020300002c001c21004090000d0302c00040da060060100d480031580e150400c1000540b41e004c0d5200790380c0c9403145075101c4103804c021011030052149000b02d80c65014407103141041d818042e114180d690b07201d0101030320700051160000003103118a45075035010075100100c40340600180c0c1c88440d20201000366050030358800618642c0500b40000584100079400401c89045038090300d8000b120412100003240c14041a60003410584034513410b01c8080b030407225010b000b01e4070079110b110000d80b5100b040e000760782007250710191088007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 867546043 1250 867544793 867544813
    0x4060c02031b03120d060f06030b010f020c01090603020705010b091f0f0e010e0c0706020a09170c100f260a0b01090b03010b0307170f01030201020c220207050a020d0305090a0512 78
    0xb9000e0004540803000101c2c1c0c1d1616090f8030940f400c100e500080009c0d864198140d100d503000689018440040d10150070f84001c0d10b4006010b075a001e1081800b015400070722101404029840101c030104d0040015006080c1900f07039059450140c1d00092044414100000e501c4040e0b6004c0c0080b00c04280101d001c6071301c1e14824103000e081c0100030000805c1c08111480c0041c0c0688014090740d4026110801c2c5581070000103510403403800b88804080e440b000140c0c255642c0c9003c4076145818610b03221392500e15407a07084490b211081c40c85a452602050300d003a002c20852000f40c8103080600d0100440703010400115480545071003804c3d1900c10030801842000c101320006e55200c5094100441c0300340c15040160003ca070121001401400100018011580d0600821038880c600322480303912642250010b05500c0070b41d035451284554002190300401c40240076a51090b500149880c4200e0303418100a411030b40200c2c50144a055a060046114030340220781c0700000495500030301e00500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 867547293 1250 867546043 867546073
    0x115050310030f26270a1208070615051305041b03030314070206070c0b04030509150306010815181803041706090703030f211a03010f020301030302120d1104060c02031b03 75
    0x80403600302e03134001007606401311f041c06001c103284050f9031090101030358a001c03e041c80700403500009841c62428011103010402d50f5240e200201d80b0035070740310340011152520b15010094510582812410600702ea40000905416500c4410350b00c0300201c0800c060b6032201c81c100d1b154041214410045055240c0c0000441d40c00c40c1200d41c81403103410714600e4003002000081085900809580c0b80110010400c0341c1940e120384c0d00d0340c00c900c442d0803910040070340318001341c68030295095142d444501c240004074401c40140c10076910038a244282c4c0e594a88900c41c40300c04440d0034005800500c107103008510301150000301d10303003141e030036580b544400e4070048000c44c1ca40c0012440d1001c2e10b0035031910010100d0151003016180d1301095012480085040141030039a00c080d0f0251b840720703205000400100350041240c085510400007a00d80e83d09440007040300800c0c4a089042201c140410701080d5190843d415440581c003c40448003404140584884455100c1c501d85425400038121000d240c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 867548543 1250 867547293 867547357
    0x9090b010e1b0712020f0105010302010509040905010f110403140307050a03210e0d17060f0d03021002130509090109050c0603072a02010305010b030115050310030f26 73
    0xb29500030002c11404880d00b0998102400a444000f022182004002d070108121042402c1c900000d004941c95500003030f140c1e000d40544c1c0c034005da848440060030443d0a520030422b00750440e90401189118982d40703442a0028001242c0c1e000000ca1100f401c0f160001c21386000c0303a408001801c0e900104c2c0d03022a0440350722a5a020224000d204034213202020703000318011031540d4001004940d00d07000d0f0041510000240c03460580340351500b4080c0b16140d10520990005090725600e21101d080d181c00ca140081c14040310790328501c0032031081110508000c3c00d008881c4200d5075141191590301516080f5803810340018216800805505201c1c200302000e140d1110050828440d402c0c3c40b0888150342c9226131144089000080c10b00108540e094814107000d400e0500d031550641d810480c0b4070b0981c440344144d00061200c003000084600c515056500c010303580c1b0030030b19681c0307106074a44814103115001006603407850844410b502c09040740241c1d589400514841d012064084800c0b880b10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 867549793 1250 867548543 867548551
    0x140d0c17090a12030c0b07090303200717011e05060f0409031101020a0302091005071e0609060c0806103603080f1801090e040b060409060606120609090b010e 69
    0x20901d5514001201c1c0d82c3c0d400c42e0400d41e4003980b540d508040c140d00e4110a02a8020400e0082c4000700d01c0c14000f1070f61014642442480c4440c1844440090032081032038590254002140c00c414002c2e040311800c2d06402c07028001079000c04100c5d5094912165009071541240c05580003a8090042406450540c20141038503000f810108000d484c401c0b145404c1e644000700400101e9000524802e0a045c0302c000161001c42600e031480c02e01189a941280000d40c09802c0c15005111035000800d101d402d074401d941655120804100c1c9061000000d410170038111406031040301c0e4403100b0560907026101c0110340380191303181003070981040680400180e46041850200616009012001914200050121480d440001c948a0100500c0340b502540070580300c604004528000700903103e8050015500640c1c8410a40320598030140460014021488040d0442c0d0800031300184031604011000389001c1219000d004c2c0e2030f12802c1c2c0b1400c0e10404080109904003000c0104021180c80d0405604 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 867551043 1250 867549793 867549799
    0x30403060f050c161103030a030b2407260a0305040b0703110406031a0303030a0b3619141005190e0403120e060a2702060c150103140d0c1709 62
    0x49000c5d50700440e1039034201e00d0703051011a13610980b201d5145005555002d207460307504000360415804030700090a0f8011060024220a000c6115011484600c02c0c400c0e441e0391441119134580d23418000040c0980016101038441e0702005020031040d030321034064800084500b1942d90720b020b00c0e00804500400600c03c2c80c0c605000d400c024440380b42e405000640c0034000500b008a4004030010800c80e00140210040880b80340d03500c4010038500c4816540200e4914401010107960f607010700b8840340702806500000c9d040e01c1d04204c10400421f0081850050a960100741c4030281c46009020070380e920b40d0303444805800f450008210518510511070b50161091a20441c8079080704914015103009e4510805030f60425820401c02c24400e00c24070601080c820180070302c0d148081c032104260344028402034010200000ca1b4840d100c0100b10300860b046c40700031100001c9d80d4a0030f00085007030342c200b041025800ba004d181151988100c50212400b41c100100c1e40700c0700c203014003850150740062146a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 867552293 1250 867551043 867551063
    0x1080c01020a021003020904020c0a050f0604050706031128080108011404060b0a05062d090f010f0927060b0a050a0c0609080a0309020a0608161202040e09030403060f050c16 76
    0x58a1b0300c0c1d274005000410025002000c0c000c0e1140740003410152090003c0760b0b142e122204102c00300350002020021241c146c00e00089928401041800324820240b0703070300391032158003a29165900f0010b80141e1a20f40c96907040482d13601c0340c1c0400d0a072039031080d40307007100054000458003003009544070304400038004100b40c8003c0c1d61000400e1040c1c115122841035040e1506c8103921808a100b07a07035030708407505c0050924055030000015025952501d6460402071003011104042c1d0180807070b000603080714405158488054480d451081c541152450324080c00c6c07000c0000c2801f52070303064072440280f513143c0d541484e00d00c3d00308441e01807a040081c0d9446072a96032180c08501e01030014005d90031155804104c0041e18010301021080c1c5502c414100f040c0c4400b04003008031515042001900035140024643e0407034030004020740215005a4007a114500502041110000040046903c40c03101440303850b41c40c02403081154400c40e4080c03074544080141c00c804501d03040e0030f4154540b01c2d0782994 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 867553543 1250 867552293 867552307
    0x706030e07170604050d170103080c1e07050118030305030106050a03060f0b09180403021906200408070605031003030302090d05070915080102040503190f1202060f01080c01020a02100302 82
    0x2d003030580980e001a8858110000b440700744002881012140d40e020304040e5500c81c100b4454640c0d1900c1488050144c2c0c4011540c0040158180701e00c01400320805110b946007003c0a016940300c18040c41000c2c08030307440c04041c403041c0405441c420b044a415841781810350f840c05c2025103550340070300c4901e010142d07140004141c141c961030340a4060103200f03000c261110100c00074080140040490910f020705c1c0281000000b960001c2c1e0078a22842b400742000d0039100a14051015040f50314107a0b4010f00b242c105a841c1c0d07a40080071344100c5d00203608031914966111002e48803031006940380350400d9030018041c00070a02a8004010b45a00505124030502243e16a1410710b0900d40000c1d03141e40d202c8a524401060b010300030809408000000c5181914110009a40303c4041a0390050b8801e140b01c402c040c09004907250501c5500440705602003945080f00a443d60300803208044640310340000400c446a0000300c40d200c500060f0014540c4501507020004a4840c002c0003c1c10503408000d45d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 867554793 1250 867553543 867553559
    0x405070b030c12060f0a03080d151205010c08130f03050d050718080d0c1103010b030706080f0709120201030509010f02041205011a010c0b04020109170604060b120706030e07 76
    0x8501c039000280400fa1501d2104484181c99000503091621900500100e586150388014800088a5024103043e075114201101d0002404140010300b0441300c2801c400503900c40c840e8250007009200e40004c1045042d000400d0306d001e6820781d2241880141c8843d10000540344501c0310404134024200941400507041414098502c12141800041c880c14507400712a024003030382c0c3c000f03440310788003924070903140410041100000d1440030300a81064000340515403800c0d8004d42e000c1e800601502c024903140c94014040e02c10035114420114181c00005410700e201d01251029142072010645180140382c00440103003002401d078800d15503a074221555403551610041005000051004c01c03815000e040150840c0c07040c9008200e0100e882070002d0031381e1ba00a40f000d680c50f0703208580303000380d071241e0004172100201034000d2003848014921041501000041d141d116074400d0406020710f140d19014400c081c2120551000c00d40c2c015031003800801d001c2c0e000140600c044804646103141d440c050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 867556043 1250 867554793 867554797
    0x10f050a0e191a041a011505122a130f0b090d05100c0c0204051b0306150d150e0603010e12160803070f020601060c120309060924200307080405070b 65
    0x8210b500544017a82d2140381011200c90360300402d026020305600740c0700700c94040e2080c490782a184c3c481490783c500103608524440e15400e080003c21300202d14614500c002001950301100e1104048000030038005845c4040135480c0003552903070380600d41401041d0b400c2c403c1401c9448400c9529020b5440080c140c41c180d4491080030301203560b2200d040c1c0003513005000c200c4134007811002400c048603240396803030400f12045a40281080d03801902c041070b106030010752409843c03060100079041c0101e91250500740c00e800000e41d0380e041c0c01c000480c4c0300c00c0101422103042c8003003140c05401010080c00035a6242e40541102d800302c3c0b4054440c02c0c45640c407090107510449048001c250942085440380b5070402c061400b40519040120b90701107240c40700705a10542108120415844920709420400070750800c050b003036401b1121514601101c4000325041040b00c4108402e1868814800d18180318841f0070701043c10b244800700c1c5541c4a030a000c0362240001082a030700c5101d46140000d8540803000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 867557293 1250 867556043 867556051
    0x408092407120e1801060315231801080c010e010c240f0e030a110d0c0b0c0c0303070c0203190f120203070f0c0515030603030a0f0207090e010f050a0e191a 68
    0x5035441c917981001c40c06401c03201d2902c0300311901e500180080c025901c8074601c41303220854110464003901c501d200059950004411f1040c03107402c14800000701400700060180c0e40c00c4090f242e0a103d1071140d001111000d83d0000042c240c0380003845a030340c194100040d80e07203071003074040e101003160180c035151001618a0120001d080c0e330b00c0001c48440595200b0342046000e00800061307c00240d801b60b0040066506000181c44d510384c880104510b05040000c55080c03849030420b1ba0740300c0c035001c10003902e50040824180d0080c001c420003441c00c00d003409960b0040c01d9004c04180d1603600103440c3c0d80021401b280019007940310030050640460000548103160346e1042403545081030a040912005400020728a800c1c01d400f401807043d6a600070007560980d143c90710303001100c003039400c80882c03902e4102c4c1c3c8001c420380e1a2024070b81d00c0c0e0b81c040d04041d03c1185039440c28000798030340c2c2100034100c4890034411803450301322807410316440b4115004c242d030040c00749401703c1c9200509046064444400c1c0c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 867558543 1250 867557293 867557329
    0x1031d0303010e1b0307051305040c050a0215070c0318030516080c01031107020f01090509070f030b063c0301090903020d0c032010050408092407120e 66
    0xc001007091484011036144e021100c04e81c090803814281140281ca800b001c1d007200284017020a00b12206098004480010540100140154282c3e8800982180d00c058180ca0040c06252102410034034409525401806a81c0d02c0320702d0038510761022030f025800d203140038400541d110400404680204110f1600700580120581c011b4a05641c8616088140c0a1507040c10b04007200401003420b0701c1c0560720120340654450040044250040b90b00d00d50031380000b40d0102200e000d0081300799010702e03803141c10304940c3c03001c10102c8600f0040002a001303400e0703020b0034280c07582e1440000b107400801d0a04500260200001004489085c449080d0402d80000e10480d55031010b01e800d055042002601c5903c260900c002020030a8800501070326014902c5000b40c01d51007010000d014007001100c04110b0364810400183c245440c02d041d6903840408500d115145c01d00200079842e9000262403c0027801c1040300f4601003003030380c841809010b001d5000c4140030b520411041241c84080c44034110355558 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 867559793 1250 867558543 867558547
    0x180e1006051e0a060507020d050f010e0106060c0c0306090309170a020f10090e0c0909090304140a230103020c01020c0a0b100b0904020c0c061b12070b060d0201031d03 73
    0x71009200c408404401012164510701c0c11445454607049444001d980142c0380c440d43e18030007800402c07021008810300418521030003a40100041042d40300c911804031340130003440340036078a400468107005199000341464403d4171741080002c1140d03100d0418641309050040b0391554940c542228030010008454080c2c002400000451400c0248403000810807907640640072003018004001200d98011318420b02ca034180840c0c800340c032440075503069200c0107060a01d43d19000c5c00c69502da4006120362401301840c5400d010341450880040e0742556420580825903a900700c0d00301000d4407103000c0003414540d003044910103c18080c0000e0070404c0082c07004100c54141440d00c1c0040c40e20041c008000c5070300c103003410712004508104480404004860242e1145403008442d414050310541032540400002403101c0b02c4c10100d407401c20b0f210090016100111441401a140d61145860040419500c0c00c0001c0d4a46055164248803d00615001803d08000b003902c0a035034000b408071078070b25800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 867561043 1250 867559793 867559799
    0x8150127050114030c090409050705041d010c020304120303270609030206070302030105030d0e1903050706034209150509062407030507020d0b0610110601180e1006 72
    0xc14003203e44900c03582d00140c40c518201e2440c1d45180a4250ba45215940b00c1c40703540f050140c01c002e08405054010020000b402d08007100112811126045000c04d5080004004810307001006840c11948484403140c54407040d0382d0301b14028500c04580b1000b40e908160810200c0001c0c030f0341c0303c85030741c41500c1c0080c940401d0309020703150500c001c1084d070405004000501880e1030210700d001d11000c0c2401e100101c0b005140000d406440540380c5502c004801c56000410f0000004402c01211751584040009181100d402c0341e04a0448203c141910300c1c5000c0881e02624128240703e0052100703424554003a1101c04940c190707103c0c103201124002ca400b101344040c0c13030410100c5070000d8046451488064808100d0311402407038854012204401080c0380342854000e008039403070341364020001d40c403042d503a00d0000710400007070750709a02035000300c41a1010030740581d440405c0344084a0060885a190542151034a2406440e254900c0d4846040058403202048440101340341c80f1808100642 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 867562293 1250 867561043 867561047
    0xf030f0f0a0501080d1101020f0f07120c02060711041407031a1f0302030606040b04030f0b01050603040b0c030a0e0a0609050c1504050f010908100f050c0a081501270501 74
    0x220107000715200320310304401044101400191404d40c01901d040010103030501e070708541d0081c01462074503586100c0000d281822610500020842140300d01c40d148504114490300b19522005064000d400c0b9504114003004514840d40748207090700c00400c0441d01d103801c902d02c95146101540c180c80071940b5510001030300100c054070801000b0017964040c0c804820031860011a9050b4859030081c554000082541034461008076000341c100700c0ca0b4107a03110381d2440e10010503050144290380c011031150004c1960314000c012a03004942010200810f070b201e5185071800b83c2c0c0b01900380c1d00c00c83d9440d0390100e184081844521541030084200040034a003900744a0b007072506690403180b00c1c0d10040071341c0d000054004144d40548074180e07404580303915070000503180300c0e813036030440c14161160709050300003421250442da1078801004000d00c000c0c0c0311000100f2260203500705090110304140d00080038030000350111052030f0f905141c0951031000820610402583d0070384080c114400c4907070107020b070356 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 867563543 1250 867562293 867562321
    0x4020a05010c020d06091a071e0f02030a1206050d140606031207200a03081b07080c010c11090403120e03090f060d0e030c010204060921080705030f030f 67
    0x4803003030030801d0b525103076a40000c5555000000c004d18076540c07108140103000321428058900d54003140883e0050512000117403501043c2803903604040c3d1100741403002c061040c042d4089182a580003181800c403140001d0328241d0820b100d1503000c503550b000c00503180d82c6014010903841d0060344100c552001c030901c1141060001400940a03a001c5142c0034aa580110b04560500b50002d809560ba5000c050041c103022030582d511a03800002e40d0004028000808020f107003561011041100c09002d840c0995202d440030310400c801e80e00101e0000205501405144d580781d8440c01c01e07500f00c403514900080c1000004d560550024075911520300c41d00b200c0303124488090041200031800d012400c80051040701c42c82c03024170700488002c10080310100f050341100d020040d405069030341350324020b0b02c982e000707400034855500000c0324040700050610143d442c1c00f001ca0318000a400f450055a21010000e0780884000c40711844104000c03a5003180c840301442c00f4103540300d402e5215041c898140b40c02d01c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 867564793 1250 867563543 867563549
    0xa0e040e0304030209010308070303020c0111040611161a040902040303020a0b10031509050f0d1d04021201060302160602031609150c03080903120108060f16020309060706180b04020a 80
    0xe5481008180003681d51400283c0c1100e0b400110207070fa0720414031307045019000d0351a407114103600304520030700024469000340040d590196a0100c0c2008289241a41d0315901000c00b01240424202441500d141080f612001b00c891554149000d95441c0038100300e81c0654003d8005800072100e100410190301d5001e1f401c04120400804128250b480781d03614900500d080c0e40c10b00740c0e144e410600304a401d200c7c1c815114401c0b002da450074641c90002030115110003100c1c9400803d183c01c0355110303103402d10a8074249420301d0341243c070f281e00b00382c4150700a41c00021403410b0500e040d11520001009400218451000d81050307110038201c552014001c22a280c01000b83d6000007440c2143c02e90340941c00740e0007144c0610300441c0382e45450380184e09500c1840004d444990303c100010403407100000e4241e0040e0046070036030352182d4542200003244209001c00800680041103604201e180100142120034040c240001d0810a020288480c40f2240c1a0445110044508200079840c000740e00d0001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 867566043 1250 867564793 867564821
    0x10e01150809030d0c030f0518010c03020721051603021515090a050a201b0f150403021f05060a0927060e01240501030612060c11030a0e04 61
    0x7060425030000c9482c1d014000c550120203560f00c8001003414880d03009080c280d10359443c208a2810f11062440f190040348144051946c00c240900314100d201e4030840f050f039500840000c80d000c0c20304050150740800103c0d018100842070001c00fa401c10740700c501820080c4250001c0c0910000303a209501d0fa00c00080c00002c8030869603140c01800e8450b8040d00ea80103200c8a13000826584d640c04190003440f03000300403079a8441c02c0d10702000c0324440d0702c010645000c044040144544130984a1550f403c0c002604035083e40180700403285504070b000302140c100b8402c2c010340350600c0000b030740004050041202c3c80c05403034a075401c0c88054100a88200094019114148621040040d1604000003000c10301040f5110382030a40381030221a0b4007000384d2155504c001d10148005001c483c00820003840c2610390000035880005156009205040484034a104109040c5800d0b446210046c2800010482401544951040d084209200410811217540c6680700c00342c6450051004a480b000300b6202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 867567293 1250 867566043 867566057
    0x40305030f0c0d08060d0b0a150f030203010f050c042102060d1b0807021e07030803010602010203040b0c160807030c0c1509060e03060a1104030f0b04140316021c0b010e0115 76
    0x8043c1c1c841913446c4005c5500301c00d004e1710613120400450000c00c0c010a40c00b10100ca0508082451002c01c3c901e48201c9000310000d01c454120342900c00c04880040e20b007075090b02410041003003005a40c0c81190324103018040c65500e201c4e4281c01003a056400340c54003c51266481c030100c080e4800c441407404851029142486582c031703009001035503d80d801c6440c2e1f846051040452048418100007400c0034550048065407256581c7d00007078040c7d00241c808503018501400061107896140c026507011281f441540715042c441a03c4121503035000c0301080e010030010040072130101d0380000c140c2009101c601100135200901c018020308801880e0050b40401a2000301043c1960300003800640280f9407080000320003818440c4644c60b03205682c40140401000c083c010700340f0142118062046000d8130015912410b0f40d035002d620791042058940c00100c0741c0314004094105203400404407020001c568102c034410f5181d001c800c0409038055200e400d034500050264003202c511045925502d410060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 867568543 1250 867567293 867567301
    0x1050406061b031103040b070c0e090d0f0518030303041203050a0920060418020306180103080328140a0c11060a150f030f0506010506090a03110402040305030f0c0d08 73
    0xa402c1d030611100601040f109004903402044140308030780041c010140711b0f9954820602d081e08002c8010721a100c3e0242e070315400180c0034100420920f0034259542d13100d04540c00081c43c1540c0541026103c004103402d1040700d0444bd45007040110302850041078011209a6050030080c140c400040103042c400b800d0030420000140091083d400c109141e05100185518440105107540500e030302c2090505008180621114450340c025401014245c407403415240c140c56280800300707801e100c002d001d404c1c100001205d9000d98211829001c1000242040c4844c0c0f464107003040d100c0381400301c4451a0f81c081401103400c40e9214128000c02d060400018120301720703d03000d4039090020441c80d01641c682c101d506442900414010281100c213114600494580c00d0040090009410403125881900004559031030030005407220264020140f01c000307400c5d9903a220041c1038681d180c1740c1041d000d12000c030004600b44050800c4a040d0101c4680741d12007046104d10388220300d0403000500c1a113600f88 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 867569793 1250 867568543 867568577
    0x110f0402090f0f06070206070b071103130605071505010f0609090c020d0809010f05040b0906071409010c0201020f060705070c09021e0a0e1908010f0213270906050105040606 76
    0x4a20100b044035030b0561003118002150320f43c4190340340294007a0b40043c03c0c504000d60000c045024420540d40c5098003110031040c2d90780e03482820031207880c8142850040240600c18070007841654842d04503e0078511488000e0310554501781c10150b40c1c405922000e02402e6441402540144102c00c2c0c10304c0b041c02078000280d294503c040074034041108220020300c03ea03109400000340000d03413940c00c02c0326240905000b4103480c011b452a1f43c40d805054007003240f042c840c0040c0261076900b0144d03985410860701c015928040c0d400400c0f4198040c2051080310842d0521200d40318500c691902d558603102490402d1406902e5000102c20b2031041c00b03040c01004000140e16441e0f0a5190b8080d9107202c121010358000c1e050480503a0302c00d040d410440e80c4104070700b000784c044550700d40003402101c3d1007080c4002070380640b0703103541c4a501c1c038000200481943c01c80908540741d07400c01e045070090107c103a00c0301030350a8010240c40568a800040010341083e2086100600c10752404080f800c0ca25545 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 867571043 1250 867569793 867569809
    0x15030123040201030b06070506010902180906091f030c080f150906130606030203010507030e07120831090b01020d080408180105041206060504060509040203030d0f06050d110f040209 80
    0x2019040541c1d40704540ca17a92030710f004440003590400210344484d0707503495200000e540100c1d00307030034001c2108112011505144d19240d01030389000304126803079900d0300c1d14402c130400c141012002d41d80d600c250000104042100c8000902001070141001c813000d00001460810b00e50361074070302d00b03a035a0104954182c0c046000e81e0030008100045050f100c5900301309000c1d140e240c2010354075509c0d2009008405070594462a5411307034090545c0d09c4070740d0f19500b10130030300f041307180180010400700b040801504203504452852824081440c01130400303100201c00002094024540e46540c410102d5800e680410050750b50b464146015101803400c1d5595190601409115005034840c0324201e482036070240040d1400b400b4407490141042c201c0782400d02c0034003240d100d4107004d145005000300e440e0034842081d520442d0094011440c1a4032440581b00502c120820b0b010a950344101c042001e030303607100c585c414650084201031802440e603001c000041c40350400c0031381300c2c0c1d10400c5150816210300d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 867572293 1250 867571043 867571051
    0xc210405190c09360c080313120204020d0510030c0b09010903080c3408030906091e1807080609011505090d0b010e0103050d02030304050703060509030d0515030123 72
    0x8030200720a91300b5010240c0401502034150440c110a031070b4a140710b03901e1301d400d1503501d02404030071120658521701b0507140d200e030300a0a008044040000d0000340c446045903c15944050801403070030034100707401401c60b601600d10750b075044903035030b0100b00348954880014040c20145000f546491221000a0000341e40e900c0700426004011a07c8403118006015a000001c03540110758105142141100b1020040c00132150b07800b20f001e00c0c0814222400011303220440340241125213403880913010011941a011071611541240000a21480c0c55008a04144070021107902c00c46083c109000703400741c1c1009100a02800d60513004101404202c0d8a01400c010701e414040e56a01c0e4000200c3c020740405c81d0f020f0180056140006a08511499894103d901607001c6d24802e91040404036201d10041c0c602070401d80c0605428404038070307039520464000314602d084a10f86040400c0240544404550401e41000140b0f43d5600f9402c0038025401501070910b4025907495100440b1171410801030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 867573543 1250 867572293 867572309
    0x190f110303070e010f11010e031e120a0902120a0503070606051903021210050910060605160605060607020301090308010e1018050a09020613090b010503130b0c210405190c 75
    0x107150581c080c02800c0c1c0d6000109448000d0226079030800e40981c0d25405410884040c0403841c40d083c0c5003126080078bc034844403c41418220766200c102e0f110002e0204001c2c10390380301154200c6840e48400803c1010001d0703125002031910350300641400c800f1540385500440c0600d001100041c84201c69240d050142da5040f90303045904000007180520700049840032440d1036141c002446043c0c8000905010050303050361003400101c4c1c480000b2280e40c0070700d000b120003003c0e5403608000011b100d500115401607000c4c20701d81c10508107400181c01d48982c0007043d404a6103030f00051003040181b004180e0720440ca4407001098a10304074101901002d01025444125500d1001c02c10b80075160f0403030411950014420350321504c0a405002c0c0c290322030310885450b075140602c5210a9401101902d100791040340d000343c0300e42e10303a8a0316040240c0080400444030010440d42c40b2460540c1c0003007800845518488099180914245103080d080c94014040f0500040504001485091018058400c08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 867574793 1250 867573543 867573557
    0x30b061e031e0715050702040606020f0a06020d020708030c12090d0215060d240606030c050f03132004050a1503021207081b031614060f190f110303070e01 68
    0x516055081080503044215019101c981d03010134941e00c907000d440000d000300d40800103255501000d80c0d0f18117540c1d20850480c0c000c0082000030405503409080800b8a0902c09460000349a5980e9002c0d4000c90f01c41400310f5003c103c00c0f140484284c200c9501030303810401044100c0c14080f000e50b95040c00c20484500442200000308942c941801c3d80b80820b40c46480c40c02000c0060b00e10300342c54180d032404800440d1070820009821480b034013503c46078080a0300d5142c504001c405044490364801030070028050025155000081c16440c8510701c038903c15036039401909101c0040200b6075102804d466401d500300440042c00600c1400700f041143d60481d0841190f240c00034a007410002a58404032550061000c4030031101c044a00c4203050040c120180c0b1413640c9502000c41058000b03004058800395540c9000900b400c0840080c0b82d04900032403450700701003103030003c40e5a40c1c524582d4230000503242042114515041003550b00480303d0440658190f280c0024001c1085006546441c100484 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 867576043 1250 867574793 867574843
    0x1103010915030803010603050f1f0e15090a0e070504061809031b0f030e0102190303020d020906040b070302070b070f03080408070818030c0a030507050d050c0307030b061e03 76
    0x540800d5030002c60b40104401d0f00c03503030340340c0307020b4001c285c111044540c9030b04800000e2100078084903a4106070307400c0c51445d07040904080810340c04038070080030035444a10301a915045a50740c4003103240715481003a0302107030714002c08100c00e061001c0b43c0e001900550400009101e1240d039001211010030300d4180000d201d0907207040841d1241c9151130302c14100040070448905100e4a08001280b2034066140c0204411410004907a80d0061110168891034007018003c00030b0f109800404000d03113140405801c0402c42400120650300540c80310402d0314001504000701601031040b080104400346065003003a40c0c5460750040003181d81e00c02801c100e00e00c400201001205070a65110a40118440e070310341c00031002e001032061008050324400d20a118600306507103840c01071001900d5001c00a02052842c0000f407226000b1040790460b2f0030b0184001289094508204540040d409466801000d060110038130020301d14402035041c0209610380e08003820384000035841d0500490891001351020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 867577293 1250 867576043 867576071
    0xd0f050a06111312020409120804020415060210050a0e0f161401050d020c0a0f060b011e0906180504020a051e160f020a030b240901050d030c05150c07060f11030109 72
    0x1707101c000209850144448e11355034a510142c0140704903c00d4408020360f010079030715258061001d201b101d00503070221001c40340b45036481d00210340229183c030002c138962034201c0c002070610460f80351040d2150b00c601c21926402440200810062541c46410541e113a40840000d02500c1068441019650000307510340030b0010400c031410045802c0515629041d80343e245c00809401070034500760004500d044c1800300f44400b1a03510451250030313220f500c0c80c1480d03e201583c4020f424020f40382d125254003400555900d50380000c007000c1c1e41a9450300e0760703124642014162103420b51911011004140086466401025000250980c00c031400b020b00303402a10009480c410180c00041c90504d0781e00034403206c880246001d1001120600304024000030581c01c9c0b007034410003446165030091480b4034000101e401400048802401582030303401c01c0340220828001f00303105841e02412404001041ca0074480c0c80d10400500d505107034400d00c00041c01011010382c600042c064952555a140101d080002d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 867578543 1250 867577293 867577301
    0x9130b0c12011203120b06220506130302030f0f0d141303030203032a0702060f130626070215150406030503030106081e040305090d0f050a061113120204 67
    0x900028000d03110703981c40300119500c8501d02e400031404181c24084921110206014a00e6040b4024100c581070030380001c0d88401b0048107141120480d142d0300008035594031218020248481d04600e03000c0020b1a5105143c0f405000740c0c04100c0c41d410081c108141c8030004900c10300c40c07281a1030072040c4c1460007804100c03a88107564074000071180801d0000308050700400558450004038052522103018a0400c0e0301880c460100144060301c10400c130300061602201500825807400809070030200260b43e10840c40c2226006640030452403000707100540889820741d08075947c90425000281000d410203035985546111400c90090080002541c85d90440010004c9440060042c40415074904042791640c0c420f000e1800003070803000c0041e0150307020746801c4481e400400500720303642d65191000c0b01c07039800600c0c00e25485908240c1d0040800e803252803401c0307694064800b5141c0e4003098901141114004220315500d01d2083c4185000c4500305010b0b14112040350102a9040c44980300140c010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 867579793 1250 867578543 867578557
    0xb0c030a0e0a21030b01020322030f06140105010c031707050c0703111302090a060806040204091d0c0f0f090a0906020f2d030415090507140306010509130b0c 69
    0x9100305141c900901812a080e000c8900d602c0e100c68500180683e001c070b0a4410742c04000e80560300400104541c030039000286140381c1010b032a0206c450751290b442c0708005075901010340d1102c1d19184410030010028040760b00410302400d000010310007554026000400c1c00050007101003000c0c00044003640030704100e50041d1916400d4504a81d22440c1682d1031a0640200d1790086000904100c080f4000f0704c204c4441d580003d110360211458090111091800200002e030015001e020002d2000310758000c151000c40c0d2154856031050408800901d01810280d82c184200700c01031640300710351103c003520101a041a605802d175651803004e03810152a111034001c4c2028400540700450030851805004090488440c00d089803032191400110032000d800741007000300c0c003000420f00044464120558080300b10700d0100c0d00080302c0e101c2c541007103243d900250041c4645085000d0a01d010300c840c9001d400700712a05401420300d40d01190941c9900c5600030001200d000c00700d100c407400c1e0002e403808 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 867581043 1250 867579793 867579821
    0xc030e0d0212031902010b0a06021c05190809100b0a0605070317010e06011404061704031101050a0c030617030702040b180903070c080105090606040f0621050d0801030b0c030a 77
    0x181d5802100c0350840b115000301300200551070550400b40e20320385229568101c13855940100084040d160313001c1150f910780810f400034884201300e51040c0e500780c2d15848040020588603c13980d03180500f0303c81d003000c4080c0424400d4600d060440589583d820340700c2c0781551201d281c0a9166813480c5000da4001d0500170031090f01c4620a000082c1c9080c1e069102c0d8860701d000c1e0b0fa08840c08981e095008503030b0085002c1c00380030400700e201c3c41240c8107103041d41e1a031050007440d02011000e40348060078211541502d8000070961920100c507001c6416004a400922555031001c03800e00e0b2001e05103481c0d010b00d050007441140c549483c050f140c3d4038100185c1410000c0342e08007080e801d00140c0c80c0c1e52541306031022100075044c0c0d0f10000b219181880341d0b521486495010b0120b0342ea41c00100002800104140c0500a590b0200415403c5030b01741080d0010813201150045218541403d600e400300c03110413030040042110041c07000400307101c0c142d90080032500c1c90540305c0e01d0344002c14010300011120294 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 867582293 1250 867581043 867581047
    0x30806031e03030a1116030c0f0219050f0a050f0609060417070608392101030c0f08070b03091908030a0c03060609170f060c0a020d0c030e0d021203 65
    0x1000800c040b00441c05a241d640040000d00c6822588560300d0080801d1188140c1004941c0f0001c00e02401300c4031225441750344020f8503032065a0001d0f910100c0d0b0419010211000c07807041c070050030007171034450b0100011074030000e0f040d03d44000103048082c003a404034000c0001040d802c01c5902c895040e01c02401980541c8147e425038469140d039217500c0ca21a40d00044c1a22010407880c5a0301030340b030710a00701d03013161420008003281d0203007440f020034800704d0550100c100a100500c02624200c0d0f030602002020710803007035145003000d004400035908908002912440d0401c0000d200003940002c484008884035143e503140b00358582000d010029111100d01c240100304200000b150085208a80700441000351000608c4214202d6100e0f0098002040c0300b003009010740341a80241e0503c64602e20122014000410036140c2003250607107000e86d080c1c5000c0b400c2c0d0802a0140400c941a1005182510014800384c800401c03110243c1c52580c001c0300705500d240c0540d216a45003010340188541225 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 867583543 1250 867582293 867582343
    0x60305010e0615010c0b04060209010e120c12060906180a020d0606091802011d0409050114040b0901180f0812040b011a03060306070305090a0b070f1d0d03080603 71
    0x75141c1a080310504000c800c0c0721881e40f560740c020004540c54907089071901c14203940d1503640c44021f40c4040b172020b041c00446240d00c11107654a1507006160601a00035040c400c41680502c030085c11010000300c03540e00710400308524070000285039580005d00c070300340703010003001303891460b0414003c1e10010b904184031f40385101c20311089800c40c10499005003002c12800d11104100b000b0310200e014002d00046c2800c4503a8102204410a0b0200d00001040004d05282590390182112003c804e40d0130b100a4400822040c0070b585507105030301100c0c00000340440784440e030901031241c1400400074007440040a010003445110016501009194400c20480d4103160074404088602440340207124503410f030180f0300c08007004044e0b90041c080580140140e07110f4440990282c00000d0000e07103144196201ba8010403d0503c1c0140560500d8031400f00301400c0300001043c0700710b85c0a2510596844054680e0b103500c540c00888101c0d034040c0f604200035122440040d0601001c10040c030010703c05010382d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 867584793 1250 867583543 867583571
    0xf0408010501060f0f0f08060f09040b09060717130f1506030501060b0c210909040812011401080a090305041206150906051e0a05060d020c06060a0f090f06030501 71
    0x2aa050b243c142e1a203084104044004590312200c8880f1400001e0f040010170419502451203035811950042685494540b00004500740d002c0803581555070310300d041d080c0441041d0a0110b02c0c2c00420ba031400d00110940d640040f01e58202c098449241520b401c91220b00340414a1503488003242d011994a1104056890f8007001d801e0070f0006a40d203520302100015038200d50300440300e9491000000d03005500551807a090071030020718054515450800c900f0301c032955602c0410b0b2145100d2024580c0324280030461510105050300b241c031b00004285405102c40e80c22610241d4445c0e603119000c6617407156890129100d000d154000c104603848803081c18200b2201c1e0b04810544071001104461050b9180d0a05064239030501c503250f000030242d4076041010051b01c1c01c903109454040c14001c2c1c003030340d9407010440c07590054207241c0855070302150360700e00d80400f0300c915600310404481050417a811319141003105000781c030521500300c1d0348a01401c52041c50350003500003150001c008014500a11401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 867586043 1250 867584793 867584801
    0x1b030203010f050d12050904270213060614160206040608010e0603030f0403021c020a0f1a13051309080304080301050301200d0e0a0b130b010905070e04111e04051003180b07050f040801 81
    0x8a10400c100c0710744242114546c401c18040741c3c1154ee4113030303070003848030311002540e400410010840f541044840700503854050060004140d6070b0b0350350040c2d600d05400e801e03400c1800740016100350401c020042200310000140c40549030122400644034074041c48500480459880094002d0503110001030f90040d12821081201c3c000340200794100d052134803560007845807500100000ca000383e02803006040845485c1001400d1400c001580c2c0b020303403035030211500101c5049034070f0100080144200e060a0055404403110030035042d4018241c06446507481c000e03000d694045981e2030104404104c8100f101b142d200350003140c00c0360300781410401d040c0c44c00d03010f89040c1c90300d0040400000300c1d44a0b038031540c0c0c1f040b0382544d00c1c0d684003c02d2100b004054405804400d1403220b080c8940c0c000c0c2e803000c05902c5010182e01b510642d55518040600403038141c85006101810314000702075820400d01c020852106500141056050303441c008207803528024031030302000404001c2000f2500c4101580 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 867587293 1250 867586043 867586121
    0x190219030501150503091537110702030a021c1e0209100614280c05060a230601111209091b120a1b030203010f050d12050904 55
    0x400308840d0601007400d41342c41c40151030540003030348a411072008142d0760102658100f0242031000180139140c910740c0310740b85442c031540f604e480112176000c100c60b0f0310f40c4280304600b143d240b4040d06210442d00040d469001d03065000e8041c0540412599a0090305041100d455602c0340030445000c041c0c00d8090700e010a0000202e00403420040410449044800410308407141035484409100f810505d0b000290400c1c1d08000fa95001e40300e280304a01c2c0f11446c5114490b1a665650880898900b040d034680000913244814071807400205080c440c1451003040310362817042d2120450754850800403140c00748080000031490007003550b1b030749442c3d40f41c0300181080c000440daa6003458a92500c444a02030b080302d1507001f01c060800c1101c200c26a036107006c951014115000268000290b800c0c81903411084412400082e03000005105072001e64980c0e001034081030b1070b460b0380343c8115600c003820801d601082d681880300c0800c094503290340e1904480d40c0400700004c0785103039082418810f15544421720f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 867588543 1250 867587293 867587309
    0x50c0d0e040f020405030604080c070905191103150d0c05180a1b0e09041b06050c0f030306031216080414031b01020d030b010504030b2e030b190219030501 68
    0x440c5800030038555000b52800d840c00100500f00326100d270b0351000e42c01c0e480070302e03c1c07a11800303941e10024400c502031113040d102d00c00150758a84085488850b900846e102c0005108120500348140700322440302d101111882030301503507c0380025041e410010810300c04c40d80507581c040081450f01b91001d0420745070700d01540814000f400394000e00c0d02c00b242c0072aa20050400002c003000c0c0c2003070307046c601161800d40103801000080747c402d006000e10320440c216504800003240001509940403041000380340102900704001d10b046060850029440e440003400441e144900071a038500700c00d00c0030842c04202da510042072070b511603903910900d95400d1507092452090280707100080c05040d071028042c2004170f0503805440c090701c10017020350003041001100c0d17041240901011001131450b25101c0d001c1c980320124044100540315140910b118000051140c0c00307000070b8104002417030030b81c001d504054501d080061a140103c000c0c0700a02680c403907246440200c5a83c804090b070558000d1341611642 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 867589793 1250 867588543 867588551
    0x50a02100f09021f0c0221010518160b0304060c020f032701080720100e1018030c3008060f01050f07080d090f051b12100b01050c0d0e04 60
    0x2581190075132800007080300c4041001026500d0044c0b0f0145401c2c0000303e400c0100d689100444c070000d900b120022140100d113942d420841d420064803c00131880c41014101c0f40c02c0d2000d0411880c1c680c01c4c040540000c03c25030721421800c0d0194000c1c4642d801c42c011034004c694480c4a440040d0102c80c0440015800180341d6101c3c01c2d01c00e512071103034580b14000d181c840d002240074000101d00700d0344070740300383c8201402000341e00c8861b64000c0c01441c420701482d800030450122a0046001110400040980340404003140c00d80040d4102d40344460003034000d40790002c1507024458030000c440c0e01c84031490385c1d00c0e02c2c5210540c5d0503400064140c0202015038140d0b51240201005450620602241c446012028440d04001504007001401c55484845e00801c040c5c4481e528a05600812507040390f0f1600000a07202d4007881080d4100d2103070800b160010035113000c0300744207500e4980420001d035516072980b4100032164041e20881e116681010115031441032011401040c186842d048148960f040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 867591043 1250 867589793 867589819
    0x3020904121701080a111302121b0a021e1507080906010905130807020a05091314010516031523010207080a0308010e04060902060403080403060c0816050a02100f0902 73
    0x491401c54169102c0c00020b0a80c0d28846d01c50001131040f10480c02c1e445a01c420f0301100c81049800584102c500001b8175444500300700c0b01d00c0100003140c1c1b00d42880680700703102480d5411350006044405002d150024511804102c4181741060f680884410403014110300b07105540703501440c55849140c0307030800d0301e850741d8a6841c6107060351001e440b00410707074140c858480b0120b0b00c0d540c028441540300400001110b0740d10004600908412a02000540299000002403090401d0415803030034100000300150301d001d2440d0700790081c07802030329020140c0d1904041c4000c048603d564020f172400018805080211007840e54130240030710320300e030700502072000002003005c0009180307038400da41a281d0240c5a8202112041c05000042c01952615141c1c0041d00140e00d411005102560051124960312821400c0c5107094401c0031802c402085104020400903800302502c0001180c00c40c80c20995800385120121301d0000c9a07448a25440c0c036080c0b0021000d00140c0c000e41c2140c1c800c0d01c2050b41c1c940 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 867592293 1250 867591043 867591077
    0x10e030606090105060f09030a03030225030915030b030a05030406020f030306030a141e0303070801230f040b040e0c0a050a06090e1003050303070801170109050312100302090412 78
    0x1020307200180c0001080340180154a00b0703d0141c0109101c01c1a071605002c100301c0042e1610400c3c42050340840d030300190030f003440302124114400d222803906903040000b880e9a4014119040d502c98802c1076580d201c94046241e209810400d0b039540014201d415603511820b10039201d50151042a000d40320b046c09003507005d0004002c0e00e204207801009000d12401540307039203408481820050010307000b141c81c04110114030014003440900528011601c0c1d184c11b801c043c11040b4107812240110304c0152440c20f4041300b40210381907070b2100b92a00e000140b82000418081c1822440e032030340c41810465800c9015030009003050040500f201ca45802d55919018002d1303101c0075005010005028a805000da07400c0c1400721030704160341024a014803545ca4940e40c0c251340003038038100c000401006c0104089007140f06100340c2c0b899060000c0144000c41d0f659036640e84100401e1003400c803060400514410300d802c028038001d5401500e800240d14140c500340c88892901e09020000c42d0402c982a03e03444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 867593543 1250 867592293 867592303
    0x9010b0a060507120201061e1a030108100b0310090605090c061314060f04030b0a05090f0a0f0c030c0f331809023603060f1003080f09010e03 62
    0x486985400c0c1c40e1403065262413400740d4103100003c0540d900c400300028020815010345145844900110044d0303810b200103903006141d140035400040409000502c00750001043e10681080d40041c00209024410040b90405060080048000e80741031060001d01c80305401640c071641a4506503452681d00408115880c011401c0384031201d1715103038007405407903608115051144401480c0a0030031000d000c01610540c09a04105d4488606000380032001d0080d000e006e4101d65058068400103d80600d41a565007a012029105840310f81010061044096080d80034540001c10b6942d50344d01c9141000c400403140c0701d590140c0c410b503080c1ea00c09419180020314a420f07011000c0d020344038038410881342c154803104408400003a50303c000551441e144004e04206001e6000300b504c810030a5194000442d041c55181074010702030010700c640f03035404a5210340c00440340801001e540c4603408100c0101ea6980c02c010110f041c0040c0e44540b000c9003e02401c1019401d030390b220340ca0982a414503403a4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 867594793 1250 867593543 867593549
    0xb10080f040c0308031905060a05030d0f0e1906020d031a0103050c09040c021f090b010b031b03010305012c120f12010f0e0c0a0e0409020402070602030f09010b0a 71
    0x5041600031840e060040d41145030424003030010365403955201d456440c11076000b9645140034a034182c090408881c41401015030080045523440300b101e141c140402e844800c0f0400542c208403032500d11110080c004c0e40d905c0007581002c3e100401110880717070001c511060500401025100e41008080500c0c0700b40260094924500c80e6400781e5600031700150041d0074017402180c0307a00420300c02a400e684030381c45a444441d07007560007441e02200541301a03050100c511140100e142c200500d00c40400c04400429046480c000202981e1365603000702c6010040e130228a21102010000000007800015080450030041c0d0000068071004c501d035a1001d04412420310304815082801082c00f8100210041e03c520412580507604e0204048019002c4050076001b250003400018400d11426020324055035200c21003c052503d00080040c01605109040d007107248590703203452803c4215156501174a03c801d510842c15500d90800c2202201c001c24100c0c1c00165540c44c000b4004008d182a580030421 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 867596043 1250 867594793 867594797
    0x10320106031b051926040209070f090314030417160914190204090c031b0206042001031b020f0f01020a05040302040b06370801030c0909030e03060c0703030b10 70
    0x70381413201e01c20034888098034502c0c00910581d920808140001404551101c0020a0b01240b09107498810000441c0c0003600720800c00400e20518011250800002c82c242c9030171141c0b405100300040c001914511407508843c440c041d07294980002810300040d101c03c180d89541420312241d0f21401d401007290341c400c100c0c20114154401144143d1010f00c00d4440b0f00d0038240c8013514081d00c40100805841310044000d0000f0740e210200e03d602c5604000142c00c804d00c1c0d202610701410180c0711030a01c02d568058180b58207446060300351142e8000d61200002400503280b08000c1d40300f02c58069120910800115400e02440c036071005080c10603c200c0728a03c0703207070321894141070a6809010041540314010f54000c401000724a0b10200c0c8448009180f500c1c10301f606040c5c1900340e0818840c81d2000c8402801e000c18040180001280c0180c40f40a950408200281003802400e0403200070151070b0489405014202c244084207210500400b07a00d4005d4400344000070304001408901e009118603080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 867597293 1250 867596043 867596047
    0x120c0c0806070c140127030e0d0203030901080a0e060103030e181009090510061e0f05010f0e010e1809070602060115050a020708010515120c010210320106031b05 71
    0x20000344c1a400401c80000b80d4000010810450000382844804441b0005850710070031140000301039000001e0f44161100703643c00d0382c1080103940400e94900070440c0a9052210540004008503541e42c4901d1991100d80215802540d6070f040c083c100c892000c62060141607125850380c0052414100b96015240401030302154502d0b01300c1c04001404d000d4400c885c8ea00a1101200281c0700038000d80d0083c0a04829030030180c41e08941c0d00c1124891035101d0740c8041d282140c200116070700820185050406030805103181c815020040710000d921844031580014000300240c01e924520981c188611f040c41c00b104e103125100c0f2000ea0703650701c09101d1841c102c0c25040000d881c0602c2800641005d0340280101d45540c0c1d1501c07945420b50b201164101c070a0382c40d46e6140103480c40c1800b1b98200b4a1002006840248080d00000b5110015410b04c80040f5848000303080c114074100c000d140360380341a142c4038002070110890807a00402c0038410000003a040c11303041541e0010000303501d60f4041040d1580340c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 867598543 1250 867597293 867597317
    0x3080d0e0115151808100506010f0815040603150506011103040e06100201090c080604050106150c030e061c090605090708100c050906190225140409120c0c080607 71
    0x10911858030f42075a003005580355a545140400055107405000d404010701042c502040f141c500701c5030004c1c0780368108847c07906040780c00780d040302a86801100c0c844940d88054504804074000d052a540002c12260303081040418400c01c580c44140175110907680c118000005071001903690041d801014000010203010460300e2904102110a1304081d000100d00304a40b6200d180703c5070015885407089420810400080140c20b03c1030070083c1400c22021004021b5044005140e407011110090074000d01642c00c0700160745d040113541180000044180038051050b40c8903001c0e110068003102c995080c940842c2d1700300d201048000582d14000e0007001c5004030744412102410766044160140b0070208041040340e00c1d008002d0554550300d1280b003a0a10381424024941a00d50032a40c0d03500f1101e81c11f644402c0030141849084a4400a12540d0468440001002480f075624000c1a0010341520044c150b41c0150380c142e0140c0c0140d0011324207030f5860140c5a2a200102c8011000440741d00b115 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 867599793 1250 867598543 867598559
    0xf050c090103091a040b0411030a03050f1b0105090d0908061e040f0f03210c1d0310050a0b090906010506030f09012003180f19170403080d0e0115 64
    0x100030528004e03500b9815903110402e614a030380c00d041d101611101d02420801007032003040800442d03566016001881c0100803902d0061041c064444503100e06a00025049a9a10744a508920b4541444001c01240c00c0c402882c6985007002180c172800b16602200010303c0641c0482c89a2140450041c10b49141001c0e410689051400a00440b00741031145d01d5000400d2441041c40403e9110381c5961904001c2050610206008644062205410088860941580500103000c0c01860a61051741c0b08100c6002a040035800c44521501619100401102e5011074001343c1700040b00381c50218182c1c59002203191250f10034050a074100c07000b0000f281c1c040ca455032056910440c4500001110480c030700c5002c02411448440384400e040100c00c0c000d03000314041102c01040011070050109112080100f03485e84403100020001d10300d10000c3d641446481d44a907541410325100032681e69850b490300a030300d0b810640d01180d0072481c24000808400b0144111014100140d20040301e0701d1819401c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 867601043 1250 867599793 867599801
    0x609010204141827060f0402010e04180809030a170a03060e0709060c08160b07030617060112081308100605060301210c0b070305120c16120e1002010b040f050c090103 73
    0x2110200c10901c0c0010982c01343c0c2440302d107025446c1d981c015030301b03420180001082e4540101204e4405c901c0c1104410f100e840800803094041d61050001d82c6800340c0e080020f0074038540c031401909401052000000c001c1100300148840000f5850410845845100d021050803089446601050944009110107070051a00441d054030030009546003043c42e5501000e840800701c81221200c400320309006409405008420260035100c0c0204d100d0300d464082982e032843d040c0320300e50708100407802100138805100100c0d03003001840003a58880c04d6441003242c1e038400000581c0d010b124580107000c82d171403512100b240c1c12520100c0d10f19550901f60344031407085420007035040b00d140000c070200050152905001d061078034020f0b220607442d40c0c909450b80c00b40c10002400868100c1040004401000c0380c900c5c04002242c011a207a01c5034010040700380e0b440280c9507022075000405c10100d41c101e603815007080381d10b420140d50500181480145240546205443d0155100020f0107084215403280e80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 867602293 1250 867601043 867601081
    0x30406020412080723071e09050106050403121b06330905060d031b0501110d06090c080702030a031109150a0908060c04170c0306090102041418 63
    0x1000514056803031010500c2110412403c82c0c1c650401300d80c00e81406500703070800480c15101c200000441c40c540d510940c4800003402045415004488401460b64400c0c000c44c0151405103401c20142d616030b5405041a00103100031941c0103202e84210520510540d081004146450300601e9103200688d41c410180600040c202e50560300b1249540d50040610711141306100c21000b00e80080d0b0420031000700f5120300405040c01000c1d03519031100041d038031800c2007040415543da0307000d44800b24038240d800340841c50442d040120000c0744d4003141141941c0898110b500402e8100b0540303100c004181e582d40c00444008025800506c010707e480c0b4041e801a406492200807403a180201311000980e10b102d07020011113550307a01140210261741c1080103400a4031510001f4400c2c2d29048142001c02e120345e025016580e0b440c00030b114400038007040400d1800c000103054541c41e10708400c1890003034102d84682111500d11401168041c240380940c5580c5410100d003150302c503621035a4240b156802c5034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 867603543 1250 867602293 867602303
    0x48171c0207030e12101e0b0d0809062805090906030f25092909040f0f021f020604110a1d1008120415080c03040201120b03031206030d02060c0f0304 65
    0xd00d120440c00c903c108070f06c0407a1040c201e1041080c20314050120b0384481302c0d440c00b4070f150044070404079200c1d50a590000c2c6040344c1c0e03140c5e944011007003243c5196881e1080c00c6070b80803004002d220300c2e41040282c950382200791901c0c3c40c1a80c5c0d00c0c04159450041628128564001c00910012100800004036040e502150250081595202c0150031599462603103010b21a6894080c440903c81c680610f0b0340b5481290090700c00d090982340c001002840000003018000c07488110011501d40709038406a00745009101c800c281c03520400a07454010880301180d0007200e400080001e4601080364800303030f680200740c112109018694070003148802600113401040e8450000407106d10070881c40c86181849280183c46034941100d580710740768101001401e12110408000030b80b000324040d0307940541c091030113015200003054124024182c5000c05030300743c00700082e00404031030314518642c00f4110a42c110751207481180000c81e240c0105a030140146e903820003400c0718114081d03000c4c603042030086e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 867604793 1250 867603543 867603553
    0x50f10030209030d09050301060806071407031806080a0c02010c0c03050912120d060503010207030e010302070201270e060613031709091648171c0207030e12 69
    0xb12000030310b0010000c0306400081c40c803100c00d10841c10203002d03800c0140b440070300920481c203248101500c550368040e100e1700c8030b000204030300007132600c5a80850306407900c40880e1661581c50708c1e00140540800c0780d040d0b1000c0d0034038582042142c8148208981c0e0304480e564520720055541d01120150701007003000341d100b45650b10008140c5000e109450407150391903891903031203440c1c0c0640380139555954440343c030030391050010f800840d401081a030107120b000d10300180c0d00c0e600c910050340c03802454602c0042c54240040c411101030074004040054405c3d01e0301e1924160344490802900c0e204510180046850306c000810009000f24403c0000140e03090202d4200f000300c4000c076841035002c0781c100712420008050303803c3d05c58100010150111041203000c42105030300c0c2c09412000d150714000045040700d224121100300c0b900c1c0d221070480c1d900c1105410340080c2e01000350344503000170310b00110325007922003000e100721114800c0f54451a070507102c20403082c40180401500c9045c0d60b00075011030044e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 867606043 1250 867604793 867604807
    0xe06101107230a240801050303070b1e0a0b1302130512030d0905160b0702010206150d1b090b060424170a0e0d03061d070c08131e050f100302 62
    0x15802c03a07440a00034039641c8156000604204441d0540041c0b113080c244590080188025100802201c68140d08418854140c1c1c80352442860504596145a0b0031800c2d1a42480310000e01031308030390f0302240c3c00c807026522840000c00d020200e01c55112a039078094061081000603041032400000c810200005890406184111060070303240f55500465645d003142075052400c41c0c0d00e2000a016045e00e800403030a0204a90000c1d64031000545500403076200c180a8400315580c0c1d45a0106140d4041c07510214403516803040300079000eaa009098030f141c10034050884030300344401501c085031200c0d00c00f500422a40094a02150f1009046604004210000000108400c002280070365040d9000141050044041078104402041c0c00410141130500422200b101c4c10741c041c21004012100d800d2684a1076025200c603150610000c1038a13038007003488028004107400880444249a0340c501c50802d0300700b0095851800c0b409125402040740c14920428103080320100381c2203289040c01450101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 867607293 1250 867606043 867606049
    0x8010b09011b03050c070b1c110306010e0f1201140f13030c0501020708030108031207030b0a1e030f030207231f09090f0603050c0a0303140c010f02040e0610110723 72
    0x160f1f0b00824004900004c400c0401c0743e036403910364403820144a040050f0321501c20030404600c0003a104504001c40d841012140750b4654601303456000c1c0c02401d01703100e43d4980c101e107400f07804884412100300e4581d900243c001b8418a118611a240390300701e80302d905e1842c0d0340c150b40350101c1c5c0c2c0040d00c0d02d40d030074410480002c085174011400b0b440303050000c58541f26401e14603040c28500410340c0d03082600b4003041074400c1d00c90a07142000e5440400d42e00c200980d041d42c02d050108000d07840a8200b0030742c0c07003400c1c040c035402143c50019180f076a4142600040c48803815500400065452a007151190705025180c100118080d034080159107414180140e54103400d5060302d508800052000e0f0380c0ea0000c1040080c100651071160800b510b03601c0000d4550b840c0601031844900d4400346512000440301408a8294000ca9440c1c0f0340070821525a80c48010841e1041c00484402d0f004050480b19440410700801756a0890404a0300034044030382080f141b50302d0410021000000c00d030350b81009044070360b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 867608543 1250 867607293 867607303
    0x303111002070f0213060b19021c09030c170618010b0d060b040b0f061204030516060b12010e070b0d1d0102130f14010f0512090a020108010b09011b03050c 68
    0x141c041d60b55001d6411844c01005540e0f8180c11120a2051820000b0025803941c0e8082d21401c031400c0d84040340c2103901d24000d81c10002c41d4941e01082ca100c40117120203207038100d0884401e49011720300609060303072181204582c180400c0204603c88c0c1c007e50000324030443d401070000f4036001c1c8c00700214072440c2d00000310384049040303081103c555840d0301800c0420304207889441d00e02001141d01b860010100d101042d42032040c43c9500900c01040000a000c0c14096021100c0881c2c804404640d20351700303802d008002706000304911717120701101030341035010740c03814010800000006806464118502100c5503103030350080c00c41008080e119401c8612200309810142149030407140096540c5040440d90703901051f5507040107000b021003240600c00161207030801c0444003820308040c07424110720b02060712a400303504003804002c5104020000146004995210349a10070380755107a03582d8030b400c507000c003900410001074002031010440140003c043c2c80e44040c0d103030080c20243c1c42e003030060712164100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 867609793 1250 867608543 867608557
    0x411091b18030f0f0d090f17150c03070e0906011d120304031b0f0e190b090405030d0b060c0a0f0204020d060e1501080106050403080d06090e0f06090106030308010303111002 76
    0x16081407250121004051084074010170141c0382c54405242401403da414001c030b400703980402e00aa150841103403204200001180034206050040c030b2a2911080d00558021180c00d4002060350101002504010710201e0043e28140c5a48002c00c140c00e040d110800c3c45a00b4495010034201c400d81402031051004001850080050b00c100341c80ea4082402c5041d22540264102401704070100082256414480d0708021003241443d1070145810420307016002c0b00003016403018607030b01401f08001c0004010300c54100d0036101884064082820800305020313a040400d960f801030180003002810300c000054115100504c014101381c0c252503c0c8046415030f4000f42c4242c0c5a507818080310744a4007081d41101c50b0246010600f66040c100c00074494001c503c03000f0182040840d8202010023650011005410b8454041062409407108130ba6103c003d44000c603568040c40c1d0203d07006d02d406016203010b0f00d4061b15003d10316440c680e41100d2442004112198900415a400031464003e00007002e10f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 867611043 1250 867609793 867609823
    0x203190f021e04060f321c0603260c06040c170601081e011b03151d0f07180e01150f08011a0c0a08030411091b1803 51
    0x210103040c40341040c032030064210403182d4030b42400704001039076000301c410003001c500d4034180030b5090030702c01c1e89840380e018045088029040808610703c00320000c3c1c0078082c52110030702025451804d080c0c81004031549400040c1c03200781502c09184441030041389c8804100610b810061a200146603014104002601c08488001d85038604120000c494800d00307007203101d06405030065501d030115a41c1d503009581148903280540800f1a1642c030803e600010001c0359000d0741d611590006440203009042220b820304400a249402188100c0420050b0006038443d48000d101519254908181410010203510400014540342d43d41103540080507401040c100650441b00e5051501784030810701c45103803400805c42e901500d10b141c60b90100e4600c1c111a4265480348102400c50720000c258410000180502d10400840c0700401039802d00551045020304890b19000c5107141c2046a0310009440b10510400207851070519404610b004000d01502c22222041213034500700802d091088404a50720 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 867612293 1250 867611043 867611047
    0x204020f040306050105030625170405010507020d0c02030a0b15030706020a05060c0a170a021b07050f0d0201121a090c07022b14070803030115020f06060904060203190f02 75
    0xf000a1405602e0150a0850141c64039103000c605203c201d440d0301903411011420750404030400e50044050820b400108040d0b10824542420071602800302910504014814149080e03980c5200d40980c1d05025401400307000318a1b110340f59045154000741c0394104d08003d10310018001d40c2c0411800780145500e401a107040081c508190f0305141e002800b0050048041003804c3d4125440203038a20300303d40c1c1c201600e00988030180e4580003401101d42195801010310341c1070a444400150010498404031a2b030148040c9001c00c0c400c80003e4150002d000c264582518807041481c0d410062903072680da050b440d0f441d0845030000305820415104060801c8000683d0b00550510410103000418149035030104da02080004c40d00036507076900f028010801c24241410383c41414000e07000107000100440b80c495031240044e82c00079000009201c0507200e590900c44179074401150b018801c9000408905541c2d5803602c80030040e501c02000b0030301511203032504280d02d6005114090038440c019100503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 867613543 1250 867612293 867612299
    0x20c0f0f12041203050703030f0608011e020a020303071d090c07110f060414040e0601060509100f02031605030d11090a05040603020f040e0f07031a01090203240604030204020f04 78
    0xd030811186201074044030604110920480c850350700020341c0c080e0b0601d03080340d5800c00384c01c0840c014940341003543c001d00d080607000908820150403580304004c0b2480e5039201d02c14240001c0f0101e1040d00c0c01500036800c107100090b20740e4040c02030040390010105a88400e40543c00000e071203000c04454000400e0030109025060004500c3c03182c80020040d284450300241000c0080c00c140501e100d460040c581744141126a5100c60700311318115144481240c0c15941c640e1070140043d04841d40c454004c801d02e0f09404040d40c07150300d04200100075a0040c5251907480d2181000752012003405480c9031004125515000c5010310605540304d8040110584403542c0004000076004c032640304502c03c0e400d008050001d030355508003441e00d03840308030740018420701d58544640c01c2000400440c4260f0181c210004144030262030040703506154136070900801d030380703a2211004034042603496030541c2e00d150310780e060a015000207030490746a00400c2141456039036400107080e0790040081003450b01d400302e010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 867614793 1250 867613543 867613573
    0x11010e0d03060b07030804060f021c021222080d06170a0201110109152a0c1a07171506070503070203010e030f12100905161709071404020c0f 62
    0xc00b014159590080d4940031030794900524000f4041d00103094507550700c82004030441b442e41220003102c914080101e0072074081240200075040035014000c5010502d000030b1421505900d40841c07091f002a00300104d140503140c0b070040e604241741d803221042c0d51765404122801035200048109460304000c11580000e8800102030200607100210030707038102a03000740091002410200323400c11003403000a00d604003914904985103403a04a10b00c0c0510000d207a001c1550002403000454021405201400b000281c11458074030115500c40c0001c2800424000a0a004818030f8000c00742103505600b2680800c0065091b502a030700840d4140e000085001c11800c00780543c840c0d496138480550f0500681c50303500c004a10591950340b0a0381c1d01d4070005010601e040c007040d40039142282c000c02c130310715085100e1011280342030500c40c0401d402c10303448090303120003000c200e20440102c800703840740310b16004c40610781380c101c4400a503010340c09004040c6071040070072103880055032203001002c0c141010052 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 867616043 1250 867614793 867614801
    0x405010515010f0e040218091003030306150f030b010c140f121222050d120b03010b01120f0605030604061d030306060a0c1104050103391511010e0d03 66
    0x25060500a51903a243c40264201e845945000400c0e10050307543c0480d11501c0d00c0c000c0b43c0841035a4031050031070a1000e500c15110f440d005030b07440f03501c0c1001143d4440c80080140c2e25800c2842c40058020001001542e120b81c106541686060611508118841d5074448801c0424020014554401e6200d030404007010400004003c07900d48030285810505072032171008640080000c808540140340345140c0d80800e24a9600040e042010380350ba0700b8191900500650440f201c9031103007420161651000d103011300c00c0190f5040c050f1118240251100d1800c0050100900c2000c4c1c5543d841c2c0740003d46031003d200c11842544626000241143c40740a2030a013241000c0403441158010f00400416843c0c0608849020541d800d05d1004244507250441a640e8555040b60f017080c2482300001c10868000e80a034001c82e400c0d0600c10a80390004902d20680c404515074141c45411044100124480700c004004089210311701038551200d82d264103030950340040c1100505900c000c503450241981446 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 867617293 1250 867616043 867616081
    0x20325093c2403140f1305010507021c03050603100b06040305010515120a050a02060d06151724130603050a0f02010914030d03110405040e1014091f1404050105 70
    0xa0800c0411411511407aa10f18010b080085d03800d100c5c00880d0460184000d0760070300e164014003d001c0d0b4503111030001e494581800d06540811b6030b0801c01820540603001c2c403481058090b004080f0850640c02090107048101101c43d0000c108100c08408101c003802030902c201c60311812001c200d080c01090214500505039003581541100c0620f50020750b009c19003226507a012610192600c03881c02081d0001d080d154003008881114070030300703080076802801021500d40c81d40454201d41d035501c01a43c501c070020b41e1a110070010940d034488410310b4a03440b20110340882480c00507625880f982c3e05894803c0d0134074240c500510b03040c01c480071580c0c07125020014022003080e0300e024405090110383d9402010b4900c405064481203913030544406181503034010100248103202c50011480da031910b41c10402c4000305072500f0300c1c008111100002c2000c501409681004080c02800e41c0c1e044060700d41c00300b44408002e5218070480c00c904000c07a003042d000307901079000060503003010244000f009007618 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 867618543 1250 867617293 867617297
    0xa0f030b0603010b030a0305030702030d140f0f0118090809042c071d090a0c12110a08030f13050a030c0509070e03060a0e0c04020325093c24 62
    0xf641d04c000b94801240004420740e00d405d105450f82c854170000d83c00d502a0002d414403e902c1c0003907940d240002681e0560080511140100145c1c03290010303036604450901910740a031f0b406414079842c0840c143c3c050030500c1e01921045081031807441c000b50030b0710705080158001c00c000a04800307c1e0145c1c412002008501c070402485110b141075004030072203100d18a40310800c40c2020010b002d4403410b00c090030500e13038450310064016860b00007400740300203000015205108008413090050030182d8510050381d0144000b9410302036205180d0025038031805400c82440c1d41c03400d0010390f0b03844500d0a03001651046041d107840320700b4030040c0001c0c1000103080f8400c110a1944941841c5c9000c00e100c0d402c00c581900c04298800030035401c2d0300e4180b80c0203c46410030310000800c880082801c0400883c41c4150004d1100c090a50008441c24030700ca000c1c800c141281000c080c13281c1c40c0d00c3c80c29894150342e080002207540c10300c0291860211801c0d800032444400300385040f2505458044d01c03a60740c0c5024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 867619793 1250 867618543 867618551
    0x11a1c0b010806100e06181906080d031a091f090e030a14090a050f040b12011d150a020313060c0207060f090b07060c05070f03020a120302030702061308090a0f030b060301 75
    0x7800107000604040020041c80440310082404008603100000040d008d283c01405401c3da00c5002a85e6022140e4509000a18144c02c0602c80c0841414420b144100100400100d464003000014994003049140611000c0742100060545072800790742d50254a60001e0760f00c03142070b080050905189601100c03420340c001c000d20a041c1e03a800c0900d0b81a110156501801e00681703001040003015201c040541c01058070400041c611015000000107425401101c6624480b1592030359032468802d40c0c150010050320005000c04805501455000d80506021449582c00b501d400741103400e42c0c408807006800130801804500e40101d044440306200f071a0115a00e45407400c200c00c680560040281440d4541c002c5005041c86182541c2c480c0341c03c60701610b010181032030301035615031281d082245c54503c0b079082600c0d018040e2095034400c41841e000307403240c0d0755265075011101c00512022542d0300014461255240c0341c81080c00d010f4044000140b195508500b8002d10004000f8401c030b2080e818 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 867621043 1250 867619793 867619801
    0x2180f1b0a030e071e0f06090b070b1512060a06150905241b010501140a060807111c080105030c030304031b0510031a0102011a1c0b010806100e 63
    0x140c44100e440c490180e00d00000c820b80740007401400c00780c443c0d20040d000d4282091003940c00b64000b500c0d0080b583d0b83c8888000703442d0b560905460b103000500c80c801808005210302b40108003103000596101c141d41c00c003040c032041d440d4000745445e45030b120034403040c2e4808000c20000580e50710851000d051100d40d00700078901d050800078411031003800303202d0158642c06131100c0811101c105001d4012055102e843e181c2c010b11000300124803200c528080f5945c01c220000401c0c600311000b01c0341484020700305a180e1030620a050380c0b020f2028201904010700c4000c00c14148105125903100c12900a201090824420300014200341041e00100d100340c01c403c0d40d05400c0d94001084604a981c80941e640c8160350409910305680315035840329401121540030040c8240e40f541c4800c1c16803258684445a904c032402c012400c03203220b40e00004401c10001004105450300da01641c02c4804200f030781038242000355581d002190420f901c03411044d40410180144104003610503401b602540c040e003043d504d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 867622293 1250 867621043 867621091
    0x2c150102060f041203020a1b030302090310020a0c08250803060414160806130e0703060f05060d02010e0409212606010305101502100e011103060f030a02180f 69
    0x605a00c400c418954009422101f050140300b040740091400565803d241c00903045c0a4082e41c806c007544c0c0e100c0c1c060491085004480351003907409036001070313644c1700540300b0700d0303031f039800143d0100aa1301c3e0030141e0b902440100c4044e05400726142442406400e44a040000070700003a102605107208500c01c03154100804408072b11140c001e811303018500718200e038035680007086005104407038484496080881d4001c0510001810b101180d1040500300600c05100000b442254410ba4880b0b6002142c403007880b01562048079004000305004000140d003a88940d0390f101191076640415441c1c0d6416455a049150000b032059503100040608180100b018803400448641c02400a81859507940c0440d14610807006410040c004180e0004403140740d4410181d42d03009003406000c1400c3c208418004070135018000c08410b040a501d0321070458861600304444e4020741c4403415054070400e0090400f60380c1d40508904e00c0d40c0c0102c4140f82c1070901c1c02c0e100b441c0b103c0040401809011100f1402c0e0020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 867623543 1250 867622293 867622313
    0xf06020705030606270403050c0c0a050d0605090c131a030d05160809210c0f0f040f0e030f030711010504020922050601090b1e09012c150102060f04 65
    0x100225003800c2040710036140c1c0091340103031305c03014030103885030b0300030082016000750060400011140c11256009510400c0001e1400e40d4017900d40c102102e960144002003160b00201c1d0014645416180c1090030300012034002c2d070309040b5022143d0b4641050041003040c03810035129042041d4082c00e60305403842000b403d54441c1401d11040d01008ae8a04000c0c401c0b01011307100d0750400204034030b400f100604180b07280d540c11000801c25601072031240101501e02502c1542041c40041d000010600d00442003100406d13801001c4550f05465901c0d0550040040c001040200a030222203900c81c1800c1d9801400340040744140389280c1c3c5000700703000c096501c050920360700031400d64090300b0709102c0d4805000f1808940710018024410500003180458142c1c02004035074400b42e41c40c07007030b1104806d188202000b081c20010b4008041c44010700080700030404201e240100440b00c4841c00c3c114890075440410211100080401c000c6076070b000c690781c14071006400460203000014181082d8031703040c0c295 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 867624793 1250 867623543 867623551
    0x1110d1a01080117120a08060405060a0303140c10110408060a0e1e0c03060103061e02040f090902061215090901020a0e0f010903140a0215310e040c0f060207050306 72
    0x440300c2c13041001040800f0400d110070342404081c1c0a44594045501500601d001c0e5005841503040000046150401da80080c0c1100e40540d64240c0c0c3c490b03090744001407980000b10a10340c0d4020808441640b2000303010700c1d118240b2180703159540b81d1030005510304004019010003099424513130f064003410800100a4141140c4440c8031502c60980c0c100c4604d04510328007440d405015610002060042c103a003e403400e035500ba440407001a00301603403107040b8461401030701321107004010284241328055201da04010b00c00b0740b07030a24118104001841e1130804440303414030300480c400044124109a11a1500a0f81c110002d5050451046000d8808034844542d5806403d0111103410541c0c454104500119000864104280e0201d16070584800c8080c009a02038040e62084440780b04194088824810520b13982451004404111020040300e1840c84000c0c0c07125401c005c41d6800c0803041c0b03203000c0d510481c038800e1202e20b0005550360090640c0e00002c159004842d0400c51500c0c081007003540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 867625899 1106 867624793 867624809
    0x312060d02190f141f0c051c1b022206330804051902010309080c0c0a0801050c07080904061d15090c07081b01110d1a010801 55
    0x2000132034000349030b0490302c1d01a00780d04d8115504c0000c420000c2c10700d40410380189603203415103000001da000d03200303800d98008400c0e00384d03403c44803c50b5196030320080d540b02c0205035000111441b06c000f00304a155002680d51110024103503128101811800d201b00554480496a9001900080e19180320040c0240440c1c800140221038980c440d60b4000c0040070200d0712250024240d40d54010100d040c1764850450500140407207000d000c81a214400424002ca40071042100900720f83d88449100d91401c014840705000d080c04880710310740c02c089507030340d200000d0001c10000c0880e940600210703441001c110000c0b00c64110158040da403048840340c80d0200a00c03c00158035415107844402078010040580082c0511020f002c1c164900084640304d80400c003030705400c0d55000d0098001750b103800245581d00b4130040c454004905002c0c40040042e201d0340c000a05104418002c05003 = true := by decide +kernel

theorem cover : BRFrame.Cov 867446043 867625899 := by
  have h0 := BRFrame.cov_init 867446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 867446043 ≤ n) (h2 : n < 867625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
