-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4329
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:16:05.297979+00:00
-- url     : https://prove2.me/submissions/46a18113-b47c-4869-ab80-b67b04659d74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 778417266 ≤ n < 778597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 778418516 1250 778417266 778417271
    0xe030318010806040f0c0e0910050f0607030c08040e06090c031e07020111042606040f1b0f0909060509030a020c010e030c0d080409050c090604140a08031b060a 70
    0x15403020020030034124400c1030402210340041840c60342d0f10741011416490107401084a055181d0001d4a003d5050100c07502480040b000641c1015200b44440c4c12907201a00143c2c44500d0b080c200000c0d64483d40f800c50a2003807807600180803a0f0a1405000644411901c0d100c40d0705200041018124000f8444404905d0402c1000b48084030180c0140084484005020b4140c6130400180c0c05030421001740e400300d03040843d002400a0b13403844860b80b034030f040700502105640f01c480c65641301d8804032405003030003841e01018400250340e440c0d141d80d81042e01194512168640404a950103541e5000c480150384480300c04051201a1107110780244604c4021840c101288102030b45800c1c00c68100c6042c05003604880d13250362030521800d00400c030000e0030348039098458a0040f0701c40e0002e0045140d0903103000d0003d09841185011105403031402015079003420300e0b100b00320f040442550802908106082800a020001000a0301e1041403d48030031a0809900c43d500703141c80c0c0e0090031003400c0360 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 778419766 1250 778418516 778418527
    0x70503122e060e130b03030c0a02010314060f13020d0513051506011b06090209040506040b10030b0c031302040c02010e2509020304020d050303090d081e010b0d0b130b010e0303 77
    0x30b401c0100424916015980304d001404520000401808103a4031903070140000103000b41a039401140c001002c5100f624100058504040c009115040403034105410510400c99001146070800d04c0400c1c1c1c01d81c0440140c07401030303410388031002e03280300b44c0e1484000e05c04808418108030060080302c0c030007412401079145034542000001d1440421841e01c1c4051480d0540781014800c0940090003107640190500515003420b1801940d20f100c02c0318145c0d41c8040c62030225010740e000c80091407c0b80d401540740e03070700c0fa240c100c040f004942c400741c84a000d0a0a6980c4900141c48034040c49003203017071580002401c000241480c50500c50100c0ca11380c200646104000709030380c07000403254265517000c480140c80c0d6036584003068a1124075040500300344000300400080c5440087c42b8200c41718296183d0702c69484846c480030300300c8001000d074180640540010f00c00020990041c060b07015400030003041080341c0c080030515031840440040030154540c0c828039a0707560048100b51001200750011031510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 778421016 1250 778419766 778419779
    0x1030b091b01030e010608030f091002060f0f061c1a0703061211151305010f083d03051e0c1318060c030903020c010801050114070503122e 61
    0x6004801c41203061503039508100300030342d10941c024400b40207004226907aa5500800c048000d03000229400e10502d8941001030b2806e1011031414000c0742691284080c41e00e4041c6819100c0070020405a0804170b1030100d801d40caa0754410004145001360a0715194140d260b003103e0540c01c004040c0024141445020054160421840c081031030b0000a43d00a4008090003d4405021021041c5000c2004142041e0b0030146e071044108490302600c4011450501010949690800702d4090702908141011411b840c500c460030303203035203c45101d000b110b001c2c10303900328080400c1300340c00a90340c0768020508428411594880803040402c80d4005210001d4a403000410201913800c6541284ea2542c5100030014003424032811721590100007841017030300094004004000c83c4100b074006104940200000c0d5001b400a503041e580b0680d100044207039204001e0281d80e01a0f03000f184c042c4001c00c01d0400c80d03041101028001c02604c034507a60780140320301c040d080c00455002050340e103c150f1701c01000003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 778422266 1250 778421016 778421053
    0x6091003050609240108040606050a150f0206240a080d03090605061818010207080a0509010315140105070227040b0a0203070e0907020c09010e061306030b0a020c030714030301030b09 80
    0x440003d11b07040442d90354629021010b00155480340e90011032807180850004020301002c0c0c0885020340e241d901c108500d89049942d800e007038030b003000058880c0700e02003042e001820310305c0d81030034000e400038000b25510380c0898a00022540000000380e0303203103960401c00c035036400383c55000366007100c00c0820783c20640b07000c40400c100030b00054106007807d104509000780039015201c006420180154a035a6410800f420320ba00c9811003a000902d041241680005940e882e50300307558540850761040b8107034800548103540040c105030781c4440d5144013040016a102c404042c00a030300303d103078034640c10149404820000b014103503402250060040103c90742c0d2060447e5407071381d400c5503404c0c0c06840b1840c0580c03c11002a420710b40001c0c0c0d0074008544c515404459901804051b2a80c0c0500c1446102080441d462400010002c0482c2c50110380b0345070a50b0042d00010060200303882c80c050441c1d407070900702c00a0034150039250304040010001e111500f043c1c20b50104559015201e204c0d07007903000410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 778423516 1250 778422266 778422331
    0xc0705040902060a182411030a0c06020f0d05011401140c06070c02010e030609011a0d020d020d02300c0f0319051606120f021201031106091003050609 66
    0x40040e44400e0b032160304c407170702c210360700414203256198a01c0845400802018580c8960140882ea10000507407800d50000102c3e4418a516920f00121510b16614500a03500801e041c4d0403014081c815207400f01810300c5034500030308010112a80383c002d480d00142607500441e01c010702e4903500f4440007840044c0400c00300c1d8008964980000030800c07500c0140c450381d0058a030799030103220344c43c108100c0500540c00300701c000215003002046a8001002c0040305004a030000350442d5101580f40c006081c01c40c0c08001051005001c805141102002d00107401e820355642d0001a07402700a04105403010300c054588044155841558888542c001c01e0ba160b00320280040c0b4440c101c1c40700d02c02d1110600c42d80300345040f281044001a0350325040140603840d21200814803501e4440103240b100224800c41e1a0458440300156541c1c0c03071900c4e1030165030400b52802e604024104252505940c80c0f492049985e80a510000340508001050100301c00c001020611034810a9040310494403816030880c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 778424766 1250 778423516 778423537
    0xf140109050a0f020a0e03012703030e0a0515040308010603111914041409130506071404050904032a05032a0a0305090111030913111204080c070504090206 68
    0x700d036203950500c280104104a19003842c18404209801003545c440811030070074030304400a0185154100340c001c0000042c070b0b558003810f40f44080c03000029002743c0002c500d2543e03030030507030381c54001d580c5605003007070350952584a80c040c000007080101604000c5d01409401140f03400c014080c200004080c0603c00c8544800d0040807413070303000b20030034460a403000140c8804100c0640f40c650f24500700e003001d02c5c18601d00d485143d8400001d9518505912026142c5401a00030081a1500b520941b00b010440c0c0c02401113210800c00030400743c56500c0b40e50f004c0c61280e40c488010051000354981c0304041c040c071429000d007004840c00003040c0c00005480700031103040041c00d40c0b00e21202c00c1d00384140f070445204800b0701850b2802800d1680000283c4409402a00c506400386003200481e03880e1b11440c000e0325401401c103150309040c0d05455021070880325200c0801860054071a0240091080480d01203455000002d1aa00c1c0007400b030211f480104011380c0c09020404980c0d000079002e0262507000e6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 778426016 1250 778424766 778424771
    0x307030f08190f23011d130222050709170a0f020609011205010f08060f10030b06120114010501111b04050a15090e0c09011d070e030d050c010f140109 66
    0x104403001141e2143c0492081d030210504c0c0300700c1d48103600200100910a0b0322107080742d440030040854100140740e204801042e4050182e4240b031742000722a051035184c02c443c28450012080702e0b84414840c040c01100702d510f400e0002031034030f00c01c803281c0225081203802680100c000200081c1004c2041c41c50f05604945641d00d0300300800c0100ca038031614000460045043c0301c00000c41c0650606c413070041e120b820041c0e50066880410b103001128042d039480e205032501800c10400300f0300c550480350b0032440003040d01c481c42c0003c41003503003504c5401d4140340a08448800402480d81c00007000034200420001401d40c0d40303240480d040c58104151020360140781c4800004880c0b0b803540d401400d1280980348151030329902c801818008011740907a080d03451241c0003503003505140c003c0c032142c1200c041945643c803042c1c00208000c0c0241c0064000d07401e02218182c0400b444d0707814018800292529540c0645510034001c1040c00c2d2120f0151500c11103181141c2c00640d08180465141501d81e0031902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 778427266 1250 778426016 778426031
    0x506041803051c020f070b10050126070e0901060e0108072a020d0c030807200a050f041b020a0308100501050a0f050c0d080a1505031015030b01080307030f0819 70
    0x510180c1700c1c1c441c0004500c42e00040c502c2c10401001d5009000344d8100511400e030b140c036900103442c104440302d01d141c2c50840312052200c0004445116607402000f52900d4440c0782604e2008c5201d40c282078010901045880d1558100b950b13010120303507030120140c5040d200200704500c100c900868100b0b0b581d40c40f00d03113150300c1c0b1040d502d40403013941c034466100000b10f072150796a0400c0b41705ca4010043c100c440341070301400000c0192103280450b40e40c8030002c00c04204186000e00300701211806814540d0881d84598000300c42c4025070100180c03414440e0050402c0351154900100302e0000186158400c1816501c10721099030311405a604030b040a09184600a20482c2d05031214015618241035a10403071143d12000395209104501032403c5500038450500d6016003018801910300500760198840d0b0b0b0505038010007900840b4031080485940c03440c5035126220b409282c01c098200446903400084c00300c00701688840c0d0100c3c81c1080d4500302909003410800e5001070b07040e942190a00d21740b201003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 778428516 1250 778427266 778427317
    0x612050708150a0e09030903100b032e150513152108030106030614091902091203030108030c07050a0807091a03030c0d02011b0801150e06030703050604180305 70
    0x315540681380203082059203140100e1203550300da21030f03006103001e17024680c0f0b6202040440d010314814104002e01810340070341c0c00c0c444164100c4056043c504107a020b517030340d81c88100c0c5e503106901800001d0b92002001c14100b80904c81c40c0e003100800d5868840c944091014210300c521010825136070405414204980011130214482103502ca003c0d0a50100100000e07195800d6800362003298501840800c05031020303400c21a40440c2110440700f081c0e083c031040002d6007031aa0041c41000c070010a030480f1200c4095001c0c2c6160001d8024140039800048e0000c00c0fa14104000c2000f042d003150741282050414403055142c01891194103000c5031030f01c00400c103410360365045681e042c0002d401c0740e86510003002019a07807a044240351015500c3c0980c01d4440550300d4640d440c0e83c0b0030701c0e12404811303403810380301d030f80c2401c0751640c10307010400d181c03481348980c1e900d250040d4001c0c030386541c3c0440c450910008010486004a03800c0c0301d005c0c40c42e1000000a80c0280030b80359500c030107042c1d840c4020f24081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 778429766 1250 778428516 778428529
    0xd060903020a0b0a0b0901050103271b140a050d03051909091a211207080c0607110c01020a0f060c020a080307200607170406061806061205070815 64
    0x2d0300101022284401c0040052056001d0710301500221407608491b40d803107006500b100d03580d0410481d4000c0c4000d603400301070412441e0120b15841400f03004c0d0084000c090a00c2035001c02d8002484840000c1109440d524024580c10060102101d05401807142070390040d14910481018140c00329054034100641c50190103010003c0080e0b40f01031204544081307020040c4000c1640310751040038005501222205892035081a121040c0014201103001c50807031140c64000380001c03210000200100c0e9000c000500000380140d1f8551506075803e404031032001c2c01d003901c069013141190b20014071400462203094800d44000e4000e140000e9a01031403508a007008813201c00640b14400001c10f106000e540440c0300c2681440c0035041c2420683c844100a0712483c050300c0140000e640700b42c0150b5941c90402c030702500030b032160200107840350740c0d03142006500d084e071030181c0e24686ea558020094680c020782c51104c02140600104990b142ca14006032084101505005c4401051448440b030344c0c4859 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 778431016 1250 778429766 778429783
    0x6070c0f0209151c11131d0304050a0801020711060d020702030a050c010e030c030a02151b030a0e040209090a1508030f0309070b0403080403110607210306140d06090302 74
    0x180c882c0c0d4051604039000c0e81032110341c01c4118000c1c0c01540410600d58443c500c441c00060344440800020140301c010400560884080c0d8540c0554400388102c03031018034024030341c600354494080c686503803600d002c2010130340c0541e0202d03407642d00410094000805403440303544810000c540c076035101c001c41c6200700024024207400035014400e290250051040025002c00b5000090343d4904000c1d03604828076442c2c2c410084159010390201c01d241d401460408504950310351450a4030f403d0420036040d00c50034100021912000c0e81000500000f002d5005804001c4030030701307a90951030003e940340031030700e6841e000f02010381d00ba0341c482c4030208204181c400b00b40107121140881c0e84910310000880081d40c002c0e0360407001c5128118000602c1c0d10020b003074504507900580c507941000d00d1a1a201c40340e0880c1e02c03020354440c00404c50a40003d0401c03440340d000502000700350141498060020b42100c100340c11082c6003274455411181036a580e103420300c6025900000200b081d040c607250a91410240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 778432266 1250 778431016 778431019
    0xa021207062c04140a051e0402121501030b0103020910081b0303130605030a0e0109050607050a140c010e100b03070308160f0b0906071704061e060f0503100e06070c0f02 74
    0x8010046a11011104000c0d015110940080000c1d1f2100c7c005c80e00c4958801c0e4100300d5403803030600042c0c00f5182404507030860882d03c6050313841007202c1204c0c680a007942600110b452054050043c415401c29048480c2d1140c1c05d0364070401c149042c8541e040c0d9489401081c04008843c1c0f054071103c90b102031094980c0e20742000a140724464807204d005c0d016420498a51141c1843d00350603004086050003140d440300c3d00000a000540c41f0080c00b00e4659210020141c14854030680c503480c0d10000c0c6004180481e1101b00002c2c0300c0d00c201201d41d05010145017130040b0603051442045e8107503804100b41d8101c80d882800160303109254030a01411400b05e4001800f03440c0c90dc55490180060a106584241801c4003640c0d41580d0b44082a41c02d8007070020540208010800010001002c940c020b9407410b0640ca03044004000201289080e103046801c0302e010210b001c08100300340d08082240c0441112008401d00001035140d1005030b550700020440020424140100004e2220080c07032a40e51540 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 778433516 1250 778432266 778432271
    0x61112030f16141305040e0a0f0311010207150905063103020c03030a0c0c080a0308060f0102100f06090c02060c0a050a090803181e03060a051909050a021207062c04 72
    0x105440320806010542c822140a5414003002c5103401c6800b00340350440323950101040780d0410301620708959803101400304400640d820004800403d913001d5200106801032000801c418000c0d242150a004d000f501c84102d510f1003210b0112644240b6590b0103000d8200b12840300c078551300d400c0492408044240d4990075000010300509401c0d44241c01e5140325000f848050849036851032002e5031100001c00c090001000b1901140351442c00c040041c00c072004c148101d0342c1d03060a82501500301d411017892040b4240d0349042c03c00c41d0300f25074010783d14406400c1c000382406140c4103142c11030f94071601c4001070400000060449c4041d02402d4101c019050107811070352615281d682c20704850080580720742c0b28140200f4954407042e6125410700b1040c6010f006031a071500d5401400003e8600030b8000c44501d0201002d10810084a108088465025000030304122405005001c584884004e01c459142c01c088402d025040d04000d00c268a55090b0300c90b14614401c0c450403039200201d2620050340b150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 778434766 1250 778433516 778433527
    0xc270103020f010c291b0403030c0c090524100206060907031b051c0905030a0f031d0c0406050d050d08090717060601030605011b020103020d090c061112030f1614 71
    0x41ca05c01d10394031145408203400051315850210840d40c8100d12a02d0000c41013000b050000900c10f00803100064070842103c1c02086d01c1d960020151002141d1440100c51090100d4809420500c40340d000c1401c1611451030510201d02c0007074840070000c0980b0b000702020400300c0d100314800d130f01a413001d0309030071412a42d20302c21400040040c3d200e0305010402c2080b4102c2030300c0601252040642c1d2a9010b001036203091003c0800342c1e0701540307c2c0c1d480024969680025281240e100d88410002e0005e00082c0070319018190800048070116048180900b6009030038000040001900384080041800c210303040e03070746061710a403903c003203500000703a03004426507c0340300b80e14000795040c003c0310242c070300388002c68452004484407031807100d810840242001c1480d000d54040e0f8010320340c91482003000b003100101078580811500007680180000340304001007051400060181e0b00030104108610f0f851810b102d00f441001c0d040281c1400030703454a400d4a500d003140101c50340040d0710103c20400d901c50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 778436016 1250 778434766 778434803
    0x70501110a1e0c202106010803041a1b010f0c170403120209061603050a02100605030307153801110318010c050f0c270103020f010c 58
    0x25085064428041030000e049980080d840762100404012a55140c42012050713803907040346030000004d4601d243d1805085003000e602c0d007010000352241099071004450000345c10082c54103034160302200c29500b092000b4059141c0c0825480d29265005035401d03100d900a01a40f003280350f4a2a080005610380152032500d50340b96082043c01507566156050f02800034410f409103440104d400a0003d040b18070031044595055024004e080c1c4003601c000d0602c01c150100a00b8040da0f010140c002c140b02064244049504104804022020304814000c091030100425030301c1c010032400501c0141c41d41101a50b649050b80240d400b031600814410b5a0704d01d09a408500144e42d0016001d070101c0d0348611001075008055280110882d80000d5184c00c0343c840011031000303d00c2c13190078104101c501d1590085981000010b606400b41c40c054840240000d08102c241d80e01c0d1307100408040304040d15190440118158541101d806842021540356070200407500d40506000007000d221100071302031400b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 778437266 1250 778436016 778436051
    0x60a0603060e0303070c03110c0310050f091902100c020d0f03090b0906030121050d03060609140342010305011503020a0b0a05130602030a0f08010503070902030408070501 75
    0x46074020001004468800705038141c4901c000c82d20b820100700e01c0210a00081d100324030a80034207038003905852903100c51070002410701e18192030a04000b500c480501581c0c2e03480c1c4000640018030f1070010b004003145070000a41c2c4220001d006441504c00c0700385400e0641c0107440303480d00550b00800e009030702070300341c40e001003981c2ca100030690004000001c00300d4a040e10384222403401c80d00030f0a01e42141c0c44c10342c2500b0001ea020647c0380300111911445000244104440c425030603003610040390150420707200811640031a400100e0362048050813103099140071400c0103241001402c036410151580c4441c05e40880030764226030465550742c442880948411046605036071142d0028030000400611484404c3c0071404040d600040c8520104842101075004141003000307030418034202041505c5540140754940e0240005d81c00006020181c681e10606444040f8043d04142c2415410840469a516900e00800c681c182d400001324062006c0007003551241d6900030000d21044400b0340c41c0782c0c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 778438516 1250 778437266 778437269
    0x32502030c01050c0906180d02030a081e030f04080d090c08010b04050a111611040f0b030c0301090b0a0207060902040603080405150c031c0b030601030524190b01050c060a06 76
    0x241d54030340008581c0150f1004100c82492800400e00d50a00007100900c00b1a11081d503c03040c0d0046d45400110300584040c0003408085000300d081d143ca642080100362685a140303c005c0c0b040352003c0040004d9825000f030310329080740e0030030300742d41d2541042501071000b00491170707002c0c6c1524904180000c0c030380015040b6a100e80b6040d141800390391212070041045e030301828450141c4070014400e030f20100302c002c2e040d9029a4012000c0c94021082080410304482851290b1400c03aa1240708039002c40c1010440d0358100001603000704a15040c0392182c9600403000303442e0791143d03900040c0e0b002c1800035940180814940080003080303141c0e56850140200d500a1198602a8051a025200546200c42525180041c41c0042c61030000c000003440c0c0300c1c00030903000c0504103039118850391854a04010300d9000e14401d800608407520140e034021a050704c8008210428280142040000441e2820203103480071982c10105101d580303e4016106409411551080d07403182404110b4008081d070800c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 778439766 1250 778438516 778438537
    0x20c0316080111070c0504022109030304060605100f0f0c23010e0706020a1e0516030b13021e04090b0a09020a0603093212030906060901080706030203250203 69
    0x1080c030b00c0383c0000c60040d00910702e0240000516040800c0181070a400030101805440041c0501e002003000410100505461724000e41d03101100700400c000e0b144c4151006010100c4c0c0d107914002021030014040010b0309000c3c070410605000080c9114020030080100d0342d44490b598035240c110000a542e4146005400751056081c0b000c0c45070105e001140500c1507803d254042d10010580d5182c8400c508c171041c2401c44d4082c0100007100c04a0424070040d0301c00c6406000b0500741030700c1c40c2881400100d0141100d01095000d101400060b5030304031004518061131001c5812100700180042c0080c103103000f001c6c0010b0484010058403828680c020034419200b1507607114020344650044040350f5100d24001c1042c107060304d012804c80d030784400c2c10340c610740c1214139601512245500141400400804044e03015004424010070840070301120351710100540d0302040c150300d8038040030340c0c070f00040c82020149640000030071400703100c1c002d10000421400b0001241c065505200942c3c0343d00019040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 778441016 1250 778439766 778439771
    0x1012020d022701050304120e1203130e06030318040e032d03010e060111010608030c03040302180708041407030203070f260d0e03031312050d05030403050712020c03160801 75
    0x56644a884290062488040e9513103801d603540ea0b603d00003064440b46040050041d9075410300880c0d5129614942c04214000c059038031500e12221f40c1c40c02c84050703040141159142001c101903030704d0000580d03141140b040510500c3c805180046001407003440c1c0c072114180000180602c01c410103000c1c00c058088a08c3c0311100c0c00c1d00811240c041d0380003c3c0610b189025007400420250343c80340c65a80d65504400707000085032641c031410240f03946d01141441e0910f0308080380400c00e62400b01c0c3c9110144000da0007128951510940c01424403000520041030380c10b00250307062040c0300c03c0012801459018089500e459160a140c248a00c614811144140e842c6029016044c900326140c00d084002080100701c0d000e030201040c2c5e03100d0801d8400c0f68152000b80103040c540440b03e05071000400a24140000003549410818188941d202c2d080090241c20400e00c0b00099002c4c0440f003810760048401200e0291159080f030401480c84081903152040c6031210720702d00c0d4991040001c981c0104004c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 778442266 1250 778441016 778441057
    0x130e0402090a090201020d08041a010e100f030c050607150609020405090a0c0e1c060f051611030f0702040f02070b0603010e010b0a15020115060c0611030c091012020d02 74
    0x160015a514110000d0051f044078414001c071501401015400c603100d98114100046e00c0741d030b50000d20100364403542c21070042c00c09206126080d43c05103000303860001000809641592070b06001c0400e24407800f13004240014946007032001400485904041c2680c0c148546c554600d800e002070340003030103441d102c0ca450b1004140c0c10916885001c1c00d21a40d40c9400155210344c6c02001401d40015400c201d01c01c10780300500000841601c2001c62038805400d0014040c10100e0880384201030803841102480344903620f90907410000829500040709070308640e9a03c00d12440030074040d003c030910600752107002242d1103003004841102d943c4a00000e9008000b400f10402c5400d00740e60028280941000b4116802d0211108c40070101c0d42032141800003007505801002d0380b021010341c65100b000091800303407030002040321034014a80d14468101c0010705604080c08401c95a10504444501c40c0d48102181c004260140310000c680c802c0c0101e0854442c2305081100700a544813000340c4e4200d5814040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 778443516 1250 778442266 778442281
    0x120324050103050c210a020c010609060e10180e011808030a150506040603110702030d050a1e0e0d0c09060f14040501030f030516020a03080705100b03031e130e040209 73
    0x240c03500790b140600185d0320000d03540c01361005194080c0003514a503400f000301a6161000b40151070080c040c0d07142c009540e915080c60200003240240003030354860061070042100c80032080313101d058405010800a4020b02d43d50038540100300080c5001015841c40080c0414001c03800d026502c079040790b800c01d00410083e032140c21189100c0d8000c05500110074402400554440e81c894019002c00020300340c9440b0707803600003d141c465441e40207000268001101c901c4950b1001a40400700311000303643c0c009411211010b030502ca04050501d0168004151203000e100c8148940302c001e103c9420108807840c0c6503071800c2807044090089005503030804d1980f0754242400d12413a070490b0340068a00000c0036803a03404580b40d5200c0d004829910b002c1002c8480560703181da01280c025881219115552441864114201203071544802d41551a0842044042e00d0200454100c0c810440380701e2001d0111301d000c0865401411018005407514440100f4010100304507180507900803140c07480140d48448 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 778444766 1250 778443516 778443541
    0x1401020f06130309090f091703010303020712020102011b111207021c0203070b0a05130e040f0201120f1d060603030310030f020f03100f0b030c010c12032405010305 72
    0x2840c51505034801e40000d00216800b40044090b28400d140203203000c2c0d81d84c0c01d203c0640c0c10041115a00b103680b40210410460510300c00c082c0e0036440204a42190300d1074074080d40350003c0d4818170311000925010002103a100707511224035a805491094006522513000401207212010600218407071400c03541c010748625030a6486040c2e0003008d104c03030a01e004a6640e28a2084107049815215000011400240081c050f2000400700d41d902501d420480b2081d0846d501c0540c41041e0380f46148007030002250382e102c0e04404d15502820720140758140c171418140204070700c51603080014a4200b0b040b2544442100302848030028030b0448030503446540c10036481e8881070760141800350301c0d01410070000c0d40845564882c41d00061042092818050120381400d4402c2c10301c01c04569581c030b000300d03051201d10803244421360590091075151071071400a070011151950181110000e4101c05001500c240c0000da0b00081560440901d4400052140b590102601611740400d0030000052038081880 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 778446016 1250 778444766 778444783
    0x504030b060f0102150a0911040b01050315010513030804030524070c080412030e0a06030b01170a11120417090f1e0406260f03030621060f01140102 65
    0x1640d1065100d000812282d003111801d054190b01400d2082d80c0d1810b803005180d03118201000b0302240c3d20741103241140f001c90f203020a6612452901440c110039991100649900201003104141042c00c1100146c550340640030129010424108010003000322074000381003180d103e42c08540321140700e92407005450741c1c2e9a1074103809100745030004403820f00c20200a03114034059002c8616103512100410071112410a0640c080342c844046040203050010254006100525040041c3e410000c0020300703c0410410294019007a400452128a40c0b5481404209110001e05503240f66240100e40d405d50101c400365090321103102040240e1146000b11000341c00e0041501314001c901404010a40e03640140d440300301d1b0301c041508525a01d840c801c07040a040303c0c03201001c0d000240c515024048d84461150980da801c08244030407510300000c21b59400c440c5c1240e00404501d051038052141121904d200420b0303102e00d4080c403418015801405040c2c503c203240360300b2910700d020b006a0799403803031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 778447266 1250 778446016 778446023
    0x80f0102190c06023a11090105070804051c0b010602060411041d0a081305240309030d11041409090d361401080411040225050a030f050403 61
    0x204041030525620522003441da01d40305120043c101030b01c20201784024401c0c3c81c8020f15001011041184400551002c811140c44000061010309441010040c0c40c0c002d160b88141808000b24011040109640c240d401800e400381802420f0702801515001119046500799051307500417002291503440422254851034202d01042030701d607050005d02000342000f00c921040c41034400c0c010040d0880a1024000040c020f00e0001c0c1c03914002521304080b80e120303910076407290404000126100c5001030051024000604065450f5943d02c00c15600754460002084406032800300300345060750070b00c400792054402107401200481c80ea00103010035840705850100c12030340042803040007513200e00c17001c0c142c1402c01528100020140f105001d00358801301112416400c503013400380405e0424501404e03130000246000d1415090903200e40011620110400380510307000142c0c1c103070039181c0741d203507545d00001c41b20403001d4290203041964417061407843c01c800141c0406882d54205110b81c2c2504c003543e03007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 778448516 1250 778447266 778447297
    0xe2d0c042105060403021006090b01081504020f07080d23040f06200d05090115090506030a0b0c1b0f030429070c080c10080a15080d09080f0102 63
    0x50400c40304004441024074071906004080366000607009004080c06184a90010b14400314150f80d00740907140c03143c000040035031501100980e180c4e4041d001c40e4001d5a02150280d60303429500201e0040e2080c0c05618041c24000907822041107080b9004209909494a00304091801c0c0450300d101c0c13132206014450300c4c07500200403e01041640f0315405081384100d6000501f80507071046008100240d69a05003030600201d042c0d00081014001c5560020060000b08020390010400c003111900c0ca0190f92441c0e9918000030354191410040b9504032a00019220f8540c54040d40c0710304141c1c842074018a070100400c6800c0100000094240040740d0800040c42c213090030030b130002c24440c5505084c83c0e1182e03090080518441000802440d00350300030072001640302e0502460518140c80c2c0c40c1090b000c3e80031001c520b12103e81c0304812a4222108a40108610f10b010748211030b4080d59420880349030042c0340c0560209504000c444040310843e0060300c2100b130510700c1c0c1e00d080340118140e4001c15034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 778449766 1250 778448516 778448519
    0x601080a021303061118041401060f0504090f0e0c0a0524040e070801080d050903030715020903011e0c11070b0313050f011e0510140a0e2d0c04 63
    0xa1494010b0701500c002032451511095807515004142d5070030200080c188200054036600c00400503148041e002c10a560521826419070203400b0048014030a0004001144040710b01c0709215a046400a090a40b0140300c68120010200c00a2102400130700ba01e11030340f02000c88906007080c0b8481207850040110301f010403401c2c4200e103003a01d86000f98502c50380400020a9482002414034042c030003950b242c03040383d810521001c2c03802c940c4c0d6001805005050200d0f0080365000022201c500ea4044804894071020254850182c020302c20310f240e05500780890300004464a004415050281701c10070701003007002e04029240180075200f030a800381c00c807490500104403818019600720b01c0e40c8150b40c80f150300d25210b490400741d14044100d66030351106040040c54840703142c0c6124911400e4410002414a444080107210403481098410421804604500c1d650145242c0003888604810016440d14107005544d80510080c9c00349072021300d412030390304c1301004420940f282200315241031905 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 778451016 1250 778449766 778449781
    0x70f080d030615120f0612060911150a1b080d1b2307170c0a02031209010c060b01210203100f0e0f0408040323060619060e060c0f07030317060108 64
    0x24441c5619482e17070145c0703824000420380b48800b02004500e000c1c00000400104a181c01401c01c42e01d0000b4074401d020038110060016002c804503038600c0c0340c5003069004021443e580c0c866034102c00f0400b03801d02e2004a110020200c042d080140440a42e0109072004a40100d06840c01c10304c04445070a80680d0311145407401b581c5600610001d40181d0b45c041120403880d01d101c00e00da21000d04030b20b182d04050603140071406c0401018007150241c84106040c02c0020000912584503050007801c40d03a00d5011010981e401031903040420090203030988111030403111100040d600980e005031982d6285040040c41d800e00d41c203014160350540440e000c0742e466103800690540320240040c0c0c0c900c6010400000045c0541e0300141550f200d0f105011240c02c034035042641000c43c010308540c0251001c0c2003203915803056441d40c03010b85980b0300308000801e00d400042407031409148060b000d50301c1241241080018001f80c102c040300e10030740d156107802035442108103480c1c1d03003a141c06010846400c0822180c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 778452266 1250 778451016 778451021
    0x10f0b030a02040f03030203041802071e0303111908090d020a03140904090c0302130629090303041706071412041505042910030b0702070f080d03061512 67
    0x49101e0078805414580c42d20020710b1001c0b1240d20842c00750380000341c10000740540a410514070908000c0c110f041c52519100d0081040300d042c005120310215040c1041010b000b94005540b00114803512a282e250700310903000c034160760b00c900c0804144c01000051009a000500d4204002580c3c0940b42c610b0607a541940c2412610405110150080c0480100c03a00c59124680d01e5070b018280c0309180710b02d140144500b0b4104441c8010000f070034501d060212102284500070300c0714020314050340368110f0300140c110078050541c005034076001c0002c0020b0302c000d0040381d080d001d241003020b41d090b50b103c0350f0041e540600045041c8080000900102e0420711150302500c0d4400d018050805200706110a07400454004803000c803020940720317040005d01071051611404101c00142d0700c1540f0308000f8210200c428261100500341d082d6071000409452007804034500802c4400f9151007001d4503491440d0703c503040c401014001a14209002400301c4010404003040c0c09941c036909401d0310445400000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 778453516 1250 778452266 778452271
    0x20409360c1a031503240603070b0414030613050a0b130b0a1a030c0a05130e0d0903060f0b01080601110f100b1005030412050d11030f04060c0206010f0b03 68
    0x32035881001000503000d0411142420500d00c2c2d00240355680703400c03a5a4640c1d1050f10322054025401100c5942c1250064165680103444080508109a07103a05c0064680b19050b0421081c3e000c02040006000728a0100311039a0b0700100c044d00e00ca070350381c4511000203080e050801340c156800220000082200c1e41030141d048142200c825010070751a07100e070000c11030140c4079910b007143e46d11496400c0c1340070504450100c1c4011070203801c0c80d46001001405004c82c1c0d01406200c0c201c1940144100502648502400c5c0100c2042d10522107010708082e000000c1413205440b258144205000c4c81880351088110001c016101c01c00d2035103a90780110b40c107408030035101055109814605403801e10030042d500a800c1c5000022a8a004000c203010106085030f04440a000c5d080c0144070000342d11200000c1d644100d498035a031100c00d07108100c005001c10350b104500e808400014445600e801c190450312542c0184014081500d0605d01240e584d4024416a140005221818480903850000458 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 778454766 1250 778453516 778453523
    0x60a0b0d090b0403022103062404050a1706150a090504060b04050a1a03010e07051212040303030b01081005090a02070317010e04050708060105060f160f0602040936 72
    0x500e05981d5901e0995074003040d5819409a841241940049809101d00c200310258842000d82181400404140c3e44800304c03050140c117100300c035401d1100740c0480040e01d00804005005030b04041d03aa4645a501c58866030422813a07009400000c2ca01003191017019100b40c1018050600440c034242d6040002c100280046a8868840348051060b980b01d0244502801044000040c2b00d50141c60141104110000d11400790341004206580b00342c0200d00901102c000760360342800c891002c801117007045907914511905480205020040c1a40b5500041d18480203803140003864541d5410928020364030700c40d55038810141380000c1c5040d002134000c0c14a1078401e007060712160350403580c0302e0082c0c0d070243c00c48000d500c075034800c000030310501704042402001503002800300c075418000030806611801247c0c90202c200010780031401c00c0e181000825054100d15500b0380d406491a1010180d0311602c200d0150303608003d41080610303005c00b06204400703200488030300c16004503a44400280c002c0581034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 778456016 1250 778454766 778454771
    0x1101030b0a1e060c0506040609080c0106080607090902070507090f06080601081014040525031515060504050a23130507090f05012019110301050f060a0b0d 68
    0xc2026031540742007200580524060b4120504450045407040c104581c001c0003013045110003800441d6000c140c1e00d0300541c1102001c50b418000d0300341074099100d0345440c3c4d10b030380d03182490000c0c40d0301001c00c7c154000c0342c0c2c40d03440302544d5650314201c5059009130354000d8100d4002c41310400440029905c44801c02d40141c0c000b09000d69a4441c007424484240c0c40b0144640008051810848081c41802a0907807441d0003d445810315894103036543e56004d2850354075900600300054221b452201402c025603111101e501021603901d00c074005840300e10345842e4400c003610008501540200280c400713480016120300185490b0202c6400c4999076885c0f14410001024005003240d2101985030340707000f00045010030142050b2000400020103580b0070103002c018040244696a4041400c10607540314808404c0c4000c000006107080a41400046c5464107460300c1d5030080107070746801c4940000084000b0000c0340d40c0e9030b807070181c042030440d40305500407500b401c18402d644140b0054006a103151800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 778457266 1250 778456016 778456031
    0x501143301111605090f010e070309030e0a091a0126150607232b0210240f0501020705010f020703050a0c0302030c010c051b0102010905120a0f0207050a03110103 71
    0x2605003030f00800040009503a4003414440c0d800c29081994200307030004903191042d0f00d0706017070503030121028010ba402c254403200c804003410f10405070305500400080c080c0c4406a0350f070040c48014070300445601001c0790040c880500541c09401c0d103181a9041003083c00d0980109030505145000c010101d0145d054284120078081e11154054000e05104204a950b070240802c500311480d508800540c00319030101c501840758404003075501d40c000781544042d40700201e100b601030b03040264941c440d940d52440c1100306140c1a00307040d8a031030410104045035120070323160a01c000c100c0c0c05078024940540d1005008010a501c255104002c080c141d20640300c01760380b039589030750500c4880c0c103054820f0415610280103610301441302c8440003c090130501001380865648580b9014903016480c01d44000c00840d0030341da4001e4004d02c01c595440360507500006240c504200c0150402c0c3d007010001904040c1303180b42140002001d00a5030b4005040c0c0010354515500c1080b0441c2120f60300c2d0405464004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 778458516 1250 778457266 778457297
    0x10c020a0b0f0417070f030204050411030d0e0411160305031b03010e1b070b0c0d0605061c0c0f020c090417130303030c020703031b030c020d0501143301 67
    0x240000903800e0300125a0f940c03038071003400b0b402c8505160342d41440e00030381001c00c040c41d8001450802c482d07042d640810b240c1d840f820046207041100d00e285415003e5612030f42c0714141d0050390070041000c101c80401820201ca81340d050240108000034006000510036074020030f004502840e884013404190340b00302e05079a0b00c118000c1c0c00aa20078465032010405005000c00601782d010407819064540030709052203030721040e04004025007588c02076500060005003035a02a0030a1010702006840c26a960034403440c9280e200004d0003d502c00c1c14a0009000203540c17084103101c8880c24603900a10020110204010589001410403070300340f40c1104940f130740302c900f20707015018494160400071109442c500307014080d1011600450110b421813501480000c0d040108803080408480794150502d45a181c16646000800c101946c41010000303441c007040b6054119076501407140d10b481c4c0e4143c6400510b505a2815001880a080c0361040c0e40400f409008441524090052400b4804081c0e2200d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 778459766 1250 778458516 778458539
    0x3050f1b0409021e07110a320112060e150f0105120709122f13021602090c0315010201091109040c0f120c0b09061603030204050402030f09061302030c010c020a 70
    0x400702e81108586d04040200d03d40702a542d40241500b500c403100c8016640e0030280c0c060724008520320203951480403d141d60744900b50a0825080241c4100802900c034a883d040d010310441d4154520012a080c00d296410102d204c080c83d42d40c184c5910f030030016800b22844040c80014a044100b02c0d0548000490700000101500740030b002e91032400c254651030b141d22000318040f28001c0000302c0350a404080a8454141000b00d003c03000000689071540c0405908404054010107035001600340240401e2288080080d806190031030548040140010f005a00f66403810a010700880280c0808015a0074203030042503009200b07001c500a142d4440e0103040608000360012000d0360741e080020001c110014050070050454003074154100901c110003d801ea101c4d0001e400b82540400420804150194041e1800b43c00000c01c1903407240b070410400c598032807046034490010300c01d0101081d503c55100800c1d02402d50040c028100c0d09004030015500702c051a0344c22600424180000a154040c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 778461016 1250 778459766 778459777
    0xf05010501120b0f0f070e2808070e191a040929060a17210a030b01030902093d05030c0a081c0e0d0303050f1b0409021e 53
    0x681003440c50b440c640c00c003080900b9000700301646010800c4244090300e03091090f05d80e4800180d15180d007142d06251b000c41e4113440b8100c480981c80b8800003484209a5075403406400380d510000031240c01d43c0c1e9035400c021040d8025103881207407200701030402d1f10110968114090545a54040d000100d40580100e002c5411100c82518240b01d03001200764491a4000085d610a902c6003020380d690030100c0009031104401e118401200f44101700c0c014944e10305100303180c42003569900303c1d646044613840c50b06080d401980b2410029180401003046980a441118425a0040c00b00c4045948802580c1e04540d0f00b680005100003d48600c40c8021480525030070541c403030480c3e815401e51510003818588503000e28151b01c203d408900500c00490002819043c00e030183f440b0b003c00303800c2c0f00c1c0103440d40e0f522598029004500000241d00f4181c140d000a4090704801d80d260000380c0c4e07611010b030036524004007500c1d01000e00704010030002d00a5005810300c44020080c4d1420501e5564020115034001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 778462266 1250 778461016 778461029
    0x915071406040b0a020405030303010e090c15070506070516110109051009180501150c1a04030804030e190e04020f0405011d0a09120f021c111603020d08070f05010501 73
    0x3241080b0401400401e61904a401c00405504042c00c140000f40c0b02c0c04140a508030510070340c2c0000d070500c4d50400c01010442c001401503d64000e00c84e1040000e07610040701580d0510805001c945054800c00448420180c440f5030031400402a6880c0370b003e07492088690b0400078101e80c00324041d0b841900300982c2580c2900d42440240c80d240d151082c00e19044480080d0500d050b004110ba0703040780810000b161420702d0007000300f407140e14160144007481010400d60803490710422082607000b202e2103005501948950140165482c00c00c160919071043c00b4510340d2071290104234940c0d00f0350940b60020310062840b080301d045100450101c034003d9101c3d04c2006050300c9082002c00d580d5078060b4026115045c20b102c0c0031520386039051540f0480005908100e010128081d18034800d03c8000c0d000304518440c040b11840c20b1750300500906c250380c14081c82d4060035015208680114008100300ca0f805007660440781d10a407070700c0b000e603003100d402074542e503110030359a900003202841418042e055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 778463516 1250 778462266 778462273
    0x210608010e010218040b0a0b031008100e060a0903200118080901090b04061409041d0102090414040209070f110304030503130e06090a180602070c14030a0809150714 72
    0x12284c07a0600b02542e42094055403070094000c10a803240b114120070b031818260125925202d85100ca01c5000c900c0c1d110307584a010300c8811003421001908441c4042802800f2200b0360b071942d14202007214400400100814644425002d1072034001c0c0541c01200a41c8000007007240d2411800c901c0c42c0007081048490b400001201d20b1550780086000001d40031440f40b036410300b814920050314000c8000c1707951400410200d284819a82c1b21f0300080302d0305009070884250904103220f018042c1d081307151054852400e041d00502d03466260200c80748201c2e002000d85049469802040e51030300c90224034003042055140000400c02010001800118820b100a55603600d1280c48105425803a41041e024100d0401c00c3c06600da0391240e035542c210941150000c1d07401c0e40020348052543d51404024007040c00440c08509201c00042c2c02402c40c0e80010915903844503000405880311209400203001c00020302840c030160038442e40f4003000008060380a450140c075501c0305440103600e014500d80d10b13813 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 778464766 1250 778463516 778463527
    0x70b030106020127110d05010216020901091e0902030a17030f0c03010305100b0109120501050f0603030c2503020618010255030503150a06210608010e0102 68
    0x354240f186102c20f2042c5a0b035003488101d25060308401000c0c004c0064580c8804441458081e543c1e40c4111403010b5225000315a103908150301518215031014051340310760000c8000054180703031401224998000032440c2d80c080c039000c01004008015100c020790301841014821400581102505001440e1030092280c59160840e01c3d564104001018496240d8007030004100044001642d1000055242d4002c1041041200122001c1d1242c2d8001c0e0043e011014102c8144203065000314040c0d00a01c40e211250ba40e41c1081c95030340e104054911003070350302c03c602e41100304001c0ca00e6140031111038400000c1e80c613a41d400080117500011620b814040726000e00282c41c0d07804024020501d002d0180f20301d00c100c8440800d01c102c0300c4801140c0c0b00540f10b4485680102180c0100c40380c6140da032140f000004540c0e040080c40d07500100c40c480f13482004084000303030030b160192162044401a42e121107425031500e007014552491802003404041c3c0760500400c03030350000c2c00342207a6410110001601d41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 778466016 1250 778464766 778464779
    0xc0f0303041b060c0c031214031f0e060108190207060c032c1b0103150b0702030d0813081b0f0615060304120809070306050c07110603151002030903070b0301 69
    0x651955000c0f03014460984100c5001480e0307094400f040b240c0250055000707801d154000e03035194905170080e0070b4a0000200300030100c042c00180074038407224140806801521956942400c8000f5640d0703501180750080000c0364400c401a00b01d81c0103007404409801c0040303c0d62010217450811924401180d1030710801e0901c41e03941e411307000354100d111000e02803803408000040e85030322030100c84c41100039941b2400c0e0710700d0f4066046811500d110803900f410329a81c1d03052826454001070b00c01c901c24000c0ca04240b458911480c5451b0260001000e512040070340c40e504c0d03807260b912030000b41014003c0202000c0341c0180610000c0e40303481686003d441c0c80e01e00801c100c0e04500807005014807501c018410700011074280f00d01030303050a182d8107112496407034079001309243c0066540000e00d501d060408200207400000c020b03140070703442000c0300e41103507035441e0401c01c9500084038111100c00d06039100701e070381d45080d0301d0703c200c000d6041c010f0780d2802180e90003190402c0080d0700301d0a0320000000041000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 778467266 1250 778466016 778466063
    0x1211030402120c090601030b0f0901080106210c27140709080a0f0f2301020a0810030218040c0b07060b1203040608281a04060b0a0f050c0f030304 64
    0x28003200740a400c00c1c105110004d800c1820161220341015981d0544c141c041c2ca8007403c1c0140400010a05405581d54481086c064000c070302900340703031b01d60418141c600c01a0700070013080300d0381d800741d9800002800c10010b10506081ca90700c800d0412403184921103003082511a09858012188a044072840e0900d80a0121500d59015000580c0818482c401054129045052240d403010440c0480105400c04421484a200c0d11107405e5030b039a0103082100c40f0560040c4482440c0c0c4c1c80f83c06e080d5841014280c031400c034030710000e9040440030f5131400c0061022500642d1242c0300c8d901014100d9118104050141c11186080740c01c2039582106221031f152210a610380c01080703000841c581418010018603400f000b078003480c90003000e0300741d1020140115141500b400207070034cc10483d441c01c0d0050990440805c60300e55000b14605003010841004150403101e800303141d81c5400c40034080d1540d040701d96a1000f00003c0782d5004a42444800c44001d0006500442c01158040c20841e00c00492608 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 778468516 1250 778467266 778467289
    0x90c040903230412060906060905100801110909270111340803040807021009060f032a0e1005041a0a0f03020d02130b0a020d020f1c1211030402 63
    0x1440b083c0003c00035903e136084424140380d030240021445030481d14200006d801190081c5c3e0380241014100300780340082c01030405c00c0340d134032100034003c3d0707459440c1c0451303244105201ca0750450980e40016280c42c00d076221540f400c000c40300c0043d08542d0502d20003800c442c0a40c4001d560408002480b05d009142d901000c0300baa01c0c01d2070030308180b0b000d004d94007480e450104402014038201100140500120806480300580c0141500a06011010f0010503084203402082d0110742c005030150340c00c6104c1d1080000101c806011540c000d01840000c802d2000c1021200c010002c00640c81080c42e128070301c40f44a080c1c45600c4164035503003444026200043c60200200400c042170043d0704050740d024600a59044107410010703582d400c24000440680f00b803070b00c0100d20350b5003404006910a00700e0000c060750b0003c0d80c02c1e181c0f025041c6800300c0c1c50f1080f07090303503041980c80742da0030b0f200200380341020b400d0030030041c2000b03840c0260102c2c00406a5080c04660604414040100f00070350800032004071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 778469766 1250 778468516 778468577
    0x2180a14010518060102100905061605180f03031e03010f0618140105160c060f0507050a0b0a1e09030306051002060a0e0f0a0b090106050f18090c040903 67
    0x250305150116021083c0a03d802040e0540070b0b000c21800e90090000c6c0441e13041209042c40402d100c1c0c284607079100f5043c0d8000850300d6600d0b5a000509100f40203850444048200c6203050a00c0c840070030401c104007110090381400708011030201540e140e078124104030711000c0c1c81c80d100d41c907007807003210f00601c82d51280e024007807845081e0306031020750f4440001f65900351017440c501410300340049916000340c44c06c0e000d43c001902013a6060010302c401650032120f060341d4614903009005801c44090144045c02406a40702d0071070039002902c02402140e000340c0395000000c001d00300140c84000360115a032400c1516a803036070644285903042c000c900c080c210540c1d082c942c90308071030302c002d6984000800d141c40b402e503545108400c000050220303c40d84040700c01126902c0300f050074031040c1c0d40c6d01078a40d24055860000300041c0c50400f14608494401c00400104100d00030024818803c000140044d60a003d01050342c42103a4443c85400100ca0281d0340344100c0e00c0d082c83c14054852130000340d14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 778471016 1250 778469766 778469801
    0x914010e07080601090c091d24131e0513050c01030204060813111f03051006020619091a0f09010608070b0a0e03060406021c053102180a 60
    0x40c040d80800040b0941110841c5d400003c104000300001c0b42c48005507008000301583c0095502d80c00400d000320940165072500031110061038649070709651000303201f00c3c250490070303010042080c400d46d6404001c07003107080c1c030081e035003100f02d01c2d40d1000b2540c0450340040c2c0500500040380034050100408032913508282403c43c501801e028000c1c055000003049101e80d0581e40c0180b108001c43c03413010b141d00c03006c0645455910082244405c2c0502030030465640042e1a100c001100c0c03030302c604040740856940b6005401d03e40c558018450241c3c0c0b10140e00840749890f10184800505900005d01032000041c011342800c2c106140960b2072018050000c161a071304080c0d041c2322140700030494004481c00003070450fa8030b107864001604c46040e101d01c1c9076410300070301013000706014040c0c0003803004072141c4100550903031030304070000100c44007550740b04440b40d01d00b80a045031901c540c14020074002c00441000c08000380e9030001701030b02040404079107680d4203a010701040214501800c000030006000d030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 778472266 1250 778471016 778471019
    0x80a0b0c07021e121e0c0607020a03060b01090815040209071806231204140a03050a1409030109060c0f0c080702041109030a060c121406040b040b040914010e07 70
    0xc030740106440b040e60030b6103078542050391540d84e003045152000d40080700b550550926102c04d050000e00c1040410690300a90b96140c1603454442c04690025600620340c1302210f045444d00300003001e03070803566414054092408103004c201002191881c032924040b42d44145400c3c03044c403220310070107000c031800c4c440352112a42245840c0850803041e00c4042c500300c0300d4108104180d000c00d45515580b210082d1000074603c2d135415200800c54031480c0100c882c40b203000400d0405aa84550385003001c0d0024109201401c045485072020104e03001d120f0780210708140c03030407001a00315016107400711002c0780d45595172400f10b03403c10242410700d140c60030120300500850320707008214860709400030311469071101c42240141c40402030350000e0001034200c4035400715624260000700301c0c8541c1307480420005c203041d103a05031f0f4600032140d110094415143e41d9403135580501000e01810b04c2c805078001d444540c10a07154646104049106006550342414510031461007403c44480c41681041a0880b250 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 778473516 1250 778472266 778472269
    0x60c13030804150207060504260c04140103020a0515180a0905091f110715020d05070810081605040e010b100923030a0807110306040f120e0a1703070804080a0b0c0702 73
    0x40b6520076a42041127103015503440002e00d08184201d000c995100e490a0030201c400c040544003903050340e10942d54100780c26110001c0200310748100420548442e003c02604e81002e0007080c0c00681c0041c06000039010f96101e109035000e4440807610741d000c2d680054101c2c3c030101e1103150320301c20000c1c0e41d000800c48a414500d02c1c42c440c0c800c4007030162131002103084c6880c0a4100c0c2e4110b802c0c81c80980001c1186007002c20b00244400402e0300d8000b400144500041060000810f501c080d0f030140a4100840034a02028440078040340c40d0164019546c40481300220f4590b2034100758000a01d6a415000c2420b1808640b0000740c0e110140e910070310011580e05290314001544103032247c110126580f5042d4901e0201c5044004d00301803034050140d0003d1104024485c500385108602c15000844503580008046074040c0c90401001d902c420785110802012644408180c81d1078213104c1a60314001064551002c01d51055000025030780c440b041040a000380282103d40003016000100d103061982e40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 778474766 1250 778473516 778473539
    0x150c190905060a05090d06020304060e0d091d13050d050a021b09041e0c060e0406060e0d0b0a14011d07080c071b170610050d05060c13030804150207060504 68
    0x9103c1d00501400085080e04d0380c0e22035000d46869584400305640d00c3c50a8a401d00240498280c0c4802d1032041700301207580c1e9401580c07800252208a035904001d00b0039022500044100074088a1410782014818000b04d6070600c0401c040d0300759900c0c4e242d914130a101c3e0080c9441f19411610749050380141c143c41c010368030b0080c030513003064000803450030014100481c1500c03005144002000011000310001e80c0942001071074204400072101089505c0e52440165101080d00d0300f03490748401001c2600300010300111034290003100c080b100182881550515006000081c0c1105054150304842e1031000c00c02d15180c1a80407400e803800c3e103e07078104101c148005010350b000051a441c1e4406070518140030f0b0603c0e2800801c1085216105c0510b5020341a464090503202e1401c40307403480b04003060504040b000d422080b607015004201a6803602d02c8509071b500102010203c0101d404400404261b83c1c0d009440034151038040c0700c00200c1c550101a203030510b180d0101e02032103400e00c02000440e81d44c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 778476016 1250 778474766 778474777
    0xc0207090e15060103020906071511030f073203042a12030e040501030812070f0c0605041b0602030a08010807030201050904020328090c0503150117150c19090506 71
    0xc01c0c0c2a0100d4903030a006801074040d4800c422340054001c1650400d028100303800711a00500c2c03403010001004000400346583c030046030b00107845d5454002082c0f402d44240e64a90200700b2800d40d0044411622200408080c6540d403040e8030035001100744800d02081d189201c4c0f241c0c40e1110348070350b1111911101901c0114500c50440124448641001450700454540640c454020401c114a6071207260465461708030641078400ca042010010342030b68080c03100d10403140210f03250100c60207080c0d9240000303400d005101f11580710346d145d025842c001542039010701174051754010b10b4a640c60035030700401103c016481848903510003401080542d130080d0848181c41000d6030301507580d41d40d04014540a0a061f10750312941821a070b00c00c50074a00da6031105451a104040e02c0d90b41603900c208065035945840440080700340302c00010003410807910540300041112034283d400004160701d8407070500388210784190702d450001481c001e40d01c3d142051401c40c21800c2c10b05001103800d1601158550082 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 778477266 1250 778476016 778476043
    0x3030301030317180303240f09060d050c060403030215090c061606020c2a06032502120f030a05010b070b0a0c03090813060f0918022a010c0207090e 65
    0x4a40204007404d920080314141e20100310216941c906240300c40c1c90740036000c1048110b541c44165000c019a24010700c05081d81400100080d099484000c01c01454482c510b034100c40502c1281501a010746912029100640c02074000c0d1078846503960350900344240050040780d05400002d00110150341d0402560030401031480302e21329070610713807804070028030448c0c10906081c8921510003001100342c0c0d03080d4405050405c8040780c0c42d80303000184001d900080d51821812030140c0b040002c141c00407000b0860320911841200c450124035001c0001d2548119103103200070000104009440c03c080c048c850041030300034551840c014440e11808028980a0207010f04551245d82d00001035101e0381001c50745640044041e40c0d24280d80c2102e40d400f9000d0704c103c0d80810f400d00300c1c500c0d540e030081211b401121031142c40019040f000f602d13160029403200820144403000d0010f00c510704141c96580141000907080002000c603000b00001e840c0440d01c0d40285416070070129040d40203e000b1403015034034036a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 778478516 1250 778477266 778477307
    0x120b090f063111030d0e06090d111801030c0605071a090f032a01200d1508030d1a1311040b0c0718090f0b04020a0b0324030303010303 59
    0x140362000040d2401001c440d0202e014203400c101c82403103142000808112822400c4030582d00360810183c42009061608a601000c04e0150440310704001c05a90100da104181d4003803e503103140f00240b030301045480c40d03600307240e800d10060042140304900000074200b14186942003240950343c003007142e0204000c00d00302200700b201050702c0b8a0200100c610f035034036410503280c541c94240c4920000058003140503000345050141c0780c0c182c48041c86500c0440d4607906c81c000c01a10712081201081d4000d00c4605005070b5910706410421001300c1485004c2c0034014041d41d52810600b03a0141074070501003031115646555060004607649204915540d0140c0c5080810300a24480311321081c0d001e0380c0e02c804e00d41e902c0001e0401048001044c0c1e40b05842c10041100c0c3c009025107003580c222180300c1002445901e02c2407254003c00c0780d525506510501c000e00e00303014a92240d00c04145500f040d1000c00710040d100490443c900c411040150034002d003680150705642c0741d920018070903500700720303806849107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 778479766 1250 778478516 778478551
    0x90f06051302090f040e010b090a0c02061b0c060403030606030c0201140615070605040605042a06050f0913050604230f130609030c17070b060405090102070c120b090f06 74
    0x4031102d1800703066510007001041164446c01c11a03000c0c0810f500400d00c03a81100d400260500000d09c5a2400303200c182e4001c2034290380e1690040c11110100c9070b5002849800d010905400a08110051040b13109607000b0a04a10f03140001c4e00360340b2061107180559042024100d22410403003501d0398010b008480039416010b013891092010302c20180064182800c000412080c003186401c01405940b0500343c40104e03000e0a0451455002c0b11000c095450910305402c1102c94810000740c035055500c00f040514006078400018400c3c40a40f8000e41426129010048586003502c110b40e0f00c030007071001c0d100014200c014540c1c00841d0003080550500103800204001c04600c02c0062540c580c041e408200d469514200030703044c04040c0340c00b2103540c0a40300c801d400840512080d1041d0a910180c0440f0503210182004080d0000410000d6550340c280700301400b00316120101c400600076103180382c004034a40d05151020213001441143c85034040e114080c0d4086002800302d2340f040342c808061a070078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 778481016 1250 778479766 778479769
    0xc020d08060f0a1a0c0601120f29090714270702010b12030d050c0903060604200715110a05041404021b030c1006230a081204090f0605130209 62
    0x55030660801c442d1024840b21340c12501ea483d07801081c080c48200d049400603aa12140c03410200003001c0010171200300c2d50801000180f11910a0090741d5032401c1814459254500460340020100c45090181d40034102c10000ca03d12100d5003044010159103400c0d0320006880101c00c07452400c0c4126941c400c201d400600e032503100303601450540d040100001051140030141550382c2c4c0084544c0c1d009a8070300b0000c82c100300c1c101c00c1251615400078000d880d80c0c3d80d94108120050070004000d1160154640b55920300d400780d0401054076038410007040691500741c440d01800c407070600c200030225220401c00402d03140d81080a40b82120403c030b16001d004174440000c03901030f0041c001101c40400c0300d12408800000c000c00a0b14000340008220780007d00d140329403c041d207406104010702c118025202e0280c0403d5105a80d02c0994058803126040da6038105040c0381c009c584500003805040405c050041d0707080b5004500794100c204c0000d0091609241c00601824007400500d00150360000e1100410f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 778482266 1250 778481016 778481029
    0xa0b0303040303020a11180a1515050406030e030c0a14070f0e01180603080a0f02120415110d050306010507060b0411090a090e030a110709090302100c020d08060f 71
    0x5000501566140c07a9685030296075035800c0c42c021070300111130080e0302806050062002001403a060038111017600c90b526000000c0202070302400030755040100c0070800f82d200c181c1040c05440d20b5a141a41c50f880c03c50020300b155061142210f4540041188501e001c00000d0701d0b01c03100f50004d0403010f0103803415044c10324024950b03001e20090505020005880710a41c0c2c1d445040311718440d02100c1641c01d07075041004075080707400001c242080030700214019610459058a0505450046032a148c1e10041c0280300341c0c000e544011800e0707603540301c460100c17981310b2003100180010100038460845100006441c5000003000c16040102c0841d01e40e00780040340d0403e1080c0000a40200301401c0694482e03c8035502041120f801001003010029400d5181e105002803030483c40f018504041682404690100c05c00003400c2c103901c144840030542800d54071444000600c00d0b001400350320364504c00501940c100440c000250b4010902502c580307900300c0400760303100d9006c55404038005800d8000414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 778483516 1250 778482266 778482281
    0x1d07030b1f020718150b0d021215040c020616081509150901081f02090105040806010b0309010b010302031608100f0803070c050a3b090109150b01050405090a 69
    0x110201d8101034600c075540c002ca00c100070340784008190740380e10010003080e00649040802850b08078210724020415a18940064006404444405407a00811401c0d42600c00d400b5a692400520715540081c03080ca8188114005400301e800500b8242ca401d00d484000c8000c052501428428241c0c00282220600a0b20602d03580b0010300c844294140f40014545102030f01d03500768000c40d049800800d07418800118000c00310f290a00e0107203c0c0c410f411004002e5080700303410505100c0d05200c0818900340030300c10903010301803004281c3e03143d14019010f2803c0d03c0c5e0580c0d903281414410024031100c82030f07500300515012142d0820b40c00035119012240c05805a0303078010b40300c8410580000c03542040100007041c40700d003c0d4418400c0e0b981c072081008500c04840c40740c41042c10308640c802c61142c0f84803207000124180c10f4014501d003003080d8500c4040710300440b04078440303964660705003041000341c650105c0c03520807014081080c0b120100c0041d00074804c500480d40f0403000c9c400052640038150b0030402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 778484766 1250 778483516 778483549
    0xb010905091501020d05090303270402070b0925140d0c15020c030d0509150c0a0b01050405100806150d020d0f1511070f02010e03150109061d07030b 65
    0x4901e86071881240820b60700a020580c0103000300102010914458401e50303039841401005940713862040c903c4420042c2c903084080c210504440d2035100c8507030b0350344040c00d12039004a1007001d40b072800c0c040361404d0603c0508481c440000300d900a0640b10101c075403600035519290503128152400074005004510403110080200209040104004030400116400b001b03170f5400315203000004604040c0c84407100886180003d0b0140030302d94092910074a000068000103901c039140c00348250031a0300b032914503075040c1c82500c00b80004218500740b501c11240e00a0408417411446810010010740b1741c200501100036041c0e10124000d926601c21b501c40d20803e074001c1214140c030314980781009100709802402e035154201030003601e8a0880f940542c0c140540d0ba00ca01500c0c10000703030780d00304540550352016810052600c6450000307403403c001d001a62050300c00d40b0441585003030b032201d0958805801c0101408101500c503040c94102c0380d1095000240e905012426100050100b4204c51361000c000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 778486016 1250 778484766 778484779
    0x70e120106050f04180b0c0d0219081e0c0a1205160f0c0b0c070c090f0e0f0a020a29041d10050904020904050102130303090f060c0b0a0b010905 63
    0x51512415030040c4200d90003658085540c8044504102c21030780440f555443c40e10001803003c00040202166640c00800b1030380326420849000204402c0307801c50040c00880400300308520605581082405602080c02074400781c3d612180491010103c1001e00302c03001c1c0d03260114560000f0f43c051503411903030303c0c030f031001c1003155181040c0f815100020f1041c42c1c001103400c80c212708903241d102e0040e8203641c030380007044940365451b1050031844540c0b18410568034020f802c04041094003403405aa601071480c0b100110358500e08440ca182044030f5100103e045a1041c506000180c4a12078400c007140c42d899101a00000d5040f40303101d28a22040c0c000c50808400a800714010702c811a21070014403070654403450b60b903210800101c000f03030315003d481e82c0070410b000002c005141410455901a20a80000d800c1251500300004900b00c1c0d43c008030003190004800b40105e5614003144d100030012454506030311059900c0b1080040000b03004000083d4590348514000c0e406451799000610025040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 778487266 1250 778486016 778486039
    0x1020d1d1909060f230f0603091501061d12010e0604030507141203040807230a05060c1207050d11040b0711010903030e01120e06040605040b100f050405070e 69
    0x10008040c510340a8080010710780f40d80401c0101441c3d040b04250781e10b003054402020000154030f01c02d0104041a550710408480b007040d1580c40d2240558080c269010040002c070082418234206180d0580100c01003102400706011610000c08156010050581c0c5403003513980c203135402d03030301400070100000e05501c030710411300042641c410010448980100f50152a40341d400e9030b09a100d01c4a5100c041d03c0741e10600205011842c203100401440744144490039601a00d60402c1007170802800720707011690007030301030303002130000a000a6034040c1000d0941482c00d003c540c103088507000c000d4010001c0100101d01c10424101c2d982c40f201d0044d0a90820741c1e115943e400d1f010300594070107601101e0b030803051410114035500400002c0d05403035040d15480d4941c0c040500444e031a0b1141d19440d00010384618000103113500c1400507501960044001090a00d898100a29050000b60500903c008040410414500300d00f0009055030403c5401151755100c101d801c6913108100c08500b0f6010b6900100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 778488516 1250 778487266 778487299
    0x12050c0405010c1104241e060e180907060f080105031b1518040e0609060a050c0909131e0b010905102c1b030402060a210f0b09040201020d1d 62
    0x2d554405562480c0e51106c050b4031030940d51300c04001d0b10203130500452a090305200c03250149031048103000c0060302200c182c94102030f2900d9944000c0d00d6903096908040024030541c1d40c44960b91ba4070b43c040e0700305041c95500d00300120380d40e11540008814020580c06214032a9600e21207040a00b100d00c2a845407a00d2186102606030640d10081c94407603407408403100440394011501510500c808400307030090303559801d101809403400030301c42c1c540c0c600c1c100092009542d590041d6801030110309801c030080c800c01d1501d10031800d034a69442081c219018650b0001a6420084070f0654540a01c08107140e16004170b48240d034051500000c00141d03101540721010500507040d400d10094150640015440d0044600b2102c401d04080007050801003002402508002c40104552480c0703290210510703030021080900700e064050030800307072520740031211002c003110301940030000310803550a134407030900b42c0c0040c1d520942011b03000d0920108902001c401090340c1441208080e01900e2080681d01510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 778489766 1250 778488516 778488551
    0x417010e0d0f0e0a03030e01030f2003012c070c05010b180604051006020c0f06090306011212050f0715110a0306080f0304050a0605030c040902070c0612050c0405010c1104 75
    0x10030401c0003c080c8407036003c4034a0103c840d40200c80c0c1580740c1c0b2000c038041030300450151560301c10829002e44c8511150440070720000c2d6000c0c003400c80324080c9481e5418505282c3c031000c0c4031000c200c103c940740f031107002c080f51120213941e40002650420440c1584030745401805808480c6004d80d0003000c02d110b17600f4041e00310307912920138101144d082166a031181c0d80072aa00c16903006050040c0c0c0812168120307810b050302e62101d801001400c43c2d0074090030600107803510070260801c050b00c00c0c60741402802c00c481c05140140440480c1440340c20b2540c0410000d40720b004280014000501c0c50001d10042d00840e031158000c070584861540d0b03101c1c084000507014001d644100301c0c00384509140812951004401d80c0d003a20001442d0b400610300c2c040c0c0403242c64001800b0507403021000c0000240e100e400c2c0c4010907100d4031580409044502d0700e84050058600c3e155a518085e041204100d10f540d440e00880701940c2090a0890104a180c1030100070f02c9001500035030481c0c50548000c0c081e19104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 778491016 1250 778489766 778489787
    0x10200106080c092a0d0509010e0d0f020109060501060c12090506120c0d09030e100c112707120b060a0804140a0f051b03120f030a180b040302011109060417010e0d 71
    0x7140c10300180e187c5403891422101700c640b40045a40000700d50001c1140300d0320501291420620001c00c240c46991a200200c41703007030748240e01040d41c2900003401c110b03044041810f01c0c046030500880310703031500010841c07074490100b0752241303011154001060044604240ca060900c40241084155224900980b002d0ba0078030794035120b8214412051030280c4a686030190850380400540e40c0c1c814500140040c000b80e255018000c1c08842400d10701e14540d0310100762141881c2d5941140d0b500102403010f0071900040000c0340910000c00940549503000b16000b9042075200c0c401e00c0b219119140120f05001401c44014149403a01c1c240350144840000c00101c0c41040c2440d40701e0204014040561380c682104d8601101c94082c0003900489003039030090b65102c00900d001141000c89800894207032503070828101c4d403181003641440245642485001c2800c110305010a1501102c040025514044d5110b9081041c10240e80341050184c2074204107001580f0720101c51030800c902038040c0454882 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 778492266 1250 778491016 778491037
    0x51b150106081825121113050601020a030c030e030304181a1516080f0c0c0a06020709090c1d041a0c0901180510200106080c092a 57
    0x10703a8082400c0503844190a1401c01490340248695081c500140d6120206a80040301009142400280d40b01709115241c0301e45114130b1445c1c401e041d41c02d04000c001740180c000044100c0c03a10301005281c0e40c000401c944441c2e01030a00d6040820545000c4410510218800c0e41500020400040714800c04030799500e051004681813020102488d140c480062060000981c03002141883c207629140300d500030022210106100f040c2e40006480d2a0560b40c40090024043d070700000e0b618a0865082c8218914600222031b960401c07860304400940e10711147c001c00340d015594029074000c0240f400ca03000020881a44400c80780c1c0207410050f988103404450032fa848004c0350b028000c9800c4441410b0b4491401c07035010b2410f01c441030004480b0400caa110620900c060341c02c003c101d50740c4640350384240100e82e03695408108298960307078004c006140140500b6a04240c1d040c0421280071540708090302058030607075040d81d2060841c26036001520112b4030945903040c0b480c44040a441d0062030a9081c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 778493516 1250 778492266 778492277
    0x1e11012a02010e0613241404020325050103020a0e100207051801051c02030c040f020c0f0303040803010621111e03090a241b140a02030406051b150106 66
    0x28080f1102d0319010100c60304001640040041400200e0b854001403543e181c2001207075445480710190022244102c0c0e40b00245030380c1100308821450100142d00340c00d0191111145c502100200c98a0b803039000d4010300c3d043c9600822409800b910403c080c224030342004200780b070340d03234403940010b0748402050040d680115449142c0b1808041d00c2d000c0c840c102c80019110700010300c2c0045522407251031001c0c007240d041c090f24507000703110b0ba21070180c0f5910740650500180d45007030401c4a81c0c03600d0b016a503e46030541003441000081388900044c1c0381105d50030b0030290f2010f0011400c40b11240c40c00200500303054984030035264110070a0b4050112141c1084412124001c0c0d04403d000e03601048512072120303170003050b10500140a400c0007a04d8515203000c2c00300e04201900d43c10081c1d81c5104241400b2504c149900842c40e44c4c483d61403110014404481850103024010080d00c0e0300c00c1d0302901c07013130003800284081080d03450350b4850642c4030703482c050304c444e40300c41102d086030107000384581800102c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 778494766 1250 778493516 778493531
    0x90203060f0406050708070509040f0b131401050d02030a020f0312030c040f05040509030a0e0301110f070c0e19050c040b0403060b010206091c26010e04060c1e11012a0201 75
    0x90040d269031f4001c101c1c980310b190820065008000141000001c44042c0c9600e03260340c1300b003a4032411820075500e000030308046800e001211808451510503880700b0710074806248600c002d03031800316640341d244e50140c41c4180101200340c00b0a140030030203920f64a07094400010083e0740c0350360348054402d6a9010710b50b0071885903950100003d075a800d8500e00d03480d03042013043c9094030f0f00915080300e04c9000030700082029075044520031281c1d0020380c0c4000244500003100d0701001002e42c21540500402c40c011a541d04025440064145a401300345a40070340d20008035420580500c1a01c000344089030401c1e0fa195140e142907000703400d00e42d4901e03002d48204404140485000f0440d00d0100039040e20741801c042180108807034045000c010164000310011528481603500c2d03810a007e0440b02c0d44060140c209403400e00304440d8803010800030014910306001190715403103241c10054100f0300d019520715201c0602d603401800008150714018075505007132491042e49454030b540030a1250001c20562 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 778496016 1250 778494766 778494781
    0x90c0f27100f050a14040b0c060121140a080a1205060a0305060c1b0d08070206010603090b07050d0b030109030305100608090c061605030f0d0b0d1a0a090203060f040605 74
    0x407580c0d400c10000c115440c44000d00786219802408440d00a0314002d40b16007400401e6040d0381d44260014950000c00040a022403181044041d0040101e844000600342146c8100d820000d2810001010f1802059401c0000c200801c4214a07160b041152590785524010014094081d81d5440040071030514000610a01d003501a820890b0303044406004980d030382000f800e61a50101d480d018400d400199082c156810400c804910106103485190355411b01e1140603140510581c0018105800c040358040010102c2800d560420443e081540e11f41d50300320440409807400740003098040d8680a14407080c1641504014080c0c024292201403ca403640800c4a82c003000b00ca5402846c0e001d0007990016007452802003401401c0f4484d4045082c22980d03889003154031102008840c1d00c030124000304404064440e01ca04a0b0080b02c0c0a402001e0b56640c94084000714105c45404107103d200046003100a6003207200030581c018141d0303445280030360760341000d100180c03000d4400b0780c0740c403000903a034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 778497266 1250 778496016 778496029
    0x60e090601030e0d0305072703030201270803041e060f0c020a03020601050d0201020c030d2309010c0209180a0311010c030608071505040306050c09130203070509090c0f27 75
    0xc2d0900090400c160b21354a050f07010304000b03401001006440b21414444c40c03e061500c1c01d0115500406800c124518103000b802d480042c006494200c4629a0345803084c0810f020b4161066409182d2948030f41c0c9905042080c0d1200b403c22100b42815004110100711450344151103c042d1500c0401001c078584000301e80c0c1c0c51304182c009016038010b10041c08180b07018002e01c400c0d40d10510484044a548070042800c01d082d81d1a0100410810840e88100301680201d0442001c2c04003400b41c184400c2d0710009107c524985d002a0203030380076a000c03408550040214081a500d40c0c0e048400800e2145030041481e640c04650700302c19481d20000c01d1a80e0f1080c000c007000c5446507001488401d080918005100304003c10b00400d200c0200305c0040011218018030340b0518560407055111001482880808801031884800c00c40c030410801510030b4000080c0d5201e05001e0f01c1c0f005903a07031100448903071413003a069a003100d84030210b00541030030043c4080050b402c64201c14000c0d126554001c1c80300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 778498516 1250 778497266 778497281
    0x9080a020709110d0e0a1b0603110720010c06150905011a07140322210804090b1503150a0905010b0a03050a2406020706020601150e010507080301060e09060103 70
    0x55081004400d02c068061741003030070000a4101a1030409200d41c1e2003118908006a42c4c000350302458104105503601446104809441550b0a503e001c080d665034180e010016075082c10440004110240741c0d920902c1c0c601d45442d07002e8002c001c00003030311003c40034801d2584074001c1220308160012a00704568092603000301d500c101c0003801c1c40d003103a450100100140001580c2d030b20081c0b01010720901c2c40710344007403500d80340650302ca40e01d400d1440b100558040c4032a0055000440c0e12108001490302044604840006c0c1001403144d03115000141e61900502400f65002000b0080c460040040d140510300e41c08112681c4440659500e90074066a60910451481080030b024452010b4060342007241e00c001c10820000f4aa29016040381d0240341c2d1002100014906290600803140c0411804015207802d00080240f0341c580411802001c5141e828041000004420187c00382d00850507101041d034000541e5841e03603161139000708420711303407c5e1840c451505c003004241d0700c2d40a0300ca05070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 778499766 1250 778498516 778498541
    0x201b1006180e030f0708120f070801090b09010303031509090507051f0509010309020a030b09010b100c0b040f080408120c011d0c19080f0a0c0911040e150409080a020709 74
    0x6003481044c440090503030704904400c4e2800c0304100316041000050040d8984a100c03282ca4480b00d600340311400800c400030580002c80326926040c13695526603035440a03141100e40c10718010945c40040304030000b1a0100313034042c40509040005400c00c109021508606448041c2c68840440e95017040d24402c84007200c1d44240850400c01809a66510a03049100c100703001502c880921541d9a232201303440c90003151b004405035034946001000c1d00c1d1141c03000040030301502d084500c26051b0788039440504070207003005191500182f290401c001d00c00007510000c1a801051742e010300a1f460350301e1140c0d8071840d80f64206510b0b04180020000c680c44080204569450081424036004002d00011065048150900001461001410100422a400c00c4006100c0504801141c3d440c000841c4215600720100da1801c240c081642d0b440c00209460841c0e49980c180b0543c0d0301c84400110b107038110450354607085400c100c400d0045c804900c0060800c0805035080311031713290791480158111a103140520 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 778501016 1250 778499766 778499773
    0x7051e060105010917070312081e0c16060e151609060e060306010207090e0106051f08040312090b040308040203211b0c0402040e1801201b1006180e 65
    0x41c091241c1810240442039417900c212038050380c43e603c581050300840c4400300c000400203010402d11881ea010f0700c64084840e07003549174203810030488920090189000c004081c94100ea40c501c14440c8580204542428502c01d9036400c02d04a400c08035494030885001070714441c055030007c2d202d4450740001007100c90f10794540140103001410080307694005801203046208260000c00c40c4120303807083c401040074501c00040c2c00d501e0b00040c80340d000405e02c590101410710066040b411904080d00c140d02c030f45d00d8940044404000b00200008001002c80502261480002c1004042c4c0103201d0600560085003241c01c40c8a10700da0004a65402c0e07d41c902061301d0030b210000c0181d0110031100c0101c950002915078503070448002c64100d802c55400f00312024042818040c00740400c04802d51507000800c0280140c100104010281a81c1503803043c40110002800310840314010001c0260940c0c41400e864281c11010804c101038022801030198110325085148048402481000d4001c0861000b4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 778502266 1250 778501016 778501019
    0xa030f080909150108361c0908120a090806010e0103060b0d1101050306030f03030a0203100e010308091905060a0804060e0d2021130e280b040207051e0601050109 71
    0x103640700d01c4402030300d22500c0100240c14204480c10700807454503444a01c00407ca0306049400c0c2c002d03440901000c00e001d101d000a020b004050010500e10707011490001129510914400122a800c1e102c3e40900c0c1d01ccc0c0600c0f0b00104a540f001e0b02030a040302d0144a050183c0180441000f441b076140050040103504180e94401003035000c0c0d8041c580c80782c00181030f1914441080318150071a0320450301c1c50380d9181d001041110303d40c11590140084d16500d4922205581940d96030141481806401031040d450360a85c9041d0f40f04030600b0002030308004c0c0016403038400c2d070000688208020b80781162441e040107451a102500000c07400c00c802401e56826507606048984ac400d0700c00300ca010708006004030300c0f660001703490700d20310f6404410b4600c050340d1703a07074207020461040382101d90414082c10a080082c42515454030740490b03450851606840c55100301c803950140180026450150030900220b0200140000810100304021104444d801d6603c00c03c0d0710992104000d00885000c00e088400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 778503516 1250 778502266 778502281
    0x403090e0906060d050c040c0c02100305040b0112060f02070b0f09010b0a050103050a021b0a05100624020c0a1403010f06030b0f0405123006060f07020a030f080909150108 75
    0x80d40740c4c1c03040c00352042e144802d41c4000030409032030b0100c0c2c0890200384690141400c50415003056090081603140800c981d04050b40c40810410041c802c05410b02d02806000042c41400d40c0701d074001400c902d00855590080b441d1038031040c7c10445540410581c580d0006084610600907a2100100200400c502c01c0c02c25006500421015052500c01542403241c0c4c0f0076026000300004001c06010300078411945036107401c51a0030301554510301800e040200800c0035501012102c41807058424450004100a51089103031100b16518258400e2030345500191804842c401c405c810007044d0000d003d01001d249410341500d545100040102076510000b50341c0801e601c004a804c103104400b41c545015000c00c2c0c440b01500071409003165018464406c0003180e400441d040c80d440031051080f581c6241010002d446030084100400180c030700000d8103421035940c0c20340000515840618080e03500c0507818004000d0b003040c2400d501680c0c0903004685106078009400c174031114141d440b1308056481340c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 778504766 1250 778503516 778503529
    0x2031e06151c090c030305072001020a1101020a15050a0b010e0f06070807050604031205010801180b0c040924120c030809010e06031503011a0a0b0c0c030a0303050403090e090606 78
    0x1503034200b082e0741ca014078000111107244d02001180665104c40e11402603003882ca0b0105500e055100c0740c0c40105408000d2640c01144d5520081e40010340450b00c00b00ea000140c1c18810704440080c801420318075142c00c60742c11a8001070044403040f0082109508000040d1644040600401c0d4001640140c50b511840c0c400001d24220b0f100d07010f03003810401c2070b94425140500c140e6003140460032002880c1c107c0c04840c807807140100301a00080c09842d0319050a110560b641150140882e0158000030b41d56000400458000300a070043c100600416542440c8010704102d0f42c1420352150041c00080311101c3c0c44004036520340010000050300d1a41c3d0712900c072540980d9806044c0800e121200345c0540d078001c051441452508114450711944404260031640d00d02c2c006122840007000f00a0582c40e0044200280e41e4842107903555400030400d03140c0703041002c00300b4076403621a07040018101681600210f014910a840d010703000c1e600e4900e0701281080c119002c0c625940300c000000d00e0341c42c200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 778506016 1250 778504766 778504807
    0x3060d030c020607051005150d2315090f060601050a050c0c0409140f060108120c2e05060a122604091d06040b0619050402031e0615 58
    0x9041c0300c6145192a408608107030460001a02c41e6000403c1105086c0c0a40c01400d51240940003901c1d500c060141c0000c04114014102400e07094100480e5070502c4410350100c00901340c2e24007113924111b080403841c00b01c0309003103481d40d802d8011080c2c40303900c40100082c8580102416101c143c203005401108990581200ca003145140c81141f40155540c1c4851083c0354038030380a20468110700c10b10700425480c1118800b84a202503100c040100032509001c150740340e040030801072185c0d40d000d10620151500c0c500ca4502c1004240115118940b0b031441903982d00220f120003428401c41d07540804000342070929200d0038400300103070590000000c00e0008240000481512200d6541c03d050301501c545400580000a8030b40e03640e4004035901410000c802c2440c20804010242841c1550b5101001100035010601680f060394000324250507210020b4042c14024204544a1515080e10f00748c000750102e10007a402004c04c0820921308000c0c00c0c20f241d842450624134a0701e22094415480d18000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 778507266 1250 778506016 778506023
    0xb030f06130336051c1101051c0608061f0803030a090501150305160b0f22150329010f12090c090603020301050f040c15030906020304050706090603090803060d 70
    0x280500480140c5164100f81102100003080c41200c90600d810b01c40111010f1091641240c0a0160311002400303468141c2d19104003880c00740e8647c103081c1a1814520040403500401070704024000c2084d1400280c580e210318001c81a10140d80e0720003c5ca0f8050b0b20803806042801c0e08104002803120b149a004020541c0c800c800010743c40e6042d0500c4581080c080d00101d90a401814502204c81c240034001805080d85031b2800346031130307c0d561884010388102414500140b020001c21604da000c0c0b03481d54002810620320f0b5407003041103241c000b00100162031060340c7c00d50075020500d1940b10400300e40c42d070740c600685946083c501007280a46005440c2d41c4403c0c2241c0d283c0e41401d000415540c01c1c24001c01ca260001300e4072904520406081d02d60040a103580881080100000b081140038560126440d9410310725190702c42000c00c401078140f8400280c05a800041800100640011202c0c21240c1554403602d030151241000c0f0261050000701424145051000c41c1c00ba1418040c80c000c414403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 778508516 1250 778507266 778507307
    0x18060f0609090c090306051e07090503060a0f18030c1505060303270d030306090b030d0c080d06030f08070c32030f01050403080a05090a0b16030f0f0b030f061303 71
    0x917241da515081e15001c47c2c01c40c0e00b289a00504641404007550000d8101d805420100080c80c200307070103c1e5079010000c104170302c916240c1c464542100c2503076003c8402e01c3d501c081801040e403240c0c18054850490020101c5d41c600f000e00341074070b07219980d214140c018100100a5881c00e00910103000c404d90031042c000031014100da070f0507007042d41c1c2c050f01c86100c2d500c42d480c0420680e203000030020480b0441420103019070401c00d01c00300e94a511800c0501b00341d6101203516110f003c4552207000034000d5410082c603211990319103038240b103c00c0c4007800f0454841c540482e6066250044c0708a0309090001420103007155404d42000c0324040c04d03140540303110250031242e1000c10194590700b5104165401e4000c00d12800c148099606c4034020301e58424442402041c05030010343d40c2d42c10036407005188100409007140e1051042e4802c1c2c01561100a001c90180442080c01d83d9a40c01402410200d6200b449001c0001094180c0410382510401084c0031410341d10304152401d44101b8002e081d030502c0c104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 778509766 1250 778508516 778508519
    0xc0203010b0909010b030f07060f05070501060b0d090203102018030a0309170705060d0c030902032b0908030306040b01110a0f11180c0a090f18060f0609090c09 70
    0x442d00204240325042c48400441c01e50b02d4681494100301464100c1d1500f600070306400c0c00242e41181016070510040c2c50030b10350322417031402c10718018000c0e6044042d1421001408103466070640d0480c250860007102034030085089004940c003118a414919400340307000885e003000c940b0750b0001420101003152400004041c070007000a0400c0e0b05400100c021829041040c0304003000c11461459560300c0d607004140282c14100011a50f02407203215448007030301c41c0c141811181c0300e80c008546096002c0e08490b000b020805800e0503000c0014650070004d03600c81343d0703654a64444d001d008221a240030113189540c403810b09000241c420f000a582c1809001904038070700a00420a1f100b0300360181002d40c004010300d107814001d11501c0c00c14148070312184103810710740501541203644c000c111100400d0f90307582c0216054503079540d0340d40075040c4000b0519000600241046003070a00480c031213800c01c1465126007140e000300780d5500400d00000e4203044140b01d400f806611400e10401c0e135041c03404041d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 778511016 1250 778509766 778509769
    0x10050c07270f05010305120a050306040c0c2301180305220f08060f07050c0c0f1906020c03120703020601090f110a0e09070f0212070606170a0c051509010c0203010b 72
    0x102c4401860080c25075441d0300410600205200b89036603000c540521a03c1e05d104401d004103c0d0101a0090744925994038110103540d004126400d035140c0c1c8140c0c1661030140300c1c0b484001c440445044c0312629400d0101c03e0803d1280740082d5030700c490341500e5150400e8070280c1c820141035641c0080b03124450001b078004c00c0e1506503400e000b0083c041540140410720308204012034445000c0c14102c18050240326a400704034010442007940d840c142c1d80c2c2e41040411900003980e0304030034030b41c150b00c855007404003045490340401c201d65a0181034003180c2d10b4105c490501e0440d40304001010b801030300140c0051106141941029150380c070040008030f48104a9030751840300d40c0c840c5402202150001001e10001c1c201010202d40c40300c928101180c4240c80b6160203506e44501c007641135143d6a0015844040111540c000405000c0c00324011a100302c1200e08655101408203059412200079100041c2a1a041041d2990b090031016900d0070b1a001c01d0056030040030b4004102d1303041d501d07010440e015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 778512266 1250 778511016 778511021
    0x10828060e090a1407050604090506012001140108151803041e140406080d0c080c0f06010501021905030d020d0b0d03050406090515090607022103040510050c0727 71
    0x10b0700d001800fa010031801840d0074100d000580c01c543d24190840381e0200016507c1e0000d40c0c044840c10440418203590760401201d80f0035010400d04041d401c900c41c0c804c00e5190545c4400c16203910405400007070b07604c0e040c030070b59109000f140324600c5440316170001d0281c0c00c0000b00c00c042c41003200105ca09240d00c03400410030701c060340902031700d141518110401016000c00301c04070503044151010030089080c0740c801903c0d40e41c40c0045c0010300100d10714490070086250304548024041d0750503a140a501407041c607884140a104003030052107501140f07090140c0030391000304400c3e8094011032030104400301c40b82c00780d0003c6000d641039658980000100d5100c00c049041c55501c80e640346940e443c01c01001402d030505030f8000074014904007448120360624441100d03030300e034800ca6490b038403903044e440011010708012941040303180020500e1012061700001907c1a140100e500b80d000e500c41c40e07000c0f0b81c14028003070420318540c80344804200400c2c0c29200c2c4852004101c0450381ea40c401d40d500702c1d09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 778513516 1250 778512266 778512271
    0x905150108030310060813240f0b10111b010e090f06091806040611040f06020604061d0607180915050f060405010212030a06180207030806010828060e 66
    0x801d6040002080421581416640054000390400d20b100b82449000302c51b1404520740c000f0a40c103024062a08400c404038540c07008098040d9090092101d40c0fa0600050003507040360600490300e000300c0081c03260090303e0800398141c2d07840c002c1584c14040c603c002c9415200362611814440d221034070500d141c681c0c2c660544075060b080350303c183c00d045c03074800d108d0b5005004080b00c22003885090040080980400d1342600107401c41c40100341d200b901d411401280c812130b440340c13041070742084e00080d0709a000f0418502c16030144100b04801540c8080b6017052910310380c500281900200c0001e900702e405a0050150700f080c041120740d03500e0711030900c5411113241e148001c10b11040b10318200417520380f441d22505d9052003603c0c003c4c02c051402c00003035907840060b400500b1807000800045c25039030144d406040203081e105505424200c0c0841000006c0d40008400d40001d0705410003d4099401340901078020146404046000824001600c9010085406002c1d0480d224a400a1641c0545e08941e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 778514766 1250 778513516 778513529
    0x913020927041230180b0429060913050d2016060c051f0218030d02031b031b070f061103071124040807080c1309051501 53
    0x8141010306044441400140107030040121464040031101c001000c07030103113a055900b203000f003450b021011102422041c0701840303004145085070380070b01c501d040b5400e0040e800382d070b070307110030b40c0305110030041e40c5243c00d04400181c14105020a29600744510225031044082c200c510314128030f0342e80c2505003090010a480040c140034207604030040800915814291620010444a6003030001003072041030510504040c040c003c0240420701c5070030702c0300c101070b4440e0343c45070780d105908005500003e4005030408040c1196100a18000c0d0900140803203010f480c9400643c14070f09000400d2818492035941c04404c1e000a100404245411444550204401034041d244480c1400484610900711754048400c0100446c0c00f8441418003108071084650801031a001314400500891403240703041e0740803406250030301120451400c80c1c0001d801500c1c2484162103040d1b40e40d010055861b04074080b115440140d100501c0b86d02d826560000520030f102d0341c1540d4890411403004401c00809a200d075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 778516016 1250 778514766 778514839
    0x20a0f03020307380609060d050307060f1a01030b090129070803041a2a0c0d02010f0e1f05100302030a050a050709140f0c04050a120b0106030209130209 67
    0x100e0495800380c00a13561404030044201031030035900203140e042c0301a040b01c6c055a0000000014018140211140c85801000520820004d40d46410060031002840d0401c500320000c4825990b100b0b0050085203107004180010690a1012001004400d101d0301c0c0080c0070411003200e2880400f1000d0020503005520564603440c007814030340c00c40c180006440c8842a034120800814110901d5070800b203a02802001c5440365061011841e18410346009202910407103501c0110554150000403102030444418803100c41901101071b680c00100d68122812140741154020384003030340e0701c880d500c00b10344130410400c2c5940780c0100c0e00300b00f031801c2c095985400c07050043e418401e040003150004d01c2c0e401810003620008000031100c002014200318585002000071840c0c20b190312040e00e000c0c01d00246010381640c0d0307031001d615480041074000ca400300d40d02000002c8460081c400e031010b40901900d203500460341c80d20003d0095003d5041e003070f4000e01088030a602c80c1101c100c090901031020909 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 778517266 1250 778516016 778516073
    0x1309030e0a0603050112061107022d100e010309061b0f090e010e0c09040f050112061a010503010b0a0c0f060203011806180207030311030405060106080f0403020a0f03020307 76
    0xd00074100081c2d0403250900d400d210041209141e10200103501941103140080c890312030040010b003904c074850010b544101c00b50f46480e075605182643c11982c2200c41c41c19050541944240f140c41c200551045010a0700e0420342d640301d500175044103403440c4c8a0b260011f9480c10b81049400d81012068407100000c44443c4104082500224648041e1401409280096140c0b0041006c03200008100d0908120f0100e5030040c1622260405e10346595001c009000c590384508207000345030741c0041c040c2c55003428140c9002c0d465503103496010741200c0603902c0a14507801d083c960001c95211468400401032a1203d200104000b4030100d90418070910015030380f5458005000780544116000440040c9090001c00040c41c1001949400c0c0801c0100582c4820702410f055004244041c0e82c1039054000200300700c100100400c0d114103072000c9403144402a1074058441d241d03500102c0380100980c0c000c030840d00100310001c00c1d004250348280b04407071424903285e0ba00011000c410a5425040e9200d40c007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 778518516 1250 778517266 778517269
    0x30303040b070210020f0a0c15091119030b0105010c14070f0501140a08010620030403150c1b0b041518030807020a08070204150308070803010e250e1309030e 69
    0xc0560407800da000c1d410883e1241083e581445402221006d0000c41a40c001c100107130300082109c801075010040110b400642040e0030321006600300984640c609641c01400b01c00004d200317900f80d0340c114036400c0c40ca0303083c00010758500071840c80a882e994004840354041010400c00c1401900541c0c40041c0c50910300400076007103c043c0d01034a420000180700c1c0320303556580034806604454242c507280d28800413900c081e11000794003030b4410100b40800070f004030606c80070342c040319461903188100708030446004c5411100521700301307180d000880360000600086a59410504c0c1c200b8091481c54010403840007450088840403440340c80f901c5e180c00201824140c20965107680440580050f1086a0352959000391038403448800074070495807003e21030747c10103100f015580555801141c890741d9a52900b0f1424032a0400d00c076118039580c0d0440014000c41e4540141840746041d559050f140340c0c0900f80c00c0d03a00380b9414000c030341c0041e5110240141901d039030040304801c1d1b02a48440c034031000c4100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 778519766 1250 778518516 778518523
    0x30c09020c191121150403090801141905070c1416060c0317060d0f0c0b030c0c0d05070b0a0905160b040e0c040f0b0c070e1602010b01080c0d0e0c030303040b0702 71
    0xd02070300c0700d901074910103440800003003241d01989080c117010300c0c5156110700d41035a2a03101600600d240398a4584001408007000c440c960082503140800d01c000c0356100350010541e8400c40e003a03000207841c1c1d0310400004006850329000e280d150310603102c0702a81c07950451004507030355002c000000c1c800c2201200f45a045440200c011400c0c0003001c566240c96800b2800d1104500c000801d6255074102d81070a020203140b4400103095210f2140e0398904104080700c0141d0030601e4000403e00400c1020541c00f4024021651190761100541111380d5806010344002d01c51418142c5490140c100302e1030b0100400f501c421f001c0e00841d2400364a45051a03c00c44140c88010070700780740114104003d101c80350314400c614089031160b29106540d031115034000d03814001c090f4401840f0f83e0000050010350820803e00b441c0140c1183c0c001c0211a4a08e001100c003420103403130016840c0c10401c515000f0881641001a9000c0c0b42d0044940560700d410102c0e04e941e2049806880781524513090242c80c50f03051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 778521016 1250 778519766 778519789
    0x40605070906090611070e01090603120c020102070509040602070506190b22051008010e0d14070f0b06010908030315010305011d15010c1202070504060f030c09020c1911 74
    0x40c50100c1040e41802c03000351080c2d4580c000c40c800e10801035421244690100001c030098050b12080e0300d2596581e41d13941014101500049481d81d514203040605140701d0750415926980507401085400c3c034040c10303c03034511400f400581c3d843c1d4003002404041002001740c940217079941e00301410074402c11a008001c544400c03a642c2c1c451440c5112508042001104007c2c001d60300001c00141c9480e1421441882c09850b4042c0c1003135402d01c01c00446c130440c003113016180e612980d00e51009441c1c86403950f8a56101e42d910052500283c05034074400305100000d21a44404103040460301580c07154521890740c1c108542502002e51440800d00700c03941d25016080c01402c280400405020200e91700b55103440c0000c003002e035040169070205015a101c0c04100714034540101c111050039402c0840203480e00d003140285805941090400a00b0b0700381400c2d42d008898005140010260510040034080e5210704440300040c800c010200e038014030301584000b40036104001c511900c210311800d01c04030300c150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 778522266 1250 778521016 778521031
    0x122109160515030103060c0203071b050a09020f07030309050309030318040c0801150516080301090f0608190f0503090402120108060a0213060e12010c1710030c05011211030f040605 79
    0x31900c42d01820050b142a2815254003030b80200701c3e902c00318022851030041882c080c048c445c1c88c01c034460102e10780d00c540d802039440030345408462907150032100702640b040702d4040c04841d80411101c804288658810700707072a441002034074504a0703010300207491500014510042c1900914141d5080d00e005c1c40780f600c0b03016540c10320b03240c1c0790700d40b04203901c603070400c1810001407050020744500000b000c88903100c04142d020780d03980d4036075854030140d0000744492100e10075010316148012620000c009a0f20170184024114030710919295030364540814089c02c012a0148014005a19290f4450010b014060940c8031442c0c900d62600100c03030b03e40038015000740030040c03041010301c1000343c030b0360f82d46000e070707001800c0080d10311205c100480e6000503c1c1d10f03010307050b518100110400640c0703c05461904000801302c0d84850b111083c81c150860685c3c440140340c0c04801408100950081d2950241c101e002d10f070000c0c80450002c25819907500031038031039001501001c00c1008103c1140310b52500802d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 778523516 1250 778522266 778522279
    0x12090308040b0406020f0c030d1211210901110f0a11030d020a120501030b012309090d0f02031c050919110117061806041503060c080610021221091605 66
    0x80002c89c1e205d101c400b90510400400c1580844290402c4d0010f0610b580e25842c0242c0d0391040d01c40032000e0b422aa0404030107100d492001c01d541803014003540c40c2ca94001c0074603070b00c0c1202003806c01805921154981c0c0900807106c2201840c0782050005c0c2030405c1c040e190150383c915503034000a100d0320b8820290711003545010010310200300ca9543c2941034444803c8003659074809140e10305045203059414561069920b03007086450038012403100b4a00304103807150608041813803400c1c0d03240c3c005c0e840e1440d100c101800d01c03545d802c003031030700441e800200d40c40560ba070448852035615110f210300c0c102552461210201d1720740c00d50348036000b09107880c45802141c045041141c0021402410245000080c40d5404040b6030380d85d0301c591004240e14908506200d415540f0700e4118080e003400c0d00f86001186040c000108a03051018039003042d000396a01625403802c2c28400314100ea0000010301ca500e00001d0350300803007658044111130195501600808074284081d1500c00d80c0324554000c24002c00c3d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 778524766 1250 778523516 778523533
    0x303020111030702031c0b130e0f010b0904151116030f140a0f030f14010e070513120320010b12030a0e0d1403040b0a0f051612090308040b0406020f 65
    0x80d8007105031445d0603600007511b000c4240040010b0050008203421740d50012800281d54014425940208a025900800e91b6012042200031900302d0348c441c0c04e216089105140001c001035080080c0460050a5000c000781c07000c1e451200c0340e125006143e9880130b0340c9241001c0014140c02ca5060b480010880c0360404480b41106600f8241d40200d4031008107024120411482081c081e07082000c9814000c20304101c195505143c8504025084c0f00350030780d0240030070104010398400c40840e07200c8804403110300c100c5480e2080740034506e0b2035202c0030b4040204002e407203d4082001e00a00d2146070001f4004541c0783c214008000e0000e2a481c1c0d200072030350007004902c40301c9030072441c0c2c058005021903120030444d01e00c1c20014038203201c00b1441c00d11804002004101d18170800081d107100760303840ea03ea12001c0c25824003a81d841c4618103141219034000c494081c00608981c641034200082e43c0f50100d44e030340c1e599490300e100d50070a13000b500c01c43c1c0021609212166040052407540840d081c014940076 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 778526016 1250 778524766 778524781
    0xd08060f061b070503161805100510030204150806010206071e05130504141e040f11040e0a050f0c061305060c0f03070b0703052401030231030302011103 67
    0x40c420220490910b040c001c4800b4260034003072101100805014040d100341c510800d00c80721180ba00d034010018240d000d00d24035101c0d40d401e4400d0602c104252010112101d040c0f9042080c5c0180d06000d100800d6000c0001061017004a65140345412440d00c9604490901e8070002e414124010030890400c1b6004440f400a05010130381c035001c1c881c460506660f01e04425003800c0b003611580d000351741c210f41030031100400808000240b600c10f007807207a0b42c030785034a0171020383d0b00e40060151030250101101e40550700100d17184003c5141e4640c002003000a40300b54400390342c1e00303100c0703174400644a03a00301c00040320108100303029800b5103220441d0400d2801042081044001c1914000c41d8011100030814691142003004100d4824602c0401c80307455010724a0403c000324021504000024180404183c60300c5007409140c1c00c00c52078482030007060321f440c001103009400c58140111101240007035070a1070060000c0030812a160384d161010418298200642540c146901d14859000d08004100d44c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 778527266 1250 778526016 778526029
    0x7020108040210030e070e04060c02371b030201020118020102060a090807050f0d032016020604090612120903051b0d21020f07140f030307050d020d08060f 68
    0x10a604aa11031185144140708600404840b102c4440034402c94001041c495444410382348120b00c1400248041951110200c0e00da61700f03051043e0032a105248105501042230220140200c00002126a608480d880d0041350302000d01c81a0300150051500f40190b5a082c06508103604211000744d4582441da80000d6845900418814003665912103800400900c0310494014641203001c40d4482c404000c0d007030303481c0c00900712001e01182c54202c018003046014000429890f07403040d03501d0305000c0c0054148918440c000d2040340e12003420800403606680c24401c5001815104050005c0d813410303844d2a0700b03c8a079021322071041c8038400300104001900041d03210740070740000c00d807007500c0c0c032155011030283c1d0600c200040003030031003000c1c00300d01041c44030307041c002c403c07190b42200c5c01014007900c40c607251002030042954081c00501034941e0750425240d00b421040002c0c04481c0f801005403590b07810800c00c048a44016002181541403265001d01c0700d40d00008212042c4207243c10000c0001c80c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 778528516 1250 778527266 778527271
    0xf0c1e070c0902040b300c030a1a090117010912050d0f02040f0312052701080703090507050105280306030b01090e030703080919080d060806010b07021210060909020a080307020108 79
    0x50385003d42c610900c3c3c5d4480c0c2c800c008000b1b50052800f00590a100f5840021900100c5070340041c03624203208024201a41c10320342513191805840030720140d082c91006480d04180c0142c082140d9202c610a000240d01200d4404200d4515504e02d9151075145a031303c07080e900300c000c1000900380107000a200c2901c400c503188040300d5002c43c841004801e60103050b1114000e9001c1b1822141e0441e107035005030403c1041010380200240d849802c2c541d1202c0d01a0304480e46848040c0480d8003d01d024040c0c0d500903030040c6018008117022140054498500b041840d5801c001035002030344504003001000245610907024100c404014003a00003a8542c10350f8034010400c000d0104035840000c190b902c070080c40a040c400344500d401300c681201504200445a2168280d602000d18083d00010180d001241c2c0b64160b0705180001807500304580c0030462030441100190350780d030140a400003241c9202d885804004c00340581c0100b0942410f004100114015a00c42d5415410412003180182e070310440c00366 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 778529766 1250 778528516 778528537
    0xf05060a0621050108010204170f06240628140702090c0f0a03051f0311121c09050f0d0f03210e010222030b0f0c1e070c0902040b 57
    0x1d54502200521003641c40c0a5503070b0198203107448000300e880041900204143e400b6540c0640c4081c102e910203580e640307a0005001602d82001c0041101050a07030041c1d28001602e040000c094400400001d0300350f484404402d6504608107200c01e90800f04007403008520200381051202c105664440e01003a1003102d000034810316503030001420015002c82554070107180002015240c0e03040705009001071030107580c001071410182c80c204541660300303000c0c0300c141c9501811601042c40701c0740c10b21050440d21100e24503107008001a10401020b00c404515500c1015513034418083e140c41e06010071103044098490084000c0141900403d842064408220754140f51417200020841a20140142c0a4071400145401c2c0000702c4244076054001d450100101d9100c0440f40741c960f50740d04a690310301e100040c00900c042000500340da0b07044a580d544220a6000d244c036051071003005506200381412040789403480415040c0a201c4404180c60260040140c02c40c642400c0810485a0340103044055 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 778531016 1250 778529766 778529777
    0x10501021b0a240207091a0d060e06040318090203010b12070201060918140307170d06030219150207180b01030b0306070c1505041a0a09140609010f05060a06 69
    0x110391900c2e181d0b40c0c0d00003006141207015040c03007600c2c2d0941d14029155403000043c458400c01207201c250718821503845510803000c41e00c0074440c04090008007240450b054410959407a01d03d000d490701400005c2c401e501c20741e10244060448120320059403610340041c0005403040c4014440540504c0c1161450400e02e4a58059584d43d00b4040b8003520098101c078612908040d017000d001c00c803807485154982d10800f03a6041594001e403805949000c0d0480207084e080407000c4400d4014040c6d4011b041c0900484c4022500c5502c0703030085405c00407402000c803803051001c1d204200d9402e13043d0544200c0d228074406014042d00c0c01071407030740f405913075001c640c1c01641c1c6840800e038581c0681d01510190034040e0956241307103000741e4082c0a5000d2450182c035845604110700d01c0f0881d00b0b00c20184600d034800c014541c4071400c004003002c100001041004200d55031034400f404681c00080046070780d031342400106510b282032140642581c40050408100c0c80c1020144415552640010015201c152508 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 778532266 1250 778531016 778531063
    0x71d04060902030313031101120e060402060714070e0703050610080105060d090b0c0c010e0a12030b06040e040506180d020c0607050313060c1208070c17040506131a0301050102 77
    0x3e13041d8850008070200b0380070a0300b000000c002c0d0040f1900c4038070300300f41c03203140600703c035550b1030b40558110803600012034009038000740051411201414059009400c00c2e101c54140320b01484c9400d17900c0c0c02a454490040040040d66076043c0201940844181c500001c01000c0350700c090b021407018003d5510910300442c20451f10450f69022030341e1580c12005018040c14410b200312942c1c0e000045021495082440781041c0d2080001c40031300c078550200b14810084900d41086000389200c4d80d21035400103040000007940d02c00301301c0c13241c01140070f040030b0b140c2e0f400d02000003404080940183d007102e030400740d12000e586d40c0100304101c05a105881c20340d038070041c514080f4110701c140b10800c8541d11070824003090107984000c40c0c1017041d1140c104808164144031040d01c403403004856a070001606050700380c000070503551203907501c07201400e01c4500301612100010140d07040304400c0401100e10301010014080011183c003000952809140d24650406000039107514a9218a03c4040c888422 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 778533516 1250 778532266 778532269
    0xd0305060609100e0f06130e0c0904060617010e0c0f0f040e10090e1603060f140117011b0e06070507081005041208090c1e060f040602071d04060902 65
    0x8480c01c2c250001d003010b650340498000038011101079183c06018451001811a040c18040103e4985010702c4030742100e2a481d21b980f15201800080c0206003440041c45004c00c00c1d1218092540502030783c0d01d50741d03052098200360b0b01181105a100c040480031180500c8055480d44c0d044404541c915480e450343e550040001010310b21541d0b000075140303aa4401007041e604155103552007664580d00062022000b0104156500c002c030861010581e40d1003042040010600d90000820750315045011505a40c0c82c40300c6820554243d02089896802c1c1000d20f00030102849802c1a000341c1300d003803000034003030403e0017040140401042409547e001420506215040004a00402030300301107030300c0310950705c2d6204040d2400351002c6904c0032403050b080c40c003030b4000c40c4c1e12441100c5010040000d07103d08401c202060754410f001c82842441c201424510b0303110040206034541c0714030003a07a500c40c0303000c5000f86065466030088811f1550b01081c2d080383c500c1c11146680094100e070000c2107804a500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 778534766 1250 778533516 778533529
    0x110403020307030614090c01080f060d0606170c1203030a0908070b040501150509060f1017040c05090c0307141312050a0210050f03010315060308120405060a09050d030506 75
    0x40020307505115450001013044000d805c0140e40442d818070869058462200241c0e590f030008030387d2404070ba8504d0014604500c05003043d5400384000f801c00044120701d403214012910550400661a8241c40c030b003c0d1a01e008003e1582c000006403207481c000382040c01c0e260b45034000a8801c0c1d958a807202141f400303001070700c1d0550310100c3d005411500340c0e041603d031060080c400021004800304000740000340368a00003558500c2044083c0268501690070004c121803400b0b0b51f91080180300901c100903110380b03046800907100360b208032903c0951078108000c00c1100d15005000e595401c00400c100903c8581c0000000980105240c042d51a02d40304400380295a8490304075aa051404402007820721000003841800762b4003e58500100074440e80c01180c040c4103e070521800c1007420401040001c040b841d2061101500b220002100d54580c1c0d982c0e4100d81c410156032062003030403c140f000703021041c40301e00e800c1001890100402005c9540e02511135400302d1034801807654581c001040742d11082c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 778536016 1250 778534766 778534769
    0x90e01050609060708131e05010c06051f1214071a07080d1a09160e19170d0201050c18010819050a091a04031b0503160b15010f0f031104 60
    0xc0080d4a0722240c000710f4071900600e101f0f0300e40c003601a803030742903001c0c040700a4038040c1c070010307900c00c0d80d490119181c42010344030180c6500501c1c4400100300c1840245070791480c0241c914480d03107064585a82c145503503001d03170045581c28250401c81003080092544041400441d4403ea8065241c4e1000d06110702540181a002c010650810006001e4003d044061140c5000101c0340c0107003d484011505600b582203d5401000c02c1c91105200c00e189000c50781d107001c91030101400d12805440f0120a1070100c4190712271074042d8440d020100c5115028014030f580121045541e41c1000c40340321035840d0351503483c0845030600c1030307900105c1c600c41e00001011000d50381c8910144410b0420100c9030004140e04401a14500a81c0012084c030551040c0103134015330301565030405407140f003018060402c0c003101080300c503848100241c0c408403849801c42c810700e60247c1d400f03000c03615214040c0c032020210301c000d4034104402d5030032420080b80c03c11501010401c443c980003403030580e217080e0301890784600d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 778537266 1250 778536016 778536023
    0x6090204090e0f0c01050a0e0a170c1c08120408090d030908010606090f1517101d070f030b030109080d0203070f051612030f020c1c090e010506090607 66
    0x540810065202d0700000c4140c07500500702c51440035020b075081e03100d084d49011039000420401241c00c03d20322450080406010090212203050750381d00c0e08001541e4000d04000081d003100c103100b11071703162000801130071401d00e20413202036600a5039403840c00c1c898502407105003401400800d007070002c61402e9071264080608081e50361655410b0103400c20700e240c407841c5019070074071901251081c8110300c0c110407980d40d5003008020600b04545050090780c84189002040044012544940b00c03001019000f0603030134001c074202900342414864a03003000c501040040301c00c9028800301d0740d072200801c114154a4a40016041d1103400000c0c050015031a025200d614040740d0f0180f100403036070003103000f00d00039151008003205085050b2100d008007c110003900781021102004100d80d0055944038103240d1400080002d28891504203c2e0401058a00da50740500d64084441699501c401034009050410b1281c89290401d070303e013003080c140901402120041054041622400141d8003010703031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 778538516 1250 778537266 778537271
    0x140a1d060c160f02032e0c02031b1f060f060504030503161403070822030510020706021b06061011071a07080a020607020607030606140306280302041d070512010609 72
    0x108031160b000211b9003150203500100b18010307448440344a02d1070044103540145050112251564200d2240940340407440d0040c1410000d0303800040c03540c1c20320f413585004c00003160b40c20b040c00781000d00025040b4606000c820001440480e50000990395030100b17a00355001ca00c015454004500d09041103035490501c408201042044080b001074005600407160300c8601e01030075199084004403a10000d41a60410f071850100c8100d80c1c2c004241550040c00c002d8644250b40c00903000c42e0901002c92074031604420140415450100a400440d002e14685000e825100c200c00300e884000c2403003602d9209030343e8041c0c00b90a0440006840185401c40129a1100c0c03130200080d40f0f0318001c494800040c0503030000510394601a1280c00d0964010f6070324411422040301a94003a684080e10055015802d00c0c0402901141c0130b0050560203028003413004403601d540b041c402500d07801c078031030558986290310100d550100001c002d0308a402c00c5800341000041003800380e0050030b203a00260300d11030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 778539766 1250 778538516 778538533
    0x50a0207050c03060402010c030c1103030d021804060b030105040b01110f010506010906050a0f052b020c0d1704060506210a03110d02100c0201140a1d060c160f0203 72
    0x10559026002180c081c6041d2201c2401c02010140c6400c1d0884000380400c50300700f100b8021034803c2851449461042c0001000d008402c400a0329640004204801207500020820209040704000e560f03221002d407000c0c44000c0c240303031544905010500038240039655550f9054000c0e8072a201c2d82c1c203032500c000c0030784c1c0d110f10304054001c1c0a45011142c160100d08100f5002407010b10400448828080c16500c2849058007010211000d920107440c122559800488014201c0042940058524544000103950301c903224040c0d4180000301c0039100c04d0050b00721002082e001c91503511940f0076800400003c1c0d07a40d5000010380e0007421003000b050991410205045150701c0010440e8030302e0300075222142541a040300141e0340d0100da4002c1401600141603140340510355400400170290180004a07902c03000840001e013810084a80344c0d00c554a07640300e09083d00104840e009255a00c0018126501c0c0030320700c221280c0308503180180700c482248400814401d01d900e080700410b1380242a2032621 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 778541016 1250 778539766 778539781
    0x1f0b0d1d2a0a1d06060a02060a020a0e13050a05010f23042309070e1603090c0512010209040f0606020604030804031b0b04020102010f0203070c08070501091a010614071e05070905 78
    0x80f43c052020b42c01020041829481c10206488202c00103500804041ea500007901019400040c500003d00c250180007920303d580750b006001c032014000c140003031a071918507403403400d548040e07210700e00e481e2440c8000c1c0b02400542d0034400c8060003100c0203880101d003a20101d0000c0500718035045091029441c1c49214a5029a100740646070714011104800d440300e02132480e40031300795200405136180c200000506402070700310040490086601240342962103002c50142000c010003040665400200106140342601c105000403d18400070405c1c1810a030020355115030140009e014822210006020503100d240e4075404039480d110700064910003481c04406403d0700b901c00301d01550815211441d510300318400d0307034882c1c280c560341d6030000c18140c1c83d00d00007070b88041030a03680d075500c4980d190b0224000950106a03a800c020248860358034051004000180f5a405854801404c100c508041404040c0802d80c403c814680200e040301c003490010302d003055a03801004480c0c10070003005000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 778542266 1250 778541016 778541039
    0x9022404292a0c06030f070c080f070b1e0121050d080105040c08060f010f0212041e080604080316030b120102041805100b031f0b0d1d2a0a 61
    0x2c801e64508000300603100710014640710300341000d0840e0414010300008084242410107141c0040c1c903400c2070080111030303454084090780310a030755051078040010040c0401078100c1e403540d80101086140400c0c005d1a020380c80702c3c8070062080d40c0060040b4500c80ca9510319114540509940c40411111002101c603006400c0a8092164922540c0340088a0081c2070081100f280710390001032205038110130050064030403070480d0f0f08410031842604884400a8801070090020b0b0148241d0703000380f490558101c101070b103c2900310314015000309081c800015141000d882c0c110f08024290001420f0080b01200241050030100d0f034041c2d020008002d09030019030003401035440543d450780020707140080d1001078074415074a811b0701ca035113070904121403890a0080c44c0c03c00c240c074074076441d0540c0140036582d417000c8541054552a9002500e803c0c44142d520400f90407201507c050002c03000c1d59951640c40310178038916040c1c0781390004420404505e540b2b00d0045080750081c03190642d2620380051248 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 778543516 1250 778542266 778542307
    0x90426040e1b0a02071a040b1b0f150103230d030b2d04020304060b030703060b01081003051b03030415050304050d090b031f03020d060902240429 64
    0x40c0c0b030b40148620445990b59204403040c4070840d80080410318a440d00005940d029000c00302004a801d00c0b0104441d0032200080100309000c8034400f03988081c540c481d03414030444a191094540c000c0c18203d00c4a01c01494450449030448481c4080e080010a040c01c208103d140360301c1503000e070080347c0e1101505030f4001c41c00600e069845068848281d01c1160260754003400c41c00c0010030315815015207281503001164082d1041e00b012440401c98000309142409541040b01c0298480814526a5902039500c1394000304203a80076441d9840e44c0c94180e00c80c46115061081c0c05103144081e0015203041007200c0c02041007a80402072200c60b00002401d03a001910b048815005030702c074105900e4172415071842511b4100324068607540750f45611140350b03102c42c0a000892441e11310004003607504d0310503403602607025010120b21410030744100910414001a00440c0a00c44104030704100e6400003560250703182c04079603071a202180c00410102c5c1107031080c00301410000040c0c2c1520b00c0610b034040ca8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 778544766 1250 778543516 778543531
    0x90f0e0f010b28050d0807060c050a0c060e120c0304060e15070818030d0f0e0a08030a08040c12080304060b09040c121506063f0903030b030610050a050102010b090426040e 75
    0x100341206402700311203134031411407881c0000b207000300d048002c107016034480c1040c150101d04032a0410700b24503000540d40c2025141c100903800c0824104082c54002415645503641202e05064181d9060040011030086900160440f000840d030484244000071155840c0d81008044410075181d2480081030035004040d1348000520444c0309280d1803c100c1d003080140d030070070f00180d81400d9176003604032600840144242c540c1085000c000403956800c44051230070724001c11410b0355900e001d0400c40b040d40c0c00101260f021b0f0800004200c0814545041c0c442030f0381021031f20301450191070403e0140c120407401e164035903d103010303000941d498000c921240365800e4010705140580100c000300c240f2041101070b03204c446114144102c4401d203d036015000e41e9109041c00640d41006030082880e081e0300b15030b81d0111a080a13018001031400110340001808244001d00c22001c02c0c00118030091009400180921407100c8800e8250304115201c2c650041d014208584695445c00c0c02d9240e0718050340e40e813 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 778546016 1250 778544766 778544771
    0x20d0b040c0f12050d11070b0c070f080f0c150d0f0209040c090608130303090803070801080f0109080405061e031e16021c09090f0e0f010b28050d080706 67
    0x100030643c0c2d825554816040400342c011520100029141150780a580b10898010032001141d030119401c0600500d4400200a024150418400750b4540200b0340002005c2c1d40100c040040b603803c00203842c041100f05075899207006100800c05180c030b004400124400500704003c80301511b8695028101c03549007100c0600c640c1135403031401d03101d8000c01d0007480c0015202100141c02e11650a0300c44407a00c0c0720385000030f07810b4031a444031211a08262401400100a000104500001000000304402c5074000810201c0403d42c4e8030045071055110f058003485010030040c403039a01c85d40365114000d034200200c43e07903032400b41c14a00d14001e0031142191452510b03004124121031816040d1703980c0129400501008003004619460035580c0d000440c10050700f804003240008843c0240c3d244a06604008a014601e4107095418940600c41030801a0315140b00640b0707581e5446480540506985603154115059076084c0c04030360a00d421035500085c45002c09410031400383e004140043c0120303c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 778547266 1250 778546016 778546019
    0x10b030a2405040206040b030415060915080f0705090402131e23240a0b090405010e07080403050703110102120103140607022508070602071505090616020d0b040c0f 72
    0x1c08129401903d000e9000b200c02c1c4400c1c40108444c100460b003007401010628129810480c1100660704507402651b64551280d011201ca02c000d682c2c4d42002c0e201c880081c00d44450a10151565142244a418881c0b00346401241c00c0d500d901050004950390740106001c1d200112122407804a42c545c0c90070078880c50107082100e13120703080703804401420210442c0c50b06911070300080c451400240c800c01900c03130050f0f0308d40c4005a61313410350b000040c032448140341d448040c00410003013112816031208c4460540e01080117a00396214149a61190303150821030340b02c0b491810216862800c2146c40c407101d600c001040000d0f4444410118100c0340b183c0b26401e051128814101c5d2640419540c1001680c03140d40792480e400c24064480458640709407801280310b41d06c164040c6010410352203500540c00c1a001804480002ca11070f00c8503000a04229181c25411808103100e4030403410070107440900702016504660310820018503854001240001904150803c0c2d4941e14181c400c1400310a0354400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 778548516 1250 778547266 778547333
    0x708070519090f0e0105011d0a0902030403120507080105030c09041e0c03050304081b030a030c020f030c03030d15150c030f1b14010609060e010b030403020f100b01021608100b03010b030a 82
    0x45901030300002404030b49c0300e1484c000c15000607403c0503000302d0a2002e031703140100c001000751060901c5000d083d919840c203540b40801385810500a9080c01c0c1c001c408001c20400884e1080b80c10902c0748024400c1c203200c10080f400c20a0403901d140c1c000802c2400002400520f244001980601343c2d42e06884d0302c0081e2100100305580c440e001a001004581e581202c00701510301039200f102110000b6040d12055800d0b9030000342541c5c0040411048181e6036810324599101c1003180d4000b40941e4089400040265100a0400201c43d4001400c000400041c54a0b0600c03518105281c001c41806100e00301d001e5280c008110300a0200c00d1483e90b281c808005591041802103904492848000c2101039080881c803402d207500080050f02903200b122980c1d800c60304200b101c4040e440c07121000103101c19284000a0501071400c2ca0182c1c2013000d89824490f810010808801880401d800050303d50500e0000c01c1c0036015844000303038103010360303100700341802400543d4401c81c03544808101c40405071240f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 778549766 1250 778548516 778548557
    0x80a0302240a0e01020417061005040921031508030c100c051803031e0408011404021f090807060f030f151e0308031e0708070519090f0e010501 63
    0x400300346120041c1400701d0303000c80b919400103c0705550003001500e0a901e549001080350a1181c04a41c580d104004010304501c04c0c400b900c2c082c01c030448041c4081602c503211410340e0940c04139501200d0364991408074600c0c0c025801706c11051810011003010503a41c800351038503a0804400006c07203006041c0704c00ba8801c494407070100d604200383c5585007440032040402600200003c030283c2c040c482041106185052200c82003044944600070a5590b420607610383d00759204038038a20030306414541400b0041c2c0ea5010262180420004e03400c0c0046600841140d901116a00c6412180150400411007543c882900f1207100c200d030301c05004440324031400c00d00725402c940c50540072031814001406a4560112184c50400178400d404c52602c0d22030320351041c0d5078000d0f120140307a00f0100004004480041540660022840c01e00b0412481d0400c000b0f001d0344a5124000880c080e04030001d59454041c03200700001d00081c1240304000760711500c00a5a1810a025150100e007200b040401d0684c8040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 778551016 1250 778549766 778549813
    0x10080d05042c13020d0c080f0d1103040515090a0e0703062130050403020f01081005090c16060902010908030f0a030b130905010b0a09020f04230a080a0302 68
    0x840b000d00b03030799214284a000e403c692101207900c403900c1400400481c100f90140ca01500c401006000300705045c517105460012401054000e102e60400202c011100100a0f5801ca450544810f66501c0d9010325181c0ca520032903506643c00801060301090f02500383c020799110341d80a440c00c00025484946084803418020312511a4524030a40c800c00202c0c004005501404820f580c0000c000310005400012004401c0700e04c00180c01050400940c600240f03000c488080038284113103182402e00968101e51400d0040500480c00d04011a0618032401d040b01c940701040065007000131050319101c80500702c0302c54180e0004946e28800f04440324080201d4a07505070800c6441c0ca0000d03980d1042e00608500c40b03410f580401c103800c1c12500d0b40c0c80c90064110003031180000244030b0402008000d41028541c0100350b005106100903500c520741030080b85c003510000c8004444001ca210342e0441800b55060000e50802c12018000170010000218141c7c0e15101b0f400b96034103081d001140f49184440c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 778552266 1250 778551016 778551089
    0x203240d020f060a052b0c030e03270a060806030601080303070c151e050f0702070b040b090d080c0304081005060105070609020a05040507051201080a02150310080d0504 74
    0x10102442d00c0e890803a00800440085040440c1004903540c460082c8101c1c0d950a92242c040d182003000c1015840e12852210391000e080030407000e0380c07111003c2c0d0759005108614403052501c048800d10b003156440c1103007440d01c0051005800da500c50000400c0070100f030b21054001d00c0381000200300d800d800b10603288201480d030b84e01c0c10652003e403918800504040054004c2550f0b407243d42003002c401c044142c0c690551980302103918203105680d82100ca500514a800f10340104009010b41644001150101e030900104035854411020000314100c80c80b84008110201c009900d141403200031000c0d00482e4414401e036280542140b588000703840c412901b0500140081100d2400a81c0c543c1c82080307668000b5000401e80358654001c03270110341d01500c200e0045000800c01e00c184954400005014186641c00340603682d0711540490500d0b0004c05554104400110015840d0f01c040f41c0b001000302104011030b101c104c058580580240e101e030155210105131361002401100e44041013000b006403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 778553516 1250 778552266 778552279
    0xa0905030f15190c051c06080606150d0911030712020604050402030c192f2107080a080f0105061201090b011205040b061206100e070e040203240d02 65
    0xd00541403403012400901c3e0403880240e40540d45a6140103104881c40f80f09551542d580c1d400304501d10a901d40c00401e000c0c1100c40c107080e42401529004215190441d030141c54100040c117150380417049502903201000306c004c1c5041048402e000e109114031082d82819001e0301c2d8055100d1840c07141204210001035008101004200100d081650003180d100c110010b0a88c14041340303405d220400c3c2e010743d140e80001140d54181c401200400d14104203806003441410301360700702590707035541c903a02d0600c01011000355a2a0f20720145c003251084800e01a84403800d55a02c02640300e020380854802c1e511411104411000800c040c1171a80c00c4459100449000340c42581c40d000380c0e0030182c80261803042c100500030b400c404503039100c0c1c004d00d03000314825040030142d8600201804a00c000103c80c40d251035207c05c0c2406100440360110344151501b0140c40511640d410005807030300040301012a0b0460f10000400588490002448902c1e91a207802ca0346440c03454001c1003000c0c50076401c040c3d485075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 778554766 1250 778553516 778553533
    0xb01151d01051c1d10060e0a0903021608010501060206010b0a1709010f020f1905160627150605030c010207050622030f1502030112080c120409020a0905030f 69
    0x60049000d80322500099400000410b070701e03c084800e5403041070545030002510000059440c109200e040f01e8812404810001d044c03804948410101014083d4112170b0b03511098a0f0606100744940f5003814241052032954580d00d0315040c0c0200703024400c01006000b04000881d030054210102d43c540350a50307845c1500d01c0b1200c44c405101c00d1002d0904c4140e0b40d03031154080c0c8c902007280050031001c006010700b103840d80001c100301400309034000341100400c14100410710f100c2400c0854210040d4000c03c0000f5444000c0c107146540b07112215141000c611030b081181c040005159820039070a860352000d100043c0d0351014142d5892001406a015030400c080503c154200071000d0900560303407038103c1000f2414180044211b060642064410100500c2124203000481d0307100000c0c001d1b654030862640d850058082d6500313406601c014140c140014100b81c45480c10403a0b04009100d65121aa44c0c41c0e980750700d44000c2d0301c0140041c2c0490004c1e50000340d40d18000c02d0807924094079601a09516 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 778556016 1250 778554766 778554769
    0xd020712020a23030f010e013e04091803031404170a021e06100b03060d03050a11060a06050109080102120a02091f170a0c090501080c04030501090b01151d 68
    0x100f03460b801a20440008228000542d5420080c054510601400015012140749002802d51b2074003840303204541101e08040c0800e0f01c4c0306060b13490020494100142c0d150500f42d420f1054426684003550f018107290b0389800329080060b4001805110b41c404100740421900c03915a4030a0484000c4c100248020340960004030080042406d0b001d0344c0b050720521150300e010301c241c3e0300030911b51000a500213010400302c88044184800034003190102030381145040d10000349400010403009040201c00726010390018029080c2d020040350060690311a45000030910303000740030074803d580c001a00443c1c0020300520600c21901d40d80b01c1340f01e215000f680c0300c818000c06036104020304ca40015070200800108003003120361800d644070540d94003010841171444038561100c0138101d0741c911440c081c40700c0710281d00580c9120803140203090205003542c0d06590015503008940c00074095500f44000d41d0204610351601e181a02d00c1c9100071017240320015412210f112040c09282035405884c64920b015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 778557266 1250 778556016 778556039
    0x5100c0806090a2c0a050f1006080304120809010c020d050f1e15041a070206010e1509040605180703030c150e0d0503060a2102040605060c10110c0601080d020712020a 73
    0x30100c444100c5045d28a1999442d19244034094050940d410001000c070906e01e280c0665002440120021414030703040010440e60440d081000600510300003411740d034564050340e14051a190001e000500c00c100342e05101d40c5540c075160a0340300c0790081c2110810880c410b52029581a500b000c0100189910040381e00c0c817a06018105403940001c1c014481500301c9524181c0f8419803155002c1c00c4954540f07101c1d0f11400d0400b9040142c5d0040ca07804c000d529455641e400342d44103800c0480410203880d2845449030100c07100d103500040b40a0020044145600520121070044c0f061000c0c4091100809841d4205c2d01c0d824007940003604040b03524081d42c2d02c118055500b002c0010051000c840c0c1e11a001100d40d84020b581020001400c0c0c00301040d49880d100c0c0d0340040405440e52860140b801410720303200d0845221815210341da07803c2d89000c1c404008191641d03a0b00900490700c43d941c5469845a46403181c1880c003006104040000c100c11b24003501040c3c01560107402e014116080c5a0420038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 778558516 1250 778557266 778557341
    0xe0124180f0209030a0c08060114151804020f0403020a0e01080303131b0f0e090f0309040e0708120702090a1b11030c1e24040f05100c0806090a 63
    0x9a02d809021a400d00d5506110740b0703600d188502c182d50f03c80e5141170000d81c2840416804903404000ca00c1c070b01c0c055a10748107810651000000c2141da81c0d0b00382d0344c540000441480c0c06581c3c00500c0820a40c0304520f0f100c0092041da030084607000b110300d0369100003014581007401500031a40091000c140c80d802d009981002d05031140c0c00e00c00744c1000d1045204900d45032644410350041071003104004200c421601c1c150400c205201034094003a034441c0c0341d50b4a100c0d000ca030600541c3c1d5224258211141800204c002c1c000c054265540120082c0024200d0b0b080120240d110310842e90203c1c0104000d4800c850400002102007205e680e81000265411309901c0036801d8130f400104a00300070761105000380003c3c0100d801c0300d55406801d04070410300e007039190100e02145855000694019100c41d0400ca584150b2080d88120100002d1410ba82043c48210032100c4a508000080d07031401d410002840c800c82d01515520f4140e945c01c00a801138460442009014519035071000d01c03c5140a0003900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 778559766 1250 778558516 778558541
    0x1107210903060219030f0c0207060e120601090c0801050a0e151804030f021225080f0a0507032d0806030304051810050409020303030a090507090e012418 67
    0x140c00c00d540b5260340c1c003664002069a03003088001d19804c1886501441003215640b4525410081c0d49104280a0b64076a254007841003840a4080003a42d90f030340307014400c1b09008000c400e585032940c1d1207901a01800850341c1d50400f140041c4000300f514200309150304200c0790305078001441502d610302c03008080000c2000042d0841c1d01c1c01d1500e002d092454331203500540c820340d6648508006600e00a00302a1200c560800c2664100801c02945144002c200f910301d0b000401e416001e0301a01e82402d04c0d118140103002c20060108641188a422801520300b581c02525400c40c011a60119902e603498180541003500290141c01084544120720084d40010302074210792a154841c0300080f014614110501c22118904d0104080d0f8855059804003d010680b0b0070301ca24451580000c0d1a8000100241181c03a96100c1003001d00c602005074800418040804021030a050300445000c1d02800062050b20080b4180004194009400c544119150003011504040b00300c103031762020b05030090510 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 778561016 1250 778559766 778559777
    0x40614040201210b120a0302120301050f0114070c08070f0f060f0807020705151b010e0d05131a0403032705040c120c090302030f06060303070602030711070b0d110721 73
    0x413105440300750b000702d800f25603100109010055441d0003403030040329183c0101d0a200c24001001240c6981a00300f104e00000d0a00c6050f820703060000d6003990040500250990780c0f00302000440c2c110200e40641503805c400400140c0c55141e104030101c0324450321440c2c0006074200e00b9506030900c07502c0b0440e04803c0c14419100e800c1d81d07500000380d000c407040009917010300001030300e140d006400046030203c1c0e140000003807002c441c030b081c031140c0c440d0b62204c42c8400303001001903001c40c910081801400a403000303034043c9142c02106c00001c541a040ba0104a01003510034000d900c07034400c29202c00c02039007804442e10031480e050038140070250903241110014030085c90307094066503901d401010006015a80c540c0e020a01d9801010310388070203600c2c0491039402900c14000d49407008422210f0603500140096034030740700c0c0e450032295100c04410810940c000c2c1e120100d83c22481d400248400600080d0500c00c40303200b100c45004510520000626002ca242c0e0700401c0c411100116400804090920 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 778562266 1250 778561016 778561031
    0x41a0c010608010609061e0302100507060507031a03030909010b0a030e030309160f0f03030305182406040b0906040c02011e020901090e040305070b0408041d04061404020121 76
    0x450075111241c20040c2d169440d2841402640018450364000702010f0b20001032030000102240880f0031f0368007020f8060030385000700b500b10134001e1003100c0800d58808410003240c9400c05000300148111a88401c5a0b64000c1d149451032a002007a6081c40f0070042c442c0d109a4604122041c0e254440b050729014544c4030500f8080840f0305001442c4110015409844080720019640000703142c00d8001ea21441c01600090003614201d240490540e641818002100d0300c8005c018086c14070301d0800c0500520450ba4000d02044400031a0303108542e03860503548080d1912800c000c00e50301c204031115085601c442c0040c4851038a504010440d60301070000044403000400003480b500071081e203980c0d4080e000180c1c41d405580c8444528010300b01085405454146039800030180c0c41a0600030b80350440c840040f50501aa00003190300030074141c0b040070280d0349442c0c0301001d40c220454041d10401c0c0350640124400442d41681c6210f594141d50700702205001003020304003c04c82841499406d03599125 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 778563516 1250 778562266 778562287
    0x305030a0903050c090613410604110417120c0c01030501080f0a02011b050109050604051203060a031112031c0f0c050a0c030e101d010e1c020d0204110306010f080c041a 74
    0x1c440b290702424008c803a100c80504076800c214503005404903010f140303810800e400c118400b41c1554180c07035005c40300c00c101d400032240c1245840110300c032a0407021000100412082d1002415803124042030320184a240e82e12203005031260902c807000115600101e1070000103601c030700900101030a846d8200c0744029040d444080c2141e2004008032800c1e8400e5040c4010700208101d1202c00000007410a0300d14a001130102d200741c2400d02c4010040d034002025485250741c5d40c05a030501d000c0c6503044903141c00381850342e40482c905640001e80070a00c4c1c2032086400c040f0130b0150002000e4192100c82c90101109400c0b107608814420607010030292407142410740d55000e08001042d141a612652201900c40c0c800056131003195080303040c092164155410f0741c80c0c0040c416604080f540400001764940d0000c40c02c01c0702c603924025845807611800403800f41c1c845002d0740c0901300c00e030303140d0300300412000c01aa100002503c407008040e1050100300840380d085005000148068039006040030610203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 778564766 1250 778563516 778563581
    0x902102a08031b0324031e0c0103060504021801050c1009031e03141f0f1205010b060304031403060406051002010c0e0f0109030b09070305030a0903050c090613 70
    0x103030126000c0c4400414404107142c8141030706022030800d49440c1c40c50800310804801c0c40c0c0400e0f5012400244c0c0500c080141c1d40034031505006010020104102e03205000d5400d0f11030401d415020302003031501b280400c080c2824400e031100b40c14450f8001d21813821000041d503054001c401c14500314880c04c440c00390f040307080f40510790405200c0e0b1500040c1203801c00000c031a82c1d4183d1141020145405604a09080108089604101802c02000300303c122003014124030051508031102c00d42d8400800a07485460011030540d180c02440208409582e580400001b44070030341300500042c08500c5500c24040c4054000c1d07420007001000010f6140d6250003096804900450300000743c0d540e101c401c01840e42141c503002680000f102d4000091400e00c0010f000c2403074074080544140140f20008110007820003406015580000c21aa101c0094120090130046c01e070000311070b14082c070403100e104c0f81000001207018a000510714082c0091003110034000381001c0b21204203120068403068034074040b80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 778566016 1250 778564766 778564847
    0x1704051608070906053106080d080109050108030310171011070203010c0201180602161b0311010813080304030c02122406030304150e090a0507030e01090210 69
    0x110142c00b145140000701000c0311a5940020b024401c0d115611104042c1010907811420002001082101c12500880000c102035084012a880385c401d58107a01c5410804c07079412600a1041408070b0ba0301c3e0740d5244c0e00c038001a80e2040550314446000e000034200e408682041d900310008440c00c02c5045940741c001d80340c040aa1143d10f010019004007542802e015808100b92140024800c91100c000c20302580000360b10060600c580c00310320108500144190210119040f82140c03150742080260b440d014001e0f440100c441054400054846501543e0100e11405641640c03d500740c043d86c448117101d610040048040000c04520280142e50b0112442d29039900c00c0014441151003869005040200c44070013070001c1c040408000d450781d070000072101a2800440b4055086c0800d4100303580c071090302040c6903400b15000042000509540c1d1209114820030b80e410b2081340541000b03603080f9200b5000294101c01407200c0484668016840743c40e0700c1004100800e6061128100c0803c00d9419 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 778567266 1250 778566016 778566029
    0xc20102007150e1207120f0204020a0e030d08070801090908120c0c121e070c080a060504020907170103060506061620010914010c0609050d020c030d090617040516 71
    0x40003404400359030001a000400d83d041c4c80224903644130302040b641d180c55500c00e114800603584200c50401224014044015a026000f551265455007001c1d10000c48180c486000c0e1080099180344075201c1e2200e01d01030030b9a9241c1ca02540d08251002024050740c00058410036420888209a080003450036846409288682c40d180c42103086a40d084c5070030031004040c80301c4140031480c221b84071b0b0025607440710f09080142da03542c032017880c0c210440c134440c0e4407172100750260b0810301050141d41d410041c465842250444c5c910f0f92a800186c82d050044424400650043c42c01440001c0c000d40c009504901c004041c6410501c0003418501e20080c00c030000c5404600704441c1c044c6d54500d8200c41d046106090811505480c00d0548112001c0040744035107041044040018080c4003881d81308054281c0c1100c241c5d00654a103080c040e50f1f4107408451140170b44031780080c02e14018812a0007000f5182c5a50355003042103100b80301d514071420054010345450052000303104401d180800e074800105078 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 778568516 1250 778567266 778567289
    0x200306090a020c2b030c021c03113906060d03180b0d0e0d120203040602280909180308100503071503150510030216020a060c20102007 59
    0x8881d0102c01131081c1110840d020300d4200a00329540c0c5401203000d600702224500c03101c210071039011045002d0039084204220020300012551600341c07030000344090070b20003501e00140404032000b000501c14031100b50311b003454016001082c05c61402ea540d020f42c0a00a1030801016001c0d081b20420601c07030303a400500b0921000a003c00071450724001c5a40110320403000c1d0580040403c000342c908400c450304108920360000000b420041b03141c1c151064080050301e0800024a004140d00104201d003640d0070110740c4100e400102c06030203000300d40250f4030312036598000aa240d5015684004080c0050080d00c0644e007000c11542c8040109200802c6c51300f00c46041d240b2012400703012a05407a05403040d10403030250502c1262140c0150454480040c0790050780c800c9004694201040000002540510315483c00104198020460101c4d64010035207118401282101500c00d01213141da015008842c55241080d0036002e001d0303845240840c20410703500b800c0b4001d03041d801d04041da0032010107200c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 778569766 1250 778568516 778568563
    0xc030106090908030610050f2b1a131112041208090d210c0305011802030118200304030c0312051b0a1b0c030303200306090a020c 57
    0x1409006040c010400c03041c0400440009440da440a4400100030600500880360010040c6200308101e03103414003a02d0300c0c19160800d05031301409142800d20300541075000d00404282803001442603020184255180706000001d48080c040c134100c10260300c00d40d03a0f0340c46250420039075001006008041c02860020703a103152030314000b11210000c0107484200641c41007003114031000011109198480303420110032001c80089080c200a8260a040c2491818040080c071140c0d019004a8140c6581c901040c1405da000c400c0203040740024070410802e0000c140311034046030507546c880c0c4031526107041010400e80343e810300f401841d07001391400c40004291000107420b00d5413018240200381008041844a03050804074612450300c4c5e4014010154400201e281c625401090070a00408645004d012a03d4050508007a03401062105401181c1000285003104112400300224440980c42c0a4113503190741090100070140200001c407030303560810011203e4007080101400d0581d11030001540c80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 778571016 1250 778569766 778569769
    0x409060e0d02070e0c13031b03050d021212060406050d0b0a050705030f040b10120501061a070803070c0f0602040803070203160f0315020d0216200f040e01060302120c 73
    0x118040102402c6402074032060107180c18410515801040aa90740c6840e440304201c500c800c01b8251f07000a1955000030f40e40328040b0628800282164020300a4880010b04400c081c1d0301d840141c4801c0d021072804024030186406107204107600b0036000f07000025502d0300c80c0045628928070039015104006200b04012124410b800f91542c08006460a0f90450404c1c00011004a46c0a08010800d080d014001401c0342e003803450200082c01d10080207145c2500c0303800d00038000c2010380542079020f030112484501c04140036080721161640000c509246585d80300e01202c0600745030208407540407921341080041140d500140c0003614000015503558006441090728109007851840f1445400c0341040004189640d000400caa81001450154070a620f0100c4001e00c5181c510501051000c00d081030311000300005110124401e1500382c030780340b080c020040d101c0741640c151190300401003020404141807a03044180411610310002c6072580e00c2c1e41c001002d4907211720040300950b02854144034103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 778572266 1250 778571016 778571023
    0x3100e13060605150421080a0e1c0f080f09060d020d0b09010302151c05040309031502131202120708010507140301030b01030303090812070e120303070f030b040b0409060e 75
    0x10304080b545903011004042035804d481c01035200e1154043c50035a10124141c510806a50365243e100154583c1c0300d41d5680090b0070000242141400b5010404081d103480e40700c03610b84038645400003000140d01c0b0b4a9603d01d84681e11a2001c0d545d5041d080c450458140c9810028041d201e903049005a281e035207041034072041341e14540369944615144d0004001584441c0300b140342074400303a03081594034151100e000d14640d2020a029090a241c14100424964080c44030700c1964400d003812500c20102c044014140d00807160100481c500e000d05c104200032099002e014854800b400804010200301403283c10711400741d2000510341d45032020003c40d1548030324000c01e4290b14003495030540d415526845625181404010b003416070703410481c001c0c00000b0b0180c510600c058031401285181800c001041c03101c50783c15450050b0100e1414107252031020040e00d00c034494550707450708940c9004a044014055086082d0340155a80f00b4814a64682d0f004072140340d03008400100e43d034011050b4041c42d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 778573516 1250 778572266 778572269
    0x60a03150c03141b0a020102091504060f02030f0a0c0c0315050f0601050412020f0a0e19050a06051c3f080606030705090f0619090e010f090203100e130606 68
    0xe082e2403e0700704400740001600d40c1c80d60324206201c2c2525605011000c2e40203108400c4c18551080004104140101c1100024070641c0c00d50f039202c03d2040310625060780c1da8051241c404e00880c0003480ba50804610821401c101c0a0040c2c00300e1040075520740710a03d83d9411441c41c5088203403140c040003c4007038550315890300010b01b843d0241c60039103022200150f03941c1a040c000c0c821061517000c0300985c0e844d0401c1030042d0001c0c80b503050300b506150b4070300f0b00000840c2241c0c40300e02d400c0000140310a0b140744156001c40e000079081103483c407101760303140c4002d03602c107101140c40909882d51390028540a50140090303a01300940341e402050b01c06079400460300a02070140c1000303c0102001165202c50041d43d40204807820704030f890f142d41c000010460045040c0c081c0c2c00c0a030100d201480703a002c1800141c07605040792034a03441d85e602c03007820001140d401d00583c1d4601905100070824088680d0055521111102c400c00b01c2e90f484825a02c9074845c192510780c1802900c3c07190009100c0d2900c01d480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 778574766 1250 778573516 778573541
    0x3090d200609010504140409120c06230606030a090624090903020c13090506040602091f09120f0b010605190305011413140c130609030209040209060a03150c03 70
    0x604020510000030138034420350266210b036412622103c4160f4650307810000c000d41c0d121854182c4540101802445009800c009a0714039040c002d02e401450902c000440c809040c2c41d07040aa43e030390f44414401290320161500c000f065441d01d03c103020840e81d20a15426029041041d6407990b0000c042c04007100c410f412001945141180c6100026000038080b400280180c42a00290389090042d90051000d40d4000d4403a000300c0040008000455004000c066011a0400f080300d000081e00b000380c0c2408000540803d03078088045c4000d44051000803a01c2c0e10603c51254140040c1da83e000c40400281d00010200d000803c000d211062080780c0c0c5061003107286001c21266241941e080651191017603440c4c001e401d1140356100580b0107820000c40210090070a0246040225009034580d10130307411140c5049001d0781c04600d180c4030382010f00c100e913001401d00c040c0791541d401700100c500014040c039a014250344400000140315060312041c1d42601480014802c1350140301500f51000f054402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 778576016 1250 778574766 778574779
    0xd230705060f070b04021f080f0108030a09090b2b030e01260414010e070501021606120b0609091305060f0415090809060f07120201060b0d02030903090d20 68
    0x300c0b908210768083e9045039030400f030680784a0311180007083c0701181390800c2019031032000d00990030644c1c00020881c02400034001640007680d83d003040d2901c2340110204200081c1c02c0040c10030400710142c2040c1071064000f000c030f5510b801c56400c10010b9050f81d1074010300001d11402400c081c140c2000c121400b00d002824160030302040c511010302c0040003400c0c00903200901d2800304090041119091466400c41802044802aa1800300c1d9030b401c4103102c1c683c014030403801c80038080300c901030010044031060385407841854140400300011300120700400707410210900c10b1004076034407010074074041c0c25a451098880a5542000c03414a080100904038080102092000141102c401e0321261082c00100240d59040d624240c0c605208564040e6409400030030184103210300701e00104012885551400341ea038040745820f07400e8138568420b03c0da03100818412541868890b800455009107903009507440c10851900181d01c90b20b084509442e03241da010036035210300508100755140440202c42a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 778577266 1250 778576016 778576027
    0xc060a150b07152c0f0d020c010302030c09040203131b0e0c03040f020306101706070c12090302040203010b0403060c030e06060d0c050306130309090605060d0b0d23070506 75
    0x204461103004001019080e2401010344400d110740c2c080345004510180341444413400392001c03540ca1070540906800740c000c2d1142036840390300c00500c115440000f038003d45851003c51005400a4100230324000e0b030100200031070001c5a850340f000310300c900c21b400c0034a400c50a080c10015440380c0c03809036601200c01405401e205021004428030f50007aa4141056604e564500c0c03d510000c0d441c0d40000d402d481101b051003880301350707a0492000e0700c2e4030030000300380c003101400c0060365028192001d001141390300f504580820725090070380b0f00040b01d0382491640740e5036074cd0100c3d049902c26407290202e102c0110b028030401c0494000c07005401c0313407807800340044490420450707107070540a420306200b203a180c100441045007240302c0d0b50003444018103544142c079001035421504a010101107001820810740880c06203210b200d407800761540a80064140740101c0c51100c0103019241c8583d0f0300c69190095100003c4110010290184410181000f51060307140310914103403298104034400e00d0705204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 778578516 1250 778577266 778577279
    0xa0602010509280f11090403030c0e01021902092a090a0618050906040f06090b01080609090d050a20070317161509150606020712030503160e060c060a15 67
    0x42040b40f140c11181c1415100c0b01494050041882e0130685900b100b0a842080f061540590122080b107103a92035140707040201000490300d400d01d80006071400140144403402500301500c0711a40b24000180d000b115451603010a49825003540003000e0001c0f000940d02c0c0103090070700d200300080a40b8140010040c080e10306150740c0b44000e020701401740303400800140c0d103580c0701d07045645070035402001040002c0d1a20030f1200507100c0210340d64040707102640440c4031414100b081911802d1450094922405900011105684695550070401007101c0948400781d227155011480c0c0c4d044a0024000d091840c0303404104441810f51218107101d0603c2610151211850044c1129a20001c0d4a904001c41012240184510000034009d50001214074058511680c003540a503030042d0201c6c0c2c2d68560364401d01ca50310000d1500200016014000f00b809800550f4440368006814181085524042000b042440d0414410990351fa4044420702007000500d10440c134807015100d4202c042d1505200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 778579766 1250 778578516 778578583
    0xc0614070b190f0606090302190612020f04230301061707060e0307151d10050a0e0a17070306150302011e050f03040b040b09151b090a0602010509 64
    0x3024103200b40302201d903a4881c501d00343d000e4090003503802c108210b41500e42c1030050959019000c101c1c0501c45900e41c818500045032605012030b20580c0e100303041c185c607001d0210041c0d008080b248403070720014000030030903890701100c44600349440400f80554009d89000c060940384a039008103004a4a0400e121250402290010039100c0030308042c03e401089001203031510344503502481d1a50707408440c0d110356581c0320980b013040b41441c40c03404440c1c80c002c00401079150001012040850070400c408000075019403e0b1244101b00245122030140d680e6422224211170f1465800840d085228240104a058464421011b0300400002c1c0f10900390350020748500071042403c401198140d002542c203c0c89142242d020f444000b0046860b401c1900d001c083c140e0080d0b60803204049000c0004401c0e03040010001c13810302e80c541d4030600039242d403421b078625416101d5503d40000c108003c10040e075100e1240102c001c0042d41e000243d01c1c58840d11141c1000c6060960760410b01010100748101c00010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 778581016 1250 778579766 778579771
    0x332120c070308030906180105010f03020409140f0d1709070e0903040b040803090a0503031e091318121701031b150c05190c0e06030102070503070c0614070b 69
    0x1021040d540325805400a480c107002039100a00501c000410000713146400f080386402007401d112480202041d0402c6603080e1102400388030b0035841000310400c0980f62942102003564002e40c2e401c402d64001010060804a5911845915500144c01070800341d43c0000740200c1d01d076100100f81c0381d80c10014003035a01c502d807a20806030045083e101150300600c0c00e0007110020a0210030050b50f40e40e544004030f440703400580d0f240d4403070062110b0024141c2808021550300d84032080b01c80501c42c0e90705d11205c5041d003140080d0303078204d9046000c1c00f08100e071710b20507a40b03603000c0003501481c0c0003028a04021a83c81014031b0b0030030042511400c01042d064040e03901e054a0380f2400306d07006000d4042c0f03114200c0140ba070201ea0303942940c20310302d14001d80200c040407580e405141a10042034240c0c1d60812100181003008021000d250020448048080c0a6940280c4c1c02000985000390a4880e00d2454002002c2178131444d40350242000000d81044103401100d4411020b00e0402155840b50f07001010300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 778582266 1250 778581016 778581043
    0xf110a050a0302091f1d010b0c0a021513030b061002030408060c1810030c030c02120f0904060905010f0e1501200c04050a060528050d14070332 63
    0x20000c41c1c2c094201c0c0b010b0404002c0c2c113190045e241c07682c400e5a5150600c9841e0020000c030411000842c15180120480785115181001001d501c1203503401d00c4009c0c034500005e1851100d0500096986804490420004501407003040b11b00d07080c4501040a4104018140f609650040008000c0b111020800d5075000d000600e03076070b4440b603070a030720403c0d02c69a103203401d03500c10b06898604034101c0c0c065001e404181101e40e010800e210b4415420f81e0340b04807a02c0c038080b00140500c0a20b01030101c3c54010b000d4120040d0000c9190341e5204825070658000380c1004012a46003c0140442c0c4129008241d120707856001c0c10040e20210350000c0c000d002002000c00c10741c81102c601e2083c0c02420420341d8001c0401030010440781c0782140e00840200b5040c08dd20f071252051100550008480f882881c80c400c10340211203004901d04010080c084c40014022070300c03984100701041d400c00d010300054001310b000d120b03031024000300444600e0392100007024285400e001442d030000420300001d243c040407841e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 778583516 1250 778582266 778582279
    0x1e0f0b0301030c0303141204081c0509030415030b03010501141305060109030807031e02070819151503210e01030e07270501120c0b04030b0c030403050f070f110a050a0302 75
    0x1b04440d00b0883c5104680c0c141100200400600c4200402d080060403d400c5400070040c968210405c407a05131441034441000c80d0348240000d11081030000c800503140001820001154901e00703000c01e003035500c01da001482058140e01d500a55013010342001814402c02c001c200514a40340d0000303840e0503014000980342c0c0c07030007103110420503004881c4a0f144e0340b12102141c00001c0c3c4004004e40d02d01050084594500036642031084155500e5420880250300291240c40380000000000051003aa0910418004400c5000000c206054684c0907619200c070003086556084032009010032280001040c1050702c0e00207010704074000881c00030243c3d60340110245607400c107550601c02c43e181c4000c521208601c0c0c0000042e440c603907000000d52051240c5070a100b0a0359032075100001e80924880074164440c01000203036540e4081c4025a801032003824450b0070115080011811500100700c1195000c014071015001d0200310222100244000c54485200724202070225440c403c1ea80700080c0241c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 778584766 1250 778583516 778583537
    0x512070c02060702032b02030c030714011b050a020c15090d0c1a0306150703201606170115051e0f0c0304090e0a0309050105070c1e0f0b0301030c0303 66
    0x41d034000c01c0f80d200d59002000c80301110000448600742c005010005d00c0001d54003180110007030700100681d00b0000000002e103081400742c3d00e543c0c07400d00c405041c241140d503071003135110000d404000c0d1603080c070041c40d912541c44002d0100003910f41101210740c0d6115000c20642003441e62688011201c07802c00644a40400098510302040c510007543c20a00e07040001c21210046500700c0c0c0d02851203003004403844448551026210a014880d10501a00141010200010344449401c100181010000c11074050b09031b09000d1a81400480e00920001000d0310300000b903144c2000200f074054450030945016002920b040a03065104035400075840c00d441c2c070003850300b01010000707946018207001c0d02d0aa8603000d054a81d034a913407250050300580c6140c254100c10117100091010300e5154580c40c0d40500d141400300558458102c074000b1119441d5406020422078a2008045c12a09145221452040c24002c82c0341c246005600000d1004006000400101e007003610a403048981600b00b060554 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 778586016 1250 778584766 778584769
    0x1906030c031b05070312050c0906031510030c02010b010212030a0b0a050a060302070209150904030305040807231009080a080c0403051603151e0b01030b1801150512070c02 75
    0x10701c0d8803882e2035030036219030315252281074100c00109071582c841e81c4ca4800010381404220126602540c207081c010000380f1400015081c001e00440d006164003403414440c1c4296000100380da141d402006c0e00080c1c4408520550940900580100350000d00140000d0003a00c40d03082ca4a02006103d01750461b1620300007a0305444500c1018040c10015180401c41070310364001402230741c0304403802c0b030103140901c00007021903880c1c0c180250080c0c001000941ea50300c7d0360320120058400a001a07400850402046000420301040180ea90381c4043c1e02080381c01500302c0c0d060800050303600341c0355014113141c400740010f0818401c561081e0f5043c00c080e001a1110030b01046180140d40005002e8801c849007240703041910f40600e02104d210f582d80c20798942d08140305400b50b40d0000f2601075034443c680070720007030b802071500404840c290602d0002050502e000000e101d0440b520084d620780c8100c103006000134075507041a500740446a0504520f01207812620804101d402050502008089409502107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 778587266 1250 778586016 778586021
    0x804090f18062c010203040b010503061e060117040609030906020a1e080f0c100f0e06150105300a2703030f020a030c090f050d03031a04020a0f08061906030c03 70
    0x4440002060908511403d034094004e510503901580c01400c81400002c1d5480c0000b0800d104440c0c034011034000560240e4150b40b500e0001d015503052048800b50500505d4030b402c039040c401c90207900003090008003801c015021075000d400800441d00078000140c00714401d00250082c503003903d0f54240b0080440e06103e0854000e03001c80c00500ca1000a1052030245c0000ea12280d0ba00041d07010070200200591b00341c211210030f0142c6206411070170002c1e401c0c1d03c0f0b03402c850213074840c1814540e290054042c82842c080343c161180c60616551007180e0710741c410310081d0701a409844400c01b00034400205c200000c1c180240001c3c80712105002d8204800c00d0b100340c10000c40c0704007080095442c4c904c02070000d40904820b80c00600007030850200010b00742d1194294400701e82001d0b10f001074580c40c80c2c401303d02811031000e02407005a0812140002d17038545100a10315072030709688070110100c100f00010500e16001d050184100003032104100320300c0031a1000c01c100e600c02e0800050410200320160003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 778588516 1250 778587266 778587311
    0xd020909010e03070807050c09010e1513020c031218060c0307030f02030f07181802071b0609050a080a0209010e130f0309150207080319020703080301030804090f1806 73
    0x203443c00301060500410160f03001400f070144c4200e040d2029032280c4c030700744002100b0911500c2c8000707002c00c000c03c2e090041d00030071f001400c0c03025250b004110110058101a82d00120b8982c0c047e030b01c00101c81560b1100c03004100c0d08900914120b14000d40103c4410350b030b6800140c00c40d40803030400000b0840d0036011b94807000000642c42815034503071410103d6211000000c41c0c5110100d00304500ca8460891070382074200a98103004941100260a800005c00035008407200721842850004010171b00e101541a590040c41c150381c85842407403d2906005045a80da0300203520f990268038003a00594640e00d041d03040d0b0389480d0480c0c509a950040c685807484100d4400392141d01021141418540e112080e0001e80c0c90501c00e0341087c000c02c0104903070302d202c1d9118010b03582c0c00610250404d00c2d01c5c6041d043c1502e441c1e10440e02c606440b5200c4c1c2440d03a00a9100300c40d41d010002e02008030103071354020354086062028041000c080b10521240600e0b0780d00d44010111641c9101c1e04080001d00c210505 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 778589766 1250 778588516 778588541
    0x10e19024e2d070609150306031227080102040f06020f0a0b13020411090a1208070303090305040302100f080709140603040c08160305011107082b0603110906041104062303041b0806060d02090901 85
    0x180c840d80d41d6334101d00035409405410451501c81c40003140c0030f400050b0300c40c1d42000101c01441e15130300e81d0321500c1300d5400250a0740480c1c0c0342c01c520300b009030b034980c0561040c0103c0ca1001c0b030f654240d16001c11500b600f00340d020080040200c1070101c045074180058400d40703a01400c001c0380c110081d18045400341b1898100a62205c807607100d0300012580704440a80c00b106a844208841c4c0320704600f40c55070585031190001c10148180d101c440f82c01c1c080e0246411078440c030403410790f44cd1107000c4c0c5414041c0d83e400c07078185113140f00720030414843c0034051504103c814040d8546445d95030b45448440788114801c00d0300c0221082800740d90246040205000000422020030007580c503450244415404040c10f184607001d0a07002c500145040d10400d0700c440010202c4503d41407400c841951030003256441c10603550141360344420409400c2c0000d42c030641c4034020300248040f041c258003c07080840c1d000740300c81e40d000f107041089503100c114800301d44540484025980741d440c03041050150051001e0f45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 778591016 1250 778589766 778589837
    0x1e030218040207050c010305010e0105030a080715020c16052209020109150c02093402010603050d0c0212010e19024e2d0706091503060312 61
    0x32010f025005c9203c8010301c00998040c4031590b0390b0300000240d01c40130701441e40e15070410580d1000240c00200240191481002020313403160b0702c602c41000b26044040106540c3d040744804110901208051030302900d41244c40c0c81458040d905034285101d00d03500030b0346210f90343d001c00505581c040c0206400030000702402110140500034018080004d541d4201e0061440c0008a401c5140a0a05001c03921121a0002c07004823154080140c0401e960105400d40d569a01e010020820030f000001d10040b0307a8a8141c0c3d0328201d8414071003410148000c1c1d4915914010000d916094082803140101012100c02c041460751800019412038542c41c020000982c0b030600100b00d8591420020341d03c08622104000d82c3ca03803094201d40f411002d800100031a0007860011004407402c24480002da481419036154004018a10501c0c00c4a540c0124006c150511000c10140249803600f2907801ca0314682070003614a941c3d92154030001036503002c414040f464800440812815900044c403440c410a003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 778592266 1250 778591016 778591027
    0xc120b120a050313090b061806070b010605120a0e06180f1f060f0608220b04200307211109070306050102070504060b0306040903050c0a0506161e0302180402 69
    0x2540c1c1d9100c1d00b101361400c16441d80c0015550480d104402002c03c0240034035150400441d4850144900c6011169100d84148040804582c2d1a030056000e4401612103139920714201a2807051030f4130041c41901014240860354010003030100719503400000e00c4481c5420240e1001c802418207000c2000075400d1320410342114040103410707513440382a1190b40006c0001544545020303030180042c1c000c0001151400000c03134000340c50b0b8124900030002644884042d2503582c1e890016480080d030342500d89140c2508000800c2403800015840c1800c110000d002c41d5180500d20001000703291481c100c2180c495907071105020b0010840000d00c01e000704102002c0c0b5043d203001d0010401c03402507900600c1401c0c00880e060400d031041005892199544504654520b01000090b01001004408228083c03000081d00802009400380c0140f003040a85498641946e4000030103458282c90002c003c1c4a211136140700c0d000081029440c06d06e4030300585d035401c0d075801c07804d124040c001071207030480c0c0700085 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 778593516 1250 778592266 778592273
    0x9060424140108040512070204020f040b0721020c06180306010806040b0a050601050f0d0f0c03060945021c0b070806010504170115120c0602010c120b120a 68
    0x1503000391850031074490400400480116a404022a002403803a4807140d4101c444005500180240038402070001d8a8050092107425594119501c5145110804107058080010384051180c400f00401c2c101020501d41c0ba200079610310301090f00501900d000030f02c5030380204600b800900c1420010f42102c804d5691101d0880c0d544404444c1568020204008150f5421144c0102409444141c1d01c0c14184403102200c0403040d4081002c00c000c8594900070000700380c025004140e81d0000d0b0b5100022080d01e00030488054500b844481c0e41c0d12050543c0203840c1409140b92034241541072000036903440150710804000c1d18000002030360101e05500382040105c60048555511441000c3d01416512641341c183c410300303c02d03141180490404d0001303108000e10810841721079180440041020b482c006880a0541d8070b54101c10a00407554010000380001e0751003460040407a48001c0011082080008014071204286484180c1d1034122031407065443c0e0401b02c0d102d40c15402501c03000c060724507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 778594766 1250 778593516 778593581
    0x8011a120f010305060705070b0610121a01030e010902060a030209060705250512100e2506021203010e01050d1106030a0c09170703060510031e0203100e030702090604 73
    0x200c00c648034450000006c00240c8504195142d203070b4086050011502d502c0104018268680310700810445614821840b864080c010603505c60509400780c000400f0000005040e41c1c40c1e4141d261310381c0c0c10441d80f071006072a040c04440c481d0b48903207130041e124620940015210f124040c000341251054000004551a4105007818010b400550301d90b1007540d1030043c04402e40c584105958540c1009001d0f0703000f00411780002040c40d000c6016100019040341c0280d5a00000d0041e001d1134070b41604042c056141c0400080040e0a401140c10b425507143c2407030450560b0301400756074020040428407034204003002c3c030340d82c540b600300502c01500c03071408002c2d80000b0441d1200040004500080c006407030b40c00b040014204110420140640c0d50460320b81e60058080580044100050300030000041001c900c0c0305811643c542240300b600f400d10303004241c030380206044124201d03803815900d041e0901c80001150714080d81580c6142d00e95075903200040040104c0c2d905114100210304402603141c0121 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 778596016 1250 778594766 778594769
    0x150e10381801080115020307020f031c020313060810030305161e0c050a06020a030815091915060903020f011403130302010e0a020102152e0501110d08011a120f01 71
    0x2030381d0f40015aaa5841703180741c4000c1c0f0340503800143e001000346a02500301500b600b0f400302c801508440d41e280800c65800d440c2042007200c80c0058001142102d40003142d2140340005066528181c1c0103402e0847d00c000c3d152020340300003000d2100019211001a101412207841160041000c4d040070b4181c1044400d103812184003100c529520000118041c503140d91080c00395000c0b0b0b401007016900c540d50555050801030441e4002d0050450700c4172503941e660b0380b00f61081501401d4101d14000c00e20000098840000400e080c05103500f40074040e0035440341030305044a80403600c5400942410740140c034400c0c000403448901000000410600210a81003541e42031702ca540200200207000030826102d003003040000340160405100031a106003807103c0310703400540181c130b281145061040082c552059010800e5448000200f08014030b44c0c1200144242c64000c40140507030f040d072150000e0404105000f4500140d0401d43c2c40f40c07242c206901500c54030400c4260064884c02d201c00e41d100001c009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 778597122 1106 778596016 778596019
    0x417070b0304060912020f0a12050c0d09170307020f0907021507030c03050124031e11041a0f091c06150e103818 50
    0x348000e5000d50b1103514000340c00006807918030700203140700c182c0d802035400400c08400c81c10008910380e412039500a40c04071800c0c1034000d094520f4000d40d01c0584603417007405940d484d2a038102030031400b0343d008105030904407520549010b030341c3c1c480c1e2a4003e4100410142c3c051390703401c05d4801d15800400900548010f800c80032a5152103400446c0e010740082d40381c04c40f900b0003c1d0035100e0741d07024000319229243c80f046441214210105c886140c0070815a562241081200710b9618540b02c0c030929180520459002c1e9507008440d41183c0500900788102803403c09100c1109000c80e04e90440e4034541504100c000350030400302e110321214440c551b40f0b8a12924000410b9803081105c0300b11400706c0c1501c003a00300741c0d0342807132080018007412f03032121030307034030601c6800e85500c2c010005092907260820400a1a51034400e81c0c029011558804400420507000f101080314410100d881d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 778417266 778597122 := by
  have h0 := BRFrame.cov_init 778417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 778417266 ≤ n) (h2 : n < 778597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
