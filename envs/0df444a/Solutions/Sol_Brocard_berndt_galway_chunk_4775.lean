-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4775
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:41:23.039962+00:00
-- url     : https://prove2.me/submissions/a0b18574-6e1d-4f4d-bd13-006be820a600

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 858633093 ≤ n < 858812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 858634343 1250 858633093 858633101
    0x207030e062a07060203040b030a0b030601030b06090a0c0e01050702042a17060a090f0b09010e01140d021e0a030b04210503060a1703090603040f0b01080f1c05070b0415 74
    0x40b81c01001440d495242ca02e01035281d000b0b521905900c680e020001644110340da8014420746100101650040e41c4c5038689224480c0040e50698000c24900d800601e60841034032400210808031f488a444141109004685aa0003480300320782180c0c0b43c41c0003101e003105101480c6510610060410341c001e410810040202d4210101d9003081c246c2c0707406100700f81d200c1502c404c060307c44c8008086201d02c002800400030b0200d460034143c115030140700006410480c034000c039040e940d440b04101c0142c00080c04000f11a400708601a51080001180806010386400c02082c2d0110142540050320341d40d455440c040d8030102c0c0c2c02e45d050741190700300c0c042d05580440c1c003e82150080c03e01ba8110f0410101141100449025603440c0f04140c004074034030740c4010402c0d2400ca0348014a81b580e01d1a291910b0400c805003080c0c01c4850394440400807070044404114520001842c00081a410f6000f504861004a1440030101401010041070001c580e44c690000e22440c024990b801948000b01d003140c08131 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 858635593 1250 858634343 858634417
    0xc0403020306071b0339020f0d0503030f0a09170c1c0c02040c090803040605070b15090f0c09100f0206010e010b220f080a2901090207030e06 62
    0x401008000804100352401035040c0d01072071300880406400000c250354446c10030b4008a4041200110b401b104425a40100390601c29105000c00c81040b005005054805000c01001c80d00144001218040004540c83c0d02c01f0300108080fa412080c1d469501d5000b04c000c045c410a000c0c0000c0c0015500010851082600d80c03101c0e01c1004d414a150004020800c9980b0084c803858580000e01041481001303048040d01e032560650348d07915034403900902150b21a81c012101c4155141c0080ca00070100b4074810410a806802c1d0f000c699140309050116441c00cc10500c525903050101e00140d85416054605824460715118203410a8410280c501601603001c43d8407000100c006005441295065500c500204010f80e0746407001841c140c7e001c001e460f00f0000358660400c000181c9590000b42000d8a00d0089140015050040300d190395002e003542141c4e01c02020003001007050780c01550040640500070314000803900d103400000740a6501c0328082160013a81c0354540c1c40c1c600042c1020030743d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 858636843 1250 858635593 858635597
    0xc0901062607050304030806010e090735060d0606030506011404140403120c021c0917030c0a03080601051b0304080c2e120e061006021b10090504050c040302030607 72
    0x81d46007001c002040c6100082004040103c000007050050b40568810005000b00400030100b6290052008040040305003008141c0103003420448210554095100301d80c8400e101c50215076500c06e024040c89500c1032104881c03160f5210000404940c0510201d4041c040c6201d807600fa0b41c5501080100f52040c400d010001420200305200c0060380090f411103031a184000003003502d41d038946080c0d0500220b2316044402450840400300c0d0294819607030400e449818003403419000d0154041652030180b031803441240e5101c0c03100000442d006040942d8490014501240341000c1900242540c940e5104044c103554008502802203010500c00c1480800081d1fa001c81081d8840e907001c829a6203c0c1d641082030035103400d1480ea221701c9002e61114103440315406022a01d50044030a695840c2190a00d5020720401404540303d8400b003481d11158100d15052045a500c150400128140d204006001d100b180b4100040b1601e85004803880b65802002154440785103005041c10410020040700c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 858638093 1250 858636843 858636917
    0xf110a08010f09021f120b0a0503010e340522180b0a02160807020409080c0705040c0c050a11220203010f050103021207110102120f0601090602160e04050c090106 71
    0xc05d82d4402020001e03081e01030008074100c01c1c80ea001c503061a14a800c07039501542440c8800310001d50000300310100000150070003080b00c00d41c140c4201a240240d243c220000101c074002c022030301e840d9002075442d000c0800c610003811103410000d42195108114104000c3c0e080204105000d03100c14042c0c0e000da183c04040d0301d480076120000b2401d01c846040186984004078005040d0744469000c4c0440da503001415070fa5a102c004035903941c5001510406105a04000d82c412041d8810700f2401403143e88a40241811285961181001c115034607510390400480398480000c1c5542002043d03150701d50010069032941414452507032214150002c9051500400c92014049901c554140e070104603860114200002d251072140603104400d5032220b070054400900c040d80c05810710483c0100d174240c0b21218160b540d82d4050b6112507503030002504821403e00100010300d0302419081c0d010f481982521507042c8007200140038850b00381c0001d000101c3d455944400c510840b420349404644181081c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 858639343 1250 858638093 858638149
    0x1206120b100b0a0c02060708040f0e0a05060a0e0a2004090c08060a080a080c0a06020301090509150606090f0105160803010f061814060903010e011b0801030f110a08010f0902 76
    0x250004c3c00340e000c02405400b00240070400c0c07000c500b09880c0039042004118000d42e654025070296050140c130030342e40b01d900c2c0c440400e07000d02d0103802c2001140c102400351011a62400340350342c000d0202084902c10007450041e1020301c0c400100007000a00300c0d0000000304840b040e0300c01050700c80020003603401112036a00a10120384001011142035601295035a038030002055070500b0f148240038010302407070010001040d1805150403991007180c01c0c400b02c0d440880381000600303c80c1303029a000380d04000c04208032444c6080c50803d18104c1d0f401030601d41e142130505640c800a010000d101583c001c2e0340400140070440840d24040b00070710382c500d8403100c42c0b104403540f050703036a50700d1242c0800d4103078000204001c0c1d290340b0f050f2a003a03000140200a8a80e02200150107802c000c61031841c01401d411040c804280582c0c0d41318180d0360010488983c005081c0da070f8076140c1017003c3c0c0341c1340e20040310395002400302e2090040420790314084001241e02d80041c4140074000e00154240e0050b60781081020b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 858640593 1250 858639343 858639347
    0x1090b030105060705070b040602030d0c030b15030601110604060506010e191e031a04120507050318030c0d0c030c05060c0c010c02041e02040e0c070804061206120b100b0a 75
    0x10301e055803011908607946200751300d400303803415081d0340c00007a807030340082000140b168000c03010381103468400c0c5c0c1c00e0100103010300c0c040342240c0b0000c00c0f5541c404ca031481e4403a0750030018400f4651080040c140075400c1604461440e01c0c1c0501182c04840030341e220342c2000420b503400300508003d52010b5400e110b48407a03e07070b1500580526402181d03d035a0404050020702c901d5104402e0095400030690b805600d80441c880c640900308807401d0b0740a41d452144015140d00c1007046803030850700308018508003048800707111810460b12140e00d034581b140036002c41850f910030640c951040d1043d030107425868554a000b0b0400040307a48034610510003840010401782c004184408a4a400d1030091881510740c40060010f15145071049098051001c0900068074241e00404c1580e28900d05101d25a07591a40107002c0c0c440e00b280140015030a220401070a4004c55807160310102c8040c02141c1107407100c054907072101c0500d8055403200e1040b0240306041c040381c86488003a00b0700e00c2426241900c0e0840c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 858641843 1250 858640593 858640597
    0x50304121707030e060f01050f06070606051207030c050105120f07020a0c150810080a0210030603020607111003050906130c0308030c0310090627091a070e01090b 71
    0x3402038030380c008140421501c01d016020001d808101000781600784548001e009182607043c1803024850880880c0c0c134a040240d0803412140e005100c9803000c0c44120900c110b6410201040710381a0f00c5c0c100111b02503072070280c5282100c0303c80c801881c00700e03c0c1d4100130202445a910031414400c0030404803400550104a555200340510f03100d100d60744036414104c0c608010300c00050f001c402500004180354600c0d20703c01e84241c0f4107642d034482c191550341810076180250b229080c46a4000f4905e1001800d007a02c00c00981c0c4c3c006d040000380f00c4d640e40c000c24040da101c0d030b2301115220807042e2907181c42c3c0f9002a00f440c050f1040d1070104094038203488460b5403120054191200f200f4030031a00f40c100300505184070301943d8014401c0340c40382442c0c807100d106500150752080a03003240c0c0c14081401c0c0d0544c0700d03074021a0410030701c00384c4a284800038040d02c082203021021360551110303080c0740070882031291900100e004080c4c8060500e031207240201586175402c902410003002d150108405006401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 858643093 1250 858641843 858641851
    0x1020a02101e0b0f1f0e0102060f0106030e071d010e2422090f0c05030a0506010b03070903060504050705091501050405120304030f0c181e0b040e0106090b0a090c0503 73
    0xb4005000703001e100005041d01010342410790f119129a894920039801d1039503c81070700fa00f42c0c5840540401e510016612003a048031841c0b4540d000000400c001e40c031980040c1e01c0004810103403404241c82c0c0c5050403510880540459100c1c0042c4010003003c2843c4408507400522107100504440c2c401e040d0b07800c510034401d4694440d00c0d4101c1e4483e02c03c08408a4401c0070088070904000d510520b1501e546603005a000507544207031140350003c0c0e1802c0c040790020b40154403a0113070442da828042100d2032038001408420412044076008400111688a154040e030b01600080414910308401c10202c1d0000500701e08a240180300d06200c40d0b41c010050340d0985400b01c964024810302c014003a032942c090382c0c0c409440b00d2078441001040c00386c0b400c0702d0801d60340c5400f0100e10081d0b8400759070301961035594140d038035030f080f10992154040722a072040032004c10003840450407100c101c41540c251a1183c010020143c2c0c1e401400c00c0c1480e011001d075000b806065001d0040500340c60002d000c40c00300070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 858644343 1250 858643093 858643151
    0x506031e150d060902030607020a020a0e04032f010605150d1a032a0301020a0c0f0c080d030e01150f1206020c060103080712082502030c010e01020a0210 67
    0x28010800407000000051000036000c2d082404901e110704101020f0300c00703103000780e00030302035000804c002c1d51010444403c02500680984000c3d850b00355841d00b490001481030303007003100310843c288000c0c110700004203919007020041500082c2c05020700742150545d80c400b078490001c8030074011008910006403000301083c2500083c402c05600aa102d1040d8500c0400b0340c1401401151030003804025100350021120800c0c500c2c15094080505080780720315080e01b8007046009801d44000703900b6400003210188640070f1140116543c500c44d0785000e0082d0b5641b0046030701e07071f503801c159003009103d8007180046549080401c545040d55015003016103009251030300b4490f800c0b00050007a2034044071691401101254111f40c4d4170700b80b01300030341c0020308221081400c143c07800310605d110b0401a4021181c02c100a007440708400c50004007600f6560454041d40000d11000304950800c1c8689800013003458000f60741e590f00001c00900303143c5100c0108489a20b400310201d040d940310b90900001500d68 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 858645593 1250 858644343 858644401
    0x703091217220804080d09090501031e030c0f030806180c1207180603051024080703150b040815090c1005040b070c091d0c0d020d0803090115050603 65
    0x10504044820a88980503043c540d001070001601c000020b0580541da40c940d544030f13003403030721002428140d6000b8030001d06040c05450500b40d116030b0b03403080405038a04c0b03402e000b030403810382d80e48004110540ca402900420310074810015642400c4003c80320091480314603116528144500c8082400b07000b040d9000b1080d03201c0000c5000780110710410030f040104801c4030b00c0c240d544d03100038003420044801c00310400d4030400c001140f5903d114441c0c5480b1160719003205d0007014140c1101c5c4408000c01d14000c0540b2410300213a03c00703102841e10701900483e0a2260348a0a04c0f41452801106887e0ac22080700d1103002c00041140105581604c8001140c00c160b0708418200120303071501a541086009800c00100e00081110012421041341d050300b82c00c0c400920710481640724004410894034040d00440305100c000e1902140078841e0500c014201d0243ca01552105942a00103c5035220320342e540d503410351312405411480e0741c018003049510724590700e01a06030084407803242c40080a18280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 858646843 1250 858645593 858645631
    0x206150105070b040501020901090b04060f0c0204020d0204080102091f14090a1a07061410060e041112040c050d0c270f1514092403060703091217 64
    0x3041c001c864200d500314052002e24207150600900030340c1304400c0140418411030001485100640654003250f4040e100c81005034003581d001e454600014200b26030060f8204400d2070600080d1000d0006843c040b0001604c50310342c003043c0031101a0001e1140c41e451000082c0122840d0b01c0040da41700310f1a41c41d0019102e085003004104070300d5198110f038010480304130440b101e80c41070001411600303028413005d104a040300c0c01c550412510988085d66090b01040091064038019150008039110250002641180c5c0140041540e0401c1074140341d503007001024042800310194441000e0b00088601001d52607040e42c034011195003a20980c171003c410b40c482c000c61001c015088140340002c042c2d00740f1103412100b50140042c003001c103e0404600342c07854081a003a01442006050b0f1001410040c09900c407131402407600030b001110900c000100d40300c5255030781c5017446100d02401d159140400d02080500e840c180c5007403105a00340400400c2c0708100e0080e00c8920302e41d81c0040c11380181c0c800d0181 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 858648093 1250 858646843 858646847
    0x5061603020913090b13030801120f12020705150f04092f0915090a060507020a080703031806020109030e04050a150e100605130605030705160b090f0a020102061501 72
    0x10780b681940d07200c6595903035100d1924480d0052501c90b8441c42d40d003081590340e000c0000211200e2000900000c22540042c411002c412200c2919075020303106a511040140d03845172245481e91071170000580146108100600b09030105038900642c01150310b00301240300c068001180102c1c441c0c56100c1e40c41ea0b080807001030302001d0305080540c000c00c40d8080c005001880b07013219402804140c0c000c075041d200306075a110300901504d10300e80d030050000e0340392842c0c10000c60381e0f50007510b01607070307c004a0f244c0000c954038100030001c010751203030b00c41400d05010048024032950b52540000c096904002c80303031000a900001d19a015002110b0010307180e00d951515800400070000c501c540164814000300300c480140c2e03c024404c940504e5a07419007500c03148100e0300c1d401031034203c11444a0303000c1c00380f10190140014607030013a0b030340c41c019040030090700d0001100c010700d035016940e0b000c01c071040c0194603500340441f845441002c402000321052550000b596a50000c000d5400401d4408082c440d980c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 858649343 1250 858648093 858648097
    0x405040311060708010e06010903020a052103030108100f1a090a06090c02030705010e010603030221131403011b050417030d0207080309010c0e210c130f0f0204030506160302 76
    0x40840c008803150b0b03240c503040c0900011005e00500c07903441141070026200d0342c8100b035003c003aa0b601800c0c200c40c451601041c000d14000b1214044030000038002c0e0704900314020000f540c0208172010003032202e608008030140c1282c2c1585021000d9505046003c117130b141e040328010401070350550380301d455a07440741f004800600b990703040014542c1c20300500d91000f503030020184c1101c900880082048641c0302d0b0a1600b211580d00c802809a00b21410483c00c0c254800302011722110400b40840c50050214400d0340318203555040803005054115064030281402d01c91103400c101d038942109100d0390003c0340035103613001f42c0c855910a003010000d0800310810134801e5500c0000c10810546d12110580b91420300380d042101c004000c0c3d803030700b0842c0caa2148100950044400007401d81e601c80b8494801c0240f20880c1d401c4150f15612490302048011746402c012200070740b020800014402414203a503009403610806500201401444184089000410182d402c840e0310203140302d0707001c0c00d035500b580a8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 858650593 1250 858649343 858649367
    0x51e093f03101d040b0c0d0905060c04080105100509151201111905120a05180d0f0f05180108130602030c0702010e0d0506042d050c09220204050403 65
    0x3040300801401154002220800c05950071a500094014801c1c0c00032200d00c001140d01418218034a800315505201c200c1c0103180c802d9260802140300e00040d11900e19001e02aa10310040200019041000d001c083c89140d03000180031500d15556494100000c1d14a080a42480350880720450448619640c02c07071100e00030404480240700040d02c1294620482d04246240620385401030010501c6c503216004884800303054160b482c0d07141d110000404000c00e0000d10610401c890040c2e01c0c01c004d201045103035180ca03255628840c01054165004010018484100082c042c081c001040e003689040d01c20392641d0020f00e000917043d80c0c0c0e8102c660694500072070282206100009000c1d60b075400f00e0040000c1c90003031300c8000355000017409011104042038001f400e0f80e0040f0300800e0000b4400140704440200d0641004926401c2e00209107000300d5500c4119000d6000c65642069800c00c1e10034141e10a07071340350b40c0702003144600b0300a00f414846c11100920841c0d0346c80000e0b00b0180110401c24403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 858651843 1250 858650593 858650713
    0xb030d30050903040f0b13060302090a03061d011b090302040507090b180102010b0a0315050612032d0a020a030305060d0c031a0114100819051e09 64
    0x35030070000c403a5600d9600600490280c00d418985c00701c1c0c800c421300d0442d0840100c02e050100083e10b4808220000e401c0080301381c0c0e01100301080000416918020200304004031a0030b050041d010704035030b5003140e81200d080380300315144120080c00290040a184122901035501041c541c1e50088100c40a507103903004400c000d01e01060040140b605040f1040c5542c9080e0000c0004c1c041c0002008a089214440240b056040c1100d000d150b1b80c0641040f60000406400c0062100005c1c010a0864000601400b60605000320140c100110741c14640e2131051605032451401d01d403070f10025103a400007400a410326440b034000c16603944a601c801ca80700354106005400c80f0741c07203180c003030804481e04070b409841101200001c106080002104090800000c1085501d0000c520043d03544402c01000c10303803881d01d0b00000c40041c0310240a91841030026135240d0300525004501d034550071358090040d000650280b036041446040c2e481058800d4040040f0745648082c07030815049a00b000b01c02d00e210 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 858653093 1250 858651843 858651851
    0x9190807030f090f1e08061f0e01050d330f05090d050414010e041812030e0c0922061a030c0906010c170a0903060b030d30 54
    0x5212006000d030164030720950b14544209280714048501c10b11900494442035034200b004c1203083c1c206a41408080f40040350540410342c0c6025160030140d080f1148410600c41c0550000b0130b150319030000015201c03542070fa013629410709001c5406a13000d00d00040030b0044080101c5600e8601c1d411400c40e1401d61014410032410400011021b00240e6402050307503411324001c1080048041303480c480e43ca8466840b18101464a034080320b10f4210506480c0c1800070800080425480d207000d0484c4040d581c112104004046240c8002042d18845024041500c1c104111940c3c1c100840e0460303139081c0c1110a030784142c0360075002070460004044214200d844000e1000100300d8170fa00648601c40c8000784801c5803018000c24540c4032040d0150841d801382c20324001a01d55801808442d602d91b000d40a124044118000d0801207130b846210880b011400305034041040207000c0c0074040d45d0a41c1600540306030700c020100588010700c03005081c00801c1c0c01d0307039010115030582013504034212070440043c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 858654343 1250 858653093 858653143
    0xa0909060902040c0201050402010210020a14190f051305090a1b0e030c03070e011e0803040306061401050f120402060c100b12030a20010212010b0d05100501090e09 72
    0x10004101c6810224055810400002c00b03207401880b40074816030301a0050500c0700f0308031051000951080c1907105c28820101c07481d401244043c0c7c090198004092801c3c000341e0b00700701f4060b1100d50302c16484420032030204900784c800981c2d0f07030301c0f841214000d64403a480d9440314000003015042c0901000c0d0601007006200240d9135114444203080c1c2d800390152201c0c448110113064642c0c007280210403980440d00c0c01003082d0344541424000b81050002e00c001c8480e114100a41943e015074015920720b600d41c081480303000700c6800c0c41c110714802401c00b203141c142480000b64160080c03040500003028814005403d41d00e4034800c842039035140c003041c1c9203c65071100160008101c1040c81c0d50150000030f044d400c000c1d20000403591108103544031901d00c80328049a07001004080b45030324a19540900900001c000b45e05841740c081d110100c03d050f103c07841c604d050b10890b840100086009929030b201004540d0f0008201c038251841198424625a100b00941c1c0c50540208226011f8a000030003074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 858655593 1250 858654343 858654353
    0x30d050705100c081e09030924040b0307170106120f090204110c01050606070f02101b110f04150614090607050a0201080c03060306370506040b09240a0909 68
    0x3280c85400e51084071a181d1000c40d42010240385d01b112900c0c0700c0c2c0e000b004442103d20b040c0c501c058041010b04803050195005040030038094001d0380c42401503034004414840ca0b1a004004102d000284c1c02d5035502940c5000c000400400c51076440e002950b40d0784844170030750003c80c2c0042c280c8030340140c0140b260440060411b13515600c20000f001c2d55520705400300301d961401c0c000b19101035030095191881035034282c081041e0003400e40d60503400d0100400040f2062010006890391003805543c61002e25103040d0140400500b011403442e200700c0c03070701540e074a07000d40780c0000005460603894140c100c1641203401017642c1c03103000c0500754401c60114541c010803500140d4400402d01c00e0383c400800d0b407101c036070340c1f507031400140e0354540d040c5c0107000040d1fa19450103600e0580e500c01c00740d080b1204100c1d000010b504c1200311010341d80c041e03211001c01c903580c142801801c074420b000703852a041500d007130521000c4007051240c040703101003907032801418696551032082e005046070003000c0004440074908 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 858656843 1250 858655593 858655607
    0x30f0b12030904230a1e11030402010e10140d090206041202040c0c0807030807050f030f1b0c070b07050a020303041d160203030a09032307051605030d050705100c 71
    0xb40511540c20610050103101d2014aa80c1102c101c1d4500349800f52100460540a0710028840c0d0030100d9801500b01c8580e802401250100c40b90b289026590f420136000060403985801031050040c00c450705c12001c0c1c0c66020f914221702d034009004075515098592441d070040e01d020b103000382d0300c00e50110780810750030f0280e100811854400c45040160105075001602d0f4407a40240140030740348280140c0011a001c0c00440c1c1c0d003c0c5451808600d0140101c06a9007240c006032110021802d6103810084d084590905c3e0b0600a4050781c0d003107041038554080940c4e20079550080311801e0314041000c02c00c202d070030003c0d46503055004003a07986070368a480c02826000042040070340c6901d5040d02041c22044521002c0b107610000e035000e14955600e010541d4098100d5003412010460502c5500c06030404000f0b00710a4101000c958a0f074540c42400e0082c03402c100c0360100d2040c2914008200700702d40d400915180700700d0460402c142c6400a5081241c03c0a0742d4542520a807810150b041804951000c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 858658093 1250 858656843 858656857
    0x50709060501020109050d0e010525031d0d060b032d280206210114010e060307091205010906060e1807060801170f0f1c02060402090403030f0b1203 65
    0x80030011595518012030a8034041c1c0c2014106400186038120071900c6507402d0741d486041070500500d4500134080a07080d003510b07416417009040d210480e41c020142e0101e24403900e40700f80300d00c82c84801d00740b10004003c0039940c44000e040c0caa6810360710312581c4044c000041000311030f05400c42c034035402030ba80d20680406901e009a00d4054003205990310085220040c0b0400d2041c0c0c0e00c051011102d07400d000c11076002c3c1c450228620101d0004847c203280c06503040f4040c02d1040f140c00c4116021b1b0ac00501910707480190240f055405204000103039900a490004807840290710190280d10360521600401072840e014024a0800c08041101410851454001d01a034032201c0300500350b25031859212103240c050380000904a00c0100301c1d22001580c03140f0f105a0010a9512410013070442038a0b20b04007102d0f54016822203d6034624a60000b00281c03c140c10304e00203000545080d44c00a030101720700620041c241640ca152848a046507a8030822540d0005000030000c14812140b19540b0f8000c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 858659343 1250 858658093 858658109
    0x914090708030309100c0203070c0303050405010207060503090a06180b0a0b0111210901090801050126030f0403120e040e0f10140112060905070303091d0c270d0507 72
    0x80c000041d01c0800000700e84c8110b100f44003401100140d015014007030012821035500b10700c000e02071071000c04d030b5840750350004601c02d444655465260000181c107004056000c1010321400b40304200c2e0410020402501d51a80181e00051286001204103450300c1002c2c400350294803087c040100c0c071140caa200460101c400d03200c100c0c0740721015602a941d02500012007100026070b074000510300c256200030301407800050404440d840d46400119003100d00991201583c4072003aa030844001090030880c08800c6001c802952030110420440c044a21807480018002055841c00e20a4a1b1086080c405082c0f40103105100c0c0312455138645580c0c2085036080d5070f403030040d0140c14072201c1080c895540321a031080422183e0b80c1c070384051056a0ba41c246025611651074081c1c060010710b0510410024520940720070240070300307046c8120720a00c2e00310a43d00a07440301d01d00348144405d6210540d10707032141c1246c180030ba400d4540c040703100d40201404031a42003a120180c0400f00724010680c481a1031000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 858660593 1250 858659343 858659353
    0x2040801110c0d111e1c0906050708030c070c0e15010807020a020f04090c1e0b13180e1f0e010c0f0c032c03060a090c1e091409 56
    0x341c68003142a21440c072505030b0030350102ca05a007000b40034901d41412071507240240c5d03c1c1029803c0041940c11150b44190449800040fa0a010f00130920000032003ca8186000030b086801c001024110b40706070b82000e40301020104c001134040c40040211402994008040c0c1045070341c5220540241038117a8550003082401280030620394482c80c4903621401c0141e00400101c88540c00b40b0805016005a0680203034a44248101150085460b1750090540e00c04020341074000012408000f034268000c3c070364403142042003160b9040340794143e5060b0b076404e080c000d500350082e551080080100c2040030819008018002450444044d001510a1a411030a00c929801302e01110300301c41c801029900413401522861001520500e0341c696000c0c07103410580c3c00c00101141c00c0d04000c0e055140881d615602182501250606000894101c49168818000c0141c60703512410303141c8440c00341e00026903180415540c01c4454200c0032006240e2032030104000081801003884404046507042c42c28818 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 858661843 1250 858660593 858660611
    0xb03010603030e01080f1924030507030c06031a040209060c010c0914030f071a0c07080d140a080402040f0b090c03010509060a12030305070e101107080706050d05040302190602040801 80
    0x3040c0406d44600e03000b40143e21100840c40d0b5041c020115a0b2070b29401d0300030810603004412a540c0c4150141d4000d40c001c0041511b1071034011000180d81c0c011004147c20910311401c2950400074000492004a902503200c148003000328411f0b028084d0203400c15030800178000700068000a60300700f03848007200000103102e030302014183d848011501c0012107074043e0307038200000b2000c00070080c507040b5069070052a00145030020303854420070380c0048100e60494040060841d4020100b081980c448000040c1842a8140301801c1e0000c02000039018680302c00062640201039401480d980390001c011084905000542c100700e40c00c00d01616001d250300710003040c9289000d4041904841d00b1000300c4441e10a259001c401a0401070070f1801400300d000402d440a0792070364110b080e1400d580d501c1e440c11101c5818541e01d0007405500030095900700c1c5009000c2907038881c0403200c80d0f45412034041104d4a99250403490450907030900745184000380c0210041058a400a1085451501c002c2c0580c0130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 858663093 1250 858661843 858661861
    0x140a0e030703020a11061e190f022104150c11061204081309091212050c0708130902040f0f090605010c060507020a080d06030606140306190b03010603030e0108 70
    0xc69114041d0151303100b80350502c0007801e541000561040302400e06400c01807554680e0481c242100c0354403c2c1c4940109210040c288031004080407141c541c80e01c140040802a03010752a000da12090512420048030b01c00809001070084400070b0015440074100701082d80c0006103000c020748411190b0000c522030050b1180b400c1030a891004000b100c51140980f901c0e55070780d030f04cc6c0c400c0072072019a00030301c040090400141c1c482c9031101401642c1400d600003400307070000c1480c5842c1008606452500c02801003a00c001000ea0300700359400100542c0d54803003992201b001d400c507584408146400064003103414000440b0b6441100c62903410001019220f281c01030035240d842c01418005115010700501003a00e0350021900003610b0b0040d00c43c00300340c07a00c0d007041d03c0e84180040d02c1c3c1c980d00c40808204100c0c003441840c00a0003115200405d0500107000241c5950740035100c80600c40341e0070b0080000e00c41e164030680404d24003e000b045015aa032a010704100c821802041c0410b03102000143d03606 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 858664343 1250 858663093 858663097
    0x60c01090c0b04151d04050a0614030106080c060f070c080a051b0f040b01031506030e0d0e0d020f01200601150c02131808120f0c07050601031212140a0e03 68
    0x5901041c1d010300201306400221022080d11003d030b9030440709510755000f981c03200d200c0c0c14040c1c0000c0a000c240d45080c070043c01c4a040d075400040f030084c1c1c50060100407000d000300f0b18440e40380741211041ea803058946141851801402400381c982c00e2072410000c3c1c0c441d000102074910ba403103142580e40741e4541c80c0c004101502c40c412640e0700a04141d0352442e640c43c1c16884022051014140003600c000c41b4642a19101c100b50800c00c0860b030340d043e807130081c00380c10040c5405d0340b0321310703d05401840748034800701d450202c0303d50000303002d055100802803080e0b0240f03a401c443c103011060060880000703941816a110800e105900c1e51940140580300c0312440740700c2c0d05200b0fa801401c0c0001881d0856a48030040c904980c5072512516030051090000d55400014080c810b9900c00c8c0240130b0400c0800800ca038038001d0500c00c9844030810110f000a4004100c00b81120741258040c0da0b509030210041d14000003543d084032521b46014004030314031001c0b000044c01118105001c011100b80050003070750324 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 858665593 1250 858664343 858664349
    0x13170702091f0b130e0a090204060f06050d09080c030d0b0f0d0305120901110a031d0102032a040b030c070308101a0c0a02150d0b0a0308090607050c060c01090c0b04 72
    0x1503012a5428003c0090060081240e11040c0c4041d8030031035900c0c006a120030b2001d6442c200a50707103403202d10f1700307500c0d140c01070102415102040034002803034070380090500c0c40344104614005848070220b05c180000501660400c10015040d680da4010070080c030001041080b64151003100303801a030340100e0030101c00040002e076060f00c1d540c1c03400691014205480c0c2c0b00070202038a0759220303251016640c51803405030021010f43d88010680720407410201840180c3c1d0100c4010981c410310401401d01d01c8500502825045200f00b2419041020300108051041e5040310010741000418883c00d020020000c01c00300e0f000b56034200264542d03405140c501400c2c0d110b24000d00004685a003109a00b0200401c80c55212004951504d030301927001c241d04091a40301c1c14a10386011038650805515805003040c914070403500c03401d03000d065035109101801200001805400f000c50340340100002004a0b00d1001b20040650307494000041c4507038082c00ca0000c04030341d800203d820000d02c0180c0c81c010f80f015 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 858666843 1250 858665593 858665641
    0x90503030712061a040608040c081b09011a0306150c120403061404051218030a0b0106020607030b0616030201090b090c0a05150a110a1203020d111207081317070209 72
    0x1a141c50180200c4040360080c0c026940049182e2740012a214200300586541008488402c01900d4035005c1180c0854140d00083d83d10030b10070408921284140e08895010030b0488482c4600a180000c404486c01400380d107100c0c610070035407000000b00c1010060000c691003900184400f030005c014000824a0a9800410651000450000d80e50201c0094400c02004007000340c1d41c1c0e60840700092402800c90015a8003021507001402030300c0d4180092036010300c0030308060201450340004200c0d148035508808202c9030700d900703141003050320071b402c540381e8190007203810344240c100944104d4403164506007041c0b242d070402000082d1803c020070594185891000e039981440d4000c03030151100000e0500c1c80003a8020f0245080004841d50315070a01c09500303540040c0ca55043e2070309030046810880a00d2000c240c14006401d81440407912542d10003003910304184180c4802d40c156208011091004041000c00790f5412040c45101d405058018002c50f09030525031075116104031441086401d03146 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 858668093 1250 858666843 858666847
    0xf0a1713030b090a0503070b040c06090e01060302030705090d050c03010f3602100216050a030803070f03021611030606011b06020a120903110d0f0e0d06090503030712061a 75
    0x81402c18490341c0c0d2100f80c001c25603071140c2c00d0740e071080d040d584140743c02c90b2003c007003000703200510400001c058046d00f05410500c591500704440400ea41c10148201010960000000b4191510800545e8003844018140c1c0705000a189001e42c2c4803141071403018003030361900d03900b05520b0106008006604911441e000400590400d55803101d05d10050b41034001d1510400b00401070b111600c007003410b032540c2d41c05031914000002c2c60950b1825a40e00007441803564a6060020030740010440350024101d050085641040000a4000c1d01a04064118080214101c0c1050280d1100b030792012410480545a583d900d190043d1403c005510a50782500d5406c0e040c18001a0075600800801c9854200490041513a00d6082d0a03201c030a6000c80001e50381e002c00a4034540100110208640581401c032189110142c0040482114440b228440e60f000b20f6048103110265000300d602c550800252956845c0020703014003c4004c65500381101807501e01c0c00554956403280e00c0d5401890701031814 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 858669343 1250 858668093 858668099
    0x7050114060f010e04021e070b0105060304020f04021303050f070602010b031c08042a050906010e1c0c03060203151002010207170f0c07060908010e06010503070314030c0f0a1713 78
    0x41d0074200042c4d1035a0826800c02c01440f10103070020b190001c48aa1040b801c0d078075109407600b141d104c54103901c07660041c80c091040c40016590070070011204042a03030010f0301d6104c440c800c203e003401607600150184c0190080f0481544020030014244c0d8000e800070b1203000c8401c4185030344c4a00c4511a03000c41c0420464641c1528820343c456600b15029020b5481e00a0044031040c595002c030b1000c00301116080d0004219605090326030b203900c007909003007100000c41400041000c0782c3d0116406080c038403401e000c610402c040c00010001464114078215184d2520310318400c60302008010181c460000001403d07505071050088400e10b65000c42e0784590110040c0400b00d10381c002034031040f0814424840c03445000d404004a500a10550751307650000e91a1070b01d40c500b11911003200f4140c3d0b400c040d0041c05580c42c0041d8050489901900c0801c3d80b810340b0b40e602d0b0441c01940d621400e1402480700001040b0030018400c3c00040c010040034480c0e4140d18081c03010b51203165283d604c00c0444030f00030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 858670593 1250 858669343 858669347
    0x9050c040617061803132601020909150a0e130302060108070609090c0309081602040c03020f0910031d16050604032012010e03041a070305030417040e070507050114060f01 75
    0x321303040c100c03400301e81c205040703c0328000f140c00751a00b04102c80b000025003d00050f100d210f615800c403c1c200021880c1150740c90106595550080c080d11140404e44111505034036194083c20003003481c41c20701e200500b400241d00406661080c01900184180d0001090310b4601044030740c201ca809803920f01c01103240050301404ae045840b003940605030b4804026007c5981c5400604030010b0130f1100c030001e5081d40c0b0410040324003540301003081510502100c4000170300f841c00c4a1074040100c400c440c1d04104000d048010b4140c1c40024680c030509a19111581800020091300720804842800d4540b516082071000c58011884042c00700c00c015106120551500382d0500f07150680644a83c000c214980085400d460000512400a500c0020208400e520505010702c0c07203135003001054a0880a0f84001707000b40005000506032401e40300349104101c02c40380403580100207551000c080ea141401003e4040d40103a28156241d50a103c40ea9850400f0200c15a106c1c0000030703d8140545901001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 858671843 1250 858670593 858670621
    0x30408012a0908150a090215030702070801020405060f130911180103050709120201090305010c09180c0e09131a060306070216060f09030602040905071107030f0807020d0609050c04061706 82
    0x49000d000e80d030740b81486c0540c40740c0c942c40c5121803d0320784050f44c038182018003e240c0149588031021691040c00240314a603030350411150340e19a07048290762074083d40c9211040010003a480031803c9840d24660084d090901c102a10480701c0c8689100d01e43c841140040d416290100ca00500240d04040705004c40701415109015050040c900f50340020380f80e9803010700b1210640340c804003203084010b00b0451420ba80d00100d0710840115000c0c8070641b021039010b45040b5004031150300c540301041c001080858500100c40005401c0502d402400b4a45020100080030940303d417030082c00340350f00044541e0f00015075107c4400741e900b507401e449841c002080b40c18280814050b81000702540000000c07940c54005003000d030806400005075401c1001016025030900300210100f40c001c01c030200301040c00b0030f44941c49a41c1040e42c19035580c05620019481680300203000300070600e401c503450300b4410002500c110130b52050b03504000b419143c0d01c403014a03a1910f4415580c80d8401c00004100350b041940c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 858673093 1250 858671843 858671851
    0x1413080304060218090a0f1503050a330c0318020f01030203070314091605091608150d050105150316150c0b0f070f080603030a030c02030408012a090815 67
    0x1510b0a054514200085c0701110035201102c3d440d84600403140328000d6480782c500800000100414041d142d603031201e0703e661504002074031080ca07210b00e65540b00c00d12a01469030350b2683d980021701c2e42c58a0001c04c0280400d00985000074988400c50481023106005960301540082100c55851881c000460180d44010b110000b00364803812920002d0440d03060301400f03002020003801000d0050b19442102002e40e522051081d00450184010700800100e0a40f42d10241d01e0f211015a90f4240c10110142640c01c3c40c50b04903101d0910755090100661260780590703e0804100d840e0080c2100300342d65400c1d800003201d01c07401528020095564140c06544030b004050414181e45d0409886201441c00110b411020f1805000300700a500c99021050315038190076400d0100081c01c058005c00d540380038a00f1b9440c2850340d07503405109514002c10540b4010482078000380310b10104035007600c04d81140003448001d0f0008001c2d5031104580260b0300c1505840030070b4000c0180403104600030b4903010000d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 858674343 1250 858673093 858673117
    0x30b061c0b0a0305070510080c070f0c050a1e06110d05030604090f0b090c2d01090f090e1516270605180a0e061017090114130803040602 60
    0x420310721501e480381e2503480000d60040000e000201e103042d080c40f2403c62444040070030060f0850802c4420744208041e502c005400101d1680401c080d8035020041d0856600041d900c0310980e200041d0481c0850282810718030741d51201c02c011542d4003800d0328000e41001099044e90000031480e10002d1042000d140c1c42540200045030540d101e0b00d0f004100c0d105040e040d55801c10756401c000400708100080b00303041409480500b004001c50043c80e840c003d03106606080030004c0800140c440e0300c1442d07284c0103413013030080c0a00b107a651845100024001000d43c1e101e103000c0d030303000790b07060742000d11176244102580051400094070b55901210040400f4084178250803142d5044084078195801034809844503440f0941d40c2d11000460703030104482d040d15a48a0f654076041803004d81d454112480c2c0094084d6281c0d03458284441055a0940380761880703806141c0042c1c20820034940540185402400c0302c080d01845031603881d07084e42c0c61003140001800c80703c0b040000c00e0014030158020094030b080c0c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 858675593 1250 858674343 858674351
    0x100209041d0a0c0608040b0a020a030e0106080718020f0d0e07081501051206101509030501090f034e0915060b1e090411040603091101030b061c 63
    0xd07100004214000070359401e40e200481038400c02c4807a10000015000d942004c0050740f80c65039505a554400801c0d400c6040d4010901e404083d01039008001d900f101c0c1e40082c048203481d02586541c80006100e0b60200f0306080074040d0381c801040c421124402e01000d00c603413510000c0c00e141005032070003010100944c429680300245042090002c13144800c0ea103a1400c016525140410250414070181c07070445400c8082030140038407001b0a0901251300c1c603102d440c8034502000c02980c155400d43e001074625420240c1030f804000b03e103041c0e03130304041c8030b503d513406026036010224450301801242c41c10b090703141c0c2c00020803241041d4041d1130f860b006640801b0022424000c050280c1e1001c03682100e0740786150790b03070301c0700c00c1a280107030301c040c04c4501701480c1040080c003442a01c4290803200741c0002c40e000031b03000c045600d403174124148004104005a694a9942070b0040041032a030100b640d0522103c0070341d14056100780134128181c54000e080700d040c1031101100e61000101142050000f66a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 858676843 1250 858675593 858675611
    0x51e032e11040b0c0102031f051c211707110733050306030f0c031515040c170f280605090702010e060112030801170304030b040f020316050310020904 66
    0x100b41c00815501070344c10009a1241015018050600441900c2c895416003038002888640c407001e090161481d000c15440303804188034281030644184082c2103621600e44421b101e0f04090300b2101010213008550301c620300ba03641d2103100b1680250f40e10783c0c0c200c40303400100d41040070b07000c84400500c01d8103409405204102c01511821031000d107130780141020030000700800c4514a004c0c442201c18040da1000303017904200d4000000e0b2200c0300c403000da012004a41c8003048400075596403e0503001f40c0600100710603400880082c201c51140d0a900041c0b100f001d0018862001c41d030f00041c02000703031030b014101460150240380d5410035040040312100e07030390b03c500061036034610103071500030202d03030b0000210406d0728810301c2e040440c141c01c500315506840002c00300195020100311304441c0ca49010502410f80085080d0951059030b001801c8400c0744018041405101e25489041d03603c203c00702d40c04150794100315081d954480c861141d160b000880c40011000341a0004c10700218010000102210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 858678093 1250 858676843 858676859
    0x60106050c0115170c0102010915020705070510081f030f030c0311121902120301030f0c0308070312060602240604090f2001080903090415051e032e1104 67
    0x41191311804c0851900c0020407000b0b082031090000e85442803009116136102a00c48401000029980c0356003036500044020a21000740151406010000e1001040e00880c4100070f100c40821354503168140d4103202e0312032034244001080022641c0c48028100c941c01d4640301500d0340e501101040c0c09200f22844420401c680c180400a04003140c20741d070a4450000b5004130254000d502906801e542c08200c180510540c20720550741142c0e4400b412007880c049514100341c200d8503680c0020250307140420010200750f0091071240740d01012120811441ea52440100da8034000d03442040003207001c900c41e408100c800319050301d61014001d0400700b00c7c2035141d6504904641c00b41001c0d603441313801e41c2c00202915030b034100c81c0030039003000d281107069070800c400d4460b00c82c0310b00062140f00c0c564869600b1a40e441041c100002081c005140d0880e40382c10410420a0130301c101c040901c00c2c007030000120700e050f40e44882c0050103451401c0d0b038500d40d0044062803005050405104c04034030805c2c840011045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 858679343 1250 858678093 858678131
    0xf0204090f0c09050a0204120b06061b210a17091924061802130b07120e0306191a04090c080c1c0b190c0e13020c060106050c01 56
    0x2445240640380b4a45014040021030b44040e15088149004000c20041d0040e407400c100a0540c1046881c050758071180002009485240141040c1a5913001d0103940180c000c00c1301c070040004141000c0407001c1d00290680344e8480c000051002c034400644408014a61101040d40b00c21070000301c460b210b101d100c1120107030340a0301007114101c01805103215521841072041348000d60400b0284036450401100070541d094040082101c00e0f400304285003028082d904540c01069041131072965001181000b451000c4940b203500d011170f5500d0080a0395041c0000c2c03040c490354031001e034050842261800c2c0300103020140045207101c01900c0c4810866034031449007002051003503018100091801c4946824111814100782c032405007840821001503903590800c00340c913400b1031188401d5440412001070b8001050006046c60324102c142204030750040c0036001c1c0d2f0601240c8820000382c03900c214005a105240b2405015041400100400c80c000c5000d844c4188010001103860009080ca1340c980c0c0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 858680593 1250 858679343 858679373
    0xc0201060e010f14030615010f021009230d020c1002010b0612042009130f1502030a0b0603130204020a02030d020c07030303060e0601020703141e1606110a0f020409 72
    0x90503500d64101301e0054011800d02c0c41c0d21080d4080c2030f044c42c1c0b0503250380207a0b0032010540d041c4001c2d030035110350b030034824002903107844415001000588007070f0070a5a5540d8050482040c11203041404902e0389800080c010070192042e401000085c014805001070801406182401c1d5034030365140c01556a1460003501c1001170301011481207250500703082256030240d0f4485205244090400c0300703142c9030381d2130301548800f281e0b11030300c0712104614250100c1e0b14101c03c054120303150f8080d000b26100313994000314021040100706009400901341007183ea44001c2d2100651142104008001030400b9005401c444000d8015641003541c0b00300f0070000d0781d01010f8000031981012505101b0980c041c8a144094006541c129a2510b42180040e590701c083c5d000251584007411a140943d05081080884043c038000358100b00b145850a210361701c04090301d1015044424a00101d10703244203500e01c00004542000410000400e91a0300550a41042c0c00703907007103a15411a0340106104225075401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 858681843 1250 858680593 858680609
    0x20903060105060d140903030901200711150304050105040b10050622050904080c1006030206030f15060a0203041a090109030b07020a02120a1127130c2c010b0d0c0201060e01 76
    0x340e498801427850841e10002c40c100744120002c2e0b00c81200124010581b0442548a07a0a501100b590f0000030038051282c0c0c00d03500d480b0000005c2004115040d0020b030b006610a05615103e5111040c0764284614076002c0c16800c92800d003d91200d000001412051121996524a0f00b80d901c91011441140c82154103442a00300052814181c000400c281e2041008154040000d1425680003031424400a0510002c1449105c0440e01d045d02291410400000003403000347e0301c01a0f0080a03441e5081071140c0b007100b00c0080c00750810f40d4210400c0356440c10050b52040c901508640c0e400d491010090115130440c42030748040310060302d41491000c0d0030350030a00180032882a84c07070009409244c2442030742c040c3e040d050095488104d0384841000143c40c0c0d40b40d81002d9030b030303c0040d40410b400101000c0c064a001c1e4200142585061074204220f407444c0412601e011211001e03507201314420720a0100180c410800004154042e82c0090030300d511501c00801c60550382e04840c2c85546081c1c0003524 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 858683093 1250 858681843 858681847
    0x12060a0810050a0b330a0e0613150306031109010605070807031110141602120d1e0203040309140616080c011a031911010e01090e04050c0112020903060105060d140903 73
    0x300c81045549103000c9a20028491b24145070948000d00c40e031070094143e4040c0d07601260b40b00902d01c14403a4a03010b8800390381529107001d440b0b000103014040701d10060341ca00d248103020000d9030500b005603d06131000ea4694910b880b040d40c2d15a00c150f80450803d40810070070550340da11003201070200c203114621000000c40e13100e0385158a00324006001d000d00542510040300c040c4050340200768140c0e05030306403e485032510182ca1015010301b04050303014020b00e4a9100044a80c00c0380d502a40c007032030080e9502403201d03841c0d4508005111001d0841036002c10180b2840c0585d0780f03a580040e4005103e00320260501d85440341650070b5a920360380001551003010040142d60034100310190031541100002d5111326060b03200e03006502554900c02d810403902070503205036070f401a00b00741c0081c84c0e220707081d003035501d09401d159480b80414084c403800600f140e0320103d8400b40394000e80c0c15903075000300504400e034601010081e243d807100c03080c1c410440d101c036400c420030110307a83c040344503600340d1011355 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 858684343 1250 858683093 858683149
    0x2d040312180c060f0212071416061d010e040504050604030f020a150c020703080a1110020301081005090f0a0f15050c1204030c0602030103030512060a0810050a0b 71
    0x151940351a07892020980300e2401070100d01c4640921040700e0b46420b04140b40044034904906040c0044084850300e000000c1040800030409400f03c08034154005542c91130104010721601a07090f403181d02c0000e155440780c00102d00050446c41c130303080414140108540001c5000c00d095400072034040c0c41c0c5410607000c1005040d000811110400200c0c401b03081e0201c059a26000418445803070194031503550b140c030905003402084000050b5421500b82c41d103400324804010403400c0020014045c0e4050140381c44070b00c0005000b581c7c180c0740054054212065643d001000814008101d44264820098802c9640c6006d000030054180121b04e00d5500c414141000748068800f145042d102c01e14050411808040e030009960b1030b0103c40b941d5030056221400e04850040c0c1c1d0750006094144000000020544c220000b00200e4950402c0c42907640c0c0c8131002c01c0000c489912600324941c01125103a94407507450391015500102107080082c0c9916100c02044582ea6004c44035000c151000c40c0c16 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 858685593 1250 858684343 858684377
    0xa06030218040b031005090a0212030703020c060711090a110301090c1d010512041a010e010e060d082a01020c010203071b120e13050a0b01090b03010b032d0403 70
    0x1c9040703100e06441c180f0540e42e00308042136444d4114001d048480399164040381e95800c081c801c2444154004010342020404544050380f40d500c00c00c400c50151284400700c0540e800e101c4182e40c142c58100c007a80300b000e0940c100303014501c0001003044003e6540c48800484000507040a14003070840c400c00001c190250034006400c813541d0700040c01c5075120080e00600e8603a8050200c0f0100644c101c081001c03034696160841c000c9224140c460400920500085241911480118100c90968041d0511a10340c48140848856030801c007801d140e000700000e2541c101003552102150b200c01e258402c100341a410040e0882c5c000300010b0030103075000414005420742c03140d00081d031001d0004000103401908e5a0303808100030191400c1043c81034a4013034401558801c50380e940e900c4800c4800380031502d049000b0200070b10042c0f12050209a020501181108203801540c1c180c0d03081350f46592454a0382061120000206603440750000d1200814003084202e146c1c003240154400e0311818a0000d0403a10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 858686843 1250 858685593 858685627
    0x21f1b02030f041205070b0a030b18070206010314030405031609060b031006030c0e0405040c06094b03060603021f0807080c040f0e0f0a061a0a020c0a060302 69
    0x120108550080c401100001212400c0310212100b603440300e07602d40d501d450710703d0070101c40d80e1151170354801c0800d00500f200d805070481504200d048640000e65061441a065000001c1c0c8000b0010f0380b055005000140c400450032141ea16050100c0342003c0c0e4400000c0c0c501040b03c0c01516501e100701c4400c0200075114000c000c040d04101d4031140c29031030031000e03009540e07070366109520800d80c07560b00c1074021a0040d41e440b1604000503000740306a18290030091415207151160100284502d000050300040001071321503140088481c1e0001203031413003401c5100020300c0c02004900704890760212036418480216800940c803500d404100e4a01e94010801034650080c13003e000c2c010410710301d010b085d5000f100980d01c20181d06103c0c120f0389170700381701207410f00a40e00b201c9402e80c80d4650100f800c9100b1300321984100c489101804980e601c1e4001e000c2507503000d1040c0301344503a04404044200120b00044c010f09901c500c101d4a83c20000c0e00040c03d10340807548100e021039030000e240740d4011213442c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 858688093 1250 858686843 858686891
    0x50603010b01021b010309080403050d020c0609010f0810080313232b2f0609010e130f02030709030510090203060a0b030a02040c1e0801030c0b0a021f 66
    0x80140341e0080c0000303915005904412896002c010318142c0ea10ba00a0f40300380c15480e004540183c0310354907450001d603100c004500503005849400080310886c80c08a04a64082106a540c10040e1201c05026500c03450050504245218814030100d07011500b04050515940da400140e0304a5240c0404035064080d0101821151507080390500c1d4a91288000099902140e000e010f2100096180e4034500c1140c01500074610a03400040002400e0703504285148151002c8010b03c0d160000d10402c0301d2071003640c2c01c55002c14030742c84a0247c00c2c07805031a07480c03c0003d186004503000c03503809044012a0b108035415804038158035014418400304001044071519064003c005a440c1500000e5039004020075404600f501c41000e500b45413000d1050700040d6602034020302c240e50790640f02602c000384c05041c40700000382504000840900c00c0f44078604980e0404c94082c541ca05109020f1142e40c41005010158481c134050f11004652086500680741e00121000490f085c1018140c1c00d81000741c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 858689343 1250 858688093 858688099
    0x131805010c022103010608070e061b06190614010c1e030201060f05040e07050f010212040b0a11070b0a0813020d0510050c0a1407020a03050604080405030105070804050c010e010216180506 82
    0x3c00103001c22600847c80351741040450601c413610500100c002030b040d10840707000e01c04007090211081da10a0000585034021056a5403440880014280c134100b03c80180c030603010011142c400c04031a5500a294410303185010b20101c006441030008131150010603800107c5c0181e42d80c0c40104800c8000c070310402d0140c00211000d1214a80281c411565120180140e5105052110807181c0301d0b8001c0100000c801d03d403410640e1541c0e81d411a0b81910f4200140b0840440d500c10310701d00440601040800a494001400b5070a00340015030403100424000d10381d0000d01c0300c07503038001b026076200f041050459100350002d14581013400c03417013070540381c01a20303404c0d0801051101c95445a003080513610110695070189803118039500026010405552026001e4000e4105000c00d003c101030051055500c00c0c1c000348100d4444020446803c502100c001d4802d40000c078081002d981301c0c000a2440c003c0510440b1b01503800e1916012100005a101040700980c02e92400301c1c1079414010140d00113011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 858690593 1250 858689343 858689347
    0xb0c0c0109140d1b0f061e02190f0c0302090f07030e0610030308130b1801060b07030905010c05071a09090f01030f020d140d1d04050402131805010c0221 67
    0x1150105141c14005680140101040c4007107040304c910551000c8003c0265922541000f5078403400034010215004034a04400203070342456280c07600004908518101080c0740b200b140c0c0345525030b05600741107940f0844020f030071200000090f030f075405030813402011241c9030004903060003140070f0304940381c00f02c2030380c0c403034101004001c2c10700180f400f00f03401c5035050b050035503469490085c00c0c3c0c0f2000103014000c24994116041c00000c2c00903502c1d105406200700000c100c00e035100d1040c034440d4012002c00500041040406210035485101c000c055144114101c48003141c41e0031016403561074245043c0315031400865040f40380e15000b180d084e007203442500e60b0007183d415178035158040649203902900076142801340b0380400046000003003c0c80c100343c3c2a5055002c0d503041c014910700170b21b4911074044d920724034000305524061248038000c96008048069800c2005080c80280c03544854500010107a054050089036081c0100310403081da0b54041e026403502e03001c8030040c80c81101c1401c00d0305041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 858691843 1250 858690593 858690629
    0xf0509060f27010b03030a031d06010e0630010506150301050a090c0c21080108030a2c130212010e0106120b040902030d0918021c090206040b0c0c0109 66
    0x1400b082150007444107151035070200c1466003540c094010300e2540c1d034052200249101c14103500d07903c000480c40c22180301000c568414440c5503a0f8503000e003c0e5a4500070000007040c1c040c40c00d080c4103c40d03007242042c200c004020a40c11b00424940c00d02000d82103075110340811000c2d14040301c50110100440d4600340c1154144400310305240d0303490041e480d0281d950409841c0d0315000c0c075000e000e0300f580700891250841c1902d010717202c94025148004003041041d00040303010f03074003c010307075507144a40d540b030092807880c0b56000308511110980410400d413250311441407903140c00003200525203008074090381d1542c0300e0510060101050b802100c041d4528001408032507070200240141201d40341001c03c0007120700c1e0008005040c0c2800c003c1d41480b40b420758490080d00598014203e0707040740c1c0c0290084001042c441b060380b2900d00000d12040b42c00c401028560a1641314212150020f02400e05060303d4041c0d00400741d0040d43d080301550310a600c0b04070a980c0c1300c580c1401a02c035054401410441c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 858693093 1250 858691843 858691861
    0x4050d200a2303040b0f03150307080309040f0203132418050c0405010302030307080903070506040e040510202d070533070c020306070e1f090b0307030603060f0509060f 74
    0x40000040001c2000000301d4150304021040034230510004007551a1240e40750703a80d5540e9800900c1050240f424450a240010303024802d0340e00c1149211408503500c203080d512100114035000341c800036a04d11845021004000303221300d50074100c03028580803000740300741015071604202c9040c82d84140d041c44011310040e00d0100540f00c0ca641e20101040d190101140000c4c00e0000e03070341207141c11880101d000110030f2281500f180c090760040054604040c0e024111300f040d42ea04c00c50f66003804c0d00b580b20f60751442c0c003a0703001000664100c1004001c82e8000c08440300441002c41c000034882e043c0410054148181400480488040b04103901c00c0d140300c0448900c0005a401c0801c008005510000307999103014221804880e640141030359000c0c5040c4c04041c10a03000c4107110782c05543c00500c2980c051983c51854410403001e900e500b4003142c5041c240c1412030b0320040980c1e003010f85401001000400a000701b50008507010700c0440c0924020398803600e0403e00070048610b0300103403014800e02e00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 858694343 1250 858693093 858693097
    0x60904050d0c2108011e0f1211090c1c0605010807050c0102090a06030518060c1801020f032d07030e040b150316110604050d200a2303040b 61
    0x640b4100b4032416030641c10492184811602041001e0000a082e92009540800210306031102a0709100807013079030602d81004054140508021203103483d03824007580201d001146070951260101010080c409404104410029100c04e0b4035440045111009941c03c420308410140f422a0300700a41880c00e80020b0000c03801820407000e0140000d58110030103820b4040340c1400300068580701c4040e648210050051034221500100440b05403002d0495607004298513001c2c0d03481140550030403c1100e850705644503607038005070652266958040049030240003414078105074114030314000f022541c40325403860f0320031800c41d80d04c00d00b00901da00083e003040f01003240074001d4500203040c00740d2401190050f0000c9100004566000c002c000c1610400c400c283d40c604038079a241410180190303100c0b0340d10030060318010543d03000241080b80703062041c4804440100040100c1c0384003c00320f24a141403941d00c0c041510010150b280c440101041544034071551042d8100842ca050715180c107909082c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 858695593 1250 858694343 858694363
    0xc0105120613090501020c07050a090e1b0d0c080615011103070f03050f040801020c150712020a02011407080f0907050102030703140438030c0d091b08070e06090405 72
    0x103414001c0e0200c2c8107011684002c40e82c0d40d000008560380c218200d0016039900e200c1c4a07191051101610100d1600c0140c010558001022801032002e4400d00801e04c0088800b0fa00b00f680110800421901080b01d40410500600d582c20240099040c000c2d080078080c12004003031414000c04040300601900000219040180c101c4d850404600107032404603800c0c4140e424000030200042004501520706600401c000f0301c207072080b01c8944042100301c00c00c02004494620224125650210741c1a0360380e00100074240162000141260342860310302174000c01565000c000941040400c5803417401d5081c2550080132500c014440303146003600003036030323480f55200080c101304110713283c01003107001c910558020f00f507060f0b42d1840000b0311408849980080b5003c407601c1128547c03000b031039a0420000c890080c2000c80c905d034508600022840007078110200201d82400c9900070030b10602140781c1c400006881418090518617142840441011401405003485804008103100014000041000003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 858696843 1250 858695593 858695599
    0x711060f060f010201090b0108073f030302040b1308010e071a071b0e04050d1803060209030a06090b07030f140103031421070f11060103020123041202030c01051206 72
    0x2e804040101c1c0034148134500200104038100010801c3d040200c1c3e200240c0301130b0308040580801a81e50560003201c1c009514240c084c41d2003c4510741c49000e110060183e019040c09841c103a81c8034842c040d6076220300c90500e074980d031100381484120402e003e0f05e15003540ca40c005040c40c504103c03450b00149031007452400300f88800140e400c1004107042c50110b06500c0070002190281c1e0b00e1119100228003150115014051138001030900380c040d141d030103c030007458640345011500b0359640200030b42c4040003e1360f1520844411800040d06402100d0001e03201d00c1c03246080d410035081c06001d03100361103038040005051424144100041100c45811681c00d40b90001e81c0260b81204001548184c41b0b04900c00c00e00014150f0900101038501c1e8051181d960310010440e064540444114190b42d0880c829900100c0040016601c907404c130200444000310a0854a01c41064400d0f0652265102d50055050800301400b940f40034030800d1031554080c00c0041c90704c848811003420151000f04038500c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 858698093 1250 858696843 858696859
    0x703020d05210a05090708070e07030906020c0a150501060c0b04060203100509070329030a0b060406150314010504020f03070809030f04090b0907090803040614210711060f06 76
    0x28503001c80303010b101c541901000b0300001c1d0802c03280c4600600381c00c0310300019030301c6413000c00500e031200064008200c41130058403c8a40d1a018011400387c40e03100000e4032076640a215038144450180f0454041074440c50441080c0d455a610031025282e050f070000e01441307442c0003100003150104501a500a503c5040140d0303d958200c0e041800e54260f400c01500100f2010401010940550204086920390848188402d20707641060f049094501183c98141d08403441d0003000514079891240c00c804014000704069881d1005c0c0750710340c0075140c1492700107521055011408200014014003408017520701794500601844111108c1c400601020100962540010140034080c07090303402604003199050380c0c3d1540d4140e41400f80c20350844062144800300702042400d030003105000d084034881406542070602c0c01d0001e0307400c0c0707480b11040701c15810100f1a007026580803000c181201001030303513100803d05000000030b040714641019a03e0343d80c40b440602c1103021003980d240784d1040040b140300c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 858699343 1250 858698093 858698107
    0x100905062a0102040b120604050112060906061e0f2102092232061302010908010e0609070b09060405040f14040302060a11210c120c0316050703020d05 66
    0x1030803010301e8050403030321944042801300d4803c054000404250300e00562242c2e0544403481040110385003803080d0340d0201c0301001d2180001c0c143e41c00500c0024026840050800e0340c40000007000e161001c0c0000030703281500c4c810f21101c0300644245014000d82800d0300d84138150408071984d02080c0d044040d01c113441c00000501c0c94609042c03220103c40081c01100703a41c05035881c00e03045510701c102d8a4034541055105c400b00b81c0d6041d64803c20802e031144010039245d00c9a01c0004e0901d858000d0076030410081e0000482c420b20240585043c501c0700d407000300074900c1c04d03907402414000301e500306984d80141003103500501d59980c01620f05680003110005102e8443c86030740700c010224092003005502c00d84040100b415001325420f0320803010000181b01c550f060360b00340c054512803442100c47d10401c46030104940680000301d41d500021403103880f89440c04100075007504000450350401c2043d8004104408203a00e0000131034a24810708000f424802c45540180d00c41d64500c809804000d0040f82c80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 858700593 1250 858699343 858699397
    0x6150103050405120703020304060806100e060a020f0a050705030105010b04030c09051909050703021c0b0a05070507051917030c1210050604030309170d080c0c0a061a10090506 77
    0x200c0c013900c501e07900203a942c09080c5406510b0341c1251041102250340c17580000c0781030034800c0c03da99540c14181d40f420314810720b0b0300810000d50011500c42045120b1070140b40180c1804024201c0c00501501c01447c150b481d1070b04050075544141c02c07040f950a010301c01040099151030446055414990f40810f0f21340e102c50341a440d6905865088141a05080c7d55105001300494000150b034001d90b210781d12a40b00c9004000d1013428040700500403019070b40001c031008140d5000940048052401d02d00d00b5200d6140c45240c080b04682000c0807600d0701c282070040240f244400710429109601d4207045283c4800303010514010b2100005e0451301c03140000b01841161030222016120040640d9112511313400d0040a80695004800c21321141d45400201c80c0e00003d0f050706402540e13a2523041941c0d03001c80240c4c550b088642c00b0710291090215806c00900e0038058230169007603d911000c03213032040c181001101c0e80620300840901541c07034001d1100e13440e50000c45041e012211100c0300c0342d0700d082240c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 858701843 1250 858700593 858700603
    0x1506030c0331030f020606010c02060d020d020310060905010e0f040506180c040816050f0112020c06010311090a0525051b0a1401052214060703051806150103050405 72
    0x2c4208030b60101546002403005038444069900e02965503805104400750301030341e8815003034a94a0225401600d03460040c0b600304000c284010040c48051f0a0500c2e03421800300303a030400d071031405001015280a1000c10792125082c0002c0009190440703c103028940410f0f0820701d030b01005802191194006815510340700008816018128081c9800e464040141750558100740180c02c2a801050903034103142c51003100c0001510740042c08421100ba10000640b02c10403543c00c0715075042e07024040a00394980611906009500485c008031500c8410002c101c191040206140c01c0507141100303104034503003180204a5011082044904044c41208040e01d580c001d83c4460441000040b04c1204904408161b00030018881c1d017480103601c0302c030a2160b00b62201199040f80e0703041c00040c00f40038501c01c4904201c029014070240905414140d900c0ea0070301d60101e071080e01207611182804500309803074104c80c2c01800c83c8005815030f401c202c248800186072040a00e810140c517900818103001090207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 858703093 1250 858701843 858701881
    0xd05030a0209042a270b0309071508010f0b030f01030b09100f060608100b090607140a0f021c08030a0902061303030804030f05040803031b0c030f030f1506030c03 71
    0x5130070a4200d40c18800800800c1e0402d241000540050a2905843da5044144541c0e030024504c130107210308108003504650001080c1c810644a40700c00000c6210080c0301c4d0217401442c1c3d81e6a42e041d90b0404441400d080f41c00c4d80b080c0c230401800c004200354075a85d00781c02415290300ca820000651505410f082c906080c46040364040c1345080c41210743d81d1103d6124004613103a680703500d0b015998900f00c2400c031030100d101e510f8040ea8104460342c12031030103500030a51103103d00f1600c00b4500311515417614007101d81c2d908a81e81c803800d034803940961130002540a40350f40d03c0800f03007102c59203503038130391880f40000740400c124652074484600441da03c0c6016141d40c9003002140c000718641da42401084040c09540540200d41c0051621075070901c1038044405031000320004604d9511030b0060043d00109450141685000030f202000e22804148018a96202d0070a64941c8a003040841c02c0298040035090780c40d030081c20181c8882a88650060300d6001407100e50300c0d0746a0307984034410b40090200d54 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 858704343 1250 858703093 858703121
    0xf0e0f04021b010605030115091e05160e100c081602090405070e090c09040212070f1517090606010503042105070614010803030a020d2a0f020d05030a020904 69
    0x40386014191414524001c009070b0510020300155640b042454201c030300c01e2105840d1086002d9041c002d5201c540c0000d40050501c01c21040405000c0c4002412203030b0580f103100c0541c404045c602c8401d80d02054601c41008200e0f0024203120708600041c000d10401c0000820b035003004501281400030240040c2d85c102e07006071280125142c64505151241ca45000d40440000c1110100d80b0408000542000c1a000070704519140d80f115000c200403003068010058040c80391701c6001c5440ea4148440c03000030500b60388004003620b00d03014043d00716500d05d07402c009208001405c00542450001e281e540081c400c1c05d0855481c0c03110704002c042c501a289804816420382409c400c0481c2e4002d001b00100c90145030104205428621040c11140d02841a10050742c41840481c00e82c60b140c0c0d0003442d00003241c601c00602000c0703c007450301c2c68889110110003001440b40704000d88507005452121310307000a1000d05160052020042d109000140c8603000351a4046540c0c1425215548480c00c44001d070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 858705593 1250 858704343 858704347
    0x70b0a030f020717040f12050c041a0316151d0d02130e03030403080f04021012020c0f03030406060e09030d0207030903061a030c010905030312060a1d0406060509070f0e0f0402 77
    0x16107111075403030784203120301c0c954038010b1b1400003113800c4440d00d122070361a40304000d40080c150304810800a1300d01c041407403945001700c508507440c641d020401d20044607107011200395054504035003036001d424910510001e100404c0c020300c1c06d03450341c0c40030381829150841e0f801c040c075100b90011540b1308580c1c3c88c40c401d5103454000060301080001001e148518440d40d103401c1c0540d14110030007624101610029080103400c403040c0d00c014011315041542110b0200014100740a801c483e500d01135140b4100c02072a0000020302082c40700c0d0b0300030315015007803100c418903071030504201c1c1e60754034803c2012070909107030b010504500305481005408000c41d000310050100130130410b178003c48414680c40b600e1103403040d400d2102441d40903548071400c44c0c1004000e541044c85d060300301041448001c1002e94801007240c0082840d00d1080e00b02507040c0280c8030002c81034070740f070300d441001c4510707540007103105801c202c003003140c40c43c0d2055100c00800418a0042c1c181d452510100b106a441c0c07048650340f181c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 858706843 1250 858705593 858705623
    0x1a090a021503090607030e1005072102090f0319080a03150e31030c0204090507030308070206150901051306050a080d0305100b03011a0d0f1a03070b0a030f0207 70
    0x18601c0a14002d4001a0a8032290303110600c095040b90400c5070424000d80100c43c2044034080540d00a42d4001114284000e10450502221002d402d0f106942d92035075074049081000d41c02c200701015a241021f8005200c0d0020303404551010301e80d40140200001e07070008070358054a103e074020320f03800c849004050342043e4582d130314900149070803240c0d64441c0c22070700d201c0a044002c0c009945840040361003442d0b41c40b9a1500c2c21942d0324280481039800c02c0d2200341c400000b070780802488000711b000e6900c10340b443c140404002d05000000c1d006040081c22500000000d41d00c220000381100c03002ca41d03030010258100006c10141616511995004182050004a403803011603601042021650b0400450b5030342900c080c0d6050241c0a08540041c040c001401424100d00003100d9510b403480107107003000040c020305001c0d03a959601e0216140d4481c120404100354203410250141e1048020323044a070700b0300c02d00314014080c8141003410103468500e03004000342154129074050f60000580c03d40509 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 858708093 1250 858706843 858706879
    0x70b0a0603030e0108040312090507030c1d10140907030e0a0503130602030c0c0f120303040818091303030b0d0f050a1a15151b0106061b1a090a02 64
    0xd041e100c140d0204850491a081c1e035841021113034480c03941522059603a0071010000001412100c0f41111180309006021002c00d502c000b0000c002d0500ca00c0601c102041128540030100c00540101d034a84250101801800b4000c04407010072001550240700a6039106421405401c2441e007843c1140190072182d018042e010008118040c0300e00034005205544210880c0d49114010448031740780c03c000c00e41e0b0740a1500445003400c105000309200b112404607441141103500988045501c4540060030b402c207091044214422040e040724a07248c0c07031601c0080704510f00c0a54400604040c3e803400d0186d00780d60740313041568031542c0094005c0e01015681c50101c1e03440084240a032900c505490600780010360000b072a078071800c1ca18961004042040003031000b24620405007060b1400c0c03d21001c804405070381d258200e5650110004a88285820702c0a40391804415400b51001e401c280803401003030000c5410304241190400341c002543d1110905420044124402035115582e0404008108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 858709343 1250 858708093 858708101
    0x170d15060212130e09120c1605040c1215170a060605030703121d040c120e01051e041a04050a05060f0f010b0903011508100609061a0a05070b0a 63
    0x200359400700c640a40c066940c0c00310300d000d9104400b0700041a5001071010f0069040000e0308041c00341d080310700642014582c004540c12600c0342180030340c05030040c5620b00d02ea441080004003001d0f1401c118081c2001030040c074100003440440d2040707858107101c03007203001110111001040c1007144e81c0281e4807104100b50700c60301444801d403003050411a000c2031a00d008150001100e6020300c4600c210741d00c160044e10b202003a10420a12070344c21107641101074440b4040c1400401c031a1f41c8081080d10303091028011280184a09603a507803400081103082c0c110410341503082a9041c0b91611190303180d141103031000c06020310070031020000e00240f20802400050f02055507115605694480cad5a14403210f160701ca08032840d540300c11103100100414401c01d402000a690050008240003440b00c0e13140c50f0041e040d5000483c40c1c1d01c8103c10300c1506919108070710107405416418080349190101040b4184405010004800782c00508460308900810481e104c1c10390260314150f06281200340d00d0010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 858710593 1250 858709343 858709349
    0x80c0415171905090312241e041b05030106030b1f030204031203110909060409020a180f060506091c0c1d090312011514040308090a0b070f170d15 64
    0x7800c110215540d0700c1c01000750354030384c034802d80d00800950711f1500722490110800040301c600340442c642000140c139160f5040001540d50940d00010360b81e05c00600c070841304c8c9040855a0055a0728190307008643c09412241107810600e4086080710300c8200041c4964a40403030f0124002c45454514580e0340c054001d001207900480c0c01c00c50700312190209800745c030f450005640d281c0e042003111021b0b61034010810303038204001400001d40c200d0140e001c50243c04007500310041c169845442d1000021041c02482004050180207100944c0707044041394403070090075003182c820b141c0e54203c030009402242d5106840c0d60800c2c1501009642d500f85c1e0f9801440800c55060702416000000300c42d0b041c00021110304098a01540496a207001040020746010030902020080540d24045240c420350b00544080c50080100d503a84105200401240c2c02043d030240701e2000702440b581d004514a5040d00980340c1d08128051400c04151602403424480c51100800d40b6207002c0030040710703103070030305004c015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 858711843 1250 858710593 858710641
    0x40b040f030302070b12071b02061602040c030c021e0c03100c020c010305041e050f160f12020109140f0d0605070801090513060f0f02160c06080c041517 67
    0x384c0c5490340306400b460301c50300e001c0a80420582022944591140303641088400c50f5105031820080320340d001071600c1d801030b00714100326080001201c041d8a0035206150708900c603401c0c1003041117880390b0040c0d02c60b4070001c03018801400b44400810301c6501801064a102c00c01001e42ea5070f0720744941c50390020040d030f140d40e00052280d6001c3e00c1ca6540a407259901907904810302540c014107400b065821181300c0302c402c8802d07001d00110411400400c2090b00003c20000072600045030406500440300b44483d44a0902462592003400150340c20041000c1501c0d801001c000c035104540004c550407860704c048058001c030078210340405000b0746030302041c0991440d60360508030345d07a40d060a00c1542c40c1500d0340b030140c88481c8551000110f00b58024a5220f922600102c0d90104681c0e211040360017080e500c0c501d140365681018200b0940e10542c00182c081c0781855034030f40c14000704c1a12540540d016a06650038002501900300d40207402071200e41c0c038800140706140c41c00c001c000a2042550704540d907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 858713093 1250 858711843 858711853
    0x301150b0d060f0e04080742050115080403020708120d0e0c01050d0c170f010f08030c070510111218010c02060a0f050c060a0911041a0114040b040f030302 68
    0x1a02c3c1030044043c0084409000c0c520f59551210348801c84160f00c90781d8102e6820080a03036180d56860618460101120302c07074015210209071044900c5402c42c030200c020426840e2100500501c0f074500320441a4500e5860158081e58603882c0c02ea26049454004201c3d070f100d04890780702c450ba4044001c01c0b9401e609203060084100071510503540380441c203030b601d02146050112606400e81a88482100e5000d8580441000f400580707044180d5000c4c0e03030304180a5030f80c1e001805100f414590120007050307400020f40c9404404c0c0c03103075511500b407030168038814400ca00f05034058038420740303040104140e400181c9044030a0f46433611b640d0341c02140300d00116030164000740141d43c00303030480340b00840d005004546844256041201c950042c10139007424054180804c120b218401c0190a01c90003243c40001086540c1b402d04c2c03030a044200b0f8503284254182120784100b100e60000c1d00700c0c0b8503000e0070240480d02c5a001d241310035002e903800c0303406540c40200b4001b641805000400e0708a900a4003619 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 858714343 1250 858713093 858713099
    0xf1b15030606030e0d0305101e08011503030806060f0d140709060e0303040e070c14010515041a040b04020d020a0c020f060307050a120612030333140301150b0d06 71
    0x14007503940d0b11401113440d400a01c040003025002e42c000787c0d4080305e415000d40c0d103107440d80b200000b0383c91449405030000000c610107000c180001d200b15002078406411a040b41ca1071658020005a0010110350040c2c81c04a452419084040d0a0707500c9503207181010302c0228260280703c21221400c490400020341000710000b015400380c1941c4403070301000b5000c1d514003400c01d104001c9005025180313030b0070014150150804210024140c481a0300c20200204980c10684070380814007581c04951441035142120703240413124a500c404e00001e4041d200402d0500c801c00000b070090041111703101c211b0740001904e0420300d40c03140d61040018402c9801020680f0100284001800200c2d20300001c20410401ca60710345000d44481c9203581c80c0401c000c903810b40c8558100c900311b2940002200807070b445890a510320700d914140c84505090301d408241380c00a44860001c036101441c80340c2164500410081e03440b82e1800c3d000b51010034010403260302919540c0c040640141c4c0940c142d040720b83c2c1ba068000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 858715593 1250 858714343 858714347
    0x170307050d060b09061605150403110c06091003050601270611030f031f0312080f060f1c020105040b041d0c09091612110405030709110301030f1b15030606 68
    0xe14804e403000344c003484c2803052640c44006e004c50781035015580c601ca1808118030288455551078499442a500c4202c0b407c1e480700100d117440643d51200703120b030b4000e01c40b086213030315a41030b41c5021401074a030204c2e803078843e840140c880015203a6000c81c82d54480801501c0c100d00840c221086403c1035607102d403040310000810380c90340114601503884143c100080b4107845150492103558403020b000404640c1c0d502d9554210041401151a0110742c8030400c2042170030000d41100d512503002d41d20081c4a1011800080d03404a03c81ea00180c64a4180740382025a44660107640c0a03002a1004581e00c94940000340c01984001203201103461a60000400c08968401981d40d9460080c0c2800c8286d22031051003240603042c60203540801a407226050490b8840740160041d180c10365907400d54a03410581032604206440d080090400d0900030801c084280701001c41e811603030440c600d0b011140081c0392107100b1014031241c4000303000420310301080f04001c81518003a07050b519101004801c1d594401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 858716843 1250 858715593 858715597
    0x61a31051c0803060609150c06071b020d060c03020f04090902040b0a0e0f041a150316061418030303090106050f040b0607030e010203091503040b0c1312170307050d060b 74
    0x20081400b00144082606424060064000000018507000c4120b08900c0c40c11401d0708807801c3d080e0540c4c00303503090004003038016105590541e10901c02c80004100d07074011400300d9030580d8001301000c1e682c00d44210740034420390640e1420140c1000303c1d03a9070340c0da56140c180034002006082c2e118520b018130a0a25140180043c001c1b208102c00845460795101e80140e02508020300c10759a5001d4440c410b461000d01e185075900c551403100c1300c1203c0d6002c150904d883d000e900d00d0803104044104400f40300054000d00440b520400c40c5c0c003203950303807400000800a590131615800d5014031004c403d100c890310040d08800141d940903510b5600700e0f02003400f040700761004501500e8100c401004024040b078410f1a108040b03560600440e8a400214008981c0081d051407080d10030764070100c03d11042011240101d0b402c0154006100c1c00c003a144a803040d0104024403c2c40d5005980e403030311104002810507032140010030b02c09480e49038648940c014141d039014070a1001400d1401c200441d504140c1c0382 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 858718093 1250 858716843 858716899
    0x80601030201120209060d0e030a090927020f040603120806030d0522030c0902070b1f0e2a091903030f0c080f0406030b13061a3105 58
    0x5030702040d29516901043c001e51204002e1500070a00b0000d80c1e101003100d0040401000110004598600c2c1c054001002041c1e02d4200f14130319800e040304400050407403c4a030a094885000100760b100b600c0c4005000c1c042c414960540103030409000000f80f00009207c44680640c9455940c0e2503540d0030b0416440d000301c90186004a0000d00c8411844410034241c00c810720ba00c0b4a01409058880e22a0303046600c07940d006c0c02c01160000f0b01c070007c0000c880c070b5030340d00300081805280a0721240030009525401034003030204041690700014001d43c0b0388542c2d00403510781a24a21a060314102f110007416131200c2c25960060641c40f00b841c08040b03a200c0c10508480c4c15680d03920002c8001e0700d00300e940c040c840c40140c85092090003c0e442c1070041074014401490300d0707100014148440c10610641300d032202010350000d850300c8070400007114801080711503520000105a9502c1100c00b001c4200450380310b5000c1c03988162100c4200f0030203000d240c01d040c2c0f81c080f00c6225411040326408218120b14138 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 858719343 1250 858718093 858718097
    0x7110712020108070e04021b100b04090f02040b0303070c031226010605160209150f09090d05131d010501141e0d111c05180604020d1e08030a06080601030201 69
    0x400240c080e0302c28a60101d00c030600400140c48c3c400301082c0c1d488940754511002d0302c00d80103140d02200c218441c3c40751078500780e01071b9020320020090b5161008640c880e944c0c081c3c003e80d01c4143c0100580d406004880741d0782e500c90032640e0401d07224181601c2e84400c4241400210b0a010340b804100040c40c0c40c641207000760307020074135826800e0031400c81344c0380c1180b011100e000e0100c0b28040f0040c1d8420000c0d80c4030b406500d42c00300b2142d0400d807c00041e108102440c50040342c001d014484000c4000c6009806441d01d03051607650780303104000c2e5840d810015407005c03100448040d200c02008076003060180c1215426a6078149169020300300020520506421100e86514184601d101da0b41c1c0e800600001030080302c0001707103d00d06c2c0d040032020754040175031000d1041e4400079911a0064600c540c40e0030012162511000d1642c42c001c1554030301000d0000b074414001c80c20500c0c00c000c03100d03442001c80019488410340031401445c1420a43d0410b8501d8030801d030070aa804a200d150010b0310074102c80e016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 858720593 1250 858719343 858719357
    0x504050412030b24120a060305190f02040c080402030c10360e0412050901050f030a090606080a0c29030a150b040303111f020d060509071107120201 65
    0x200c1000d80050500c0043d580e0480c00400c1c00641580102001080b0b010000300310a990310154284d02c4100907000307046c002440d18001050000c03410003e814001c400d012a43d076100790545041000b00303040c248000a5100c4e0a0545e142030450380080310500036407003641110b24481c014402c20810099802000c00000d4422003d4219840710387c00303e0084002d942080900c00719034041c01d04030404142c0020b1348858400c0140010005100203140441c840340c903245083c8030007600000e01610070b84601920340c49001c0041407150701c0c076a0119040c00c5d800b1804000342ca07a610140c5480319100e0700f065901c240040300004416050b40081e0052000c1d07a151a4000181c85113002d40d1382d000900120314240e41c40c910703500c03211224a80c0390080c141d14490a61114039525004260400d80080b9140c5c0f5004010306882242d460413036000a590348250140e00c030701d1481200802089a41c0c000b691000704001801001034100106450021030141610949500c07480c00034860350a003000240026a8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 858721843 1250 858720593 858720623
    0x1090812070317011706010f0f0b0c0102090406080606010e060301030b040201140705010c0c060c0e030714030a0b01030c05040e0a0512160f2a050a030209130c0b0c01050105040504 79
    0x80c080040000c00c0c42410b180004030340001c004124480d0903001006031580c12003010a16001c104030050050024107003500e400346c2010000181c0003054416042d00200c00700d107410302d0300829010b480640700082d000308110359584d4807447d07842801307448560102e04200e0001c40340d41000c60441b410780b40c1014803400c2c00e445690044900211280300c0b100f42200c18400240016000c0c0900c103070f140180d5480c20311200c0f0604091040b00c0b4101f40d050148011040700e0905500c012401c00708075031807101c44039900f4403d000400c0c1400e492200060100007a407002000f0041c140011200341c40b816501008100c101c81406a900c50302e5180c0500f140d4801042e04048004900c0180101c10400c81c10704113180c4156524001c94240c01d00031552401088001c429440720b004440200104102d0320401103841e00c80803460046480c08003900518000c40001e40d1980e00c0c00e0f111145542c040e540c01041a521001040250400c802487d201e5003090700000d840c0ca018000c060147c0d802000803d03079048 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 858723093 1250 858721843 858721873
    0x10609061b030e130f0b04050601080f07021015080d0228020d0204020f0c010b04060b040b0711060a0c03110109030e0d021305150108011505071209081b0f010908 71
    0x24640412001c010300e101c0046440d444c2e0000c0c0504229507000e0100d1001c290b240c15409894600030203e0180e45068108034082ea130012030365801803160f0400e2580741c2c840708012400d0400f00350452021500304144034181400c0c01054500b1243c0140036203241d402120000c80c1c5400300c02d04032000d203101060344200030044030350000c201305100815807044500030782e003c94160307088203007184035001d0040b9443c00031200a0203221071222003280d04100792414102858601e000d80d0003881d42028000c140c40b03041064003001107000560080080f500c52010041c0240403501c4030070b00300d00007081c04d001100b24034014040c204188d80e0688422900c0c10541c414031499581100c010b80c0e220500354002a40f490051007814066001075600d460601c101000262401c1e00c1030f0b000210807692541c41c1c05120340d0050a0b01c0119500103441130075100a210201d40800c1181c00c50b1240c4d000d501c40b101d00e00600780d0300b5044081c205441c103a0070b000d8035400560740740c0c1c0d051045412513046480311000503d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 858724343 1250 858723093 858723137
    0x10e09060f07020a050a290613110403051e100e0a030e130c08090c0108060f1009030c06020a03090605031006180b0c060a140c16020612041a01060906 66
    0xca10403544c0400d4203807101813800c2203000701681d81d545840b08100d078900505461484400c880c5450402c541011400b1411400341a44e114500030303510041c0206da49142c0044400030368000e811200b41482d1940c44405150500d00c030184140302e00d0854445203040b03406401680f1421002509844e00d11385ca0a07194040000146680300d24006146e6005910900c150641d50f05180c4d00e9500c01d113015800c1c60700e041e034505446070511040030308000c00b076a50106a021511019900d12140c0d0800450641e1241840c0c0c000074070010a0300b0010401030340c0040d0f0a08007500903035480b0000740e546c1d03500b552a44429540d80040c5198001c00744802c03400b5103e55181031000c2c4078010003543d0b445a140000d9005010341580d150054010b2081400c154001c2659500409010700e40a0078040100300c5244a0038294100c0032506452280c00d65881009440e0a04141030b0a03081910305441d040d030504803d50554051580c00c8400841d916208003c4402500c1854491080c0760317503180c0ca090003075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 858725593 1250 858724343 858724351
    0x140d021b0f06120a0606260c0d0207081809060901060507060e0f03070c0f082b0903150b030607020f0a110301021e040603061d0609091203100608010e09060f 69
    0x1115082080c035400d900d000203042d00c11302c0310140004000d418007000900c00151019400c50020414184240d40403143c104560001090030786e0315500c074092011440a13011320b00b03000d001c504006c1102781d00082c80c254407207000e901c215803c80842da030300070810a200e8001e01884000600070b018010020f84254000c2107440748690449290382070030125645903034429801181d55441400c01004010443c10110025001000141c4280042101c0030f400c0d20a581d00807140414086221140c524068030184005e0364020313507420340303403440e100401c0041c1180c06d5505001c2e114010005045610107e4541203412540000d08084405a1035150b140c4802d41027032035141d54200300d1426440b0b1840710303214017030020f800c1080c0c440c8e15002015049689940c000008440c06444060070806110f51203a8480c43c1115814040d48882d2001840e000c0c1414850644c40b80010070321402c201149841000c40d085a030b00c00e441aa21004220b898400c1038810340e65561004011600b064103072500183c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 858726843 1250 858725593 858725599
    0xd030b090f040f030c0b010f031406010b190e060a051206030c03031c110309061602060c0409091e08040906060e030304030605130f0c05040b0102030c060105060a050702030a140d021b0f 81
    0x40311145440d0062a00420780c002410305488c2e0004004011880150060940780304010f00041d614001602c0600d119203100704803050070602d503401655020344d80d204140c81014020300c1c2c41d42c01264001d0b03c150f20000700ca4044548900c001072203481c0024402c82d00580c058042d43c1046000b41d080000c5400d8501d41c640c2503500e8075034001841d00d414000d1351040851400400b01c50070005231000c1d8440b0541180c00440d0001c600304500d0101000841e0f04842d40e10030b000406880608020034224076520341030f503050360380510540600588101500582c1e0396001c08100d5656030340c1040e2090480d9024a0350190010710007003011805e16400b41d540101d000ca6241911a42c0e681c030342c3c07884030100a003111519003400782808603007058030408030f181c8000c1c0015460200134094840c0d8079101480b4146c41501c00289030102248204251000f03264040d0454000c203c103490007002402c80c40740c130071905125a51444500510020b1a8031101c0c0b03034281c15207250300c101014000c10002641041ea0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 858728093 1250 858726843 858726857
    0x3020309030d09110118080604030f030b030a050a1e031d0a051003020d0c0e012118110f010c0f06020919140f1e060d0605040603050d030b090f040f03 66
    0x40ca86845004040f5601c1c42100c0c07000c420100d03030001610521481400f042c0340c4a00c4113003071082d0782d00054802d8016805003400b14021150101c1140a031001d500c0303068041c0200784a10301048030010b5a001c8040c0300320034603844d11002c403151098841c820800070700062040c0041181500032882440382c403480250004c10f2107525840030450050001181d800041da00050102c40c82c8614800c40301c00342c20070301d80206141010350000300301300e0b0100c3c038904103404451000d0030840306c564002110b40c403424620b000b400a241c00d0021751401c082d40301a000d040d2000d0301c007400d5803055a0b490300d1158055081c0503001d02d0354807204025000000d0344c0b904034845200442e60302c1e20b40c442e2034000b8800e4600c0211104d0544003403082c07d0905503111802403002004454070266016000411041c0c2510704a031500c1d00d400c0e55038080e2256902142d0081d24125021080c000702003155002075803551014810001c0307110611120a00c11507944500c180b8000c007180c001810780400c01709882c0280b50101e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 858729343 1250 858728093 858728107
    0x12050a02101b06090809030604030c060b040614091512010617160308030a0b06030a1a030a08040501030905071703040816080a031409041401151107060e03030d15030c240302030903 79
    0x2464260306882c00c0d0042044034040500308001070142400c13914dc05e550500c003072440c060014006020480420303100b0f0b806000018500c4483e030368042d8070326400415034000c83c203480c410316000b0002e43c01107000c081d05e1038142049203a40050b1403240d81000784c200c564082d24507280d030007068101412407003000f40c89802c0244595200390155001c1d18504e0750005400340441d2402c40806000e2a0040c0660450300c00c80000c170b20f1040581c4c08903042820302080601291404508040720383c1c00001420780303208200441d404c0000043c00c190b441c0a02124102d9001d0000380304103500910611900e58000d0320310000082c070600318840c3e08100a0101d506090105001400391035991881d0002181614010003404140030380d41403003c94141440d6625162101000307032070b4030035402013000380206600502e074642c034200700322034041c000080c04104500d510001c0d81d9103050240b00544443c03a04440100d166505042101401501d50041200e0140760311001d8001c1d42000309a6031880c00140001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 858730593 1250 858729343 858729349
    0xb011203021606020d030605090f0a0b040609231807060f0e060c0604030f0e0306043c120311122a07020a080c0105070303021312050a02101b06090809 66
    0x1d801401843c2c002e0504221750041c001d0458410740d0120b8824072022044c0880240240141a0031244120011034001d40500c0428007401640e48008451450032207030b80c45018882c0307260303034290f900900c6403d00e41d2030352101d02e6080c4421014503c2e040c0c00c4404200427540c0074007841c102e50886414500703041c0011100140c51170300b21401b5407000d600000308100405a004420249280702418620006403a09010a03500d1000400007803200c04103c480076007160502c0d5151240000400320744813026004c0d807104c540500100022940e0314022804000d8680c000d018207400c05c01500100ca0404910184031000c100010300598501c0c0106030003800b20318106500d1001b00c0c0c0a0340304841d030b00d4600380b050089070005035002c0c0d070361500031000c1400703941c1c0e10504548070035406103805a00c0d640004141e04d80313101c0d683e10040b00c1180c880d594404100707000c603034800b8840c0201c1c0c140c525280d141c54252080040d500500c10700722081c850841c0014490307484a0f060b17501808103542052540e0000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 858731843 1250 858730593 858730633
    0x20405010503390318030a050a030e07030804080d0e010f0e010e15030a0614040b010203070807080408031207020d030501060e102105101e2105060708090d0c0b01120302 74
    0x842440c0303c000820402c0f04500e0220300c2c1d4000384544015458258031030401040c03401401a031074105a140d1140007940081040030401654101e8034541e55030b603950b02c003182d5500032151181d000c03d0205040f880290300403a00100b505890782c43d14000c3c01541001118005d844003415540103545a821851100e0ad01c2d0140d40300320100480010f015092050a00c444500c40300024400c0e81420300c40301040e40c0c00f106554500e68408a5252915171034030344400680100d8102d01c41c10710001c656407440c0440b25007468025840f9400b41c0e102c2d102d0141044095400900621012885801d401060f42c108a81800e601c40000c0c81d000a80c008009000109503029000700b0902c1a111000d01c03081028900e4004000e0a16020300e90745d00f00a240009004070452044e0004c182c0340410902540110084804500741d10501707590440c130302508090603a43c800d1300e0b800a01d2080c00006d5131400e0090503888042c1d038119549074003036842d0041c800d04c415040c0c0743c01c5003140680b00803608100380c45e0034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 858733093 1250 858731843 858731941
    0x305101401020a2111064008040e01060804050a0b0604020903012c0d020c09060607020405070c210e060f0903070e061504230102033a020405010503 65
    0xc84640e44103080140207056142000140305160002004d001f01c0c905503c8481c100d4008000300b2011b00c0c04200c401208180c0701a03003400f0140c0816260508200d503032801001594090003941c1b110b42d0301c940c022925144200d800501075840703410a2808280043c2000c3e0348074a00800161420f6040d5010078256040e0364012103c283d03d080f01c01404c0003080d9920824404e01c0340040c800c14400000c000d55a00c403005003180501116404030300991030300310442d0b51640d00503206116509144c1c50042501c06143c0098524680222846c24540100c4400c004883d1141d1b50300ca8211042c0f204110081d403259a403016543c0b02000a1489502d060000324010401000200c01605d03100c020b1284940b070380528000311800801c0103000410400e01c003081d207211010b8115a6001c110b00041c0c0c514842c10388408580181d1a4408119a200d9080d168800100c107515120341c0c0004034442040c2e01840c000c5901054047c40015080c0b908580e41c1050315000c54114601c1828005031f0340b0a01d18182 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 858734343 1250 858733093 858733133
    0x103030c0213021b071802070308220209011503050108010c12050a0906090807030315061d0a08010e010f060b03060f0d111c1e05071205010f06090b010f0305101401020a 74
    0x311081081c03c1811b2079040f09101d0800c2d055250503030603a401055280010680006a90361080e0000c094402e1180c400b403150340074041480b42c1d40c407074090200d20394900310100c000a040200124510790103010b104144511606c0b00130048801107040c2019110041000515940c0e030312003003000c140e00380a201c003028010298035540340310318200201698440d0307444c40c00012420408200c255400382c8805a00105d4040350001c61011100290179540d00368403052841d1b0030150340c0b00070281c040d40070500da8801c00104200c03442e03440400e5550b0b400100c90301540324280c48030340d50311400c0c99044590300324030400f0f10886020300d2a0004220380c105a040d2400c1b15442040301003007103822aa00790b910a462244441304090030b9503055a071381c2141c0207090700600d040c3c02400801200350400310540503208001d12845445402c4080201900907016001503641c403a04011a03001e40b107464055960a03002d0050942440d0001c0400003140760f030603045100e40780c0d46101240f00e5004c5121030480c19 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 858735593 1250 858734343 858734353
    0xa020a1a06180f010b07060b09090601080c0406030b07110f0d0518090405070b0904090f0b0907060918021e070b060306100608150a180c170103030c0213021b 69
    0x3820920082461034445025910101c0703007032000610706108544d0440e03000c408441e0fa155081c0c917080c03004d0070001280541101141003400035001e400705400341600d8060049405000030441000286d440911000c0e0903400759802048541348204410071032500001c0441d21f94003580003c1c98034014410583c0800035401140c0e1a622a800c00100c07404c40c181155504070f21300301500c80030384450f0580b1420203000000920800d50303484a40019440c0d40c0c00c82650b5003038017903070f060602000740d04941040650107480030200d4010700444000050f40c1d00b580000800040b0451080001e41c003900d0070060003140030890f1107000c2c2044009299143c40f40c80c5850180c10204107061400b0300180000c052110700700000c0c0b241541c000410707a4402c0500c0c030501001c3d000384010030b04644c840c3e086440d010b10100030412184210341c05c100c8410020303070f0f126000d180703880c00d5a5085080c01c4c04000d0000b101e82ca04800585042401150200151500189010f809081c0c0c8014056420031101c0e040d000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 858736843 1250 858735593 858735601
    0x3010603020a0806120d030903032c010f2a0c060c0507050d1d190f08030c0f06060f04051b0c0f1006030201081f030f08030f0912030c0a020a1a 63
    0x40000004e4124030b050350500301c1400d1720545641c0b14009904900100355643d000d030401d05120b50009801d0351400905480344184104002e60703250744c0322150301065130030300000442581d040e11998010b1207070040241d2030f55811048101c4140d07200a65641004402c145144c04200c0600c1100f40c071a41359200c0a648000b0392516a05040056240b48280280415071442070007040f5120900e0b139104a91902c1140c2d0242d0380001c0d01210780d00400d08615070210003103000c51002000b000024508411110070115410001d42e896004889003a00000c00d0480354001d4100741e0050b40d0020490300c00300412900381303046018541c100f03003400c1d1007a134048001014100014090010a40d15501051141c86d0035500041c0c941000545982c100c0d003d041c0700c8848038802034900700041c65120f90311950302403460500d00090340080e9001c1d08801801c0011854260002070300703511055840c0078003802d40d900c0d480d41c1811504a0000c1400f98003c0d00070500c001440e0140003100030740308083d51002814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 858738093 1250 858736843 858736847
    0x1e0e04030c0b270615150f0403050309011805030d030203130605090c040606030b1005130b030a0515010314040305090411030c0403030e03060c0d050606070b0906010e060402070b011707030803010603020a 89
    0x81d94001c0071074150802d401744640c0c4200100c4c0c3c1d1146840540d0200306c2080446641c50051140c07041d103003003040000c1004010004040b00600710102c090365988107207407a0180b02034a458080c42082d40c168000281d8200c118000d80146a108605900e0241c03900e1180c0c8510040e50000c44200d14280c0121b140aa12403038a07210342e40240456140401501d00501d0104904100800d41c5105000d030200380c0302c004450300d0380b81402074100c0e4007000380c9070b0900c00812805000301351814644100815900781d01e6500c28402c0038215a1455070a000940b01c5440c25104c5502c0340c40c0e265006500c6042070072304000d5480c0103501a00e034840302d2554451450500900380c40ba2803404a12a030082c0f070920109510442c160b80c604007841d8800141611003600045030391045400092200e0303001070400030105804103d0034102c50b83c1051500880c2c2d10502040100c2c440da5200078445221a070040c029030055040d11186079009000b102c0130282c998540302461b800980c0440300103600004d000250035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 858739343 1250 858738093 858738151
    0x15080109050f430f0b0304120509060702040905030f0a080a0b0109030b07050f0d09121e1413050306191802010c1b0b1309061e0e04030c0b 61
    0x15428164409031950005030032101c9601c20040507441034602204608240115040c001014264029064a59103103c0170310540c00c1100c003694640360080751209180c0c05441200c003100030041c0b50b0b914100d44c603170030840202121a0213861510007400700e41c04100c00c000007409445c0ca00d8076604058a0300e994154103071402c03501c150307040244140c0304100190007403180c140c1150107401c00c90b44650101402c604140101911410755504103440e8a00b4492400d04c02800141d059507a0421300182d02c01c9120802c4901c0040e4002560740c8100c0c4520000c2c40c1c02074252600d44400058002c0c1c0c0ea05d000030700c0d000701552144032061414209608a4040d44104c5071110300e941c2160a501065030000703030007034189040241c04a08069100401810a4601d1102611040503941c3d200c1860041e0702199504074002c3c1f159641c6031580100d000c407800c07096841d18100c0041070b05403503401e050098500140140048060040e0307021040000368800440a20031704c00d105c0400c12061000101600035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 858740593 1250 858739343 858739363
    0x6060b0d02070623060d0f0209070c05010e01200702031c18081b1c0219090e0c060d0b010224070306050913020f06070b0f0109110f0304030315080109050f 68
    0x880c8444c0c00402010542c11006600000c1115200300424540c140740c442c2c21040400294050840c0c000c0018061304041030030b5803280200f000b00036000540e149903007220340c8900751405108010307051410f40d0300507400500300584007030b00391401d40f00d0002441209044808480b804540c50000c595502705072031855000a00c5034500800440d03000c607408400c0300b41c0144c80e0360300850041c41800e48450030010100c1015501415001c0e440c0d607120041303456511140140c03901c09051106140b01c582c40040c006070040c01c002d0801d483c0c8880c200f02e440040021404040c1540600c04107070b04600700d00c04040d540c40d010465034000e1440c20b280001c048940d10f820a5228820410a1180c0d0641c1e40c3c180d40907440d4155031440d003403916100041d07014050b03103600030709252420007000107540400a4080c12640014018480c141d0109912646400b56046d400d0f0010403e000107008240b00360014030307040600032008408262110401d41c2541d008e407600380c0d55030b03002e501c9150401d01c04019039070407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 858741843 1250 858740593 858740621
    0x6020d0207030804050618031c0f021203061e03060403110d05030705031b0405030102070f0c1203080a272603100506072307031505040b1306060b0d020706 68
    0x485425562204070f140554001d190080601045403184c56502581302c20210000904403540000324010810251000c1c040c0c80300011402c208400b04c2a00005081d0008a241c030f050701e055036120414064030a14041a15451a8003000c940400e510107020306409035009941f802304036862191803510704040e29020004001e810030030008042c1c0c1c44030503a80c10402d1038a021128020140c11030219001c1c1e5041164103500c00540c2508021520682408092203005002c08296991404104516050f41d002e00132840440000b01c0b1540c0384c0d8002c80401e901b101c0740100040b10060b41d51000440010211000ba0b1036134040c1c10010b07120500a044801c090088616500d015420541480580e12406005903804100f810410600301381d81d424615010b0807225002191041072079480d4010f210550b4500704040361403804d03105a00409228982181807102d441d121a003040b220024002c0381500d00b103944103008503503000c0f0400201100d4442190258903100281041000c0f203404074040c0c0e607 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 858743093 1250 858741843 858741853
    0xb0a0206090c130f0e0d03060e011d0402090414060709090f09032c040e010504170c0a030f170c0316030b1c03050706050705030a050a0b01080103020f03010207060e010606020d02 78
    0xe0745030f6480743c00c02d44580080401185101c5205204c20141c000940503032081c0c02684481d0302443d03419800341007219055540b010899903100f08032811030310713100c0c106c41690a443c400140503003803518032150080d1182c1c10715610065070120590900c5400e40c2c280d000141c050b00200040b9001d4010100b84c2040c1c0b450170001400169409000e100381c0b01c01e8024449d8408111080c01c0342c0d42074942d1030222020b4030603c207030024000e14a0090600300c40888a401060f001c6030300d0780e109041940c5070003903c1c4008040c8092180c9068681c50303c00c144007010044061441003141d00d0702181203000d005112700040e01ea0400c8c500c2407451030a500c0c07020b01098070303080072403d07161b41b02c82000992401041c00c03148050840c0c10f0403103040c450484003400190801d41480f50403a44000294421443d504003040740391034080003101034426400b401400a0f507100300510252601241d403001218000300014a0b001d52903403070030191b030090782d0452410395441e00200f1071150140141014109648040c2c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 858744343 1250 858743093 858743113
    0xe07090602010c090e09010e01021305030f1b090a1b0c0b070e0303070b070c080412051b10030506030c100801031a0108150a20070c0b0c07050103090503130b0a020609 73
    0x2803031040c05100d1300c4180350404002c42c0c6c6690080d0300c8400100c8240d0020b56a0700d8080d46492041846842281e000744210320701d089070030740f000c17440c105109512202c146891751007004011084d00e007cbd01d2014083c0d0358041205aa0030f00b090701060303480c010b0b2625041e01070142418001600b0050168050286140d0030500682d0044122004d503648503a00c41c03029110a00100c0e180300111400504440700010302161800005080482103841241254186828500c040c0100011100b40c190000e10144044600754001d130421907201c100601152661010240003510141c210421303500070075554001401031002d62800b074030419502614552465141044555841d04142d40400301d1100850220b01c0c481c41d1504001c2e4850203040500040035031034a110021981f029104468007050808005030b11a15901078540002e000c030040c00d030540ca018010340117464113020403a0035000c10000720703603200c0003c040003000c0d007600c444203071701e514020380060314002c00508103209640c4441000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 858745593 1250 858744343 858744347
    0x18150c05090f010c06091202061006090501050f0d1e021c0209030712080d060f090b041b12090203070b07030807030b0906010e030f07181a030d0e060d060e07090602010c 74
    0xb1010009013840c00340020600340c00d11200070001200010012281d061107405204da001407081d0080b0b80703c0d011081407503030b5000c0a60f01c080091040d14007180f41840555190401c160203010088200702e408200030485000c11036541440b201c0c103094581e0f022560010000000e20341203c0e003032020030110b1a007483d01000a03a95000b61044152805c90410b000f03080001d03c070261540111902c109100c65900c2d0402d05495098901030090f980346000e80c4503003645030900404c0809a010319006048040c0010203d95070b42d42c0c0d1502c04041e5440d96019401a1401c003c80401810082c2400d0b4540c085482d0003001103201030301210405013807201030105a65000c41d42c42d0040000d003071100307444110300c000ca0704010070000d10101c10301a4107800600320000740d5038422049881c0354100940d580d071030840610b4801506640390554004031012507414051a0f109a03840c0e001001c050070700c3c41e5207203848180c4440b500807102c00302a0f034040c03201c49500034440c0703070203001d01e0300003406005222000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 858746843 1250 858745593 858745609
    0x90e06040f110111030f091e09070302031b04030c090605060301152105070201050601020c01020109150b040b0a08011e020403020306070e0402040f0806010f06020106060801150318150c0509 83
    0x80079100b04a102e40c900126800703500400205016001a07a440e0320407018296105d420084100e0b00400040300341440c04408840c404000c020014442c10b041d484e00e4404030029000104800301e14905600d8040102140e0785c05080118418247c0c00942030401d000641510125072003140036413810301c018007000c0150814080c41c0981c03454140300458050340c03529142c0c1d03659906c1516481c0792005200340c0c15410b4000d03d00ca08400c0c1c00b2190b0551144004a08990940710042c009005218400306410b032130740c20858038914000c001150700881a80054003408482d80034070410f07035680144040346000c040e1074118800491000b18103007440c540108ae15103200800380c0c03041200078800d2415590311581903801034200c5008143d809900c4042942d501e440c203005280c0210701c0f42e00001102c4e441401078400b40d40155a54a2080c2d2030003050a0004079031115442c180343d224404d41802000c09900440950702451000d00752240c640c901c80202c4a00000354401c010040001c60040e455042e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 858748093 1250 858746843 858746873
    0x1180f090b03012a0201060314061b130e090f0105100e010b0f09090604060e0a020a0e12070312020a05100f1a030303060111010608011b0801081b041e090507090e0604 73
    0x21882c1500b4113010304070300401194100400f80568040300a400303109c00203586226500000c40c094920b4806610181c1e03501410f15006240010b01006011210516010680104900e0102c42203134062502d0300d800c4d075404503000d01119004140c1000111101c00c00c07a40100300c0510200d1400c2241640030701c882c4160300385071b400b40c8107800c00300d91039403a2a03010800400640385118403e046c40141d000c080d40c0a0792a0b00c000a9220045c2a25440c16400158950904000400b6454519a5a10080351440e40301209601850041e807006c100c2c14403003241c0d10749018a0004103102c1e100c03000811210313000e07000c0300000d440072015021601c00000701c07a0018000d08140400a0002c42018098206500078002c2c03542403d540c0f0307682c603107202000d90240d8802e4440c00c4c1c6036a01c030f015103592408480c000c50811007407040c9111050506a0100f00c00c101410400050205050f401e038050300d5400ca4115801e5002e01410441400640f01c0d14580350100c0016100e1410907454400070140441 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 858749343 1250 858748093 858748151
    0xc1208030a020c19060204050f1801050d1509050d14070b0609130f050a02151c0b0105091c03031b0806040c17070512010b03090d0e01180f090b0301 65
    0x203240c101030314104402a070b40491391441504804007484e0a101a4006100390f502802d14a41d81c60751301e18054a6000340c105500d890080030f41e21709410094141001d0005461150380c41c0020507000b002800340e030603013900900040103041c0303210340005c3c041c0129a45001c02e0240500100d4006810380c01540c1d04043d04841d6000d85855480c006080e40b44094401852050000c9450003008130105141da00c00e40200c80d011620f1701d242c0d0101e80c09100c0d0723901050030141200b4050410038000c3e170180080d40710600d0701d6410329070043e02140f101307420500381c04a00c3c054400a042003660601823080714401c2008101a44042000044d1219001030000352003681c43d840c2c0a450944648807900c1114001c0c00c0c4e0850f2804e00010140072039101d039008201c001100000407889990090450b030143e04050010104003948800031221184101d4070541008183c50800c0c641070207950302100034140e0188002103080c41d140c220000c507040070240a0003a4100410040d01400401d00051414204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 858750593 1250 858749343 858749347
    0xc090e03121503030706050f0618010b0f1312170a0f0e040207120c030f0c0c0902030402030c09090c1c020913110a090b0f040605150d020c0303040602070c1208030a02 73
    0xc1c1c0c6a19404020b48006a4040c40b0100300314003888542d402c40c40c081d500d06c00c0d11144c9a21071805120850b455451003000042d808801000701200c0a03000303245107041d01c1d071000d013054450804a10546916804400412191480d01007800009840c0200c1c0d018650300d45858018021000b505007507a03160840c007030040014441c09540c65940403909a00d5200342c1c0b40384d51002c03194003e0b00b01c0c1c900c101c056001428a450102c281c501a80304084030541140b00d48840300d02e0210044040c0d03000801c102c0c0c16000f03c3c03c00c0e0700551656103820380602d00c0d41e40a014911001018000080769801c0b420100302070030b0000c1400740e214080d5450300a000c0c40d03091004007108d801d00f0300b03960710a1290302d13400002c0ca15001800003401d5002c0401010300b203980100c2d5805039020017003a2001c0d8041d10344d21090681d181d00300d80c00b50340c004080b9041900c0025081c84a08800641181c00031681510306e25000150303801080f10700d0045002805255200c03d02c4031020f034507054440d01008001d51030325540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 858751843 1250 858750593 858750601
    0xc140f0904120530011e0803030c220e07030f020301050a060804030c0b100e1f0510020f190b0f010e0f0a0603120f020d050a120203040609020a120c090e0312 69
    0x8251074410490b8074203085480003002008160301d43c40240701b004000f003a800d10704a214a000f030030200031100c200c0c00450440d184c81c0507030070890b485548070b00b00045012449449080e010f0320318400416070140c411990303141c4840c0143c19192078103076010002e481040144038942e1040c94240a44500d89400c10065a1305d107020b58070700c1c00c0b181018003880721131006c10200c4c03000a4a020252541c42e000b0b4200c54039802d084407138915004050f4000710b461b2440c10310507030419181d02d509410080c4115240318800707013001400c00c0810f008008010040344102c0050018142d41c880c0c11003603203003001e03e05601d418a001400800a48140c0b48403140c07a01041d004003041c0c02142c06036812902c060f420180d100000340400e0f800c0d03505c00015004204c040341400340600160381e10a980c41d180c2d001d031030020000300c20003540010b000310b0700b0f02d035904030350700250b20340710341c5000500158001c0b400d461000d030401018010301c030360010030150305110b00c40312900710100984201201c1d11300e00c101162a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 858753093 1250 858751843 858751867
    0x150b040e0f1f0e031818040506061002030f0c071a0403050d080a02070c170105070905031e15040305211005090711030315120c2202070c140f09041205 66
    0x8900c500095a0b10020400304103081c5030020346005104102c8003281c04000d05006e8502d004e1003100c010b40207800c0140080c0d4a828614104041e9107440e10549217086003030340315841c09130000f512600d0750303502a040c18001d4016480d0608a0030b45080816424a843c69854954448001c44120204500311002c241a8515134059a00003940302501c0340c43c20780c44416003c3c81040c0d4903822012582000c01040c90b140c0100300041c26154094050b1101032840b921004214401804800c2c1c1441419100c0a07050000c0c101c03240120b20981e030f1181d6500c41c284080301c1da00540700b110034810200340144030068140040c004103d0b0340030b55800051b80c2d11000306817a1080300b200c421030300740000000c01c101c86400b21010191000111042c0500d40701d10045a0f954003c2c07a84100d8100e0b148008450000d01810245070348140c035510054a0107100d035031060559025503000740040183d1400c074520b2841c100044c0003442d03109558500562500d44c40d83d1a100c0a0240c6100500100044007031900c0313 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 858754343 1250 858753093 858753101
    0x304111516080a121a0d1b0b0a1812030c030e1315090b0907180f0b07060501062d0203040317070203120f09011b150b040e0f1f 56
    0x2200d600e10050080e440d0070200e10a6101c2850000011211240030b105403c2502c610324401d21703070420510304c01c004001482841031303e07140d09403901401c1c031000045031000b50303074130342e0141044072a05503c40c00c06102c09007030a1003200d42c1c41d084000581081c465080c40c00001c0205a8146c80e101c05224618103050724000090b01406401109080c13080d40a60099080345103511034074503070903862642d0b03140d00208482d142d0710140e500180a2000c1a0707a144209858168059030101c103a01640d0340c1c8240b00040d4451381d028011109020500c1e100340613661042034010129800c001401c05141e1202e20880707801144803c55080d5181c580d202c6581c8200107032406198170900c200c0705c01551603048082a0002130b801c0344a0300c5001411034031424444246c0781034805001503182410382040040d250916055460230070585420316503070224001e0505001710302c0c2c078604000b4155003424188025507030124881c00c917960080e4000e25804d00d00003141004d4a444151f07800c036001000c05800c000e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 858755593 1250 858754343 858754357
    0xc030b030a030f08040f121d03010204080613020a0e09060a1d03070212032a070906030b01120201021002070b161e03020c010b030715030f0b06040303111c02010b1503041115 76
    0x1c007a035001512199400448e0141101400d621b0860300003c1041018241d1285026a81c055004000440c401515079001c9941051000780462203440d103907036140c03800c10300c1100c09c01c800c0d900220521242e1141449500110780300f0406000b00c0903444048c00740e8910501100900815621003403240c00d031024015950606203043c000f240703003403854581c41440c044100d4461000c0c0a02e11340050420b805125a80841e40c4c0500c0503c3d036a072910064199405907924281d055004956084060304218401441424840c8000403510b00b4240307410b0141c40c052925480500c000350301440c0798022380702c007102a02c85452401582c0e81908608450241240c94080e60700740c41141030100e031688420380601c14007034166a080107050200710321702c000e8030004503555801000800003030011034440c5a50300c2d041007205040f0f40171100d0920840f4140c0640501c01c10040c0d545246a2116180c01d00c0364940201500602c6419410240c070f400c0110b21242035900e1140007403000311402c020b40c5500b03640d08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 858756843 1250 858755593 858755603
    0x708040e040c1e03020109170a02100c0b0a02070b090105010602030306100207031e0510051e090321010510020102210714030a05070e03160b03070504030b09010c030b030a030f08040f 80
    0x50040790100c0000f141890100700d010901c0450b01082c4400651942e00250369000b004116081c490b07000e000c08503800340009020040400c10a001040141c2441805040808001039584c0020308000540f040090001401030741400010002580e000007a6500820f003111800c10040340b0190076450041035605c001c1000440410115038140010712080000b0f0280042e00c1d005c0403a1107082e41110011520100300c0c0e840501e00202904005c4074056010f40110120303864101030002c103001080f05a007440300800c031203000501060826908100e00c840702400207504180d03480140c81c24280e0700031403800d13032800c02100044485201c0d020300540032080c2c0c5112a6682001411311002e05000c54101c40400c1d100b0085441da810000382da50041490306020420039814210304503080c1d40041c00b00030402c00d09000220102e120102414001c00c01400009014280e03114086d0a40d603811130b0305440380e081040701c0008a5040740d259000d2205501e040211584d640c5010041c1040d0341c0340140c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 858758093 1250 858756843 858756869
    0x923030604050f010c08040b0112060605030a1202010608010209060f0304060212070309020411040e2418040b01090204050a060809030d0227030f151905040803150301020708040e040c 80
    0x40c0480070030046881056007000b0f05c003900b01070300300b90341e0610180e90003050302c16410300410084915480c06120a0701c1050041905681c90b07000910f850b80546054900484119500c82402d80904c646c80c004c004000003541842040800904a409030b50200e0800410000000d0108035040e4116034000c84ea05000d18403d00784071350010300812018504030300441c0350018800098100c3e90550b000c030385c001120301c84039035a0840f005c101d200b0b41c015521007a0064004900711680c9640003241c07100910b0581c04441e19181c00c00c03114209040e4044002c55104100c00c0c0315603100c000b540000e851582c1000d00081d11a0300a40c0d25610a41801c0b00c1c40e5840070880e20307104c000304610303000303039848000d60004040c2c106420035456a0304550581010f601140040801c0b41804108560009900d8600cd402e039100030025020348008a90071100c01a0000400040401010800c1c00c0034205a008504007140342d52040810300c80d0703001d000c4019005200040401031942040c8001d4207001443c41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 858759343 1250 858758093 858758101
    0x206030403110d0903020f0402070611161703072a021305070f030506030c0f01020c091618060207091812021f090506010b0a0917100b0402030709230306 67
    0x801400d0000844416402020710140103184200c2c8004c2c182c0c0e130010401e03071074031001c00304110081d07100aa04079400c41c0c56220a1550946507000350814540424410103440c40c246411000a043c001060081c501d0074410301c10764a9114051040f00b062040c1c0b400040d610225915544006038440254410100c0d03200d252510840d82045002e440303103480d040d20049420030140d09940088400039010b5014084500403441c0010300e2150a05040c015a495038007010085500408100c0c0c0c505000b0640c20cd400c00d074558810740c060786403004440c1c0080e115082c802c0003900d4040798452104120b448100403001c841c10200c12008241d03204000b01902e00c40100040e4031384050000406000c0ca03a00070070807265015006540b5210381c0540a003640744c0c00c00c5400016030304002c1d00001007188501d008514107000002ea0010351001c2001804101c06108002044c1c80201400394000d40c014018040c04640050200c3c00741c6200d0220410200941c0e007103101540d04844403254580b003080140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 858760593 1250 858759343 858759347
    0xf13080307060f0b18060418060506090108070324020c031308060106180b0d14010f03150207030503130203030c01020703050d18081603090312020f0706140409180206030403 76
    0x1841e005104110610110f09800d540e90121542040790b584c010038001c10f44c110300f0b40b041c5801c42c1c0c407001c001c00006506407850507016620304064400c0b55416910001d01040d03140100490f801000c004006007103040c00c1d992440044024140818020041c1c1000080540c1103501614079010401c2c048944480c1c40030314410f10102d007031048215030700404d400418030601c150612086c1c0740c3c100420640051808283e14010780c00b10070303940c0046560303e01d64080359058040c0360f8024514440103009036421802c1007a8103200040503568030303920401642000903000001c0d83d90000c40d00d010440c0700c0440e03001107400c5103d0120303050f903a1351001590f03504240d080001b46c41c4020903824104840402441e08400e9003034580c03c06013010300213210742d50040c0380c50783d1f081403818841c0ca000114690340f03035105032000d0007881c0c40d0005078021010282c1a0542004003800502d19460180d00018040702c8a050521640c0244d02c6015201c001403203011849214034006694050300e02580d03440c01e03040c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 858761843 1250 858760593 858760597
    0x3031209070315021209030408030a050d06050d0506100801140a18020a15091e03020d1a07050a0e19120623100b0702100305091c02061608010b040b0f130803 69
    0x248490b01700007103030b0301d00c9000044d1410340c6c203081c00039403522541401c01c0c1d445d500140e003040b241d40d80310000403036a51590007460a0f058410030043c4020700b009003410b0717444241c0381c1003200c113030707140103c104d1082c01c074004003a401480d540740c00031742c117000040071200480411101135088014903c0002c0c240e810741d440044c1080c020758400746016150814914001c12070301c5030001541140c4000d002502d0043d1011641d40d100700004107440540c1c111006519030110361080120b41c0208165804c02e820804030144684100c81c807451107480a40c811040c0070542c02403001c000030008191040088981c0102c104445e611400d01a058010707404a4003a84116131144220081c048001491340c4060142c0c0e2400354001c140c801c554100700d104078024107005204918074860340207415810301c8042c044c228486281c0d4050071051410450808001030b0b5100003008106040380100074900030030003030b00d080d114944543c0b81ea03418492404d007894040d422800e05411905680081e4038600040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 858763093 1250 858761843 858761857
    0x11b080901110f0d2403060203190b13050c07020301020301121b030308150a170105150f010801050d030e0a0e010e07030b06070609060f0f0207050106140303120907031502 75
    0x1000b8480303901445071105050062062400c060003040c01003858404164210383c3c040d0480c03d4204000380221004c0482d11940c581c0142d0b0003940c0002408000d880d11400c4aa2044c18100140201811030b404550405901c98000c200c180d83d070004510220a040100d40c01540c00800964907541c40d50042c840201c2c51000450310f0132818000c5600b0540c518950000701c80e01503c58655603500c13400385485008081950980c490030520300400e0100c0003554200341f0411540c000078040c501880744032050350044068a1062240108858960780d1002500b815a10180c0b0030510381e040c03900d000d803030801500000580c072004034503020440306420703501281225400301c00da48964a80303c2c015012a20041512a00140200314001c00324003941c101048503841010001103001c2040d8500b0103d8030840340141103aa0001100b1090020034082e84000d03107802441d200000701070500090303492081c415002d03902641440010800c4d13000784007005c011a081005e42060120b03440f007880080d80002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 858764343 1250 858763093 858763111
    0xe0d0c050a1d06040c05030417091e031b030c0613120b1f03030c02010f180602071e05010f140702090424060807090e10020d060509010e130b040203011b08 68
    0x2c0000d0403860a4016281d03c11031546505146860301d8407001c5500f01c2460b4000103101d01004451f100e80c5800b000518070402d03200a800000c00850101401e00c055554030300f04000c0b030104070540565011030007111310107084a85654441780b04603814040c125950101d110310800f8040300f030a00c80d0310350f00707903200e4085202e41001e0301c5107441690044c260035000140004049103148030040d40140d03100c600c04000790800000e48085441809030300c0717840350020030043e046200104001c01c9114045070401560900b145d55042c1004002001b20782c0d1006908100080750200d001c141e450581201c42035038010302100107520f80340c2403228000c08811a03400054549034404e2205103090312442043d00c9014025140b110301e040d070000050441d0b00c074218258000c0c040414004000c0c0d06c028520366428580100d5128030300801c00005081c140c0c00000d410b5140780801446040220440e004298041a10a0b050f11075001190050000014000c500c0c85502082c1d02c4081e00324600d103104403541 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 858765593 1250 858764343 858764399
    0x2030f0c010f05070f060c0e0301090302010b0111072108070b011202120109050a03030e1510030b0c030112030309061b0306051509030606131b030203100e0402010e0d0c050a 76
    0x60403044038035100310f2030301800065814170400001032440c1c1146816100303501d00700923400303d0000002c1c2160110700088000d40c2d590150301080d940c1042c1c02210600300d4201803d025441e040c00440200a00da0400c104c40e81c194011300c04018086003034405094022461440381d607152380d5100d094010314001a48225144805942d0b940b03814003842a843c0d50000103481c001074075541c10340c00703081880c03828059800b8403e01080301e46c1040d03540e544200698506070032003d145080800060ba8064550f842104040005001c80f249040303800310308546c07500e070000e1111020300700f000040041c1024810a54042c20307050080f154503403c050286c5000700c41034950a142180081d40a00c1400e0880342c142e0412000600300b841c002c81030340c0504803040070101d144414490803501d0b022010210501182e4040300b801803242c2c80003404009820030160020240c1015000070302100a851a45481040d079040714400300a03403061b81034000c20740034040880311900d030703210303002031b02c501c480740300911016 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 858766843 1250 858765593 858765617
    0x30d15090216030e0a05100c060b0f0d110a0f060201050a15081e01020c030f12071d0603040309051f081609030f0302010209060f040819030f120902030f0c01 69
    0x101d1080310422101036858a02400382e07598150b480b111190529503101c02012000511501c59071074000052595035075801d20704210746002d408447d84200903a010f04584119001591182c00122004a0300024042c16000f40304000807820ba10702c2d000556a00010180044c04a4054000b036001f040d40745400d11029a44842c8103142604ca44111242940020072101e17606241c400324030354143c0b500d0005482c0020740303e0740a1455124a070b50400340c9000291004c5100740b4a805950007004518000300c55111108014900c0001c080c005481003000001240402d401a0f80602c0145806403842d000c00c0c5036202e403076164100b0300384a034001c0ba5a2030002202c4c0f98507001440b0510a10f40c82d8043c1c101e0554503201c9992170165011829594200b100c28850340d1000041c103040821440c0c07032903680d810110410b0410041300c0710701584000b100c40240c000f903000b80341400d912550f0701d40284810201948400507218522020b50940650340c0c0b0308002100200341c4481020003030301e5030003081d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 858768093 1250 858766843 858766859
    0x302030609160902220f1d040f08090d050706050415080606030703020702061608040906080312040201030c0306170a0b010e0112081e0c210903060f0c0c030d15 70
    0xc0c0c140c500d0865500301d070018016103c044d4003811101c1d01c40030740c40c0310420407880d2100c202c1c03080c1d0700b0031805411640780c100006070000d0f010a6115000d014a012103040960f01c0c07482e60b92000e500101950f401041038041522102c81d41300715907800030101c0e8907071039482da000340c8564031a002d07003000d5203903c9094525290103002c0c0740307001c1c0202a11082c5542d55101080780250000c11049034880c404014184154001b2840400594011803507182d032186000c3c070f000e0403a0150391007584640c20504c82414800340c207420703d590198083c2008904440d2600c3c0480090a4a42000030101111956010710500009015910b90711910102d103040c0d0300c031406180c1c00d03203091289025500d4072580090009000d04003a220034402c0300f100b05103d208400440f4241d801a20b054201a4800c1c0c43c49048040010085200e100440c5c00ba00e2a15413042d0100340c98000c01030031500764074404008121441c44100803103511241c03d50690361940c030700c0300046026100041c03104031300d807111040110710301c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 858769343 1250 858768093 858768103
    0x506090109020f09060406080f0309012307030305040501110c0c04060e13061109090406090201080106080606040306150801020a080a1427330c03130b0a09050a0c0302030609 76
    0x5800074280e2076543e54250800424640c020102a04030781c03543d10010361070004110408120310f540004e140c0f43e5138040f0005013031a1004c443d2070201800004a542ca8621003c100e80c240382d0145400328445d550790407c2809050002041441c0c1c42000808054020003c10298172010044130140310159480ca90592400710503154504086d02212000700000e01641c01005407042c00c500c843d0925407078200044240030100c40550740e081d204c0f08044115030344132070401d003d810182410038081c1010700c04254140201d003c014103127551084c2c100b9071a40382d13150340c00080c500d50f4000e40d6a01102c40d070051a40ca07042e10a050f10300c0c1440f00000030604007044e220301c0340512104802d0106840344001314540d035200c000c01003500581010070203000782000b04032141c0350311807e05180303508500949001000300070301c4007403103801c140181b03e6854031981110300655044040700c081031722060200001860b51100c0100300344540400c1d0f2040090f06841102100c1c021070540e4025550301400c90b44403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 858770593 1250 858769343 858769361
    0x90e0a020304020108071b240e073f030e030f241302151e03010f06050c030d0203011203110a1a07090513020904061a0307030218100c05060901 63
    0x2082945002851b032074172400f2944c0860b101000541c81c070070103d407918441e40302da030301040c0d500b412410034840700130201c0d000300c1606190090042c00201e191860380c501a03a51060310204034850050306501103100c182244184000001c541e1614444074507001d00808408806980203018540104000c5140400c0d0690011245800d03e00c1c0c20032030783c8803100071200040426456814041da51030140e150b520030000841606c080c0e00da41d81e1400404039a4021002c640b18044550070001441402c094101ca81c080715a01d0030507684440030f140c40c8034258003802d00c165448501c00301c000204002e910380519200c41c0242c407100b4030100844010341d1101c1c1d0001b4080c0441c4518581c020943c1c0e585150180c0c07145540c60420b00032503d034030005aa040c99808643c110a4000c00ea0262510381403180400030a0704011010b04c141480c5070803040c80c08000c040d84140356020407410380103a075420113100703505002462450294801e55002d0445101e0b14005c0c0d0351403044200003103001105110300c5c820 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 858771843 1250 858770593 858770597
    0x204081903270504020f0d020a030510080c010c0b040501060b0c0106050a050114122206060302030c06070512030a0f020a0503070305010906080c060d0e01022808041505090715090e0a0203040201 85
    0x70b120f00748000d00020394006121045010010007001013400c02d588068452000381c1c0c0d402003024100001841c45c07145168000e0107181e007041c1032042c02c1d61b0b0040350501c7d010f5407003241c803059a910b80c2000360041219900c8801d088100181d17102c80c20506600c032500340c66080314000c031a26101c400440d81c03803880200180541034200002e038011120030501d164480070040440006070207209200801e03a8006804441003074807144248110715050010300b5416a00f924407a00301503154503040c0d0780e49440065212503800000220310044090f07044200c5035058940f0543d5510300507900100180e000321003a00020b4907002c00480c0d4620030b805200c0440c1c1c00c030002010100141420084180d00450001c0d64159845614030840c43c0e0031300107440c9128012010460701840d50f220301d010780c001c0f0141c0800300020f140800001501d101d89a80c17440b41440c070005031b103590f160100d91802c101c0b60466030042200c000840003c0b98001d0940c410b540c1400706210301394403044c40c080280d02060780d000340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 858773093 1250 858771843 858771917
    0xa051f0609021201060c020d1704090e0102120402010f0207120b01140306010305030a0323180d08060d2a0e0907091b0503041502040e04020907020f0a0311010204081903 74
    0x3105c188940340c0204003600061910070004625580c9a4503048080d68600381c488020038100041d08c00c504c945a034410201c00254034001c0360f40c040c1020080004c100a040c4610200d40e001054400c211800103040d04d0424a5521440303410081641102441803043d088041080400581030121b40d0504030f0350b101004500748403448009401602542043c0d005d2800c0e07281d030803155280180350050180a245011031a24a148842d09041955102c104000c1c03120013018424151126200d40e80c1650f0010013100e101c3c465210a20110311306104540005034a02d00701040500345c2c800043d000300101000c907100b1540d9501d02e00b086d12080c070303640d00074000c06070903e0425074024001161310512803030540042141c00020202260025088124889040001c02086003440109181c00164600003044090200010309950f084d04e918003d0412201225540e00d1500035019100a0301510082e0707024040d0202000329402c50004013a40003a50300160004d180000c0505003104512451400c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 858774343 1250 858773093 858773099
    0x708190c0c03110f010204170d0c150f020405030d0e04201c1d0f0c040204030b06041e14060a061e0c030c02060301060815060a020a0f050a051f0609021201 68
    0x180c0c4100f00303281d4100282c080e00750711000300c1d00c0c284002c0c00600081c0c460094080304d0b9802031844c02c1c01040c2c070007081c030010350b9071800401d600c170740760017000c0020000c003050f0000084134502c007a020f580d05c6990584200310b000101c190f003081c14400283d00a42d402c001045180660020b81b8400074003202420f001004040c14801c05000090000109080086201a4940162108001021749404a5402c42c0450914446040c4105c0e2070300141107034158141415501d0b1020820000b03800140f20b03a6407030405141250f80901907004c0c8403090078003080070a1030405c00009689049603124482c82e0000c00200c0c58034003500c0c6403414655030055034070b9000361082e0305841a422101040c0c00340884202010010713034038500194007030b058541c1e0b541c090b414005103004012241c0580f00c1e02c50b0f107040c081400d030641d0004a0003001d903044103152040e84458108542401000c0d98054420f010700109041c41c4000e04060317a1003c40d101c01d00700071803507070342045000320300a0303900b01000c003c00740e0010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 858775593 1250 858774343 858774347
    0x50111090d200306011503060b03100b1c020f0903061b09091317040923310b010515180d021815040f0b03070605210708190c0c03 57
    0x11040006400b480264070b2200b480000740b80100980c030626440d00040c0d44180400d905002d0744004145c008045405c60070302c001010384c0c01049000f0740c0c078499804195003c1c0c031002c07502282080040c20600b1550760707900b4580546640c0c00302c04490f00900c59000807c03440e6600d4108100991001b240e228182100d00041100d16600079200e5903003810a408410040b464400b42803601138061f034401d55036586800030040c1034034500690f602e0003402c0f01c58039200e04566030b480302e980076030314039000161080c100101e02d00b41c2d41c01300e035698200d03e807010302c10003048019403401c3d041e01c00444403241f11f80520210745225200381000c98028900082d120112800e2114140c6c40d0b840c4000c1410368503032040c148450354030008843e000c001001da5012100c550801c1e2080c40b4a0684006062003900003003004039545415621030030041000004170701c004080c0700e0301079103461524008007150b141408000288041c00641c0c040c440b00c1c801c464440d200000301e100740f100700c450f42e80300e000b0542826142 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 858776843 1250 858775593 858775613
    0xe06090d030c2907181a070c08160e190504080702060a03330b0304032a061d100b061b061b030606041809021c050111090d 54
    0x1103041c000c01040301c0c00042c410283d5111518800101e00c2d03582c01290300c0c46049003601600c107105004041d07402001101c01c004c902c0c42030324007801e003000f809021400071402a01c954800509030540307036076010420310b60114252402e030303031440080c07201503032038007280c0709001000d0300c001400e0350700007501d0301507c009500015486070207011010b0520305180c002c24480d40c0401040c2d00002d559038042c10b00940c40b4000180340c0400c1e0048035001c0c074400100d0340c0340302c03059004069170564080005401c2511940340400307101500091a00014803845c001c1a00004200c030450380281000103075030031141c010503140348180100004107100c4100704041d0000700352198440d034001d102000740c0300c0e801c1004440704643c00b00e410b00a0200c0d14101610200d24240c00700c54441c005420014813001d0342e1644292401da800d04144043c040d9420324114009064400f002174001314424000d0031103001c4a9030070494640160028014a40b64912a036024480c035000d5591001f002260748003c0341342400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 858778093 1250 858776843 858776869
    0x50f0f1c1b06031e0f110c0a03120b0a05010e1c05070e06060703050a080618010605120f0105010e121f02070210020f100216050303091f050114042f190e0609 69
    0x1e001b600142e050489030311401c041d00003544101420000c141d03220740c411441c02030342e410401c15011544c1c0041c006d603030304e40b150b1030400021070100c503040d6858140154402c2419105042400b015290107071311800280b080001408182d070015580e420880c044461995150350340d9413816a003201d080e0752200c000307020680c002c40d1000010072191490f14059002e84269116075440d015003402c10316264800600b070120070004600108400c0e604003850103071050701103031143c1c0c03052603101545e86001d00c41440c40d003084402111a031841d0340c940e402070841034001d0750880401d034040350099980d02d51103000c994031a400714800082500807540540800f03407001880428a0025840d0180b540d0810381302c14481e50411702006c0c004410001d107454600000e20390600c800d40c501007007c1c020030381c80007005010b9502c0d00e0b0f0700e8075201170149048a044125171050400d01a507007407080c01a4000c45071001c034801403d0751110106024984140d000074009140c90325080c400d5060040e406030170b074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 858779343 1250 858778093 858778121
    0x3210f0318050a1b170307020f011815080702030a0e04050601030e100c031b0e130f1a0111012a0c05120702090c0301050f0f1c1b06031e 60
    0x140480010000e000c840f1469005407100240e051203484095004103060340059a00e420340400050090404025942c1c1a03804450185a4a00c1c04005944000410301e4844110b0542c1102180e40c61425031a140c5c0c910301c1d43e41c0c2c200240d07100e02e41030740d9920515044401080c0e80e819500300b180791540040354409010301d8042031030342602015500d403c240d0120f060b1600e0316907021072091540351241040d21040c4810b45481c0c0014600c003d003d1500e81c00900d070043c50070502c201c1114107141c008192003402c030a0100540034a200702807000c9050803001ca0300045400030401c205034014014505480c81701095220020000d84aa41910312a464224103105452002d200403410500110341c080b1b605c43c4c0704c1e036601d4200b44108141004c00074150310240c4000e03c0140040d0b291040200036214042c4c3d10055544070110000b98035040004860240c6034400181e28200054401000c1d0003468840544081540b40c2e402a4240c40c030721a9500015103ca00300d004240324280c000000c1401c0320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 858780593 1250 858779343 858779381
    0xa090507090c020705031c0c03030506010318050607030b1905060d060b0325090b0403032123090606030607080a020c0102040f06081e01090b010302041206050103210f03 74
    0x910380240036141e4058154000d41c004d0f610402440c1001d100d0048803041011031421160100384d000340104c03140140243c10140d80b000064010390280e030208442d800c508a100c0e0402c206c51070302c00da45844c00c0719100300103030030140c9203003141c1001e44e52001181000344080000c81e08017800c5c000c10303030440c08040c00603644400c400140340362048003d45c000c00b603484001042450681c0305110001c28010700204000302c9180803c4542d07050015281500d505160580360442c9002a501034588840c0349140707150700d40000594001c01d512005400c00100682103070301a0b9803030f030140381c8810302100c1c07a64260f00043e0009190901c6142d4441d8403440141d001814190400301c1c560032a0800d07003041d0080d0300c0c8842d0034442580c0102c03e0542c0703c0b03201c040c0c000ca10289481c5030301c1404070611541d481c032501d56040080300e038026016a40601800148100b104965007400c8002c1c0c8001cac8401d450b20052501c00384001d03007440340012720003586621046d004071140356040340140b181409004d491100c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 858781843 1250 858780593 858780599
    0x3030d0603060903090f03111002160e060f04090b060906030313060203091e01020714181905090d020604021c0b0a1d01060303020a021903081303050d05030f0a090507 73
    0x103885010302942c002c1400007001851407602405882d419041b100482c102c41c0c1c2c0c208001412060542d1007100181e51940171144582d200781d180107588d104090140724000ca0114848000e06085271151008440c0141190403c3d0f091104540380c1c1e80e0054484405980010500e003000180c494010720040d0869203042c00d8440e083c00b440030550081401a0030004400c0d40524100340018071000510120b801804c40d0b01c0f001039601c074124483e104d10215801200c198558501d0b001440c800002d441000681c0b0744026880240300d890110601d02600e01400f1070780c404e10029101d9001c04030f54006040684590702041840c0b039003001d00203c00e0301c03c51080b00000c3c81444800740540e00350240820342100c01084906204440c00c480c50b5660300d060001c2000c00d13400070300b44503040d4042c0d48004500054110700203c5001c10f40001e41b807502c00044800544410b110481d04903030181d0309441c50620700d9001114180f1054078400a419059400314808408039030120390b04510642c2150b05481c0c1e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 858783093 1250 858781843 858781867
    0x306060e0618010c0f030c0501053303010e071815060909021c090605060306090d09060302030405101e0e060402010e19170f0106050d08121005130501030213090b070e0303 75
    0x171140e000b01c00040c0845035075801c2107424014a500020b0307004a58580300c000e83c80c1c17040d40c40c280d84450491042a1918008940c03000e50125001c0070441042c0d500c51900c802d04250f03000d000c606c5441c080d9140c0340c42c1580e15808032181c40280e034660f580b101901840c01e040354001c0d42001ca100c4540000408007145845c4641c496040d01c2845000040b480703140c080700f050304100700103012000903003164503052030b000c0e40710141200f99031a5080040c0c0300e032a94140360f86009440b2003604502c1d490409288500955007408869510304214240000451a4030040d04e03010b042d900280840c010707803500802843c0180f000d403040c249540413241c025661345680f4000001429080c40e02e900a038030078001c00c110a00920014043c00e80c1d030a2038442e89683d40c09100d00c9400b982c5500d00340c0c42070120394410304801e1054000d140049c1500b59a80d10b62100d840181020301c4101d100302c00480322429401040e02402c400c0760f4115204050b1035646a109858400320100c4165040c0010003404607411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 858784343 1250 858783093 858783113
    0x306100e0a030b27060613180308060922061d1518031c0b01180b03160f020705010f03020909090f120f07060902010c02040f0c0306060e0618010c 64
    0x43c01148808214101048405901c144200740c00c138440542441e0382d04014000562135400480c2603503110201070041f4030b601d0041c01261041c01010101d0f000c0c400c28594071040040c06443c041702c0c045c0c80d545412400340728000e589149002d401013006d500700d01140884c0d0049801c0d8252607004000402503141c0142400b605900d400301d400c2c92441408010b1009a09440c80040401c004510b8a48100100c1462400202c600540651151410380c4103034070070205910b10150220014038007039180c01020940350000c49041c108400780f034488d00102031245408007101c82c410340241110500704001181c10f1450005c1321418103400b00700f590700036121403064622802803c2d000c1c01c2c420100910341c2d41000d15200c410a035101040c0f102c8460403200c08104c405095000000280c840d6a51005a581003502c0c980654082d14000c42c6044a0741244c2080390504503507901040b00b541c540d101036030174030041410507400040903c0001081e60f6019038000c11000305040c03200c0c50081c0c0e9510000c400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 858785593 1250 858784343 858784349
    0x31b0d0305040e0f07020118020d0b15060a02030307300e010e0703030207080d030501030c180f0c020102090a0608091e0307141501060503060906100309080c0a0c090606050306100e0a 80
    0x4c460b0510400030495421f114041d0302d000c0d124807840d24030b1069000501070700200d40019107030b003a804010807a0003ca24070b140445440180206885012188010392030750001c81c0d514000c2119201d040314541c1015140440d11700d085074507180711000c080c810100400c005c03001a18150740c4d03800381c2500a0300c10001000214829401801c000e42409241801e0480310000a030605041400502c001290b00c0c05a1007a26070b140a43c1c503410114410300c0d800f4122504ac403004040c644220100710703030344c1900103001216040e111400055551101240c601604458114045c0c0001c01100640303840000e60400b4040842e0849060000607141c0501c2c144108000300e680f0343c4841c00351810724482c2c001d0140107240c036041041c01c4d0720f4110003054650714000c0c200b034461100348142d01030b014041d91040701140d4015035600d40f592060742220f0340e101c01034007051721031010840c400600c0403e98040c1c1015660542d48003800d41d107406c2c2c1404080c2d03c0880084044c09043c0c0c20650641d12040e0000d001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 858786843 1250 858785593 858785611
    0x1a0f0705210417011506230406090312080402012703020307060302030711010c020a080922150816060e1206041b0909020a061223060f031b0d0305040e 66
    0x20b40c9203031a6100940c0b2003012034400030b99041424419410725607880034070488242e030405000700b0104510703045011041c403400c180305020124003c00c041c1d5102c120318003582c1c0b240032070b28050352000c0300a50f100042102d000707000420f00c2608180450200c04900c80c00b41411119420f215241da0010303090800d81e03002200042d03030110801485a0f400f00800d0850b84142000b004060329a41c002510350745605805071100c00c0028072076480d40c41ba2104480c802c00ca001492020a180c40900009001d035003141c1503403130f20344840100c1e42d03810204402000142200300420550f18100c0c080d110b2081d209804e6502003034020568030700c0a001c1c0541841148940c1c01c0c03010306004c203c13034000b510010750000b0b44030624004d20080103880300b0410707900740c6006e410100c030010201280f81b0050203090f8002d40a180c1da98240d4403c0d69040c06c0180d016400844902191441d102d0906944420741480c01c9039845490113004414140720407080708183c02481d0051900c0d03100c1c01d003108429419102000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 858788093 1250 858786843 858786847
    0x20f1512160c080702150405120c011d180903090909030a021b0d03030e010f060902090f2d0f0603090a03170108070501110f190b011a0f070521 63
    0x1440c65000030903000041c4540c140100d0740c0d41c00b500d07406040c1c0240e66000740504002450798007440301140c203480007004000c142c0f201c512038040341181c80c0c0d403102c50154040b510a02121100e80032000110034100c00203000c01150280000000c00c030f030400644106042d010800c4031305115180c240c0780710710640441e80116038441e9009402850841c0b000d114641400884c40007044c0e0346da070100351141c032a4040c03078081048041e5400342070040c2150186201c042c1d2801c880094400c2e40ca03000380148100494402d903110b200441032000704409001d298000d101c0703424044200d030b81c080703e08440c1c00802400481d06a0841e80114610341d0044d248030110340d000e41a90703400c00d94001000c045148151510215551600c003e860b901e4109020780e50510490040e249080070041000740e004a440b041141c007003001c0d41600d41710311210f01c403066580d160000004906c05a0b8084444e4800c0c5000ca03020703140030142c04d01c050720b58105041c01c4500d4040c0d01061491901c509601c14448921007060039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 858789343 1250 858788093 858788101
    0x7020409022706060a0f0503181905100b06121f0e042a1a07051203012c1306090203060109060503100506150705071d06040c0206090a020f1512 63
    0x541c110b00c0041c40f081c81010704001c65817040360b104c0d41c8092038840c0b508181d0f032a40c4811021451000070174070b400941d840740300c00c1c41c2d505403103c40e40b140c94680510b007600c54038401145c1c44c0301500e8401d80280c2d044401002a13008070300402d801c45034000c20744101d103585480d001d4201045810703181c3c0700b9040d0b000388405110034010000071800c0c0c00c0008101c04800c3c40d0603a18191030b1900c4511a1a8151044404118000c642c4200f100c0146e6484800c0d104000c21100500940b60803e020301c80c01c034021480e10700740ca581c0302203007407054040c0211520495501d00c9400c000c8542c2c865000c450705919188006c0043c1c8041000f240a00070a43e004518542850305143c03820019081c040c0c42141048144030060300c80e0040b24002607803141000d55600b4180c20540c0c5481c0241c1c3c07090000c1c011045407070a0901c13800c00c0f124001d8000300d40030f0248003a5890101d0b40d40c40c0a03908440756800120101c0700610300741301c1b00701e90f6840240c071903000c030030280401000e0350f08009042c0240380d849400b04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 858790593 1250 858789343 858789409
    0x30909050a1d060609010b0c0a06020d0c08011a030c0f0f0d0501050102100911090a0b0d030809100608030904051801180b01080a0302060c070501020910020a0606090615050702040902 80
    0x40c4101407542d40050600d03140050000e0520314040c13180544081c030028105a01e908180050041d203a080802590780d12a9602110000c120009401d0001070703807880082030301c80c85805903400c050410030f00241140c4500200d4817103540200e90054002001b0130000030b5100d4201c0140060341002400011258904000a810071103044502d0044901d04059140082c0c0345402034010343c0d0080c0ca500c100759444105060040c02d142821540c80b0034a140d550003090381c0402500d104980e0041521402005064403a00380c600500034075405410610035041181001e9008a902150000c0c03c90162404280c0343c4e400c540802000700128002c5201560511541e03003505401450715000810250005480003921241d0103001d0042d650b01c00511803044c8403094050380d00008006142c4006105403040280d41c0f202c00c0301c1e04940b02e07420700741d00003001500c0e0b11502049609030400100d400b203917520216911b0f400030500302e074065601c005e61005030322290800c0d080c805880c2000c0100103144c540e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 858791843 1250 858790593 858790631
    0x18030501050a050c09031b0d0609080304061b09380409060b09011b0f0b07091e061d0409050102031302011b24200d0f060819030909050a 60
    0x7602003138801040142102d450004100040d81090840d40b09860380e018000741249544610181c041406d2038030080c24060f03030030b00a40c025441440104902c0c80e1f40c2c1c0e071713111003507005490344004504034038000c011841d00c1050b0107000d10129404020320240380c01300d00c2c102e03d00f42004442d054001040503c0704403100d1141d040580040392400c1c2c200040740000910358410b010a5140703004a01c04840b0411201401000105620012202c0513180030f0300001d14050346031040c0303c100300320306220700082051101c1550036503078545e446107803c107840030321214102d003414090798006550b40c001c2d80114000f072002d5030281c00183c5090800380850300004001c20a083c10306001e895001c0540d03c0021045c513021104440110300c401e40c03482d00803c6042c01403030900d204005002c5d014075490201085170000300110203000700e0403c080e6007400d5404084603240c2c01400c0e2943d2041030000f1000d151720104200b031921a00c1c054042e55164443c440913140c0a403440500107407501c0c0100004109020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 858793093 1250 858791843 858791851
    0x30204060212030421120608030307090b0c060703020c0c030703050d022505130605040f06030309091418010603120e10031109010e0a08030a0e19081c18030501050a05 73
    0x30740c1d58254201505c0310000d0420201c5213901050303641c064002c0440c01949040081d4001c21001c11040e0f6607402219104c0d80100c41c4030001405802e00818400000b1064603503c0841c5030062100781d0b50307507405170001d41c4201c107a5140d41c411042000c1040e034040280c21301940c4140003501b41c882801401a24107451001040901c03001041d54000341c8400390380100031241c0441750000c401c0949005c91001700510313000f05403c0781c01c14500b690030711415040102220b210b60388a0201c190348007030500450340302541c11824048d10b03c0104110070801039402d0209121540005019030382c82d91200790080000e180940860000c5202048528181c1905901e0603d642400e00088150b03140503980d500c204110b403414001034004050040d1180101400901a80710840b82d8910b03080102400b0083c90100c0702e4030800d2142903214885585805a004039909a8000d1040912140141c000c5580c40c0c0d011100f0088450344540180341c11500c02ca00a500801c00080c90b420041d03081c01c2504d9000b8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 858794343 1250 858793093 858793123
    0xd0605030606090406090c09050f070e030f030702090c280f0305060d230708101823030d050406020a020c0109050109150509030303010602031b070e04021e0405070302040602 76
    0x208102c1c1c143c8034070003100d510550200001078820460b10b008480807240d50400c0480070720301020411030909040010703014801c0c03502e48400340480d0608045c0c1c1d400ba010b004621541091007580c0050402801840d005007005283c24203041032558015002c1e0b02e8038a2004245d00b8040c0320381e844a030001040043d07000e003031030309100360310703059012540c21901d0402c01810000e04060b0707815003032a1041e0444400c400300040e100c25666a0300850342e101e4910a131001c1c41894074449928000c0d0042d081e5245685c00f00031f0602c800f0949001120040c0d04010f1000f0302c1c00200510801007220340320b014800c503c29040142c941c1080c1400900d042c242e08030540c1401010507090156a80010900044a00810f00004031300c00c3c075442100d441c064128503d808d03120100c00414500c0e000b1000e841c1142640f0030103c00300d07014102c0180e43ea01184103c50014000c5000310300541070030349201c2c401d0b883c040c1544a004071910701060071a01c0807501c0b4000203502040030b0040d980c0c18080c1d405001224 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 858795593 1250 858794343 858794353
    0x40c06050c0309010e0f300f070b0901111f050a200d1508031b060106090902070c030210080f090c131a0604030b070306060306061b030909110d060503 66
    0x500c50a0b907a80301c3d00180d941442030308000042d5aa131024005000e8840140c84400c0301140410014540da00c0d03a0030701002069184880320080000041a03101b02c0321003001014114505401403000782d0115140341d04000b8600300c01c0032001700410aa200d0101e410318a4880010400200d5084800190151001074104000030b482ca488241620f90300f1801c1d5410b4556908540103074800500940c0f004610410102000103241003000c8090440d0200408c40c5914080700d5030019900c400382405100003082104e101802113803010f03806411214860038800796001c2c2c403600081c6070b035480344002800150700b50341088940950240c4207034100301e504005102d4a00c0840005d00c1c0741c1607003820201099030f01c1c0103000c40d8919085444001e8880900307101d03591900d9082024007003904484410120b401c180c80000c90a101e4820312045400f5941c0c0d10740640802a801000c50519038070584c02c01032604408225a400c4d4401c25260340244d0691580e58100040c00506480607640f00034030a03040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 858796843 1250 858795593 858795607
    0x120106090f06020c0907050c120414030102041508040623190e101a0d050a030810030b062404120506060303090d02120a060504030e01081b0f0a02011b0206040c0605 72
    0x1380070720442c4c0d007200d10580c2507840d260111554001c44002041510a4080143c1c0c0420264020310980b00d80308040004000800d080c9400d0748142d200300d0305030340120905200840e00c1180105d40251040e54040303000b00c568950b02401280790b0380700344040210801400096040e210700c0320040c0034806024001440358187d80344d110583c5220921340340c0c0e20b50740c6520443c010301c03010280d0550010248210110103060940d034440003d2011008070b0908008a0700d0761a00a01e450112507100441d410b2035550070707041c4140003102586003041c1d05103000b0795601507080c400181c8043c0284145004d4800c244e414514a85a0090200340c000d07001000510780355280c0c2510030700840d070141c607642002ca09a5490616003450200c01410745440e11040c481016409016251501c80c00da83d1800a600c85101621003144e802108110341c40c010032452080e0101600500081000341c000012400c0302c141c4603010616008011800581182c8104410800301c903107058050440e6242550074140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 858798093 1250 858796843 858796847
    0xe03030109020a1206121709061606090f05060a150806151f1e03021c1505030703210804080a030b040609020d0c11010e150714120106090f06 62
    0x8418012440034076000503c580301240614005030380030702000ca04104c507039911a242002d130440310b14111106641c0601056201e605e1000f41c58964000034070052500c0b01c0d80c05540103e250406c0b00304c89003500c503400d00000c1403404083d00ba55600401c05460203140c00148502102d12800d582d13003040700200702c280100382c4002001c5620103000f5148541c01c01001c2c0c0040c1040412170031003c038130342054800300c2010360310040070031800610300c10540e101c1c40f4884082d0b0981c003414080b072140d00078850801c10b0360481c80d005041c04608400d155650662190f0129090200381d82095444202e848a00c849030f03a0f00d8514049148120310349200282419641d60300d45100d002800003c15481d440800f0310b9548070781c0071000521018108668a41d084141c01c0702402480050801144140c1c50110302d0110601440000c000d281300580400d60008001c003088400c040c0200307040082150b80d80d00034139981c400508802c6418901c1e800b03a985043d1004040896541012507010000d1904100700d075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 858799343 1250 858798093 858798097
    0xa0e010e04020a1a0705010606050c0a2604030b060a080601061e14271909050a02040801020f220f06031d0d050406081305030901120e01050114130e03 66
    0x103894100c60462030701c0300c1c00014a03a105540080303030000b10b02e100b101c0d044a01c1c0c0d001045182d208000034802039507109025941c50090515501c0280c00c03003191100080da0b800080941018900034160314a8822012200242c100c0d40040301e14003030607014424585070040b441c2005001c514002c280c550305001d401800d9981230600d410880408813a000c02550240c920a035255a001c80481e032110b4030140c045824888403000100d0b00c8000410301d040d00e0501c2000481e8556000004126040c5001500402044000c2c05007038440e6080c040404c042c8001c2c0020b01c04800c01001d140c0d1580e800c649021810f241035480320701c816401d20001c1080c200c0c0c191680c01218420b04001036941002e03e58400d030040101c904030380c2c6000d6100380c2601c142d0420042c0041c0c0c2c20650f1041025541e074699108420711907000030303180e0b80c401d01c41c901642d03210b130300880d0701c0408000c0f01180f000c031540109401c0d0399084e003010a00032580e145c6000b13142000040955410240203062001c1650760782100d4480c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 858800593 1250 858799343 858799349
    0x2030d08070905180402120f2806020d060828020d03020109020d0c0801060803070503070b0c1b060a0b06030f180703020d080d0c050c0714040603200f0a0e01 69
    0x2128500c00099005406198004010040500010a050200d070f403007071210401120201e214001008031001c01150016400c290341c140710008014110b404040c801e55001b545803040800c40d0b91042c00000142c03e40064111540d080402194507424006228140540f5000748803580e00001c07007005207a4082d41c04041e0203a01564501c04a40450600324050900e595020f508840c2035182d07038003000b503009003040407504181c000300155912071502c243c80303102d542c0c00601140d109004150109403151080c0da080003404c1c80c881d02c0e01c031190204070000d0000c0c018016043d00000204980d42e0040d00806500050880ea41480d40c0761204402200310300192111032500c003440e15181041d04100407150295400a082000d004001d18045911381c1c480964202c28604141d002165140100191050048080094000c1a0810f1810070809120b00030240e8000e4880d08000003082d15068a009091b4040700c00040402c04c0b1070512035054400001030780264010401040444c5950700c0362415 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 858801843 1250 858800593 858800597
    0x30c0c050a0f1103010218101716020c280501030c4a030d08040807060e0c1f030b150d1802061314100f0f140a1d060702030d 55
    0x1a50070054032200030f50403440d030558800144a04407142c0c500031001c540a080714a10304c03046100c8012141c100c010035050455400c2c5d140071a4a031a40b840180c8000b556502c1180c81402001c0001041e030020201e4075030480000002c07800c5030070006131021000c0d007001e0034288500d080c10200101234096140d01c2411010700f581d8060000708101038003040e40764511007503100e005854901001e4522054226901c00c0c4101c005d80c800240c0101c0c5001c0c40340b0780082c9503a0900200b5101c800141080b485010f1160103154400d07011035844055021403410205201804407504950180c00c0312205034072144a2a00c01c114400191f10781000c540040b200c802c0040342502c403041c4030380c1000700b20300350095000001150840d03000b00007805100c111880d00e55101d08043c0700c0b07810721050003540c5002c04001070b0011040310b042409040101103000543c80d0000411420003036060054100f080300c500001ca1501c01c0c091a60031b03880340c85110350000c580140c90704205500095075050001e02d0941 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 858803093 1250 858801843 858801863
    0x614190e040905240a06030209040f030306121a10051e0105090d140607031116020f10080603120414100504170a0212011a06130f15030c0c050a 63
    0x2486450701e07003000c400c495000c0c0031501c4143c0c0e80154041c0b41446188204280c0c8a01c600082900150340100710849070003900000c80303910b0301c1d1a00030b803942b0310640603024103450f0100010840000c440c00c074502401141c490003016102e00205000d01c4010701030441394000700c139080c0003544e10200c1c45e0300300840b60020300080c0c5107041c00688076806044c00c210790101c500e41c1c110060129085503c6401c240c94401d9450340c0c0d881903001d60880e20001c10b0300301c102c13109101031751500c07030b050141c003029038001400106800c141c00b0008640c0700e0315003103140c0011100c2c0b0502c481401e0030408480c84d00421520a8240350070030f481145004002030510b40f02e40c00c078403110040e413401a81120b010385140d1004107a007403110201c09a0300d0362024000ca005078081c407010300d2031403018858070302a0042030416881d51013000081013074035000390000d600350140c20700c0002401c04c40c562030308009042c04070860703542560125000d022901501e811005101131b0803115800100045000924107601c650110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 858804343 1250 858803093 858803117
    0x20405071706061809041a010501051e0a0e0618030c0105070f06020d0902100f08480c0f161503020708070b01080102031b0906040303081e040804061419 67
    0x710f1201d141944c2140c0284a030b03014002031001c011340004101c0c2002c01c2003642c0c0d981e11401115a4441c2d20801e801c50034440304046500c1d54400024400c40d800c030314009000291010020f045031348820700100700f00101c0e04c0d030710056040611840030070410900380b16041c070099840b4561290000c010082000e0780c00a090717a0311003426409080c600d6000351550680d0406814090500c4080c4609040428049400140660a035020100c1d42085102c200e220900322659080c0200c4d00c0083c8040d45161400b400c1910001400c2c0079011650360b01005207910102c034414031b0304103c520f81400a110b00202414000e0030400c00f1488071140041c507005940c0d411504059a0074010540002c01d16050a000042c508505401a6010780480c4848100d1140503424044151042c0350340150028000d000800119010390900755006075484516007048030920085420641d08aa01f01c61072000441e060081035846110300c2d640c0702c001181d181c904400c44e00203003482c00c0140240c0302003002100c446 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 858805593 1250 858804343 858804367
    0xc09132003130f030f0305060a030327031e0c1508130c090615080916090b01140f040e0c0306030a0b04050f0615010f030b1e12061302040507170606 65
    0x52021141c00000103c412910b520300203082d50740c09044640001e040c100400c91760f1078404080c0c8200c1740d16850340d107403004907460720051203481c000d01e01e1070070340c0d41243c008081140f00d600700280f00032001d00215100110715010b900780a40c0e400a9001c0748800d00100c5a03190040040b0350071003146559403111400920305406101010381004070000c6c10048001401c40d00c030001110005010740f24180e051b52500e880c180d58851903411074041d078041140401c6001055445040c0c9240d042c98050b6202c0b1620f00c2e560b4503507002c400724400074a40040c0401400d03811090890300842c8001c1d102d491424081c002a80e2000301102c0505400206001f00702000030802030011500c011005031541c0f4074184100f404004a04813200b404120b5a070041d60704503103e4480c0841c0918001c1c0014403201001c6c0903400859244c1030440d030040900c1100d01001282003010912070b07a0054181d4540d08441d00c14082500c002801c02410703c40100b48080040405a4aaa80c4a94240c400350703200d0940b1044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 858806843 1250 858805593 858805621
    0xb01120c12050c0109080c0d063314090f01030303020f0d05070905031009200a1e1a03040519110406030b0406050f0c0d0207020103020906030c09132003 67
    0x4600440c030407114207a000c101d804140c007100c1d450b090b21260013a9940e44000f075200d40c22054000d5004014902210021300154410030141450781d00a410700460102600074200f6903210740c0780401c1c41e519040102820704002c00518441c10b903241300e03d0341460030000c00c0400044c0001024150085401d00d000c101107c191006036031500414070031804c00b8180035020b0b10a60007403034040c0c06002011169050a40504461264031500b100c1c00078445803c800c5d1256881e20441d0f84c4482040000500d841000002d0384040460080f581d031100d107844800000d0151003c001100d60000340200008500040b501c0010201045000001c00d00b151402d641e00030074260f003c41d84a450641c1c080207001c00c00d02454440e80c42a6810403142d2075075090b00f03641200c110781040300c2250821000894070000d03005888032520604026082044410000b5001e80044503120110400400c2054240c500308000141040c200c810170000860030740a20f0030030214103841000c3c140b50000c0414040411506 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 858808093 1250 858806843 858806849
    0x408190f150b03010605030c060a030e0a05010606120e011104060309020f04020a02030a0e1f11010207050102042711040b090d0f0602070b0a1a010c080d05010b041a03040b01120c 78
    0x10840c4605401681524002c1c41040c0100d8000d41c6480c0d804504c03820009241c2e92000402007501d4200000d0003070031400792209003aa94030303600071300704500001402406000040c002e15100d00440d01061080d000440c0c0c05148040096814080852590144031044506407945458041041025070002c103040c000c41d0801290890302c00a99020704a5011024209882c4c90b80e44002c40c0f130889504201e04030b42192141e40c0070010a10400080500521035120030803403100015041489a844840c01c90b006030b445845c100007052080400c18803001c09000c10484008010040070204c0341004401e4041c80c01038203d03070007001450a94564682d111401c10541c0007030f5000720b405003032074090041c1d000b06104035000c1121002160461249000f113180e220703e44840180050201030045400416001c019204440100050905207010b80a90740c0078201d0103101c159628070b04000e905c8000403800c090f8102050500c10302000519410290381120240c90703552040b100c0e0b03424000f40d03e1005074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 858809343 1250 858808093 858808103
    0x30f07030b280f08060c0c0f070f030c080a111210152103050a050d230106020d02120d0b01050405090f06040614130507031b05071103030408190f 64
    0x205440c142200750030900c41041000b00d40b04440365294140c4036080d003203010300e40701a08081d00260300840d0340b20282112032828822a0304034002001040e0034901280c214118000d1b4480e030500c1488000559040102000310003000f12039041e880c1d2040850058000310310400e890001078600c41420004060018100002001002c41a0411020f00c181c10700c03911710000c100510030140b100d40040c051000c41e406440d09440c20310780e40c50440ea190b00c000c20300d001c02c50b65070035100140348002c600035003a00c80c0d03030305902c1907035040481c06850441204128002c5500200103035aa00d1200c1096032002c04c000720001c0380e06403100006030b8642c05140c000b00e130854030980400c040384107207091060140303800761707801c012281d00da00312841480d100e5a4500d4103c150341802c8401003416600c4580d1100c041d02c3c002034415011303460081207030003801302000055004510340381407056901c1842030990084000f0f524152815451584076100300c0100030500c2c060121440500000020666072a6808 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 858810593 1250 858809343 858809359
    0x1e0f08100807180b06090109060e0604030c090902130b013002030c03072a0807152d0c0c02010c1b32091503010e0a0302010e060c0f030f07030b 63
    0x10319148001d40e81180c81240a03181810190a001d043c0041106d00140040e1b41e45000d036401c1860039101842e4008070190403c10030000000410240700008000c0c2c5006040440d4100c0d60740108444100200c8110106070714066041d00b4680c0c204079030a00c0c1008040c02041e580614101c0d00b0f0080921400708030700e444c0004208007104564000a501c0361070320b03484051900d0605011480c0e0345c42d4540c0b201a100704807045000100d05044040d00d1401c5c4510002c502040342c0f41135480c2920301c1202940914180444400714551400d40e009806110b407000801c000e038000e610003230640c64030001c00b07070501c0490146141400721910310440d10001641000c0085035031400008030800c1100d00c150000ca40da04c400c07000c1181000314101c450000203200240d1900c0e06000e2100c00d0040d0040507506641c3d55006551120007444010300d0a8026000020302201100b0b90a050010040c0a550340c22000c000c02d0400714101401ea03030f004003402011104550320550190000c000c0154000c2d80728005c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 858811843 1250 858810593 858810599
    0xf0415080f0f0d090605070602070515180c09070f090f0311011e120b0117130203120a0c0b06042c0f0c0d140102070c080c011e0f08100807 61
    0x2000491203940c0c4059801c41c0d041c40042c42d0250f40314401070140c2e200041904508026091240c006001c0d054003e440043c50003038140e448a250240c081030400c0802d07011010400304100401d00c00d88e50441c1d2501030103005e00c11000181c20f904004180c9030501010b02c42035081c040c45002050040c2c0a44002c0c4409180c490504150001829039031310300142d4015010326104c0504518045c01701d905851355644d4101c8802240c000d051411402410001d806050b46240c0541d20701e001c3c0220300d070705580d0344100c1080c0141030919012040008a1403000c000ba1100aa4083e00010113503800000c1140355885d03140029000d003031030880310055181110450f007413620028415400000c1c3e82e4085501009041e500301d41c481494040c0c581e03001f88c121882d40b0109020100c02d105140740480010b1910354990396a02842d1816082104c081e84490f010000550708250400704600c1c424803c4900a0b0392004010420340e03840a0240800c20745070045160806503501000c06403540f20b080c1e40d5100c0d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 858812949 1106 858811843 858811859
    0x150a02070f33061802042601020405100509130b0d031d030102160308100b0f0702010309080a02030c061305250302180a0b0f0604050f0415 61
    0x680c0c80392451594103a00c0082440c141c14100000b003c90404880d00100c14200d4030110034184108000c2c40780c410b10700c69408010b019000312511000010445502a00841c4d01854004c0c0c5107014540304250840080c2c01204030941d4019007202c00140c8003020b50f035001403003030381050071940700202083c0704501d0403034034101d44603214002880307001c040b900320b03488182c820581400805440d4201079100b041150042014800f08a200b814528030f00141d103c0c2c0403a0482200c0b00140620441e406a0000c558403504403a500780c5035914a00c0c06912a84002d480440c280204800512828601000c060302107801800610002e10080c6201c4074524901694803142c1c0304100000006030351380103c200780e500da407000340d24203424001081000d44030a01519803140c4000e110540650b220001074070b0131508211010701001c10444007003030041860f50300001e208460b507200461a48 = true := by decide +kernel

theorem cover : BRFrame.Cov 858633093 858812949 := by
  have h0 := BRFrame.cov_init 858633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 858633093 ≤ n) (h2 : n < 858812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
