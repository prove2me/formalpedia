-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4106
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:35:46.485781+00:00
-- url     : https://prove2.me/submissions/d1b979a9-4b17-4e32-b255-914b0972deda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 738309352 ≤ n < 738489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 738310602 1250 738309352 738309367
    0x8031903050402090103151407081504061805071e0207030b0603060f040803070207030510020c120a020a0b0a1805060615070804030204091712043c030201020904020403110411 77
    0x144083d641c1903070703003000800c00c81411f204c2d040350040030070404032400040c02c041000820765010444501c1001c0210005110b00d60712428041500c0c014060300800c00c41911078030000c0b10303459005541c0001e0b035141c201e0006e0003480d50718003164501b0585500603002031340284180a403607240543c0055003500208070b5883d00c03010075840064082d1004026440000100b00c40074801c011901c05107801070103582ca8408a111644025803040480c0b00d0180a480485d0314442071b10f00c1507075801c0e070564010b4011800d450744c07150a40d072030007844d440d81540e0320300c820300380d07200814268a0b07001d10130b000070400390610400300002408d4000c400c0314038800401c4007000040503203041c0c404481c0c0c143d90102c0c1040051401c0c02c00560181d8000a10384004a81032180780ca001c0111030041c1c1c01201c20039085c4c00f02035801d41e01c49141e240f100210b840a0f48070801c030101c082c03110140b11381c064400141020003101c0040c050364410303401a10041c101841110301443c1c28410041c00520003480f10786030052 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 738311852 1250 738310602 738310609
    0x3090a0f060221040906180609061a25030210050901060609061206030b0c190206060a27020301080c1302040f1a09040c05070b090a0b06060703170108031903050402 72
    0x94443d05080300100c1c00c8080902040c03501964080d00c1c6480e0140406601e6906001c108002070030b407016418100200020709403490f100d080c080c1d54503902224410b5641d105c8502450744001000b104072400c40801c014580c01010000c40b20900c00d6005d00b190010316a51441621400751894401c1d0b407600f2010410260004190000c0f20111f00f0492441201c8101c00c0004240c1d960000d443c01030600704001142c2e082c0347c02000d1078848400c92014030410640f08903550f0b2022a00c494221103190f0003070041500802440c8a603104044060908564488903201660409c1e03101855030350040c0a82c080d40d2034580b40c002e40102542d0b0045007890714048a40e0040d0600d4442c5500c07424104580c8800b401d10304080780c03036008028105024030544114004e01c25480309800f503403139014040215008000100b48075884c203811043c0c10303c154a440080003003561250b04100d052080d2403a141c43c00c4411518070038024001e039405552a8691010703205980460560702c0c1007014600b07803c000040c0d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 738313102 1250 738311852 738311863
    0xc040b010909110d020703050c1504020f0d230105070e09040b0f0603190305040501030c05360904050a021c0302062d0a06170d05040b09041d03090a0f0602 68
    0x1a107918001c02e0407030307660440c5909886400044c40e07089000081c21418160090000d00907643c90000322040c4420f0440c050710006402d0341d0080d4402081804d2806c03d00c2d2040700001c0c428001c000d006400212001d47c55401890681e68030140c2e51140308110b075064100c1081d080c002d009030784417001c600d095501c959806c98010007104200c10000b000c0b030b9183e24200841c0c04512203251840e4603000c42810050155007051043c1800281042e000b803064502c901c2c01d03242c40000071a04403465800d145070f02c442d0090302102e5062000c00e03020365141540d44020074940174900070f0015081149590042c4a911809803002452500a588213080001d50002e0000d5010310100303800724480d14106c182050a07041226480c1c5d80100940c248942441d50358841350444a80c00d4111480d00304010f070003925003409012400202c0c0d0b050208225100c070b1400104040c3c0030092000400642c60b10400254a41141e416146540040f4a1080d5400c04100100141c19418186101607261080c001d560302c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 738314352 1250 738313102 738313109
    0x1140a05100b040305060114040c02030a111002040e160813060b1507051e0705030a02010302070c030c03080403030311120c0901170721152105060a0902030c040b0109 73
    0x116038803800107594100954800c4054162048199929952414250b0343c82e102802020b110046145114a40b4a054800c607898116150040c4d801d01c1400c0105850708503204410b1040c50280800c0b2021001c0c480c4002c0c4043c2964a840340410b081c4059205054100c90010000b444040ca040c1302c1080714402c540d4443d0b503030010021a0590460001c10f644070b405504422002c180815980e00b008000b1500c95500c002c0d500c01c2504c100404400c0e0340d983e6001c1e06c101030301604005c17110805035103c1d80092070010300901504c1d004545d2607580d500c03060440d038400c0c1c8400801003014000c05030325000302d4219800c6c41c98002e0411a12414000c442c0c00c1c090681c1031505000a1110020703405a000c0300010301d442c4102c40e0380303894826805000001006001482c800e000070302021140058440c28040d500c1d2514003c8000341004800000141ca00708040c00c108200c480010010b2420080d0a201d0394590a01140441d4584107152a2884690300c407803049081c1041c8025a9a001200001300e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 738315602 1250 738314352 738314371
    0xc0f090c090803071a0907030b0a14060a030c060f0203040503030406030204030b0705030105060909040203011803030c02070b130e063f1f1805150403141201120822050f030114 77
    0x207a0301ca1058541c40c0c101582d00027010300e1084810451190855803148000d40d110352480c0f07d5503a200c400704400001c2c1400010310132846900b080c002079100d90544218911140100c4e8507140d140c3d00024510703001540700070000790700042d090081024160220b03403c0030306401d02c02d0665040c00c0c0091224010b19030354500440420b4001029507509410140d16014113104034000c95105007402400f51403801e440c1c1c030151007503000000303260000d401203d5007150150501d0285606101e808041440058140b0794448846188000c400ba9510300043c28035802d031426114114180400004034034075601d10030959001322001a0032548043c03684035404142c08070005a040713440f4000c2c40040b400b100c0141c071901c2284540065902110041070081d40641c840d140342d40c21001141282c1c0c42500390403048070104000420000d40305180b26070b15988184070340c5040c12038251810742c2000b6410000c01c105404100d04012604080c03410213903a03131080d402801003c1100c0c40301c207031a00010341080070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 738316852 1250 738315602 738315653
    0x3101406160210120f0c02060601020a051b030f07090b033f0f120a0e01091e300e1903030c0f0611190f08010902070c0f090c09080307 59
    0x2019206130003410003119541001c1058405110740c20b00200048081040544982804501d25600008208007900d03880001080c441e041c64070520800009450216003512988c82c54402c150420710866014059800700041d016003400101850410000503120001051002101c114045503c1c8603103050a24100c400082c8412141d03580a403040a68212240701c1c0866103118210794042c0301130060f10541c20034032003041c01101c01400c1794507800009062000035074100c3c10011160907114a030a010b41b803c1010001303000035003455441d042001c0101e49034981e20408005412504814040005542d00300d15a11601c15020100f603190001501340300d01d4250071070400200c86518003119511603014021221004458801c0390092404050388003210320001d40314510075042c452014030555618131807a4a4200446c000b03600c81c4d54103a8901d080b0031000f20702c2e4018040d410740200bc490340001030503101040001d020100942140d011030f0000c204041c042071b80b454000e0340a10000007a000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 738318102 1250 738316852 738316879
    0xd090803150604240e19030203060109110a0f030213030f03120501030302030406110c03010f020406080f10180b030604030207060f0503010b030103111c0812010e0f0c1b03031014061602 81
    0x350412480529260721030346c003914901c0d011400b0070b0100c044074403e030102c842070790b20b9242e0b82e410340300481003018540760280445540740748038141040d0b1400c600d0500503d40100c130324075045610f0a030b80064582c4440e0b00303282070401d6031042d1301380c0d50010403002c00c07c1154103544d4029181d01c1280305500800c50300004140e01200280b05806c10640e006008100050b08044444041e4005103d0200800c04000001d0240c20b4030361070107885401c014440700390260500c241d2100c1405290125010b8035500d600301c1d000c43d1000c109103030046000e43c004000641c500000144520b00e5402c1c80300c2081020300040000f02c03103170300984c4d064035800112015091100310100705164bc142c2241e4015030039030304202c400d20a0000c02003082d12030704c0454410b584e807600752081c248501981c0803000980210300182d420b00c01007000c1e096411a50304000c058070340000c1254915001a030794031003000752081c1b0800a0109140712000c3c410000e64403941490240b8400030016581c008010340102d210a0880 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 738319352 1250 738318102 738318107
    0x2010e060909040506011721030a09052e06050315060301150f03150b0d14010b03030f0d05090a020333070e0f0102010b13110d09080315060424 63
    0x4960071100540310503214a098140340713039251020710800340d04030a4000c40b00d15242000c6460140080941c0000c00e40b41c01d152051704450b0b000400d081d0109540d000548000390f0188000840307021142d0801035403012000e8054036403140c40410101203484e100003000a5100840c200c1e060103000c02110700246d5405010038050700341401440c20a0021460100e452500003c8c4001568060407503c01215518084841250b1040303040d80d504c4240c64408000040b607620030f0460084d030640002c641e0b079000c0380100c1d103150003800d04038a40b040301048580c0400762511a130350303101365101d004003504021900425240d440c40f081d443c914040142c81303510200301a42d81c0780341d181c1150542d42910f00e030079080184a11203041645110740d45160240503150301c14040c940119900500c04500040080d0035100140010804034aa660013401510100d07842c03840740113156070068410a942e4541270381255044803400403002d106070001c0c00103015800400d00d02c1e550031f280c1300395002a0a41240e005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 738320602 1250 738319352 738319357
    0xa0807081603180603230402030f120414060306060717040509040308061f1b0f0209070503191406012f010c0905060c0c01030209011214040314070201080402010e06 72
    0x69200c10007a21a00010194000e03645081001c0e0358602c000d01540b107181c11000e0392002d50b40c092403e4101d007200745c2114264007009400070b10043c1240c50348000128011b0030280c24031441e880d1020081b508010482c64610380c104040f00888400745180343c480d00240d514029400040c01c40c114881100c003c0c4103221046030080c0100a003905001d1034245401412601d080b921580608a03081040c00381d0a00c0902c02144001542c66541280c2e04620108203075040c03146090f6421141c00d0304c02ca015845070407046001c0d840c1ca9941966905d41050300710448480c0300800480c02d868000341c100d100d18150710241e04890246030560982d81c14104a140c030003980c83d014002400355003140480903105512040a038151511200549540c541c10040c0501942a41c0705440e0080c1071901c403550f10940c003e00b5410414141211110000f0075160704031000440030003a54482103087c0001c3c0364110320310041c0e140284140b035141240640c0000c1107800b001d04002e050081c89071035008a0740c0d80405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 738321852 1250 738320602 738320617
    0x303120709090921020d090b030702070e180c0306090604080706110d05061e0f060a03061815120812041514040b0f0c0712050403021f030506120a080708 67
    0x1061000305100d06180b04c562440800b03000c000460781e841800c449001040c00048002d16032107004105140450a92a0307600003040e0408602230383c44d001c5104880a0400ca0103540b030045840e0300c2c6030b824003a451070050150f20040c442c1c0e00030070400c10205000501c0503070165100302019100d080030301c1c0c04409001d103da0380780c10101c8041182e001680f41a403056124a40489281d060302c0d04014021002120443d50701d50000796100c807803031031401d03d030b001011021740b01e14000404d645d66100c0703040c1000040b4003503045291503a07152865850050783c0307040540510890000c0716100350703850700729a21030300301406100001e0b40005024071560281c1c0b0100303d41075800c01d100400d22115440710642e41202d08484104012020a4103140d0f0303200c00502c01c042ca4035030549001c110b511580c900308401c0b000907040101c108800b100603140c0080c4906c41c002c05480034156007201460250544200400440c082c211422007001e08a20011b201000242c0026074160784030790504210556114891 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 738323102 1250 738321852 738321869
    0x11a0d0c14030319030b01031b0f08150901031b0603110405012d030b18220c0b120109050610050d0e07050d050f0d14180117040303051b090303120709 66
    0x2c075220321541c5c254105500f00701090742c0821080b003440141d808194002c100c2100058440f07011140c505001da040550855203c010030303400700d03141d0b00006920b0602600101c4041c2d8540c40b0441d10100343c130040401400705400c0501041c0f58446407904140a6446018100800c098034400c08034020301d03a08060200700400300035031414010000c0e001d09a4034107064095209040e4100482d0b0848003101d00078400c070200c1035a010300f400030302105080e410f01d0030360710300c004071a000600c19200c10050503084e03165400740e44c0399032528031000c0032076400820246c09905001c0403050480d90040c1141e980c100441400500c04000c0d0600754901a5641c0219030003000b80c0c0b42402c1070240005a03100d808165004850054012490896480e040810071000031081030000d150520300700c800706209000c061502444c00c40ca80041780101c130f04281c0381034002c00c0d5a0340500c012924480c401003208821081c001d0310340f103819404241d0360300c02c0700490100110988040b502062150391090020300d5000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 738324352 1250 738323102 738323137
    0x2a0209073002041a030c0409020702030f03070f0b15030d0810090207060b0405281e02070b040c060c0c090e0a1203050a052d0405030c0f011a0d0c140303 67
    0x58150700250b20600401d01c2d891802407031a07142450f02c0782124414044180d09609042c54a0032603400381d001054204d9160240f400b0707079040300d41c0c1000642980d0740208980303680c0d0b8402d42498040c2440182c007550303624825a428041c0d0361000100c0103c9240a4542982140e1321111440d00d868101e800c42060300e0700000d012030178808175030050b05841c10119410401c2d0740b80c2012009000c81c00895103a0001a007a00f00101c0d400280c1c8541d080d02112070b03580f50301070b4102140c901240e10403181100c1d001a003c013071005102c0d0881222000c0c001d107080c00c1d00c81203500d80b41e12a2840003440381422190b01c1e00100301b602c5500340900c240c031a603c9180e0941c1c40301c85000290240000700c6201001174a031500241e00e601e003240c10310100400c01ea07002c88101c00408100c901d9054002e05c04d403601d101c20400c400800004004d089519064440001904004480c84601820b41d1f0201d0354456200c9450300000702c0c440703000f07501c201c3e04640d64030081130125102180c258022a41c20f8071958490 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 738325602 1250 738324352 738324437
    0x4060e01060e1e090a0f060b0a090f0b01020705010e0603090705120304060e011d04151a0a110109020105030610020f2a011106060409020402070605072a020907 70
    0x9000e08140260700b9000c2c4128494516440005a160f044440f100c1a5100e0140400403c01c12020102d8281c040d200100310300c03030708202103a611070103275000381c0701e00380d41c0c540345500c504161080010041092002c3c0c111680b4190009101c400c94021640c03240c0b02c00004200500003c0040304d0050402501c0d5070b21000b00b0842d1541c40e90401e109000218070343d000942c8007988100d200c18504c51028242108003022401403000a0030030040c3c286000e86260300110703c2c0e404a1180ca0600045410940d075207006519009224840500441e80d1903070400c44104010f030303044410381e54401002d443d0350f00310100c03840c2c1c100d2034a0101100310031280035460410071f001448110340c00c1c140d403004070140940d04040c40110f44031200c09140700d2142d00b160000c40e00300d140941112030071301d00042015042084a8454204030740782611808046146442c0c00000e840d140c603441207040c40c00704124480d260950b00807030368480b0f006095134108100403030300c0024030035071900d05410062140b4900403030865 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 738326852 1250 738325602 738325619
    0x509011b0c090c11070e011a22061202030f13081c0911100c08090d080c0a031b0f080d0212040f0b010b0f0d020315130506090f070806010804060e0106 66
    0x40c1e41e81e070400015840c4a00844c05000040d05030b00b1207507000301810050b86003006080c45420a0101f40c9040c00e020003500030f001c000910100d0b0000c0c40442c031070511600d40741000e00b04070f0701101900c00c118018030421200c41c0244486951064201c04015404586460401414820202145024642101c801c000e50b00b00742c2c043c9108a110364074030a2080081e4040107841c0b50700181c60000a81e00c902c4040008082401074171940030003400d141d024130320903030790075107590000d80c03803000da9a0001000005156114410300f200d52501d9206041c0342e95903843ea03440c038cc5819100680041000101030090403c02d40c100d40c00351044546618150034a4500000d00d00d0f0f5101c0107a41d24048100041440909107003100d01306005156410f1402c0e07078004c0218081d4200800c44190131200c0c00c14200c480d2a010840803041c0100c0e48001058502002080300c4140041c000c1200f000c092070030024039980000726a50854030908103990599140d107081005840680c00460480d402d1150000d046038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 738328102 1250 738326852 738326861
    0x30a0911030a0c1505030f130201112407030c020304030f020d0b0a0506040f33030609150608030a0c021e03010c110606030c0d0201111c050403020f030d0509011b0c09 73
    0x813070300304480c00c40c080c042000322400d000a82d8000071582c10000400d4440440c0e803544503807240b040c10304038200185051540d09014500f200000d0140c1100281118aa501c40d0040c0d40114242001c0090052a40c4000d40d0390065010041c00c0f50449202042550b4985a85400f01c690040c102411440c080b070011703000d044140c500b00c0c0100e04041803ca0340040d0b9004045040d14494220fa401d00082c0940c072007104d040f02150140000480800300214206004014045008e00790f0001043e04100c0004112206644041c510f03402c140000544190b0012034030a005404545285504c42e074402d40e0208452038020245d413542c0391840403042c1d9074100100140308846001650101e03540c090906032242c910080741984503003d42e0040c00150f016010000020021404844240000d50b01003940500a40440808544c020408008500e00384100c51010312003a405040c50303003182000500207001342e41156040c81800c405002e0f0610304031032484041e46d040b1020b0561285d9450b02900100b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 738329352 1250 738328102 738328109
    0x1030308040512030a2301060e060703200604020a0f08121b07061d15040b0a05071b05090115140306040f060906030611030115031104080d0818070b030a0911030a0c 72
    0xc500d2501c0d0352031030406c041ca0304965150301c42c51204d05004081210f10784c030a080031420b01038000c00742007800070100000114011810000c2045040600400540801c6a48042481684d07040240004140440d004400d80c214075402034881c100c42070741e00080c1c0606e916141e190f05c100340f0005041a403150710002104021201003258807400c605201520040302a100311200c4100010031205584400a00d011040ca15140303042200c1d50743c1c1d00b1a135191074504406011b41401c001c1c0117038a00f021340716004011488494122503d80d1601820241001c0710010450034040001221600e17903800c114203444901c1410003c540e01c400c4071600400a600081d25030f10b180c0000081c98124000c2203a060b50100d00303e41d04452941042100680621a41078000f2941400b00180058080290100140352501e80460b0b600d410000129082c1e41903c405030b50750b01c6800c041001024000441c2d820400b00e01d004500c80c1220704120030003440420010350184603c5400c1d006108603ea940402c1c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 738330602 1250 738329352 738329381
    0x41103030a0206040c0902090d1101020705060c01020304020306071b02040b0303090a080106180603032c060d0902030c0604140f030f031b0d020c0a170a0503030c1201050d030801030308040512030a 86
    0x4907030b01c6d014010101d0203041c0100790052119003482c408a5001c080c0c05000c29414812a02c429441c0d401054903a0842c95180005a4001c07080c0011481c0500034581d2240051030140028405000c0700682c0c2c00507510040c1c02256035205e80c407200e440a0084030000c3c1c2c0050310220030f46030789070015030003400d00d885495600b9101e20340038100d030462405828112a050754590000581e081080340420322505081c000101c000b003200c43c5e0a0302d402d03018040c007030101800000c03017240c140141402c041844000724419413041000380401e480580d4120b24038001980d102c0c01e042d80e46404a07142140b50942e10700c8500c800f081c074000296071200300b0307200c2903002c5081d1071069200e640d0a0703a60b010894903d5134400c07110174060000d2128183e60000d800021001c982e409c0307040d61205402e51740191501c0502c1c920008541000c1000300c0c20300da0040c58152070f4500c40361400d490080c00008103000003010021a10301080074040108144a200c02040c030400c1e03a2420100003c00050170780c61051000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 738331852 1250 738330602 738330623
    0x30408010e03090a1809150e0105060d080a030c05071e051006180b03011b1d120a0206031305010c0c0b0108030327150a050121030c03030203041103030a020604 70
    0x12007900200c02d4550002d409409003560505040e011808508645c8001c4802965030000c80080b0b900d8440c1003080400204001920050a40c645c0e42503460080001340100d0311046000300144a4030100e6010b0440c52800103141802080c01711018451001702512444d505070340d6109201441c41001d9825105000f190390704c00400e0306c68416103c1134454200c0a144004401c143c040f06500841810381004000240000c03216004000d8040304038092400251b070ba07082c0120002601c1c542c1d403118030f01101c0d0030720218041c0c611242e9419428400900859012011540034107006000c0c00c09164084024071140e8080c11004005a50501040e900b10426200001d01c2ca0004001c9900442003101280000e0121401110400c203000c0e86000380b500c039218030007940b1090300403080e000e8105414040340301d52604108581060003a61511940e40c0203407502400a508203801c0d0031139644c941005602e1b0b59a60501031804c0400303401c116014040000d0079121940c3c003091140c031443c4205280d01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 738333102 1250 738331852 738331871
    0x9051233040b101d010e060109150806030601060212070807060603050a060b0301050f060f100909180210090510080907050a03030206040c0e011404020c01150b040f1d011404060801020c03040801 85
    0x1103a06584148140c00c4d1055401400219060030a041c2c0c440018107100100b00e81d94a00076240c4c200340b540300c02c0080c411505003ca189810700c40e00b40107002c2403005025000342d0080d490b2280c0300d01103004254a000003400010400d554000000640d042000d95105400710308102000e0500280d4040c0301e035180c140001c240802c0c0c2003110740079000240010720341803241800d002a240e41f200b040303004d02440c1c00000501c482c041c001c20b600c254030b0b0078204a4075a41d62041c0304030504005011030901407145400e10468a400c1400310203290380e49009801c649078201100d0030312216400140c0c214608540c080141500005d403a0300440c03054010f031a01c569104070900c0d03503407000e024401e030010100c02000c01c4c0b403800c0d40107003503903181c03410000a08024030308142c2400c60040e40880003c1e403011070208810340d04c1202050041050100b0300c0d0682000c0c40726441c1c2813005018001d401060207480c1076144c3c0b690351080c0f0150070300c0c0000310343e541c1e0114034065507030b00a803090004642c00c00b103004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 738334352 1250 738333102 738333119
    0x10c080a062112170702010603020f0301020307050a0f0306080114041506231807021c0905030a060e0a170d0c0e060910020f03120709051233040b10 65
    0x41c0c003580035140d1440301099036500c0841e03c005048052040081c20880c4036100c0e400a104a801841070340c0001030007a00d1441403001103d12440b42ca0710a034414010054425040300c1241c201c01401e24101103084814070f421340040c030b0150081c00c442d41c0303014250800c035080555131600039401403d04104180e80780364074200741e80550040e403582d0780740d0400c01c078007150044450354982c8100403d0754070203c440e544025402007080700d2900042e8808402c0c05841c08404d401d000c0380005914001507864280004079a68070b52080340104203554a002c0d40284403001d1000f42103046c1d201030401c1804010388614810380c0c00c0408040d88452429a0003080c03e8080c40c1a50090b10016200354140f90080c0100045c0032002d50402c1d0a60040800706000300d5018001001a26031110445840382050407005090300d036160040c1d80201002503069258500008011001007601c207010380004d030242c07840a448034814140c1c042c0b034848140a00003003141810310701e40300d000c1150072800220780e9200355 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 738335602 1250 738334352 738334379
    0x13060816020c01030b010314090114061f1211030a0506010f0c1e02031207150b040513060c1107030c05310c05160609050c0609060a050d060503010c080a06 68
    0x52409680100007a82c1c071940203400140034100c0c14100014141034122190070b5420080340d00600d180d55914200a00d0000303140002d400070000c3d641e040e6000c0301042c0c410784902c65a1004403c0c09100005108100d2164021a000320740d81003c8070b480741420346e040b402400341502c010b070102d0105114070105511913400c402210350440c105520040c3c01e4001c181d004003113150141d030180100c1c41050703c110780290082444030721810340d801c41c8010483c0c0e41022074024032502441242050b0a004c1100f50380d0310646880c0750000400260342d4801f000075244c4400d07c040000c92801043c8002041c0200c00d44180c0403070f02c05aa020704510f0218a58103800303811504103c54248408400260045065010444021150038030520380000d03092402043c446c2498115240c9880740b010504101c420b00804400308000da420314100042900029101d0088107000700410101080e061013207021500410020100034000300013070100d55000500624048a42c4a06207080100002ea070030841d000717 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 738336852 1250 738335602 738335641
    0x601080619050405030903030a21050609010306051e010f050a0b03060105040b070f20131e0c090b03010b21040305250c17010c0206061305040314130608 67
    0x5205200384181c00501d002404003400503105840207101c0391a0546003040244040032894650307500c071403201c0d040c690380c01d401101c3d1744050758108028000d0a0303c8074507a25041d07960103140461680d441c0b901c90b203a240003208210954080c02c00c000180040c0a00021050300c5040d00c0794500315807122445032181c40140c6149000074400c1000b086442c032640d001e440c200d8400e110940b581c50310740c1c5071141280665100280102e8580441c101c3e2458074229100c1c050824110071f100c030398105840f025031490b504003802c02481c0c4804415a125118402d5200509040788402d910b0b541c441d50a0940307500001c4c600c0c4003111000c0d80c1415152641010350340302e90351691b07070945010031740303006d90308007581c801e00002100c0644542171000170040c015100c0940a05000b040030200c40006041c05c1d00c818003100c4095410110512080303854007000004020661440131910391510b140848421100c1d1310080d80075035001c03c03d0b10302c00348401840402c54207696100d03030090300d6403858029014200203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 738338102 1250 738336852 738336871
    0x806010309021306090b0103020c120705070801050109051e0937060b0f1c0f11060a0f090f0f050904080c060c041e052101110c0f0d050906030403031806091406010806 73
    0x2201400e5260bc020041c80502d200d04280c6940e00e5a469089007901c07002c0e0030041d916900c500401811540c000b5400212454140031783d202818091504ca80310304690154041c030420341c03403a10194640b4103111396109860380020f40860700d01820000001c01c01c01900f20701c640150012a00c2c5c2c1d15040400d4035038035040040c0d00001c1c3d40c0954522481d000c000300c048840420842183e02541e0b641d50144c1411080b6413158280d2502c00c40e0010701d0074007107030031010341d540342e010701444042140c54201e03041d04c10076191400140c07201c0c00c0c00040c50051074400200e80c03160f102008060803805020b441118890780d1220b9150081c41e11450f00e4400c14020f458100e80490b19909045184205005050b00d01c0c070000500e10350b000c0042c4500341e000040c400e0080d401850000901d0744200104601c18000340f4005040510100019100784400343c0040d0030981c4868548003072058142d01c0600e0258000800c0006034603600d0070003603c00c01d0000304205400f400000003503444001c1089486100d100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 738339352 1250 738338102 738338113
    0x12030503150f090c070c0f06090b0f0408030a0c05070e01060e0d231f330506210a0509030a0f0c1b1818030806010309021306090b0103020c 61
    0x4241d011540c668200803194460681520b1601d40d03119003e102c0d0154884961190381c40c140344c10900185c1445500001590388125020041c80394828800e00564030300603521641c901030804200800d000c0d640160030680000940785030192307080354620036020300c07038025218165134400d50303007221080034407622000c108042101000c51815400c0007048a00c25000e0342260242254030800402803250b141050754006903550300300c03a200014100c900d0a05001c18003050440f0b03403144102e010352000f104039030001c1180400a003880c90b4900406000f000c1c08480e11400310f81600b801c410034196018007031152603808240c0b100b4950040522410040700114601061a482250032020107c406410044500c00000024500102c04401214050303a4400741c182008400032020090030b045a04035450301d0002c0c14223101500919200c00e406003481d0074207039184001030f00980b4608000960201101c15608052802548200180c40d1001010000310720020700550492181502c41c05999200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 738340602 1250 738339352 738339361
    0x50604060506040f0c0302210c0409020a050408010c02010f290f0a0504050414070e161803080c012408060f04110a08010c0e040c0503060d0804050d1a0112030503 71
    0x12900190b401441c054800950003114602c0102190015241d0b10000303030300081e550421050303228000e00d18842443c961034150501c4030303e090480c4114440d402030150040f410121684c024030503a001041400000c1c0b10032642c85800034020840902c3c2d40c0c95091401e01d10190304400d03001303003098400c62781045212094412080000340183e203240150f1090b03551b400441c02e0f031158000d140c05284070f203402c458440a0540c20506081c0c554010903c01021081008066a454403100e0017075000c50400c04c800121070f0303084946028030740c0c001902c0004005000c020707030302e01540503030160308403902458019480641804407200f010b1142e11040e40c44080801c0030880b43c0d41d242c58126111301e0040e80e0002c880d270081604040c4503403114003642d40d210b21900c55250001150f03000350b141120b04014151440e0380140050002a01e203d02400141c503100c07040001da9401c503000340c6030040c01890b03904228541205001c106990b40814141200f00024120130800b00409403140e0680320305045503075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 738341852 1250 738340602 738340613
    0x21516060e0f1515100518190305030c01240e090a0618060e030a120c12150f0b040b1e0d05010e041211070b070602040312081b07050604 60
    0x45694103a841d60050b0300c41852184020041c603c0080c0100c50160f000d45001a1416480c0c2210390b000380c00f44800d804002401079100088500d10f4611520387c0743c54a02c01c0b0040307104001040400c190442c0710301d8011050000c000050154442e2050013446032005a2014182c0345141060200c0c106810b070b88103208110100e45031603800b409a50031906c80d46102e480f14420756040020b40c050b0030000c0c03030b076520034441c50f1700840d02401184070086d403601503040b00092034040340002140d41b03c0d07554412080c00c035225221480604c1a10700080c0300e1040c040188144084a80c032442c142d081010f83c0000c3c202c500e500640701201c0100d40d00906200c11302d02041e694507a248041120200700300219a2050100d224035400380001407407011040c80d1620740350b6441910031084030140900354034503560a00c00001d4010580c1c400c00c0d030950b12500e2628202010b800740340c000620864140c8036110180340c0c0655020304c41c1004414246c3c4440c840680e0b00118460030201410a030000c2d0700280c0401c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 738343102 1250 738341852 738341861
    0x110319020c07030c06020706080c0d1d120306011d060d11280905010c0c06030c020c1201141b0a03200a030b010e0a081e010207021c02151606 62
    0x1444010161900150912075402d0040540003100d101100e01d0090104a40c10420346026204a0078190070b942009007482915003d25900d4140040d01c940500c000f110540c0d5200c5030303503104a0100c03042c80010860141641d001220168002204034001c109608450160315044d010082d06543c540602080b412019202c00e001900207140d040041e5086c51041190100551100d40c1d80042c1c848a841c100508003141a880281085411002ea40114355103104000444400b42000100007108030810b032704041d4000d03440d96004605551851a1782c0064003d0a5140d21000c4d0720107083d520103001601c80440c560746164407220511090034841c1c0a40e004180c08070441509262002d840070319410640d2299540f10b0009440300c0c410440365820510300c1c5095030b0100ca03600c1c0c085003088003096444603103078005c04802440c48001015031600b98100e51000d034020302015017002605007034413445554800203c1c0200d141c0810501c41908040a841c00c1c5241c0c1c90180c3c1036110076480720340c080e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 738344352 1250 738343102 738343141
    0x6070c02010c060509070e190515011d040609091407060f02030d051005060711090a020a210b150a0f02010209150d0f0518070b1e1b070306020315041103 67
    0x500c10304401040c20f8031f0380100103200e00500301c83c0142c21040c8120b04025154094403117030000551906035a2160780002404801402e46010300d0b41851201000501800c1070781d014001c003514020b000424000f600404252410310a8100d4031441d5031001d080702e41d02095841c2c240140c2080c00440c030b0b034207019005a908000c18003c000041511000091003580c0000d01c111115010825001d502d418210310095101d801c000c02142003140c10000505041c0300ca4580391064501c3c0501e08580c40e0441e481301400d26000361603010064918540c62600c1d50240000002103a29509480c4080f17105001303d030b00c5030174050f143d0070070020782002c01c04540e0040000c0c0629a03445d103c040e020381c1240d201c0c65108482012003222101545200541400c84075000b50200080170408200e0b4524183d62444440341a80020380e641d1813501c0b0f0b40600700010405c81d461030b004a110000a10980e0740241d8040c4003d189205000688a0708210403540348030042c50080c00c1c21f00c0001c1400d0b411003118840d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 738345602 1250 738344352 738344371
    0x40506062b0e06070c11030d02101d011a01021608100b12062d01030b0c090102030f03070804030e0402090123070501060305030430060b010c02090a090506070c02010c0605 75
    0x240308002c101c505080c0e040359404000f940d148071410a216a030f441c6403813503200c1640036003460b1464160094a5107041c25a0030004d5450304c034080e9040096807802801880000c00800034002400c2020300740203c280c84190051040e0003604150340003075038511048414402c01025500d1018922502500741944d072194081c02409101d1000c0c00300344030b8180700e901680c117542c0d40003404c80b0540d812441001e25828405124000600014074442e03d0ac5030054075003a019910390000800403461b51181412900d02c80d00d012050101c006e030800b41c60b0f030040c0e221b41c588603503c6221805200c00c81c000c1d04041d07800903285042d604603550f0721403150420030049603009880d01c43c00d41c443c5ca00307440295000701d0b800d5000203820082c00a1100c81c21480524004000c14120340b06080000340c9101160080c0c03080780d550140b940c85a0058441c6402c0365400790107076040f45001984400140388104084da4a4041d10307000881061085c18200a650350503125584000041e450b402c2c0103020090174410b8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 738346852 1250 738345602 738345611
    0xb0a210222050103030908010e060a090c030c03080d06051c0308060a0b0c0a1a010e07050a02150916090e0a030e061e25080901122405040506062b 64
    0x41c0c8662210100119400801d07010030154074503e07000b04140c206600007005645050f111000043c404500c0710740220a00300081204005420414a250802d81c00105241001c403000010040d14030007418544c0b03907501041001d00c0d0390300d05112011900d0012402d42149080e0181d0000b0b015245954000340e020b01214281916020108500d42c0b140034200f6017640000121010018903401580942e002c3c43c12143d081e51401a28409a141c0680101d040c010081070103a94240708001084902240140d101400e0406220072520340342c115040450010500e200400c4044c01401500d1400b24501c1c01414404000d442c00c6485103482c0b00c0d215070000d0200b10744803030f4422a81980f034890701540b012543d2188024020230115240804807071400e240018113402143c05602598070f80102801c0200d001351070700a0840080103155213604280000c18039102d14007034891310b1134041e114281c41c200120703100d10081100328003c294440c0d070207400b982c40036006600710000e00d41c005914040c0119 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 738348102 1250 738346852 738346879
    0xc0708010e01090b13080f2104030f08070906050405060f040305060a0b130905070e0a0207020306090c041103010b0306061b01060902090901090b0d1b05090a090302010b0a2102 77
    0x1800d440e81c840911100d41c0d100d003a00024080c140b044c0c0c9800c40b0301a07104200e03116155031400300794015411651001c0fa80400da4440c03002080d684404440b41260f80032025240c01d2801601410341001c078100090621380c00620035a010322305440c140c07001600c450703091529003c1000500c0c1e000c281a158820400d000c0000010740805c192030040c911081c0204525041c01d0522035215410044004140e08204541010500104401342a908420580724841c0d880845841c040d00c0f400400a406118480410442d00f80c0800c0d03030030408404440c18400b051072409116442c0c0021f02804a1152040000c5296841c201004040741940b1903081905030780e5401105013101c1260340309084840e0009901112403801c08807507405007058500c01c100711030320800421240c001e000401000043c28442000c886102001c00c08002c2c84024181c1b40185880607400300a403144000c2103001d58241103401a0701d140c50200801500d84041501450300101000600d41c10180d900580c4c029040d8004e01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 738349352 1250 738348102 738348119
    0xc08040f060b06090d05010f0c140715061d0f0c09010816090305120316050c150606040503070611070e010e070c0602090d08070302070f0b04091a041503050111120a020c07 75
    0x83c1c02980586e000180d2010046001400d0300c00007221f2130100300700410001d001c00c070003800360717108950800c0c2c040e00b500d808101d80c0f50080010742c100c4056040c1001c2c051016490008107288034403142d00e501803582d2135081d0040881e00840542d0384c04111414000b4840800341540394406010754a44207980c665691030345424000c03294038184400b84000b04000d02c51b03030381d0701c00030502d10242d2401d541b81040301c00340315444004841e071b0344000c040400085099030791010180d070301400c40142900c4070907a64a4028114030100b02c601d103810701400c04006040881c004405040358403078400070509940d00e01c0c088488c1121034004a45840e0b0a20000c1c040382c0300d2443c545002841114016511403103401c000e840c007034055000004841e8080c10910030718481c3d506072000c484210001080c102852440450a6203400000c590080d1402640b02d4840000c170900204803401035000b0072016005c5140086607100b004185007402c03c00e480441c2c040340c0030740e00405445001c4019281015218442d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 738350602 1250 738349352 738349369
    0x6040608090f060f06040b1504080a02040b0904240f1506200d0f1b0b06090c030702031c09020a0602010c0f050306030c09040f0b090703060c08040f060b0609 69
    0x82800140210100445840c0070840b405034108404000c0c4030920340450303003000307440c402480d0900994451001442a46942e5801007414404145082d100d40d1074102182c3d86100c101001c0e40304505003480f00f58203013000c0c9605401141c01400881c81841c5241c4440b0428140307a0401a0966039450f040c0c4500b5211300c5001c0c244194078203610522480c0c00b900030140c100d014003062200181800409948400007411340c500c0600c0d00307064000b8181c0c1082514008003214050f58100010756202c010044002d1a481c8940400c07182042a500c890141c2d14050008032034030000359000b0044140400b41ca4001c03d50711405122020030450102ea01161802010364080320150f03441d801940da083e13400400380d0400042516190f810340c075001c00002e17502c050341444180122044404101800240038800c003060703400550101d240c0c20102c200941d21500381c40305642c1d41d8940403500c44054400c150403030140d904152001c030040360b6500c0d01e9005081240ba0264021410803803c40300f52a40e525 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 738351852 1250 738350602 738350609
    0x6091009170c120303071d061b010209040c0906021213030f0302060403020f0a02150a02070e070509270a05220302070503060609060307150516050c130605060403030c110604 76
    0x540301e50302402d0140441da4030a4601034a07107400a00400014540c0004020000d401c100589100e484a0b90045180362040002011150032415218000101d0540060410340b1051710300708507540140c50112032080440c080c20303005810070501c01941449250103024541c8900080503289551b0b81d64a80a1151292045000d83c1004040005254050002c6103120311403201509440003160300140d00c0e00304081c07801c60261004100e644101d07200704840d00182c00346000505447c185000060f01541003c2d00081c4514035002807101403403600100c0000b80d05116902d801c01d41c031a041103502415000345164080601d0f1201e400c0040c03000080500da55020360060030728242070030203041c01c003000207054078010380c1820140072054a0000f0080121660255000d0250100c004210b40c24861a402002c600740400c041e6000c1c0000420384000d02da008899418807002418010014bd800a00c200b13030b8414400c3c8020000720b40906c5515054500c40c40184d02c140b6040f07000030303006410542 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 738353102 1250 738351852 738351899
    0xe090705101d060c0a0326010b070c09020406080103110f060a03061d090a020108070318060515220e0c0405090106061403040b13051504060507030f0b06091009 70
    0x18051a03080140891400c0c80b18040d10341c1454940a40070442c1d80390b025042c01000c118400303054131004289881d695103820702110f41c8200a5a44034604200707034015030380c00d03aa40d40000c000042d5444052080358126041926019416840c68440d15007003128806129001150340029084659480008007400a115200000c1c07542c01c1801c0034074010039440d40c42c140c04000c4414001825800100c00d040694240b80c04001070b983c080c03049001d0680d0424a000c8580c020801a04100c2c0c950401c61042c0d9442d0044454102c11a04006c500030602804014801009442c0c41025445401032200240d1302e0f0f00b02ca40f422140341c0410120740c8101c46e82811079650312428019540e10524013580c940c0e40000f90390450810fa241d0080ca00809801c001c10002220704031000c01509001000c010201d00e44010180d150030309224014201c11162100040d1902c069010038074894481d13600b40d0034015041c0d07800c014505045c414140700d070001000a0250044000542d210254044c180d014480d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 738354352 1250 738353102 738353117
    0x17010603061d01030f020d1b08061501031802060a1b061b020607120f09050105070905041107080f0904020405030f070e0709030b061e0a120c080607090e09070510 71
    0x100b8981c0341c80e081c45040c03645000000c001000460700100440c41c4290301124038881d41d0449241603040410018910807008281e00b100007000032021a51502c5003c641e004983c880400c1e600460860310800b00f90a460740304481c8190140c2805000351a10321158149260340a4205042100c0400c1d441021070f1110346560f00c0c0c10703001c4540141341140840740c0c0028000c50521380006004100034418404980361354188440400c6000d03002400c801c0d8001008008034108440010a841058086d9a01032403d00540c00c1888101c42e00301c03080c40e60002c0c601800e00710340081c0281990701111080d6417103074003030001089690b0144408066015800001c1245a18100d00ac2c0c120380c5000705075005111444908101054074044085d40c0101c0484440410181a140c00c68a160455168580010000f0741c042441d01c07181c0e03080c4c00a0780c019411414407039a1054090394030300b021544100000d040e0441044501c0c01044516000400300003545c0c0403030f480b0b10100700601500e81000300041d142 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 738355602 1250 738354352 738354359
    0xf03080601050945071d0a12050105010b0a050a0513030b09061503071203082802070309150927050a05070f030c14250c1d1303050a1701060306 63
    0x1c001c655003c1051020304202601400ca5008804d00000d00f0380c0140220a13102000c0e600b220103000d00c00c048024030f4a1003498481d4901c1652980b0384100f10748540c038140000c166181d4000035103944086560700d551030324100b110125881c0e003040070003100143c0d8850000c00050320041407035128042e508020089441c0060040d19103213032481d050303406030300881c00a0080b421046d0801440607014108141c40e51602400404e1006400d64100d407092850f074601070001d0644c4d0010941c05010b81e8412501035140d4200e0480d0080c00121200400c5000004101e452100b01c0d02d03401c0000712a940340203000003803091009a40d0112840030045946104100c2103d400c82e00c80a14030009140c03c104842e403000014010001b1a10a400c0c0c01101180d50b50903d03599040580303c0c00c1c80d96a10468166451605c08070f40d80f041d000300d8038000919904503000d011385a1496102d00001069003079800c2d01a1401d40306640440040c400b00305000030305c11049143e0031146070007041e1030b5500240075841c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 738356852 1250 738355602 738355669
    0x7060804051c090302120319031d07230303070b1504060b031e1b070b0a1d06010b07110907090305060106020f120f040f090b0405130f030806010509 65
    0x42d201d40400c1070051007020018960b80040250150380e07050321241007410685500758a1805203040781450b20440c3c45140c110720307615401c1b401c500ca1103503880c0740c40743e5500b0550644a807c0703401040410007042160841c81104500414005240541524034205090301d074414a410115020701541011540511060030f0030b01c525401015507540d05419820410101c01349501300d1086501c0c810f800d200070400c0149681e0076900740d5031000d500141d4418061410841c0032400b202c03004039103403810441300040b07110303904c0003920381c600d1a0103072210303a09000e103401980d04604000d0b07501d4007801c603211440d500c0e0080c05c41c0c064480c40c0c445a5a4500e0751034581d2138540160400c0c4215003114492a40e01080003e502100701c5030110303001e07265a1405000e502a010755400901c0c03040c1441c4000481d00c01d5544411f44040f0103803001d008595174030021802d1280c01c2d0b64010b00c401c010320070b6070300828403c044282d08000c0502d081441c20b65281d0010fa095000c450365411505a0811541007218 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 738358102 1250 738356852 738356863
    0x20120090d020a0308030f0c0403051c031803020105010807090203040c0b03070210090609051b010c0204091a010e1f0e070309170307110114090c091009050c0921061302060c0706080405 81
    0x1a1001d60f234500c1d041c00d5a41e4151200b01048410350160381e90507003204c0950180d0492000090f4881c0b00d2110140c0703d0900038040c10003031040903000e028400d8045103e00c1d45000301c900c181d4216170b900304180e1503c81440c0080d070000704100d0450081000c545031008450140505640c010400460070034040c1c18424101002c41d02c023340003c0c241e807542c4140780d8100a0390030750190115400603405040d0700f014039403000c01040d4041040050310012521400b1070400b1406260703602d144e1f96139800214082207560800d40900d03010b503080003000842541c803a0700422006440344200ba0000c0c060b011440909800c2511342034046041f200d82103150040911034005c170749251807440080c13414405402c5490781c0140c0030306801180e600001620a04e00e402c0008020280440c08201602d031040246611307030804d840d200d1140360300c000705120102c07070307403804101d48414031000e0b00780ea458005c0c5004245071010360403030704400180312081800320103103d580020101900c1c0c1d0446403410745811810700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 738359352 1250 738358102 738358111
    0x20f070312030e0706120b0f04090302030a021204060503040b150a0801060501121803030902031501030b060f031606120b09040f1103160506092e02060106020120090d020a0308030f 79
    0x691203800108517481d8800041c0341e0f1100d4103800001c0440c0540f0200f0b0600050210b0540c119041408034410964004010801c3c80c030203030b003610040008000002841d00c00d503c40d40d00003c0b01480482c000c00c004070116038214490b00c0c0507600601401300031468041281c2d10142d9140d550700c40403c42c5580000f1041003114400740d04201e588040b035120b0452900d5030801404041e91102c806046440070041001d0003006905035542560f500d14018104000849446005020403800a60759080c00039400c42403a1070301c07040741c0c40706042503030840c0d2038007010842030841c50329800c0482d01501d503510518081c0307010300000c0007840320381c2c00c0c0185055801c0300303c203000358403034450b00e10640c80720b0304840d06680080300c10079a509401c07800100711130b125080804640051031003083c0c5981c0e48035031000c0080c81e5034080c1c40d0a680d035036209900b280c8041e603180040898141c513815501850400400401c3c100509020344180c0c2c5401047c003624954000316903509000085c810f070204043d2140c0c2e0702c0f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 738360602 1250 738359352 738359381
    0x4020904180516140d060c020c06041212030504050615030c060a1805060c062404020a03020a030e0303060114071a2701050c120a0f020d0914010c020c10020f07031203 73
    0x48004031380130840c05480c5070000780c0016a40e00a1060a03442441000b480480042c42c59071100d0300c4104103400d8407a40030044a02c1400c00a56401c5c1324081c0c010180314035005009462240d80e20015120030b900b1180741594103018410100300d01e903845e0000740c040701c403c507655035008110100080f5003000050704003900c00c6400b0f0001644c10500004c00c1c651104099000709410110038816003100a02000b000d5842800490904902907250f80900900605952705000400080b408103844c1d10080c2c170201d000600e502341c0d402143c00e050300280000361042d802c5248600c5a80c0e070f4203001d100103a48461510f00c1c54610084010b400d41d00407009880010004c01050501503a070360242c2c4200303c002ea9000d681080015221806a80072090032000003c055540710702c5103420f800149011001101c81e0490344040381e402050500c5401e0658070740303400034503410708020208400a40c50120110861240400080707442c0024080b1a0055110360032aa1000380400703401740c10348582a500780035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 738361852 1250 738360602 738360629
    0x1023120f010302030a120302090d030c050d090f06050f0f07051608120316030b0909010203060a08030405181003050f0706090b090907110f06042a060c0204020904180516 74
    0x981d80c041025544154000403e08078401c486c8400e5020307000e020b006981c03101c036032a031003402c1c1034001404040651050040d1201008601816522510f01c0d0040d2042c0000c1c06500384007641c059802400d0038401c3d031010508002c0240150b20140e40109801c80b02500004a01640440384450a1024080c2100503207520000c0401d000315a00006002d00e0b9250b41e5407613102d0340e0341d010b0340c00303003401c0500500009454508125224040d6009403401c501500500000086289001c02078805842000f89600c000750007585000b40e122a02500c41c5d000306810103c0007000443c10851016071800d480b0141441d90b00d0040090300880466000016a410401c8114490b030360322102d05604c0391150411600c1810303202070103460240003404100861080c88140420301c0345c0c000001c0c96504018252201440314641d0304401c80b1a18450000403a1a41c0d5080c2c00500e8207402415076140042c1001540b0002c180300c120043c000c0e02c0342510250003032612440700c0c0403026001c20160685074918007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 738363102 1250 738361852 738361859
    0x40c080c030d0e0f180702070e071815110a05240105090601082d0115140a050309031e07030f0212120a0b04050709090501091a1023120f01 61
    0x1400d40d94224101445920040e490581581e507005c80103c0c2d26144081c9201c45140c08103020b9a104128001e10383d031508064001402e042c86200c20401c801204082640250314104032080d1410300a44408107000310302c0d84d030f04840642001016605800b078002040c20b5212002d100001640d5009440c5654541100600a41d125104c0c0039800503400c0c41e04006a98400c0305a4240034240000c10f4413400002a40d070040483c01a0594161642500d0310070054070410000e48401d500403203e580041c006024200038180030b08081c5501441a106591415001c0b0b446110180340c50020403411900100307400080c19409942c0d140354a42c1400280003a91103812000030501540000c4810308985400182980305c6c40c4e040314006500c00f92052000d41426400a80a10800c0c024100d1003807400300002601c03002400740b80e09100c81440340310440b0703130740e4070901c000810f0b5070280304148504140b080820507011002c22091040c0c0d107844c1601c03000c07004400200028042d2814402c3c480400050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 738364352 1250 738363102 738363107
    0x3050a030f120b2d0a0801060e130c0513020d02300603100b0d0b15090912180103020705161e150c050a051c090503061e0a020d05040c080c030d 63
    0x40c180f032080380e0185000b002c20211303501c602a0200d403850360400b1000400013030044054002e0f905a41d050810142e20ba030b55401c00302c9108940f0071000e0000c03030044404020750305280301400703244141c412000d49080340c40c0403120181c0c0d00074000d5003840546003090400540d02c8680200c000c80c40701c4000700b95810a07400282d560b64018203003000c3d441d03032080400d4072aa50741024829050f405004c144440ca4039240500ea241c46280c05940aa44924005441080040741c241c40030070001c80103d05100f0510482030080c99445d0205050550802110b000b18004001d0200080c142a0b503940d205403c00e2809203080d19221481050300803080c20030f00620520b480503482c071000c0380c5091080685c860420619129482401624501940f0900900c19611000445807504103450710b0509a80d07403002c0c10360752481107070044241000000c16803a00e0102500f0b02f500f00d400e1010150074503140e100000308840080e2821182202540c0041007020024006a1603000c1308034094200d014811001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 738365602 1250 738364352 738364369
    0x50708071b050a11040f060902041509060215100305010e01061a0f220b0a050c01060f0b120712020f09040509150a02090a090906020d0614010f1101020403050a030f120b 74
    0x1003d144c14003c8100d12500c0300d6102081001a094003803103016560f000b038000961044c05800c2404220f0701203500034034007806a440c211030701940102184240100c2d54046000003030321010710050b050900002080c000d0040c6450480700d1000000e926203085201e016601c91100703000750381001440202c403640c14100940322a5452500d968032a90154030000500c103072a9040715241c0354002c500048a651303ca0701400c0021000c40080020586900c07104905102c1c91162040c00703182040500c034140036000181d90003801600744601c1030090300c0c2a40d4183c0e004148800e100308000700e00c025042c0f410f8054950000440c20151801d0724004a80c680d900c00f000307114107007883d0002a1b42c062074461408410080444490800110f070b103e280540113580040b0780405040d003899000318149420400c3d4920001050710b030102c14000345031090300d09a00c803160501c0c44d5542401300001282040c0f001c8940341c0c0c401c1d40c0d070741511591001e014001440d03018070010b0691404050305102e45480c50b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 738366852 1250 738365602 738365623
    0x9050114180301020906030112060501080705060409090302011407020c1815100c08040902070b06090c0d1a0a0f031e1e0f020d0503180102010e0a0303050c0d050708071b05 75
    0x14803071618008101003030291280d40c20440d00f2420010000400180e10b50642221920610080c4481c1e66201b24a681c0c400284c010075a00c080d04000800c403059403580a0070409100780004070320031050f902440a103d50458040d005030300401008541817405190102d41500411041107107400d280b0510743c0c0300540300e83d609004041c1c40000240d1903000b881c50404070f83d42701c801c2c15130300c9850b01c40032800394021210841d0814400008602c05280c84280e0501c1000310440e00340c200880210940042c0c4031040310100050340c2d0030401ca10540310440c500024142800c00303150242e02d1032400b6044441001000d0301541840a0350304002182e13403102c1d0340b1800c08080d12094000003402c10394900580c1000095000d10802c0e503050811201101501619101024180b1200b024400681c2a42d110018240f0945c20908940002a020707034010b5070000541140c50f41050f00c008850001c03a2070949080380031031144c10421a246d03501415140960342c108510b00000c02090389c41b241d4903090b105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 738368102 1250 738366852 738366877
    0xf03061f121d060c0a050d06060c02010e060c0d03020d0e0106140a0e07080c07150f0f050105040605061207031b0503040b012106051909082101210618060b0109050114 73
    0x5903680301c240300c0e100747c44282510785820083e181e922240a48909034000040380411090900900303285000030599a00050b11805400002d00c0540d044009602c00d9007006225a0344580c28205404248254805404c000044d068036181d41d50800041e440d117640080c0030b801d01c0c4420094082e911010190300941c03d1802c140c0c8814841c68001d44c3c81c050b00c0e541c29041403a112403081c01025941110320608149001000b2030390329030040c0f0040c1c6900c1e005058000384200202071500036040750003039101650380340018140c54681e00d200c1850b40f109400000048022051009000050001a00402028010010804012001440095411501802e655503070800900200c00b20048600b108038140310401080d0501d14100f5a107400c6444849080705000c14044289010300c042c0c641a609441128805c032002441d4205c604400014215601503d42030b100043d44c240a07283d0411520900c0c0200e1080f41c0d80000401d0000c841d03101a040108443c43c4124414a0108541c01c1c1c92212 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 738369352 1250 738368102 738368107
    0x332101180b06041703071518020f03070902030f0108060609060d06051b04080304030b100501090506070303060b131503090308130f051509100c050f03061f121d060c 72
    0x7000180c003d00071540044030704034101144402d4184007000a2038414484c1d0800c00348516a28a01e80403900e9034003440c41c80d10790000000c40549401a40b010401c0c034001e0480c0c5984c2e44800b80802a600103544102d02c0c00c00f01c1005000181042c00a658000000e0342c1d1503481d0314040300007403d00400c400000d4440c55440f404150f0140700050041e07207a07019800081d41c0d66507120b030415566401844203450381c0d01500c010545145c900982d00c001c5580503903070021058140b03020005940d0011782c044040c19030301c0070f00007422030000f405420100031082908404c1480c1100f070801140b0030010f0002018600342d61000025089103001d5044118401c0c1030000003814130305490903e103818000303411403103441c942c4180d0444102c0c0300d520890990b4150f415110359514008142d2320102c411034049403050100600d4001d014016686c40710b03004001c8a105403443ea58180554014010b1500141206030241d45402e260301482c800e46c030b10b00c903101d5140110385a80944500010f0513080509800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 738370602 1250 738369352 738369371
    0xe0a030b0a02070b040308061c0803010b0f040918060e0c0d0602030a020904110901020106050102060106301a0301320c0912070608070f020c33210118 66
    0x40e030b410f44002035440000f80c141070415081c007802030036080342d1740303440f17401440014602c11721090441410075a00400c0c2e203007503900b44200c000c1207411010440850313000034040068064003602803202c44c084040030303540c0800d816003008003d5901e941c00f0350740385502100580215490302e03410300b00d20715003009005849844020b844006032084008190303100b400e188507660050041402001090703401d8008104a40d0303910b0042e40c503030509124207000b061030500c00040c03d65208000c044e182c80050b01d031002c4252250f1551040780c1c600c0c0403601101c480369040c84c5450909110303956200380d5074004051020540c22076410340d49081c42c94102901c41300e00115601d80700d680d0a64500100003031a1107500142c07421282d6070b1f107009200c0c0c507001030504404036405d03601503201c049203804280d002d081c01c40140310a2140c15036540c89003400301c0c01ca41002021490700180c03643c0c20900c40b851a42d0b52038819203c00b800c0842d58800807260050a4801085810304a15500202903141040854500d14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 738371852 1250 738370602 738370621
    0x603120313060c03060b040603150e07050a050a02280c05040e03090d02031005011806050904080412020d05060705121501020316150908090306070e0906130905100b100e0a030b 77
    0x2261b900180c0700d03110129000c10310a405400820591a0043c0c40c00c01555480c1d0b034000640205880a4011440401400344003a1142008001d02201030040364500189454690514403651106e03001e01c0341c1c00480076041002d030308040c40007000122814031070000c04150143e101e200d4560b2840c4200012841401152405c0c80b90704424418403900300a00c0d070b0340ea100c6040d1100380d00106810785103820408941440d00000e031900880d003018055040c03d0405526030015058880f040e82c1c0b20208601502c00254104a0076200c2c006959409441c1d51a000c0640a140f001a01c03c40001e410301c005108266400815148901c40800c0b6514602031181044a007258044107803501c0a1b0400701482c00348032140b0000c114085084d000c8400d2503480e00303401c441045032041556030003000c40b40030907801e2510201c044411101c14400007146003143c0c0d01d0510b0842021203424240b0745900a0940e903180c404006010314410b4104002102450400910100c003c6d010040c103480b0a03001250700d441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 738373102 1250 738371852 738371861
    0x70b0d090507051005070510020313060506032e1a09041209090c051c09050604020108060102160e060f060a1e0c06023106091716030b0603120313060c03 67
    0x43c2c0030f000100c03134140b8044014040d50042405481601c03403d545880401018403c8a00c07950030a02c1515065074640c2c1c880d0090030018000550610540010700c030083c202c01040c2c040c0ca03c041c01d5408420302e2000640c019220152802e21550384d0702000c18003e03032110100c003030740990b102d40c1446199201c070600b0f480c00c080c2a0411b0082a1604852488242c3c102d00206449000480101401e858060141c42500c0040b10028840d400c80d0b00403c4c019401103810700e800c280305005980d01c940c915a981540902c060b80b00015400c83e00090281e20300785550301403d1300401761683c900c1d142c101d000c06005901180c00951500d05213081880d0a20711031074000768850341c001401d5580703400340711b01d984d01c480b08042424080c1c900c542c0c0c42600902c05441080c01c4a02c50344601d01060310340402c0c8001c8405071460200c181c003ca40340010354003541311203203020b944030f80841802420400141482d150ba019200c108100080092040c580440000000e155a206c8004070705100c00c002c0840140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 738374352 1250 738373102 738373109
    0x821030702010e0313080601271a061204060c0302030f070c0507090501030318060509010e040b041404030801030b0c03070c11030f0601090c020f0c010c151e0518070b0d090507 77
    0x5000c0401d4842e00a80c005c64010200da00a004658813a62200e01a1071b900700030001212508969150701024100f05402c000d4a545a80040c5181c1c40000000308043c1e07442244002c0c00228004104800c2000d14426004a80c140e407908505500e071440104d510160094440018407120350601801c002c0c0c100100c20142500c04801d10075545d4a1601905028030341c901c1c01607092910700b01154852140b0b0030348001c2d400c142d4442e100001c0341407d100c001d202002649810a40f144017400c070130501e0a9000340224440d43c3ca04030030758914103000c4020340001e003044006c2142001444500c03075001c1c0200c2001500b002c44000d61303598030400285001101c2681d030303080b0f0090400000c1e444d0350707903442003140c0c02e040d40039590341013200000162150510344107180803075040380c00003010079680403010411001c05a40050080c0311040c24101078150308032800e0031185c8074400c2003112903038051140c3c0e80800300c90041c4074403814202922818018031410000d00742e600c800301d03814044100460780c000e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 738375602 1250 738374352 738374381
    0x8180f030d0c0816142a24061005161a0106020d0c1e0c030f08091c02100e0105130e073f0e060a0506030106082103070201 54
    0x700c039003001c0004040c0600d02c0c04100415110700015020800700c100c6000c40010a5441100c010340420301d00c03015810240c42c2e01081d0080142e24406103d40340da0070603400ca4800000c12196011941400c1c01c441614810100790303000200303014940e01c40c44285560301c03c4c1802c2003502d03025400560036909103400d0000d880c55049101c0102c032103d091a0440c1130f51481e60a851511f45003140c140d9050b503480740010140b00050220f0340140890781c81e042d0303046202e6084501e2030b656a4440e040e40d092500c030242e071070b50000501d004075031615071082e0b540d8000140c0c0001d0500807036000141d6801445880788180b110300c45860004d68440c1046400314407646981254440d01c0f0f00c5641e080c803008586440108480c809186034809000c4426891512000d400c0c01c8003000200a82c4000070790300010b01d140e00d865004405400c030043c4400341c400e4400150018140c07800304201400d442c0660300c296555003008048600105031000c90031240c03020309a400350740f601d40d0300d8105d004212180400e180c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 738376852 1250 738375602 738375607
    0x3060f0a1b0c060c0c0f0c08190b06100507021e0405240d0c1d090c01020a0f080f0f04120302070905010803041e050909060f0a0c09090c0e060a0207230108180f03 71
    0x1000138040b92002950710340821107a110032081c4191089040c081c1d4050318440ad10b00000755035181400326114501401e00c0c20504000e22507011848211550200d0b400c3c0ea0164070180e0030904280c454541d0080b0440351450400c0010107802a140c00b251040750301074840305040006001500100c40000c000600713010300c0d040d50310488141e40710b4082c1ca8186281c010000c0000066100155058509400c15a444010507241c0e0355110564000e451035078001c171041c0031244180b40440081c00040c0146c0580b585c21040c03600c1c0003402c2030b40e41d03000445070916010040c848030b880002a5800d880e040d408e51012000f4004d030000040c1141e0740300070f500002c402c040140000012800e50700440f85901140c52075107e04444005480030200208001140d9600820403080301e500607031101e1000d42040281c0c84115004034489510088819000d603020700010020908880f100c0100200040c001c050b0400690000800c08103000c3e00780c10305000261005003000c44103124000c0e9040c40c03a001c4a5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 738378102 1250 738376852 738376883
    0x21c0903020307090626010b040510080d0f14090d050a062703021207020105091908070806010b07020607212c13020c0c03060f0a1b0c060c0c 62
    0x144814040e01080340240a409800284000c0030300810b019580c2031411348403080420505c01c01c2140582d110f1003840c0d034840107400703516159841000e02400035150108032403428241c520b4070300700b18a1440300420180c10810300d6803580c000790454007030300441015503440e0800310006000d030711030a0029005020b0700e000001006010741c850354115083c1c004d00ca6103031000321608100f002d07070014042c015030019880d0314030805146004008007881418001c0c100365060020681450f020440250300d045040d00511200004024590090070b00320300821312981841d103068414049d000009000301c1c0e02003022410050440c510b042400742401911080c00c070845c1005089103c142c02c0341d480c4640c11541d1403420564012104403000001e44140d00f4100c041d009100213500003071013604c090043c191001c0b01c560b41400f9560050a0003020050681082940481100c80c0c0c0b03450700446141548100c81d0803500401004a5581c00240c0019000143c3c0b0090f03940250403c0010080d644e5a80802c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 738379352 1250 738378102 738378107
    0x1f0908010f020d230f06010309120336080d020f0d020a03110c0309150903010c050d05010e04021507050c0a09090b010602010614130b04020309060a051005010f030c021c 74
    0x415000480c83c80501074403828480d50000000c0407081400c0d40c1c140040062010b480d9001243d0f0008010b14000440a0390742d103810240403404403182d00080d4640c0c0101051176040c540c400f803818403103010182e5801c25141048011900003000130702041c0c01082c4490410101d0741a501260000200c0e540c0c0c900f01c040c2c1642c001c1d4417001d85400864613211448459070080070648040d161440000e524040c1c0d010100410001500040c0800c0075040014010f10745087c0600d5145840c40d8480507112001d2403c00400d485058000c001c80071042c2c070801000d03a03181740400106000c00f44180355122360900702641051072801c3c0058225880f2540066110521303404609840d0161905020598a07074030100d090b24100e104800c04251604488540d915015001c043c41740340c80c210002e00c00c040c080200d81070742c1084032030700b40381d82064040000d4540580a881d034841500d9020200041c1810006007000d400c11007035408055446012a0b4228020001d02c09842c2c01840c40718084071042000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 738380602 1250 738379352 738379357
    0x1d13090c0314060a02130608060d063e0a050711030a0804030204051e3c06091332070b040807060206090d030c05070b0a060f12021f0908010f02 63
    0x1000c148a90f000003003030160688281c170b600c0703c1c41a0f25102a14030f4490b089031076000281007142c3c0320718824a03000001d0968031940c1c06140c01e22100e801c10160392140304680300101008104001c0c0141154801e29220030101c80c20a103180c20704945420b840d0521050200c0c15880c9903425101d4400b4800511413150050b20499108850901090b0345204c0e003401007041601d1001d10130010302d804524101c1840c81040c1c1c0e07100070754001d403070102200f0001c0340e0480119080c201c0001409806c0c0445400c000c0c1c03c040d40107650542d886d0390101c0310341c0c0c0e00e07003456201c50130144031505008044009031060303a242d8900c00c291000300d44009484101d148015441480380031030700d2094041c0007a9050020031010301c03c0c0c40a0000e042e0400850100303401603c044031443c0204082044642c0000301600501303030043c07400740800103405051002105584031a40c0002c0c00c4044407000c030b000182e0301c40103803560168000c2c0070203010145107070017500c0da05130f01d80008071554242503e1b0791420105502 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 738381852 1250 738380602 738380633
    0x10306050601030902241c051609030b0c0d1e0f06080c06190302090d03020708010b06270a0b070807110a0609151e0f0f1d13090c03 58
    0x10800c544581c0c0c010340440e060040000d4021100c1c581440700b0072564166500316114010701d00c1d01d8890500705600000c07503005105a0410f40d03030b205010543c081e98904000c402ca181c200100c81c5419a00d640c0e200e02001400100d40722800618042c608500350082400148000ca98400a13412119002c0c0a000c10030000c1800502c1d0480c00529003400140c4219100340181041d4541511500b4011041085d141008281902007111802c2c5031108561a040706010f030303000e800e0b56410b1041050030368001c0c451140c800d50080c00b0381081c03a440c03040c0c800c1003042c441c8003442c1d450300524040b84910740035512509070f821002c64000706100619008058592159982a000f002168100070040130385020755000254500018000745100c01e0382c40e0401d000381e04205040c0418201e40110080f5180000e900007200100409a40c1d0b41100c91920440c5942c140f502c4030150845a10b038084024606551040980c100e04401c42180742e4400100c594201c1224060700d91030742440d4001c1c108210 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 738383102 1250 738381852 738381863
    0x50c070804290f120606070b100612060501050405100c020406270c021c1b0c0303020f0714040903050f120609011a090d11040e060709080106141009030c0602060103 72
    0x4651120002c1940480c0d04030452528200d0504204031010002984c0040110390405020032441c070210781c0441600344100410000a121036041000092050300884d055101c0c00c2d052013414801aa003201c00c1d1016a01c1c25034205000802402084401c801082c4c1e000e50068078000c2d000c60703c0410309a810401103062283c40308142d0480070054203e400c40411200140c01c041d0321410450380c110301c0c048044100d032a01c04140000702100380c0c0d40e4208118211404841036404001309601172100440e0a20040d024004661a240c00c6492103100548a10b11803580d40d9040c20806005006881001505a01a6481e258078274058070030024241c9000740b00764222000083e221000000700e00d02c0514000d2581d050680d03d00030b02854000d140c808580d0201d00440710b03101922540300740690611524020801410448809000038030a5041700784664180b48044c0b0000c1030904250704500c3c2c2c2680e44181043c0c5640045a210f401504001c0100742c5140c80022501d0b800102a41602d0156 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 738384352 1250 738383102 738383159
    0x30204140306010e0c0922141e0415060807120308010509071202070812100608130209191508100605041a0907030f0603060e16030312050c070804 64
    0x882015690700d002d100f5008642c0e1288005040c42c0490000380031240340c06030140781100c0c0040350031208485480b441400d21641c1e603070940d190000320001140c0025127076100c883d441d8000045a03000600040c4060b004c0708400300b40d80000289070384036100404400b41a6503000340c9a600012802103045010740025840000205513490617000450007801c854035407460042203800102c0c040d4015000c161195507050010100c00c0c1c1c0700004041c41030761058180241395003440406400441701412000b150801614200b0043c7c50710202c270f94010005e060707803001c031201aa030301802030700d050320a11000c1c009502000400540014804907010780d481e8060002d0350300d8406001c1100d0480c40061019005012190742c82e00302030340060742000040c03502040c12612561100c2c1a2140caa208136419a81c803003080c0110030051045804402c0c0c1031500c0e0318818655140188107588036500d2185d910f6654001c10301d4202c0c650101d60740d440c3d0001c0744a84503036640a20307072000444551030400400c3d86 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 738385602 1250 738384352 738384389
    0xc0a0f02150406020a110609090a1b0f0e040b24071109060a030201080402030703080c0a0201140c0304151b0b15121f0e012a050a1b150c030204 63
    0x1c1c0303026607050307403110750017841071008503103502c040e0020160301190080710810842d0260340b1111641032081301e60700c038080742c90074001e00f0108070b90100d02d82c544104402000c114503595030103411501a044103d4000c01d06862500000c0e4a90200701540507984100c0c00502c96101d8001c005030403164010007101840da0405802d00074070711001c41d019980040c0543d414001580500c2c00c0b036400c1800501241c008c140c4075603070394605a000d100702010641c040f162a108541c0c0c4804281d0041c6a0141c03c1d900703285607401703581e03500e0040380104030002c0c41c0844e00c0b050440c4101c00c40d41b42103801c1c00c505440030800d8184407030301c4801036074a01c02e0b811610b580e0804500f8201016100202168000d006040011071119085a412408295000e031a19400161040c090241703500c4170000c3e1245010740d2480861401200003004006820b00500b401000c03182034000c20304628040620322050308060319450f045c0e100050220b00f0784a035030702e00380c941e044059241d4054010703a59030130320102c8003511 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 738386852 1250 738385602 738385639
    0x90c090f060f1409070e060304060e0c030607120c0518151c050601081f060e040603060e030c0d08091b060d0212010519140d03051b0610050a05010203070204110c0a0f02 74
    0x85c11740d1b44541000d010008140002e200303601400c0d20795003100507a0380c0104640002070400c481500c544000604140704a64100d4092003092100c00300e50424034a0b000c0120041549143d2100081340b203024058004070100c680101100d0f4040a250251501c03200202da0040c0180380a54801d80010f1304180003405840c1b0854588094034480407403a15581e1030450102c468003180c2d2903558015072220000400a1101e000d03050460008a02a58540e050726000301d160200181d505401c00c10340000b4490290b0011038090751400000380030b80301800ca5031000c101e01f03110326240401e81c5031000a410b50601103024409041e96811034034003030900c12000d140507000d01c15000c0c10550309440d00035820146001800034007618800d04100f41071043d449440340300c507961400e4044154005400704071002d04502b00110151104541601036541003200003596400b80580c000d000f660340d501d01345400214030042e100d8446015003200c680440710301d4484205481110100d014a44a030b42c6003a5011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 738388102 1250 738386852 738386867
    0x111062406090303220f08060906150a0603050408071502030a050916050906120106080303090c06040b0d021303050d05090f03030a0f0c061103070c120201090c090f060f140907 77
    0x620043c0158144410042000025018440941514080440005003900c00e002e0b118000302034030400350900381f9241010506010000b02440d0006462402110f034036903894907144d040d2000c62500003030342c1d956841d1481032403244520107054410700307403050796920807160015889034a44a01c1032013039480c0d074000305954008451520a180c0f4620320140098100b501145500010052034940035894040702c0c1c1c0d007142d283da040400250000020044c50031410084908003280590304280b410740782410081142c05401160740c0d0507900081c0e00842c0d02055062000a550000f0913140c0107e00000060425480788503100d00a00d0720300c203040940e14001c403e90300c1c0840325440e94581c0d0002d20350f00700e07607241c02608201d078501e40c1c03509800560f01c1c00c2800f5520030742440d01c9a070300c00392003414031154551400d0400c07000c680c14020003000140c5602100c2c81203c407603410101c2c1000d00c0ea100ba501400050300403035644402602c00240210720314448d01409001540c2d0724002d030315064030484190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 738389352 1250 738388102 738388117
    0x4080403110d0321020d02280806031b040b1201060f0f0503030301090509030f12062d13020f270a080d0c060204050d0309060807020102091c020111062406 68
    0xf0304c102c40c0c402d1805130b040d10702d000a290052005291030404281e9104981254519017124820310040c841401103101c288814844107080c14006c520700321000176070300c60078a50541d00c0064509005900303529150060984030400074104a903088105400c54020903052184010100300684000354450035084a181a03d002a02071481d43c1c0c2881c20103006000064040c83d0544420001414901200e42c05000750101e03040b032000746420204c00700514061007150b11411003104c1c6c00c0e40700b1446101c05140394510400d40303c1504800700305030701700c00070300a201c0003c1d0401d900092203000b804d00c00890308050b9074600502c000200034081030160850081c0110304003a07001c038002080172400345030140005d07032068401620701511000800c03101d4140100803000b0500d10b8005120464002c24061b034859601d100850070000d809000a28810101084c1c84101690080c40004d5911a03400303811007000090884030340d81400070359210000c0241c0f0b038142d05001c1d0441d000050b880d100301180c018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 738390602 1250 738389352 738389357
    0x1a0415030209090a0b100311010e06030406092a0f060c051207020d1202060714030907060503090a0507060c0507050102061902090415120303140f011e0e04080403110d03 74
    0x91800d40d800e01440140c09440d825042c404c03000240c2c0000c1c0e4054115110356501c3c061040c105107540b0304410b07241c540c4041541440000380e000042d5844640540354400c0e049140800c820201d801c00d01e005242c41221010040d080f010100d80030b01d01c03000780d0000ca6010400402c841955040122041e005c44207000707005421607201c031403400b01d070308000e46101800101964007482c4c0d55600c07642c040c0c0d0030070361003400768004108021240c1d402604d440c00d00f81c01d500300d441c85c1d494100b00e1151180e4140c0609010b01c0000f00118490880801c82110100e5200040710241900d888003c0c12240c00c0510880f6103108154020600e0b5102041c000d00402811002c4a0402261807515020703400034600141c00c15551401e00e4015004410510020400428041e40032a020b080041c07e03600400402c0209002940070b000e000b803500c25149044070310300020540e0f00c2445401440b48020076601c25040c000c59001030000303002640009000b140d1280302e43d45003081000703080c0300e031900740544003034007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 738391852 1250 738390602 738390641
    0x109082a0603090d0f09051305190509211204060501080f0304031a090a0f030305061212030a0b0307031406100e16110f16050907110604020409021f031a04 68
    0x901d074004c42c4c4100c22080745e4180401c81b01c1d20b0b480401d80220a40100405850b01c4409119110078004002030300ca8034002028056842c00322140c1d40c1e14100d901c1c0850007010f0811030410540140b40c280c500070102c54144043d642040d05183d00035240a008448a40c0141f01102c2c107000300000031074081369400001c0b04032454180e0701301000c10100030030103202e034069400621300007501c0041c1e0302c0807644246c90004181c18030006014000022030311102071a800392204c070103441069001c2c1c070344c00010440c0104015452102080c03e042e200d5000521002d4030303004046585c132000c0b560720b02c2220499000d92000396500e01d4241103c500b079030034070303c540000c2c40c0140c615885250604604008401182c071540307869000b031031034000c0c0746880840281c01c0c6001488203203041ca055540021035403510903070346440d000030f00f9181e05020f00000d1203555104e51003421500e075000d5421940745c1420807010030040010000d0090815a0340da49454050300c0c0520440303141900c100d18cd4840401d1b054070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 738393102 1250 738391852 738391873
    0x61608090d18080d0f0e010e012708030408030405010e09220203071502060117060f1305150f1f0f030f05070503010203160201150509150109082a060309 67
    0x45081ea24000c042c0906071104101090782c0e8030810101c081c0b80d580743c0d21010030542c440030003000031030448074040c100b10305003000c00d607142e038480441002081d5145820700c40710000e000711100031240e580301084901022600150300e1002001070405c5520a8a400420003e800e0810503616000c0359010714041d41c1104540341e40c3c0040c800c90202c6480a030171214002d807107214003841c024000e010080141d0054006100104441190707021103c8448010400c038282281c0320501c84000074488240d121009501409100041160404401d04041d401e00d40d41401100082501d07000c844072000780e040142008002154490101c04075401000c3c03d042003811031785c03100c00810092400382c5072842034200c042040e9601b8801180210700c4a221103403610b11ba01030190035101c01214025008103c100c0821150b1115000140e100c64a1606002c1000320040143c41607001600050010311a0009542580c005200c1c0e401440c400306410030358110100d400c01140f0301c400c1700c0d8045180c02609080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 738394352 1250 738393102 738393107
    0x15050601030504200d140a0c05030a0b060907030207080a05071407031101050c03040905010608040b070e031b010201180c18060812030402031f02070317040f0809010e04050108061608090d 82
    0x241300422005000315501031194481d03c4000c84110340454164001e075007550200000301c10110002e18056010349040409a03d5035170100302d00508003409003e440340090001840703079040791260b69001e1545a03c0d017018000050507504900d030200c07005e00c0942481d0403142340c0047d842080729805200441c800c252400115210340040c0c5e84550144014400814812520301819000e015075035101c400d00e1030541402410104090004414050401c411030040d40b408149261001002c1540c1c05c90000d20f03e00403801000c607403441c128030042c844003070410031861151080031588200d00001078600c003014414100c490a10074646c09500175400c031840200e03500d02a5500500007000d80300b41c912030040d10720404810801d41e18526500085803001c250b0080c00b4512210460200c840e020300e05540e45124240c0801c40103494400041003e07034980c2c0c401e041c081c1e208140a0410310603940e5588150b5034581d002d8508048071034030881c0400c0341c14810000244203100300001030103c01c14404c0706 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 738395602 1250 738394352 738394403
    0x1180303200c0a2108010e070504090507120c0201020a0c17042105070f05130509010b03071d060405040c2102060c0c0a081609180f15050601030504 65
    0x458001c00042144500d8040303000000d4000200200b01a200f0380801c1d141105016104e0818558503040c84090a2000c03075214218030305440110a0b512416100e201d82030b0782901956000c420420300301010040f409600c041d428800d002d01480910954029410a03801d0b070007111a11000541c2825090011a092822040004031303421511070be0180c03952910300802800d0203003107903100e01652407001003020801c2020010034404030101c80c0b003410800040c0c2070200403a400040340e504c540c040783c042502940407103040180101103d900c03a54448040d0b11454414541c070032600b40030700c00940c071424140501481107a00c540d1000c42e203410f000c0440b041d81c0210f5202d88646080210a1005803100d4000700070030740107003005100440c440400c2144044c00c0360480c402541002041d9541e0198114000c42580c1094030046a504021500503a200c0610000541040100030100b001e010500d8000120f445070400c2c203015a41d503060055094540507107004000c005c9131154480c000090004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 738396852 1250 738395602 738395621
    0x1e1a0604081f0e070602240f0a09151e050108030405100c060204081501090f0c020607030902010c0b07050408070e010f1a091f020705120a0303050712050403021c0201180303 76
    0x200180c48075074844840d142c02903a400a401580c81044a0038094100c0a00329461801e442c540e0381c41c40c5081c1d48442104d40000c0d20f00d03c0d016845400c0001003100c0030124a8810510b0340080045020f07003007600254606400808803305d01c0d150001c90604004812202501c00282030410903aa94000841e5402880381c3e05407a0281d090002003807209041c02007032084025480f5115055041c440c1c0365084807801c900318a0160b240401c561001600030070710079440f0125060004000c0c41c0b41c001600c0044030310b240100b60601ca08200310b40b00360050b02070401da03990b100403280c049840303240c00800d0b960300703008103103195206100402005031128503004400f44101d0710316040c00780304400700e400c200454065491a000c000c40144000b681002664010281100c400c00c5040b52480d101c0e4072070300c178100d020301019110307000103242d1400f4001d10401200d0f0008100998030301410029220a03840c022154108003c1d06410055841402100340141d007442d142c01c03000c0643e541c00c0e0001d09102c2c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 738398102 1250 738396852 738396913
    0xa0311090403090e0901052508011e03020604090203090609120904021b0607110c0f010c02040c031404030203070c05060f3114030706090e04080309011e1a060408 71
    0x9601180c04c12104074014080c1041400208407400c0c000900c00302002c0e80401800e515103d400c0d01c805490f0302161107411500e42e4038500520445000302411908641d8002940000b0005000035401c00603500561180d15244140c481907120844055121f03101441b500c0c61000c01888030210510b800d50080001e203001306030310414481c50407031131030510320110b80105c00f0514840c00d40c146a00c02b400700070040541100c5801d102c0344241d0000e0400000300d000a4042c0ea55003149200316400380e40090f1180440400580c280d03d0f2515000f90f03603a2220314212414070800b80006600d050040a8a400e007000403040341c14180003801710a01c8800c0381c8000d42141002c1e1150140c0c0000da6420329020b0400c5400201c020134000c000c0c035143c00441d03400a010403a41c41307410040b100d140c1d100540c0056102060981d07a0300d8000640d03002d0103070504000e0340d0440076154003280b00d41542c00b80305281441c034481c0c940f46030f07070504102403400755204210498020080c0c001203640c005440d0003d40407070a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 738399352 1250 738398102 738398117
    0x30c050405091e0f07120902060c160f05030105040206030711070e070306030605090f0d140d02121e0f0612030705070f1703091f0302190906030b0a0311090403 70
    0x100000b552210302943c0020885a185110540c5110403802c0c80b0f500001c010740780300003802c0642d00100030101e04600ba420035540d40400703000719580c400841e449048110100d0780d02e51004c2030403000300c2c0f00707500c262210f01a2178a400a41c80c101030040300c0c0300703a4005055604668400d00c00740d50440030701c00c4d00080350040c0c400c04074203541c24400d40f0b0b000d160a035400250b01821071800d941181c80152084489500c0008641070f60302c40082c0340b0b00a003d0038a4050702d205656640f04a1600a45003210321590000c500825250000c0c035032103104d003420003805180e000290b03a904608610a581210360200c02000050007401c1c46003070072020418400891785001c00c5070300e94a003044000e0300f00b40504414802c0400010009148a540d5000d03240003840c070341024080040d81c440c00351124081090009420541c09600a44c1510944054100700c0b126125100b480207000c0800e80c040e0b400401d251070208611800c102030701c00166036000100240c0d203c0c0d20800c07c00a444000d00460070045003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 738400602 1250 738399352 738399359
    0x7030c0b0c01090215091c0b0a1116060b040c03020a080a0c05220e2815080318010324033206011a0307080604090503090612190e0d030c0504 62
    0x4405003040451a174920980c0c840896004110150301c01c2e249001050b810404c06e507004c15003000312150000c9005400103140035a840d0142c035140500c1415006035551040c041040c00050f401161400408071010040404085001c0e8200e000e040c0010300046c1c044400a10b0040070707503100450081c0142800c03810f0124000c0c4401c00f1032100100086104010b400c01c01414031200506c40c0c200e50300c0c103004907500d00d800800c490039041414003210043d4903118541d44650301050104060310f40d60007034036610302e641e80c20800c040c0f807507044443c0000d10744150707007900c5001d812480582013183d80c03420340070038a181c68503c1091161070090507121607183c0c0c0c103601c11801da45003180d801410000380c6090341c0751506141000f2001056041168410010007442c258064070140d0b2002c01210000b44024140c140b0314994090144c006403c0b02c000500d000003c0e0702c000b0100d114030481c8940642818424004805503404d650303184640782d21032680c0d01005c1c0c2c0241c01ca43d141e4180c901c1e1043c145540c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 738401852 1250 738400602 738400609
    0x20d083103022107110d1a07090314010e10020f04120213150e0c0a08010303032d0b0a05032b030920030d03200703140a0e1207030c0b0c010902 63
    0x841c01d8010f9510300203124010050f200c85039201c021000c0f10800c90b80c4080e41c450301061900c3d40240326003501c400000861980c0942c0700d4801854210910404e402041c01c0903600a01c030751000340005215108d20155400d42078005c403a038500a801c0c01600713040c41d0078030342c4002c4071304d401089038001102c850801030440c40d840f45050070003088450702c01d80c0c2d140000b114105080903003000f040b40c4080001c42501c1cae4001c1c00d828112680f5140008a021898800390311800344100c102072440381c100707160107881949401034140e892703003151098040b6a8607400c150b55586c58081a4602c0b80b200311185d000d19115025913000d0441c1410007055001e0b01c1d9445041d0000c6000f03200d41d0941200f600507106060810024590f5030303182c00c0411030440300704500382c2c00d039105411000c10840000340a004140c45407894401d038504103180e0f5074a4403c2400054090410144a2405480b60030b114440c01c8000055010403a40c00540f44c48101d8280609580b0036031051080d46001c3d9200c40c45040144c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 738403102 1250 738401852 738401893
    0x11b03050903060705071203020708120402061603230c0a062a090608010b0c0a0209280e2b0804030311030907140307030506220b0403020d08310302 65
    0xc80e80e8405541b804c1605c0d203120954a000850402c051041c800700c80060806003c4450f00c1581c42100e241c80c1c5c3d074903c000b420610074002c07014010f0350014614410140c102910400702030000014a05d90402c03403030000c216000d14a10b2124030341c0006031403000704072544e214a104400402c00016050b0220310700c50f1400b02441255800a08400800c003d1560b20070030281c05044021201ea02e40741140b042c5680d150402d0340007a01c0383c1c5419011400c000441d03d800c1410219110a00ea8403110201034003008064201c6807509a016440d2103158503100100903488440502c60558011110900c084552034030041045052541e1140140c070290003200c003440c81015141e000b40b15860400c080f800070300c1200b540380e50203940200d10a00c0080c5020407003503841043c0b11044c0071080710044e001800c1d079800c00006814407030903c0501c0140355002c51060105d5280d901c90761500c0d02c6452881119403002003032100c0314190790340b200a03a000b403084900c003d00d00030302c111000807591001402018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 738404352 1250 738403102 738403111
    0x110d0c081005181542190e031f0e100902031b1305010305030901020d020d02030a080c0409061d0709060c0b13050f0307110402090a060c060906050115120b011b0305090306 75
    0x1240d50268600200800720031351340351782c041340d00c9414031420b000500600710080d00d0060038460030480b00c0c0c4140d1010000034010511280740c200300304100c11040300007880320701507409840c05071907154136510300c107809400b01141e07014004001c00c003048081e1350444000c42040f26803005000d43d40500c59021401001d010b0f5024502441d55160440000791034070f18003c0000703055400c000f0000030510b0f0080291303410009030381800501540e891864550f41d00c2550401c40341146042d0000c40c1082e43d010100303c1d2440e0750300503100c0b41e440c0e031401039421154a209810010751114422000a0b181c0c4034099042031610011881600070307a07580500b03080c102040080654808034498040c840046201b413411141a1011450100644d0202302e80a92a00460082c40703d03800d8800104040e5a104440664000c1010081561034001149a2568840c0c94100060421207444030000d110310607200106d105844020a10103029030503c09045506019014414107000d0082c007070710b05100c200e104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 738405602 1250 738404352 738404419
    0xd200603040b070215010605181f02010c020712051002285d0207050102031b120106031d011407020f120409110d0c0810051815 56
    0x5443c04500c001c0c50141c0c005000c03210b81c4a0030004000a81d0000c0840e01907007001c43e148108070300d643d00440c2130b4101001c05507550342d03524214440081c0e17040d803003c032003080558240d612031503603050400050b1488542c00703403050700404080c02a40c40b031540200318040034440b00c8882a1521103030040c1d10190401c1c101c000c510056100d4030030f03051212840030b42e400d00034030211094104c51001030b0707090040c0402101c8100c3c04d400040000c1c02c0c0d050f035082e5441802009650300c4095180c5207010390008d5514003038506031010f80340c1c001e22034013066610070640310880c42c000361310300300048015000b0014690000450001428800c0720203006043e1308024060b00302d030040c240040300a1070403890100c900440e070400702515044000450845080721494000415924104044c0340c1440c410009054030b142d2600d0f582e055110303080b68180e0300c41e4400c204a4414141e0b25001d10075140460039490251444810000b404a540546010581c2c01e003e8003020742649500c3c1c20045c0c0c07003c170a02aa01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 738406852 1250 738405602 738405623
    0x307090302181b2502040603061806050a230903160303151d06042d0e0c030c15070201031d010c0905030f120304110d0b040b0108210a031e021b0c0d20060304 69
    0x2d00460333010b41d030303002800c3c8042042011000c800d1846118002d0b070126032580d4440002c10b000b48001c0081c0d4860005c1d0b101240b64107500d500e0003400400310200041c50784c8d0b5160200003010142e6aa04949410301c0d032501d00103603070b55142044000d1085440300f040011010a41502030780c0d4600e00380002d00101d00c000500c0c1111054200c0c6800a42d514180c86540602000300013611008482d10703103001d50362001ca442d40318501c01a0048d082d804400c0c03102c89080100444004415006100e85001940380c03098803a48034000c1c0758076001701120030350141d801004400320600c40207005640c85409040d402c4040185000043d100d1450340005481018500007031100b400041c020b034134010015000200b0b505c03449552a83c000c841e00c101155031401e0081030409185000b6001000000e9105440144000000e4a444025000130311a6000140219800503c08800290040340524002c2040c3c00900c1180d03100c0100554111810a480d01c0031f011500340303034a904014500542c419881c440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 738408102 1250 738406852 738406901
    0x620011503110a0302030d0c032c1201050403080c070f050703060c080a050417070609050f0303011502070b030a090f17031501080403140307090302181b250204060306 73
    0x35214902c102c1141c82258442010401a50001813482e0008840d0402e00c1d140c2c22542000e03609a0304103086024448003810a020b41c1c07074006042a00e400038111000105007900b402c045003265411039000300451510070100d400460030001400c01640707d030f249448a28603665800c5e080130700981c42110070700d45900800095680040d21568071040b049010001072800303483e0001c0b08464103640d0001600005629001e00042c0d400251445402c00100e812030200030106582c4ca038024480c4401403410041182d6440d4070228501d42141d51411601e4215100c03a80d00e00c00800341d810b0202c680c580345402d001c0000d1000d07040d00d410413014101c0d1030b4036440c050f206c2c2c14000030051607090400100e8801c01001a421000190045c03007452041c5e5125900e903113040d612240c0982010f580988400380b0072060861141035180b01c0c1c501c0701d8407000b550710b28050103081030080341c0d20b403240c035481e040c407120050118000000141c1e00007800862819504d07110b850450b2004100e1052a41c0c5040c41003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 738409352 1250 738408102 738408113
    0xc0c010e010e011b090e04060b030d0f110304050d0b0a2004030201232a070803070204140105030a0b190f02090405010f060c060e03070b0c1909030308010620011503 72
    0x420700c10200b1941c4030080c00301c6007001000e8409900400025120b03d50101f400c2c080258402240000054215040010340303480c0603082200302c6608000180540303503002c00e80c41c0f005c410b540c01c480000d0102c90005025030f588111070b48005110984c41541d078003090401c1c0901040c492800034036003400710395481c1103000060501c2440b80000c1b2540020085292a02d100786007110848520f01e000744a524402c0305900e5441c40ca80d0305c00038085d1051b02404104041c01000501415201702c0d4100400c03110800b588040381400d104e4564590410101000828045941544e00040f02c03410b030f60340320b062081c441c01110300700301440c8110740d4003107025280340c14140710700d9024003090b0b840100c0c2c0601c1c11000501440038200010006912100143c620070310400030340d4a41a032200010210749096090340b001500460038960030803c6604280003c02d006d180881e042d83d41564035070080c2da0070b041c02a5a211003846016a844081290001d5001020301c03e0314189003200f14040e41491540c00e00c0f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 738410602 1250 738409352 738409361
    0x91a040b010b07170c0c0907120506041104030201120f05070903031205090c06182701060807020d050304050f100e0d030b130c05040b040f181a090c0c010e010e01 71
    0x100300280d400c012503408a00722188400003100840c410617607480704401e6032410b0500756030103541c2100a03c000d0103012508907113420900d130b8030514100700c07581d900801c00055811251201060350360800092003d5449002e413003164803400000410072002c007100d040c040359011a02680010141041441096407250f071a520408087c0c42c02d01c03090a100403081d0b100c01100300010b200d03220010303043c18481840102941500c10081c18901810f04e15104070803090b854000b80c1090155480021480e18080d8249030300400c2e00d64002d180000e4242da087d20310b0352010308151110720035030031181e203803900400000410820440d00400d040a0100c0e100345070500c250746003130031716051140b4090961510981181030450030300b4003192a540041c130948a52046401c8055000d20010300810790400c41c1c1c007031038111441d400c5204803441308480e4080c1125404000f8002e81c13809419420340c1841e18545240d00b20400b0144203140c21a00da10171821680d0055401c1c0140e51a00103200507000d0a124 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 738411852 1250 738410602 738410609
    0xf040806180c010207060e01091a0304170c0d030207020607060504050c04150b03241507380406060b0c0606120a0506010e100306060b12060411070f06091a040b01 71
    0xe2041002c80b40010352503d0043c0103030001c200c5040c52451450b842545e491000b84500c00b43d00554a181005411840d0300840d0150b03501f070410350f4800c6401c1254421140d00c01e158402070b20310515009000ca0295000200a0ba440007050003240080340903840b88500451007240202440d04a6006002c11307a6a00701088025410a1a007004400d446008403980401c0e64503074480c00680060403a112604001c594075048016000ca000c203464602d80108003090140f141405a11840300443c80343c06001204224501d41481d141d400b1050712a10081d0440d220707005c0030034181d80b82c462500e43c641140d0341c1c103481907200300c2c113000080c10f003e41d03040710207249640035044800880d200c60341e541c14184600f058440f013140c0003900b95540800b4080c00b465200c00b0902055a071041d5840300c6030020510300c80c040b2206008511185030900c21036015200704080f1505040341d40c1c07605080608012400d8488a44035080800007450341d6045090030b861a12818a06044c21700b81004a468140c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 738413102 1250 738411852 738411901
    0x1303061e0f0b0f06030a061a04061d0d03051c0513020f040501050906060c0f071512090507051215010e071e080411060d06090204050102160e011a0f040806 68
    0x6161079503100d8004818074000140c135129526110300341c181e401803100707a1010303191000d40c505825140108000420403910030342e551401d000d2841c0c1c41c80080d0344400000c1030f884070909901e0740000c0e000c0e81c00b0f80020012060784011756003038288050280d0344222a51038140d0881010001145442d0400c262520010345041046605010100b210410b024107a50704c50303203001c22500380521080000d00d50100220007540c032400d9503100260011815141501e010540420841c9800881d900c0b540c2c24130b80d08200140601031510701841f48001c050b4021420f180107140742c0303802d401d40b04036a89008040c001c40ca411907140c05139000380000f100004c44090f40d844080314021b80759101c0c0c8000d41154000c0f01001d1052000340000d0708038481d41c1e07551080395003800800207902d6040e1340a04115202a000c1c1c44460150060440d0600540c1c0240d10145032044014010078001202e05200c01d02100071291624003030300000012500654403540c43c1e5401102080b140700c501c0b1560200d203000701e1b07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 738414352 1250 738413102 738413111
    0x30106020d05071106030612071d0906070806060f12010f1401020a0345052b0b09030408030403061b11100c140a020708120307020607051303061e0f 65
    0x41c1e45044c40c01e040e141003e84181004800700b5410340c0c03009407160302008082c0455161a6403485980d644204026800c880100044c0004094940218040b031091b4800da44003c000d0b034403401044141c1c1c0080401c841a50001d102d40ea141014241165010340b00e42e02c08000308a1030000b22425001c210080300341103401a1002c2c0340004d82009482103603426008501e18202035045403003c0301d05901c000754200e411910003030b080c0002c032103243c01d06580003502d02080042d2130340317100b159100200c400612080c184486203008503081c02c1000b608034502606880c6003565070424580b0b1500250030070b03200c0542d9030840342d5402032a80860082c508003414011035070313500c806103d522891054046604c3e6a00d85680d80702c1c0703602c60100d82c02c6800395086500d4407002c004900950728009170003110041e01c41c1110050b101038090341502c2c0708a15950007000d0301e655985e021200d98010b40c01c80c280445d0412008400941c00780203404203110745010001e000c2c060540343d94292000224800100c1b840c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 738415602 1250 738414352 738414367
    0x913020f04090c0c06050f060a08010c050d02090301320105090103080403060b0f120f070b071e0c0e0705090f0f03030301150e06070f14070f06110f12030106020d05 72
    0x54000d0780c04507a00310000282c071000c441002d0740c4c91030700f19400034000c624050800003115020034074240584000c0d164001100d03269120203080700e0601710040d010602c240400a00c2c000250000c111034880500003040d0b0340f84a250b0340c0280c0ba0400c0b03103c4505000c1c0c00034500c01d003403421099401404112100d0141d5451034841280910035800702504054503035816031008c0d22051307001c5014040c040c0c00d22082c0d080d024445501d400481e8150003050146000005045007602c040d03901c1190040b074106424541c49403d00125040700c04221151a10f47e0800189200c2003c01e05204200a4643d60b503107148440400c0340c04440944a40c2c030030740708042c0c222aa62400420707a4103541c4002001c1030a00e007100d1098856510082000358055400107101c020800c5859090400f14880c445820740c010b0710704849520340c81d1a00070342807552940c00c0c041100780d104018102411342d00c102903440000d12095501e05222820b01070f020118800401000311686c10000340500c0c284500d4242d06082c80c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 738416852 1250 738415602 738415627
    0x30c0b071409010c0516060f1404030c0e0603101a0103141003060c030b130905060105061204030f0c02031608061e2d0702010f0f110304240e03091302 66
    0x1900350720b0382c10010040c90440030170000f0845c249403441031080c2e100349595900ca008100c2d0300c05244100004035440510100e07c040f81d0190f509903036010401700b207414140007614007240030041502d98140310f8400c11000e802c03824803610000c001d440d002c030740481d01c4101c000f50540e400b40c142070f101110300d1820408103903c00480c00d01601d901c9400803c0509034050220060941d10052541c8440c094014183d070150a42c011001d0381d11450035039202d42c0c2e031107003002654082e03a4401e880703840406d400180003034032601303803407a54003220306101d5002140c0d50040380c0303003911701c0b0b0b03401000c911000b4040c0302844040003019400126120300c1107401130700040032001100b000c0c100350003454910200c02000c5682d140012510740e1818862070081c0b5105800030f003e84201e2000020007454100180f131981441d0003090100c54070040d4a91075511a9658050003407001c041c0c800d05103c40300c04040302e030380f5140140b19040c0a084010358450310f4090030800a144c0440b03c45c009144100040c445002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 738418102 1250 738416852 738416857
    0x71b0e101401021e120c031c05011a0906120108010911040b010c171207170603011109100c02060c030a1106270307060507110d08091b0a12030c0b0714 66
    0x104114010130500407002c80d42c9142c04440c034465030003a2070206601c0070801c0000040d0080ba840211080342e01004185040300b103520a0080300b42c1401c22002c03010019414070b005101c3c0800140c10303c0d10300340c02054112025907080c0c020720410f035103400f20442481040000e038206050101e504101c141d00d1703000042c2143d0781c0054020820020044155480c001c0002510751244814007000d0061405540090002c2c01c00003c645e00a202c010104c0c24a007014805c030722000000b1403c00e89048030a50410011042039500d040400c85602c0f80c200041e220700300500102440d283c000c5803180d802c030b84042c0504a0741c04c2d802c4560f0f40f0901c10003420f0304400d040040d03400d40790303604504030b9600094030600f18030542c100074051904102c00d11020542c08003801e00d40700c0080050b9201541c2000c0b0440d00100252003e142e03540c440713032107011610b050b0410320320000b4005240e010111785d50544240c100c04841c2d4142c01048140d0405000e00410018850f0310a8082c42c080c24680c5000452201d44d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 738419352 1250 738418102 738418123
    0x22030201020f300909040f020a0609030f080c010f0e060603070608191805160e0f04260922060f030c0320280614040506071b0e10140102 60
    0x910750f07200c0100410700346000c807501000060100001d42c070b403034200480480703074540c012030140e07540610020b100d6201d02c6801042d664000d450304041c85494440748000c0d046210107188030755958010200c060380b14420740d2022034498015000301d143c100209400c10709542d201300b003400002030402109550343c40141d600300040369400a489a00c61900b0b441c500c180b001c004040d441540c03200016000e03820000c20803103040003110351035980c1d20715214410040542c1d0080200d00c4850b0101c2d504c00b1034040442008440300c05250410381040e00041110601010040845071040c4050031004030341c0c010007018100c5448070b24005d5246a483c0100b0070940c1c4405031a0000c100c1203c003403c1c1c3c02c01601669048014501c3c4500b494001108003800141e90300010b041c004100000303041809044c00708560410300ca885406d0903d804140045035224800440e82074000c141c02c0e034541c0c859000000007a042e910300c954102c0c5441a0b0b6400b5010351500031070052410703c0c840203400da070b0014641802 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 738420602 1250 738419352 738419413
    0xa021605101218150b0a05101209140703030504050405010603061a090105091e04051005030a081b1e010e1507030f110c010c0201052508070522030201020f 68
    0x38940c00b10760f10352a8210700a00c420004000008411840e820034040c82c00100c0341440420754600410050004a0102502183c054608c0904001c025803002000500a4200c60035419510003d0740c02c050075174000710045a0045800d01c6203040074880c01d40500b07071600341005800e08014090082c130030004811202d4110000b84003089074403483c10340350045006083d01303980c84001580704a41107544840603004d01d1800c0c00203900a803c480008085070000b4025001560242d02c604c00c035075002d0401c590745c0404a005041500c034081200d9009404002c40c00c00e0908070410006003981d42c2c654078848280d000f81128640001610551070700459903041c0012a000c286240101909644001ca89100d8001ca000c1c0006c01041d00b2031041c80c11b099008009554800c1403c0e10706102c2202024052144825504081c602030f40d14582c0145241c14142e0508402d110600d114405812026001c00c000700020401c40d41c040112850071550440a4514502c07140750355400f420190910001c07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 738421852 1250 738420602 738420611
    0x60e010f1523070516030804090c031107110112110d020a020f060f15030708060112020109090c020d17070206190f0207080726030c0d0608030a0216051012 68
    0x24690041001004a041290001c0c10680b15100389401640180d0420740e2203000312a0b5180010b0200c00808003940d83c807075052418507051100c0c000c010101c0e002c0c2c0c08203042c1c0c1c61a442071201c803000e0251000c0c6204a4440880407140c2000410300f0b012140340700c120303d09001104400583d6281940c0121501e80001a201d114000d000c81c60f000d01c07a00e1100160060100f44046c888081c004540700e200841100e00b0401160303030615588441c0d078400d0310813640208005012180100520712076a40c014548808400d44911400c0c088401401c1818096405041070440c10340d0040ba5a810351a210102050b9a02d0503983c065200c0e00e000b400030252031805169203901c0c0e0b4407680002c240c0d0050039411525240c0d180313400610745d4001d4005584200200b1b03e0b40903d00c004a036080031039202003079041d085454102c1000a2500040080c0aa00d0b443d62808a0308606c01c00c05002200503d078010400c448964482d120b00402c642c110500600028401c0c01c8469044451613122007170140c0f0015 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 738423102 1250 738421852 738421889
    0x201090b18010c1a0405060708090a050303010506071110050901021b01020a110622031a040309120501020403120c06050a0b06040509100806010f231e01090e1603060e010f 75
    0xc05036106085006552291800d00092140000e4507621410154961000701d40300d5140c600d035110003c55000300318de4400c01c01405542065805850b1162082c48882c551102090001c1c0c10300350185207070030008001103800413807580d04003c2c129243c03050404404880041100003902ca00b240e200c0904022031104e00d004040c0c031100100c0c2c3c1c0f1880d80407002201a18806c8030203041801500c0251341c1c034050440a4983c00d40305880321b038040e07031b859141d4025a40c94510907506242d1541002d8078255404d02c0000003154031030313045210101ca0743c0c5d100202c82d003603480c0c1213003101c0300508000c1c00d081c43c00320100c070700742c840c9811a010b13900200d07812415940e4550020b5a80c600640002c030403401010000601b04042c0100d040c00d50b00329044c400001340c0584c96442409141120302036001c01003179014a407078400c1d84010082c40c401894035070b209640303c9804101c03803035040c1d49c018503041401400150282c2e25110300d4003c0c0c20040a00da1031549481c0140020074118007880e98880b20424000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 738424352 1250 738423102 738423113
    0x16030213050d110301020d14090d02150705160b0f090c0a140301061203050307080f0c040302010c060e1609151401110f0708070603061215050903160f0201090b18010c 73
    0x42102c40f0000c0095680b941800480c0d0082c1a680c103040401c1661500810803803800420b0200301149254020000362040c424402c6044101601c4c2c9010300108102103403500710031440201a03940100100c071101d050903005801041e2000340f04c1d180c0d9802007070416800340e50b0629003a00301c134401c00c05c400715480c540d000240103006503844039400444001288040680000295220b9405034447c2d6440b0f65a44000100504c01100c4413040c1d080c0801c0188010760081000101480c0108070018842c1c0441002c6ea160a043e0f108494407079003540400c11071201c0713138010340c8026401c400c03031901d8003881d10340d1107200111400e4080b4103008003070024083d801420801c0b102181155401c40384000d0313440d840292580a64010407001906009000c5818046418203102c02503119104440e03105075004407800804c000f5005912a010030405011082e1000481203d01401100540781c00b41c0d591002404848107a80200340c00007041c4010790024552445c44c030351140007030a091144119a2605 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 738425602 1250 738424352 738424373
    0x703020915030105131103030c07030b0403030f020a080405120408060c071707080c0c0405372a090608041101020106030b0c0a0905030f100f060305010e0616030213050d 74
    0x6150305586070138100181c1158001810002a010301e0191158503551024141c40c4c1c42151007030381e442d500010013000041d24000b9940d5000f0301a03e8005121041c8001c020140d920901030a0000340540301032006100051040040d5414028010382c58a8601964151a10310003059501d40345000b00e04201403040e107001e070703d0920304001ca40c681d403181980b0b1310284070b80103e440c6c24820300c10072043c61054241445558010b032801440e03400c081000c5000d40006900c94000349841c0c45404074a501d00340c1c518003038141d0400c405460024a035003071103030000c80750014891210802040350010486c207070f04940e002c1c0d08686c01100015503190340b040141c0c0075115680c001840074103020308000c0c2111400f8040d200c0a2036a0307a94002e2a030f070303c00405544020141000030300350450440d10040d040780740e00001d0103207001c5074046074850b030741e07101c2600315013a44145400c2e5030024001c0000120522504d081c1004803401c0450074514196035085006249000c0c1c540a124440020410300000e0b814 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 738426852 1250 738425602 738425641
    0x40e0708070303090f08060f01090506010c05120a120b06090d060b0a03030504030210020c060a030e0f0d0305040c061103070b040809040f0e01271e0f0303060509010b0c07030209 78
    0x7114040c656034a401801e030800341c403822050303500e052400700740c06d240401e002c6c4c001c140c1401003002e564200700c0a4402440081c2025050000c4c210201001800c24040d150f504000a070304241c0b01d019a10000c5c01200e2403a1540c06030703614100c1c1510706e5a6136202555032040040d80c26a5204550346000d00042240144803548124203a10002c10954030030001c0041e41d20907103980304041c04942c001e0f030799a01c001c019194004000d01402820038400da200212900d4250121443d8480103030750682803c40d400361080002e52120100014030098141c940001c000d9450000c0e5001988c144d61603c9000f0311500411181c1840b02041c02c3c04210320559480941c01442044003041003070300080140406c40d00b4034419401c200b4040854030302c103a4081c51b441e40720000840000307030b1f0795200c24205007040301e103c0e40001d1400c021808141b25554900e5094866100002c419050008104020805038070200d20700004104412140c0000708250007103d5047c0d8800f08151039450218000180540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 738428102 1250 738426852 738426869
    0x9090f0702150906040c23040b03120403060b01080105030607080a090602040b030a0606020d02030a1707260906060a0b1207090801090302061501050310062a060c0806030d0e040e07 79
    0x2c1480b0b4a68008192140660310529401100a690348000403100c0f581c450944158066440003c00f41c1c1041c0d00300c1d00314888000e0603a6072503107404800c246540c01a40081e01d5039540c82c0d82c2d0034029600000c1c0140500003c50041402d460a400008c003c45c000809050900c0d86642000d4104100e0340c059401400c40346080507200d103000c172000342c018209481400014820481070407003031800070080f202030b8400781e60381c0350914014207440440701c4000b030603c4003004070f5804201d05202c0d04031100c103420340e204c1d0003000711818109245c07843c244024080c20311a0fa0303411001c120201c494800c840c005040f40180c0120350303840b202c3c00e50b030300724140d0700036600c5501f05030b0308404065010507220700c0360080100c80c50f48680800b004541e40c1c041150701550383d0068000c188000790041d203005d0741a61502004110004005840b010307900000300049402a4844000522054022040c42c0d40300f2400e6004082c0d044076404000c150217519412140965610444a100800f0500c1400090302c4403c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 738429352 1250 738428102 738428143
    0x20303090a290307020d0c05070801020304030c0c09330305030d091506030519060f1a040c0c0201020c0f01110109080a09080106141023030a1109090f0702 68
    0x801c40070728002402c51a0882080d02c0b114280b400000001c03d5a000702c070706a0041100411413039041e22281c400d40000d071020310502d200021449003d000031032085203c1d0b170b40c000e0501503610b000c51400881c0e801116005040004018108040034004d0804c0130090a406800d100e40d80740040d86640c1c150405840d9000000f41c4450b40c118a410280c1a18801c00a803c0c19504036012041110b030f90b80070040c41600114170320054503c154020b4450180108400206c0a11441c81c54007207507080134400200c000e03000c3c4034009619003841640a100d0042c102a0386011841e40000d44941c0c81c040094400e0030082100d075201d911600b14406210302800003000784e0030050a00c50440c0d080345040ba40000d1070040d01040c4407606000b220101c600012510900344030340c1081140c040f40082070401049000341c0d41e0f081c0403800c0300c800000d684080b01c0403070780c0b401d0120b07240c0281e41502c2502c0080180811001269845078000b407075109602009048180e2601a022800c080641090500e5107118 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 738430602 1250 738429352 738429359
    0xb0a1203020a021302071a07110a02090a0507090b0d060306050705031003080a0207170601030b0907080303040303051b0a080a05070507050304052107140a1a190318050601090f02070203070909020303090a 89
    0x1f6400d6035000d201140c484c1c0e21102c0051590b141d841c0855240250054913980124600c82c04903040346070400d4480c140414a0354841803035650030f070406c0840010098842c1010820b003c4648503c41c2c2048803440c01c00c2c91440d0110004801910a01c0002d08400000030710f8029644203000c0c0c40050102d2801840c551182d10542c0f69941d5020b000a49a05040c00080340d0700000026070f0408450505001e9402c607921a02e064004000042200300d0400c0111009041d240c01d01c2d009141503d1207440d1290745040080303e510489200910000500c070003040b4107c04034400000340e8049584c11900d031881c40346403031038031000010310404807184e500c2111004100c0b4035041c0303a6a50070050070b42d0400b03030565840303100b21071120030b00b41c0d1207848040c1007168031403a0200c5419414910301504020884481700000180e4841100c6015039060b0042070060000c040305008010a984c11302d5819420005240c0010707844120341d00c542445565141401d0f030071910144242e401c20307030004040c075030207554 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 738431852 1250 738430602 738430643
    0x21c060806070f08041e0b04060509100501050607020411070b130b1b300a1d01022110031704080606100f12110c010b0a1203020a02130207 61
    0x46805202032902035000000c00305440b4070b1015500c94550740d00d1031a5511203445803420982c031081d6040c100581100260045182d0700c032102c0c002c0f4802d60300010b141c60300c01600742c00d11030381216112005003844010011a61410b082d5200389804076400a0004507a0022810f02d20412100400e0658550308202a03181c1c01006000703524040c0f200030a141d601c084003448903400713005804c41d102200344686c0c51b01d441421f035000000c0468540c1c40d0105090700c2207910b01c0c903070110b41c1c0781c0007a902c035405014510341050620110003101d100a50a014803c100300600d110441c19070300e1300c4421903001500384c2c85180c940f00021030300103c1c00f0a81650b0030b10b8011060340140101c1605206000110ba41c034100706014900400c03d0b9a103009080421040840c1d141d607101c94aa202c42d40c9403e421552148503400410091140000000b0401d80c003c00b80508403003da8051303c0e078106c054188502203600800d014001d82da040b107503503c02d0000c40454a000b0b004011000e0400f4000040d0940071a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 738433102 1250 738431852 738431861
    0x27010308091f140924030105040c05070b15011829030f15040b03011a1002070e0606030408070b040b070810080312040309030506130201080c0c0d12021c 67
    0x110a0b181e210101240c0000d110381d0715000900d9400003064035044140508400d0007078400b02da0700421003001c040d20440e040c2440401c9000b80300c41c0000000040020707207018890031451280b20708040f401d100c1184c0b22081d64400c002c0c180c021440301242e501e800b984c40383c810b40c1207030482505074405154a401800a50305011107000c0520b4000781104580343c07400c80b060300e22858007024540625916032040e400610404000d4982140e01d40103c7c0009550a01aa220200d00c01c0c0030010703603481c4102007014885103051504255000050140590701540c00c900d54040c1042c1c8429a030f94495181c403020354414044041c1015034204140400c120600f1803450044c4181c3e56485c0d42c42c1c940407450041c00307009120300700d007a60040103045c551032000c0810340c0d8010300900b0a01c404c16542c1d250b0a040050844039071b402602c030080080210340e00041034039013059030b0001c0e160424222408186ea9101d14940d03003c1030000500c101c1c511102d65804580002c1440d210001071100c540d5a24006031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 738434352 1250 738433102 738433117
    0xa0305040915050d11220e102a020a081b12040f050904080d1419051b0c010f1a040f090206071506080a1211060609010527010308 57
    0x807410403064542d44200e50100b10152480101000116026640c4112410541031016500308042c44403032070140190350b140c41103400d1904030106280000b901020304006080c807100100c0391070461225408010070078003d107841890a0038000d9411188401e91800c940741c0c070010110540021182c0e11010f0052100c0d080c02d004504a4840c002c1d000300c90b8509001e60300620041c0c4000b0f00b01000546003001a4a0b01300d4000c140f100d03d80b607003400f084401d80705140d890b5080b4044040074482e252100c0a4813040c0040c0181d82013205080c1000301e0f0310a0ba1550f404508003560200b41c00080a070294000f402d074030341d41c8000704590007140e9004a45820602c004503c55460124079600c001c51600505100507401401c040c6031200ca550780c0c04510f040389a01c0d449040c0e44800110f0079000030040d40e80042c4c090300d81c0c8014402229030041c40e00003040c2c004402604454140020742d15415a802d06449044800070021009c0d80c4094034501e18003800b903200202840d0000050120000050802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 738435602 1250 738434352 738434369
    0x6070809040c020c01120f023c07020901090f0f1407090b0f0919081207020f0303090d0303051305061303080717190b0603100f150e04020c0f0a030504 66
    0xb0466540d01681c5444d82c0310003050120360007280005502c450b992191203030b80e402100060402c04400c2c1c402045a0f03207901018034140311600940403035504621302200305251000c065141c0300c2c1c1e60b408a0089081840703140b04c06601d800c0d602c2218849a001488201031b001e07030400400251003014019200c0596820010070f204c0c03600800d041050208807603d201540305030a182150b444280080703000f1074103141245c0034442e4004110b00720244440a5080044062151030301c0d43c1740100544c5045200c0f80900c01d0b03208212440301d684410900d204001c0d0541800207440c3d540b0600181840b0104100629600604040001944829104080d41802507542125541e500340b0b003580c0c1d02d482d441d000000c2ca0701c1200010841644010306041d01000043c01040e45400e200100d440c07508240d42102500c12401e4081c0101c52280c1061401080c2601c0a1030190b2503941018004418401c60305001e2900001d0048000c10308120b496101482c844c02c40703490401c00e090040507074010b800385030f00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 738436852 1250 738435602 738435611
    0x31501091202280305030703051909080a02041512080c10090b04110a0b0f0d0b010e0604031b080604080d0b041512060b1207050102010f05041a0a0b0607080904 70
    0x20000c1e00304009000681d070190200c01c030030302000c100e8401d00c0c040001c070302000507038100c020000540c1400540b5190b031003501d034aa101e8003c245183e00c188180d660090070480a86000c00c80340c1800284c00b40b013160184e80002e04401c65050a0452510340c0d08200300030502030701e440007088075072401400301c886454142c0d0203a01d0075540102c1940c0c4a258090042c1802c0404074021488489001540400081054150302c5d03850040c490981c010100541000c940803601c151166014000d040e5000401d10301546083c00360713000625a4001c9000240c100c0704424022140d2010751080a405003a01c0e03c00ca801614061130429410b074008460a4030290500380110f03198141070040c026a08804104003540ea030510340d04400b4103181c00000c0e6889500c803421095191603014848010030030751300107031440b40e00384800a402d441311040703001d401301c0c40d000c20000401c020070038220051b02113042403412516451031303400c003034503000400365130250002440d042000301c0b02c1c00030400c040c0240d07020300c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 738438102 1250 738436852 738436859
    0x1118090c070b090309040f0605180907180b040e01060302150406050901050306011e08070f02210a020304030b0106030207061811010305090a08032e060c020913060203150109 76
    0x20105a0540e852040300400780074000000e442c00004590000f0391204490a0962400015003036030a0355401d04030a65559100748007600300404130401c00e81902c0092111030a05c000ca00381e86002070311032808180306490f100380c1039a00035004481002c10007001070200c8120100c40500a2056201c207c0c030401a0081d2100910072420030390381115000d8840c641040000760065690781c0c0700608450402400701a1804035022a038810024010303d0380e180c030424a400e800c081d181b01c88442d24141954007030714043c400e0b0301d03582c600700d07280e8001640d05540f11181d10324140d2850060340c1004140c8045200049000e56150307014041503400741c0740038810f03002d0710743d2200d00164803050041c00600011010312007550207500110703000106c004c220348100500740c40c0d40340207401c107036801151310f100384042501c0381f41144c0d00d14501106103940322092524040e4080d009a10781c100c000d010304070b03050005940c0500c1c0300701004044e810000c19941c4e4178100748101d455000c080c4003d4003058030380f480403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 738439352 1250 738438102 738438109
    0x30109060812090d020a031e03030b01020a0b19060b0d0221010b0304030309080d0c02010b190b0403060e01141e1005011209050106081510050102211602041118 70
    0x15261080d50a440c03d251819010601101c0000c5880c1070340c00c00d5071a24000005419a5072843c904c000c46010b8074499050340c07400406885000240b90304540c4100c1485000c2503102c0400354000703d420f02c9080c804d4a400e03840c1c10152290303030301500c2c1c082c0d000308516094080a8004258030306c0c440e4a000f080092440103d000c1c3c600a010f842c16040c0103000050000340a9805907029a004a10341070401615a41100940740049103410060751501188207180c1807000c05c40d0842030700c07802e644206508201c4480894003442c0f0015110b07179200e90020799075130b1083d40800350142c242000304e50baa1801d0f82c0700c803c0c2a480008061500c140c60800100c0d00b001c5c50040c0305c20b841c416502c1c01410340c440b03c001c1019111219003a10035540e51b1000181400d010000c0401d01070592030501c0043c40c1c280360102a4458640c01641990001c685c20100a1001030150410403000b88050762207042171404a514401c4080e0000d4100b85045600e0488449580203801011081d58140b01491f0507d0f050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 738440602 1250 738439352 738439363
    0x24040e01060219030509060901030e030a0e09221704030c0609080d0e01051b0f0105100f080106061e0e030709020c07060203090d0803061512040c06030207020a090507020309060403080301090608 85
    0x40e0000c1c900740004411403030400020300b042c03235051501040185940600d5415940405007640c0414404002c03e442d904003e200240d01c503030300058019a910b90b40d05503545205145d40000c18140382820540300c5a041c48059402440c0c100450700c907038988540c000340c09842c150103900b01a00c1601512607010b445104000002c0b181a5901810292485507a020385020740d00c00790194040d40888a40c508400d00c1182d100b09a01030b00c40c0c500520384516000e11140c150403020250f4181441489041c0c1c1080030303013405500c54492000e20070407240c0304403119881d4440b266450300402000084c1c600c0141c0141036100401c40544095964844059030740e0310401e014103070029080d004505c0030030740c2130003e07550141010300a4039104241d4010102c440d40403040c815852a410740c18070041c0400d43e00700001402160500710b141800e26000181d6012142c41015412500c40c0e001446261003402641d13807256020b0b044a440700e03203d2408900c1034200740a1703242c01518080c000901102c00092 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 738441852 1250 738440602 738440653
    0x30b0d0c0807170613030e240d06050d08090f0a050402070b0f130302120304030e0607030512010e04080d0c020c0612181603080310030f03020d03050606040f0524040e010602 76
    0x1717455100c00750581e404d4072803c003800551035000782d2000400400850440b02c0702100d60000a085a642d080703a858001210303034541000d40a036100c2d800c603100284080c411110341034000c07108141064102400a5040120341c0c01440e001030000ca044130422280d12151405514111030641481d52280d4500038112114440900180d0206942c6400c0380500030041da005802442c01c4003d05c0c1e05030700400e8650b0702084d0304030001391000494448411b021000c01d809040c0c1c00c0c00c1c0b054281415204c602442c05003131082d0465542c0c0794a40070344503008200305010401e014000b20740301c0d0301d9816008500c1f042219080e0649a8011405c9241c80000c5641405081142002004e0301d0558507075221035080203001d21009440183d001c0040707500da42103905da80340301e030740244a0207021110040580780082c00490050409000030700c101202048130300103889003601c201c00e1840c4c181c01d40d03026150320049410580e2000090200341e01d031526a6060680b542c070740845070214081424202c20203a50712 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 738443102 1250 738441852 738441871
    0xb0d18081b0c0f0411090301060b03040b090d0c060b0310150311060f072003030d09060b01093b040f1403030f0604090201110706050a11010b0d03030b0d0c08071706 72
    0x800f001e540b92a501401800808082c0f090801c401c0e200428211000c03a00980c11004002c0100002c10180010340ca40c0004624080c1141d07001452000d030007119031400041440d5212000c0310015107041040d5403076035042d44014007800b00f4030020421010894081911004114504414981440700443d00444001c0650600c0d1940c6529620b0382e2401039217101c80c40c0001c0d08400052584d0820242034540c0c007800b000603481184d0f142203c100d400c0b0198550500ca88603104000044d008031030105040c401c26200c01d4003081f20300c6171040c8420640001c003e0305022a00f8003040c001b5210300001242e1242c040c80c0c44050725448219035074007080701c02c1c0144451f00c074000f40c080d00303090700701000c0c10f48181080e44125040918690410130150080c8000034401700b0011070310f41d0f100780d040540c48444802001440840c6012418812207568090f00b41519a41c4946403070b158240c1d00100d294001703001e581c026450f90940e50b160400c511920400514400c500c41c40c251000c03c01c81d00400050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 738444352 1250 738443102 738443119
    0x20a020307060305130609080307030e01180b10180b09010e150d020111010e0f070b16060b220c02210a1110022a07080303010b0d18081b0c 61
    0x4400c4014104c018445403032448604041c2d400a0020702030500a1842844065100e160922006003126021520f85c00c1e10703030410070714220340d40042000440c200d07007042c0e010045030f0320010802030000e034541c060300041da55007542c4103ca184e954805c90440c00c04540c01c43da666a81d12030880840381c1a14440d00c41404400300180526049680001e1144103051410422145864840c01c4801c1c04800034410f41080e1000d02c50200c0620191024000c2c2e03130311607410034000810301c00c0700da2503c1d07100900242c0e603089104200e90f82e03505019034958030340c01d01c3ca51155480244001420031440b102d805032281c1104000148010149203508000141c503160811600080c11aa0340e0803c2503001641e0241c3c00c40143c03c110280010b000e013020021803444526000107002021070021996481150080b540c01c2c031011401200701c0c0c0c115404005070310b40b18000740030401d00a01c04074010561010f07410110f1010002803101900c207403c5016180f0303d00168000085451704400c01e04158040e0ba40d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 738445602 1250 738444352 738444359
    0xa1706090303090d030e1c08060f060a0e09180d0c030e0a061b0309180207020a08032118030a030c1e210f0204081e0114060d03020a0c0b0a0f020a020307 67
    0x1030340c0843c100751031010854044a5400c7c124100030661480300c130340000c0a0608000307240c1002e01c0ca006401c01c0c103441d0f0500d06840700000500d44800c21921707912685684022450510b0b030b042680300c994141c4002d0f100b0f1030382880006014070f41d0841c2e084001c5031001d002e900c1e2030b1500e0f050800848000742c48401c0202d035811040c00d0200304010048042c00480c0740040750300c169040c1582d139404140440142d42c0e8035503004104c03018000e68400300d0131758001c1248080390300001c1e24100c2007820b030604540383c41c0c694250003080005801c107a00d42ca4400400e071032080035410303041809900301e251906e0041c4802e95810326a400203000c111804901c803003074a0340c51103403150070b1400701e018000030018900c0040c1901ca42030b07900550102c00d040d03000d10365042c4020030503c0064510a43c0c1c0008101d80e0551050b07509000310010716852003215415046018580240160010282d100c00210101e603114034802c8250340180001b000000c0d460300d0380390300c06400080c0915010741c0081c01404014035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 738446852 1250 738445602 738445607
    0x216080627061006180b090907231e030708070813020a090203010614071e030e06030a06060e010323131a0406050a020424020106050a1706090303090d 66
    0x2402407201c040008400090124200c080c801e59002d92014400c14050310b1800f8402415080c504070510070803001c140040080038014011035030ba11b0402e0310341413419503840e881519500302c80410b030f0810b000d040c0c0040c401c0294a400600107081c0740884100c28100c2c882c00c40619020440d1004041003419000c101c80d94007800d0640da102020481c0150704a84036400b10341f02208a51020544a4000c40140300720354200800905030f0307440449160030131949803562084282c0360484a111072400c9030641007454820311203200e015030050400d956900b400111080200294070030382001814480144090b0342c8680500919440903a07240004e07072082c582801e52200010741500c4c00c1038440751800c40000d20300d03920101c28401c4504240700070319090418000b40e51006000c00442441044140140c142048080e214150300f0307029811074040c0700c44282e0040a40380c01850b440300c040350b000245448541246c40b900c8028905880c002e0f281c8400c2e281d601d0009891408154110184400300140b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 738448102 1250 738446852 738446881
    0x30302031204050f0a03050309011a0d082d1e0c0307020103110415020d1b03091520070311060a0e010c051c030b010215060a06110f15040302160806 65
    0x180202c0540700260b00440320070b46040031030030045000c161f0220401000985c280301d00500709469401902020031800b001a181c1a00400018500c01000c192041d66807803081090308180300412000b9010060500c5c10300f01500415501c2c801c0702d0038414200e00d0010002d0039101c00c000002c0083d03003000b0365a80158080e00f40d01c4203003890800c00307200005038108081c0034100d240b8102d0300503210140b40d0310340085c110080502c0c440107030801c11014400003a48100388004846110544004613141c0c0b0000b11282c07000040c61502c664800300d18034102c1e040c003141c02803c44c0d02ca6151185036416034000e00009000e42c83e4900040340d14110042d030307030354000c00c64a40c0582c030510555080c1002101c55402e100b0301c0009090019590303008407405941c0421040c109118605a000e030b503441c0140008600390f20a000d0f072030070032403ea05508141d030010403018440c1c007450402e689000c851044c0c5039100e034000b02d4040c0c0042c800e40440840110b024280c010a81d140c40000d001b1030303504da86a208450 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 738449352 1250 738448102 738448111
    0x717070212091e030a290618070519030b0109091a01030b01110a0f0c0603020717090303130b120618151f02070e0a0204053304120510060303020312 65
    0x81c450740034a11070b15a820321691700300c02d10483d151961390491814000f030030701c804a000b40913132442d142805440e9594001c142d040060a07035116042e642c0c0c41000300c0707607030003a0f140322548140181d04074144150560040803600b80c00ba0f0710703440c4565a4180a10903140e40040700c0c2e1404000c0d1807074070100e5100b50094508808103050100203619403540d92407900c174030403200350f4210603d00780c0711040026010f8000c0081480e0318041d4103000344e68803030040750281555201d01070080020220b0003600e0500945585c0c2c008012240440d96413040c600780c581d0320120b28400c24002010001e041c0740b134038400c00c0c84c4595644641c3c0707007075a842a046034240d100030b80c5982d40c0210081007802c80c0038101d64400e074013072016501401540b03140040829030300b14090040c42a1394010b00c41401192200d41001c0205a50000780c075031010f205212035600d809011180c4025200c001401080b440303d004440700c641351042045485400e003610a0070201c4185000013801030b04200158500185004140d0390403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 738450602 1250 738449352 738449389
    0x20c010e2b0b07090b090f19051002010506042a0c0f170c150105012a2f01020307080405010c020f04050a1d070303051209010212071707021209 63
    0x310201481140600d4110031802c40d41d006015040115a55000c1c00282c000e16813800c1c9107041010100024030300444514500b4050020758019503183d00010303211200070b180180c03583d42c6040e46003100a0103072000700c030003900640c100107440d80f021080300c071070b06010b4515884101d030408841f001243d015003070342015120700281c410b8401c04202041c10f03e510084005031060380d2041503408090074000912060840d80d00c08200400032641c22481003590200100d054050925440040d07094561000c0c002510b00e442c3c0c018941c1d49440f0384154202181941c0741c1c41d040c88403402004903500d1141442c01031406000340020051540100782c40200c051005003803000010480001c81c007180d4084400d00411900c130500d0600c011102007444135140c0165001e0b2441c1415130324090114481c01c6011500729070f403840042d2454800790f0654251101e41c4089402314106200c00404a6041c02207a020a82c0070354003060403180001526500b5200921955041c4240a02000f1882d080240d20000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 738451852 1250 738450602 738450649
    0x504050912040611070f090501090c031a04020702011b03020c0102060f10050402030405150a0501060306051f110a05011a090f0f0408090d0606090905070f080a060f14070f020d020c010e 81
    0x8080ea0071b6440c140151804880014081d0315000940341030700c1d250b10b11142810b01d44101800c4910000c0c20003840e11009440c0903a40d40418401255901c40702072303000c8044000401c124040580c085490006800d09074201e40868503840d03030f140507c0360103903500c419001c4607400030040ca00b40760f00030319402402201a5281c000c0c0b0fa0070f060032a610b04a80c10811147d5603030040c4502030305403041e03202524003618481d003081d020500d250620182020b001043c403007001c0700064544410084001040e40c8000203024625490242100019580d184240704880c1000000c0040b200b4082e0248242040100442c0644460b103c4502e40d81c8100002a00100911041804207000e4043d1200030000407100040d00f8038075040031800c0c901e698200760070a0351110b0b010420440b00007290f222203a00003000160440003600680002d1101030a01106941c503201005030320b50708440b420080c2100ca8082d6496006084401c0341c5070038501e02c103280822011507205d00d43d418840c101041e04815550f0142 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 738453102 1250 738451852 738451859
    0x10507140c25030203012d0605090103260a0906030506040c1718030c07090608032a03090409030e0a08011e090507050a120339020f19050405091204061107 68
    0x307080d2000d01f0754540011016004240c0020311803c0d00040e000c10781042046042c2c10038002070744041041c8005454500c0141003d091060100702d620506104940c60694482c60220040c004100038815000032919240004001c2e08081c041d440b2100026500d00cdc1000002c902091000900909602c114056104914400010400090244000790402001014070303001c1d12000f92016500b1060050300141b00801d03503200108140d400c0101d440c0c22005c1c00001100c1c030f2614501a980e040e9a00509088402d02411707000245804080c10940d190700b2440d40720303c84242660b80010144004d0f044054009202070031903800003004a10490540e1085562100013500c03d40054018185041e03612810b0810542c026001284000c1d002c2089040d101d164240c07078140c4e100d1a0210708000c1d6603600c01000710b43c0d80d4140e042c41a0030003031815280e4100c0c850b003000d007510300b400b40380d010301e10f40f0022400210001542a9001a030390b02c50501c1c00b81001e60440d102c901c031440038010f6225036007012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 738454352 1250 738453102 738453109
    0x1404060f06110a05030c0124080c011b050709050f09010504020609191203020303012c06270411030d030603080901111204030506150904020a0303030b030717010507140c250302 77
    0x800103100b800f0004248151401c0080800300420b10052803403042341002041140c1c4c001c0380a0807050000d080a2444882c040030242d41d10b2204d080c028058055948082600622603000d24020703c46584006e659995021102c0e00702c7e0300c01e40c0d0280d40403009000c0741509182c024681e0343d180c500e0310201c440c10f580d039003007140510b40c502c0011005608040b0044c4a10402404043c42c0c5a00890707034060b81549040340001c54002c0501b00074028550220411603603171419444280e610700c0003403007403040e143c2414441c04800100d000540309010f10002d62503958402c3c0941d03015281c000d8001854164404010355020f00e40c2032890b0304034011140c8101c204c2c0c5080c1d000c5c000035030040c0301602e80e52030308801c41425041983e01c803610440750b0409000158950003c4002070f6541820001444064031000034501100d90303101008420160f150b0745020707032041d0083d50084107251a102000c8030345010b00d00040c0100003806001d50301640700d00d0311240545420340802d4a410300039004180c0c994010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 738455602 1250 738454352 738454357
    0x10b09151603111c050f1c0b030d0201140a1a0a03111c15050c16050114010602240c041203050c0705030f030714100608071404060f06110a0503 63
    0x2501000940c01400c41d092580002c041c4540d036080001800200d241004891a0114500280c004012010a00b01c120035102c01c00c492061040c1031440002d514034540c4c000103081807001030382c0a401145113141d041401401034549800f00c01c0d450b0481d82e038449182c03400400d5040312800d400005007021403029180e09000d14084c502a6080b21040082d40081c071155804564203c3e20042c250000c070404191758031410309e01c6044042011a0a4a035400201020300400300200e1031000040d00c01010414158403c0280c402d66445140c0c007682d071104107076220300310600c01200c2404180140000b100014201c1588903031640211818183c0f980c0300020b2500d48003030200d002c030310006980c1694100820aa01c001c1c00b0403401401d08100001d45a0748901801200405918102e0074080205030184501161070700c0d1301204022203541c42250f030340d90b00d0141c817a105440268100081c2e55043c14054070056a080030030b0030400d20315003c0b080341e020342110f00c4070341035020703d02c2c0d13400c0001c106000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 738456852 1250 738455602 738455617
    0x30f1c0c020706080c04050904020d020409060e03210603030f0a1112040509090f0d0c030201060e070305180c01021203091005040c0503070905040c03170418140c12010b0915 76
    0x1411480c3c107000c03002e01058005400200c820f44140010800c60340c6080416a1166040d5001b03403e4240ca80b0200307001d4406104020700c43c50404d4a000c00001000001c0d005a02c2070030b000f040b582c001400ba010f84a032040c5e41c0503425030000c000b10a29420a1801064084e000349031002e1000300c02030b84281451501002e9200824000904001500d001304516070403120b000c02a0020710f103201303000ea40c1d07200001c1c4c5a40034007840e039941c0c1c001c5c0740c000c1d400344000305030251000da81d0785003070500140103000850f07039440300510070304103006520000140b00c00c4500040c1c009107032407500c200c11125503400041c0500000d10900e009100c00a80c1e038050140240c0c4140c070000020f9003000308040c00d00d51140c114100d00b40c54031041102041541a072842140e070032215061484e03600d04182150b07440b80b5080344031500a02c2d80041d000740316550042440356411807000f41c1540703c07002903507501e220740d82c2c9032044010440018860021100300030060307000d00502900800d521544140707510340041c0c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 738458102 1250 738456852 738456857
    0xf06090a03152a0c060b191d100303050a05031009090302010905010509010902061909080d0e190b030f0901020904060b0408010b06040b07060b06131e0501030e030f1c0c 74
    0x107031001031040b0700900d0110000c003e8098180c0300e6500c2d40e0040086a0f18100500101e84a4407510116158031380300c81e0381544003424034050903441c1d11603a0452090445804407801c1c40342e0001e000e07119490104400c2e00e601d5a600b901c0c02401d2a400c584a41016207020880c3c2520000040d12441301d00c01c81c004113101c0c1d0000b007018560350600d9821540000d140c582564146426040141d56600071a0030000202c000c814151a00190440701e820301070300404514851620071030f10040c0c0000c0c855100035012142000000307041610705e0380f43c02d5a8420000303001c3c02400490383c0b2036131482d21590b209880381e0005042c805440300103002d40b2459030124150303000004040c06022803c0c040c0da0440c0e0000c0e141030703141c10300c0c2c2036803030f1058442c0134006001d49540d5080310f02c40d50380c0c0c81d0464080d22600400000800e86a5482d4600c414030349144011001e0b5000703000a4550103401520020302202002d541031008001c01c15200354014107102c10403400703103d200940c59446100b800b8030b404490f03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 738459352 1250 738458102 738458111
    0x90f0e0901050c0a090605160204140a05010b0f07033207050f07060504062618061e0a1a0a0b0a08100e04030318052a0405060f06090a0315 61
    0x1502040d00310745001d081c4100f050001c0260400c455004244602180c4c41c91404503a00c04003c40030403a62290113000039406070030540c180144120800c0d01d00d0054804403003c00c041e0342c2e10458420680305000d40a66150750070300101e40800d028060404100402000c1c070388030000e644800030030890080c0c0a0020f0464040351010500c0310030001e8071010700804c4002c1400301e0034988081c2003070049100708420042c06007461402540c0100d0602d460112032541c42d002410b204030304102d0b14048a00d02c0c4940e205050000b00701000d000c000c0300805040b0030a005468450300d80c002c01910301c0a0481e11040c0241d40150001c0d06c03443c1c80b01b0014500a9451911010f04820043c00d40c030000d40290031a280c3d8100a01040302115a02500300340e15040000c1c4001502103110320740d503404c0c80040c08600414280d1418800303007040003500c4070b201c0015640322171200020001125004e841441d00b25000701d80c0d0303040c01d00f032990092840020050840d012155282da410292400c2d0405101c1403c1d01e6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 738460602 1250 738459352 738459361
    0x30c1c0c1806060215010504022d0a0e030c011722062c1218031917041a1b070303020d090e040503091003020c0a080909010801090201020d050901090f0e 67
    0x40b40301e03903005804903101038a101110b00d4450b0700c6030207060180c1481550300003410741003101504500c4000700e11408400b01d111491201907611904241000404201e071400608140d01e80400c910380c9450050b140d684460340c510780840c9200c240180741d985620313884140c4003110390805418821441c4034060116010205240401c00541001101c605035084002e070400704210108404504035403e0300c0c99600c81c003201061519603490780c560b0711341500450344440b410400c071079614401d06014580e2820000118900e498242c031440c4140c050307041940700b0b0038181c00045e00013400d05c240100400c99010140e0082a03040840e107904c00c0700540d02180c031400d010340d0812a494003d29900751980c2041c40c042d2112074803403007800032041c465144542007510032406a8195082c1d41440000c680c901101890888020303401108514412800c1e07030300001c1d51a00500858905550680c064008444044c9090f03030720780c0001c41000d040c884181c00206588812800c008001d1600740103440b400e042 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 738461852 1250 738460602 738460649
    0x9180b010f0e0a0f27110a08061f02010e07060e0d140a0602030907081002070209040209060a1511070f032d0b040b070e01020601050a0b070f08030f01080d0806030c1c0c 74
    0x170084201c1880e0b9007802d280d898005809002c1d180003404030b003000011030740c3d02c0b000510f440502000e0000d10404408101d180c0769815400352880a64040488040b642c9a2a050365020150900b1aa200d20002c103003400042e646c521040340303901c5110485030511155030b82e12003640c0045600d40c0322a40209001c2161120030403038035411280b1280d046141c810542c0100d1070a036401440030b40202d508601244080d143c21649030020201500320000920544c200101104d02040101006104001c2c4c08a9000e444200d50301c2180e03482007a80c40304260010311110380210102c2c4003e8002c02c48521800840c1032014040c1c4201d2140345682c1417031504403000703484541032900d01ca045501c0300d03005002e82e0f142c01c010501034803564042162599650f15000b0005101140010404840031042c002200b0514403258142e9400c002a034070745003030b9280100d03068401220031640c15413040022070013508011090a078071030043c1540310350001c261f40f40c482c000c1e040795110725000013801c000060030b08e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 738463102 1250 738461852 738461909
    0x1b050a08070806010c060209030f0a03180b030f180a050f0a0624052413170f0712080c0a0b01050108061206040212010b1009180b010f0e0a0f 62
    0x1c910b820000305508002c030000b000d03140503c100916465001030014071940d020400c50900350540412101d441e00140350040c20020075030510303102034442d0880420095440d0059070301c02d40e00c00302c4004e01551181c0c0c1500d080200161040313400d004425048001c110140184000800b611004013554541d510341392040707400700c20341350740d804043c03150f0180c1240c030112200045841c122490104990b10103009560200001c03181111840300052113229000740519076000c503003a40b00c0e0481040717107a042140c1c0318180e02a0810345030f000300030188160403000000303a6079a80a0f00c035035402c02120440040c9800500181030704d010661308010401d543c1e0009510b0b5015109840221a101401c0c00c1d942c1c0c0d42e180540700a1188442c2c80140c4e02018095004280c4071070000d1032000300c1483d05101403e403620900030381c045550075581c41f0038070320218065102d110070183c2d202c00c4849007a0320101c801c615643c2c0a541c0c88503161400140414842c610354000c1c05c010038562984150124032000c0d041d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 738464352 1250 738463102 738463111
    0x90409032601140d15090206040f0f0302040e1c180504050108101b0f0c0204180804060e0405040f030507170d022701050a05071407090504020405060301110d0f1b050a08 74
    0x4e81002c40000000b810001101c401c1c80d00c8140701003403090451000072041d0003581c10a45c48401500c1c00068024183e103a000200e9000b0f480c00c004810405e403c0c591202c1194404040c03000d01c882503026190303c1110303071500b081e40c404002d0300300030745480006090724401e03400300c501ca622400d2070108560761031194801c000c4a9441500c442c0913440c10203820030042004070414013b00d034480c4029921203070007400039103540e034403203204c0c20103245032100701034019008950000300511074800c034504003449100c3c062504a040341c001c000f0281c2d02110680e10049048490004c48a0501400c205400c043d090800d010180541c0701c02100d00404001e254841c01e003010105481581403e81e6004801c4030003040003464a9030755078020307040035000021300030b001c0302040c814000002080309a5030f2029008170701c01c8505001c00d480321000c041c2604d00c851502e0700c0551080180345106111a48851a841080c01d0f020940005560300d01808040f03410340741001c1140000e0423450b150f404501280d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 738465602 1250 738464352 738464359
    0x1030308310b0105030606240d0e0d0309031803051002250c1509030b0708061c06060f14011707030902091501080106050307020316080403060c0c0c0602011109040903260114 76
    0x40c00c2309060f509180c24500c0312941000e00c0010781c91007400038a4010705c500240701c0007220040ca6100c200100100004901940081c4080c070700750555400d482c80e0a170071203402000822402412016510082d031128031681c8840c01178141d00141507400016098a03140100001c2c403009240c1001c1a900c2e0002d100c6100811041d00d40500006010040c91a0402c00ca481c0c542e1131591584081085694540c1c03103800c0b00780c0008a0003042180e107400c56007c0d540d59030302c1c000c00e940e81e83d0300f0480c0c24900d003501940420041a07e103014544002d800c507a00c8442ca00c0e0110f02d9544540204035004025101213505010401c044400e9507088526203005002e070b450103524620300003000075102d0140040042d0050407903050032051000200a540c0a9600100c0c1080305406500c40541203c89540701144c0160a03031030005007490040c07240307016410000703100310300d00340e1610100001403074021003c0b400d01030000e03404681035034070b020351071800d0141c032000c0c9400c1c5d4100fa80b400c0d0031507202102c8a10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 738466852 1250 738465602 738465619
    0x1505010338060604080703060b03010f230403030f14041109090712050307080a03020306010e150403081317030a09051c08180907051b0601030308310b0105030606 71
    0x240500010507145108841c504084800c1d218400040e600d0f2140368001c882d103100707014001c400e1180d0341d803111895070001c40c001c200500c00c0c140c1f50b00c143e030200c50010349024000e149000c4078101324034040307611601c41d15001800e80d00d5050410100c0307100350b519204100c802800c100422401898920040078103c17510962071803d00074445e1f561159000d5107002d2421803800e070040020030025189035031f6204420036191120444000c0094000305d820302d00103000400054014200000691101500000303064682030a5440d01602940304010308101c00001d200c00013680d200000c0d50b182d041148030055540d40c5001b0364000e01495840c0c114a11600580b40c065103003004c8a01c4102049510409140c0ca0301c100180584402001401031a001a001000c000d16551311000400f10300340c841ca0f00d0042420700c01181a42d4050034000100030611402c04a5007110501004415452003444503103203d5426490140b00c141d0710b40002c969030600413006202a16051188a0b400081640c2445 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 738468102 1250 738466852 738466913
    0x3171302280b03041e030c0c03111f0219020105120906040c090519110c01110406091a1b030d09081803010b0f0405060102070314031209030307050d020306010c15050103 74
    0x40c24410b0788a102010003641885e00d401c150281c140b0009164200d03d18080c0250f0b40e0500b0131b02607031036210182c03051a240b10f14070800340c00303040c0c0b1089044a5a000f000b0401c0409a61071440329252000e905100003807151041246800101310300c20020304010740070340d007414640384d10b11107866005052058240380400118851800074003906c2c941d00900410202402c2040c40640e00c41c5e0390390084154208030155040311030410050040760f50307d50b0740c0060300e6558044a183d4000c0784c0070036040d01d0020041880247c1c4141521500064031009487c0307400040a0150f00311182c143c400c031901c140c08541c500c40304030014580820140290000e000418000b4001140480610407251203180d651000c501107074400c000b8603001d10b5000c1c1c5144481c500904903542d132500305a030207072482c404040c0025003003c004000c0d0ba0107804251511401d00c8480d200700c101070f4100505040c100428032018801040384166100c14040f42150700041550660a0200411800408040d0071511006845 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 738469352 1250 738468102 738468113
    0x100314190624140112090209073504110102160602070302030c150702041509091407090608150c0d020426030a05040e09010e0a12091203171302280b0304 67
    0x4003d032071002d180c801003403040044107000030840710714082d4100480008028000ea0043c01d6019512001000c42c6190000d2640719214080710000000342c4030311000102e400a219101c40c255941d00500554810410030744c404845080a98422801a0300c074010401c02d505040c1b001401e9100c0c15a0110b06012401c03a000650740b1810100a014a948203444154510507000410260030f401605001000f66414003420034002040c00c40302c5409584c00004107141c240c4110003c0f00c4407038000d0001502240c1e6400c65031400184400316024040144c40c55030103003031008002404244e960107040f048030100810381c4500b58055600c0316841006400c05a54000003a50100c030014030350040182d9a4040d000e000d45400403900c0014410550080100400c01359030080d940e00650321800d02e2965012180810340880b100030b00420103640314030b0b10820702c2d0381046500940390300512140309031643c00300d500069002c0c203d188011321116108882d1405e40b0706000200401ca81042c2141008d441d01c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 738470602 1250 738469352 738469379
    0x90914070804020102122b050f0f0901091a01030311120d020702031203010905010519211b080106061404140603040c1208091008100314190624 63
    0xa50051100000002d002c41e03208000c0b824044812100c59616400c0e43c03031a072004040c1c003a28134880300c602d800c10f8201d69100c901c542441144103542134071083c0c03514100174000e104058452003165403a0211000803840c958100b40035107806121410503503241d03040080000307104000b850140c0e004039181029039201c080076501141414400141c2d0b0300301c1c51001914100040600148603e004000021210190391055040b25001da5200c010842100300050242c5068061103451a05000c00741d4500e20400254040e05031050b001c1c40780d0103009548203074061000d58041e001c1c0b0b0b9102d40c41409000d5014600c1800614015400e60a00b414200c4003000a0b00c2070403618040c150100004042c04419988200103001841800c0c4d402e2a0a00340034031540d00c056011406944c40302d0209550600c58101d60b40b25034503441c0002841815035580d80c6060b060403880c2c4401c1c0c4601c3d600011040c43c001580c000351441107e002402035511a0403800c50702c15002c401a080c901c0074010407400003034015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 738471852 1250 738470602 738470611
    0x30b03060721020c0f030705010b010c0c23030a0f03090f080606100302120907050405070905060d110c0d0507050d0804080301031103011b05070b06040209030a060f02160c0303090914 80
    0xb0742c8641205940c0000240201100c2c001944181c4804188020004c0020070403a80640e000303205440b10340b03005503480b01c3c1100000740507064801d02004000d0a0f640c12810b1030702e000701c0490300c070362408001134600446544269100d6006000700001c040c2c100102c90014040300240c216140e01d013210281e243e000041c0558010940e940045141c030b446681142c0300440e0304006035a141c1800f0313040c559a41c2d5240507080c001c51411000c90b800c18083e0032240101c3e00010100751a00080d0039403032010b002d014070480d9401e001030241030107142003031214a0659045030345031074440e0f48038103209281c0003503030a8a209220941003072001140803101101e042d00e8001158180414400020a0061000104621064000e081c0c0e0150781603001c001084c0c018011070f00c400680e10382400700002c92150781e6070b965140c0d1040b09010001943d81d044030300008000c840048c20a108042c0295142040b050100c0d80b0f911443c200388109030b082121240076200e0540c2c00c101000360490141c441003400340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 738473102 1250 738471852 738471887
    0x150807180b0d0c030f0302010e07050f0f041127060c03090603220c14010f1b06060302060705030c0607080f3103030f0c02010b0a0e2212030b030607 65
    0x4807558540c5440d10329104155001a10003041a0b49041c141c00700d00032074104500550a046d100e00348075400042103001e8a4005051410804071401044001c0410100581d0407a854143c0c5a400912003005002c1103d40c85e0b1202d000340d80c441d000e503203c0005840000e0300c6a40f00f84400d00402c1800001d403541a01d05640690303a9864114405408482680c580000c0604500b0f03020201300100072100100d40c035a810400c50303001d802c001525a000028001000034018810983c40001c440080c0000c80c0d0040c0301c0069400e4490b00030401e103600c480710036101c5600005195410306401c00c54664072603c0c81c50458000d05140d400d082c110301d0007170210108104102c001201c0c1d500101000d80009000d4090700080c00c0b00b602c0d024001d0131040c5000030036180b6200020242a0060240400b5103074000d00204a281c101074420929070006000e075008a540d40c40d00d03241d8040710f40280341c07045014201444180070641001400d40c1c58a018842c0a43c2151043c80101c5404c121a0000a007418 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 738474352 1250 738473102 738473111
    0x3030103120c14030307050715050933180f0a20040f051306060803041a0d060807060203070b0c040305210c010204031a060312180103021303030315080718 68
    0x60621916103c504078040406000c00428898081c0d00040100103d512451052108102481c00781c0100c03401111042c6036900100040702688088070310050350382c100d0b288441c2e000340d10000550000e200468100002001040d11500141c0c0d04000b0b80e00c5020050000700208415903039610303240d42c071000b05400420210040c0708015a1290481035001a00c00c50410aa00c0c1003070751000d100003055426682b00f843c2a00101e10350034040211000d0b20b01e8400d60038071544440c1c9110005602c802d0460061603524840440c00403420300104005046030343c000c40d102e83c041e09209000140c064078806610034104810000106c001c0341e80d19050400211003000001e001c24040c0c000e11403265030b68034552000402008121030b0705010441a0749880c11600039a541e0000d0603510900202c00002118041c06003104011980d4207400d091074061401600340141410042e0204501d500128042511107660a0784640550b407004000d010400c01020070030310700340c2c0400e440101a41144d190725200c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 738475602 1250 738474352 738474377
    0x10e102403082d03040606060914090406060503031b01240e072003070c0e04080306100207050901090605010e030a020604060c020411040603061d0402011e020a0510021801020303010312 81
    0xb2600d01a003021040b0104000440f070100a0344403035881100e00f00c50759031621a0214025128040c1c41c400d1310035100f4500368410509040141c1481e004104850b0107454803800b01d4603860a102502c800086800104094003030742118500752007510200c11b1800c03040c4c00a00420107507481c0704e4402c8500d074041944240c1c6502c00e00301caa0850030035510038280c03038600c60140a601c00100820700580240345030040646c0711141c807201481c0549000d0b10307924060002c40c3c004d180c203451a0007084410300458000303940d242c0204404002c01d038050b031410740d03a0b44010065035070080c0c07204810302c604030098882c1d42056400100180261b00a03c1c0401c03107003040307010464407070380e00c6030f508031410841c410b44851752000d00a000e8021401101520421000c000e03141c2c600c2038079080c0c09180d05840d07841d8201d6603000e10000c100c050590000461142c115030300b003c2076041c0602120713424543d1002da50303407004001a0514200a440f094110f503c1040108042021401d0704000c01c9058903203c1c072013190 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 738476852 1250 738475602 738475627
    0x120507120237020c0a03110f0d20011116140a0b0408010506041127040f05070c03181a091207060306050910030305090f12010e10240308 60
    0x300c4104155451450918401c070b16011014001c0242c141e08440004000500f40200d98525210044c800302d006204481503103001b01403003408000280c9001101c070100d4031601300618024800c160041c104240c403200c3d559200c0c00344086114414006c08041910303030703c04102c0034810300c070b1894080c02405c07941c4015942c0e165280d000b080000e2407192600c3e26000118001c160036a10307e4800d51504007542c02206091058030031346590b003102812a401d040c1c001030100940307240301c02da0143e5180e4400c8402681485a81e005e150700b50f849002014051070050134012000154800d1240000301c03c0013512006001c48044400100e000780d1100b1080c00420141079005c3c40c200071a001d54907000c5500b6034198040c0007110401c950940750340d100d1010100b00440140400740000b00200043c0305079007450040104c480002030302d40400701225442041c2128000f195800c4582c0003610b00003080783c2c0d03a01580ca501262100d45c2d51842608111884a40030180310081c84170001260170300006c032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 738478102 1250 738476852 738476887
    0x301120f020f13020d181e050102130b0a0f0302360612091c0c11010c020604290a0207060c0311060a0c26010504020f07021509011205071202 62
    0x2c20103003400c00c446000e8024100a90440c10894040b0b078a00120041601d006010b01e4681d10703048020a4041044030082c0c500d50b081d4890251115902004401d283c4130310f100e91000100100d0f44a41d45455040b00001c1c0351030071b285684401c060060222001e01482d403040c0c0f017802c0c14110703110001000e01c0b0101182c2c41c003050004607480072002c80c51028202d0700c80010380c8144c1d000410f0700e0485554003468441d5040320380d82680018040500d060000e03006814103c2204014102030040c1d03000303a80000c550754402e40060080c603107454011401654201c5411075154003654040f4108011081c0c000d40e02c164034841c003002c000000b01c0440505025002544055540c44140d95482c80d016030791034050800f40e103610300018031942d07501c1750b030b40e00c1000410325500100401441992804041102075040000010052101001a007005070f030744074009400d01a8841402d500e4203404d6001402c6103405101c00007a00d0706100400050950040000c0c0451806000c01038882801e84000403413034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 738479352 1250 738478102 738478129
    0x12010141308160f1403030105010f0c05030a320d1a1e060c030d0618020c07061110090c05091006480b09010e03031b0c07060c110103020301120f02 65
    0xa184c05c0320103955442c004c402181610400c1c0c8640b81202407034403044641d8003542034090070942081c0810080148a42c0c01740b9400100b0084020120400030010b104088540c507003440e10b1003001039503a09000d190b0190171400c04401c03107649500c1d00217801213000c1550212046105e24803036154111196030318800d503040d403540002200c0d1900888507003003006100900480c00c0301d81c58271940103203014060085070085404000034085044c41c0040c1500c200e0b00d6401c90030000d0040c0c50001007503030480c0c410a00e802d4090aa1041420b1030403091103003007500501300c0c442061f4415401c0c0f0a0a40049412180d1007851000b00c2290307014699151000160044205003240d0403160702d0040c160302a4891801d0713000702c10f8010907444d0380450718200ca082c041c00f19029041400012000c0800ba96620b6402c1301c0c0240341031901800e03120050816509801510108610081c41424001c550102c00214802801c0071441c55041444401c00800030703903001272030700c0080c030041021074480f0b07403207202c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 738480602 1250 738479352 738479363
    0x51f05070b0108060a050c03040f060e03160b01052106010303050a300e01180b040206120f07030f06050901090e1204080c0f03010c0806012010141308160f 68
    0xd03584a040e21034031104166a104d000900341800308500303402c7c0380c04480c045c50740220b00e0f040c600740d19035400028165013413022003180003d03c105200341500e000f5080080307104449030101c940c1480c08100741c01040c9000c01071b03030346548030003600b1303090300040e807141920b80500308141c880b03810540450b1100c26540784010018410340707501081207400e5000c50340707134080294184240560000c03200d00b203950b5a44072200c5004c0040002c40800c032a000225007190019080d945072201213420744041c108203451034a0310704410010131230101c2e85846144880701c0e401c4020301580b0318101c0040d0540006000740c1000d90b69401c0081c28404040200404502c102c61244e5125590b50b0341d0143c4508041100b00d01443c030402c10b23a9000d00c2c0c10300c150031031010380b80c0342d00f645512600b004441c1040728003160b26021300c0540c51540301c030b8410480c134505034559400120324903a000000810f02d0201401c92a8015000134030000004d1116060711810306050145240c0007102e4108030202c8843c0c1e4001800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 738481852 1250 738480602 738480623
    0xf19060f0b03160c0b0105010c0602091908070b03040503040b030a0209041e0e01050603060a270f1a100b1606090b0105100f020d0c11090f10050a051f0507 68
    0x4001a81c400998811901c1c0da1800100d03030074403e81540c0404103c0c000405081e0494014003507580a20040d100381401030000600b03080101d4040350400c610700c3c410031410324211204224861081201b407014004440991b803c60038180d8903295240114041d18000d54000700000c1c64200307192341907a40e1782400a0007072042c0c0545443c070011907000e05100040c824107003880b640b880300d014043d96015800140c001c204560760052040c00411441101c1c0749034140c85980100440e104034000f84610780a510030401e09c00030313884d2164a040052108804444200c000c200a4a00c8000501d084074107400c03000d5503844000200e28103600f01494000c2c501880d2070280001e001d44800c03100d0580d8070960305200d035448102d00c2641c0f1400303e0400c800050748542070002d0500d10a403102c0b903401d407151203d101da2510032800503116900484240c030400d0044000c10491107180d8004400603c0c0030303070340b1200503400c0c40082401d0007080c210910f80c4404080b0791a2410f4450700c1141d4800360448581708 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 738483102 1250 738481852 738481859
    0x5060f13050f06010f05030c0f07080f091e0108042a09021c090b130f0f0b040218010807050103092316060e18040c0b1804050108060f19060f 62
    0x100100400e0300c1c0582d4032040c000000301954002c200e200c03200081e035100e0034210741c2c0722044845150f00091a44035019000c0c020040080c02e20809048464003c1440d507440e4200c40e004e10817680240c807171a100034000c0c41401511a6003200c500c40e0060f800c001202404068080c04884803002000c41e03c22409280c500000c205619502404c5000402d1400ba03048001d420048410f480000002404c018120b101080f41215103901110406200341d0411010f40419201c50080046400382a10b21100003070410003180b4100201c1110f507054940003440a504010741540d13203003500e00805046c10359440c1008c042c0100d61401ca81c00d03054035601c40f003000d48001e4066440b6240321030161b941489510010508901032404031400010281080301c090b84070b614016424207024000f501c01c615000300104155090b04018402d81128070191640f500241c405c1c031040701da05a0001c4480d820103003d208110100500240d0000c880401c492021580008084000d0246600901d4511075034003000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 738484352 1250 738483102 738483139
    0x60906030411030d17010807080606060304210e0108100f09020c0c04060b040503070b030c0a2a08031506120c071e0506070306090e0c240d02030121030503060405060f 73
    0x7a07a000210403003402c891f43c1e903c41856a134445400340500e42d412103000136800c0d040880c0910790041c0136010490b02c98080504c0e00483c0850b40080d400080d124500c05ca07005c2d40c01045143d0440303c45103030381610901d001483c255800d021b0289601380c6130005040c03403070100e041050701d1031404000c00130401182c3c1d40c00d690180b03906c00e2043c0c50007801003010006020a605060702d1141c4401d031916443c049141100b00c40c49841e00050080c1c1c807140ca140d800788064107407c00b40038984074115a6079203081c8465020000004414410300c10241000a4118142d04112991f000403a43d80704503150b000b540b82c02504c005a0740c0c0054030300c11401d0240c0701444000541240210790725102001200c0c1c6444611041d108140c40f40c051543c8503845010030790034080c14a030034021282103411420350f5800b02e201940d601c448002ca001e2500400103200e88108048425041441e810490080034015900541940801041240301d1039407040016019103e035002103a034404010700020307041c900c0401d103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 738485602 1250 738484352 738484367
    0x4031d03300703020a020114190804060e01090c03140f103206130f0c1805030c0a0b0304030c2102010b0f0303040311040216030f021605060906030411030d 68
    0x9101c40c8544050681803403240d4182103500032078241c0d0203011800003580064901801007101400004401c12140d41c084010107a03034556a02c06a840011030b0901d0f060410541e1010750f00705000703034504103580c1d000440e0702054904403a440848030f642110300d014624141381440c911801c150041f0014034140d20a40c0d8003200028014880020194814500540707078002c010810300304018020f03020901910b8548145120b22116250204605004441180954aa022445021524a08a211151005115200c0540300540061031341c90295400512058490322859040d02400408103041c140724624629666030402010010b02c000d031614444115146900000154a44404045180740c900380c2e0390103400c8000c00840c2405d04645031b245e104644411055031140c3e08000000c100c0c460030041e50f05407070083c0c54403d0b0304040c2481c0a030038070a031907018070700b150329403c000d2055a803844c00707845031100150b401075101d6681d4500100d1650034007484071342c54454190404400d9511499 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 738486852 1250 738485602 738485653
    0xd0c0503042901061209231c02191104050403200d020c012601090e0d090803040e0403051c0c0f080402100c0515040302061005030a0b04031d03 63
    0x314984079884504242c050b0702071400000e01000c00b0032004010b20342c42640141c001d136400110000d0381c0c802c9580c410146a4200e0322100c422081c41c41c03040001e606c20310040e003901d000c054050038503000700c4c1c0000b034655118142a00203a26002e840310240200004900702440d000380c0108018105400c0141441c0303c0c90100b80c61202c440322103195440d40106c0c3d105061500c9800030004842803c00550b0017204408145104684402a500c844116940e1250090150120016035010380d12415802c0c040b030311118905000f5070040800240c00000100c2d01116903403040b94070283c1300c0d880d0441d90303446405000d842c5440071a03400c07880080b0b070f40d01c10004550a901d0300c500c410742d0880c06442c5824115006580304044000c0030301118000d55103a00410310030021340b225a074082998642c510f509071000c0c1d0043e400602001003890030000300b80d010701011001483c80c0c5405603034201035400001c00090030045152242221200c50348510209a1002016a5102e20241000396128100070700c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 738488102 1250 738486852 738486863
    0x20a0c12020f01050a0207033509010207051806060d110c010e011808030105100c120203030103021503090318130905030702090604062102030a0c030311060c0a0504090b060d0c050304 80
    0x3002c40d00c0541c0900200e58141da015009040c40501c3c58481580c1c2141408001c42c000140c01c00c01408045884003180140046c044110f40303541109000918002e803e0308000e0040904001d42d040c1074001c42d08683c1e00c8601150341c42d82e505145e1500c2c10262400e04448441980e010501200008040d00700b5603942000c40020002664071010302164010200b0000d42100007c0005001c03174100000c4041c40f0070082d0804616850b0503680f440d01d0410f0501c0d80c90010f0f04084010301c11894032501e410303000928240c40c0c60640c14085c61307444d242d10501015407070507210515800d660303131030381441044480c09400e010003041c503c0f400c1280e126409075608a108411000c0010400c2c5498800c80007902e0a43c4035401c2020401009801885c0e000070717042e42e06d40300f0140c0300d000241e0641841009984240d071100241c16a05541c2c41c64160054000700000c0e00a010b00c840c07241d030000540d01140d40c2c10b50081820b0010102013640740c03103440700500c0c0302c50401e50000203031504500107501541c490b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 738489208 1106 738488102 738488119
    0xd02010302210c1801022823030c07090c02031b1f020406020d140d152c010b0a1409041b020c012a0201050a020a0c1202 53
    0xc0b0b89140082d0f000044200c20f0010f1040802070004080c00203042010a011280a542d140c0d203088650036042071070202d0a000304100c04004100c5440342d81c880710260103960079280c5e0300903403000e4507a0ac0380c0c4400044010007407043e201030700110782c00ba60600a40322141a010100041000000c1c42800c484c154180c000c041c92560b0258201001a03489180c240f01078148030b5049810b506018100800710901d41c1c5080403181d0300384a01c1c4000030560594814021035404607000008800801c000150349040c0e0440d908849908000c00c44107503aa862913442401e2040c02030100001c1c54131040d0701c0b00d1040f2580503000d00070008101250f060141e010703560120b401800351a005030b000c240200850751300031200c0305440321900b161864006042e0440e0b030404014000017410000000303480808280b0070300c4208a403a6001e40200000ba0350b54181511111a044003130b44150500e = true := by decide +kernel

theorem cover : BRFrame.Cov 738309352 738489208 := by
  have h0 := BRFrame.cov_init 738309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 738309352 ≤ n) (h2 : n < 738489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
