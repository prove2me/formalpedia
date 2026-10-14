-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2588
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:09:19.129307+00:00
-- url     : https://prove2.me/submissions/7dafa436-52e3-4597-b4bc-9e59cd9d4635

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 465287769 ≤ n < 465467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 465289019 1250 465287769 465287777
    0x210f0c0c0b0310090f0c0e03010902012111030a0f1d0d26150102060114063c0c0c0d11040f0b060d0203060a0605190f02010f021804061403030d02030408070c15 70
    0x7c400c04609040c09030021079501a1111501c680c91081c4685641c0c01084040c0912981c0d803c030544070001d8140114002d03602164042555006110684100ca403c024504009502c003100c0340c883e00008115840b0980b140e0905001c2c3c15800c0701034010a02000c150709003410024030400220b0880607901d46a03400d0207a085a500343c2c0c940019074071803101182c845c1c0e4000400d01440c0358104500100203100c0d455200d4040907161024014114400c4044601e0300400e0042000410b0660401802003600c50417650640c00b0304090700d40e00b542d80d81491415001350748501c41c0b020a0030103a08050729200d0702404040e42d8420311000040250010b43e059449001c402c413001035040c0c0315000b0380394185150903044c1c101100421080d1001c446030f24206095540b1442e103407814001c644094441100c0c4044a1952400d8440404c0102c400b19080140510321210500c0d400b510300200391080c000c1c55610050b81c9071180c0c00c2c030351502d0058140040180141c50408200364000400142464a440d21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 465290269 1250 465289019 465289037
    0x306020a03021e0f2205040c0f030e03040e06060702040b210c0d11060d27030f1e0c02010909050a060302010206251b210f0c0c0b0310090f0c 62
    0x54400d10030720541013000714505051224541c5561641c82d40c0491001030030340c40d44e0960f9030304040f8040e120b48880440200f9034982200e840708d60140610300080c5000c0c4050b61170542070403012001300f903000c1d05a50003042d02040a03411504c40d035000c8081d00e04018170300c000c980700c0c0070007401891012680a035041d018210510070f25041140e411104d20b54009040c2d00b403921034009110150308102e202c01c0242d500c40007103942105041c01503001201942c60300e0b82e034160301d07420702500303912540b052502048040c02e58a02000481c01400e03002961601d401c008032002c600040310107504070341101c04514980014850001f52540c44001100d200ba02a101655140c401e041b041010901c20350408403c203070242c107d070b540f20f01100046c038100859191100902d41d203c442d186041c0c840c180303000c7d1580c0c40787d640006400c1168209411820b10b0405422481d543e142d0303c03a2010b91044210110f8040b000c500d0400311001c408025000030b42d010041515441c04002c042e02840300391601180c0012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 465291519 1250 465290269 465290317
    0xa20030a0e010302040e1b0403060f091419060e010f0608030a0f3e060711060606040803180d0503130303030f1404030c030e0a030c0f170d180306020a0302 68
    0xf0085c0c034120f0324000c007412895643d029007810810a06003800d091040108808400505c5612601c0f0107510050400146840940f9209008102880c02ea855681c00156251007410020031400303400d44d03000c4400300d00c8107a504400b50141c9481d0382e4010407942440c0000c03514000020103003034034982c55696070400c24081031080d070b900700c80d0905d01882da0a0308000c000311101d814104800301c000a84001880c12003881c440e50403c5410b40f600304c00515400c1c910380d10030750b0030040984c100310200e8907146894030746200d050707403031240344203041045010100c845815542e0003803907407405800034140c0383d40e503c07451341c0d800007886240400c401003403410054040e088440d108241c00f10844468841d05500d60303850560303809401032130071020444d520018000d552500d007841c2000b584207050900d0068200502046180c9142d0002034501941e40811a1000000a40c48542d1031032800e0400e2201c20140d0071100884003500041d010900000348400c0080e030690041881fa1034140044600b00300003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 465292769 1250 465291519 465291521
    0x30e0a060f0203030703020a0c171209010b030a0303091412030a05070c150218040e0706021b0102070e040f05010207150c02161e031403071205040510050a20030a0e0103 74
    0x200c5403035030050b4011310004100c0d90080c0d00a001c446445c1c01e1100006820755242d005620034044a0440408040740e01c0642d418501c1c603c681240400009215406a20010a60f0784d4210300d0003404054440ca2410181720f030f00050010155450340c02e0b607007030040841004546500603101c10204614100000340b095101d012064081580304451407c04100f004490010350007203000310748103010004d113907030a950351482020100003c60340075100c00b07440c200e4080d041800d84c00107111901e480c8820741d0f4a50b039000c50003c081e280c1190344004d10703480d241070050840202f810024100d601c001603100c188100700d650ba120b00c02e044142801544503e0a0880c0c4450343c641c074981503d80f00f1507080c40002c1c0d810405240781e17101c0004a46442e80d4030307162070000c0303606880811480c2e00002541010300003080c107511020340c05820024075161401c00413803034800d59211600200000400d0b8091500d01c605c0c2c0d042d6035841c101c410404400740b45c9810310f031603901411780403010038065440b0f00400d50203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 465294019 1250 465292769 465292787
    0x2030307030e03100c0504060f1209120201140114220507030218190b250f020414010f0603020a03240e06190909020303041706062704062403030e0a06 66
    0x11796540c40c1d08142c1382000035280b0070351030550403051204c084c46000b03205800f4841c0b48600c50160501600408503104040d0844103560f0341c2902000080f80144210840a140d803041c02c14103668400d5400603240f0f4400d10a900016071041440c1411f060112190b45034016050040359180e0800300240c81d141004008090156009451000c85008220586c1c41c03001a01c2d181d40d9034800b03215036208281820010502d600021200c2c18041102d11080d400c2500c42c0e034500c080d10310901740e1954180303254601a5000f5200d1101015000900061224800c0d00120180094030003030120b4806072700840c2d40904036900074000003010020001c0c00514045001003000c0c44441140f1820070b05000c0010090b10707000005a82500c800c10002400c241d224507464480c0418401070105070604008000714080c01200100301101c1440d5007034042414040310a401992000300050154074400314204420440d078444109102109400000c2c140c11415002991004540b600601c40d100c507402d5440f196 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 465295269 1250 465294019 465294041
    0x7050109050f300303011403060705070f1109040f03080708150d020f0603180c0414160e090c070501151409040309080d05070210030b0102101802030307030e0310 71
    0x34005624405080c4180b5090403070301958241401038440d0380c000f02a2070014000383c1c0c4150b20000c0104081403150010004a4204030090b0015090020004215000743c0300040d100802112003981008081d03115005817a4010300131078110b1406040c4005030804115054001c5403201c0d0000c0d00092044007010700c9103601c426101151070580051107070200d00300074100d8000120000b01d041d81d9940b040a1807042c000e83d08402064603035100700d10b05100003540f580c2e00480c00d014a1b40248065442c4159015400b10080080d174440500c00f10340122110800a07001080807080c4681043c07071000070310710715000d10000c1c04580c0d40d4040d1b0640c6a1503912803a8012000820010070525000118030b070014080d1038031a09040e10b60411600704103504610380c0c04941c0c002000c8085040006c40c0054402c0755040c104040205440045e44500d800a080b41080341d072109440e00310701000381591000c41d000b908498850040303107009400d0311140c00146204c1d104068503208454114011088414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 465296519 1250 465295269 465295279
    0x70b1006050d09050c150304020a080d020303010303030506130c0206010609170a02090711010612120302070302060c090117041a0c0a050a0813140c0114040807031b0e01170705010905 80
    0xb80108000004214034078045807140500301a9100554603440d02c418486440350391a5940d04241c4100900c0313030110360020740306800c44256600f02c01d401106072411203400d4200803910350354503800034807031030300182d290724580f491301f8082c02c03440744d000030031394140d403810788075882101d40740c480840500121180584066022842da5401810000720a40c0c20001c84e0800d010b4480c141c010007420340341181c101280d60f07015003d4640c280003ca41500c9210312480c10218a040c180351002911054001c00399131a4440025030840140d21640c0d0354045140044910130150800d8503091007100301c0304803104501400c400210741311004040850342c2d8034115071a40f510308600303510180c42240d401440c80108003a4010000c02090340302d071101c01e000d0280030190010b51406030003d00320552001d0303415040b82c4103000900244400003079940c141c07500811303804d06040b01e0204080c00c2e8400354225140c0328042c480001500b424101d0100c440091444c10b03654503a032902c004598249941c0700d410307400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 465297769 1250 465296519 465296527
    0xc0305070e060708071112100c1d040b01020c06070605010e06010f09091104270e06100b0715020a021e0d0e060d0603020a120b0105030607020303271002070b100605 72
    0x40b40d130030050189511030020b01d04040d206000262000381e1410a028054011841c043c440798918815200c0d14825820030b9a4900c040000d10206411132180f25405581d03203071403459440c1e0080003008060500104400e558a41d80d2a01e180685000c3c42146580c84141c2c011941c82d41c000c414400d8031710f40701d507188920146002600006007034200c280b424a81010403021400314444881c01e10503003019a000c0a0158003140010200e41441407000300a402c00302c203000b180150132076124201d4600b14055a06c490860400701c200c109000e0300c8840052001070801701d40b41d00481c514841480151301032040100c840c0b0343d02c4e296000207910100207100c60100c2d00d01440c007100035244183d11005c0000d1516100c1d404070305401d02d00c1c2c001000081461038a03104001c0ba0700d80d040e0260200360007901442c01c0c1403601a41c4c0b40401741510000c0c04a0409000028070042541da42c07000705082101c51107034000440030006d41c0003650a4aa901500b070000d01e500c2d100400c0f00046a041d561640d2070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 465299019 1250 465297769 465297773
    0x60c0a03173102030d1d01110d1d030106060e01080a05150607030c0f05010f0e0a120c0f06050708041221110403050102030f090d170f06010c080a030c0305070e0607 72
    0x10184940840807a810041c011880150f1001c10045d2040810350311a140c14210b200444850101311501d1181081004034411103403001c08600c4440c10f0070f450808926030040c0c410468048004052000e03050741c60644000340380d5070f000d0941121845c00303803102040f5444181003542501d00403510306d10f1000169840302450304040005105203400fa2900c2d60340100710742e96000c0c0b0380345a4282035446c0d80d154801180040010f1281a42700302c4148014020342105903603507005140101003000901c0002c0b2400c3d024400c6482d40481e0b020f03402882084280b40070750000e4044d05058409640c1100c20452802c03802d40640c00c1c154903858000b46100450f41d201c410080600540c00c240304000300180400800607109001035130040d00e9084070600c0300d1601000d018900701d003c1c40c0b11403c02030075040d4000c2d1a01d80113400d40e0170800e141d558466554441c00141c400404000d4010310b40c0704006000c3c1102a4164041001708060303560602183e02e5200040310090500c0300c0d4140c0c811410040703940 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 465300269 1250 465299019 465299071
    0x20d0c0f0c080105100501030513030c08071a01180b0609091603063303050709030b09011b05030411010f02030405240304080406030c0903030801051c02060c0a0317 72
    0x31840c826000004819202c819a5096410a44000e100c3c00500c1d8401e006568160151560100b80c3d89440d40c0030300c041340c40c020994000c000d03018011040c00120401803041280c0704540201007200c1c21601e559442c0030b0070340105840c804a0b40424036103800d0b09c2481c5407660444e603a50038005e0054280c0d48694101e15a200d4803071020030289542c0d041c0000c0c2e0301d501e10003410140388960300b007080c0070180c0000906c40d8403407030f98910040500e80320030800101e0300408042c059030740010744929070f0361700e00440c0d0340103080d040f040d003085e00103008802c140b44c1da10000440c4690320401e056081e030b03c00700c401502c0c2d0a00fa00d19801c0560002e00052219090018102e200740e09102c4685044040080c0b1981d440e503c2a103042d01d58400c002410700209130507004520810f81185080d004051460310010401d00c010f0003030324418039003560070103030b027140101d221408242c0041203180d0b154030b44070b481070340c0d0324080b0001c80204e003058601500b14000d1000e094030500313100d03d00b0591207020240c480 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 465301519 1250 465300269 465300293
    0x50f0c06270409150605011206260a050a11010e09071d0310090c08060c0307021209010203090411040f05030f0a0f140a0f0605090102130302060906160602030412020d0c 74
    0x250308140e0b42c1c0007510101300104024003624401d6800055024107000005003608124161800851304190f41005102c00fa6404038a40e15181302400c2d0100483c0b1501c18248180044040e08a00c80c83c0c90310801d0042e06c00e09451540c0c400d80b100000105035605101250600301c8107a4007140c4400007201204150080140c1c2c040c400405031031106242d10803a108940c01101c041d05c08142008041c04604401c00429402c0b900315005c103419490302900096075011115949140803c1c0406c001f07040764000c006031007175880010824082c043e520010385165401500c030f03520034041d1100e8001604d003004140b05a100307202d24007601c619a000d032034034403c0906034a000c44540c0380c0002032408895086c80b0b4941c80e43d10444c0b1315190442242070541c26070704040d04000141e441040586031076010f84a03103100b00c1ea4190303011a21100342c240054214003e45036000343e40c80c0b00566910410402e58000c2d8812885100070344080c0b81040e40485c1d40b1400a500da2001c140301c2580d000105030103554403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 465302769 1250 465301519 465301597
    0x1806020c121c0e0a050a0b0c061311060a0c0b072714090c1b03070c061e030507050d0f1d0703081b1c0503040b070216030b13050307050f0c06 62
    0x4401c4559036400490801b070030651020b0f218460104860403000c1041c001203070403505480c0d10040303151045c0c41c0c4640226040103030900c00c040008690301c2181c0664034118200350004400d4829140901001c1c002d14111102c00d803000064080c03140c090300d40030440b0303000d459004030031002c400003250074098a0700c0040c105150445045c13140085400c01a2003076101e00d4400c102850311410070b0b00d8003d60001c42c980000c4140004882d00341160015007241858180e404c0c54003185a0700d5244060343d10b845501201380c4817905150020003210187d401c14841c21030b51003280803007101c0d020845620b9031168000241220b404100b202e000f1001c84103901140c00c0708009851010711203a00501d80e600d003c600c400041303403011040005104c12a040307070f503101c912030000e00001640100780008061450100400170488000400d60002c10076950102e002c0d405011281d035445903040640d51014092000c41d82031082280c1c1c0042810304009446a40790403c1d001030b040c50b52050303d14809a654640c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 465304019 1250 465302769 465302779
    0x70e01031d010912030f060e0f040c0f14130203010e18070b030a06050f0a06050901120e03031f090b1e0103240513090807030f1806020c121c0e 63
    0x41c00c803410038822811403038481e0000000d400c0b0000300203001e0b00c41100402e1005481c2040800c52009050315a650010303008403140c20301d64841c9040700707019000b50840c080d03186140c2c4011030040150900b414200740704407078981d00800f255403a030003030344801d0041401d004090008100c403a24018103400c0121103003800e917801c0c4d640302c0381d205590b504201d903140c1c0d02c40c0e00d0724030810050610784c50396040d417036003690070750b0302607040a0024125200b000c2451341041080d51901d42c0005407507001c2116042942e0580b0707582c2c2818043c07101794030490390740c0c46400c40d04c0c41c10001d9260b48500c500066141c000d0401144145540036046240003150301c1941450340364100d001d554140da003c01c4160a08400d01444140c2c00c10060103002c000801c40c0c42c198030303d04075440c070110302407900783c402c00d0350700d482c020301d22191a020403203111803040c02c3c03000340c14400d03000030500072707000700b08071500400030340c0d8064590305480c002c07503524600c60402c02c10b404902ca01c1900c0092040b80521040240905 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 465305269 1250 465304019 465304061
    0xe060705060903041a0304110f0a0807180605100f080c0c030a0309030206090118080702010507080d0f1b0f11030405030a0b060a120b010e060d0c0611070806070e0103 73
    0x340e450405204403841d800b160030002d010302c0081c99190f106940800f01c51000c2d8103514180d52440021099590380074894411244004041d07a00d8802039005400f41ba030617606684d994400c20316904007030012403071481d400c0080104c0c3c24204621a0403c2c1d0038103a980c0301e0319484010084c3c03000800507010700c03800b900c104481c0d80440e6040004080d4002290b800050050a9040090034800003414004040c1d0600701500c2280724001980c070b0015070050289680d403141340c40117955602ca5000010480b00700861001070807c00e41e4400b4600b4a10014280100c440d129060506501c9083d403030408151844281314009226a0010480c0790601040324649510784000a25180410b10111403580c064400c001e014240000f09800802400401440311003003651101102032050040300011060303040052195034a140f404008a50003008a0400607101c61005000d074501d016446141c0c41018800142c010001440134859010399540b82510b00d5000e004401404c1d230844450442a0995 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 465306519 1250 465305269 465305273
    0x7020a0b190e0c0307080d022d19120305060d1b270b03010b030309091b04030818010f020c100207090204080303191514010c05100c1803050d0e0607 65
    0x700c00c02e950402e16a00409504090f507081500c0e02d5880e805c011401e8101c8648411840d40000e505110340c90102890035000c0b1100000c03002c200e0805c0280515440340150000e0b0b0a8020b484081e0020700440c1c11281d143c608241c15010381c5d03010380c3d0260f00300d0a491000c2d000300769903003c4081c00c40c0c10000d8a240c821381d00c0c0402e03940c00800c02c140700041e14141040085000382e5200319644500243d00900847640a180026140d019200c2e1150181610200160a850b0520901c510010404a82c292070b00e0f268203081c40d5503040030b900c103140c401701c000c00c80001d0f602580101220070b00c0caa00429590f81e03903006100b038030a0050008000d6108003440429034464a0007c0d20140032010000c640328074000701c02e40300340c600b0010410f581c03607e00800c0075000c0000e401d560054a280508600142c501f090040762640141e5102404030700540c004003017202c1c1d06400c01a00990319907100722903481300d40103a00c0b444003140f0008120303601542c0d012165a0103200b400c082120000c000c3382c04c1072525 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 465307769 1250 465306519 465306521
    0x18071505070f0203060c1803070308040603022a070e07080f04060216050111090117040302071a0d0c03050103110406050a0302131e050f0a0e030a0c0c08010c08060f040507020a0b19 79
    0x9484200170748002049594845547c3d0f4050000131000f100201045807542d00d0301c5d607040c800c1c0d005100c1055000180d008950b0248002040c568000341c2c4511400760108050310b0b141d999502072001c000c590303040031a0455126503607850084140d510100c0349520f45988000081d8040201d0750030490341060340c00b0108800380f02e0f265000300300601c200d5a81581800040480c800c04024440343c080230343c103000100307074002002e0303043c0d6507200325103200004a029030005034040e5411400003182003050380c1009652580001d8100d901c0740080000e400340070340c1001f0030f46040340a0181c02000303106082000d4078003c0304060001748500c20024000c00d840e041500c0000552444c084800d84860a00031010003002d006503100c0d1803200100031100c4524403294880c0b01d4814600100840c0200766400d01c10400c099030002e005c00e0008120f03502100d00044d00344601260300a22403103800c1059900b40c101030250034420b140325405440740030010341c0d400150700d0029102840304104a51504011409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 465309019 1250 465307769 465307771
    0x3031125050c18090708030c2503120f020c1c030c0804090510031a101202011422080d0206040308070309080a0507061b020718020c06010e18071505070f020306 70
    0x43c40380f40040e00c4d151140700d16002041c0d20100f100d510400041041d0440400c1452590074610621004070007400c4022945041f1908040c1c01c4049001b4225200c1c0d070400c0000907900c4190302521100401181000f10a041c01d462114000c111000c000000920480d8203011403441440c8040c201501e40c007a001c02c51300b040f1b40c540c4403080c14420034418414400100d030140c3c1941c5034034240d1464011000c20070412a803042407504403210192008580c01560400303090340510004686079100100d01440e1382980365610051401c1986004c0303441d031804034052030b000550340c000f003101e600e455500700e034585001001042050b5841c034598001402600007844c155215607142902c0340c4460400000f2200f90300442c80c080c5007400483c0c281c1c5078010404e44119504012080450380705015450040c0c400c60400f50414010400040342e10708126610600a440c1031a00c0c180300980040003564804840c0101c04146440789840c05104d8441da000b4844180300303e40542a00100e5400b107460640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 465310269 1250 465309019 465309049
    0x504030207030b2d0a0b04050a050711070308031f08030c031e182110150e070e060a14072a1d0405150c030403031125050c 54
    0x101840800030b0118408032540c120760750461840e04a080130030ba2045010f001c201044021003a000003c483c004244e00c103014101001d07105001a01d0544440b000a150803101c10002c6011403e000c403101c0300000d45070301a2a0b00089451650312041c0c02e600700c1d40040404242040c8076108003203203001091001e86400003a48004540314804a100b00f040c0d80854500c28994140a10400140d0f9059200740d0400140c03e840304d1542c041c48014a140c00400d040300c01d4403610800b03200715030b580130a61010382d001c24841e9045040c0d507110352000c070011101340ca0000000e50090444030082c0b81047c0100f00d040e1260500d001050315001c503440558102d0402a2041e0700d4028014201e03d00300101c07400559030b81c0b0300118406003080201950792204002044280045100050400c403040041309801c4007465003944040c0346ca03140034482544100c40450019040540d00b140b1102000182e8000b42c1c08280900c044048004081489800f090340640c0d0030711400700c0002490319084c1010400013 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 465311519 1250 465310269 465310273
    0x27030f07060f2a021903020a150b12070e011202010f0305061903030503070801052b14150103050c010e090105060c01110412031119170f0a08040203060f0f061003020d05040302 77
    0x41c00b8085d041c800500c040e41400840020f0040000e0f5010890450003075121054460391800401000003e05c480d204054004000f0b2500d10f2645030002040c01c22100200908582070b030300c809250b1401c51000c50000d010404a140000031a030090b00090b074480d0000e010101c03d1002c020b641030f55003803650300a0b004980300100340f10000782e003e5126805080e007a43c202c03100ca80104070a22440b8000d10b0524035180809010404102845403141ca0700030300c0078115004124203040081c00e002c401c1c0f004035510b10500d5410801540030b000280040000200040c2c4181c1ca03100610070030354021074072803403555030720f02c00c18034280205006040070345411b000049540040c0c3c0b6000e04806018594645c00e5480050b0800441385012504241541c1c010034250802001a00454140c0503511844042c07500c08901c0480720f41e40700c02807520450089044071a0341c0c54413400210a003008bd18101c28a11000700010f2030b50800e4142d0803d040902c1c0780040c130b0704803052003a50454070142d804800503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 465312769 1250 465311519 465311591
    0x9130807061a090402012a050d180f050d030309061e0b0a0501020303090d0e1906031e02130e1e010e0604060b0a0e040b010c02030627030f07060f 64
    0x1103110700300703402c0429600b0219506040d00060000c01d040b011102941d200f20243c0e40d004c00b00e08000d48240ca41c0101115945003100101800e1042c003405040c2c070710b018411000418041000902c412174001410803410a103040d2030132400f90500395021f440094564960810446c9104184c00000100c81e00c0081c510b45410200941845540d015a0445d0700503c00d20080100101d90601040d06600701030020601c1500410741083e8003c106001c00230f1103090014109030190801c00308038100c140340c0950380d01c8121440c1e08901802ca543c14449054010510980902082d8103410100404070240304281010064960900c02d8110b44e032100078107010b01031142454000c2c00080d101051425007815540840248521031494075284566111511000300e03034001c280c0e041015030081c040c0d0304903291410300810703107040d5601c0086041800c100c03c3c0711041c0011054400c3d101d103849250340750482903203071980500b4421500307000d880c0e610030840c41400c2d45040d500c0605001c1101c1c8440c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 465314019 1250 465312769 465312791
    0xb070c0b1608070c0308010e100b0406030203010906150c0b06040605042d05061c03120c02010209100503090a020904020a0e01060206180109210909110903010506031504020913080706 80
    0x3182c030150400051062074502e4400080c0c21034280c9040d100e8080000f80a0758902d80381c0d5600c00c03015801480781c0c881c0050045006941900214142e803e07d0006110702a500e0f5605144100c1715003202c400074404022050018101c1d2140303507040a070007030020a0141d1030750300240c1251032040c01ca80c0d090b11204c9800b0b85406100005040079000444e080119140c2200800c4004481c420031149442440c3c1c1c00e5802c0500511b452038020000507010000b840c0340c00c4001c1e000303502c40e21090703104000310101d920304244648110ba2180049002804003c80680d092100302c4001503c2207901404a4030007040d1a02000c0c0041c2c02851690300030161814140003891541d83c1154410300d23240d0400f802c40002c10070801000c0c0c0c86018810b503000007040401c004440c030300000d401200c0f4490500e0303040d502c0508070b90044c00b07075900210020002da803224010140d881c041d60032072889800118001401600e03000000c580c1c0845002c82c24200100550740e0403000d54804401200c540f652011180a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 465315269 1250 465314019 465314027
    0x1b030b090c0708070210020115090c0810271b090e0c1201030f063b010524130c080a0b030a031706030109020a03060603050c15070b070c0b16 62
    0x381004a00c4841842c0416503101c03105a44a101400b0340608001d50801e09400c0c400d41c4482111020380c200348020303686074144c0b0000307801ca1a60410004400c80e000c204d0709010420b04404581800100041c941810480e0744010768100c40403004090340c4e44c180c04600c04490007180d40d00c117041d5650002c0c540c207003105030030303185005441200c20800c10301510700420b141c80c8405054039008640d61002c495289000c0000d0460000440e840150350b0105405044180841c0c00c44044069054455803100700a410f080300d404490403885c2c0160707403500c0070503180b08100800c1854809000c8000003d001c0b00040103840140ca05040000c040500300440d24285100759851107004030003a2135001e1150700d00404400004c20040e244242c6500881c2199400b51312040d4881d501802010410703581c2c3c20100000c0099100c05d0381d00e4025810b80745032618010340e80d450010030301d4680a050440d180c48048013070100030005000d01019070034903408030b8440b0344803900c10b180095224040036000b0000030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 465316519 1250 465315269 465315271
    0xf040501140403031202070c090f0606030c0e010e0609010c050609030a1202070503030411041814010605220f0f050a0b0a06030203060105160507030803040516120c03151b030b09 78
    0x1842140c1c00d2100340300180e400708040e91503050f056000342c0ca45600341003071110110aa800a0a200d03e4107491407034003030b0641c02c00803c50b48551420040d0501d00441601c040031401c0c0b00c24000346482c08ad0442d02e26007079000d000c418106140c030300d80b00201da9031401d262000c00d4868450561001c10034801c401d0f800401c0c0810110940d80644c10a0340c0c0e56103040e52400040c0c0001c02c1405040702074a0507840daa071203407802034485260300c0f03901c0201381090f00042080c1451000d0315400c04002244070f003064011091440321059818442d40ca00d104076800804280c4248100c081d2124070300460421f40c2d02550f40202c9810302d00051560b1444200105010180d010b40141801441000482d03a0000c003a45c020304408100c088e0560b1039490414200b0540303410080c5250380110502c0140300c00013514040e40d0100000c940c6106448041075140148402d00041040024103001d00005250700c2c1003107040c4140d84030210714811448203025044640e0f40304480025178406c40b580322441d020000c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 465317769 1250 465316519 465316547
    0x117060603030f0d02030a0e0d0507031106070905010518030604210305100b0702150f031911031302030a020d05010509100b030a020613180203040c051206160903080f040501 76
    0x10343c0f0304011003d42d44254000c0d604e945042c1a40440014508025030304103802c003682410030f40c0d0510303c1041002e442504510000d0740011840c03038600360800c40c0001c019015642541301c03000c01d03502e420011903890b841030040e0904c6542a00c5501e070991410070138240a07174441c03a212400c1e441d0000010303184201461400042505140174030200b400440103400688801034007a9940389050700108828040b8111502844600004c0ca030001c2100c0388061406070500c10304208070002d4004d03201040c0e03400104d0105214200300003107544030120480348e990302880502030f42c141510640028039804203402007910103035101c904020000700c0901ca14071984030082020000086a400443d5440300300c410b0090090b5000104000700442021010008101800e01c00d0a000c03038030140323070000e0341060f10111211220781c18081f401e4030b0f10032038003070512110034010800d0740c2d94249441100f10700344026a01788840210040f0100f44000000c10b50030000d24002c5075550b140500040080f402c030090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 465319019 1250 465317769 465317773
    0xa05033c06011a13061b081c0605030708030414130e0d0206220b1506030705071a0408070231023f0603031902010b010e040209030307080d0b090117060603 68
    0x550b10746011600d0341d1340503141a49405040900000c22500505206000190040001040c40808256404004009454812014080107a44100f850b0b034070700150081083c150030a100030b02528010b03015016484000821000c000321140c004d01c01112218190440c6a401000d403041c40355404001c00c81c1c0107020030000c0706641214552621403074100110050030300302c000c40440c894240c07440c1460709505000b07004a98a051032040a8440e5000744000c841210420801560507a5a000c02611850b08070b01e8a920b483c0c030942c00c00c183c80ba032070b0a800c040c01403a80201c441c1804070440c0c2400c244010700005030748851150507411306405170420100482c00c003c900b500500070105c14080084012034200389039031a00310010b411030103090020300c00a50302151010140360f0540058500001c281c0300c40361440ca016060200364130581081d1a0541e004214036000280c518000f800d54111606000880290400000c0c071007040c2070340080169000500c4d140d5000e8401e1013010342000b42200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 465320269 1250 465319019 465319027
    0x5010b0d061401141b16030312020906030a1d030d020d0b0a0b0a180302221802060927090f0d030b0a030b13121d0a05033c06011a 57
    0x200092980c0c10418a4001074038000c116203001750f07005030b07000d1510100f0f001582c1301c040c40c40b518880151104e1100b600011440b034010f4030a18030a100f195004c180c0502118a155160034001020b00f10001c2c0c4103044543c80c0c2c10039900040d06001400c1c280208060146e0b481701a26006429201c804840c0c900c500041c5208010300c0480318200c81880c0d9007030400200c3e903141401c400e41ca40740107170700c065003140754804c2010b240760340501c2500070007541040c00c00007595001406c0205049803040250815010804600146803c68041000c804071000d400441c082c1c0500e180504902562000c0c06940310ba203401402640600140a900800345130410004040760009614a1407620002e07040b20003003400b0504c141c81040b0b080e01603e41102404400d100c40d28001451003c0a0710352901c801e040a0030292241340072420601206d00050040c0803180e9034210260f81228030440c4200c260b41c028500580b4a0305036540943c0d40c0c60703040050300d115032602080000048500b0392100340d60314100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 465321519 1250 465320269 465320309
    0x18030306060315150a02010f0c0f0c17040b0403080705060f0f04110a1d010509010f05010903330f0f0207080304030806131d0715080c0a1205010b0d06 66
    0x949901008520b84035a0b054486400704114001d44035410003d9200000e4a010b170310b405402100107040781c4541000418103104088454113030101030038001400da28114008190003624598002c5220750405107041da445011002d03540c0300d548100c07000c0d640070801e0024000e00b4426680c1c080e2202c0460a498900304c1003441d0f08e01d80c0140001c04141e42e44a40b8460358440c0041200038104110f031000a62500c0070748151912800d109244c410800d24002007114110b00c0301840441d88180c485040e81c906568541100d440c180112550b0507042003450298003040c64480d060b448103580c80046c6008201c0800c030140c036407a440700c0d805d41c1e004208900003e85401c04690703205400d450714182c0d41d181c050028a00300301890400d1250b41c1402c0c0c804a10340d081381a02e0034030110460440b4004e0340d0b01c074045184c49080d6078000010800000004410240800c000c0100617102e241c010305003180e0020b848102d61080e004900c40c0300d004030313920035044001d22a0601800c136802403055481c40d15 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 465322769 1250 465321519 465321529
    0xe16051305101a04032f100c0303020d11040e040b061507031d040f0234030f0c0515090c04110d0b0409060c23070b040b060d0501050a020318030306 65
    0x7a104042c0608050201c1d04a0980401c3c19a005990b115420800c40d0700d05100c0d541c0981444410144040301d1402559031504d40f626008544032215140c0c08810074250314203800079002a101091215215208101c1d1448040000d001900d0001c030541014145401c159400b0f4500502c11400340120007092500700d14207400b581c0004d40d00d40f0b13001c5074a04444416003004000302e202c150f00981459002d99104003660080d2100341039212414a0641e08814034444186006e034040d003000c01d103d44d0035800309105081e0454800f01c103007400c0c80310320345903601c0c58a031401c0310b00d1070140903680e42d0500c81000b80912100802c01d4003280c1c180103c070700d0240300d4019031042c1d880724401c05907244101d0032f980d104c941222500300c0d0440010080300034028400351650300d1480450034000c10710814051081200020784900715044800509259955a103100d0a2003000d4041c036408140c030f44c400000500d090040358450f501c0303484050303164200b400c2c014421544945494103190420310802506481e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 465324019 1250 465322769 465322801
    0x3240f0402070813030c050f0301092a0305060408030601260c0904060f0b07020a0b030903030106140702031009030801091a1314100612051909060e16051305 69
    0x104540040c2d907141e5502d0035081c18882d60544050644141400005010200041108464007035236031600d42440344040608950302000b004090140000c1c03241300ca03030708101e07864000b03020382c83c503043c440c80e12038948901c1d03c0307012102201e20308070000800c0300c10b50b44070300125004001c04003120a03424508000c0030700c1d00b000410b251001200407a0032034440e600c0b80c00c40d0008007409034030200c8043c0c43c0c082144996200c4901a4080d06801200050007407030281200d12400e03c030005141141d00b0050b0466580190102c000301170380052080d00c0141e50240a1021401c6a9110001d103d120a2501038051401640915809440e0606401034071a1a010880d0a4a81219a80711003100103080400502949120204502d500010800c0542840c4440d0703003500d0258440c1c28813504d0110501050700d070121740c04445c0407040603400c0c9081c400741c3c11034120103100704008950002c103061980e14021005413548080a400f500c108001e081050301d00d0008003003900e05000c546040454a41e12442c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 465325269 1250 465324019 465324049
    0xb0c0c0906031c05030a1503020321070215030901060b0903070512030c0105010b030f01050a060504060507020a03140309210a03050a05040b03010e010521060112060e070b0324 77
    0x5900001c009650520100205031444121145010b40c4504000c0c035076001146c00c0506a4030381411291143c1c41c04c8242000c8a5000700280310041003002400c02e0300d5607650f03038000304003c14851040180e030f40c0040b0b1620400201071481d1640b921500550a41d0400d50004d030300d030002008408031603140800c20360152142641d060b06524440c0505130f14510420070356036519440c02001154801d011002180100f415a8103070540341d072604200425801c4034417440700400c004100421455002d0400782001c0c0d07000803c1c0e0b00c0301940e40c1c2c85a4858000b40e14145015030800100c0010030b141220041001051020949900030400070720140d1703501040310040d0a00c0350200b90380d001c0714803031000c6501924010603100c0c0c8a50751400341c1c1c040d180083c01001e105aa605498400001e90003030000203000c0600001d010316440d025074401200c0e549a41515002c2d01c80300000b20881c801c109400081080800c4180d880c640ba403640022141e1200d81c6503000980b4806a005999541600b118105 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 465326519 1250 465325269 465325279
    0xd0c080f01030b0c0c031905070302060f0717064509210708040306060303110604030f080c040f0308040e0906090a060b01121503030201110406090b0901090518040c0b0c0c 75
    0x30030006417092944c019400100e21104a04404001071648480500a4184240c0850b0010f40701d013549a448554210350080c000360401988003816881c20041980103000a0f2140c0002d81c107680c0c24001c07015080d010303c10502c036104540c050035441e60301440b42c98100318490445908010501c50b407030f43c0c40c009650b03040c40d40c0c2030810010000d81600311841c4c90ba12100082d580c035928a011005802e192000303030040303009031081c200f0710200402c43d24855a03042da074a80031083e03c00401c4e1410310000c0e140798a02a410300021442a51102e203400c040c5004680d42034841e443d2841f045c0c0740100007881c911035600180240180c1c4da00000d030500045034018008070707018844200407140f19882c100810012410301c0c44070701542040043c1c42c029607000360700900c02500601741c5924540f0071481800005402c030a400c0003051130140103000310b60014540622102d40d0f03180026500c00140e0441c0c0081c5e400c1070280030410003501d01000080814807a10b80c28000c1c1000300d280c41d4421081414010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 465327769 1250 465326519 465326527
    0x52d0c0105161e1505070302250311010204060206010f06090f091a040c0e010215070f0819051609140a0b0d110406030f142205010e01020d0c080f01030b0c 68
    0x1808041c4000c0003200e034500c00422000e5400c0020707070300d081e51106004c1e03035140c01d0104e64154824004c40d207044040881624007154290304c200c00b500e000c0e1780f05804000560340e000d21754282c203000810041c20705a000300b18a5040415150403200f00e50700032030a1125100040084008401c09081118415100001c0c04010005180c00031104c1f642d00960161400c1e2101803d01c2d000240300360401c03020f9085503a11a4030300b58204410000ba5145400314690345a00440e8511400302264415842c56024034564a8640c200040d80e000760f44e10304c0c2043c152422106041d90004002d00140500680c800300040e00381c01041040365180121082d042000500b0381000b905500300031540c44041e451295210f98a0718000c00401ca504a0102e4036400d040d2140012010008401d0240c0d0710030b01c640b01240140d80c080d1071031b010038000468065407140085a0043c0080c0f02404002214100200e4801d600d1701e002060a0402040080d288003100018408103940000580e840500c00c5d00896035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 465329019 1250 465327769 465327773
    0xe1917090120070801150e180c04020906162d1a06031903020d0e18010506090a080105010f0e07020114061c0209010902120c0406020c041503052d0c010516 68
    0x1006044c3d0030102044d070030078026000500d50705501e0000c5924520081d200e589900700c04c2c00032980380017941d0b00143d02c1020f020b5074030b28256006101000c0014201d138500703240c0e208081c0c035010381100c1c1078414001400041440c042415071a8411b94034400758425204500e40e12010080203151110381c408a91310002691600d08001211550158138032030700420750140f50080d9204c1d000700702100044c484446111160622800807003400501e1000e900541e802c0c5000d106441c0c011840881d07003d42e50b500c001810b003400b88a0036001c0d202144409a00c1030400c915148080c0e400b80c038a004580c9449404018182c2d0710035003a8010b8000c0b6012031042c442010201c000980702d0390040d5114100d02c7c00003d1700a0030358001c0051448241466101d91b4400b00c410001e40150701c070b07a00240e0010110b0340903601e050351201405c4541d0b14502a20740340c4a8460324680700c9010710100f080030b110b450204011042e606851a15040400205407400103603000910034002d082034482d07404151040141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 465330269 1250 465329019 465329023
    0xa032a05030c0c0301060b041802030a02190207091a030d0f09170604140609060403271203091401020705040e0c100f0305010e01050f0f01030e1917090120 68
    0x1000603084401c490700e40701000072807900d40c101c540e03005110b0340c45c0080010b079404640043d20304803900c030f50003d231030b0201110805000c2e61004250b0088980e08101100580070300581614050070030354002c018007400c140500048600100241c481080c010f03c080c0b909980004448130072100b20301e0710f81c00c1c8000707200303080e030707000c2c2c8036401031040c00c0c082c0030101d500c004000900718401c43c000c4050320024180485a19124030082d15000d480f50090400600402d004101054402d00308165801d284540744030b00c5503401415401800c2c100c00b45050794024903510800b00d0001d002e04002000780c030380c40e00c070020750b84071024030030329000301c0d220707120342e6141d900501601010304000ba00050080340d18010051030302d50110760786d030040b0385848008140d110f1902d07600750581d0030181c0541360105900081005d01040c80201a042545603600d100c072850040c4428000c185100495075451080b0746410508550700d81400041040140301454142c0e900c0300c0450801c211003030700800c200700d030422054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 465331519 1250 465330269 465330347
    0x130201030c140a030c14070c060507111507030e0f0604090f14040b061002010501050604090932100b0603040f050f07120c080c010e0f0303040302180108010c020a03 72
    0x30020100f00e0800158050b08840c00203100d950b50b504041c52034001002040c0940d00010308840240f003420300032540140000c101c042d0140c00c01601112034000090310390f45100f440901d00900101f41d5074205500919035141d10300045501071012030b01900411005e010714440c6a10700c5072250b112440c1e10b60554041c03594810701101450b00e51410382002107030008141c40c8030380079000350400240e8003441840b0f154140c81008000501d0546059000c0020700b404400a440c010400c10b6002c003030f410700b0720560303224002c500b66030403150b686109418200759120101c0e070041c500b032002c4a082507850390201c9500660201308081100c816040a40c5440d070100d110038124451040c000c80d0700c0c0e842c10110300006101d210124045611958551388500d04644090702185140e803070303a603262900f1308030100c18540c05411039041564940000c0e4152400e41058000d8454440050004241c207019602003210503000a01c180031007680c00910b0841d40d00c0d14030303140140020462400c07512002ea44 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 465332769 1250 465331519 465331547
    0xc0c0d1d03030d0501061403010f0b070312020c0f010605060a020601121a09060603010f090f061e020a09090609092001170a140106020f030a050d020403050a2108130201030c 76
    0x42e40c542c00e10180d6880100428041c013400324070141c000310381011031a002c0701e0581e48018004c00c040351900c410050b441d003107000102e060003559099030004d500c4a00c05401c1d00192113009107001c14890506c9400c42d8038581000d0701a080410420600e02c0d0000317031641c1181c5d4a0b540090708030205007031400c03d1144070a001c00e02614000c040c02420803000441ea401340c0400c900800c0884004400d000c11280d5200004104011390b0b00154007140003540300481e100003050040c00750007002200301e401c0785c0c041c10800010900000b030a00800c8418400c0074083d040802042000e6003403500d50700e41805400300f804c030052101c04e5001040744d11a055290f000010003e480c0c1d56801c1042c400c10181a448a4210320703903204400000d8054400208030380b0001d49003015500c3d0a00d5070404a807598064491544950340030003001000036400c2000600190017810380010034103080200060300305051064200308000c1c001488681e943c25a09041c03d685e09080000e45d12855000c1a42c2c4001c0c04070340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 465334019 1250 465332769 465332773
    0x3020405070801170a0c050d0f05011d060903030c040302060f09040501090e010f060515130b070302070e0112050c010516060912020d020a200109090911090c0c0d1d03 73
    0xe000546400c00b000a040c0c1c1c1d240c1c048940010046540c55540350104000500503c40c000c00c20849400c0a03049039013481d00941c40e042c4130207031030b4a6080c00e44001070007095504031003c4100440709002c0c8941c0f50010192400307036142d820000402c41403400f0b20301029203c1c01000a0350012090141d044405400d000b03070081c020341d079503080c20a0042002c016000180e5003440310359010b0300c07254400e0170251400104040c00c45520040240301c2d40c0c000601481031103e07615004103591a00e5406007031140d20a500410030f031402d22043c4074002c80d041e40f0507410700c0700c560b82d120005403000c542c0308a414070a180850b2070b280f0700506586160b0030614060085403a108200003442401248010a0ed403030f41c080782c100301c0c0b00c000c0132696100035420203010a0740b02c1c030003001880c10584000c480180140b4245240a86031170500d000c44080201c121801c0c902e441e02180e441c00e0114813140d1024010071810b06048081e40c0031616224098019000c009540a1081d12440690607005201001400b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 465335269 1250 465334019 465334021
    0x30c1a04170106090605061218120c03090a08210a1403070f02010501060c0809040908040e0c030109060e0103080a080702010615020a02030114040f11060d050f150102010213050f060403020405 84
    0x1000d0703402404035008803c1914100900828070f814003030121943c1c0700d01c0040b5161196614409540348038140c000d144014042c2d48448840d440c2c601d8040c1400c4545840607554988105c02000469140c80e8480802038000094100950969500711020b0100d41d8510954030075a80c5001c4400100c006200704a4941c04030501500c2a4081c1003020120030030b40080100d81d885950a99491013148001441c429042042c02c01c2030405400c280103981c81343c200340e07003003a44a00742080d407130b0030880b000d448000003c001080b64487c540108801000c010705070344813a5056072034080700c900c1080f0311101841440f00c04607488510075400365000706009080800400700504009450b4108501c081e48079600348203050007006004050540110b50003080700c810140345c0e40e2103000800702c1c100702641c4200d09206101c4013500c6400b0300c40c858010360181615601c0d140d08440c0e400c40d1034080690443e0703c1400301600c100d46480c460801e94400b00c91020300c9014820000c1c25034491a04004d41242c1010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 465336519 1250 465335269 465335309
    0xc09090c090a17100b04020d02040324050c07020d02010e0a080d02060f070e10180b1218030412020a1203030b01090614030a0b040e010c081609030c1a04 67
    0x60160220070021101c6010065a60070107003502d0a0f80f0707900c100c140c0c1004140e00c03881215035202240409010b00094100040300203032804a0300180d10584d000d24900c452a0510064840301540d510106c0c10304200d18140300d06000d040e8080d200000703006103070a511481c01d41e8002c80f05085c0b00070004181100040c2c0754090785440700d0403142004091b00c0344002044002d031014401a214000942e503891034040c3c0101040303030700b046528002c800e10202034000200d03500c0458445c4090300c04002c015950b01e01d2001c242810300f000400e50300c01e00c1850b42c000640d501d4003100322070031070f00808504401480c40b4000110301c100302d5480822040089803680c0f04040c0c00d41c0202041b213009886504c002c0d961904251503400b200340c02c1480c0a4810400100008140d500101d0030440203080001c581445009041c00c45801228010101d9111000c02035110304113464030302c050115250102c4250700e141d4072100c00040134041c80b022104040c4004808400c04019034005040700c220f09000c1d54484 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 465337769 1250 465336519 465336541
    0x9040f050a0f0c0801120210050d020c0d1103091f0207090510141c08030c160c03020406290a1107091512211b0309051201060605120c0909 61
    0x610040c00b03141c1007260505010340581c0d00541203c60140d80c0707241c10444e507801c02c200b06140880580078000113105542952180e44003800c3d00152890007040c19028184c0041c1c00604c8c0c8100d2002c1540c820090086240c440c188000944400c21440c00110504540d09a007003840300d810501420780380c00100700d0f09911462020342160408031009802c10305030300900907000c03441d500c2001c04110441c0050001911134004580c80001d41c0c40c02400c0510304844295400b14616046d6030300031401c074040c020b51802d40316400c003e01e00b02d208000c2204600038080c044201450490124400115658030703150b006520030001e2610000030382d140d49890380b414100402da600106030341c151440d0804540042c50020342c0602a0300b07c01c001e00c2d000303040031441c07102d4001e00c4402c03420414504862032159103043c81240f03001d80b00e515007120003400d010500403070345000d052040403030b0304080d8100902a0481d04035052401c6a10102c1c000c5d5a54048541051064201041d0811940410040034001d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 465339019 1250 465337769 465337781
    0x2070806101203030c0302220e010807080a0b0901110313050d0905030706260108030a0305070c030e090709050a06021b030a03080105150702090103030c060e0703020a0b1c061712030103030c02040209040f050a 91
    0x30b5078540c540242d030bc41c1c00c210760754503141c055824141c0c172506410340861680e10119502590483c00818003111082450550b504207841c1d0701d48811041482034204a024032203201040e00d2881d10341e2040d40782400017985c40803103111356014466410b4002520b80f9820441e840001018407070a144c9581d202851952640040e4212001a00d4003000c6400d46100f02100c010540c1c250381d80d032200524800c2008070b0050b000d045402481644580081c2c2c6440d40f032139103001880f0540203004142c008400e41031210403a280d2580c070a8101100300c40c00079030000f5031241034031415203018241c2c0c80c00710042000d1f0b225103200a03600030a1a0000000c16034008011025288a50307028000da003580361400b503503241c450200a40c0007040700020302a680c92031020300ba4144812010288404500d2203c10803146550400703000381d5410f129051103da030420481c00c030003500403051071171585151030007042e000030400002e1003540c0000d14070140b5510780c0c00a00c10000e0705030041080e4104030341244001c000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 465340269 1250 465339019 465339029
    0x110118080c0f010207030c060f0b030a0507050316121112030d09200f01030f150905150105031e040227180106120206250302070806101203030c030222 66
    0x72401440c2c0790101018002d4944095158841c00c19030034203551403102030045d9500c4806c21941d03800140565550400c01801c2960141c009408418104403d045c1000c01400404c4c00391041c02100700004600c4e40320105509800840d10345c24407490394000f801b00003004040c4040c504c030106040441e40350540c007004446114402d842800b14000201c09180704102503000d900c8185902c8911095010f90003925038510a000c002a03035900060100c0c102c08450f401c0b40d003049a42d08100106c0200d90030210400c0c1c8402d0910300c0c25450169200500f41062940001c40c02100c00081030854482103c1c013480e0b016044000c02c0307400140005500344d02002c9035207200c005152002202814410311030030781035031041c10200890203510340070321175568420820f4850300c000705500c2a2b0035985a040b07072043c1078401d0740902003051600104914181c8041d206041d440101d9200b0045000c1c081502071206d0791500300810304072040041540280100b9001503d01a0119400f41b83c8031500d0840c682559 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 465341519 1250 465340269 465340273
    0x5160609090614011b051e010902040513051b010c08030c0a0306061b0b0c040305010908270a0608060411030c041d0c04030323070308060f0409020f01110118080c 71
    0x950345000e054600800f05030494081803441c00c0c0d92018010308803a80b40003c0c0030710101c3d009045454280c0d2200c4ca0340e90703a180090f940d178102210841c0307000d00505030071039205181c1d007007404081e4599a4544c5017113408091040c0c03070400601440d9002d0803810800540200c3c0c0035489280078800441298400d41c4160002440c0c260007240003402100c421144c0d14017200c604881c000b443c0d0350000060009440ba01d01d02c0740174400080011400d01a2000c07051192904680301d0660b000a002c0c40402809007442c0d1008500901d05a03480d81c00b180380c00c1765510b280511250700d801010a0040042c03840c6030946590000802821005071801401101c1d5a240100c1e400d030514038051b844402c00f81c8860a203100208400c00202c0d00c2003815a10603001c1002c0c070112000769414039511640700c903604901003101c41040100c0c600d000b00100c1c01005054405000b12503040e400158408040b00741541400711948010703010a00035440988554040f003298402000c090400040da40c00c54005000e00d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 465342769 1250 465341519 465341531
    0x803070809010509071a1e2b090f080a031509051509090705150f0309060a0e160e15041805061b040302130209031005040c0b21040516060909 62
    0x2030b01c0001d03d010071100b0198210081c1e00300d02040006c282d002080218003840030726004801003050000901c80001c002c0c4880c05045002c00c0c28400c0390340212542d00c400c519064194002c101103241c3c0d001c40d554042161541c82504a1041e4000c21068608030040784980c4804295040c1030341c040307801042d49590800140e412002000994613003116929172131340055008106508009c0c00f0070550851440d0b0b102e0402c00005a8280079030004c03140000300398012420310540000034070520fa008010b6401829030805680120209545503225081040c8520703000200c88031440d2010101400004005215100c0481400096815841000c2c0e8680c01a04013207020011302031040710205003c81d0459090a196400b085000c545c0703011420581d030340802041c038407039800303000000e08043d01c24000074036403c0505010a0403045a00244054102004600c11503454121604840c05000c01004010358036840c0ca170b0300f0400614241154018071a501055054202940e4016544051001c10107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 465344019 1250 465342769 465342781
    0x141b0f01110904090201020f030f030a0b010c0317060f03010f1b02070f060c0203030f0301060c260409020c0304051c1101090321021507030b092409090a08030708090105 74
    0xca84081c040d205074403900700580c00d030604050f0085555140140151005d505001461074216448031004d00c5903030700004100700c00d40d800751007271000500c003c1c606120b4940c503542d009090795541c20b51041c0c26640c6c041c00202c8a07074600d1008214108050000d0220298500801d0003a000d1841c010046521500306081c5140c03001031580708843c625040b0100880c41c03c001900c4450043c54140e8040c001084600c2d156038400c4000c60007060075540303401e181e03261400c2008a000384602d0071080c0c608400781e1200c100740018190307002e0758000c44005942d641d44071407180c61b5104039441242c0000d89403054405008090000d10001401010011008041c3e030004440c144c805010041a02d081c1100b41d0005003043c18000d48040035a004407002c01044403050070290360100c500000280d00e540302e010355414004c0e102c58100f8425580000340d110307000b00d9094080b40940342180141e900d580003d094800401c8143d4007541c20900142c0e80e401e00340001064441c0c100c603800036640c00d00c0d0200360 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 465345269 1250 465344019 465344021
    0x1806040b030d030c091706012601020307090305190b060f0f120705011407170d0e2b08010f090c0903170403020a210602090f09010b070506061c06020307141b0f01 71
    0x40141486e00140c16a60300f40b12506003040f05049003003001058206000ca404502480214040e02d520b440b400b41240c903601d07065107000c401459402c200001c02c80074030b0000e0140400c00c0e030031680845000e1806030b0000301140543c68820800303030b030040d00d40105804460000c40c559050350001ea030313001f26406503007842410910404100030a500f08000d440c80c6002580d001034030b01c0c0c0c510f11401041c01c0044000341460003103c40780d03442c148480000300503c50040000c4442d10101541030443d00f640c9423180322452240306105003074199456008400065119035180d40145901003e042134015810b0000000b5800901040b4011030001c4030200d440d00503c07814040c000c1c040c8242c41e5900003680d8410340030f03401c400b21103604103084000b0b0b003031103039078000d4610f01070102d00700c03255110780850407c1854a0005000c4900810010035541c1201d40c4040e41609100c2d00420056541c0d1107900c0c0489107a6038010050f5640d82011403c9641c115903c03103e0403078010f0b050304840004943c03068240c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 465346519 1250 465345269 465345299
    0x1050709060203070803040204060506030a0c030f14061203040f0801050103020307141011031b0114070903210905130c02060c090109120606030206070503130b04051806040b030d030c09 81
    0x710259006120643c00a01e2910081d540144080c00c04030b0a19641d502045090300159178071002540c40380340c03943c100d035414440d04100e0020740c10280700b01d00030000c00d00c01c10000030301068051040754220360040300c002c204403001000c00407100b90440d0f0b5105201c0b4003c101c20700040703200b4003c0340c9001883d01038420406012150007800e010010760340380320a860804101d042028180003e020480d00010719824889440d892800081030308a0840c1030f0785c080d03800007803800b001c5c05298076091020403200c0c1c5094070900c0b002c0c81c0b40701c030250a0201c1070318041c0555000300d9100c4890f041d0780d10080c3c143c0e0032440c8404420380846845440e010034110541c00b4942e21315000480c075a2007040600f6002a6040185000e0140020f515072039070081010340d400010706984940c00012910811003211040c00000d04404060905042c02d180c0000d401040d0500c00e003036000760b8030000c2103966949034001c91030003d0007400c48044000120001d009080301b5110480458054000010610b078004004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 465347769 1250 465346519 465346529
    0x3020f030106051315020d030e0d09060c080d090812090c061c06150c0c0b0903060711010b19060e0405010524070f0507031514060909030904060906050301050709 71
    0x1400d581c01c21400b180d494110081ca9107080320710590001c0d95a070100d40f1080007200f02c4d805803900f007800754805404c0c0c1d840304241803030f26070200745507043c110340c0034120300c0a45120389030003034a80d951030901141c24026019680c00191030000040304000c0300d103000340071507100c1c114961910f80c0d0b03c1c1d4086842e41d40360355820b50450420440c40484a00d02030848002034451280040c03400c0c0c413282d4039400000010820f001140c12948070005100c0303070208400c0145540e50005180003c60b0011a0320b8007401707801700e01444400d445c0c0c4101d1501c00e4002c45620f450103440c2d00241160085076009030030340781c030640000c0780201e40c44440500f498010742341a80e0026094560004d0300b48989120030110000c3d070301642d1400e00c40d0200243d0981c504a04944c00341e401050801d04504140a0682c03070032444a400c207103000c44a502803400340880035488001103076200465500da065842c02c42c460078054540c40307460514041402783c1c00d5803040301611342c1500200302c0c664420b4403d5a4448142c059 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 465349019 1250 465347769 465347797
    0x5160813050715091707081507020d031805011a010816051207300b0901060c110a1a070b06063103081c0c031503020607020d0803011e060302 62
    0x3d03c01206100e4040d003000d4454030700100407079560074840c91011000c0f0441c441c0d030b40010000b0403444404000d802031121801203030b0306003803c003d14007950b1a0791085601c824541c5070884144240e00c000381c0001d003603800200a02481c03040d580e1a103004003402c040b0302c0c0400c946801040d600e2184681d108507901160b25120300d00901183c5602042c50014044420080400702030540500100340301440c1c400e105c0b441132000c0e5007a141300c10a4803116609a4002ea0751030703004104050788410000d9019400055000c0013000c1c403404952440c886411003036603100782c5911030079458020001481c4a42c041d041c0e0844981700d44080000034031481d00b044405030894000525640c0792080b2010280c0700e01d400b100c00d0666650f50b0910b03da0000c4ca1400f07642d1103405c3d0140d106507920b00412003043d00c035103001c1100704d03c5566003286406807404060b000300707c08a216821512800400ca1803190090b1a13162a50717034802d08442086825003c88000340c40000c1e00050b42d50107802030360802c0c1c5004117 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 465350269 1250 465349019 465349033
    0x10b030709061d12100509010513031b120c1b14101b232802010201060b0304080306031b060702120a021003020306041d07030f0f060516081305 63
    0x40201d81c280b03414800a00d80303d0484000c001941d482000d05400c0ca48250b015010340c040881000040301c0c1c0081500859906250400a903280055003141007150b2504080884180007800c441ca402c06511005100c65410300c0a84a0150070180d5a400b481c810110610b26102c240250126402148a074a040782804c0b003144c0b2041c40c0c8107200104540007490200301860100d4000040041451000e641e518810b90141c000c2100a190074a042000000186850010000600b600f040c90103c6070034034181102c0c526007160300c00e42154006003103003105035480741082d0038801c0c5940d00691b01c292091003940d59580f60008214480c401c9010000d00d407500708211a0244020f803449140c4001c000d009203285140142d0b01ca07990064000200c0d640107880380340c08014001210010340c01038032005901c03d80c099000b240029a1819a50701c0079076083c50032003a02c0d140c1c00c2c02000b10030003444542002e007084102d0f080d1002a88156000d9514403007e610b0708050f020711100380d803a001d40a500801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 465351519 1250 465350269 465350279
    0xf07050c100b0316120f020d0c060f0f0809070902130522060602060f0a050402040905011503170405060403060c110f011a0904020f0f060d060e0906011505030a090213020a030c08010b030709 83
    0x1414546c90b5001a01441d01c00c101a0389699000c040e54020001080070070b03140e04000341e0b104219400da003c10341030144150a11150f102d907a400c95114100300903400064040d00f0101d2030307559400801e030262103201c10303800304d0403100084095030740040703075142ca440d0b00080e03024800984103001e001c00d8941144241c489101c0c20000c3d0034010026070b001921103903140300051003440342c0a640202998001d0150b4154a420b6070764030b084156400c880c500a10040c0300301d40da448220740032a40e00050000c0d040107561000d03a44407405c0e02002c2141d00543c2004490742006400488500c3d0710003601d00850002c6104210040e901501e01941009130030040f0013050408142c0c1d056035000c018a00d5062001448450041e503055030410f40340050311100348100802c04010460141405a84072800594030000040507400010104500329444038522820f64481922020300800040400d654070003400c1e802401800b00f10131810300240101d0000981c82c1c0092040d0b03800b5845550711031824526103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 465352769 1250 465351519 465351533
    0x4060602070e1608160e0a090b09010902030106050f090f060c030a1e050d09051e070f1505090d0311030d06050112060302100323010909050f030406080f07050c100b031612 75
    0x80030305420700ca1b14002c94a155030b0392001440003400b09100124040102c88140200c60106038450b0340407500510040c00215013010580e01e100e0a80311155480d2094100062030b4250400072544d009400002c0250f1014008001082c3d100c80948610701586036141100e03079004ea800a0700c0000440c144074051041006030020b00c0d201d80034608440003d41c181310300c01c002c0c1c0c810001244003940086003c002001c605800310000f00741450450a4000c0c0021020386544a4802c84034030484001d180301c0101030080250710300815010046236110848451300e980148000e02032280413886445076000c160441c0d008600540c0e80c081c10b0f081c20030031703000002d80c007500c00c0308108500c44c0c44150341e00350350100d25020755008190b04440491260001d0424505001000340300036000e0300100401d00c881b40d040004290892442040d001180c0d507000d60484150048100c041d903107025980441c404640f0325040103140c004101e0a440804003400d4440e048100395203d88201c0383d507007071920b601180f58 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 465354019 1250 465352769 465352801
    0x41706100308070305030a021b0c18101a0d050702100513031d0a030f0b01060e060c0307030f030f09110f120c15070b010621020301080618070504060602070e1608 71
    0x541e11003d03041403c03007191560300d00035004600c050b50342b126803a04160310b130031610051000c400480d4056642040d110180d5400c900d405518a4200d08810310640b812094046441100401200700918202500000d468910400d2015011410940032605a200f500750240043d03a06d0344403051104848800e042c404c1c40c450030490340c401208180000800d801050058055201e240602080e60401c48050064001707007006138041e100a10050105110000444460301d0301401c098011100944080340030b000d151800c404501d081a80c881d0410502410702c1c91003000c2110701030240c0941a00303101410050749a0341019610103807100e61a401c01e00480b000010701000c10b0340c5491095201c61030103070400e80c0410001460034006c00e08031040001e049240e5140c044042d461545420f820030303507030b01d4054515072803454044044803692804003c82e10041c5009001403095507079a5201a40700e02e25442200000b207900f00000d004d45040b401050000081501c0d250a60f031078480548407600c2d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 465355269 1250 465354019 465354031
    0x60206071206050d050a0b0c04080d080a0b06160c0b0a05120c070206030f090c15071b09050c04050306100501170901060b031302100c24090804170610030807030503 72
    0xc1e440d42c01003441d88400c0410b80c061406400140f16420040c500000302e000020315026001e80300f8407050244100c08943d900300101d2030b01c2e101c1c2d03141d21002a5000204010f43d02da0b54441c1c0000f50200c405071203002c15414850103462025a1243c1c0c0d03204242d0b580c802c0c0c0c20702c1c00010300c0401100700c80040010308030fa008202c844016092403045e43c0441d4680d03006480082001102c80100b110b2840d00300241c11444c00140e4460311680f0251040e2001030103078510080c222100380c03035141c2005c130b42c54102c0d0b802401401010300480c2000381c40c02c14168014001da9001e8040d030400220034401e0207903902c08603001a504c1c607003114000d00c3e2204c0044005401a40a9500c0b172400048044001000d50b010700d410b1707005418609202e104102c00410701114072010300080c4001200803600070311864007000380038020080c010465660010040003403010081c12580042404a14480305110008a414290382255060340341d0000302c01140380c0a100040c400789080080b80000782c404c1c0061900b00c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 465356519 1250 465355269 465355271
    0xf0108010b0f0f0d06080f0d020d0e0102100c21020c120304031b0506010f06080702070902030c0c01020403050703170c031c06031e030f031806090302071503051501090602060712 78
    0x161003002843c80f80c0c0d02c12452102d000e80c541c17509226081c01800b400e12440407400003001c0401d40031030060744034031203611003000b03000c0c042d24801020790007070015400748a061081001780f1000b0031740142c503080042c02c070b041002c50b07200c031240761040d02403003181c1d04000300c1401405490181c4000d561540d0000308120200b06600220115254076842d0070410544140060320f8598144107895103030101c0340d40b20780b08100142c418068001d07004101c182c00d40d10300c4013025940c2e80c3d076901014001c0c0308101400b02c42d58400a400828404c0101304130040d2071083e0b50958213080c10b186883c51134010081820981d8008100d00300c00500c002801000c4000b1000002c0740300c83c0c0d2515601d002d001844108005591905003800c01c02d42d00c610b100c00c403512541000c00c151411032401c9281c001500e540240040c0d507511580b01450700800c00381004000b40e280481003002a1300c00103025040c10b595030440e00d448410500d0740e42d8040c001120944400f03900070400e0740e81c1c8403801c0b245201e101c52aa4001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 465357769 1250 465356519 465356527
    0x20c0a0f060c022404120207150302180a08070909021c03020105060301050609011a03060a1a0a02010b03010b06030c0306211e010b0a0b0c030d0501170c0f0108010b0f 73
    0x80a204034080c0c0e003401030900041190688a000e82444140380ca04007451a040c0f180030340e812a01c000c115080380d004042d41d01c02c08200715099117070500704d8201554a6100c080002c01035a0b06400811000e0409200121102c0707070001030252151641c043c0304907a800801c010b00c000c0c00954009214280010128920b80b5805003240d016882e641101340d006075100d90800030b050800b40280380d00032070283d0300b5240c41c4d0f01d4110740c184c503400c00818021075460f000001c91015038030805550013501003140c951018031040b0741c08074a00e91204d0004805542403802c2982d2a250601c151021844c01800b1145559118911800c003030340020003ca50007008821003400c01d90140b0f0400481206180060030300c00709090440d075650400090910352681044020051381d240c0d28040380441e511030710202c4c3ca9600710203411307086010f01c0b22081d040d14500000000c0c4843d82c2482c01002ca4846019620902d1034001031180c03003c4d034881c0300c902090003180100202405800280f2070140d0b000461410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 465359019 1250 465357769 465357773
    0x2001050703211e05060f2409060315090106050f0901110a0b0a0b18061305090a1202060414030a0804080a1101050c07060c020d1e1110060311010504050310020c0a 71
    0x8a03142c552a03800c202403c050b01d10b40c41c02080c418941c0001007140c180c2d0300d0030f0a22000411342c0900d00d507090580783e812400041d800556030282d99000c90000d110356181d107085d03200e020b02c07031250030000d62090007540f000148d020b008808943c0d64004285403e464500d00c2030054904910302001502d80e0b10030503600c00b0206440341c5106001d03900803540481d00b00000c07000c000503443c50060f1985c43c036804030240190717540c4000c6c45003400ca002040c04103c40d9180340e903ca0801c4045140a0004411540b01c582c8143c0e0104071140308501c15041c1001340003040750520341d60300600b001500480c2612012401291a2401030205880507180451001000484083c251081524822540d038004940102000018001c51906400f00d01c0140f0203510210b41c02406140d881c001c03810740442818803804001c0c4150b2a501c08031421900301d6450940010002005050750310007500e224040003100f039181d41c440c400312030803124000c00514030f007541d01400303000940c00781d80950f42c0c2d445500c3c81100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 465360269 1250 465359019 465359021
    0x12060907230d05070e040c11030301031104020c030c0607030c080105030a030c0203120c0606040b040b011202030a140103030509040609110f1803120403030f020d1b060e01020313200105070321 84
    0x1220369140c0d41c5da03040c2e0440300801c1c003041c2e801c0c948145050058080302c14000e40c100000b540e0440313030040c061720300f600d07207070000b0a0080c400d43d90818245d020001d290014030740c2c001481805a20b06e960100005085114105c65641c0d080c010b00768140c0115090502092052030503240c903d0004059071289140c1c00548451030340200201c00c4646c00a10411010380b525100303500e0f00440039038041c80150005000204440208150b05000741e6000c80410104503803036102d07020f19200610300007940e5031681806000c0c6d803c8035940501c500e080c030002003104a400c0c00f540c1e40e5010014100d41c10001c074910590712a4112038200184a09000180030711a5070030840c411900c09294115540c45086080c004d0059041c1711452042d94804035000307103607503408132500301501c1c040946501c0c1c4a0701850311001405645281c07410941c008002e02100e50011428102810710a0307010221920200b0381c04400c1144104031540420030a22003080420300846212040c1ca85002260740d040000c001000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 465361519 1250 465360269 465360271
    0x7030804051c09030203121201060c051212150d080a121b05030106020706051201030602090607020a17011d19020a0e040b0709091b030b060f04090212060907230d05 72
    0xc00625521020000d6003401d00800c0003580c62286090711b04504814230324038041c0188980c00401400f88040401c0c80428429042d80003281e081882d599410748008000702c04094401c0c1411146400c01e5041601d45900148041944101314904211818905444815000211200580d01c8500045400700c030180b0382e10b001e501903192161a541451002032411a0641140040c404d0402c1100a0841c03283c500604403940a100940c1d100540004078000b40511003000350050900d840108030141c05141e10500641824000c00403521114444180b140d00c034514001c0c503400c41c508100000c00c0608601041900146c590003c0b0340da2000c100c086a002140e047c0e401c1e9100c1e205010170300d0307031200344400200007480c41030140349010001e60340c10329500e81c1d06206042d0344200c0d9414907140c880030b0740c80030400ba14603940c4650703580412074003a5110640c1c2400c0d02c4100c00000c1e82074074000c1c49990064000ea030b50880401c00c031070903c4900014243d41403107007002c107210004c080603150189d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 465362769 1250 465361519 465361573
    0xc07030503030414030c1b01030608010e0604060b0a0501051b0133050405040b070c05010f020c07031502031b0904111c0c1e05090604090c0f08060904080703080405 72
    0x2507542e031030181803400e02c2c00e40040b0440041e400402080c5140c4800051920728220b101c940c554100c2c030382100680c0106160742c0001615424002d60501600c1c010800030701c214051241801032503c4001000690038540c000c6501045082c01401e0035050700040240b0f4200418000284800c0418849078400320041004800031500c02c048020301145800c05400800050300c05024500b003d0795820907d00c00189084100300d020401c0c0b50501209400c142030044403d01d04542e2400091318103500c441c0a400203460a030050790140301d0002a510071248514000b84140c03824803a0780e00c510040b94041c9202c40d9101d92203000840f9040301c20401800303001c48100b00800031195202c0111b0588441e00c0c4040c4c1401150303d4100c0580d101d40c0d010311001c00080c070744a942d40110302e0014426004a801080d070b05031500381ca6800b100c0d0480144107210b1140e4442041c1a5039090400817003000c111001070007030b5402d00902c80000d002d0342426411610520690b00c101d00e00403c0c844000700c1c64002c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 465364019 1250 465362769 465362773
    0xf11040308071b050f09040302160f09051605030c07060b0901170f0d051819120b0108010c0909020304020d300c0c0e0910110a0806011b0204020a050c070305 69
    0x220382d0070040b84100341e401224611040900c52868a400038508410513406540510718040c005810144244682c1c000c0f220221075541229440d28078222009407203010310111503160401103a03160a42c80f07500e07002c980a9640303480ca99502d1504400c1039800050045030102d03107902810540c4e0341c6401c12103000e80340e80c01500036000141c0038403510307203030b449404c2c060990051400c2c0c05056900c40300b2a5040501045a5400b890780c0101061080800025020014004010106031070030003101380542d003401a40c80100590f21282100d080302c0c2c942511b20f001c2511804208464001a00555402400241110100b1200c1d440341000d0303844030302c00e600d1203c020542d042c459000c06d141003c0d01c030b0350134500f5071410200c80c0c0c2d03510040d5516000e01c1f18114a200000f41501d6030800082c40e03150501c540501c528084070b4403008103500186600350105040e40c1c0090b4295201d00301c1d420f8001031200383c0791321140554091100a51100d52aa010848100081c3c1c80b41c102c20000a00254801e0300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 465365269 1250 465364019 465364027
    0xc0103050925030501240909050d03020c1608060915070c0b1503160602070b12040f02060c0a0303020d050705070807111f020f1b0a06141204050105180f0d030f11040308 74
    0x2d491100b06c51190001d1011a18043e46400400c20010b01040d110499040060783c4c2d44c048a041480d141000107490700b42500180301142401c40861401d020f002000700315070000343d8001d894407440e4070481c0c100300000c01c142d001d480480c03000caa42e20b812241000c8a03540d00c1142d1400f003414580f4600b00140d40700080c8004005055041014100420b000d001d054282210f150b08100504000381c8003814607190040c1041c29036492408a91080b84002e045940c0d03030546184c060040d4021201418680380382c0320003c4c4542d4000c604503840e4070303844a40a40b4050084e540c1289240282c0c0c41c86800060000d0300070811800441d0a02c4248170030b0300100702d0341c001000f000e0724102545103400d21010f00c07104143d10984810708410b05559882c01d11a81024004407030307020074012101c00254030100602408103211040d07020310301418500b1a00d000b900c0301c8400c56039681d100030160607100d0740400070607580188070360f000402c00380380c07402d000c501034a0f86405840b49070800e41041d0350702c0600103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 465366519 1250 465365269 465365321
    0xc06060b030412030b0f0f04020909190e0703080304151103100f090606050909190207060b040b0405060307090b010207120303060e1509160513080607020c0103050925030501 76
    0x220000f1200c0c1103280c207128881c00000812181c50403104181e00074a248020901a950b90703070184c414182020b0010100d900e02510448a0650004107001a2910f0022499041840464444140c80c0c002d81c215185860781da45030440d00c1203101d0307010300059464074410060001c600040d4040d4184100242a45051038912404c0c0d000c15031000c0c920074a0701c0410041a9000710990b58001c40480d100c3c0038550b80d400303818144142c0e9003030b4410020700c0010200c080000e02d80c40351603107503002e0301d003005488a01380c1440211482507800320381c140c0c003885080056990725041310644000600c180c0d8003140d0341e095025000b56a8100131030210780c854030148080451510402e500081c543c112a207000072010109941160240c0076080c0081d030701c561b10302514094400c54190310400e200b0340c0d807255510301c540d40c0c03680802c0e200540103003d80c4518010355071090140798000e000305000341c0030280b44162021500489054100c0c0440071015000012400a01c0780302d00c5103000341d1942d2407114100e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 465367769 1250 465366519 465366533
    0x1c020d050309100c170c15090d0f03090b1506040503030304060b10231303021915032a0c0b04060902090c0a051204030504231e090f070c06060b0304 65
    0x20b443c1000b000204034809000c105078480304040302826058040c0d0710700c00350f4101030800c01510306140419001d4002d0041402c0d001842900c003042aa60700d03601d03444040402c07400c0d0b4144080c00384c10350703070404041041342e071413810803140c8004000c122070b03d010341d1840400c1c11074100721000d540e0740b541e800b80010705041900c0c00082130741c014030300250854440300241e0701050300303e80c40c2a526840800c0d0308101740c5212240c60091a00148103201010700c80050f154403482d140141800641c0b20341440c08124000e009000c02c01041002e01908054603100800085010032065400c02130704500600c041100304520070f000e1f500884000c50002843c1c01409019580074001103e1000100401145250b019040e0350758182c5412182c2d441ea03d0b9030030200da16000d40c4d0000445800b0422100030610140708428402040a0351500242d58004005290915100100c41e4008440308009030020500017070103540f002c2c070f40c03c1280380404d40344c5a0608a5107150410054440300009001c00d02c080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 465369019 1250 465367769 465367789
    0x102100203271903210209090a02070c03020d080a1e02071e0e0f010602070e0f07030c0c12090503060603070f1a04080d05030406141b07020612091f05040b04021c020d050309 76
    0x1701540c190318008004020450244004040f40801540800c0c403000300310505440c6002950014055602440103013081072003584049181c401040081d40000701c450f440c0c02c4040803960142e006820001c2c0741540c0f0503200d0041025544a620181d10042442c0d1100c420241c00758840d144441c11560408001070b203400ca40340c001283e416406c00803c0078520100b0000742c1e2108840c5400b00d03c01484401c1900e200486c4da1000301060703031580c04413903600d500840610889400f2001c4580c01d445071405d16854070454041d0076000040d0520a001c200030140c1308025001800d58030318a0907585081c09828044c000300340030001140002480b082c007241c2e002e03590110100030780c071245500f230a580041c085d0b1f4801094070303018500803484400b59650030b416107a00603800032301d440142c54440002521114000c031120544141a66118044c0c2c149101d07031403042d0352100824407241c0701c03a000c01c4031030007102c4a030059042c002810704006071100d101107521148118001c641341c008071010418401d40f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 465370269 1250 465369019 465369077
    0x1020709050c1c020d090818270711030415030b0405060a06030c03091a090613030e01030b06160c2d17150903090102100203271903 58
    0x1c10541404026621941100c5400401e0744110007100f0311451a6800303409103200c3c4517030480c0b07002400300a0001c08002040c0100c0c0c3d034140c0c86d410841c0c403410855600741d0719418801c03a107070602d8400400702e0710032441380e000b00b5541080200c884c46148128a141d00580100300c4000110040c0304130305415018828035960200c1c0c05000c82d260200100b02c580d6002d206660030191a1003040400034020360122180c4c6800c1f0b8020140c1840c01303041c006245200303135003c2c004e510032440090300c01071043c0f90200585515655140720b20a62500440c085c185c000b4289500c000c007045218581c1e08000c4500c0d07100c0c0d100d0007090106e1490a540311a140c0c6405250b1540401c030028000e004041c005d030f0714425a40108410342c1103195007c0c4031031800701d020f4040c1d0b00560901050110b01400040504501c01d0700340d0803103801b81c0f13803004880b069000640709208040b201101d1040140e185104080007000040100c50481e0074610300f482040ba0300c0007040c0c01140e045c101d01180004030107020b0100203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 465371519 1250 465370269 465370271
    0xe01080a05100501060c060b2404180207032007240908070605071e0203070303090e0703060302090c0318160801061d0f09010b03070b0307020613030806040f020d050901060501020709 80
    0x517260000207400100300d28001000c069036640b2802640d680c94040885c2d4600340c1c0c00d850a9220341503010b050f26400350084181629011510030301105050080b2050940d042d40d4108012140b0300701044044900300ca0681c0d02e0040c0e10011409040003907030741403092007910800f4107041c0d103a00082e003112000c0c0c001d0b240c00c3e000f40d54140042c80d000b800f104d00e9107900084c0306580308104141252600000032000b5414020703084004107160344116403c083d14010704803845240c880c014250222012448004e410007030303560004010004e250081c580c0700500d017103036051100c401e05005003007401d216446036403401c0300107003482405001d22445011b405070804005041110610403906490010158000130391aa40041d000003420b411114203000064100c1c0e0b0510f0b12880c61688542085640000500c5a000007803180d040c5801003058841e01a01c6070310854550400780320240c0b02c0104400c030b000382c08020603d0200582e105691141e0f980c00c000081440c01d01000a04181d03499101e0301d00d031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 465372769 1250 465371519 465371521
    0x90602041d0603121e04090603021305061c0201020f0a1211011a0d0201020f0607020106170a0f03080a0b0a0e09120307050412170d0501080618120c070e01080a051005 73
    0x2640f0000b80391a0004140c10f081920f808240c04d12000e01c08004400c0c080f220004140007800f40c10681003003080e24403c032140522442450b60300400c407201224920f910001080d0030074144256050303e0103a6500610690302d8104400b40b0760391520313040e02d00483d1078481081e050000203038000c000241c011260700c0280300c4826280365011038850b00c0681c00c1e1056070580c50410840e8020441030f2540003000040d00c00b14684401c0182c02000540306600c0400d0003d001c112040703001098845803c0c2d032040710322071f021500d0785084411801c020504070883e40d0b00c0e0b900d40911fa40d0185c0c924010401c1c41d2078070b2420700e042030b260350406d000d80c800031210000500600840c1c3d6001025141030300c2410100499020082c1040c81407154086804481150000b03240d410807a0603030446410f8400000c1111039a03110031003801520412049041441e8000903500844c01000900901c50030150104990840303880d0840380d1400c8100307a000040c40e0340001c00c8441005030a0100c403024402030381c410445 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 465374019 1250 465372769 465372781
    0xa02040b030f0c1c020a0320040e0d03050403030b0d2901060c030503041a01090f1a0604050d0c08190c0608040201080402010809070e0c070201020105060a0b0f0a030f090602041d 78
    0x76440c8140328039032190546800d404c8114103140d00c0c0c0070310240c0040c103100300d65a40f4100440c54080d00c0440c1d1040f040104000c0c00141000d01510803003006000050201e100e00c410200c00134070340604114101604c0d00c41c5030105584c0c0080f50b00c242ca020b4250f640142105c844250a5110141c21180350b010307101c001008801e80009801414680504140b50759646500e00165064030030207103620301290600020510100c5036100300c1c03034402403060821144001d0b80e66814140005049154882c1c0c041100740b01904102402401051040d290051080d86442c0c0403401c11010000b850001d151040079a014410411540c1c4010561401d109a06003840c0d0002403440d00000d001038107102440021034003540041203860001c18503041780e207843d414440070f541c0040d0f1160509038019803c040208895240c907200e200111824403a0040c81d118140c80e41c0d611079001a07030200300f0705035601c02076154041e1500aa0361140e110b8800181c0e124184030740700c60120840001003051083e02020400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 465375269 1250 465374019 465374023
    0x8100308091203090405010f030b0a1e0911040504030309150605010e01050f07050a0b270304030f02060409020f210403080a0b041d01020310060f1710090e0a02040b030f 74
    0x101c0c000e5603224800705698040e07514520404034a290850f1610000107403c0c0358102142c010b9070b219441480d0f29850b40c07180402524101400f0b0051001c444a280103444d4240e400b0984080c4510315035201800d034600020b0032078008440c250302082d240d40c5c05400b0021341d42524445c0039040f44081101d00d007420300080012100b1150981403007000101044c00c50b19542c141c4003100d50102c2200d01959492400d8500f031704007a00c1d00b000040f5520030444014528490907a001c03048078004600701441c43d154255800c1060301d040c4c2e0004130030000030405001c0c90000303006030b0b20b03c0c1580b190381d00d03400480c001000f880c80345151032900017a070500c00003a43c45400c03070f47c014042d2100440d802d4401070000b030040a02d403013101341150041c481824004419006076200d00c508004840c6095921101038620904c01e401e103200081e03c100001da08101100d603126001104000400c0180e5154200c240c1141c1403580800400d034072896a60045103440d0054101880e02a005801201c0d08180603a0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 465376519 1250 465375269 465375277
    0x20070b04081803010e0106030201031d0a1104020c06070201051608070e010309020f100305160e0102030a050d0605060d020c0d09270b0405042604260703020406140108100308 76
    0x70800400040e004281081241d490701c2d0001c001030081100422a0301c8081c02001c85e0700c41280424144011440580d1011424660340d81040d00581030892595540c0d070141301e2425507030381e4005d80c2405031940000c1d003040014421030785600002202e04001d0400c1c24240f00510590040229900c1040f0b603155102e050b84205180a0a01080e800c0b20f6100107003007550340030b080f160040849913850307a84030317410703084180a180f00081c00c032100d28680800300e03107503085103031502e016078410440d1030f031a40d1151006060b03200340031000040450700e0f2000564036070b0006082200d4141c02042c0e450410030140710001050060341010500e29103060942c69051038030a06510760030501d202801c03001546c3c0d4200e083c1c0d001d4000d00410451409240080700705803c00e03070f2800410b10b500440343c80a040f031812141901c522001c402d920700c18091000c00510b0007241866028001d40200000513100c500400001e0300f4490400c910075280c00000402402c8024556090884110001c00216481c40221 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 465377769 1250 465376519 465376523
    0xf040e1b0304170d0e1002130803041413090b040b0702010c08060913030201090203010203040b1014150d38090408070602310906140901090c0c0b040620070b04 70
    0x241d0b444030000702130b11004000c0004803071910b01400c9001325a40c401503000300307a61500d55402c011256161040c403075403070246000b44111040b100c603601425140912070003800e0224840301160910b042d0ba03403620210310a0324106c4002c511142031009140d0203004e20030f46041c3c00d250008441c03030100c1c00998031000151441011081010007001850300c00c0d0032403001140c0190085d5502c1c1800d20f0201d40314001200c2c46868a1000764001c2030301c01101c07032150445180180b5009032044103440000850748070b80b0014980d00d07596210a00341d8a07001095204002c07540d43e07800d0384c445a458003d105000301482d5188a0902c170000c00001421000aa0745020b03005100142c07103a5075081100307520145400300404c90b4241d40100c007917101061800c40e09548a206c01442000c1d92545511007030502030300c009138406817078001444400d5155000c0e4000e41da842c5401681395801c2d4035001d40b00c15003590181d0301161910020850440310262251a03070380815420361500c0016124905000c03809000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 465379019 1250 465377769 465377813
    0x20306150a0c2927070e0601090509100b130e0a0b040f090f060f060b04080a03030b01030b090a0c020715030209090601180611030f16060506220b060f040e1b0304 71
    0x3942c0c00041d100071241c13210500d050304907039501d521225003282540c4225000e07400202d0002c0042584c2c01c1171100c50f800358a0030229408820f06042103580d45400203c0b0305c002c045495000000d01d48070088805008103044040041c00d00e10713100500050b200e5126841c40c055081030201400200d51868000510350801c00c00581c0c290307000301510103001c1c103601241e003032240890003040c12100172072003000c8103119441c1000312010550040d001d9a8800034850f5110144200089410401c0c1d0420020101c15105840b000ca03100c10a0021040e0766080300e01c0080c0e4003061886480c1810000281c0050303013420300d0030a001c4040d100c246a25441d004080800c04021a00803c1500c1001921064485c0c0d4110a0311080d81c03141441d40b580319590269542810070000c14582e08281625030343c019503401102107041e284403d10400742200c0038000d504044100005c43d00ea8074120082e0029000d0382d004e060041c203141d0499807003107042034080500e5400400500000400d4120303601200c240c1208 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 465380269 1250 465379019 465379051
    0x60a050a030b0319350715060b16050618030f0a0c021809100b03030414012f06090c0a0302010e010e030105090106050102240109020306150a0c29 64
    0x2020a050850144031000407032401605402001010000c545c0070500c1c040c603241340305594a410302000740540e80103448100d010802900031440c1081041d590b40540000401c0c1c3e07a07991440129150321483c0c0003886031100c10368640401c882401103030781123210102040400300030502c0303041e128410ba018209601c03d0000c3e441201c9401851044650340c0c00501e0f8103a5500c0703981d0165000401180c002525020342048098484c55a11965605402c0940114102414101014a000c44002c0c1680c140900d00c0107007182803100c4000140080d19a800f072250004407284034034904000a0698241c1ea082032203003200300d4840107a15001c40c1e40900c0c16605c400400c40043c0e81d000104440f035501355090004200c280b0a05400c95800c41e0020303401c481d100d0a824100160b240b4070404134181d02144100104410446a005150003100041c00c07039400e8106c10b902c0280540c0462400b10103d80700100b004240608400405096082c1c40808650140380900006a0329801044410171a80d405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 465381519 1250 465380269 465380291
    0x603070302210121082208100f06170604150f0509010b03010c14030411010314070c0c0b070804090f061203020606010314010302100f18030b100503070b030106050f0906190e060a050a03 81
    0x114024003c004940581e18200200c0f40c800b0054842e440c20070010301c0c01d0950012f55643e1140d0790100c400c6400001e4085500c2d96035a0301060b110314041c15564030313111100c60442040c0d038407405024003260400010450154024142581e8071440305030306201e03031107002d009c40030440300489034401d034800b440c072035494102e01c01a4001c100324031402100c08510020014402d800800283c2034070f021b0f180400840356030355042641ea2103503040041070100284010003810318960020243c480b60700b2004108543c83d030704005860401010240c0041c2d00580600c451540c1601c142c0740700c805844400443c45d81190080750404443d035940d03400b00210b11000c4101076101c1c50094a12107407000d81103141540c1d9060920140000b6960703a00f07201003c0030005081d28000640c80f04580070140321030305580ca483c01c160381039080f840d01ea80a0b42d1040159040079918071000707054124490f03c003541c800388081e200038011b001071180745015042c03c01040c01076540001c15150604244c2c0741c0415018460 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 465382769 1250 465381519 465381577
    0x5100806161b08090f040209061b0a020303130608070306060c02090621010606031404050a0308090c13020c06070201060807090c140a03092a0302060307030221012108 73
    0x90700040308091001c940c80c02c10803201e1001084e4140d021901340031040d004c030b01000102d01c140400700e0b600c51410045584e0602e02080030f441000c0000041e0b643c2041da42e0040f030b0442d44540004a240701c01084c00740300c825007241c8503a4000030b90f407408005c40750900b04040c0000c044020080d02c2910108002005d643e25008043d07141c03010020302100780380c1c25131240c0e13001e00300901a03000030904010102c0084144040c4c4244643d4100703004081c10f80f00d41d101907030b07004009009060140100c0400312441d0715811807540f5240c00611006a490840408a03420304001806000c00c690401d00d081045c0380d000654134054480307405002482884444054465503a4114440000720b0003203000210350b41c0540c0000390841c000d0484006000000b044888048218642032010440151040c005070030b215028541c000030900380103141120240d10415184807000c0303000c5404e0b440c50010700202d03030325140c840404101c24901a0610841c2d5940308122301880c01d018014240e5220b01c2e288240b10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 465384019 1250 465382769 465382787
    0x5011b030c020c0d060f060b0a030c02060f1501050424030501060e090f07030207021518010810090c031e05100602030a050f030a021303082101031211100608060a0510080616 76
    0x2888101f0854140d4400440605030070449001000c20f203051841c0140c0c500200722284603524062880c050b540d1911404403041101101c10340c100241408049480041104078031110a030036111548501070100d40201039540507009071040003015180c681007602c8074603a113900318003040c80044050703440f800110000d001d41c0308042d6010025641c1409442e00c5640188003014090b00d044114208000054941d140143c032480700d9a090380c001001910116480f2141c2d0300c0c0035207030102c1d03070003041500030350312888072240c81c05100d54450a11840d0340d8144a030400414890010754204615840e01a142c2d0040b852a0012075a0010016000700303031550460362402490000e01c11202e449090900840d0008006c0480600360701c40f8080700807259080c054100d940c0a440d01420240a900441e541a02d60030728051600c10550309081e5114a4081e04000d0007201d00108507078a4501001030540f180502401214080c0d5403062080c480c1c0847c0681d0701190301e02d000c041c0301140303200c103c070a038074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 465385269 1250 465384019 465384041
    0x2713050c0607030809070b071a1b0c15070f021b0f04060305030309060901150902130801020f07050c0904020a0b07050319080402010e040b0906010309050102090402040305011b030c020c0d06 83
    0x50000d1500d00b0180c200c000384d1301a464001c100c50700c0301c0d110440503043d4407881401070403014005584c1240e241140b001c0c107500c82d003070b10900400b1028603114845550041d050b024016005100300c00b10790a401d1610640c00b65035460002c400100c2080044d40b2a601c07401100300c01061030481507450317120034040710000000a00204445a42c80c182180c8030b401c240e07032502043c05180003050446ea0f05000d1000303152407442003013070b00c14a0189014020340c040000d0741d580454030a800254142c0030b2001c2d00b1106c0d0710422103581c40d03003907281007420440c2010080c0d208241035401d0001588500002009466600510940e20451414003615500418450300740e0050800c00b01000326a0000403103000700d01c00c0e00c4d42d01c0041c4004003000300b0b40d114454119004000080012400d41c800c2c0c1100000a018000040c60043c0e070343c02080581e0b115400540d9141c0d1a6000051800f00103000400c4041d9149810000101d50600094450000c8079400e0f101d083d4007000b0406018080d803210740022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 465386519 1250 465385269 465385279
    0x150411040c050c060a2304030807080601030f090b01060306090207080a080714131d0928020d0515090609030301061809090510110a140c03040e010303050304022713050c 74
    0x102d020341005c0080d280484052445408401341c00381c60030380841c43c031401541c0c55111004142e403152011101c0c0d4000525840c100b545950b52100688542d1041d0610b40740100210105581061406010b4031202d41c0400c10880c4104200404188d0150550b46038440f035242c210129200c0c060200e07505104460803c901050000c1c1503d64961500540801c41e102e001d00d4503113042c41d100ca540e51441b004c6800307071021341140755900c0400c401003c502e10324002103c4454032480e001e40101d020b0358600181180c059016021901c000010415510b0344050390318001c1000b4074009241546a002c188105002e004124810035443c040c944000000f402508604200103103c2d0700f0141e5481042c800700e01e92480c80e00c9a400300c0168036200b120300d0148640c80f030389800d003204105000349520003049007450b40020b000204903450f48005141c001e60207075403013903200d06090040000400c0d4650603024440500000a92413803000d0940c1640a01100001192000d56040c603e0800d01070102241d442 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 465387769 1250 465386519 465386521
    0x30f080c0a14031c0207051e030c100f05250309060b040c0f0806040515060304050a06060f0303090509280e070915080d05030103080717040902040602150411040c050c06 74
    0x841c4001000d002440340702003414104501070741011040b4810104003400e83e4010301c032401084048d941460078a078021004683ca014051174506092400b1407118032800740e01d494031000a603105028454100c5000c03d1540e144c407400341002c00d41075031040d2800040c561a803820409000e103641c050705008501800500a00d41403035801031090303501c503081c00041040705020402c94102485294440c2000c071101020400074402000010340008000312443c2c0304070110200042c205014544c0100050203c0ad0400350841c0b802500e0b610017a040b441c018000001013001e1280301c140f01d0003080c110000318080150810901c0c07005041120048403607072261180c0003807000d040c3c0d800310b551702e6117014a180b05a9100c420700c030b480d03415a15a0b000060814401440840c15040003814610f124404440814455171a180300c190040ea000c4c2e10320660104e4100562a01400702401450081c94110762a142039500c15840082c01c01406002e6a5202d82c02c8440d580907008a9032500488000c80b031362 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 465389019 1250 465387769 465387803
    0xc1303030903021e240c03072409030f030504020103020d060e10170d111c0e01080906070210020d02040b18030c150d02070c051c0308070207030f080c0a 67
    0x402041444202c2c0592807a041440d031000e0503007a0b1000781500280400d02040d501221a4a0784562040b845c04201c020003048003010010001440014401e5106031300c1200400351010402c5001d00ca00310b1441c0c1011b10840019901403100c20782c2824505001031035480d2070004030000e02481401298047ca00003000c030341003610704001031182996664048182d0345400d4030340c180354840c00c0c40300140c0e40031280f80d020071b50040001009208100d400c07129400300302e40407201d0758902a5120400304001c124223102c0d075680b0040441e807002c158801040182031018009650340700e540b1110081070390110307401564082c1038045030010120440c040d61202445402654810701484115209101d111008151030a18503200d004c281401c15a103802c040c0b40e203032104065030041108888050011202240e141c6c6d030100302140346900d40c05110081840c0703203006030101c0b00207421801994005101000054120207403480368a41c494443c1d40c131036114540303a0b8504001e51000a1000840d404805c80c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 465390269 1250 465389019 465389027
    0x807020d0b090c0102301204060209030d0f020a1221050a0e070312110c040204061106061e040e100501060c031806090e1005040509010902360c130303 66
    0x1014907003490a41d250300c2090001666074400789494205a01581030382e40c0c06d0860380070b2000803181c032180061881e08a86903100400c200f411601202c09503804034903419242002c101d5101052200c0c24210034051072004080c0d554040c18a00510b258001301020b119144541702451811001800c0c11800c0169048442c000d004100d880c4c44a6a280c0601d02c9003412000416504403608000c080c0c0b110b201c0d00100303c4809108408a103c0e61207195000c0c001030700c03184020001428159112001000c00079442410b04001810440c42407000f9a0300802500c0032100510b0721000c00c44000907039120b440009414050141e814010356490b0400002d20540c2210541c0e00b002d02c25503c131464100103540700010000c01e802903100003106a03006001703080307400e0089a0008141100d807500d00d5550000181134580032a4214040d075180c00c0d4040440c10010b4640e66403440002240400d903402840d0120703500041c0d0800c0400114130008200c040340060304a5803502050384822071143e8907420090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 465391519 1250 465390269 465390271
    0x4060905070815250c260405120706051c0905160806010905071d030c150d0b010c05250f080304150e0d060b010918050109051e130807020d0b 62
    0xa9900304500e000110484a61043c2c03040b0406060b51a100e02044602c0172030b00307204107440c210b071392080d41c084124401601c1861088264070040e5450350315800e003424008084210240796540c1ea000f00e41c00d210180d080420703209800d6a2006008007005155208400341840e804090a40d0080301401451503c0d911948030079600b1840883e200c0340d0362440d000c4116030044981703800048031004e40043c40400b003441c03902ca10000504440420f106400050310319103118000c0b01e0420340016800850319854003801c81170312400d081ca071122040944070a500c0da040c44400c00c4103d07001742a075100d501d010b40d030034001520401c03802c3d090030b40e182c0c00ca2940da603210b801150315454a02d0790000d036491046824172980d0a014089068508aa5441101030440c11890b1410b1090390032000c90090b0941d6403c8c00108280352021071113514282d800b80444d00050700803411200c182d032030f40444001448045401c00b00c030040d03209601c0458107201085000b9881c00a52102a0118850600c2500e01340b039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 465392769 1250 465391519 465391543
    0x3010501020d05070f021c080a0804031b0c0902070f0c06022a030a02010f0201020d0905070e0a050c0301151205091005220605060604030503070f1506030206030f040609050708 77
    0x2c4070180c1c03540605440314050600300900d20500e040003480107082c0101041708a00c080868100022001d6603041c0b850b0700030b5402038000890b001c003080b0a1580c020004961285600700d08121404591120b00c5600c089010384184681c00090a5040200e401c1108180541080c050b4143c2505c07900002e41700c3e414040241d9030304650100e519130144110304200d0a00000900825141c0980d60056602843c1c00c403a00003175550034440c9440c0e00c0c9640c01044d809034850380103003603600d043c4819804c801c80d02504e4068003910340820010038442400480781580c112580c00c11741c80384d40210443d103024400c41869400c1c4c0c20079050080c4124001036040c2e00d002802414400c507520840c01d040040e0040d412540b030512240000fa003c55280d80c4815042a0050142340c6840c2c0c030b94583c14655406010f044880c50300c000060014040802d00410f810406c000007031010b6465a000542e080c040645150050400343c004902000b0a60b0b01460823240c1c02803c1c1c0d01c0880d40d52180a48072480c0b070b052 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 465394019 1250 465392769 465392773
    0x70620033c013c140a03021c1703070504030f080c030a080103120806030607110f06092406010e010503090109020409050105010603060b0c100b132c0a02090109020d200301050102 78
    0x105081d070050188407041201002c00e0601d4080c9030020413040001308003100342d0400c003c058040050f0b199041c0b000940d034001d511502c00c4114a140254803141c0100c0088011320040c4244030445038414111411aa00090483c0d040501c0703080400b201c0c400c1441280461000055a00c0c5e95034000d90700d0750490340103c5c460b20040c490400c054032035403c120740f09903140d08401b00060615000711040e95104404808640029102c40306051a114003650942c545620192040804c041c01da044a034031255610016062410810006800c1d41c001c1744440b030500170f010000030b804040940c0445031241c0c0080003844184020304045009100078000e100009042190103d400c005030021034090049e20700051460300308484519000b0980c9018040e0b05c07428101c0340d415203203810b006401100074005040160108407211818224804901070389540e0403803d902c1c0050b984030140705e03046072010100540e41c8c40080e000c0500070401c814960301d403c10701e100030820919184000d141a25070a8003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 465395269 1250 465394019 465394079
    0x905010f0c02010e04021308070308090907020f21091903210806040c021e03041e0b030411120d02010902090601090b031503030f070620033c01 63
    0x3401c46405100400190114086040e004090b04183c0c1c0184540c064030090351484a446001e09410301c010307580705669203000410400410700d4200341ca0f5802004900081031801151080d650b101c0c00480c4000022882044554800ca81140d00311940450001d2210140481c1c1d0b0908803540d44090000380c03810320308400c00800c110b6003065040c803c503040b030301c0d20b1019a66540400002c1d14442d0004c00450003854000314921110040a140520048001d142c80e5404e01103206401500300200c2407114552aa00308004a40102100d8119410002d40410011b242e001300380e050341d070400108041d1190000b80111207030306600440701d11380708170340c14561615141d0045a85071998014001c05c440200003280e801c90343c1c061002990440641900c0c180540142031035803503001003509455407a140c103080d500d80140310403c3c503414122507040038114242402d40c04044842e4007480130400326100554201d464042031290301d600c5090a0800c0c007076841c2c04183c00e14135040c112400501e03c4400b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 465396519 1250 465395269 465395297
    0x40b07020d05070f05030706050403050409051003080f0901140a05210603030405100311040e0402130507080112150e15070302040e061c020d080c0d080103020a0302091008010c090501 80
    0x82603100807040940c0d11a400d200560b1581100d00d018040b00b00d0b820700c001c001c50307000900b0700d000d17251080e07000e0b803502910346182c0062081541c10080030441980e074848011b0000075043e10554952500c900c0d80a0f40b50070251005803000c28604c0344204c2100070100b02e02c8040c9074002c005007114200c500c0d80041e50b1010601c0900003800644000794150024407080c8443d0400d40038010800c4a00d1070081804001c0740d1010410754400d410048264480d00104029410200ca48509403034070b414007081985008075004000003418003540c885400858904818403680365146020000b2a03101001034001c041011503031030306072456918500301c079071001552941c0a8400e030703000c550610300782d0000d550324003041284112014840200196044070a0809a01c428403080c0100e445403079410703541c10802a00a19100c88101e0300020818454010700042c0c440740c0b80c1e8400c5990540d144185501c2d0100702103008003254001802940c038001401070682c0d8405440c1e42113440c203803520061040c000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 465397769 1250 465396519 465396523
    0xd061e0e010b0a0303030e1204150801060203090d060b0f280f08070306021c1509110c0c0d03030e0613212c030a1b05031c030908160b040b0702 63
    0x6014843e030310003c100303010008030380660803030f1461040c444103a031422036142901c4e035242c1d0000e03040708410004000a00302c4d0590400da186000d0030f050f0000714105941070000990b008006840200710507100c1300c0b04440e80c0c179824a0110035506c02094485080c2c22032a12042e806d6030a0303070184801501c4003000903e039400440d0401901d030034002410704a425a2100d201a501c9100c1148100e28000c64005c008200c034403a0106140d0820708c03141c855890554400b0030385250174245025007004020503030614400242003015200261007012088d07865040070b50080085012550243c041c402c100007a1601e01000440750303c3c4075140c1030384280c4500c80f0f00c0030b8003070924404c41c0200d050456500600520812603d04100c0d403e110002c1c80e041040109042030107109080f500d441c80c0703a984410b40340071185440044c26069004101d11500b400e840c03d01d007460000c100c4103055640301e500040c07010440c200c40a06400000076000e010851800011644003250252880103104001c07440079840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 465399019 1250 465397769 465397781
    0x5032e0f020d0605040e031204171207030e061005190302150d060e0c030402041a130c0908011b1409180f07030501291b010203010503100b0607060b0d061e0e01 70
    0x1a22001f141480c4411805005810000d441078490350304440c2d0740b140c0b4000a07401060380d0301e503048142145007008a00070301903030003a800107001c0c1e8100c4004c03c15140d513003032a008202d880446084502d260010301c1002c50f0101500040d410904000c610350701e0b03080d400000c2c070b04c1c204003900070815a036481e069841c0c2c80e60b0a07100c85005a0f000c201160240c030b020742004d04070446013079a03c41810540c50008445001040035104901e4a560b84400300c290050392071030050840000900101c0c7c4100304001c480703480b450701902071080c188648006014000c043c1d41280c100904810b100d821038010031142c601003210b01c0101ca013807590006107414824000c41d030483e0b62444100048841e02d0b21002400030310891603da000300e080c0700100450103501e03040704404448200040c1e03254102000e06091000300c2d0200c000140c01d01400e821941ca50408468040e42c1103480000c10314002400110015000744002d04107608100d00b0b10b10b014003078401c04001006000c82048600c2c50380010600b0ba0301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 465400269 1250 465399019 465399041
    0xc02160b0f0927060102010b0d330c120606030e0703020f040e071d1008030913140a0f0605040c082d090706081005032e0f020d060504 59
    0x2109101a00e907049011025244040e00209103001c904850000d40d00c0849401c0031603401c02d080c450034010700b03580a1160003031240003070714080c50740140c54480a0f0b81002a00c40a60700c01c240c51400c1d10120030600c202c100803c0000014000b010206000424440c01510401801e910300080021894001d20400c0007981c0380a002d00301d02840c503002c019411103403c4c485508142c5a00070500014424008000605605414a0512030000d80074802114000700302441c00c100d441c00a01c0303200000420b03546007000803500340901d0050a1224000303006141c101c08043c2e560201800301e03106a50b04600311111000300104a80c0340c2d280108019680341d120040007080510010826140c0d40f1081c00d0010503104d8201c059003103100303260b1455440304031624a8070390403180f0f052080a5200a030107800015610342c4c0902c0c41e00309000241c483e041c3d9550114140c0080380d5044003506c0c052181c0d844012144000c1100c0041da404141c041d42c1700319901150b1030303c1c15001107403c0c0380c00d01c250003042d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 465401519 1250 465400269 465400289
    0x7050a060b0f1f0e190311120604120c2306060f0f041503080f040e06030303100506070501111903151d09010e0a060c02060901060612200d0c0216 64
    0x54900d0ba05850a00401c3e1000080080703500162a59484074803540000d44415030b0502e80c2c0303525600740200403100b10302000d44aa940d07410303515000c01000514030b802070b4220a40e40e0384241105030a440c21100614002d03c422461150242814100a038010720304004001b9245140d59034010000c40c1040c1400d02688031170446110600d5041c9036201c00b06040c15440f40c4c80410343c4a80b00c00802e034011300080429010006024488400e40d40d4211342c00400c117400a6045061070311900d65a818a8041c2c03a014800c00f042181c180002508412030395400d10140311b0340e54541c01e00c1c2caa820341601131158003007824000c0d51400c15100c0494542103440c3c0d1aa00c00012410b80901206c3d03850141c405403240d2340399008003650541c14170102e50400c1c030802d0002001c160646000e410420024070b80d24059160031002c000c1c01da003000c814981c8100199000503080c465071542d240d40c01048152602865000c03030b4001c00c0140030352249486102a03022145001201000210f11001c03a000e290800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 465402769 1250 465401519 465401539
    0x70b0418090f05010b0a060e0609040513060c031d07030b220602040608010e0f040b04030f020f15270705041121160926010e0307050a060b0f 62
    0x81a040c042615180c280600100e8480344588407500c549000c4541540c01e6550340156100c0d0b4075041100c48002e080d41e00307001000081200000d0704a0081c0c8400c54095601d64002400300d24449540d65015a40301c1402c12982c080c60400030000e040c2c03010283d148686021070b6121080c000503c09003166030000c030b8824030344e4a46410241e500c240c049403064607036242480c040011722038000b070800f034140c03035031600b101d589000c00110500401900e861009410041800089024140019885500350401c07000104100108901c4c00c03110318050074003409105558a40c0c48841e15502e80115854501c0701800041c80d00360700e01035100f81c0201d0400350700454041007079082503044456510030402d8158145101c0c40c1310b1005c40020b01a44482503c42542084284c240c00c500c1d11034088040e01e801d05850341000780312003a0703040d00000044450600c88100004900075008100103044040550f80c681a840c03605e5566040301c500c0407640300781000c0c41c1c40c080d4240303000d00c50303e00403000305201c040d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 465404019 1250 465402769 465402779
    0x612020a120f020d0311010501150f0305070513030f06051501020706080903040e011502070f051e0402041208120603060f060409051002040f050f0a05210307020306070503010611070b04 81
    0xc0c0251110708035100e000641e14072026980d8000b41415281c0240c45585926255540781421030308160030070140c0000051458646503840100c0820700031050400003010340304c6000075595400386804210b060744c40b60301c010003049126811020f6440c4600c905003c0350310b450800100c0c601c00c0031307001401070f400700c0802c00c015442a4500b54025000605491800d501d42680e18520042608044107280030150820100b40c2d041000800500c03147c901c59030007900301400038951905004401803006450700030440c2c1035841d40e04560042c40f2103400a4050001498580101c0c1c2054116050ba60031030300000702c0e01d040118101c0d10480400c0c0381d00300381e6640c1c2c20800c4010404982c3c02e813100e101c5c0712848112803a1520041014050202003840124070b80003c220460154800f5035000341c0964404211685401441102607220755003a03101c04108016044e18600682c000a58541300d0f80d0f051002c1c0079000340003141695803544c1e514055003400054296200103603c581100b483d002c220400c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 465405269 1250 465404019 465404039
    0x3090a02130b03031308150c030c0a02011526030406080a092f030d23070314120109110313260309061f0f09021c09050106090612020a 59
    0x301c003121041c00080e5480808022925580000d603201203440c98440082c02424010812442c0e0034040741c81703485c19403501801c100a28040640084000c04001c9000304009000790058880708030803c000f40c20341552000f5180b084030300310040030f502c00c11030401340401010100403101526003d40764100981c881d070607907100801b5112401c2d506603900c441c00c0c40d9a10100801d1140e1200320844140c086541c4004160400c1e000c20003020501080964611b035064020350300481030411407080300d0315007040b82401d690481c030f81c0360b0391a5042c100003401d42910440039610b6040c2d0700c20107010080490651030903551440241c0340340c40c00704900d041d664009950501c0b10094181940140c06440340c468004e91a41d41050382c003550f031500000d04008421600301407504920103c807034003801441c0707400c900110400e032030300404092980000e410380d244001280744504401d00078408000b10309044c100540201002e006811482e0f0804c0c4000079400300010986a140b60001c00e54080d080c134184c5d20380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 465406519 1250 465405269 465405289
    0xb090103060302031b0306070318020f180a0504031404030b040b0c0c07030302010e0c030109082d041202040c08010501121a1507060506060a12020a0e04060f0f0b03090a02 75
    0x150400d9160302010006803004d00440b400644171803480d940c0d0500043c05c01d400c00e500104540201071800c603000348100714002c0c80035400b58042e29800b51411007036001c01c88080284050541c0741c0365460130703c508003d9543c042840f55000307070303030b40131960319480c1c0100e80c01d00c0b40344009807500075000040360100f428100699003242ca00090f00c0d00e03244076400c8081c2042c4c05039206030090b0355038041c440324110b81800b1184440740304030020018403003250745e000303a50300480e0440c1510700c8104072082d62403948640821380340c4880c01142601c4598a01d03c2c240132110b8901c0c224080c0d41050a8000c003240074015a034141c541c161600d410f420600c80030344000741204014a8040d00f526184604079849518090f110013001c0d45002c4e035200d000b41003c0d01074031000303807065000380c40400850781640c0e4409151148500507860260f955030500c0c030704580f50341040e0f600071b5010f841c004001401e07444095001301202c4160310003100a56650b81701c0103090004803810b00321a001001c0e00e10041c03030120401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 465407769 1250 465406519 465406537
    0xc180f1823010902130902040b0a050307030b04090f060e150601030c05070f080403051207120c0203010b0901080706090f0b091c0f0b01060909090c0333020904180c0b 73
    0x4084901c2890002181d000c0e8000d030445540000c0009120182c540300d800500314079042940741614104028101d4842c0d02640c9082000101c04107245030300c60f8001c0e050420008109214248890034420b04d13540340000d0445001d07181081d40201030502140015200292041142e6140e49000055000d0000300c0310210070071008001c1354001408600c0c0010035280102c1c0f006e80c54605510342186407401c0d101000003040c109010080000c6c035000d0600c030082081786084d050800caa4808207024100010445500040040021400340800138040046800940d14403204a584484060081344240240458100108690801c41c2082e548449010b12903500c00e8560398519214107036080c0036000101ca80f006040c3c0100710056010046401030920440b00704451403940d901c0c91001078582c44000c101c1428502c4c4804140c0e840303120001c01c002006180381243c1840c000920085d4030240c41580f09074903190805107020107903081c001460340d20a0380701910a007058455803c9030801c4d000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 465409019 1250 465407769 465407801
    0x50a030207050f07080f0a05030421080a031401050a0e06061b03031f060e130506120307030e1203030405031b03091e280501030207080c010c180f18 65
    0x41c00907404010f580c0c1d400d0581c2d0060010036040559403800e141420003c4540c6511a4080b14003252021003110202c0e040301c0345043c00150781d001000d0841ea001980075002003004940b00001c035070141c112900710082100c401405070b0300d590400c0347e1300126028a240c4560755000003000303401c0c208014084c458040074000c1c98281c1c0c0e007200b41c5c034640c000c4440711403805414882d041400c0424850f50060103d03400d0100c3c000710b4200c0460606a00381c1c44c090750540c0c480c00401d0894030381c201509400766106060302e58849107801c0260202f0b400e8030a6500440036050043d0380b000c0080300341c9004650000155181400780103001e6940107040c0e44c4000700b4081040b6602c01c41e5100c075041d2a0035a004183c113058035440038108900007035072002c0c054610401e030440203021100e040000040d90000d00f0016280c4000f41006020344c058945840c0c020340c80e00300300040c2c564000d281c1010b820400c18030180060f4071000ca4094183c490711400c10314149510050684081c1500400d010605101d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 465410269 1250 465409019 465409027
    0xd050c0712050304030605071b081309020d02121303051b010e03032805010302130c0905060304060510060e030319020a051e0106060e060304020108190207050c090a0903090501050a0302 81
    0x600c604101d0488900300c0c0c0a52000070300b0010001140682644074401c0d00f091064010349416002120b8006040204440c4000941c804a403d43c4000b2a01074489010b0441d2108080d0400744025446181c0c920510481800090600c0c0344400b207941d0b400354103645403403c1400c1d041e0a5070381ca03030300312150749015500c804a0701104c1500f0000f4500c20074000e01074070600c000d00d2000c0f401c2c4143d200c500a25840c2080d0050016840e0b00c41401b11002002c0d60005c0e0910365100300b00e40740943c6400036988150000709000511a10360490b13170240011000e1070040540d10403041d580406000411501a0402c0c008103034440c082c1e150345134541e8294015074201040642d00c490901c500c0001c001d02010030025101050007091040034050082c3c2d0400301c1e00b44401400142c150301000348020b0400000380000b40025a0010780d030218654025001c0d0b4560510f03282c9a612003040b108030794094a11140050005a000e000346030035035070561140445582040011a010381c40764500c2814980c00300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 465411519 1250 465410269 465410279
    0x110f16021309110108090606010c02060d0f0204120308060603042a0302030a030f02061602060109050903070210081608150103091121060601050415050325020d0806120d050c07 77
    0x8064044020f1245490954554024001609440707003e0703c2d440c3c079a4001c804002e0310f660080f070002c4a154041701c4058894500b041084050f1011807550303c15280040307400500228000b510720070240c0310342c850341c81a5a40c1c8081c0314170f0340011100a0540c40c01d8240c84482d116980c900e4000e540303407400c0321121060310b03500440d00d0908160300460003d00d8074000440d0135541440b0960700000c881c111840f8518003410003e50b9000d040c0038255440359170b0808a9040e001c10000c4411b099809003170a000d0302407100016004000454401c0301d80c1013040c40c41c0203124821407030701e0702c20405a0508440402d8a200460007080401802c075152840000b003800f0940d01c1156180e0003905800c054064240c03c50809402c025014010a05100d0107005c1400a416180041841c1580030b1510300e883c1d81d145030355600211000703071841010451111807000036503408501c0c2002c03600c2c0c9441340c1c611915600c05000c3d410305c2e003005411182d0824125030700081d05ca58011f141c5012440211a083c82d158 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 465412769 1250 465411519 465411521
    0x30a02120f04091a130501180b1207061d040605130506010e060f13080a0f0228090212070216060c020117010923101a0706050a02090103110f160213 65
    0x7095010040c0030350b050070380301c1703180c10113120a95241d105014070a0394504408104000122105200515100e0600b59100e4407448403036005030000c1800c136010360743c1c1c1d890094040950709450741500d0640032456001800c1501480b002c988016082e5203c24024042060042c0f601400c214104080e0341248d6085036540f10281031610300d841d2440784e0350402c0b0503112240c00041c3e800075415170025010a00442d048101c52008250103882c3c0d007000504041c00141a107006000e00404040040fa0100d42c40007154060201030f40640340d0115141c0700c4003000d07079031130703030503150f0300103400c0350307481d050003080c0c814007d85d482c503031040c1044029514000880c0400c49001d80083d5400360740d0f4a150000803c0c681c0448940d003001d99824441d0b81080e03203020201c26183d0051a60011043c0c0700c0301440c40081d02110b908a820010400460918410034070285d80082182800607040c000010f164060000403210f54040fa103a419191120f10071501d8400c10354081d0a0364040401c00c004103203041c43e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 465414019 1250 465412769 465412781
    0x604020927070f1406090f22050f07170a110c0a0803100605040b0a1d12060402010906030c021b0414040501020306011b0209061909110903010608030a02120f0409 71
    0x19480a00116401c0c06556610030b0700c01c0e4448141c003203000900700034a464170030455521040540349202040d800030301080b030300c00c51030801c400300420560046260400542c0000c1c02806d10310707d90944c94941901c104c0d68610502c0b400d1840d000e40c0008141e8007411540040168040c031141e4506040301c141145080c8064654151990b0500104210072450b0440c072200160400e414217904050070310a014a045c095070407480184040520080800907103c602d142602100030011450f01003407a584544034041603800702d0205544a0000c00c0560082c010400300341c440b94010141c40c1002214984600e0b440101181c000e07648056040510420203003081c400ca01900002d07a490030300c2030004100303280704030281c104904c2d400c50000c01a0364138a44180c1120084922043e060b0790114607400c134004c5c5030b0110340202c0c9000c0030b0914203a20480905040e00046008202e202d0b80c0300740751500c0340310380800c820041c2c00020b4259a60319526000d4142c881030b403440d6a0900351108400c904540f8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 465415269 1250 465414019 465414091
    0x9010608151501080112030309080d09050f07060e1320030c0315030a02090403122d0b0414060904030c0b1005040e010b061e0913050907061106040209 66
    0x341c1000c10024600c10000e55603a401d084c41c1c5140c0a600d060b000100fa440f0070500101050f4591518030140a5034a0668008541c01081003080c100203280c8155144040e00b52f2030300314000e9401c00180140910b03803100e00618082d01c140a000d10340b55485c0020b200c4ac5100c2c2d4404518405e01a01c54201540950311a040b1500140d0344c90500511307900808400e685005c6c842e03840f4120441c016250b880d00c16805c55418107050742040d840f29040302c094581e214010030213585020541c2c1021f411890466038843e551982007100d1111201072000b515618120b140c0380c0e100000c04244682054510994002d0003071401e0001c0e040181c0e2490703140300f07003582e80c0c0c1c0004100308d07014095072a15118140150b000c0700c0007003001d032100320301040950060b03034505000d14120f03502da186100134000481e000a04001c141c8940240c84141e41c8000b840240e860f00418403981d400480c0c5280a1000c20103040404030040405940b1139080001415006184803810203101800da0408480c010085034504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 465416519 1250 465415269 465415303
    0x50f0f0a08010b070203030a1d1201020301090b060f0f07030203300105030a0c1a1c0f050f010806040f080403021e0909030406080115050c0607031b050901050d0509010608 75
    0xe00c94020050048806030044520480e041102c0001a07400000f102c5070695a8240a406401050140d0038070002c11841d10b60442400031940e2100c00040d1f0046040e104036007410051a0b030020f00f446000e000308030880790f01040070003401e030b55401c041c0003501416100c0c4c41200d19005250f10b80d04150149410051201c0c840602c0c540103448201006601404098000b0801d080b0207071a29500c1580301c0c801c90110006100c00021b11500e10030494840c40c2c0140760801c1d0400c400070780346c40105401101025654500804200140360b1084018100c070b400400801c1942c6943d00c03001500158641c0468000c03904110003c01600e416801d07511115400c105c50008000303140c20311001040040614150390800c010501000350048400c03815980d0070303030342906d440d0003446050300c4031720a1180304012803158004014a05906412109031100c007908030040300c01103810141e07000c0c040c05c0d9049020883c01e2001d404013203241ea00465000c0d07071040010800d1540c510360383c0d0804407120703441801c2d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 465417769 1250 465416519 465416527
    0xb0306061606062108090405070207090606020624030706052118010b0913030804300201200403020609030114190e15040807110406090b03010c030921050f0f 69
    0x48858038846982e9413501c084102884441641c1d40841c51150010940c4116500d00214000034420807181c00501000c1c0000c00100b51070300b1020b99110400c8900b5030303100c296100d8112810f4042c01007401c02120103070040c1062410060103440301c2c2c21142c03600c000405500c07404443d0410040006008240030510b0001c83c081217040b01d070a5803c20740d07009003c0d41012041c0460046a02c2c0c110460a405180800c59510bc1e0b24020318102c1d60a07a1150401c800c21103040e1802c060b4441003081a0902e8000700405492001c40c2c0a0909400c20750102d003e60030701080000d400c00c9802040041740060002803180300e00d42b41e030040c00d0010b4645031031106d44154001610b00a0b4407a1004142c55000280040e04000004042000008100915039100800d46004100c2c1010005814010051050111540310000107004246c4820124465030901107104801ca01a01c68034a2040d04407544065054904054002140802e4541000c21000f00b0030700640d00c900c0310140c8200b00308000801e0365 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 465419019 1250 465417769 465417779
    0x8010b160c0f15080402090105010e010e0402040303081e0405030d0c0e030f0106090b0a0312200105070216211e1e21050909040c08060a0609050702070501090b030606160606 76
    0x24081610316003c00303105019041c0400342c1e5030403040c81c2c1190402d00e0300044554141e80100c40400c0d40703401444d0003c0c00818080101508405814414a07042e29001d010501b10065000841c1c1c0948001e0055081045044503002070b42e000a600c444090811290015003000480c1c9020000d0b131700c0b850070382d542e2001071010164038041d0071011107007180d043c017443e0708607114040c103800080070540600c0140001c0441504c44481202c1001510034000c22a910f000070b0040d407200035104541e15110884500410f094401c4a08414410503518031107090020941d5203003165000c11056610000b1302d0300410000640007201004102980d5418240d0310f4010f1620b0b400f58550b400d0543e08400c002d04000302d415034881c0030386072014000c8901075000c2c1c81f14208180b0004454128000501601c1c01b0091940d40541201c801c80300c52000800040e80da855080741c0f149a103000b407900241003100c0410202600c840610780040780200302614184a074031001c1c40c0d08000348d8048803000e86580701008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 465420269 1250 465419019 465419039
    0xc0302120f01060b0408060105040f1404050f3d02040f1806380421030206090f10090501020d0c110d0e1f020c100c05070b0a08010b160c0f 61
    0x10090012004c0300303007064200306800303488900501405014a5036080455003c00054116104200444030700d0403150070a07041c015182c545104a03000030f40f084040a15503005054143c07403d9100c41107000f214103c811142e46880e01d00c45003900ca00c0f5400f400b0209a4204060445d0000c0400d8403450312200c0c0340a03242c4007601c01a5110344080c4180a180c02040452080c45501440c0d812125280c0800c00c1d041f00140b130b00581e04055000704a40b40318107103500642c4070b0076102d94001e800f1200c2035a54401c1140c2c1d1138809210402c5240c0000b10501071041c03490300810103082c4564005030a21700c031040d5403400c954a005090001411701064080c48403400c0c0480f1100c501107207010035000d1843d202040c04944a196400480c01a100326403160303600c28040440c44410081c80c41040c0201c0002c018195003480c00d042c5c0f20340c06210000114030707003000b040340c40a078010b4440301440ea1904245001c81d4205000d40300740d503508a500d090015031105402c90203018014200c0c3c04440c201800340d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 465421519 1250 465420269 465420281
    0x31e090a210509062d07061a1e0a091b080708060d1106071b18022719060f17040c0506090d02040603140f0a0c120c0302120f01 56
    0x401041000d100c1d0340c510340d8040201c5071066015034000e0f507200341e0030285400003111100d031841e101c502c80e001804030103e050010000c241c0561300c10702c1605801800c1a461092071101703268030581013009900e00e01404004040d4905000304110245990b0341404420717105120034075042d40b441c0c119005503080c0c021040a800c03003541d18241d4103070300d08680401d166003a003ea0107400b80703014560742141542c540007111200b5a1005100c62600092030741c01460319124041c2400c02c18900020108454841c8203440c00715003a0110304a01e4902c8044184000901f400f0030713038210aa42d5009032000550903085002041c135542e582c440f490719050000c040c81c420000d0719000400b90000d04c00807903691600c000a4400840740c9565444842000035206440d425000350450b09015001041c80001d247c10600c40000e2416207442e002d5980b0400d0301c0e501c40f800020035000c00210700b486000304c00f6080001043c4151540e51103641c03250000340200082603c880301c640c1c03110b559800c000300213000709 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 465422769 1250 465421519 465421553
    0x5010306090b090303010e0103080d1118100c050a140102070b011401020709061202090903041a0705060907031a0403032705010608061003080306030a0c150e06070b010b031e090a 78
    0x13031070655041c009907655440061002a207815004110404841a039a10210140302d80f00581661001c44007201100c01c5400a040b9100d00f014810881e110740c0940f001c0410550b2240151940d1582d941d81c5100015040400d0300c06994240000800a82e0000300f8a01030a001c02d4079110382036107840020714010711600b00c0720503141803600402040541ca01c0b140b03d4564100c0d401c4e0b020b5034610498030302d1405158000700380080c00103120300362001e0b0000104544c5001d4016100c10f80d40f500c82c440c5e43e03100030344001032180c80c040140307907402543c110300c03290480d1080c60040b6031164210880c02d0b15007540711001040c4400c9450072810094248110002041da10b00648a1840e107202080d094124503c009840254008002040b9540500100016591007160941e009441c0c00c015601888090b141e0004908080e80c0d410319440d01d4802c0c0c580391944688101400d070308100c1e03101843e400180100c400004c0c4032143c50b41201c03170100500d20484010f80108080c51041c10143d100040c040c181c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 465424019 1250 465422769 465422773
    0x4062114150111060c091503070e010513030c141c0302030904092315010902090d080a0201022127060f060d080309010b010f03020c15130605010306090b09 68
    0x48035a440c000004590101031802400120030350800180e8049030300444181090165104001d4403801c0314018100c500c030203482050b03640d040b0940c041d9241c401901c1d03803130110300031200d05120382d0710900050048140800c00500c040c1e9076503407107203024640d541008050705040041b90400c3c1c1003012900240c03894890612115003c41d8601a440f445401c010f90f001d542c0f07480720841070165201100300e58180154181c4c13840d440080b501030711510b000d104220303403441d80c1c0c0000401e5040ca0003500d44000004dc0305198050040d42c402502d540801d41c44000d65409200c850180071420514410b40c00c80d5200c42c00240c601048480764402c882e04a00c0201403c6030007040f840381c000602d1551221900b540c40318030340c88801c0060070b044410280103041520000421001036419001400c03a03840030380707440e40540031280c01030702a8040d80300c60300d141c2d90006040d80301c070078007400035582c00c001c0494900e10403240343e4440754181e440981056801d207440c0c0021000300611010b18661003420440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 465425269 1250 465424019 465424031
    0x403020111010507080f060f1f02011803090605030417130503100c09030b090a3905090a0c1110090c0b0c120304031701060e28050d0512040621 63
    0x900075080c41000340006c040144000001202d5403146081d80700190001410404e1440304810411142c0300c011850b40019400d2000605101c2103c080000c0c02c2c43e41610360440041c01c154084030305400013841902c3c94040310708280f51141440c0700624071040020a81120b080c2054185031810f40c15102d0800100d1514150001340c40c2d0086603482540e034424444161500e80c2059580340204c01480a4104074200b01c0034081c01c40e01340c1e092034055800e600c0010201e408940c5000080c4c150b88140f45d0040314820018610a02d60340c41802d00d0305890800c0d40000f086008202c0c94440c610a040850660303844486042c4400c1019400080060750070035803034499011100d686500b410f0320886e00814000c4042070400d4011148980050304105030107640d90303900c28008001001b10350b031040c000d50b261948071280001b0300e42070a402c0c542080b006420946060244070815198031000c4d030301c030f00032401c0c41c01c540c650010052005048941c1c810b40702c07503100c02000117402e02c4034200c01030301c6241903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 465426519 1250 465425269 465425281
    0x4051206040606061e030905010b04020a090f060305011a030402010201060b03090f0715090303050703030f0906020d0c030b060a0f0216080607080717060402030406140a020414180105090c130b04030201110105 91
    0x81c00c02d080345c030b20701e0007045224891404038090500000b074146d1013030000c00c8201da184c1e4400380602c00c035410300c01c0002300706a407981e041d4111a028041c2c6284407100c100507200c0041a0b40045030000d10601c00020341a680f403460304400d80055801c401c60346c10810380c00c0803441080081001170041c4040d40110b060400d90b025110319002e200040034004085008020701d4041e6000e44100303804090148120780d83d5140150080d80415200003c0b03510f801c00808120344248181001004003030400d0b4030b4608008425074641081500543c21441a012a2010145000003110003011024010314450800c2c0f03402811079000180104100807192042c01e60005588188076000202500c0040c1d4a44490a0040c094040c0307001070303600c4003041d04c14040d0050300d82c0d0081040b50101040c0c2c0219405500c1004158020070001c0303a0310045981c0103000d0340c501040165007003419040035500d041c2c510155823900c10803940c06400040c001090410955822602110701c014080e4000c00040c6005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 465427769 1250 465426519 465426557
    0x10c08090a020d050f100b1005090906042c0a0311060c0d020a0306091b020c0f0f061605060a06060801060503091009081e040306060515030a110405120604060606 71
    0x608064850f4400084000034040c00b401040312095901040d5925185502031542c090030350038138960700403500b2100070800e0a00c15000e03200c00d804010a00040b0352500300401c40075004054040c1e005540c08500004000447e401325a451951003014100c1c0d0403541c10003810f482c1c0f00c0f1040f8051074218400300003001190600310380b10039004420041c2c59a0712000304800802d99900035210061801001c18100040d54840c044003290a40c2154082d100c0a41072001d02c1e50b01c0100c0d250010010f002d101820315014000e4110107609802040100886842e1145003010503519000540d0b41e07404244101c5901c5905603000d0405410111301d1403c1441070703581e031070061100502040e5510f800003020440650119580106041070718014285a4655400130354814801140c0b590710300000001c1d24200000a0304002c01d4451070581955103006462019280c90407041080c07141c2004013180e5561011807401c1d0504003000103280e945050b241000c01c41d00b42d5007140c030074407100700c84091004a038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 465429019 1250 465427769 465427783
    0x19031d090c0a120612050a0c050307061d0d0204060312030f09151a100905040e0109050d050310080a1227050d0215030c0c1005040f02010309020f0a0611010c0809 71
    0x2840c5012083c100700c0c0d0790040014029034101110910341c40d0220810703c200060340c101058000c2d840000b80d07580d03400415983d8211403054034041400681594504c1685507a009421000a000700914200a500040c2100c071150011501600e181e80b66900c0780354188100343c04424031800420181034562140807107041d10750340e074480ca262580800004242c3e5040c9000079060f001d441c02800320203241c80a0420f03035072401214000c3c1c1c6800900d4184c039105009008855030400b014002d00c1442010840c3e07140e10003804040413219410000440d403000304464801039000f21081d8061804c4002e000700028441c0906800809000e250f0303000c1c1044818080017215422030f1900f242c584684085824501580d0381e1103042c03d404010085c00029210050200c401e911080c2da158841f01d00c208002ca136420340340584809d240041c080010350103076224807200c50009008070304510a07a400541d0481c8190000c10000e0740ca40c0a007a66040240a0b010030315030503040c0512285044100300c1d03030b1348030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 465430269 1250 465429019 465429037
    0x6020a1509030c06050a0203070e010c0c0b0f0c0706030221060a0b03060d020315040201020f1b01120204030813090e0c1e2403100b03131419031d090c 66
    0x40c1d281c1c1e0200c2014062030000070307260f0344880144250325090b80142c001b900f08440c55400300d200c481452407198840c000703407691244d004032074603082400e003112440d507900016003251892208014000d0b41010412a86004140e9607602581d50021180d100008440301000e24146188510910456980e0f01c403822007074400e060030080e260f541c0c0c0400102104890040a9011300a03020759601c5600034000b120b10032030003a005c071480c06008240d050382c1c510110b11a040900000c03041e9007030351340c80780c031280f904184e86150150034130761280c84a003180e6015030046000030729101420031141109004850948507042e001d8241402c2000100d48a08020328492002c07a01e14480100290340c0d0402411200c2402100050f00544011503c0c1c500c0d807050b20510111361303a038030300042c6040800007142e210380c41c2a4007044000710300e643c9076402c4c041103002c90b0b0181c4c01810a8101e17820320707418105500074080d540b086800d080c0341d1180d000071b1102e01091805001007504004c120820b040403945480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 465431519 1250 465430269 465430271
    0x6080d03020a051902011d061806060a060806210102090306090f0c13110f1b0c0f01361406120f040c03020a09090b070809100207050102090301020a020102040f06020a15 74
    0x40c1100d1300301c2c0180103d40075030303403006080b1000c01a5101d0000d1442c0c031800100410707207210f00d2000346140c0c0d2000c0c121400c1d94022940c4030b00b4001c3c2840b405086412110142072030401100c824a00355030150408100c0700169400f00720140c0c0c0d40307010800e02e41c00c0070040300940740c0b40c405030004603100d0070030021480c01140900200c40d42c154103a4045917541014884954036001c0d20b0f41040e10980c00031612180205650420b0445031a02050041d00540014484a1b8241700070005580d00c1c1201101d4900709130f51288001440030884010389424044401160403a908084074001d040104920740e030700441b414000f10a9291041491540141c1c40d0b000350541541d491402e1000808030b071700300030b420114100780003074220841d404c500e020500c1030141807510390f1240011512400101c403c41480c1d4040410400440c200782e00519043e0b00410015182c84041c001081c2686c2c02070701c451006070740c00076003085662544100c41010f0061413000d0000e15001d83c40d601c1204100150580d040b07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 465432769 1250 465431519 465431557
    0xa030c0b0a0e06070b0105090133020f0a03090501090608040b0c09130911090c09090619090905150c0c03071e231006050117070c020a0906080d03020a05 67
    0x20314002e510840056900811082e070344c000d04e1070328400d1a030080c0b003114010b44840c2d00200700400526242c3c0c102c5200d0341e603440610002403180c000d14138044d080e040c7c01d50090358119001010213201504459000352110240a0b2406000500100003a0301075010081c59406000000d030001c110340b40c01c202e10550003903c403030b03400d0300040d0006079000e00d080c02d003854400424100107400540841c4144125001359055407219030000c42c0307120341c07000646d0004500700094128a4856071290001880b1845040700c3ea0702c0b060088100ca01c40340051740e0b10343c4601032140c02c02c1c142c10107555004104a08050801031490003140d07403400b84000c02009a0313144442082841151800034079400e402c9110318090320f8100c00c0c0e00068055064200d09140200018071500342501c0c081da4040307802c1170390ba440441c040310200808100010341042c040000c42d40310399001d81c0e9140120320140041400c0019500d207007440c1c051138802800300820525005010206c0e0498214003641d030008141c0f88202c0c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 465434019 1250 465432769 465432787
    0x10e03031b0f03071106160203071523011503020c071503090606090f0b0a0620010e0d080a0605011805011808030a1206050406030c0302060f1608030f060a030c0b 71
    0x75014441681125020200c10481003550041c0490241851902a552640c649081d40c038110304000c001003025034010030603280081d003514602090180f48110003d503100341d481c0c05514a0354a1418070000c94900b0340140302040441c040100c188501e8282185401101624030350ae5000c07600c2080d003500302400c81500400d002e500302d076001c113a1040c410480300e502c03084000b0007003c007012980da100c6d00e07040d131141d003a0910307034910300541d403080d111410030303c5403602400a01043c035103083c13009548510119511290410500700d800956845401c56494040440d0040b900607034001030411405641451110703407520040003d030391003032030f205121100f01c81c60014490b20700ea005c0500351000140307014131140e200040940c0140010018045c20365144108001d0340d15074080a0100c540c0600e0400051802e64024202461800c0c0c50f68249080d12074064011501c400e8250f44d40300001040001c046030a10845901000880f8034207000c9003152184003031029940a176600f100400582401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 465435269 1250 465434019 465434071
    0x80d030213141c210c120305040b0606130503030a020c0108090309100c02040b180601090b1e070c0e01090603020a090515100c0c17011b020a0204021c0513110102010e0303 75
    0x104c4034141d000c00c10340d401d4482ca00286009207002c01510301881c12071044801782e219016a0703005640040b51184246c8401042002d141e110007004101590751102c0090103480c140083c0400d03517115000741c80100202c4002601004000b070040ca699041003044808070b646800309852000e0082c54070402020052005c180140701003541650b1083c034224484c000e20200411051247c2d00a0341e0308103000d40d40b140e682140b8040c800c0c0450000000c2d4020154001900000e0075000780244400a9100c3ea94449104001020703044152150744038034013031085d400c04400100c02003003030003c200110314154007045004107146d40698491f0f2550001e4400040c810380300c0d82c3e00f03560402c06d4000c80d983d40d00545500c100301e07255031140f50b5080032401c1c0d098441081610916900c2074014014a071202c0c0e08000c000d600104140840303079814101c0a1800499114251044034001408070002e0f0040c200580810100b2403800d045a05080400000d0320010065070b4000410070310500c1e54040500d1190303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 465436519 1250 465435269 465435293
    0x90b030403030b2232090a140105100b0a1b06020c1906050703200310090c021f0203150f0d0b0c030103110d08030f0709080d030213141c 60
    0x103520190004c1004000016102d41100c181202130007049442d640c41920b25007103960311702d4542aa01e81c0b0a44c06821017400c070043d58845882c000391115040070360b503803074941d0003803281c011000c0e907450040001000706c24044101030011262200d051410803803004020018210b8250b48014074031100204001c5103805640f8841500c1d015a2100c0c0010360280100c000a0b510139a4014104030101728402e00034030400400c501403514150401c0c503451003212013507001600601c90340003092400152090070b0311500080c10843d9001d0300c200e4240b0010343c1d501c1803100220042c001e1041060001004c4060000c5054076000c1d514183c10003481c1e0000b4103403081c6050090000c880c2d00c01000b060540510085040c0d91160703544c4a40c41000e2418010147e41b82c01c13006000110420200381c000c0c1c0071001060340110280f61140c44151560941410300188540d5840441d8001c44d4607000f007000140c2060140503115481790300031044000060741180b021100001050003d4241410720443c05141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 465437769 1250 465436519 465436541
    0xb0d0209010207031e15050106020616050c06011d09070b03010510020a02031005090f03040e040809030f0f0f0d080610030b031213060305070302090f10020a06091101080c0a090b03040303 82
    0x2c0d403042c41e8003580005601c3c100105c2281e4a8501013402604841984100c9050b611164020b2015a560112580c0703140006410783d02400018048141c03110b01c1003140074042c1410380b031301d200201c03403d4984041c030940107061082e050300038960074400003000c10b0a89044540480b41030950171400c1d00142e040c100c150b40c000e90140504002c0440c0c1d8902504024041d440520850f081100c0c1c01c080305440e4042e600840c0d44d8511403402280108405002501c6207600043c01e84802e50b80c000100d51800344546020b403190b4015210501c1001c03010b0040003141481400d280d103507031520381c0029100b00c51401c1280c040c1940c8040c41c07441030301c0412680000c80c403c4600d640c1d55a0b1100c0b20350002d020580301d40c200217820100087e42c03a030310038003c0e2180301c08050040e0201d12040c1c800c100c1020740b540018011441181d2119000c604203000b154900790150f044400004110400100801750003407141c0f0800c1000c110200c8055482a8100225044103180c039849844528045002e02661000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 465439019 1250 465437769 465437783
    0x30a08090d0507080a050705090906270a0f1e030e06070303021614070902090f0d02040e0d0e030601060e010237050d0909061d0a020d06030b040515010b0d020901020703 74
    0xf000c00c0d001302c00591148001e000310200c07040d6603074a80401080d0041140d0000340c503001080440c902801c00031400d00013081c030784072a207071480c8501003442c80c04122003003d80d0000d4007071400c0340a110340281d908071081c5021002111901040d1405000c40301d0140016008030350020303403141407500c0799059031071900d038140e0b03410307500300c485c1c2880c0c1510045403e0181c19801000c100040094051084804026014001c14140c2c0c1d15401045003110f0000816600130b0307100ca40c20987c080007440b40245001c019180d51821081d564241840c014050700b01c5010712006040c0144640e070005801c84a91460124401a01c000c1d50003003044401c2c04e806490001c898451164208074010800c429400500c0d950001c01c2c030f5036140d01c101500c48920940c102001c40d01c1c5001c100500015010343d10071820780c8090719004540608130215501070740251200480d00f020b00c010000180640601c03503050940344102541441c00704003161003242450358410340d00103404500399000b0710108004542000c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 465440269 1250 465439019 465439033
    0x30c0d05070f080c0a0f180929030a02030616030e19051005010609050105130b040311030f0115121a04030509100c0b010605071e081207020c030a08090d05 68
    0x103010b441d0485115160001c2080340002511024082054400c0340740d080d6111030b1604200d54003500d03d500444d045180079281d0b0140800d821000d80a00d0400440400030b001000510f03c0001d0040682c25038100d10036013100d95a0800b44e80c00080854028107015010314180d659410194010003030f640e8000424010f042c400380040030800382e0119154065000d4640c00e031014003d40040720424004d650100304c071030900380001e502c140080c00d01900b94812000ea0340d92254002551600917501c11980324400e00c87c52803031070400f4040e5443d4104004024000c50b00900c4030710010300094094440428a000000350a114542005070707140450060b8245240c00e1500b00181550300c907452041c001e816456a09825500c100c00056120b50002040c0d100c0d642031010444440c2e210b51001d4440428805400c1050061001d0310010707144503002c0c0c1607907078a40101d4446840d000805100a54100c1c1c0d00e010403d0320085849a050f550003051155038680700000150803224115002e442803007568 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 465441519 1250 465440269 465440281
    0x1409060c0c03130602100605011b06050901020412060c0e1c08070c1508270303040b101d040203010605010e033c070e0c0a020709090507031a0402040b03030a05040b030c0d05 76
    0x4906c08124014500d0184034a68980005640d4003400442e00500814084003400200e005a400385400002c014009032910342d41d48582410405a140d080c0c400c55916406218200d400c208003810010041d507412280700d20030001c004d511001390178068281e2000003503007010000d013504210083c24504410000100d50518020320300d01044440d00d0348504580c140c4480b05c00070070608600001c00200562450303440e0748d606054440c0245c5a500d84907602c6070080303190510b84c0310306800a46203c0141c03490349018010142550700f40e90190b8180829245019401e45000c20f15006d1890308005244626502e131101c1d6904502c000540503002c0a805000040c2000208400049901d0f664503041d454648070011241481903041040c0544c0c0a01410046062260440c40c47e843c01401030b03822541c0c0c0c0f9100c0075100540103444c3c1031582c80c80070400c400c501d403601c43c55103c4803003a0000e6040041038140900284071301c7c010070600080100015940e0799180040300e100b91101c030300510882c1802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 465442769 1250 465441519 465441523
    0x20601060c111311190207080a031209080301120c05010327020f091f05040e03070b07021f021210030503031f12050a05060c1806030a0e070e0a1409060c0c03130602 72
    0x860516817201541c0c2d10010f0320b6440014141c0c2a5205500a0500c1d440f0954040d9002040024414019910341e104180418140d0303024500a054880c400184000c44e0718102f001080c46400c40360506140076010300144080580c030011058a921303034035405c1c0805000003020424200704996018403000100989103240101d84008d0001454110340d1031a00d800410040d1030400345074441550081c00508040782c82c501495801160900550b070500c0810700e2460581d01442c403120516940003d004c40516a448441980c4540001e101075981c0d0304651b902c90720b07440048c185014401c40c4460700d90602d2440e0312100c0c01058a0600301100074841d2500c039880d00030100c4103680070f01444000800e104014000c46441b144903600301340c2681100002c002094201810000c01ca680d40c5005035030903c0d0811a000241080401d0360b041d074a41114018183c0d00d242c064603440800a20600400d002c00250301c0d40c0045041114640b29202e80f04103500c0c41c001d08016500100e00355100003401600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 465444019 1250 465442769 465442777
    0x7060306050112020304020f1903080310030b0114100305060f060403111c0c12060b042c12030a02030c0c07030f0b011203020604030309050f0a150507020601060c111311 74
    0x30a8070f036840d00c01000183c0c0c008a000c1110302a4020f00c070760901700000d2400c4103a08203088600e00103803108507103a4945a210b60802c542c0e40d03500901e076200c2441440400b1101c54018400c03441506200d00e15480400c84403e01c51840b4018540c842000c64010740e1901c00300340c00900c018160b25140c0e680c90600204030a44600d03c1c5000d408020400d40318103210110181180b40c00c41051a519440d003540101c01e0281d0719410b03141180e407054985071503a2039006990007004030001d03c07241c00d00c40146a1405040422040815611a10050a07894413a8054a9104441c103c0040e140d503111011012a44204c414041e22070040034000300401a003d6004c4e206c4034020036600e02181e88803010800706142c2800080d000d40e0003200000c000030b10030741212400e2841003094900c03906500f48400c0c9041d0070001c044030030a1503076981003054000c0b48610b66106150384018100c552614201800d031aa00b0380f00071f81b54159020f95210b0540f1401c0140035074140c9004104039100d2108418600f50304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 465445269 1250 465444019 465444029
    0x80f030304150b01050a18090e0609011a030c01082a030f0109090f020f040b10030c080c0304020f090403020a05030a0f02150c0a0e0d06061205070905330307060306 72
    0x11007029072001c110588260fa01c5040d060311681d03d040c0d0300c0101a1100341c0290401c403c0010322082c0415500c500d401015a5059094003c00312400c11fa032202d42982c2415a40d580f0300b103203003103e5518540e0002008200c40c002824a44956250b9406041640f02c281d02e10100c61040410301314241c400c800700444c4030fa040a085012140d032105101c0044e2441520003030200340b410380e05900986064950348070b00b05001800014002e03400ca01280d05d6504401c41e0101007a0340b40100c400c0309070040071656014045072421455883c182d0700040381d0b004605116806080514000b07820035008100c101c448940100c200c90321540c8408004007007920300d003110070050140381c1c0c4282c4a041c090b40a1406408450201800c00c0d0052004035281181211855441403c1100040100706244038150250040314841025002581043d91801d80542c2c01001c0d15842c001c100310b40c2a10350140341d01d00b8514440c0c0b0400760300c0c140640c000329501d08444036906010b207000c0000c400c2e4141c0d00100c1155 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 465446519 1250 465445269 465445283
    0x50c210f0309090408090609040c0206091e1c02031c1505030607091a0f040b210108030910030912020c130608070b0a1103040b0c15071710080f030304 66
    0x100009202503160b016801d0750070b4011100c40003180015800703c01078000000c0c0501018105000200001d0035540c2d0340d08007a0141e0030405c180b0408180c240200e0344003c840501ca0313000300101d04101c0760f541c4000d07164070a960f02d050541140c1d186c1300b4002c0f91444491188002c64910000104230005c080030b5210400d00030f0140c500248070b00740030030102c1c8100d00039241c819000340380c0004030643c65031690824101c54020481014001070b980c1c060406410080030940d1503450f00c0142d650211420503001c1100c0010340c0040100c001c0c0001100c0c000c180c20b4505000c1c1c42c03030203e0158044d20040000401304440145920781741940007a8016030850120789070388250450301c0703418044440a01803214550070070841070010020141c0103100c04546440c1106620012036001800c1d40c0043c1c10902001d03400003002c0000075000c001441140e080c180b4425040e040c82d2001074401000b04180c91030303d928000000c0c0f520305110400100400c40d032030a564144040465058513a481160110390078 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 465447769 1250 465446519 465446533
    0xd14011515120905240f0124050904090f12020c01092d1d090c0102070f030f0203100509010b1903021c05010b061939050c21 55
    0xc0c10701c07034903448141c0c50302c6041c2d0020880715403070003500d40319600742c409109071203040326000881c0311718050350044512030b84458140400806c90104041e40003504160240c907006d4558540c0c41c0f403080004e0981c2c24000c0d9180c0203800441c000d0001c800001d01440488c6142c9000d01c500c1150f0641ca012580e0700f602d41d50540d100055820500901400c1551740440390401c81809100600705984104500320f00303060f0b580c4820020398500560404e0084554520500ca000702c0c0c10040c40c0c0d10386400b400904503440c2007600c0001c041e07000b4800904001d424001c6a4190345080c4800d5200e1010214244118604440a28042c0c0201d1040901610500c503003421301c0d030040c42e581d0082c1c0342e00910550240319503031500d0030b054540c028207030303119540c4000c0c2c1d0106c1e555020040c81110760009000d40c1030b0091070805003a60001300203c2448000c86403e5400340030200d0000d81c3d100d400740214280e0740c811402e181e45810f0300360f0100d682041c0342107810356070003403c050302c601c18030b40c040100c3c1c583c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 465449019 1250 465447769 465447779
    0x309030807110304180905010203010f03030917060c030c0d060e270a02040b03030d150512150403110a0503030c070506090304030f032006070f09050102010e0a110d140115 75
    0x2102c1d1400701e4281c495001400305014110840212075204040d05401051384c5500761141401c9a00a0340290465406040b0820801d5001040d44004008900609803002d6110a6047c0c8822008003c0080a90000006406c48482c00705032a85920740c10b0042092684501da030a20b0034009840f1411074440d0b00d07504240b40d000058078200c1460070b450182c51000481e0303003808098920b500b01140d0501050001c40d07103415083c480e0740107800b540420186200d21f424140003090242c80030540c46600590702e81c0ca4443d0304004000c4e0440d5151a02541c1c4421517034420b07052902e14007000300300380000010f2103103102e240e80c061707c00345028006950454540d43c082c0f0384d0700c0c41544402400100c4007154000440d0085400d000507400003d001844400c000d0360311820440211401c8011480000c844001c02d580b0610000c0500000e00007049061184802246c2d00e0301c0d9071307400a10b0069080d044024589403032011181c600d07400044202103118070704005019000c00506901e50030394000300022 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 465450269 1250 465449019 465449027
    0x6012d030f0f0e03090f0109210b10081e1c1e020106050d0b190513150b130e01150807030b0f010e060607031e030b0114040b1213120309030807 63
    0x80c000040100551800034544d00307110383c20564006d0107042c00100d1100041040c0c800c2d8026008600e4082181e09081c6546883c00704a0409400f044d00c07500e400400f440300000024412214040300702c4001c1c250102009010310340004040c140b4002c40100c002001500c1c0c1094080000c2ea405803400103403955903003822401c840561240b2580281c000a20002040ca60109560020811221014002101500c41061b034009071114200031003844130350000e0040007880785603800c004641c140704200c48040011031100c0b885421a403042c2e80c13011200c102c0b020950010118000f2800e600098960300d04010351214410f100c00d4544103018000220780040e50b454542c182c0e0b030107000c0d0b5034036601d49005000080d00400400c0701880351051070136111000c884007900c402c92140e6004070b0f9843e0070900040070b114085141100400c400c1c4802d101d142440320a50320702007194110140f01d07075220010b13030a21f1300d80301c0006011480c0d50700d01030148540c143c00c10307003d140c02512030b0b21541d100c40d0f10440e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 465451519 1250 465450269 465450281
    0x10503210a0c02030a030f030b030601180e0307021c021e01200a060f36111903030305040b07020a0302100507050f0c300306012d030f0f 60
    0x4100a2030054039440a12503080640016011803800703109218455010a00d8403680c40801d8001c0b40390700c02c49904040e8140501d0002e00c3d82513002c0c0c250395250003405549001c1c4480a811119102c2c20800c200c28810810703103030300d1a001010311300d001c65410360140f540245044268054902c0c5480700c1402c1016546140080300107943d10807031803c8042070310040c4d0382c401900d650070340284034025001c0b0711507000f590741400c40704e10005036180c041100c1c1c51144400c3e00c0001010b14400c0202c130107000281240c02c070700303907084510042c03130f84060800585080c180014448440001280c040107166040c0d0016120710310070081a425a12402410b0303a445885100040c0180d01c40e03461000c1442090b000350360800182d0034018100b10070b140700c00d01c0940080c0b0754601c461380100c4014840b0b403019880c108001c8040c40a100c08025407040c43e074120b00c802022541409003403c0721044960038601024607200d840b08400100110104005024000806945840a0078007949000c0303900c031881a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 465452769 1250 465451519 465451543
    0x1406090601082e0e010c12060f05130207021c0606092f0f04060e0901090c140703090b03090c04050105060a050406210e0303040b0f10170a0602160209010503 69
    0x3004a0080218805070681c408650800c01c0c07803d1070303078948500649001e64040c01c002c020001c40d1101e448400100041c0b1b00f419160596400c245040104031518000700c010346100750f61601030058500310b040c001c0d21075014007c2d04410340001c140402095008070420844c85850284212940d505e8010240d5401010641200340c20b400c019400460b1241034030450301a0500a500340155504241d041d0b070841da000002007544c004403a016882c1018031280500030140f8100058401d104000305842c205c0d203001e4a40d9800015072006043c000d40e60100100200c680302a500d02d0141b40103615510342c06011400346041100118007440c1540c16103414840c0c0796600342c2442d00c0e00508841041142c0d403080c5241d800b440c0e0220078a900c40c060041492101c20040da60b81c101031810a0450070010514280c9076218801d00c90520400794400d02140c1e1444003c040c84400810740c64104103012074000d204610018a40c070030b110004031079908103030003140c100740300e03a980d00c040c5902e0382441066 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 465454019 1250 465452769 465452773
    0x31201030f0614010608280c05040915082503050106060e0f040506030d0302070c05060304030306061e050915130801060501230901111005040507090b0414042607140609060108 77
    0x585c01181c016108844a0790451501f1160110940110308848001c4079903400030742c00042c28440601d482c015035200050a200c0c520f075a40c5010081912030302c2d40c000d0080745006440c10022080c010804400146130420020018680d0b180405000c00c00c0008640d801841403030540b00d0580b40511400380714103030150290008100b0000b045009600c6040708480c10341012001062540b1203a0165110b244641c500107503550501e100940080c3c0d0540807040300088840509409070b50103815501850703400d0380c1e005480c0c062003e003a0000e006928281104420001000550410541200d011140b01b0b880e00c2800c150b4101c240c03201c1c0c01c2040c00030b8644250801201d41103500c100c1c0625078510484040da021100c1c1e890007401038810a82d41030301d0710381c00101c1c140514101031141e0b540d01e0308200c1d41000450741c030203030065011000800240040340401c0b080c5007041c6410010110945000056a603298003c0ca030030500c02c14a40f02c540054411000000d581c11300c000340b120705803528000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 465455269 1250 465454019 465454021
    0x201090c05120a05150f091204090f060e04200f010801120609080a02060417032e08030f0c120301050303040b0306030c04020d1406031f0b03031201030f0614010608 72
    0x5010041042d80035240151003031040110101c0e02c14043c08507001e01482e40340d84c8608004010001a00028103480c6d8036401007490b01d1001c0c0320001c00c49084890f01100440d6003020b148500005003429444003509402520402080040300900d6400c41d07400c04a210300303281d004c1002e0004080580b0030203070114082000622107110114000e03a0340e82c4c0310354004907013641c903990386d00e41da03030003d022143c00340e400601440104420b0304040307041030b04e50f001c04504624100094013040300d003062190201060344415458866170401022002d8071940080321358544a02200f0a1158042d10100030a07024074128400c40403900300440303040340e030002e005505250602100030807960010b848543d00d07101e004494000350302c3e00e0014048003001c003a0001528504046019a8400001c207a2817103600301203402c0d0071204d100c02003407031032081190300000c18241319000f280c40d510580e03a0040e0303070340c01002c00042044881c040e00c8000620990301442549030284074480c02050a002e20b9000c200010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 465456519 1250 465455269 465455279
    0x1202060d060b1b010c080f0403050c0c030303090a0507080c06090621010e090c190909080f07080a09080106060e0d021801030b01051c0c0b0703021c020604030f0201090c 74
    0x1000341021650800001601e182e49500810807580700000c1c0e802c000881c0008041e100a0a00c2040c0080c1c01c1400d022030306140101380ea912185008100a0a025020a0b0361903040b5080080341881c42c4080c003260765a040c91111180e0720b021041c0116075503c208070b80030030801c01c01308d84200451000360910741007034200c00401030f00741c0140400c0800a015143d1210b80c4042220b41540200752901b003c0220f410b203108047d003030100340d190450140c840f4120420094540c980002c040300c0c0221000592060280703801d010702d10401c04240030f00340b030220f44a8140800040100400850382d01e0781c0606035611013205003601c070309101d0180864004242d81e4224108490b40840c0d0070310003010000100c1074445204010f6100b0f802c259600725903000140110f080448029600d40c0d0f821400c44640b035940e64034903111180d24051214000d0000c07034480308050003040108499242c48456088045117403900075600c01f0201c1d400d4001034075603840d00c0151401840b460606d0303130700f0100d000310303071820f00b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 465457769 1250 465456519 465456529
    0x809100903053703120b09151c051219080c0a0305181519142409070201140a0c0806010311040f06021605030127020406090c02030316091202 62
    0x48072100d500340f5100009103402003040301c0d001c9080380700c0d4440b1141e0807009540401220201c245180c007400340001840088500340c218503007190301c119102d102c60020401920f079250003074200144144103925242840b000340c00043c00580c445003a004504000302e110403900c0600c150b450f814001c5081041400031442500725552298180003803003c402000b00c0818501150403c10400d0072822605000c0c902c0c8040c2160b40e0101daa00304140100800300000116440d40500044110100c40e2003a5140503291200000c824500030041c81e078034a03101c0c80c040d0103001a05010f06400000034006003415141d417140500c44461903071921100d68617039005600802c0300e6080500d100c1d1080c000001e503000d031904100080c00c2658060328800ca200c4c014074032404203a4008500c6641005124140003004512107059800c0310071242c1480000d80c004980140140d403ca05100c03800c003092003035450340000c02940030f60443e201c5207519483c907180440c1c070410f1038050340b8201450042c00c88003510f44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 465459019 1250 465457769 465457813
    0x4151d06180a0e12160c050618010e0d0b0915010b0f030402010c050a02031e0c03010219050f0f1306111b1017010f080709020a090b03040809030a080910090305 70
    0x80800c071542d03450380b036030901c481740c014014800c00c20042d50880400c004035180203c3c01000140c0740070342840710340041103650484200b2100d040100c081030358030403940c0d200c01070020144c1040403044141408862151950911400c00d9001c000c0b11000180015040c411100c8440d00a9429070668072140e0044660b1030714000d080d00c0601c6550b80785400b60f601440144405001c1d0048041c403030f02c85059040c14481e1040f6818401d03441841000002c0c3d0318507420491040c4203143c00c0b55906003001c1145654003807a0606c0a18060114142a15150421004e404e4440c580c554012520300d00035110b136100d681c0401100e035a85440444045824018809040a1071a040110300413002d2089c081d034508d000d13801400c0f1402d82c103000300a40e180512003c4050170728a00158941400391001600c002543e1007207801c12000000080c0501c100081980c41e9114001d0541d00c440c0100c1c01c003141603030000103083d40b180b218001480c0704c0038028865101101c1c0d014015111100c00b1019000020344 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 465460269 1250 465459019 465459041
    0x60f0c0f080901120e0f010605060c030d021308010c0305060405010b03040f1118041a090a0803060907260601120608060117030c0a050604050601090209010503130204151d06180a 78
    0x1894096420b00c4d6103850080008804c03840e00100300560807800d040307080d42c51036440395008d00c10400500700d2000c0b0200c01c503001080034220160f95602c0e10399414250a41341e41c071100c0c00e540b0740a8017a85d041e5040c3c00c100d005000c100e41c1404607988800102020384400c0d28004d00742240e10081038001900041216071046000340314280321141c24031168641c0c0d008880840e541215941502c42b5442807540300c3e500051000000e0000741c0959540c000305100c09424580301d440710314005641303036220304010800f90440889418032a80d94440542c0200c905450b46804540c228903013200070310f1244170381011149001c005144c2e50340b07404900644500084030b810918001040055503e610800c038030340318a8822002005680782c50304013541003640680110f813680340108854580360381c0c80030a40c0d0300400b105191401310032941c40024005d10000301d448c580c60500c60310005060340f070f49168402e103900e4600c0c06401540d0303180401212040e2440301041c1c0059010101c0e4285130b460b809100d41c50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 465461519 1250 465460269 465460277
    0x6181d0405160321020a0b0708150402040303081008010b061204020d06020a0203071b121202100e03041d0705040b0f0904410703020a1b0606060f0c0f080901 69
    0x4100d1102402040380c9074200b0703030325002066203e0000c400c0100c3d130014091078034405040d0207030301941c032940c11600250202042101c06000705001c1c3c00603092151400f080100115070750741d0fa174980a07114520071240c0e150006559480001c035010107000d035280303180307009140e54602000f00c00103128148003c1d005036004002c0c11882c2d030005601d80b00404099025800450300c0307040924060141524055040040a100e0603042110925450b01484201c0e40100e18203116078403100100d180c00021240303a82c0c0c1d2820110301100c0c0b0f0314044000d00c140e582201d980d002e0405190356900c4c3c00c8100b0382d40039000400400c810400e420152014020240315074070b00c40d1805030f19400042c20740301d0443d1010030a40c1d6441010440401507c40c0c003808088091040300d0a080b840d0b4043c0c0480401000c000034181c0000c1d410740f109208944d015611402c82c0100c9034120340754148a80103110070b000f100c1c0410b08041e903402c411030241000c030100540c006042e0030b0321200740d41e40c190f654009074041c6042c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 465462769 1250 465461519 465461533
    0x20a05061b091c1509050601060f020a02090a051b040806150a0305030c03030601030b1c06020a03020409060b070b09060c04120201030b0310090c0605180f190306050106181d0405 78
    0x96598408400c1d4481c4000d60291540101c50900002c2d4484004d07440781c40e82d00c2e00703028000040000c03404604580b0b49040c80f000d445400c040985c101028503d000b5400b0700500c04001c40142c0690042d8001e50102100f0030b22b030b601c00b008220303940c496400b40c0380c403680c44040003810180104022602c03124014208120301592592940d19541140300c0c2506036403c044100121940d041c840d41ca844a012511440c00885003514445d0a80f100240900210f40014101d440c2a000c0d40403034000f841600c80400145a40d804048200d8000031300450f0419085000702c1c2e106140041c0050003a140f14a003d85040d00d00340c030100d0700341c0044100b241855120810101c9580d0140000202550781d000080303902d105038a084202d22240da01300c642406824032110407041510018016803280a80758201040785402c00929007880804042c840b034000b400c4080100460394001c181242d0031600c1d803001c1840340008a1030b0340f11080c0550400046051221080319110780d12554015000340c00307a404c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 465464019 1250 465462769 465462787
    0xd080105040228180603050105100c03050a030c1b03080105090a290a17010c030c140a1101060807080d02101e092406060e030c01080123030303040c05030d020a05061b 73
    0x21210b40c001004244d036003004108134282441c840203d40014a0b000280012f96a400b40103809601424010503580d4419600310900400c40d04030b20700c0000d4411000303115540750040c0740482c01d008040c01588003070003180c002091405844542440d00c4d40c41c20300002000c10100c0103102c4880b8603035009004c4d00c400502651600c0307400d1a8041c428002040c03240450b1030141c1031301d00001c65242080703545994502d000c00c00406a451101030f81c134101e4040050490844e0140940e5040b20043c3c0c0104c400004710454001075070500d500450302500c0d03260889075200f00442d205035860101440d08140c07191005070882e0b0000228510483d000340d00822241c00480c0c218550315000c12149507105004e0160030340200d90095207d00490040628408210000302a01c4042c810b00314040c108200500c11541e10b55070034000c00b40c000d0201c907203d29103410304c501034020340e1003014001c4c01031403410400103201050117100150048020301e41d50b250b04401c52030050410701500600282846014a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 465465269 1250 465464019 465464057
    0x613020906070f030e0909030409020c100e030405281701020d05090d091e05060703020a05030a0e0a06030218010e0f181b03011d13080c0d080105040228 67
    0x466406511103a4400c070f034503c0c01400f10800d68040301d22940300c0404018900c0c000004032415034208000142c1c0b02c1c103c80000c94a0705181d641d5159409003004154413180b1400405030080b100e04030340c003c411100698800c2ca4449007400c0d2101d12042003041403080c4002c0349405000c0182d054001840d10680200031402c40784203079070801494114480c09480c15501c109500040d000c5854a400000b40804000300141c25a2207000c0c09500003003049001e050091140481c2540c00c081500d80d2803807100700040420030b1204995101e04210f060201d030040c480d2003666070051105041c60030403c4c00900540e060154096119400b00b180d4001d130701c1b0381e110a403000360030701c0580700403070404d060452054901100f0340d22485a808000c2c0010031004020786200d000c4d03d15000071640700d58440200c015942d285440c005810300c0b2000500b42542d540015400d0f20a09490355030304801d9884100300403c1c3e20a20b96204020340e92200406009003002c01401c01d44c1205060034540326694120440c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 465466519 1250 465465269 465465277
    0x70503030411030c060c1c18090504020a0614270a08100b0907020604030f031418010606020606060706050c0d0c020703030f020303270c0a15020c06030402090613020906 74
    0x8842040007458040a82000c00c06200c16104c21a1a2030504022045507959001c1401c07402c0310743c0d05076080e420912030188c0840e1100e0f0b00c460b071160030620f866408075070152106580407030003640c03000340004403c3d02c03501481c1900b0f01c100c5401460071011115003a182014420400800f00b07205207111540c2d81c410410310000c000075030207005901440e002d190220341580c00d003e8044c4a4000821441130b074081455640258903040c0340c0303907070500d1440417002080d40320f031070303540585030740c024030002000d0304404d400b40c501c101c0000c2c040292100ca040b03807240c1d0103480700d03900a14180000f800140300c0b50400c507404200c0340c0403e81884000e80a040540c0c61b001169009a044a0020300c00e241d40000e8484256000703000840ca103081c010710500c81d41c0206c680d00c405004080f0342e4001c003000d05001c124600c107030041c14000c00c151144110b2111fa0200f41100303000d0300c02c0c241c00039554103080044d41c2c8105d0300140110b2465407510240305080e40724a200010072542040040c040d9035603600a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 465467625 1106 465466519 465466523
    0xb09011e020f01051302031e030412030201020d06090203040203060106081509180a120f1404050f0a120f060b06070b1b07080d02181e01050a050705030304 68
    0x490800d020602c100d801da508102c203200502902003005000e01c3d0007102550a44a81d000d07081d42d055824501055890b0400c1c00100148581448011055070190002515028402e589001100c0c0c1c1a0040e4040a5020042c04258242080f86c03034054085400e040f06141000842059801c807001d00e5203100301c180000040c44441c58813000302c882010380040300e1800c5450700c2c03d2401070810302182c2d00003400800724603d00c20b115240901c900f0119200f202c1ca0b00341014240309100c544900803c4d0040000100010501207111142d05050701039500440d1010030380c94040141d80d0551241c5120f198240032810100720701c42661900f1640091a458810303642c0c0f03040084e540500a805400d40d44081030040c0c800307649400912142d4100341e031f00b1800c1d949040400007200401410442031100c002a00e100c5035000780c00420b050502c1e414840d0400c2217550b1030030b103554012102 = true := by decide +kernel

theorem cover : BRFrame.Cov 465287769 465467625 := by
  have h0 := BRFrame.cov_init 465287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 465287769 ≤ n) (h2 : n < 465467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
